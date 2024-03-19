use std::collections::{BTreeMap, VecDeque};

use rum_math::{Rectangle, Vec2};

pub trait PartitionIdentifier: Eq + Sized + PartialEq + Ord + Clone {}
impl PartitionIdentifier for u64 {}
impl PartitionIdentifier for u32 {}
impl PartitionIdentifier for u16 {}
impl PartitionIdentifier for char {}

/// Stores the UV and absolute coordinates of an item stored in a
/// BinaryPartition.
#[derive(Debug)]
pub struct BPEntryMetrics<Metadata: Copy + Sized> {
  /// The UV coordinates of the item, in the range `[0, 1]`.
  pub uv:        Rectangle<f32>,
  /// The absolute coordinates of the item, in the range `[0, n)`, where n is
  /// the size of the partition.
  pub abs:       Rectangle<u32>,
  /// Additional data stored alongside the coordinates.
  pub meta_data: Metadata,
}

/// A spacial partitioning data structure used to store rectangles in a 2D
/// space. Unlike QuadTree or its binary [equivalent](), the sub-spaces can have
/// arbitrary sizes. Overlapping of items is not allowed, thus each leaf node
/// can only contain one item.
#[derive(Debug)]
pub struct BinaryPartition<Id: PartitionIdentifier, Metadata: Copy + Sized> {
  /// The root sub-field of the field
  root:        u32,
  /// Indices of sub-fields of the field.
  /// These may or may not actually represent partitioned space in the field.
  fields:      Vec<BPSubField<Id>>,
  /// Maps entries to their sub-field metrics
  entries:     BTreeMap<Id, (u32, Rectangle<u32>, Metadata)>,
  /// Stores a linked list of BPFields that have been allocated
  /// but do not represent any partitions within the field.
  garbage:     Option<u32>,
  /// The number items stored in the field
  entry_count: usize,
  /// The dimensions of the field
  dimensions:  Rectangle<u32>,
}

#[derive(Debug, Clone, Copy)]
pub enum BPSubField<Id: PartitionIdentifier> {
  /// A sub-field that represents a free area within the field
  Empty { rect: Rectangle<u32>, parent: u32 },
  /// A sub-field that has been allocated to an entry
  Occupied { rect: Rectangle<u32>, id: Id, parent: u32 },
  /// A sub-field that has been split into two lower order sub-fields
  Split { a: u32, b: u32, parent: u32 },
  /// A sub-field that has been allocated but does not represent any area within
  /// the field.
  Garbage(u32),
  /// A temporary field type used during the packing process
  PlaceHolder,
}

pub enum BPInsertResult<Metadata: Copy + Sized> {
  /// The entry was inserted into the field after the field was grown.
  /// The new dimensions of the field are returned in addition to the metrics of
  /// the entry.
  Resized(BPEntryMetrics<Metadata>, Rectangle<u32>),
  /// The entry was successfully inserted into the field. The metrics of the
  /// inserted entry are returned.
  Added(BPEntryMetrics<Metadata>),
  /// The entry was not inserted into the field because it is already present in
  /// the field. The metrics of the entry are returned.
  Exists(BPEntryMetrics<Metadata>),
  /// Some undefined error occurred during insertion.
  Failed,
}

pub enum BPResizePolicy {
  Allow,
  Deny,
}

pub enum BPInsertPolicy {
  /// Indicates that the item should be inserted into the atlas in the sub-field
  /// that has the smallest possible area that can fit the item.
  SmallestFit,
  // Indicates that the item should be inserted into the atlas in the sub-field
  // that has the largest possible area that can fit the item.
  LargestFit,
  // Indicates that the item should be inserted into the atlas in first sub-field
  // that can fit the item.
  FirstFit,
}

impl<Id: PartitionIdentifier, Metadata: Copy> BinaryPartition<Id, Metadata> {
  /// Removes all entries from the field.
  pub fn clear(&mut self) {
    self.root = 0;
    self.fields.clear();
    self.entries.clear();
    self.garbage = None;
    self.entry_count = 0;
    self.fields.push(BPSubField::Empty { rect: self.dimensions, parent: 0 });
  }

  pub fn new(dimensions: Rectangle<u32>) -> Self {
    use BPSubField::*;
    let root = Empty { rect: dimensions, parent: 0 };
    Self {
      dimensions,
      root: Default::default(),
      fields: vec![root],
      garbage: Default::default(),
      entry_count: Default::default(),
      entries: Default::default(),
    }
  }

  /// Remove an entry from the atlas.
  /// `None` is returned if the entry does not exist.
  pub fn remove(&mut self, id: &Id) -> Option<()> {
    let (index, ..) = self.entries.remove(id)?;
    self.entry_count -= 1;
    self.try_merge(index);
    Some(())
  }

  /// Reclaims a garbage field and connects it to the existing garbage field
  /// chain.
  fn reclaim_garbage(&mut self, index: u32) {
    self.fields[index as usize] = BPSubField::Garbage(self.garbage.unwrap_or(0));
    self.garbage = Some(index);
  }

  /// Recursively merge the field with its parent if possible.
  /// All merged fields are reclaimed and added to the garbage field chain.
  /// The root field is never merged.
  fn try_merge(&mut self, field_index: u32) {
    if (field_index as usize) >= self.fields.len() {
      return;
    } else if field_index == self.root {
      return;
    }

    let field = &self.fields[field_index as usize];

    let (parent_index, child_rect) = match field {
      BPSubField::Empty { parent, rect, .. } | BPSubField::Occupied { parent, rect, .. } => {
        (*parent, *rect)
      }
      // - Garbage sub-fields do not exist in the field and cannot be merged with any other
      //   sub-field.
      // - Placeholders are temporary fields used during the packing process and should not
      // be encountered during the merge process.
      // - Split sub-fields cannot be merged with their parent since they are not leaf nodes.
      _ => return,
    };

    let parent_field = &self.fields[parent_index as usize];

    // If the parent is a split, we may be able to merge the field with its sibling.
    // Otherwise panic, since this is the only condition in which a field can have a
    // parent.
    let (sibling_index, parents_parent) = match parent_field {
      BPSubField::Split { a, b, parent } => {
        if *a == field_index {
          (*b, *parent)
        } else if *b == field_index {
          (*a, *parent)
        } else {
          panic!("Field has an invalid parent");
        }
      }
      _ => panic!("Field has an invalid parent"),
    };

    let sibling_field = &self.fields[sibling_index as usize];

    // If the sibling is empty, we can convert the parent into an empty field,
    // and reclaim the sibling and child sub-fields.
    if let BPSubField::Empty { rect: sibling_rect, .. } = sibling_field {
      // Get the bounding rectangle of the two fields, which is equal to the parent's
      // rectangle.
      let rect = child_rect.union(sibling_rect);

      self.fields[parent_index as usize] = BPSubField::Empty { rect, parent: parents_parent };

      // Reclaim the child and sibling sub-fields
      self.reclaim_garbage(sibling_index);
      self.reclaim_garbage(field_index);

      // Recursively merge the parent with its parent.
      self.try_merge(parent_index)
    }
  }

  fn get_candidate(
    &mut self,
    dimensions: Rectangle<u32>,
    insert_policy: BPInsertPolicy,
  ) -> Option<(usize, u32)> {
    use BPSubField::*;

    let first_fit = matches!(insert_policy, BPInsertPolicy::FirstFit);
    let area = dimensions.area();
    let mut candidates = Vec::with_capacity(20);
    let mut starts = VecDeque::with_capacity(20);

    starts.push_front(0);

    while let Some(index) = starts.pop_back() {
      match self.fields.get(index).cloned() {
        Some(Empty { rect: field_dimensions, .. }) => {
          if field_dimensions.fits(&dimensions) {
            if first_fit {
              return Some((index, field_dimensions.area() - area));
            } else {
              candidates.push((index, field_dimensions.area() - area))
            }
          }
        }
        Some(Split { a, b, .. }) => {
          starts.push_back(a as usize);
          starts.push_back(b as usize);
        }
        _ => {}
      }
    }

    if candidates.is_empty() {
      None
    } else {
      use BPInsertPolicy::*;
      match insert_policy {
        SmallestFit => candidates.iter().max_by(|a, b| a.1.cmp(&b.1)).cloned(),
        LargestFit => candidates.iter().min_by(|a, b| a.1.cmp(&b.1)).cloned(),
        _ => None,
      }
    }
  }

  /// Returns the UV of an item relative to the atlas.
  /// If the item is not in the atlas, returns None.
  /// UV coordinates are floating point values in the range [0, 1].
  ///
  /// # Example
  /// ```
  /// use atlas::{Atlas, AtlasInsertResult, AtlasResizePolicy, BPInsertPolicy};
  /// use atlas::Vector2;
  ///
  /// let mut atlas = Atlas::new(Vector2::new(1024, 1024), AtlasResizePolicy::Allow, BPInsertPolicy::FirstFit);
  ///
  /// let id = atlas.insert(Vector2::new(100, 100)).unwrap();
  ///
  /// let uv = atlas.get_uv(&id).unwrap();
  ///
  /// assert_eq!(uv, (0.0, 0.0, 0.09765625, 0.09765625));
  /// ```
  pub fn get_uv(&self, id: &Id) -> Option<(Rectangle<f32>, Metadata)> {
    self.entries.get(id).map(|(_, rect, meta_data)| {
      let dimensions = self.dimensions;
      let x = rect.bottom_left().x as f32 / dimensions.width() as f32;
      let y = rect.bottom_left().y as f32 / dimensions.height() as f32;
      let width = rect.width() as f32 / dimensions.width() as f32;
      let height = rect.height() as f32 / dimensions.height() as f32;
      let rect = Rectangle::from_origin(width, height);
      (rect + Vec2::new(x, y), *meta_data)
    })
  }

  /// Returns a recycled index if one is available, otherwise allocates a new
  /// index.
  fn allocate_field(&mut self, content: BPSubField<Id>) -> u32 {
    if let Some(index) = self.garbage {
      self.garbage = match self.fields[index as usize] {
        BPSubField::Garbage(next) => {
          if next == u32::MAX {
            None
          } else {
            Some(next)
          }
        }
        _ => None,
      };
      index
    } else {
      self.fields.push(content);
      (self.fields.len() - 1) as u32
    }
  }

  /// Insert an item into the partition space.
  pub fn insert(
    &mut self,
    id: Id,
    dimensions: Rectangle<u32>,
    meta_data: Metadata,
    insert_policy: BPInsertPolicy,
    resize_policy: BPResizePolicy,
  ) -> BPInsertResult<Metadata> {
    match self.entries.get(&id) {
      Some((_, bounding_box, meta_data)) => {
        let (uv, meta_data) = self.get_uv(&id).unwrap();

        BPInsertResult::Exists(BPEntryMetrics { uv, abs: *bounding_box, meta_data })
      }
      None => {
        match self.get_candidate(dimensions, insert_policy) {
          Some((index, _)) => {
            use BPSubField::*;

            // Insert into the top left corner of the sub-field
            match self.fields.get(index).cloned() {
              Some(Empty { mut rect, mut parent }) => {
                let w_diff = rect.width() - dimensions.width();
                let h_diff = rect.height() - dimensions.height();
                let mut index = index as u32;

                for i in if rect.width() > rect.height() { [0u32, 1] } else { [1u32, 0] } {
                  match i {
                    0 => {
                      if w_diff > 0 {
                        let new_index = self.allocate_field(PlaceHolder);
                        let (sw1, ne1, sw2, ne2) = (
                          rect.bottom_left(),
                          Vec2::new(rect.bottom_left().x + dimensions.width(), rect.ne().y),
                          Vec2::new(
                            rect.bottom_left().x + dimensions.width(),
                            rect.bottom_left().y,
                          ),
                          rect.ne(),
                        );

                        self.fields[index as usize] = Split {
                          a: new_index,
                          b: self.allocate_field(Empty {
                            rect:   Rectangle::new(sw2, ne2),
                            parent: index,
                          }),
                          parent,
                        };
                        rect = Rectangle::new(sw1, ne1);
                        parent = index as u32;
                        index = new_index;
                      }
                    }

                    _ => {
                      if h_diff > 0 {
                        let new_index = self.allocate_field(PlaceHolder);
                        let (sw1, ne1, sw2, ne2) = (
                          Vec2::new(rect.bottom_left().x, rect.ne().y - dimensions.height()),
                          rect.ne(),
                          rect.bottom_left(),
                          Vec2::new(rect.ne().x, rect.ne().y - dimensions.height()),
                        );

                        self.fields[index as usize] = Split {
                          a: new_index,
                          b: self.allocate_field(Empty {
                            rect:   Rectangle::new(sw2, ne2),
                            parent: index,
                          }),
                          parent,
                        };
                        rect = Rectangle::new(sw1, ne1);
                        parent = index;
                        index = new_index;
                      }
                    }
                  }
                }

                self.entries.insert(id.to_owned(), (index, rect, meta_data));
                self.fields[index as usize] = Occupied { id: id.clone(), rect, parent };
                self.entry_count += 1;

                let (uv, meta_data) = self.get_uv(&id).unwrap();
                BPInsertResult::Added(BPEntryMetrics { uv, abs: rect, meta_data })
              }
              _ => BPInsertResult::Failed,
            }
          }
          None => match resize_policy {
            BPResizePolicy::Allow => BPInsertResult::Failed,
            BPResizePolicy::Deny => BPInsertResult::Failed,
          },
        }
      }
    }
  }
}

impl<Id: PartitionIdentifier, Metadata: Copy> Iterator for BinaryPartition<Id, Metadata> {
  type Item = BPSubField<Id>;

  fn next(&mut self) -> Option<Self::Item> {
    None
  }
}

#[cfg(test)]
mod test {
  use super::BPResizePolicy;
  use crate::atlas::{BPInsertPolicy, BinaryPartition, *};

  #[test]
  pub fn size() {
    assert_eq!(88, std::mem::size_of::<BinaryPartition<u32, u32>>());
    assert_eq!(28, std::mem::size_of::<BPSubField<u32>>());
  }
  #[test]
  pub fn creates_correct_uv() {
    let mut atlas = BinaryPartition::<u32, u32>::new(Rectangle::from_origin(1024u32, 1024u32));
    match atlas.insert(
      1,
      Rectangle::from_origin(512, 512),
      0,
      BPInsertPolicy::SmallestFit,
      BPResizePolicy::Allow,
    ) {
      BPInsertResult::Added(rect) => {
        println!("{:#?}", atlas)
      }
      _ => panic!("Failed"),
    }

    let (uv, _) = atlas.get_uv(&1).unwrap();

    assert_eq!(uv, Rectangle::new((0.0, 0.5).into(), (0.5, 1.0).into()));
  }

  #[test]
  pub fn insert_texture() {
    let mut atlas = BinaryPartition::<u32, u32>::new(Rectangle::from_origin(1024u32, 1024u32));

    match atlas.insert(
      1,
      Rectangle::from_origin(512, 512),
      0,
      BPInsertPolicy::FirstFit,
      BPResizePolicy::Allow,
    ) {
      BPInsertResult::Added(rect) => {
        println!("{:#?}", atlas)
      }
      _ => panic!("Failed"),
    }

    match atlas.insert(
      2,
      Rectangle::from_origin(32, 32),
      1,
      BPInsertPolicy::FirstFit,
      BPResizePolicy::Allow,
    ) {
      BPInsertResult::Added(rect) => {
        println!("{:#?}", atlas)
      }

      _ => panic!("Failed"),
    }
  }

  #[test]
  pub fn remove_item() {
    use super::BPResizePolicy;

    let mut atlas = BinaryPartition::<u32, u32>::new(Rectangle::from_origin(1024u32, 1024u32));

    match atlas.insert(
      1,
      Rectangle::from_origin(512, 512),
      1,
      BPInsertPolicy::FirstFit,
      BPResizePolicy::Allow,
    ) {
      BPInsertResult::Added(_) => {
        println!("{:#?}", atlas)
      }
      _ => panic!("Failed"),
    }

    match atlas.insert(
      2,
      Rectangle::from_origin(32, 32),
      1,
      BPInsertPolicy::FirstFit,
      BPResizePolicy::Allow,
    ) {
      BPInsertResult::Added(_) => {
        println!("{:#?}", atlas)
      }

      _ => panic!("Failed"),
    }

    assert!(atlas.remove(&1).is_some());

    println!("{:#?}", atlas);
  }
}
