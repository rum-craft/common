use std::{
    collections::hash_map::DefaultHasher,
    hash::{Hash, Hasher},
};

mod test;

pub fn create_u64_hash<T: Hash>(t: T) -> u64 {
    let mut s = DefaultHasher::new();

    t.hash(&mut s);

    s.finish()
}
