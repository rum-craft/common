use crate::{CachedString, IStringStore};

#[test]
fn interning_empty_string() {
    let store = IStringStore::default();

    let empty_string = "";

    let tok = empty_string.intern(&store);
    "".to_string().intern(&store);

    assert_eq!(tok.to_string(&store), "");
    assert_eq!(tok.to_string(&store).as_str(), "");
    assert_eq!(store._data.read().unwrap().is_empty(), true);
}

#[test]
fn interning_small_string() {
    let store = IStringStore::default();

    let small_string = "test";

    let tok = small_string.intern(&store);

    assert_eq!(tok.to_string(&store), "test");
    assert_eq!(tok.to_string(&store).as_str(), "test");
    assert_eq!("B".intern(&store).to_string(&store), "B");
    assert_eq!("B".intern(&store).to_str(&store).as_str(), "B");
    assert!("function".intern(&store).is_small());
    assert_eq!(
        "function".intern(&store).to_str(&store).as_str(),
        "function"
    );
}

#[test]
fn interning_large_string() {
    let store = IStringStore::default();

    let large_string = "
  Lumina eiusdem a sororibus est agant montis tu urbes succedit gavisa dolore
Perseus incerti, repente pariter. Omnes morsu rediit flores, nisi scelus
confessis cristati ramis silentum arentis centimanum sacrilegae pone. Silvas
dieque ire *fuit*, resides videt quodcumque illi circumflua petii laeva ne
timidas Venilia. Accipiunt saltem apta modo! Annos tu tale concita nostro
relicto orbe quid, adit nec possederat simque conprendere defecerat avus
Cyparisse multarum!";

    let tok = large_string.intern(&store);

    assert_eq!(tok.to_string(&store), large_string);
    assert_eq!(tok.to_str(&store).as_str(), large_string);
}

#[test]
fn interning_same_large_string() {
    let store = IStringStore::default();

    let large_str = "
  Lumina eiusdem a sororibus est agant montis tu urbes succedit gavisa dolore
Perseus incerti, repente pariter. Omnes morsu rediit flores, nisi scelus
confessis cristati ramis silentum arentis centimanum sacrilegae pone. Silvas
dieque ire *fuit*, resides videt quodcumque illi circumflua petii laeva ne
timidas Venilia. Accipiunt saltem apta modo! Annos tu tale concita nostro
relicto orbe quid, adit nec possederat simque conprendere defecerat avus
Cyparisse multarum!";

    let string = String::from(large_str);

    let tok_a = large_str.intern(&store);
    let tok_b = string.intern(&store);

    assert_eq!(tok_a.to_string(&store), large_str);
    assert_eq!(tok_b.to_str(&store).as_str(), large_str);
    assert_eq!(tok_a, tok_b);
}

#[test]
fn interning_different_large_string() {
    let store = IStringStore::default();

    let large_str_a =
        "1: Lumina eiusdem a sororibus est agant montis tu urbes succedit gavisa dolore
Perseus incerti, repente pariter. Omnes morsu rediit flores, nisi scelus
confessis cristati ramis silentum arentis centimanum sacrilegae pone. Silvas
dieque ire *fuit*, resides videt quodcumque illi circumflua petii laeva ne
timidas Venilia. Accipiunt saltem apta modo! Annos tu tale concita nostro
relicto orbe quid, adit nec possederat simque conprendere defecerat avus
Cyparisse multarum!";

    let large_str_b =
        "2: Lumina eiusdem a sororibus est agant montis tu urbes succedit gavisa dolore
Perseus incerti, repente pariter. Omnes morsu rediit flores, nisi scelus
confessis cristati ramis silentum arentis centimanum sacrilegae pone. Silvas
dieque ire *fuit*, resides videt quodcumque illi circumflua petii laeva ne
timidas Venilia. Accipiunt saltem apta modo! Annos tu tale concita nostro
relicto orbe quid, adit nec possederat simque conprendere defecerat avus
Cyparisse multarum!";

    let tok_a = large_str_a.intern(&store);
    let tok_b = large_str_b.intern(&store);

    assert!(tok_a.is_large());
    assert!(tok_b.is_large());
    assert_eq!(tok_a.to_string(&store), large_str_a);
    assert_eq!(tok_b.to_string(&store), large_str_b);
    assert_ne!(tok_a.to_string(&store), large_str_b);
    assert_ne!(tok_b.to_string(&store), large_str_a);
    assert_ne!(tok_a, tok_b);
    assert_eq!(store.len(), 2);
}

#[test]
fn interning_strings_on_different_threads() {
    let store = IStringStore::default();

    std::thread::scope(|scope| {
        for u in 0..4 {
            let store = store.clone();
            scope.spawn(move || {
                let large_str_a =
                    "1: Lumina eiusdem a sororibus est agant montis tu urbes succedit gavisa dolore
        Perseus incerti, repente pariter. Omnes morsu rediit flores, nisi scelus
        confessis cristati ramis silentum arentis centimanum sacrilegae pone. Silvas
        dieque ire *fuit*, resides videt quodcumque illi circumflua petii laeva ne
        timidas Venilia. Accipiunt saltem apta modo! Annos tu tale concita nostro
        relicto orbe quid, adit nec possederat simque conprendere defecerat avus
        Cyparisse multarum!";

                let large_str_b =
                    "2: Lumina eiusdem a sororibus est agant montis tu urbes succedit gavisa dolore
        Perseus incerti, repente pariter. Omnes morsu rediit flores, nisi scelus
        confessis cristati ramis silentum arentis centimanum sacrilegae pone. Silvas
        dieque ire *fuit*, resides videt quodcumque illi circumflua petii laeva ne
        timidas Venilia. Accipiunt saltem apta modo! Annos tu tale concita nostro
        relicto orbe quid, adit nec possederat simque conprendere defecerat avus
        Cyparisse multarum!";

                for i in 0..400 {
                    (large_str_a.to_string() + &format!(" {i} {u}")).intern(&store);
                    (large_str_b.to_string() + &format!(" {i}")).intern(&store);
                }
                1
            });
        }
    });

    assert_eq!(store.len(), 2000);
}
