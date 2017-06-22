#[macro_use]
extern crate debug_unreachable;


use std::cmp;
use std::mem;


fn nybble<K: AsRef<[u8]>>(idx: usize, key: K) -> u8 {
    let byte = key.as_ref()[idx >> 1];

    if idx & 1 == 0 { byte & 0x0F } else { byte >> 4 }
}


pub struct Sparse<T> {
    index: u32,
    data: Vec<T>,
}


impl<T> Sparse<T> {
    pub fn new() -> Sparse<T> {
        Sparse {
            index: 0,
            data: Vec::new(),
        }
    }


    pub fn contains(&self, idx: usize) -> bool {
        (self.index >> idx) & 1 == 1
    }


    fn actual(&self, idx: usize) -> usize {
        self.data.len() - (self.index >> idx).count_ones() as usize
    }


    pub fn get(&self, idx: usize) -> Option<&T> {
        if self.contains(idx) {
            Some(&self.data[self.actual(idx)])
        } else {
            None
        }
    }


    pub fn get_mut(&mut self, idx: usize) -> Option<&mut T> {
        if self.contains(idx) {
            let actual = self.actual(idx);
            Some(&mut self.data[actual])
        } else {
            None
        }
    }


    pub fn insert_fresh(&mut self, idx: usize, elt: T) {
        debug_assert!(!self.contains(idx));

        let actual = self.actual(idx);
        self.data.insert(actual, elt);
    }
}


pub struct Leaf<K, V> {
    key: K,
    val: V,
}


impl<K: AsMut<[u8]> + Copy, V> Leaf<K, V> {
    pub fn new<L: AsRef<[u8]>>(key_bytes: L, val: V) -> Leaf<K, V> {
        Leaf {
            key: unsafe {
                let mut key: K = mem::uninitialized();
                key.as_mut().copy_from_slice(key_bytes.as_ref());
                key
            },
            val,
        }
    }
}


pub struct Internal<K, V> {
    index: usize,
    nybbles: Sparse<Node<K, V>>,
}


impl<K, V> Internal<K, V> {
    pub fn new(index: usize) -> Internal<K, V> {
        Internal {
            index,
            nybbles: Sparse::new(),
        }
    }
}


impl<K: AsRef<[u8]>, V> Internal<K, V> {
    pub fn insert_fresh_leaf(&mut self, leaf: Leaf<K, V>) {
        self.nybbles
            .insert_fresh(nybble(self.index, &leaf.key) as usize, Node::Leaf(leaf));
    }
}


pub enum Node<K, V> {
    Leaf(Leaf<K, V>),
    Internal(Internal<K, V>),
}


impl<K, V> Node<K, V> {
    fn unwrap_leaf(self) -> Leaf<K, V> {
        match self {
            Node::Leaf(leaf) => leaf,
            _ => unsafe { debug_unreachable!() },
        }
    }


    fn mut_unwrap_internal(&mut self) -> &mut Internal<K, V> {
        match *self {
            Node::Internal(ref mut internal) => internal,
            _ => unsafe { debug_unreachable!() },
        }
    }
}


impl<K: AsRef<[u8]>, V> Node<K, V> {
    /// Get a mutable reference to the closest node to the given key, as well as the first index at
    /// which the keys differ.
    fn get_closest_node_mut<L: AsRef<[u8]>>(&mut self,
                                            key: L,
                                            index: usize)
                                            -> (&mut Node<K, V>, usize) {
        {
            let closer = self.get_closer_node_mut(key, index);

            if closer.is_some() {
                return closer.unwrap();
            }
        }

        (self, index)
    }


    fn get_closer_node_mut<L: AsRef<[u8]>>(&mut self,
                                           key: L,
                                           index: usize)
                                           -> Option<(&mut Node<K, V>, usize)> {
        // For some reason this fails due to borrowck weirdness.
        match *self {
            ref mut leaf @ Node::Leaf(..) => return Some((leaf, index)),

            Node::Internal(ref mut internal) => {
                let index = internal.index;

                let search_nybble = nybble(index, &key);

                internal
                    .nybbles
                    .get_mut(search_nybble as usize)
                    .map(|mut node| node.get_closest_node_mut(key, index))
            }
        }
    }
}


pub struct Trie<K, V> {
    root: Option<Node<K, V>>,
}


impl<K: AsRef<[u8]> + AsMut<[u8]> + Copy, V> Trie<K, V> {
    pub fn new() -> Trie<K, V> {
        Trie { root: None }
    }


    pub fn insert<L: AsRef<[u8]>>(&mut self, key: L, val: V) -> Option<V> {
        match self.root {
            Some(ref mut node) => {
                let (closest, least_index) = node.get_closest_node_mut(&key, 0);

                let index = match *closest {
                    Node::Leaf(ref mut leaf) => {
                        let index = {
                            let search_key_bytes = key.as_ref();
                            let leaf_key_bytes = leaf.key.as_ref();

                            let min_length = cmp::min(search_key_bytes.len(), leaf_key_bytes.len());

                            // `Node::get_closest_key_mut` returns not only the closest node, but
                            // also a conservative "least index" where the keys may begin to
                            // differ. Thus, we need not start comparing at zero.
                            let mut i = least_index;

                            loop {
                                if i >= min_length {
                                    // There is no difference in the overlapping bytes of our
                                    // search key and leaf key.

                                    if search_key_bytes.len() == leaf_key_bytes.len() {
                                        // If their lengths are the same, then we're guaranteed
                                        // they're the same because their overlapping bytes are all
                                        // of their bytes, each. We can replace the leaf value and
                                        // return the displaced value.

                                        return Some(mem::replace(&mut leaf.val, val));
                                    }

                                    break i;
                                }

                                let difference = search_key_bytes[i] ^ leaf_key_bytes[i];

                                // If the difference is nonzero, we've found a differing byte in
                                // our keys!
                                if difference != 0 {
                                    break if difference & 0xF0 == 0 {
                                              // If `difference & 0xF0` is nonzero, then the difference
                                              // is strictly in the upper nybble. Thus we increment the
                                              // nybble index.

                                              i + 1
                                          } else {
                                              i
                                          };
                                }

                                i += 1;
                            }
                        };

                        index
                    }
                    Node::Internal(ref mut internal) => {
                        // We can do a "fresh" insert here (that is, safely assume there is no
                        // value sharing the same key already in this internal node) because if
                        // there was, then a `Leaf` would have been returned by `closest`.

                        internal
                            .nybbles
                            .insert_fresh(nybble(internal.index, &key) as usize,
                                          Node::Leaf(Leaf::new(key, val)));

                        return None;
                    }
                };

                // If this control reaches this point, then we are guaranteed that `closest` is in
                // fact a `Node::Leaf`, which has a key which does not match the search key. We
                // `mem::replace` `closest` with a fresh `internal`, and then unwrap both `closest`
                // and the `replaced` leaf to get a mutable reference to the new internal and the
                // bare leaf on the stack.

                let leaf = mem::replace(closest, Node::Internal(Internal::new(index)))
                    .unwrap_leaf();
                let internal = closest.mut_unwrap_internal();

                internal.insert_fresh_leaf(Leaf::new(key, val));
                internal.insert_fresh_leaf(leaf);

                None
            }

            // If the root is empty, simply insert a singleton leaf.
            ref mut none => {
                *none = Some(Node::Leaf(Leaf::new(key, val)));
                None
            }
        }
    }
}


#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {}
}
