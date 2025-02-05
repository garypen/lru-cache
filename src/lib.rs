use std::collections::VecDeque;
use std::num::NonZeroUsize;

type KVPair<K, V> = (K, V);

pub struct LruCache<K, V> {
    capacity: usize,
    entries: VecDeque<KVPair<K, V>>,
}

impl<K, V> LruCache<K, V>
where
    K: Eq,
{
    pub fn new(capacity: NonZeroUsize) -> Self {
        let capacity = capacity.into();
        Self {
            capacity,
            entries: VecDeque::with_capacity(capacity),
        }
    }

    /// Get the value associated with the supplied key. If the key isn't present return None.
    /// Update the caching sequence to bring the key to the front
    /// O(n)
    pub fn get(&mut self, key: &K) -> Option<&V> {
        let at_index = self
            .entries
            .iter()
            .position(|(entry_key, _entry_value)| entry_key == key);

        match at_index {
            Some(idx) => {
                // Small optimisation to avoid removing/pushing element 0
                if idx != 0 {
                    let pair = self
                        .entries
                        .remove(idx)
                        .expect("must be present; invariant");
                    self.entries.push_front(pair);
                }
                self.entries.front().map(|(_key, value)| value)
            }
            None => None,
        }
    }

    /// Put the value associated with the supplied key. If the key is present, return the previous
    /// value.
    /// O(n)
    pub fn put(&mut self, key: K, value: V) -> Option<V> {
        let at_index = self
            .entries
            .iter()
            .position(|(entry_key, _entry_value)| entry_key == &key);

        match at_index {
            Some(idx) => {
                // Small optimisation to avoid removing/pushing element 0
                let mut old_v;
                if idx == 0 {
                    old_v = value;
                    let pair = self
                        .entries
                        .front_mut()
                        .expect("must be present; invariant");
                    std::mem::swap(&mut old_v, &mut pair.1);
                } else {
                    let mut pair = self
                        .entries
                        .remove(idx)
                        .expect("must be present; invariant");
                    old_v = pair.1;
                    pair.1 = value;
                    self.entries.push_front(pair);
                }
                Some(old_v)
            }
            None => {
                // Only need to check limit if key isn't already present
                if self.entries.len() == self.capacity {
                    let _ = self.entries.pop_back();
                }
                self.entries.push_front((key, value));
                None
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &KVPair<K, V>> {
        self.entries.iter()
    }

    pub fn clear(&mut self) {
        self.entries.clear()
    }

    pub fn is_empty(&self) -> bool {
        self.entries.is_empty()
    }

    pub fn len(&self) -> usize {
        self.entries.len()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_stores_one_element() {
        let capacity = unsafe { NonZeroUsize::new_unchecked(1) };
        let mut cache = LruCache::new(capacity);
        cache.put("bob", "job");
        cache.put("bob", "job");
        cache.put("bobby", "jobby");

        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&"bob"), None);
        assert_eq!(cache.get(&"bobby"), Some(&"jobby"));
    }

    #[test]
    fn it_stores_five_elements() {
        let capacity = unsafe { NonZeroUsize::new_unchecked(5) };
        let mut cache = LruCache::new(capacity);
        cache.put("a", "A");
        cache.put("b", "B");
        cache.put("c", "C");
        cache.put("d", "D");
        cache.put("e", "E");
        cache.put("f", "F");

        assert_eq!(cache.len(), 5);
        assert_eq!(cache.get(&"a"), None);
        assert_eq!(cache.get(&"b"), Some(&"B"));
        assert_eq!(cache.get(&"c"), Some(&"C"));
        assert_eq!(cache.get(&"d"), Some(&"D"));
        assert_eq!(cache.get(&"e"), Some(&"E"));
        assert_eq!(cache.get(&"f"), Some(&"F"));
        let values: Vec<&str> = cache.iter().map(|&(_key, value)| value).collect();
        assert_eq!(vec!["F", "E", "D", "C", "B"], values);
    }

    #[test]
    fn it_can_iterate() {
        let capacity = unsafe { NonZeroUsize::new_unchecked(5) };
        let mut cache = LruCache::new(capacity);
        cache.put("a", "A");
        cache.put("b", "B");
        cache.put("c", "C");

        let mut iter = cache.iter();
        assert_eq!(iter.next().unwrap(), &("c", "C"));
        assert_eq!(iter.next().unwrap(), &("b", "B"));
        assert_eq!(iter.next().unwrap(), &("a", "A"));
    }
}
