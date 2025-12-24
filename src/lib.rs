use ahash::HashMap;
use ahash::HashMapExt;
use std::hash::Hash;
use std::marker::PhantomData;
use std::num::NonZeroUsize;
use std::ptr::NonNull;

#[derive(Debug, PartialEq)]
pub struct Entry<K, V> {
    next: *mut Entry<K, V>,
    prev: *mut Entry<K, V>,
    value: V,
    key: K,
}

impl<K, V> Entry<K, V>
where
    K: std::fmt::Debug,
    V: std::fmt::Debug,
{
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            next: std::ptr::null_mut(),
            prev: std::ptr::null_mut(),
        }
    }

    unsafe fn insert(self_as_ptr: *mut Entry<K, V>, new_ptr: *mut Entry<K, V>) {
        unsafe {
            if !self_as_ptr.is_null() {
                // Fix up self.prev
                if !(*self_as_ptr).prev.is_null() {
                    (*(*self_as_ptr).prev).next = new_ptr;
                }

                // Fix up new_ptr
                (*new_ptr).prev = (*self_as_ptr).prev;
                (*new_ptr).next = self_as_ptr;

                // Fix up self
                (*self_as_ptr).prev = new_ptr;
            }
        }
    }

    unsafe fn remove(self_as_ptr: *mut Entry<K, V>) {
        unsafe {
            // Fix up self.next
            if !(*self_as_ptr).next.is_null() {
                (*(*self_as_ptr).next).prev = (*self_as_ptr).prev;
            }

            // Fix up self.prev
            if !(*self_as_ptr).prev.is_null() {
                (*(*self_as_ptr).prev).next = (*self_as_ptr).next;
            }

            // Cleanup self
            (*self_as_ptr).next = std::ptr::null_mut();
            (*self_as_ptr).prev = std::ptr::null_mut();
        }
    }
}

#[derive(Debug)]
pub struct LruCache<K, V> {
    capacity: usize,
    keys: HashMap<K, NonNull<Entry<K, V>>>,
    head: *mut Entry<K, V>,
    tail: *mut Entry<K, V>,
}

impl<K, V> Drop for LruCache<K, V> {
    fn drop(&mut self) {
        self.keys
            .drain()
            .for_each(|(_key, value)| unsafe { drop(Box::from_raw(value.as_ptr())) });
        self.tail = std::ptr::null_mut();
        self.head = std::ptr::null_mut();
    }
}

impl<K, V> LruCache<K, V>
where
    K: Eq + Hash + Clone + std::fmt::Debug,
    V: Eq + Clone + std::fmt::Debug,
{
    pub fn new(capacity: NonZeroUsize) -> Self {
        let capacity = <NonZeroUsize as Into<usize>>::into(capacity);
        Self {
            capacity,
            keys: HashMap::with_capacity(capacity),
            head: std::ptr::null_mut(),
            tail: std::ptr::null_mut(),
        }
    }

    /// Get the value associated with the supplied key. If the key isn't present return None.
    /// Update the caching sequence to bring the key to the front
    /// O(1)
    #[inline(always)]
    pub fn get(&mut self, key: &K) -> Option<&V> {
        match self.keys.get_mut(key) {
            // If we get a key, then we must already have a head
            Some(value) => unsafe {
                let value_as_ptr = value.as_ptr();
                // Shortcut if we hit HEAD
                if value_as_ptr == self.head {
                    return Some(&(*value_as_ptr).value);
                }
                // Update tail if we hit our tail
                if value_as_ptr == self.tail {
                    self.tail = (*value_as_ptr).prev;
                }
                // Remove from our linked list
                Entry::remove(value_as_ptr);
                // Re-Insert at the head of the list
                Entry::insert(self.head, value_as_ptr);
                // Update our head
                self.head = value_as_ptr;
                Some(&(*value_as_ptr).value)
            },
            None => None,
        }
    }

    /// Put the value associated with the supplied key. If the key is present, return the previous
    /// value.
    /// O(1)
    #[inline(always)]
    pub fn put(&mut self, key: K, value: V) -> Option<V> {
        match self.keys.get_mut(&key) {
            Some(found) => unsafe {
                let found_ref = found.as_mut();
                let old_value = std::mem::replace(&mut found_ref.value, value);
                Some(old_value)
            },
            None => {
                if self.keys.len() == self.capacity {
                    assert!(!self.head.is_null());
                    assert!(!self.tail.is_null());
                    unsafe {
                        // We must find a tail here...
                        // if !self.tail.is_null() {
                        // Identify our tail...
                        let found = self.tail;
                        // If our head == our tail, update head
                        // as well as tail
                        if self.head == self.tail {
                            self.head = (*found).prev;
                        }
                        // Update our tail
                        self.tail = (*found).prev;
                        // Remove from our linked list
                        Entry::remove(found);
                        // Remove from our HashMap
                        self.keys.remove(&(*found).key);
                        // Drop the tail
                        drop(Box::from_raw(found));
                        // }
                    }
                }
                let new = Box::into_raw(Box::new(Entry::new(key.clone(), value)));
                unsafe {
                    if self.head.is_null() {
                        self.head = new;
                        self.tail = new;
                    } else {
                        Entry::insert(self.head, new);
                        self.head = new;
                    }
                    self.keys.insert(key, NonNull::new_unchecked(new));
                }
                None
            }
        }
    }

    pub fn iter(&self) -> impl Iterator<Item = &Entry<K, V>> {
        LruCacheIterator {
            current: self.head,
            phantom: PhantomData,
        }
    }

    pub fn clear(&mut self) {
        self.keys
            .drain()
            .for_each(|(_key, value)| unsafe { drop(Box::from_raw(value.as_ptr())) });
        self.tail = std::ptr::null_mut();
        self.head = std::ptr::null_mut();
    }

    pub fn is_empty(&self) -> bool {
        self.keys.is_empty()
    }

    pub fn len(&self) -> usize {
        self.keys.len()
    }
}

struct LruCacheIterator<'a, K, V> {
    current: *const Entry<K, V>,
    phantom: PhantomData<&'a Entry<K, V>>,
}

impl<'a, K: 'a, V: 'a> Iterator for LruCacheIterator<'a, K, V> {
    type Item = &'a Entry<K, V>;

    fn next(&mut self) -> Option<Self::Item> {
        unsafe {
            let self_as_ptr = std::ptr::from_mut(self);
            if (*self_as_ptr).current.is_null() {
                None
            } else {
                let result = (*self_as_ptr).current.as_ref();
                (*self_as_ptr).current = (*(*self_as_ptr).current).next;
                result
            }
        }
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
        cache.put("bob", "jobb");
        cache.put("bobby", "jobby");

        assert_eq!(cache.len(), 1);
        assert_eq!(cache.get(&"bob"), None);
        assert_eq!(cache.get(&"bobby"), Some(&"jobby"));
    }

    #[test]
    fn it_clears_correctly() {
        let capacity = unsafe { NonZeroUsize::new_unchecked(5) };
        let mut cache = LruCache::new(capacity);
        cache.put("bob", "job");
        cache.put("bob", "jobb");
        assert_eq!(cache.len(), 1);
        cache.clear();
        assert_eq!(cache.len(), 0);
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

        let values: Vec<&str> = cache.iter().map(|entry| entry.value).collect();
        assert_eq!(vec!["F", "E", "D", "C", "B"], values);
    }

    #[test]
    fn it_can_iterate() {
        let capacity = unsafe { NonZeroUsize::new_unchecked(5) };
        let mut cache = LruCache::new(capacity);
        cache.put("a", "A");
        cache.put("b", "B");
        cache.put("c", "C");

        {
            let mut iter = cache.iter();
            assert_eq!(
                iter.next().map(|entry| (entry.key, entry.value)).unwrap(),
                ("c", "C")
            );
            assert_eq!(
                iter.next().map(|entry| (entry.key, entry.value)).unwrap(),
                ("b", "B")
            );
            assert_eq!(
                iter.next().map(|entry| (entry.key, entry.value)).unwrap(),
                ("a", "A")
            );
        }
    }
}
