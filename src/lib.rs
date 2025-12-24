use ahash::HashMap;
use ahash::HashMapExt;
use std::hash::Hash;
use std::marker::PhantomData;
use std::num::NonZeroUsize;
use std::ptr::NonNull;

#[derive(Debug, PartialEq)]
pub(crate) struct Entry<K, V> {
    pub(crate) next: *mut Entry<K, V>,
    pub(crate) prev: *mut Entry<K, V>,
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
            /*
            Some(found) => unsafe {
                let found_ref = found.as_mut();
                let old_value = std::mem::replace(&mut found_ref.value, value);
                Some(old_value)
            },
            */
            Some(found) => unsafe {
                let found_ptr = found.as_ptr();

                // Update the value
                let old_value = std::mem::replace(&mut (*found_ptr).value, value);

                // Promote to head (if not already there)
                if found_ptr != self.head {
                    // Update tail if this was the tail
                    if found_ptr == self.tail {
                        self.tail = (*found_ptr).prev;
                    }

                    Entry::remove(found_ptr);
                    Entry::insert(self.head, found_ptr);
                    self.head = found_ptr;
                }

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

    pub fn contains(&self, key: &K) -> bool {
        self.keys.contains_key(key)
    }

    /// Returns a reference to the value associated with the key without
    /// updating the LRU position.
    pub fn peek(&self, key: &K) -> Option<&V> {
        self.keys
            .get(key)
            .map(|node_ptr| unsafe { &node_ptr.as_ref().value })
    }

    /// Returns the key/value at the head (MRU) without moving it.
    pub fn peek_head(&self) -> Option<(&K, &V)> {
        if self.head.is_null() {
            None
        } else {
            unsafe { Some((&(*self.head).key, &(*self.head).value)) }
        }
    }

    pub fn pop_tail(&mut self) -> Option<(K, V)> {
        if self.tail.is_null() {
            return None;
        }

        unsafe {
            let old_tail = self.tail;

            // Update head/tail pointers
            if self.head == self.tail {
                self.head = std::ptr::null_mut();
                self.tail = std::ptr::null_mut();
            } else {
                self.tail = (*old_tail).prev;
                // Since we're removing the tail, the new tail's 'next' must be null
                if !self.tail.is_null() {
                    (*self.tail).next = std::ptr::null_mut();
                }
            }

            // Remove from HashMap
            self.keys.remove(&(*old_tail).key);

            // Take ownership of the data and drop the node
            let boxed_node = Box::from_raw(old_tail);
            Some((boxed_node.key, boxed_node.value))
        }
    }
    pub fn iter(&self) -> LruCacheIterator<'_, K, V> {
        LruCacheIterator {
            current: self.head,
            phantom: PhantomData,
        }
    }

    pub fn iter_mut(&mut self) -> LruCacheIterMut<'_, K, V> {
        LruCacheIterMut {
            current: self.head,
            phantom: PhantomData,
        }
    }

    pub fn retain<F>(&mut self, mut f: F)
    where
        F: FnMut(&K, &mut V) -> bool,
    {
        let mut current = self.head;
        while !current.is_null() {
            unsafe {
                // We must grab the 'next' pointer BEFORE potentially dropping the node
                let next = (*current).next;

                if !f(&(*current).key, &mut (*current).value) {
                    let to_remove = current;

                    // 1. Update Head/Tail if necessary
                    if to_remove == self.head {
                        self.head = next;
                    }
                    if to_remove == self.tail {
                        self.tail = (*to_remove).prev;
                    }

                    // 2. Stitch the neighbors together
                    Entry::remove(to_remove);

                    // 3. Remove from HashMap
                    self.keys.remove(&(*to_remove).key);

                    // 4. Deallocate memory
                    drop(Box::from_raw(to_remove));
                }
                current = next;
            }
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

impl<K, V> Clone for LruCache<K, V>
where
    K: Eq + Hash + Clone + std::fmt::Debug,
    V: Eq + Clone + std::fmt::Debug,
{
    fn clone(&self) -> Self {
        let mut new_cache = Self::new(NonZeroUsize::new(self.capacity).unwrap());

        // We iterate from the TAIL to the HEAD of the current cache.
        // By using 'put' on the new cache in this order, the items
        // will naturally end up in the correct MRU/LRU positions.
        let mut current = self.tail;
        while !current.is_null() {
            unsafe {
                new_cache.put((*current).key.clone(), (*current).value.clone());
                current = (*current).prev;
            }
        }

        new_cache
    }
}

impl<K, V> PartialEq for LruCache<K, V>
where
    K: Eq + Hash + Clone + std::fmt::Debug,
    V: Eq + Clone + std::fmt::Debug,
{
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false;
        }

        // Compare every element in order (MRU to LRU)
        let mut self_iter = self.iter();
        let mut other_iter = other.iter();

        loop {
            match (self_iter.next(), other_iter.next()) {
                (Some(s), Some(o)) => {
                    if s.0 != o.0 || s.1 != o.1 {
                        return false;
                    }
                }
                (None, None) => return true,
                _ => return false,
            }
        }
    }
}
pub struct LruCacheIterator<'a, K, V> {
    current: *const Entry<K, V>,
    phantom: PhantomData<&'a Entry<K, V>>,
}

impl<'a, K: 'a, V: 'a> Iterator for LruCacheIterator<'a, K, V> {
    type Item = (&'a K, &'a V); // Yield references, not the Entry

    fn next(&mut self) -> Option<Self::Item> {
        if self.current.is_null() {
            None
        } else {
            unsafe {
                let entry = &*self.current;
                self.current = entry.next;
                Some((&entry.key, &entry.value))
            }
        }
    }
}

pub struct LruCacheIterMut<'a, K, V> {
    current: *mut Entry<K, V>,
    phantom: PhantomData<&'a mut Entry<K, V>>,
}

impl<'a, K: 'a, V: 'a> Iterator for LruCacheIterMut<'a, K, V> {
    type Item = (&'a K, &'a mut V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.current.is_null() {
            None
        } else {
            unsafe {
                let entry = &mut *self.current;
                let result = (&entry.key, &mut entry.value);
                self.current = entry.next;
                Some(result)
            }
        }
    }
}

// 1. Immutable: for entry in &cache { ... }
impl<'a, K, V> IntoIterator for &'a LruCache<K, V>
where
    K: Eq + Hash + Clone + std::fmt::Debug,
    V: Eq + Clone + std::fmt::Debug,
{
    type Item = (&'a K, &'a V); // Yield references, not the Entry
    type IntoIter = LruCacheIterator<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

// 2. Mutable: for (key, value) in &mut cache { ... }
impl<'a, K, V> IntoIterator for &'a mut LruCache<K, V>
where
    K: Eq + Hash + Clone + std::fmt::Debug,
    V: Eq + Clone + std::fmt::Debug,
{
    type Item = (&'a K, &'a mut V);
    type IntoIter = LruCacheIterMut<'a, K, V>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter_mut()
    }
}

// 3. Consuming: for (key, value) in cache { ... }
// Note: This one is tricky because it destroys the cache.
// We can implement it by repeatedly calling pop_tail() until empty.
pub struct LruCacheIntoIter<K, V> {
    cache: LruCache<K, V>,
}

impl<K, V> Iterator for LruCacheIntoIter<K, V>
where
    K: Eq + Hash + Clone + std::fmt::Debug,
    V: Eq + Clone + std::fmt::Debug,
{
    type Item = (K, V);

    fn next(&mut self) -> Option<Self::Item> {
        if self.cache.head.is_null() {
            None
        } else {
            unsafe {
                let old_head = self.cache.head;

                // 1. Advance the head
                self.cache.head = (*old_head).next;

                // 2. If the list is now empty, clear the tail too
                if self.cache.head.is_null() {
                    self.cache.tail = std::ptr::null_mut();
                } else {
                    (*self.cache.head).prev = std::ptr::null_mut();
                }

                // 3. Remove from HashMap so len() stays correct (optional but good)
                self.cache.keys.remove(&(*old_head).key);

                // 4. Take ownership and return
                let boxed_node = Box::from_raw(old_head);
                Some((boxed_node.key, boxed_node.value))
            }
        }
    }
}

impl<K, V> IntoIterator for LruCache<K, V>
where
    K: Eq + Hash + Clone + std::fmt::Debug,
    V: Eq + Clone + std::fmt::Debug,
{
    type Item = (K, V);
    type IntoIter = LruCacheIntoIter<K, V>;

    fn into_iter(self) -> Self::IntoIter {
        LruCacheIntoIter { cache: self }
    }
}

impl<K, V> FromIterator<(K, V)> for LruCache<K, V>
where
    K: Eq + Hash + Clone + std::fmt::Debug,
    V: Eq + Clone + std::fmt::Debug,
{
    fn from_iter<T: IntoIterator<Item = (K, V)>>(iter: T) -> Self {
        let items: Vec<(K, V)> = iter.into_iter().collect();
        // We need at least capacity 1 to avoid panics in your current logic
        let capacity = NonZeroUsize::new(items.len()).unwrap_or(NonZeroUsize::new(1).unwrap());

        let mut cache = LruCache::new(capacity);
        for (k, v) in items {
            cache.put(k, v);
        }
        cache
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

        let values: Vec<&str> = cache.iter().map(|entry| *entry.1).collect();
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
                iter.next().map(|entry| (*entry.0, *entry.1)).unwrap(),
                ("c", "C")
            );
            assert_eq!(
                iter.next().map(|entry| (*entry.0, *entry.1)).unwrap(),
                ("b", "B")
            );
            assert_eq!(
                iter.next().map(|entry| (*entry.0, *entry.1)).unwrap(),
                ("a", "A")
            );
        }
    }

    // The remaining tests were generated by Gemini (AI)

    #[test]
    fn it_moves_middle_element_to_head() {
        let capacity = NonZeroUsize::new(3).unwrap();
        let mut cache = LruCache::new(capacity);
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        // Initial order (MRU -> LRU): c, b, a
        // Access "b" (the middle element)
        cache.get(&"b");

        // New order should be: b, c, a
        let order: Vec<&str> = cache.iter().map(|e| *e.0).collect();
        assert_eq!(order, vec!["b", "c", "a"]);
    }

    #[test]
    fn it_evicts_multiple_elements_correctly() {
        let capacity = NonZeroUsize::new(2).unwrap();
        let mut cache = LruCache::new(capacity);

        cache.put(1, "one");
        cache.put(2, "two");
        cache.put(3, "three"); // Evicts 1

        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.len(), 2);

        // Verify tail is now 2
        let order: Vec<i32> = cache.iter().map(|e| *e.0).collect();
        assert_eq!(order, vec![3, 2]);
    }

    #[test]
    fn it_maintains_consistent_back_pointers() {
        let capacity = NonZeroUsize::new(3).unwrap();
        let mut cache = LruCache::new(capacity);
        cache.put(1, 10);
        cache.put(2, 20);
        cache.put(3, 30);

        unsafe {
            let mut curr = cache.tail;
            // Traverse backwards from tail to head
            assert!(!curr.is_null());
            assert_eq!((*curr).key, 1);

            curr = (*curr).prev;
            assert!(!curr.is_null());
            assert_eq!((*curr).key, 2);

            curr = (*curr).prev;
            assert!(!curr.is_null());
            assert_eq!((*curr).key, 3);

            assert!((*curr).prev.is_null()); // Head's prev should be null
        }
    }
    #[test]
    fn it_updates_value_and_promotes_to_head() {
        let capacity = NonZeroUsize::new(3).unwrap();
        let mut cache = LruCache::new(capacity);
        cache.put("a", 1);
        cache.put("b", 2);

        // Order: b, a
        cache.put("a", 100);

        // Now "a" should be the head
        let order: Vec<&str> = cache.iter().map(|e| *e.0).collect();
        assert_eq!(order, vec!["a", "b"]);
        assert_eq!(cache.get(&"a"), Some(&100));
    }

    #[test]
    fn it_handles_repeated_access_ping_pong() {
        let capacity = NonZeroUsize::new(10).unwrap();
        let mut cache = LruCache::new(capacity);
        for i in 0..10 {
            cache.put(i, i);
        }

        // Repeatedly access the same two keys
        for _ in 0..50 {
            cache.get(&0);
            cache.get(&1);
        }

        let order: Vec<i32> = cache.iter().map(|e| *e.0).collect();
        // 1 should be Head (MRU), 0 should be second
        assert_eq!(order[0], 1);
        assert_eq!(order[1], 0);
        assert_eq!(cache.len(), 10);

        // Ensure the tail is still what we expect (the first one put in that wasn't touched)
        // Initial: 9,8,7,6,5,4,3,2,1,0. After get(0),get(1): 1,0,9,8,7,6,5,4,3,2
        assert_eq!(order[9], 2);
    }
    #[test]
    fn it_survives_random_interleaved_ops() {
        let capacity = NonZeroUsize::new(50).unwrap();
        let mut cache = LruCache::new(capacity);

        // 1. Fill it
        for i in 0..100 {
            cache.put(i, i);
        }

        // 2. Random-ish access pattern
        for i in (0..100).step_by(3) {
            cache.get(&i);
        }

        // 3. Partial clear and refill
        for i in 0..25 {
            cache.put(i, i + 1000);
        }

        assert!(cache.len() <= 50);
        // Miri will catch if any of these pointers became dangling during the churn
        for entry in cache.iter() {
            let _pv = entry.1;
        }
    }
    #[test]
    fn it_is_reusable_after_clear() {
        let capacity = NonZeroUsize::new(3).unwrap();
        let mut cache = LruCache::new(capacity);

        cache.put(1, "a");
        cache.put(2, "b");
        cache.clear();

        assert!(cache.is_empty());
        assert!(cache.head.is_null());
        assert!(cache.tail.is_null());

        // Re-fill to see if pointers are still valid
        cache.put(3, "c");
        assert_eq!(cache.get(&3), Some(&"c"));
        assert_eq!(cache.len(), 1);
    }
    #[test]
    fn it_handles_capacity_one_correctly() {
        let capacity = NonZeroUsize::new(1).unwrap();
        let mut cache = LruCache::new(capacity);

        // Fill the single slot
        cache.put("a", 1);
        assert_eq!(cache.get(&"a"), Some(&1));

        // Replace the slot (Eviction)
        cache.put("b", 2);
        assert_eq!(cache.get(&"a"), None);
        assert_eq!(cache.get(&"b"), Some(&2));

        // Update the same slot
        cache.put("b", 3);
        assert_eq!(cache.get(&"b"), Some(&3));

        // Check structural integrity via iteration
        let keys: Vec<&&str> = cache.iter().map(|e| e.0).collect();
        assert_eq!(keys, vec![&"b"]);
    }
    #[test]
    fn it_peeks_without_promoting() {
        let capacity = NonZeroUsize::new(3).unwrap();
        let mut cache = LruCache::new(capacity);
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        // Initial order: c, b, a
        // Peek at "a" (the LRU item)
        assert_eq!(cache.peek(&"a"), Some(&1));

        // Order should STILL be: c, b, a
        let order: Vec<&str> = cache.iter().map(|e| *e.0).collect();
        assert_eq!(order, vec!["c", "b", "a"]);

        // Now use get(&"a") to prove the difference
        cache.get(&"a");
        let order_after_get: Vec<&str> = cache.iter().map(|e| *e.0).collect();
        assert_eq!(order_after_get, vec!["a", "c", "b"]);
    }

    #[test]
    fn it_pops_tail_correctly() {
        let capacity = NonZeroUsize::new(2).unwrap();
        let mut cache = LruCache::new(capacity);
        cache.put("a", 1);
        cache.put("b", 2);

        // LRU is "a"
        let popped = cache.pop_tail();
        assert_eq!(popped, Some(("a", 1)));
        assert_eq!(cache.len(), 1);

        // Verify "b" is now both head and tail
        assert_eq!(cache.get(&"b"), Some(&2));
        assert_eq!(cache.pop_tail(), Some(("b", 2)));
        assert!(cache.is_empty());
    }

    #[test]
    fn it_contains_without_promoting() {
        let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
        cache.put("a", 1);
        cache.put("b", 2);

        // "a" is currently the tail (LRU)
        assert!(cache.contains(&"a"));

        // Put "c", which should evict "a" because "contains" didn't promote it
        cache.put("c", 3);
        assert!(!cache.contains(&"a"));
        assert!(cache.contains(&"b"));
        assert!(cache.contains(&"c"));
    }

    #[test]
    fn it_allows_mutable_iteration() {
        let mut cache = LruCache::new(NonZeroUsize::new(3).unwrap());
        cache.put(1, 10);
        cache.put(2, 20);

        for (_key, value) in cache.iter_mut() {
            *value += 5;
        }

        assert_eq!(cache.get(&1), Some(&15));
        assert_eq!(cache.get(&2), Some(&25));
    }

    #[test]
    fn it_retains_elements_correctly() {
        let mut cache = LruCache::new(NonZeroUsize::new(5).unwrap());
        cache.put(1, 10); // Tail
        cache.put(2, 20);
        cache.put(3, 30);
        cache.put(4, 40);
        cache.put(5, 50); // Head

        // Retain only even keys (2 and 4)
        cache.retain(|&k, _| k % 2 == 0);

        assert_eq!(cache.len(), 2);
        assert_eq!(cache.get(&2), Some(&20));
        assert_eq!(cache.get(&4), Some(&40));
        assert!(!cache.contains(&1));
        assert!(!cache.contains(&3));
        assert!(!cache.contains(&5));

        // Verify structural integrity of head and tail
        unsafe {
            assert_eq!((*cache.head).key, 4);
            assert_eq!((*cache.tail).key, 2);
            assert!((*cache.head).next == cache.tail);
            assert!((*cache.tail).prev == cache.head);
        }
    }

    #[test]
    fn it_handles_retain_empty_result() {
        let mut cache = LruCache::new(NonZeroUsize::new(3).unwrap());
        cache.put(1, 10);
        cache.put(2, 20);

        cache.retain(|_, _| false);

        assert!(cache.is_empty());
        assert!(cache.head.is_null());
        assert!(cache.tail.is_null());
    }

    #[test]
    fn it_clones_deeply() {
        let mut cache = LruCache::new(NonZeroUsize::new(3).unwrap());
        cache.put("a", 1);
        cache.put("b", 2);
        cache.put("c", 3);

        let mut cloned_cache = cache.clone();

        // 1. Verify identical state
        assert_eq!(cloned_cache.len(), 3);
        assert_eq!(
            cache.iter().map(|e| e.0).collect::<Vec<_>>(),
            cloned_cache.iter().map(|e| e.0).collect::<Vec<_>>()
        );

        // 2. Verify independence
        cloned_cache.put("d", 4); // Should evict "a" in clone only
        assert!(cloned_cache.contains(&"d"));
        assert!(!cloned_cache.contains(&"a"));

        assert!(cache.contains(&"a")); // Original should still have "a"
        assert!(!cache.contains(&"d"));
    }

    #[test]
    fn it_compares_equality_and_order() {
        let mut cache_a = LruCache::new(NonZeroUsize::new(3).unwrap());
        let mut cache_b = LruCache::new(NonZeroUsize::new(3).unwrap());

        cache_a.put("x", 1);
        cache_a.put("y", 2);

        cache_b.put("x", 1);
        cache_b.put("y", 2);

        // Should be equal initially
        assert_eq!(cache_a, cache_b);

        // Access "x" in cache_a to move it to head
        cache_a.get(&"x");

        // Now they have the same data but different order:
        // cache_a: x, y
        // cache_b: y, x
        assert_ne!(cache_a, cache_b);
    }

    #[test]
    fn it_works_with_for_loops() {
        let mut cache = LruCache::new(NonZeroUsize::new(2).unwrap());
        cache.put("a", 1);
        cache.put("b", 2);

        // Test &LruCache
        let mut count = 0;
        for entry in &cache {
            assert!(*entry.1 > 0);
            count += 1;
        }
        assert_eq!(count, 2);

        // Test &mut LruCache
        for (key, value) in &mut cache {
            if *key == "a" {
                *value = 100;
            }
        }
        assert_eq!(cache.get(&"a"), Some(&100));

        // Test consuming LruCache
        let mut vec = Vec::new();
        for (key, value) in cache {
            vec.push((key, value));
        }
        // pop_tail yields from the back, so order is a, then b
        assert_eq!(vec, vec![("a", 100), ("b", 2)]);
    }

    #[test]
    fn it_collects_from_iterator() {
        let data = vec![("a", 1), ("b", 2), ("c", 3)];
        let cache: LruCache<&str, i32> = data.into_iter().collect();

        assert_eq!(cache.len(), 3);
        // Since we put them in order a, b, c... 'c' should be the head
        assert_eq!(cache.peek_head(), Some((&"c", &3)));

        // Verify order
        let order: Vec<&str> = cache.iter().map(|e| *e.0).collect();
        assert_eq!(order, vec!["c", "b", "a"]);
    }
}
