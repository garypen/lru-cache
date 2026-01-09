use lru::LruCache as OtherCache;
use lru_cache::LruCache;
use rand::prelude::*;
use std::num::NonZeroUsize;

fn main() {
    divan::main();
}

#[divan::bench(args = [8192, 16384, 32768, 65536, 131072, 262144])]
fn my_cache(cache_size: usize) {
    let mut cache = LruCache::new(NonZeroUsize::new(cache_size).expect("cache size > 0"));
    for val in 0..(cache_size * 9 / 10) {
        cache.put(val, val);
    }
    let mut rng = rand::rng();
    for _ in 0..(cache_size / 2) {
        let val = rng.random_range(0..cache_size);
        cache.get(&val);
    }
}

#[divan::bench(args = [8192, 16384, 32768, 65536, 131072, 262144])]
fn other_cache(cache_size: usize) {
    let mut cache = OtherCache::new(NonZeroUsize::new(cache_size).expect("cache size > 0"));
    for val in 0..(cache_size * 9 / 10) {
        cache.put(val, val);
    }
    let mut rng = rand::rng();
    for _ in 0..(cache_size / 2) {
        let val = rng.random_range(0..cache_size);
        cache.get(&val);
    }
}
