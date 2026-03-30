#![feature(allocator_api)]

use std::sync::Once;

use deko_core::collections::String as DekoString;
use deko_core::mm::frame_allocator::DekoAllocatorApi;
use deko_core::mm::DEKO_FRAME_ALLOCATOR_FULL;
use proptest::prelude::*;
use indicatif::{ProgressBar, ProgressStyle};

static INIT: Once = Once::new();
static mut HEAP_BUFFER: Option<Vec<u8>> = None;

#[derive(Debug, Clone)]
enum VecOp<T> {
    Push(T),
    Pop,
    Insert { index: usize, value: T },
    Remove { index: usize },
    Clear,
    Extend(Vec<T>),
    Reserve(usize),
}

fn vec_ops_strategy<T: Clone + std::fmt::Debug + 'static>(
    value_strategy: impl Strategy<Value = T> + Clone,
    num_ops: std::ops::Range<usize>,
) -> impl Strategy<Value = Vec<VecOp<T>>> + Clone {
    prop::collection::vec(
        prop_oneof![
            5 => value_strategy.clone().prop_map(VecOp::Push),
            2 => Just(VecOp::Pop),
            2 => (any::<usize>(), value_strategy.clone())
                .prop_map(|(idx, val)| VecOp::Insert { index: idx, value: val }),
            2 => any::<usize>().prop_map(|idx| VecOp::Remove { index: idx }),
            1 => Just(VecOp::Clear),
            3 => prop::collection::vec(value_strategy.clone(), 0..20)
                .prop_map(VecOp::Extend),
            1 => (1usize..1000).prop_map(VecOp::Reserve),
        ],
        num_ops,
    )
}

/// Align an address up to the specified alignment
fn align_up(addr: u64, align: u64) -> u64 { (addr + align - 1) & !(align - 1) }

/// Create an aligned heap buffer
/// Returns (buffer, aligned_start, aligned_length)
fn create_aligned_heap(size: usize, alignment: usize) -> (Vec<u8>, u64, u64) {
    // Allocate extra space to ensure we can find an aligned region
    let total_size = size + alignment;
    let mut buffer = vec![0u8; total_size];

    let raw_start = buffer.as_ptr() as u64;
    let aligned_start = align_up(raw_start, alignment as u64);

    // Calculate how much usable space we have after alignment
    let offset = (aligned_start - raw_start) as usize;
    let aligned_length = (total_size - offset) as u64;

    // Make sure we have at least the requested size
    assert!(
        aligned_length >= size as u64,
        "Not enough space after alignment: got {:#x}, need {:#x}",
        aligned_length,
        size
    );

    (buffer, aligned_start, aligned_length.min(size as u64))
}

/// Initialize the global allocator once
fn setup_allocator() {
    INIT.call_once(|| {
        unsafe {
            // Create a large heap for all tests (256MB)
            let total_size = 0x10000000 + 0x10000; // 256MB + alignment
            let mut buffer = vec![0u8; total_size];

            let raw_start = buffer.as_ptr() as u64;
            let aligned_start = align_up(raw_start, 0x10000);

            let offset = (aligned_start - raw_start) as usize;
            let aligned_length = (total_size - offset) as u64;

            println!(
                "Initializing global allocator: raw_start={:#x}, aligned_start={:#x}, aligned_length={:#x}",
                raw_start, aligned_start, aligned_length
            );
            DEKO_FRAME_ALLOCATOR_FULL.init(aligned_start, aligned_length);

            // Keep buffer alive forever
            HEAP_BUFFER = Some(buffer);

            println!(
                "✓ Global allocator initialized: start={:#x}, size={:#x}",
                aligned_start, aligned_length
            );
        }
    });
}

fn main() {
    println!("Running collection tests...");

    test_monitor_heap_geometry_vec_growth();
    test_vec_random_ops();
    test_vec_large_elements();
    test_vec_strings();
    test_vec_growth_churn();
    test_vec_string_growth_churn();
    test_vec_byte_push_growth();
    test_nested_vec_reallocation();
    test_string_push_and_pop();
    test_string_reserve_and_clear();
}

fn test_monitor_heap_geometry_vec_growth() {
    const HEAP_SIZE: usize = 0x400000;
    const HEAP_ALIGN: usize = 0x1000;

    let (_buffer, heap_start, heap_len) = create_aligned_heap(HEAP_SIZE, HEAP_ALIGN);
    let allocator = deko_core::mm::frame_allocator::DekoPageFrameAllocator::<18>::new();
    allocator.init(heap_start, heap_len);

    let mut v_deko = Vec::<u8, _>::new_in(allocator.0);
    let mut v_std = Vec::<u8>::new();

    for round in 0..64usize {
        let target_len = 64 + round * 13;

        for i in 0..target_len {
            let byte = ((round * 97 + i) & 0xff) as u8;
            v_deko.push(byte);
            v_std.push(byte);
        }

        assert_eq!(v_deko.as_slice(), v_std.as_slice());

        for _ in 0..(target_len / 2) {
            assert_eq!(v_deko.pop(), v_std.pop());
        }
    }
}

fn test_vec_growth_churn() {
    setup_allocator();

    let rounds = 128usize;
    let base_len = 4096usize;
    let extra_len = 2048usize;

    let mut v_deko = Vec::<u64, _>::new_in(DekoAllocatorApi {});
    let mut v_std = Vec::<u64>::new();

    for round in 0..rounds {
        for i in 0..base_len {
            let value = ((round as u64) << 32) | i as u64;
            v_deko.push(value);
            v_std.push(value);
        }

        v_deko.reserve(extra_len + round);
        v_std.reserve(extra_len + round);

        for i in 0..extra_len {
            let value = (!round as u64) ^ i as u64;
            v_deko.push(value);
            v_std.push(value);
        }

        assert_eq!(v_deko.len(), v_std.len());
        assert_eq!(v_deko.as_slice(), v_std.as_slice());

        for _ in 0..(base_len + extra_len) / 2 {
            assert_eq!(v_deko.pop(), v_std.pop());
        }

        v_deko.shrink_to_fit();
        v_std.shrink_to_fit();

        assert_eq!(v_deko.as_slice(), v_std.as_slice());

        v_deko.clear();
        v_std.clear();

        v_deko.shrink_to_fit();
        v_std.shrink_to_fit();

        assert_eq!(v_deko.len(), 0);
        assert_eq!(v_std.len(), 0);
    }
}

fn test_vec_string_growth_churn() {
    setup_allocator();

    let mut v_deko = Vec::<String, _>::new_in(DekoAllocatorApi {});
    let mut v_std = Vec::<String>::new();

    for round in 0..64usize {
        v_deko.reserve(128 + round);
        v_std.reserve(128 + round);

        for i in 0..256usize {
            let payload = format!(
                "round={round}:index={i}:payload={}",
                "x".repeat(256 + (i % 17))
            );
            v_deko.push(payload.clone());
            v_std.push(payload);
        }

        assert_eq!(v_deko.as_slice(), v_std.as_slice());

        for _ in 0..192usize {
            assert_eq!(v_deko.pop(), v_std.pop());
        }

        v_deko.shrink_to_fit();
        v_std.shrink_to_fit();

        assert_eq!(v_deko.as_slice(), v_std.as_slice());

        v_deko.clear();
        v_std.clear();
    }
}

fn test_nested_vec_reallocation() {
    setup_allocator();

    let mut outer = Vec::<Vec<u8, DekoAllocatorApi>, _>::new_in(DekoAllocatorApi {});

    for round in 0..96usize {
        let mut inner = Vec::<u8, _>::new_in(DekoAllocatorApi {});
        inner.reserve(1024 + round * 3);

        for i in 0..(2048 + round * 8) {
            inner.push(((round + i) & 0xff) as u8);
        }

        assert_eq!(inner.len(), 2048 + round * 8);
        outer.push(inner);

        if outer.len() % 8 == 0 {
            let removed = outer.remove(0);
            assert!(!removed.is_empty());
        }
    }

    while let Some(mut inner) = outer.pop() {
        let original_len = inner.len();
        inner.truncate(original_len / 2);
        inner.shrink_to_fit();
        assert_eq!(inner.len(), original_len / 2);
    }
}

fn test_vec_byte_push_growth() {
    setup_allocator();

    let mut v_deko = Vec::<u8, _>::new_in(DekoAllocatorApi {});
    let mut v_std = Vec::<u8>::new();

    for round in 0..256usize {
        let target_len = 1024 + round * 37;

        for i in 0..target_len {
            let byte = ((round * 131 + i) & 0xff) as u8;
            v_deko.push(byte);
            v_std.push(byte);
        }

        assert_eq!(v_deko.as_slice(), v_std.as_slice());

        for _ in 0..(target_len / 3) {
            assert_eq!(v_deko.pop(), v_std.pop());
        }

        assert_eq!(v_deko.as_slice(), v_std.as_slice());
    }

    while !v_std.is_empty() {
        assert_eq!(v_deko.pop(), v_std.pop());
    }

    assert!(v_deko.is_empty());
}

fn test_string_push_and_pop() {
    setup_allocator();

    let mut s_deko = DekoString::new_in(DekoAllocatorApi {});
    let mut s_std = String::new();

    for round in 0..64usize {
        let chunk = format!("round={round}:{}", "x".repeat(32 + (round % 11)));

        s_deko.push_str(&chunk);
        s_std.push_str(&chunk);

        let ch = char::from_u32('a' as u32 + (round % 26) as u32).unwrap();
        s_deko.push(ch);
        s_std.push(ch);

        assert_eq!(s_deko.as_str(), s_std.as_str());
        assert_eq!(s_deko.char_len(), s_std.chars().count());
    }

    for _ in 0..40usize {
        assert_eq!(s_deko.pop(), s_std.pop());
        assert_eq!(s_deko.as_str(), s_std.as_str());
    }
}

fn test_string_reserve_and_clear() {
    setup_allocator();

    let mut s_deko = DekoString::with_capacity_in(16, DekoAllocatorApi {});

    assert!(s_deko.is_empty());
    assert_eq!(s_deko.as_str(), "");

    for round in 0..32usize {
        s_deko.reserve(64 + round);
        s_deko.push_str("payload:");
        s_deko.push(char::from_u32('0' as u32 + (round % 10) as u32).unwrap());
    }

    assert!(!s_deko.is_empty());
    assert!(s_deko.capacity() >= s_deko.len());
    assert!(s_deko.as_str().starts_with("payload:"));

    s_deko.clear();

    assert!(s_deko.is_empty());
    assert_eq!(s_deko.as_str(), "");
}

proptest! {
    fn test_vec_random_ops(ops in vec_ops_strategy(any::<i32>(), 0..100)) {
        use std::sync::Once;
        static INIT: Once = Once::new();
        static mut PROGRESS_BAR: Option<ProgressBar> = None;
        static COUNTER: std::sync::atomic::AtomicUsize = std::sync::atomic::AtomicUsize::new(0);

        // Initialize progress bar once
        INIT.call_once(|| {
            let pb = ProgressBar::new(1000);  // Default proptest cases
            pb.set_style(ProgressStyle::with_template(
                "[{bar:40.green/blue}] {pos:>7}/{len:7} Vector random ops {msg}"
            ).unwrap().progress_chars("##-"));
            pb.set_message("Running...");
            unsafe { PROGRESS_BAR = Some(pb); }
        });

        // Increment counter and update progress
        let current = COUNTER.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        unsafe {
            if let Some(ref pb) = PROGRESS_BAR {
                pb.set_position(current as u64);
                if current >= 999 {
                    pb.finish_with_message("✓ Complete");
                }
            }
        }

        setup_allocator();

        let mut v_deko = Vec::<i32, _>::new_in(DekoAllocatorApi {});
        let mut v_std = Vec::<i32>::new();

        for op in ops {
            match op {
                VecOp::Push(val) => {
                    v_deko.push(val);
                    v_std.push(val);
                }
                VecOp::Pop => {
                    let r_deko = v_deko.pop();
                    let r_std = v_std.pop();
                    prop_assert_eq!(r_deko, r_std);
                }
                VecOp::Insert { index, value } => {
                    if !v_deko.is_empty() {
                        let idx = index % (v_deko.len() + 1);
                        v_deko.insert(idx, value);
                        v_std.insert(idx, value);
                    }
                }
                VecOp::Remove { index } => {
                    if !v_deko.is_empty() {
                        let idx = index % v_deko.len();
                        let r_deko = v_deko.remove(idx);
                        let r_std = v_std.remove(idx);
                        prop_assert_eq!(r_deko, r_std);
                    }
                }
                VecOp::Clear => {
                    v_deko.clear();
                    v_std.clear();
                }
                VecOp::Extend(vals) => {
                    v_deko.extend(vals.iter().copied());
                    v_std.extend(vals.iter().copied());
                }
                VecOp::Reserve(cap) => {
                    v_deko.reserve(cap);
                    v_std.reserve(cap);
                }
            }

            // Invariants
            prop_assert_eq!(v_deko.len(), v_std.len());
            prop_assert_eq!(v_deko.is_empty(), v_std.is_empty());

            // Content should match
            for (i, (&val_deko, &val_std)) in v_deko.iter().zip(v_std.iter()).enumerate() {
                prop_assert_eq!(val_deko, val_std, "Mismatch at index {}", i);
            }
        }
    }

    fn test_vec_large_elements(ops in vec_ops_strategy(any::<[u64; 16]>(), 0..100)) {
        setup_allocator();

        let mut v = Vec::<[u64; 16], _>::new_in(DekoAllocatorApi {});

        for op in ops {
            match op {
                VecOp::Push(val) => v.push(val),
                VecOp::Pop => { v.pop(); }
                VecOp::Insert { index, value } => {
                    if !v.is_empty() {
                        let idx = index % (v.len() + 1);
                        v.insert(idx, value);
                    }
                }
                VecOp::Remove { index } => {
                    if !v.is_empty() {
                        let idx = index % v.len();
                        v.remove(idx);
                    }
                }
                VecOp::Clear => v.clear(),
                VecOp::Extend(vals) => v.extend(vals),
                VecOp::Reserve(cap) => v.reserve(cap),
            }
        }

        prop_assert!(v.capacity() > 0 || v.is_empty());
    }

    fn test_vec_strings(ops in vec_ops_strategy(any::<String>(), 0..100)) {
        setup_allocator();

        let mut v = Vec::<String, _>::new_in(DekoAllocatorApi {});

        for op in ops {
            match op {
                VecOp::Push(val) => v.push(val),
                VecOp::Pop => { v.pop(); }
                VecOp::Clear => v.clear(),
                VecOp::Extend(vals) => v.extend(vals),
                _ => {}
            }
        }
    }
}
