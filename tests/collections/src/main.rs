#![feature(allocator_api)]

use std::sync::Once;

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

    test_vec_random_ops();
    test_vec_large_elements();
    test_vec_strings();
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
