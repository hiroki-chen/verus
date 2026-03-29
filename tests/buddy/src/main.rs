//! As it is really hard to debug the memory allocation before the logging system
//! is up, we create a simple test here to verify the buddy allocator works as expected.
//!
//! Why does formal verification not cover this?
//!
//! 1. The buddy allocator assumes a lot of `unsafe` code and low-level system details
//!    that are hard to model in Verus.
//! 2. Some Rust trait creates "hidden" connection between allocation and high-level
//!    data structures like [`alloc::vec::Vec`] that are not easy to specify formally.
//!
//! For example, consider we created a heap from `[0x0, 0x1000]` which is invalid
//! memory region in real system. Then we allocate a `Vec` from this heap. Even if
//! the heap itself is formally verified to be correct, the `Vec` will try to
//! dereference the pointer returned from the heap which leads to undefined behavior
//! in real system as we _assume_ this memory makes sense.
//!
//! This test suite is designed to capture such edge cases where the formal verification
//! might miss, by running the buddy allocator in a controlled environment and checking
//! its behavior with real memory allocations.
use deko_std::mem::{valid_heap_param_impl, DekoHeap, DekoHeapPredicate, Heap};
use proptest::prelude::*;
use vstd::prelude::*;
use indicatif::{ProgressBar, ProgressStyle};
use std::sync::atomic::{AtomicUsize, Ordering};
use std::sync::Arc;

// Strategy for generating allocation sizes (powers of 2, typical for buddy)
fn alloc_size_strategy() -> impl Strategy<Value = u64> {
    prop_oneof![
        Just(0x1000u64),  // 4KB
        Just(0x2000u64),  // 8KB
        Just(0x4000u64),  // 16KB
        Just(0x8000u64),  // 32KB
        Just(0x10000u64), // 64KB
        Just(0x20000u64), // 128KB
    ]
}

// Strategy for alignment (also powers of 2)
fn align_strategy() -> impl Strategy<Value = u64> {
    prop_oneof![Just(0x1000u64), Just(0x2000u64), Just(0x4000u64),]
}

// Generate a sequence of allocation operations
fn alloc_ops_strategy() -> impl Strategy<Value = Vec<AllocOp>> {
    prop::collection::vec(
        prop_oneof![
            // 70% chance of allocation
            7 => (alloc_size_strategy(), align_strategy())
                .prop_map(|(size, align)| AllocOp::Alloc { size, align }),
            // 30% chance of free
            3 => any::<u64>()
                .prop_map(|index| AllocOp::Free { index }),
        ],
        20..100, // Generate 20-100 operations
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

// Define allocation operations
#[derive(Debug, Clone)]
enum AllocOp {
    Alloc { size: u64, align: u64 },
    Free { index: u64 },
}

verus! {

#[verifier::external_body]
fn main() {
    // Run proptest manually or via cargo test
    test_buddy_coalescing_regression();
    test_random_alloc_free();
    test_no_overlap();
    test_memory_reuse();
    test_out_of_memory();
    test_fragmentation();
    test_repro_heap_size_14();
}

} // verus!

fn test_buddy_coalescing_regression() {
    const HEAP_SIZE: usize = 0x2000;
    const HEAP_ALIGN: usize = 0x1000;

    for free_right_first in [true, false] {
        let (_buffer, heap_start, heap_len) = create_aligned_heap(HEAP_SIZE, HEAP_ALIGN);
        let mut allocator = DekoHeap::<2>::new(Ghost::assume_new());
        allocator.init(heap_start, heap_len, 2);

        let left = allocator.allocate(0x1000, 0x1000);
        let right = allocator.allocate(0x1000, 0x1000);

        assert_ne!(left, 0, "left half allocation failed");
        assert_ne!(right, 0, "right half allocation failed");
        assert_ne!(left, right, "expected two distinct buddy blocks");

        if free_right_first {
            allocator.deallocate(right, 0x1000, 0x1000);
            allocator.deallocate(left, 0x1000, 0x1000);
        } else {
            allocator.deallocate(left, 0x1000, 0x1000);
            allocator.deallocate(right, 0x1000, 0x1000);
        }

        let merged = allocator.allocate(0x2000, 0x1000);
        assert_eq!(
            merged,
            heap_start,
            "expected buddy blocks to coalesce back into the full heap; free_right_first={free_right_first}",
        );

        allocator.deallocate(merged, 0x2000, 0x1000);
    }
}

proptest! {
    #![proptest_config(ProptestConfig {
        cases: 10000,  // More test cases
        max_shrink_iters: 10000,
        .. ProptestConfig::default()
    })]

    fn test_random_alloc_free(ops in alloc_ops_strategy()) {
        use std::sync::Once;
        static INIT: Once = Once::new();
        static mut PROGRESS_BAR: Option<ProgressBar> = None;
        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        // Initialize progress bar once
        INIT.call_once(|| {
            let pb = ProgressBar::new(10000);
            pb.set_style(ProgressStyle::with_template(
                "[{bar:40.cyan/blue}] {pos:>7}/{len:7} Random alloc/free tests {msg}"
            ).unwrap().progress_chars("##-"));
            pb.set_message("Running...");
            unsafe { PROGRESS_BAR = Some(pb); }
        });

        // Increment counter and update progress
        let current = COUNTER.fetch_add(1, Ordering::Relaxed);
        unsafe {
            if let Some(ref pb) = PROGRESS_BAR {
                pb.set_position(current as u64);
                if current == 9999 {
                    pb.finish_with_message("✓ Complete");
                }
            }
        }

        const HEAP_SIZE: usize = 0x1000000; // 16MB heap
        const HEAP_ALIGN: usize = 0x10000;  // 64KB alignment (typical page size)

        let (_buffer, heap_start, heap_len) = create_aligned_heap(HEAP_SIZE, HEAP_ALIGN);

        // Verify the heap is properly aligned
        prop_assert_eq!(
            heap_start % (HEAP_ALIGN as u64),
            0,
            "Heap start not aligned: {:#x}",
            heap_start
        );

        let mut allocator = DekoHeap::<20>::new(Ghost::assume_new());
        allocator.init(heap_start, heap_len, 20);
        let mut allocations: Vec<(u64, u64, u64)> = Vec::new();

        for op in ops {
            match op {
                AllocOp::Alloc { size, align } => {
                    let addr = allocator.allocate(size, align);
                    if addr != 0 {
                        // Verify alignment
                        prop_assert_eq!(
                            addr % align,
                            0,
                            "Allocation not properly aligned: addr={:#x}, align={:#x}",
                            addr, align
                        );
                        // Verify it's within heap bounds
                        prop_assert!(
                            addr >= heap_start && addr + size <= heap_start + heap_len,
                            "Allocation outside heap bounds: addr={:#x}, size={:#x}, heap=[{:#x}, {:#x})",
                            addr, size, heap_start, heap_start + heap_len
                        );
                        allocations.push((addr, size, align));
                    }
                }
                AllocOp::Free { index } => {
                    if !allocations.is_empty() {
                        let idx = (index as usize) % allocations.len();
                        let (addr, size, align) = allocations.remove(idx);
                        allocator.deallocate(addr, size, align);
                    }
                }
            }
        }

        // Cleanup: free all remaining allocations
        for (addr, size, align) in allocations {
            allocator.deallocate(addr, size, align);
        }
    }

    fn test_no_overlap(ops in alloc_ops_strategy()) {
        use std::sync::Once;
        static INIT: Once = Once::new();
        static mut PROGRESS_BAR: Option<ProgressBar> = None;
        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        // Initialize progress bar once
        INIT.call_once(|| {
            let pb = ProgressBar::new(10000);
            pb.set_style(ProgressStyle::with_template(
                "[{bar:40.yellow/blue}] {pos:>7}/{len:7} No overlap verification {msg}"
            ).unwrap().progress_chars("##-"));
            pb.set_message("Running...");
            unsafe { PROGRESS_BAR = Some(pb); }
        });

        // Increment counter and update progress
        let current = COUNTER.fetch_add(1, Ordering::Relaxed);
        unsafe {
            if let Some(ref pb) = PROGRESS_BAR {
                pb.set_position(current as u64);
                if current == 9999 {
                    pb.finish_with_message("✓ Complete");
                }
            }
        }

        const HEAP_SIZE: usize = 0x2000000; // 32MB heap for overlap test
        const HEAP_ALIGN: usize = 0x10000;  // 64KB alignment

        let (_buffer, heap_start, heap_len) = create_aligned_heap(HEAP_SIZE, HEAP_ALIGN);

        let mut allocator = DekoHeap::<20>::new(Ghost::assume_new());
        allocator.init(heap_start, heap_len, 20);

        let mut allocations: Vec<(u64, u64, u64)> = Vec::new();

        for op in ops {
            match op {
                AllocOp::Alloc { size, align } => {
                    let addr = allocator.allocate(size, align);
                    if addr != 0 {
                        // Check no overlap with existing allocations
                        for &(existing_addr, existing_size, _) in &allocations {
                            let new_end = addr + size;
                            let existing_end = existing_addr + existing_size;
                            let overlap = !(new_end <= existing_addr || existing_end <= addr);

                            prop_assert!(
                                !overlap,
                                "Allocation overlaps: new=[{:#x}, {:#x}), existing=[{:#x}, {:#x})",
                                addr, new_end, existing_addr, existing_end
                            );
                        }
                        allocations.push((addr, size, align));
                    }
                }
                AllocOp::Free { index } => {
                    if !allocations.is_empty() {
                        let idx = (index as usize) % allocations.len();
                        let (addr, size, align) = allocations.remove(idx);
                        allocator.deallocate(addr, size, align);
                    }
                }
            }
        }

        for (addr, size, align) in allocations {
            allocator.deallocate(addr, size, align);
        }
    }

    fn test_memory_reuse(
        size in alloc_size_strategy(),
        align in align_strategy(),
    ) {
        use std::sync::Once;
        static INIT: Once = Once::new();
        static mut PROGRESS_BAR: Option<ProgressBar> = None;
        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        // Initialize progress bar once (smaller case count for parameterized tests)
        INIT.call_once(|| {
            let pb = ProgressBar::new(10000); // 6 sizes * 6 aligns * 20 iterations 
            pb.set_style(ProgressStyle::with_template(
                "[{bar:40.green/blue}] {pos:>7}/{len:7} Memory reuse patterns {msg}"
            ).unwrap().progress_chars("##-"));
            pb.set_message("Running...");
            unsafe { PROGRESS_BAR = Some(pb); }
        });

        // Increment counter and update progress
        let current = COUNTER.fetch_add(1, Ordering::Relaxed);
        unsafe {
            if let Some(ref pb) = PROGRESS_BAR {
                pb.set_position(current as u64);
                if current >= 9999 {
                    pb.finish_with_message("✓ Complete");
                }
            }
        }

        const HEAP_SIZE: usize = 0x200000;
        const HEAP_ALIGN: usize = 0x10000;

        let (_buffer, heap_start, heap_len) = create_aligned_heap(HEAP_SIZE, HEAP_ALIGN);

        let mut allocator = DekoHeap::<18>::new(Ghost::assume_new());

        allocator.init(heap_start, heap_len, 18);
        
        // panic!("allocator.min_block_size == {}", allocator.min_block_size);
        // First allocation
        let addr1 = allocator.allocate(size, align);
        prop_assert_ne!(addr1, 0, "Initial allocation failed");

        // Free it
        allocator.deallocate(addr1, size, align);

        // Allocate again with same size - should reuse the same block
        let addr2 = allocator.allocate(size, align);
        prop_assert_eq!(
            addr1,
            addr2,
            "Freed memory not reused: first={:#x}, second={:#x}",
            addr1,
            addr2
        );

        allocator.deallocate(addr2, size, align);
    }

    fn test_out_of_memory(_ in alloc_ops_strategy()) {
        use std::sync::Once;
        static INIT: Once = Once::new();
        static mut PROGRESS_BAR: Option<ProgressBar> = None;
        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        // Initialize progress bar once
        INIT.call_once(|| {
            let pb = ProgressBar::new(10000);
            pb.set_style(ProgressStyle::with_template(
                "[{bar:40.red/blue}] {pos:>7}/{len:7} Out of memory tests {msg}"
            ).unwrap().progress_chars("##-"));
            pb.set_message("Running...");
            unsafe { PROGRESS_BAR = Some(pb); }
        });

        // Increment counter and update progress
        let current = COUNTER.fetch_add(1, Ordering::Relaxed);
        unsafe {
            if let Some(ref pb) = PROGRESS_BAR {
                pb.set_position(current as u64);
                if current == 9999 {
                    pb.finish_with_message("✓ Complete");
                }
            }
        }

        const HEAP_SIZE: usize = 0x200000; // Small heap
        const HEAP_ALIGN: usize = 0x10000;

        let (_buffer, heap_start, heap_len) = create_aligned_heap(HEAP_SIZE, HEAP_ALIGN);
        let mut allocator = DekoHeap::<20>::new(Ghost::assume_new());
        allocator.init(heap_start, heap_len, 20);

        // Fill the heap
        let addr1 = allocator.allocate(0x100000, 0x1000);
        assert_ne!(addr1, 0);

        let addr2 = allocator.allocate(0x100000, 0x1000);
        assert_ne!(addr2, 0);

        // This should fail
        let addr3 = allocator.allocate(0x1000, 0x1000);
        assert_eq!(addr3, 0, "Expected allocation to fail when heap is full");

        // Cleanup
        allocator.deallocate(addr1, 0x100000, 0x1000);
        allocator.deallocate(addr2, 0x100000, 0x1000);
    }

    fn test_fragmentation(_ in alloc_ops_strategy()) {
        use std::sync::Once;
        static INIT: Once = Once::new();
        static mut PROGRESS_BAR: Option<ProgressBar> = None;
        static COUNTER: AtomicUsize = AtomicUsize::new(0);

        // Initialize progress bar once
        INIT.call_once(|| {
            let pb = ProgressBar::new(10000);
            pb.set_style(ProgressStyle::with_template(
                "[{bar:40.magenta/blue}] {pos:>7}/{len:7} Fragmentation tests {msg}"
            ).unwrap().progress_chars("##-"));
            pb.set_message("Running...");
            unsafe { PROGRESS_BAR = Some(pb); }
        });

        // Increment counter and update progress
        let current = COUNTER.fetch_add(1, Ordering::Relaxed);
        unsafe {
            if let Some(ref pb) = PROGRESS_BAR {
                pb.set_position(current as u64);
                if current == 9999 {
                    pb.finish_with_message("✓ Complete");
                }
            }
        }

        const HEAP_SIZE: usize = 0x100000;
        const HEAP_ALIGN: usize = 0x10000;

        let (_buffer, heap_start, heap_len) = create_aligned_heap(HEAP_SIZE, HEAP_ALIGN);
        let mut allocator = DekoHeap::<20>::new(Ghost::assume_new());
        allocator.init(heap_start, heap_len, 20);

        // Allocate alternating sizes to fragment memory
        let mut allocs = Vec::new();
        for i in 0..20 {
            let size = if i % 2 == 0 { 0x1000 } else { 0x2000 };
            let addr = allocator.allocate(size, 0x1000);
            if addr != 0 {
                allocs.push((addr, size));
            }
        }

        // Free every other allocation
        for i in (0..allocs.len()).step_by(2) {
            let (addr, size) = allocs[i];
            allocator.deallocate(addr, size, 0x1000);
        }

        // Try to allocate a large block (should fail or succeed based on coalescing)
        let large_addr = allocator.allocate(0x10000, 0x1000);

        // Cleanup
        for (i, &(addr, size)) in allocs.iter().enumerate() {
            if i % 2 != 0 {
                allocator.deallocate(addr, size, 0x1000);
            }
        }
        if large_addr != 0 {
            allocator.deallocate(large_addr, 0x10000, 0x1000);
        }
    }

    // Reproduction test for HEAP_SIZE_FULL=14 issue with non-power-of-2 min_block_size
    fn test_repro_heap_size_14(_ in alloc_ops_strategy()) {
        // Target min_block_size = 3.
        // ORDER = 14. top_order = 13.
        // heap_size = 3 * 2^13 = 3 * 8192 = 24576 = 0x6000.
        const HEAP_SIZE: usize = 0x6000; 
        const HEAP_ALIGN: usize = 0x1000; // Use smaller alignment to fit in small heap

        let (_buffer, heap_start, heap_len) = create_aligned_heap(HEAP_SIZE, HEAP_ALIGN);
        
        let mut allocator = DekoHeap::<14>::new(Ghost::assume_new());
        
        allocator.init(heap_start, heap_len, 14);

        // Try to allocate something small (16 bytes)
        let addr = allocator.allocate(16, 16);
        
        if addr != 0 {
            allocator.deallocate(addr, 16, 16);
        } else {
             // If allocation fails, it might be due to min_block_size < 16 check
             // But min_block_size is 3 here.
        }
    }
}
