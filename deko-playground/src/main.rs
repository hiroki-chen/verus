use deko_std::mem::{DekoBuddyAllocator, DekoHeap, Heap, HEAP_SIZE};
use deko_std::ptr::DekoPPtr;
use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn main() {
    test_heap_allocator();
    test_pointer();

}

#[verifier::external_body]
fn test_pointer() {
    let v = vec![0u8; 4096];
    let p = v.as_ptr() as u64;

    let (deko_ptr, Tracked(perm)) = unsafe { DekoPPtr::<u8>::from_raw_uninit(p) };

    deko_ptr.update_in_place(
        Tracked(perm),
        |v|
            {
                unsafe {
                    *v = 0xff;
                }
            },
    );

    let val = deko_ptr.borrow(Tracked(&perm));
    println!("val = {}", val);
    println!("v[0] = {}", v[0]);
}

#[verifier::external_body]
fn test_heap_allocator() {
    let test_heap = vec![0u8; 65536];
    let heap_start = test_heap.as_ptr() as u64;

    println!("Heap starts at {:x}", heap_start);
    println!("Heap ends at {:x}", heap_start + test_heap.len() as u64);

    let ghost f = DekoHeapPredicate;
    let mut heap = DekoHeap::<HEAP_SIZE>::new(Ghost(f));

    heap.init(heap_start, test_heap.len() as _, HEAP_SIZE as _);

    let a1 = heap.allocate(4096, 0x08);
    let a2 = heap.allocate(0x8, 0x08);
    let a3 = heap.allocate(0x8, 0x08);

    unsafe {
        *(a1 as *mut u64) = 0xdeadbeef;
        *(a2 as *mut u64) = 0xdeadbeef;
        *(a3 as *mut u64) = 0xdeadbeef;
    }

    println!("a1 = {:x}", a1);
    println!("a2 = {:x}", a2);
    println!("a3 = {:x}", a3);

    println!("a1 = {:x}", unsafe { *(a1 as *mut u64) });
    println!("a2 = {:x}", unsafe { *(a2 as *mut u64) });
    println!("a3 = {:x}", unsafe { *(a3 as *mut u64) });
}

} // verus!
