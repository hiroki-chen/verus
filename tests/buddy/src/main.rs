use deko_std::mem::{DekoHeap, DekoHeapPredicate, Heap};
use vstd::prelude::*;

verus! {

#[verifier::external_body]
fn main() {
    let v = vec![0u8; 0xa0000 - 0x10000];
    let heap_start = v.as_ptr() as usize;
    let heap_end = heap_start + v.len();

    println!("Heap start: 0x{:x}, end: 0x{:x}", heap_start,  heap_end);

    let mut allocator = DekoHeap::<10>::new(Ghost(DekoHeapPredicate {}));
    allocator.init(heap_start as _, v.len() as _ , 10);

    let a = allocator.allocate(0x1000, 0x1000);

    println!("Allocated at address: 0x二分他 2{:x}", a);
}

}
