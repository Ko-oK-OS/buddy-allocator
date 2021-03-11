use core::ptr::NonNull;
use core::ptr::null_mut;
use alloc::alloc::{GlobalAlloc, Layout};



pub struct FreeList{
    next: Option<NonNull<FreeList>>
}


unsafe impl GlobalAlloc for FreeList{
    unsafe fn alloc(&self, _layout: Layout) -> *mut u8{
        null_mut()
    }

    unsafe fn dealloc(&self, _ptr: *mut u8, _layout: Layout){
        panic!("dealloc should be never called")
    }
}