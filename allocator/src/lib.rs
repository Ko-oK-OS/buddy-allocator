#![feature(alloc_error_handler)]
#![no_std]

#[alloc_error_handler]
fn alloc_error_handler(layout: alloc::alloc::Layout) -> !{
    panic!("allocation error: {:?}", layout)
}

pub mod freelist;

extern crate alloc;
