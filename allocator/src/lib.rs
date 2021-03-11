#![no_std]
pub mod freelist;

extern crate alloc;

#![feature(alloc_error_handler)]

#[alloc_error_handler]
fn alloc_error_handler(layout: alloc::alloc::Layout) -> !{
    panic("allocation error: {:?}", layout)
}