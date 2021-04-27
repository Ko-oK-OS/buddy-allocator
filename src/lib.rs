//! Thread-unsafe, panic-free buddy system allocator.
//! To use it, we need to wrap it into sync primitive to provide thread-safety.
//! TODO - example
//! TODO - panic free
//! TODO - allow panic when #[cfg(debug_assertions)]
//!
//! reference: https://pdos.csail.mit.edu/6.828/2019/lec/malloc.c

#![no_std]
#![feature(slice_ptr_get)]

use bit_field::BitField;

use core::alloc::Layout;
use core::ptr;
use core::mem::{MaybeUninit, self};
use core::cmp;

mod list;

use list::List;

pub struct BuddySystem {
    initialized: bool,
    base: usize,            // the starting addr managed by the buddy system
    actual_end: usize,      // the actual end addr managed by the buddy system
    nsizes: usize,          // the number of different sizes of blocks
    leaf_size: usize,
    max_alignment: usize,
    infos: MaybeUninit<*mut [BuddyInfo]>,
}

// since *mut [T] is not Send
unsafe impl Send for BuddySystem {}

impl BuddySystem {
    pub const fn uninit() -> Self {
        Self {
            initialized: false,
            base: 0,
            actual_end: 0,
            nsizes: 0,
            leaf_size: 0,
            max_alignment: 0,
            infos: MaybeUninit::uninit(),
        }
    }

    /// Init the buddy system allocator at [start, end).
    /// `leaf_size` and `max_alignment` must be a power of 2.
    /// `max_alignment` is the biggest alignment of a [`alloc::alloc::Layout`] the user can request.
    /// SAFETY: It should only be called once and before any subsequent call to this buddy system.
    pub unsafe fn init(&mut self, start: usize, end: usize, leaf_size: usize, max_alignment: usize)
        -> Result<(), &'static str>
    {
        if self.initialized {
            return Err("init twice");
        }

        if end - start < leaf_size {
            return Err("range too small");
        }

        if !leaf_size.is_power_of_two() || !max_alignment.is_power_of_two() {
            return Err("leaf size or max_alignment not 2^n");
        }
        self.leaf_size = leaf_size;
        self.max_alignment = max_alignment;

        // make sure start and end are both leaf aligned
        // and record the heap memory range: [self.base, self.end)
        let mut cur: usize = round_up(start, cmp::max(leaf_size, max_alignment));
        self.base = cur;
        self.actual_end = round_down(end, cmp::max(leaf_size, max_alignment));

        // compute the max pow of 2 smaller than size of [self.base, self.actual_end)
        self.nsizes = log2((self.actual_end-cur)/leaf_size) + 1;
        if self.actual_end - cur > self.blk_size(self.max_size()) {
            self.nsizes += 1;
        }

        // alloc buddy infos
        // SAFETY: init all of the BuddyInfo
        let info_slice_ptr = init_slice_empty(&mut cur, self.nsizes);
        self.infos.as_mut_ptr().write(info_slice_ptr);

        // init free list and alloc space for alloc field
        for i in 0..self.nsizes {
            let nblk = self.n_blk(i);
            let info = self.get_info_mut(i);
            
            info.free.init();

            // SAFETY: init the alloc field of size i
            let alloc_size = round_up(nblk, 8)/8;
            let alloc_slice_ptr = init_slice_empty(&mut cur, alloc_size);
            info.alloc.as_mut_ptr().write(alloc_slice_ptr);
        }

        // alloc space for split field
        // blocks of size 0 no need to split
        for i in 1..self.nsizes {
            let nblk = self.n_blk(i);
            let info = self.get_info_mut(i);

            // SAFETY: init the split field of size i
            let split_size = round_up(nblk, 8)/8;
            let split_slice_ptr = init_slice_empty(&mut cur, split_size);
            info.split.as_mut_ptr().write(split_slice_ptr);
        }

        // cur address may not be aligned now
        cur = round_up(cur, leaf_size);

        // meta data lies between [base, cur)
        let meta = self.mark_meta(cur);

        // unavailable data lies between [self.actual_end, 2^(self.nsizes-1))
        // due to the memory size of buddy system is a power of 2
        let unavail = self.mark_unavail();
        
        // init free regions
        let free = self.init_free(cur);

        // check total memory
        if free != self.blk_size(self.max_size()) - meta - unavail {
            return Err("allocator bug: tot != meta + free + unavail");
        }

        self.initialized = true;
        Ok(())
    }

    /// Return meta infomation for debuging.
    /// (initialized, base, actual_end, nsizes).
    pub fn meta_info(&self) -> (bool, usize, usize, usize) {
        (self.initialized, self.base, self.actual_end, self.nsizes)
    }

    /// Allocate a block of memory satisifying the layout.
    pub fn alloc(&mut self, layout: Layout) -> *mut u8 {
        if layout.size() == 0 {
            return ptr::null_mut();
        }

        // only guarantee the alignment not bigger than max_alignment
        if layout.align() > self.max_alignment {
            return ptr::null_mut();
        }
        // note: the size of a value is always a multiple of its alignment
        // now we only have to consider the size
        // because base and actual_end are already align to max_alignment

        // find the smallest block can contain the size
        let smalli = if layout.size() <= self.leaf_size {
            0 
        } else {
            (layout.size().next_power_of_two() / self.leaf_size).trailing_zeros() as usize
        };
        let mut sizei = smalli;
        while sizei < self.nsizes {
            let info = unsafe { self.get_info_mut(sizei) };
            if !info.free.is_empty() {
                break;
            }
            sizei += 1;
        }
        if sizei >= self.nsizes {
            // no free memory
            return ptr::null_mut()
        }

        // pop a block at self.infos[sizei]
        let info = unsafe { self.get_info_mut(sizei) };
        let raw_addr = match unsafe { info.free.pop() } {
            Some(raw_addr) => raw_addr,
            None => return ptr::null_mut(),
        };
        let bi = self.blk_index(sizei, raw_addr);
        unsafe { self.get_info_mut(sizei).alloc_set(bi, true); }

        // split the block until it reach smallest block size
        while sizei > smalli {            
            // split two buddies at sizei
            let bi = self.blk_index(sizei, raw_addr);
            let info = unsafe { self.get_info_mut(sizei) };
            info.split_set(bi, true);

            // alloc one buddy at sizei-1
            let bs1 = self.blk_size(sizei-1);
            let bi1 = self.blk_index(sizei-1, raw_addr);
            let info1 = unsafe { self.get_info_mut(sizei-1) };
            info1.alloc_set(bi1, true);

            // free the other buddy at sizei-1
            let buddy_addr = raw_addr + bs1;
            unsafe { info1.free.push(buddy_addr); }

            sizei -= 1;
        }

        raw_addr as *mut u8
    }

    /// Deallocate the memory.
    /// SAFETY: The raw ptr passed-in should be the one handed out previously.
    fn dealloc(&mut self, ptr: *mut u8, layout: Layout) {
        // check ptr in range [self.base, self.actual_end)
        let mut raw_addr = ptr as usize;
        #[cfg(debug_assertions)]
        if raw_addr < self.base || raw_addr >= self.actual_end {
            panic!("allocator: dealloc ptr out of range");
        }

        // find the size of block pointed by ptr
        // and check with the layout
        let mut sizei = self.nsizes;
        for i in 0..self.max_size() {
            let bi = self.blk_index(i+1, raw_addr);
            let info = unsafe { self.get_info_mut(i+1) };
            if info.is_split_set(bi) {
                sizei = i;
                break;
            }
        }
        #[cfg(debug_assertions)]
        if sizei == self.nsizes {
            panic!("allocator: dealloc cannot recycle ptr");
        }

        // check layout
        #[cfg(debug_assertions)]
        if layout.size() > self.blk_size(sizei) {
            panic!("allocator: layout {:?} > blk size {}", layout, self.blk_size(sizei));
        }

        // free and coalesce
        while sizei < self.max_size() {
            let bi = self.blk_index(sizei, raw_addr);
            let buddyi = if bi % 2 == 0 { bi+1 } else { bi-1 };
            let info = unsafe { self.get_info_mut(sizei) };
            info.alloc_set(bi, false);
            
            // test if buddy is free
            if info.is_alloc_set(buddyi) {
                break;
            }
            let buddy_addr = self.blk_addr(sizei, buddyi);
            unsafe { (buddy_addr as *mut List).as_mut().unwrap().remove(); }
            if buddyi % 2 == 0 {
                raw_addr = buddy_addr;
            }

            // coalesce and continue
            sizei += 1;
            let spliti = self.blk_index(sizei, raw_addr);
            let info = unsafe { self.get_info_mut(sizei) };
            info.split_set(spliti, false);
        }

        let info = unsafe { self.get_info_mut(sizei) };
        unsafe { info.free.push(raw_addr); }
    }

    /// Mark meta data of buddy system as used.
    /// [self.base, cur)
    fn mark_meta(&mut self, cur: usize) -> usize {
        let meta = cur - self.base;
        self.mark(self.base, cur);
        meta
    }

    /// Mark unavailable data due to the requirement,
    /// that the size of buddy system should be a power of 2.
    fn mark_unavail(&mut self) -> usize {
        let unavail = self.blk_size(self.max_size()) - (self.actual_end - self.base);
        self.mark(self.actual_end, self.actual_end + unavail);
        unavail
    }

    /// Mark memory from [left, right) as allocated.
    /// Useful for meta and unavailable data.
    fn mark(&mut self, left: usize, right: usize) {
        debug_assert_eq!(left % self.leaf_size, 0);
        debug_assert_eq!(right % self.leaf_size, 0);

        for i in 0..self.nsizes {
            let mut bi = self.blk_index(i, left);
            let bj = self.blk_index_next(i, right);
            while bi < bj {
                let info = unsafe { self.get_info_mut(i) };

                // mark alloc
                info.alloc_set(bi, true);

                // mark split, skip size 0
                if i > 0 {
                    info.split_set(bi, true);
                }
                bi += 1;
            }
        }
    }

    /// Init free regions between [left, self.actual_end).
    /// Must be called after marking meta and unavail data.
    fn init_free(&mut self, left: usize) -> usize {
        let right = self.actual_end;
        let mut free = 0;
        for i in 0..self.max_size() {
            let lbi = self.blk_index_next(i, left);
            let rbi = self.blk_index(i, right);
            free += self.init_free_pair(i, lbi);
            if left < right {
                free += self.init_free_pair(i, rbi);
            }
        }
        free
    }

    /// Push a buddy into the list if it cannot be coalesce and upgrade.
    fn init_free_pair(&mut self, sizei: usize, bi: usize) -> usize {
        let buddyi = if bi % 2 == 0 { bi+1 } else { bi-1 };
        let blk_addr_bi = self.blk_addr(sizei, bi);
        let blk_addr_buddyi = self.blk_addr(sizei, buddyi);
        
        let info = unsafe { self.get_info_mut(sizei) };
        if info.is_alloc_set(bi) != info.is_alloc_set(buddyi) {
            // one buddy is free, the other is allocated
            unsafe {
                if info.is_alloc_set(bi) {
                    info.free.push(blk_addr_buddyi);
                } else {
                    info.free.push(blk_addr_bi);    
                }
            }
            self.blk_size(sizei)
        } else {
            0
        }
    }

    /// Get buddy info at certain index.
    ///
    /// SAFETY: must be called after the initialization of infos field.
    unsafe fn get_info_mut(&mut self, index: usize) -> &mut BuddyInfo {
        let info_slice_ptr = *self.infos.as_ptr();
        info_slice_ptr.get_unchecked_mut(index).as_mut().unwrap()
    }

    /// The largest block size.
    /// Also the last index into the buddy info array.
    #[inline]
    fn max_size(&self) -> usize {
        self.nsizes - 1
    }

    /// Number of block at size k, based on the total managed memory.
    #[inline]
    fn n_blk(&self, k: usize) -> usize {
        1 << (self.max_size() - k)
    }

    fn blk_index(&self, k: usize, addr: usize) -> usize {
        (addr - self.base) / self.blk_size(k)
    }

    fn blk_index_next(&self, k: usize, addr: usize) -> usize {
        let bs = self.blk_size(k);
        let mut i = (addr - self.base) / bs;
        if (addr - self.base) % bs > 0 {
            i += 1;
        }
        i
    }

    /// Receive size k and block index bi.
    /// Return the block's raw addr at this buddy system.
    fn blk_addr(&self, k: usize, bi: usize) -> usize {
        self.base + (bi * self.blk_size(k))
    }

    #[inline]
    fn blk_size(&self, k: usize) -> usize {
        (1 << k) * self.leaf_size
    }
}

/// Buddy info for block of a certain size k, k is a power of 2 
#[repr(C)]
struct BuddyInfo {
    free: List,                         // record blocks of a certain size
    alloc: MaybeUninit<*mut [u8]>,      // tell if a block is allocated
    split: MaybeUninit<*mut [u8]>,      // tell if a block is split into smaller size
}

impl BuddyInfo {
    /// SAFETY: must be called after the initialization of alloc field.
    unsafe fn get_alloc(&self, index: usize) -> &u8 {
        let alloc_slice_ptr = *self.alloc.as_ptr() as *const [u8];
        alloc_slice_ptr.get_unchecked(index).as_ref().unwrap()
    }

    /// SAFETY: must be called after the initialization of alloc field.
    unsafe fn get_alloc_mut(&mut self, index: usize) -> &mut u8 {
        let alloc_slice_ptr = *self.alloc.as_ptr();
        alloc_slice_ptr.get_unchecked_mut(index).as_mut().unwrap()
    }

    /// SAFETY: must be called after the initialization of split field.
    unsafe fn get_split(&self, index: usize) -> &u8 {
        let split_slice_ptr = *self.split.as_ptr() as *const [u8];
        split_slice_ptr.get_unchecked(index).as_ref().unwrap()
    }

    /// SAFETY: must be called after the initialization of split field.
    unsafe fn get_split_mut(&mut self, index: usize) -> &mut u8 {
        let split_slice_ptr = *self.split.as_ptr();
        split_slice_ptr.get_unchecked_mut(index).as_mut().unwrap()
    }

    fn alloc_set(&mut self, index: usize, set_or_clear: bool) {
        let i1 = index / 8;
        let i2 = index % 8;
        unsafe { self.get_alloc_mut(i1).set_bit(i2, set_or_clear); }
    }

    fn split_set(&mut self, index: usize, set_or_clear: bool) {
        let i1 = index / 8;
        let i2 = index % 8;
        unsafe { self.get_split_mut(i1).set_bit(i2, set_or_clear); }
    }

    fn is_alloc_set(&self, index: usize) -> bool {
        let i1 = index / 8;
        let i2 = index % 8;
        unsafe { self.get_alloc(i1).get_bit(i2) }
    }

    fn is_split_set(&self, index: usize) -> bool {
        let i1 = index / 8;
        let i2 = index % 8;
        unsafe { self.get_split(i1).get_bit(i2) }
    }
}

/// Init the uninit raw slice wrapped in MaybeUninit with empty data, typically 0.
/// The passed-in T should have repr(C).
/// Return an initialized raw slice ptr.
unsafe fn init_slice_empty<T>(cur: &mut usize, len: usize) -> *mut [T] {
    let raw_ptr = *cur as *mut T;
    *cur += mem::size_of::<T>() * len;
    ptr::write_bytes(raw_ptr, 0, len);
    ptr::slice_from_raw_parts_mut(raw_ptr, len)
}

#[inline]
fn round_up(n: usize, size: usize) -> usize {
    (((n-1)/size)+1)*size
}

#[inline]
fn round_down(n: usize, size: usize) -> usize {
    (n/size)*size
}

fn log2(mut n: usize) -> usize {
    let mut k = 0;
    while n > 1 {
        k += 1;
        n >>= 1;
    }
    k
}
