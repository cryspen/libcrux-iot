//! Very simple bump allocator.
//!
//! Safety ⚠️:
//! - Initializing this is a two-step process. First create an
//!   allocator with [Alloc::new] and then, after it has been moved to
//!   a place, set the internal pointer with `set_pointer`:
//!   ```ignore
//!   let alloc = Alloc::<STACK_SIZE,T>::new();
//!   alloc.set_pointer();
//!   ... // you can now use the allocator, by reference only
//!   ```
//! - Memory can only be freed if it is provably the most recently
//!   allocated memory.

#![allow(unsafe_code)]

use core::cell::RefCell;
use core::default::Default;

/// Bump allocator.
pub struct Alloc<const STACK_SIZE: usize, T: Sized + Default + Copy> {
    /// The backing buffer.
    #[allow(dead_code)]
    buffer: [T; STACK_SIZE],
    /// Points to the region of available memory within [buffer].
    pointer: RefCell<*mut T>,
}

impl<const STACK_SIZE: usize, T: Sized + Default + Copy> Alloc<STACK_SIZE, T> {
    /// Creates a new Allocator.
    ///
    /// After the allocator has been created and assigned to a place,
    /// use `self.set_pointer` to initialize the internal
    /// pointer. After this, the allocator MUST NOT be moved.
    pub fn new() -> Self {
        let buffer = [T::default(); STACK_SIZE];
        // We can only set the pointer to the start of `buffer` once
        // we can assume that `buffer` will not be moved anymore.
        let pointer = RefCell::new(core::ptr::null_mut::<T>()); 

        let out = Self {
            buffer,
            pointer,
        };

        out
    }

    /// Sets the internal pointer to the beginning of `self.buffer`
    ///
    /// This MUST be done before calling `alloc` for the first time.
    /// After calling this `self` MUST NOT be moved, as this lead to
    /// an invalid state of `self.pointer`.
    pub fn set_pointer(&self) {
        let buffer_ptr = self.buffer.as_ptr();
        *(self.pointer.borrow_mut()) = buffer_ptr as *mut T;
    }

    /// Allocate a mutable T-slice of length `len`.
    pub fn alloc(&self, len: usize) -> &mut [T] {
        assert!(!(*self.pointer.borrow()).is_null(), "Internal pointer must be set with `self.set_pointer`, after which `self` MUST NOT be moved");
        let allocation_start = *self.pointer.borrow();
        let allocation_end = unsafe { (*self.pointer.borrow()).add(len) };

        if (allocation_end as *const T) >= unsafe { self.buffer.as_ptr().add(STACK_SIZE) } {
            panic!("Insufficient memory")
        }

        let out: &mut [T] = unsafe { core::slice::from_raw_parts_mut(allocation_start, len) };

        *self.pointer.borrow_mut() = allocation_end;

        out
    }

    /// Free the most recent allocation.
    ///
    /// This MUST NOT be used if `allocation` cannot be proven to be
    /// the most recent allocation.
    pub fn free(&self, allocation: &mut [T]) {
        let new_pointer = unsafe { (*self.pointer.borrow()).sub(allocation.len()) };
        if (new_pointer as *const T) != allocation.as_ptr() {
            panic!("Invalid free")
        }

        *self.pointer.borrow_mut() = new_pointer;
    }
}
