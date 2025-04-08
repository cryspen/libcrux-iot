#![allow(unsafe_code)]

use core::cell::RefCell;
use core::default::Default;

pub struct Alloc<const STACK_SIZE: usize, T: Sized + Default + Copy> {
    /// The backing buffer.
    #[allow(dead_code)]
    buffer: [T; STACK_SIZE],
    /// Points to the region of available memory within [buffer].
    pointer: RefCell<*mut T>,
}

impl<const STACK_SIZE: usize, T: Sized + Default + Copy> Alloc<STACK_SIZE, T> {
    pub(crate) fn new() -> Self {
        let buffer = [T::default(); STACK_SIZE];
        let pointer = RefCell::new(core::ptr::null_mut::<T>());

        let out = Self { buffer, pointer };

        let buffer_ptr = out.buffer.as_ptr();

        *(out.pointer.borrow_mut()) = buffer_ptr as *mut T;

        out
    }

    pub(crate) fn alloc(&self, len: usize) -> &mut [T] {
        let allocation_start = *self.pointer.borrow();
        let allocation_end = unsafe { (*self.pointer.borrow()).add(len) };

        if (allocation_end as *const T) >= unsafe { self.buffer.as_ptr().add(STACK_SIZE) } {
            panic!("Insufficient memory")
        }

        let out: &mut [T] = unsafe { core::slice::from_raw_parts_mut(allocation_start, len) };

        *self.pointer.borrow_mut() = allocation_end;

        out
    }

    /// This assumes that `allocation` was the most recent allocation.
    pub(crate) fn free(&self, allocation: &mut [T]) {
        println!("Freeing {}", allocation.len());
        println!("self.buffer: {:?}", self.buffer.as_ptr());
        println!("self.pointer: {:?}", *self.pointer.borrow());

        let new_pointer = unsafe { (*self.pointer.borrow()).sub(allocation.len()) };
        if (new_pointer as *const T) != allocation.as_ptr() {
            panic!("Invalid free")
        }

        *self.pointer.borrow_mut() = new_pointer;
    }
}
