#![allow(unsafe_code)]

use core::cell::RefCell;
use core::default::Default;

pub struct Alloc<const STACK_SIZE: usize, T:Sized + Default + Copy> {
    /// The backing buffer.
    #[allow(dead_code)]
    buffer: [T; STACK_SIZE],
    /// Points to the region of available memory within [buffer].
    pointer: RefCell<*mut T>,
    /// Points to the end of [buffer].
    end_pointer: *const T,
}

impl<const STACK_SIZE: usize, T: Sized + Default + Copy> Alloc<STACK_SIZE, T> {
    pub(crate) fn new() -> Self {
        let mut buffer = [T::default(); STACK_SIZE];
        let pointer = RefCell::new(buffer.as_mut_ptr());
        let end_pointer = unsafe { buffer.as_mut_ptr().add(STACK_SIZE) };

        Self {
            buffer,
            pointer,
            end_pointer,
        }
    }

    pub(crate) fn alloc(&self, len: usize) -> &mut [T] {
        println!("Allocation {len}");
        println!("self.buffer: {:?}", self.buffer.as_ptr());
        println!("self.pointer: {:?}", *self.pointer.borrow());
        let allocation_start = *self.pointer.borrow();
        let allocation_end = unsafe { (*self.pointer.borrow()).add(len ) };

        if (allocation_end as *const T) >= self.end_pointer {
            panic!("Insufficient memory")
        }

        let out: &mut [T] =
            unsafe { core::slice::from_raw_parts_mut(allocation_start, len) };

        *self.pointer.borrow_mut() = unsafe { allocation_start.add(len ) };
        
        out
    }

    /// This assumes that `allocation` was the most recent allocation.
    pub(crate) fn free(&self, allocation: &mut [T]) {
        println!("Freeing {}", allocation.len());
        println!("self.buffer: {:?}", self.buffer.as_ptr());
        println!("self.pointer: {:?}", *self.pointer.borrow());
        
        let new_pointer =
            unsafe { (*self.pointer.borrow()).offset(-(allocation.len() as isize)) };
        if (new_pointer as *const T) != allocation.as_ptr() {
            panic!("Invalid free")
        }

        *self.pointer.borrow_mut() = new_pointer;
    }
}
