#![allow(unsafe_code)]

use core::cell::RefCell;

pub struct Alloc<const STACK_SIZE: usize> {
    /// The backing buffer.
    #[allow(dead_code)]
    buffer: [u8; STACK_SIZE],
    /// Points to the region of available memory within [buffer].
    pointer: RefCell<*mut u8>,
    /// Points to the end of [buffer].
    end_pointer: *const u8,
}

impl<const STACK_SIZE: usize> Alloc<STACK_SIZE> {
    pub(crate) fn new() -> Self {
        let mut buffer = [0u8; STACK_SIZE];
        let pointer = RefCell::new(buffer.as_mut_ptr());
        let end_pointer = unsafe { buffer.as_mut_ptr().add(STACK_SIZE) };

        Self {
            buffer,
            pointer,
            end_pointer,
        }
    }

    pub(crate) fn alloc<T: Sized>(&self, len: usize, init: fn(usize) -> T) -> &mut [T] {
        let t_alignment = core::mem::align_of::<T>();
        let requested_size = len * core::mem::size_of::<T>();

        let offset = (*self.pointer.borrow()).align_offset(t_alignment);

        let allocation_start = unsafe { (*self.pointer.borrow()).add(offset) };
        let allocation_end = unsafe { (*self.pointer.borrow()).add(requested_size + offset) };

        if (allocation_end as *const u8) >= self.end_pointer {
            panic!("Insufficient memory")
        }

        let out: &mut [u8] =
            unsafe { core::slice::from_raw_parts_mut(allocation_start, requested_size) };

        let out = unsafe { &mut *(out as *mut [u8] as *mut[T])};
        let mut out_ptr = out.as_mut_ptr();
        for i in 0..len {
            unsafe {
                out_ptr.write(init(i));
                out_ptr = out_ptr.offset(1);
            }
        }
        
        *self.pointer.borrow_mut() = allocation_end;
        
        out
    }

    /// This assumes that `allocation` was the most recent allocation.
    pub(crate) fn free<T: Sized>(&self, allocation: &mut [T]) {
        let bytes_to_be_freed = allocation.len() * core::mem::size_of::<T>();

        let new_pointer =
            unsafe { (*self.pointer.borrow()).byte_offset(-(bytes_to_be_freed as isize)) };
        if (new_pointer as *const u8) < self.buffer.as_ptr() {
            panic!("Trying to free more than was allocated")
        }

        *self.pointer.borrow_mut() = new_pointer;
    }
}
