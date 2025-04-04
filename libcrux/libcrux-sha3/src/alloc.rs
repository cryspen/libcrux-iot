#![allow(unsafe_code)]
struct Alloc<const STACK_SIZE: usize> {
    buffer: [u8; STACK_SIZE],
    pointer: usize,
}

impl<const STACK_SIZE: usize> Alloc<STACK_SIZE> {
    fn new() -> Self {
        Self {
            buffer: [0u8; STACK_SIZE],
            pointer: 0
        }
    }

    fn bytes(&self, len: usize) -> &[u8] {
        let out = unsafe {
            core::slice::from_raw_parts(self.buffer.as_ptr().add(self.pointer) as *const u8, len)
        };

        out
    }
}
