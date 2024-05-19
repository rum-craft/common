pub(crate) mod compiler;
pub(crate) mod encoder;
pub(crate) mod types;

pub use compiler::compile_from_ssa_fn;

#[inline]
/// Pushes an arbitrary number of bytes to into a binary buffer.
fn push_bytes<T: Sized>(binary: &mut Vec<u8>, data: T) {
  let byte_size = std::mem::size_of::<T>();
  let data_as_bytes = &data as *const _ as *const u8;
  binary.extend(unsafe { std::slice::from_raw_parts(data_as_bytes, byte_size) });
}

#[inline]
/// Pushes an arbitrary number of bytes to into a binary buffer.
fn set_bytes<T: Sized>(binary: &mut Vec<u8>, offset: usize, data: T) {
  let byte_size = std::mem::size_of::<T>();
  let data_as_bytes = &data as *const _ as *const u8;

  debug_assert!(offset + byte_size <= binary.len());

  unsafe { binary.as_mut_ptr().offset(offset as isize).copy_from(data_as_bytes, byte_size) }
}

/* #[test]
pub fn run_x86() {
  let prot = libc::PROT_READ | libc::PROT_WRITE | libc::PROT_EXEC;
  let flags: i32 = libc::MAP_PRIVATE | libc::MAP_ANONYMOUS;

  let allocation_size = 4096;
  let ptr =
    unsafe { libc::mmap(std::ptr::null_mut(), allocation_size, prot, flags, -1, 0) as *mut u8 };

  let data = unsafe { std::slice::from_raw_parts_mut(ptr, allocation_size) };

  for entry in data.iter_mut() {
    *entry = 0;
  }

  // Move instruction
  let offset = mov_imm(GeneralRegisterName::EAX, 2024, 0, data);
  let offset = mov_imm(GeneralRegisterName::R8W, 2024, offset, data);
  let offset = fill_with_noop(offset, 20, data);
  ret_short(offset, data);

  let funct: fn() -> u64 = unsafe { std::mem::transmute(ptr) };

  dbg!((funct)());

  unsafe {
    let result = libc::munmap(ptr as *mut _, allocation_size);
    dbg!(result);
  }
} */
