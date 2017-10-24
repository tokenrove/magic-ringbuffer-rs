//! The Magic Ringbuffer
//!
//! Beware, this crate is in an extremely primitive state:
//!  - it can panic;
//!  - the interface is clunky and will probably change;
//!  - it's not portable;
//!  - it's not well tested;
//!  - the errors reported are coarse and not useful for debugging.
//!  - particularly, it is likely there are leaks or other problems in
//!    underexercised error paths.

#![warn(
    missing_copy_implementations,
    missing_debug_implementations,
    missing_docs,
    trivial_casts,
    trivial_numeric_casts,
    unused_extern_crates,
    unused_import_braces,
    unused_qualifications,
    variant_size_differences,
)]

#![feature(unique, try_from)]

extern crate libc;

use libc::{
    c_void, close,
    ftruncate,
    getpid,
    mmap, munmap,
    sysconf,
    unlink,
    _SC_PAGESIZE,
    MAP_ANONYMOUS, MAP_FAILED, MAP_FIXED, MAP_PRIVATE, MAP_SHARED,
    PROT_NONE, PROT_READ, PROT_WRITE,
};
use std::convert::TryFrom;
use std::ffi::CString;
use std::os::unix::io::RawFd;
use std::{ptr, slice};

#[allow(missing_docs)]
#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Error {
    OS,
    Overflow,
    Underflow,
}

impl std::error::Error for Error {
    fn description(&self) -> &str { "Magic ringbuffer error" }
    fn cause(&self) -> Option<&std::error::Error> { None }
}

impl std::fmt::Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> Result<(), std::fmt::Error> {
        match *self {
            Error::OS => write!(f, "OS error"),
            Error::Overflow => write!(f, "overflow"),
            Error::Underflow => write!(f, "underflow"),
        }
    }
}

impl From<std::num::TryFromIntError> for Error {
    fn from(_err: std::num::TryFromIntError) -> Error {
        Error::OS
    }
}


/// A magic ringbuffer.
pub struct Buf {
    capacity: usize,
    pointer: ptr::Unique<u8>,
    read_idx: usize,
    write_idx: usize,
}

// Unique doesn't have Debug, alas.
impl std::fmt::Debug for Buf {
    fn fmt(&self, f: &mut std::fmt::Formatter) -> std::fmt::Result {
        f.debug_struct("Buf")
            .field("capacity", &self.capacity)
            .field("pointer", &format!("{:p}", &self.pointer))
            .field("read_idx", &self.read_idx)
            .field("write_idx", &self.write_idx)
            .finish()
    }
}

/// An iterator over a slice of a magic ringbuffer.  This consumes
/// these bytes; one can use `readable_slice().iter()` instead to
/// avoid this.
#[derive(Debug)]
pub struct BufIter<'a> {
    buf: &'a mut Buf,
    idx: usize,
    end: usize,
}


// We need an fd associated with shared memory so we can have both
// mappings point to the same thing.
//
// The portable thing to do here would be to call shm_open(3), but we
// run into the problem of generating a temporary name without races,
// and although O_EXCL helps, it still becomes a mess.  So we do the
// unportable thing of using mkstemp(3) on /dev/shm (a Linuxism), for
// now.
#[cfg(target_os = "linux")]
fn get_unlinked_shm_fd() -> Result<RawFd, Error> {
    use libc::mkstemp;
    unsafe {
        let shm_path = CString::new(format!("/dev/shm/mrb-{}-XXXXXX", getpid())).unwrap();
        let p = shm_path.into_raw();
        let fd = mkstemp(p);
        let shm_path = CString::from_raw(p);
        if fd < 0 || 0 != unlink(shm_path.as_ptr()) {
            return Err(Error::OS)
        }
        Ok(fd)
    }
}

#[cfg(not(target_os = "linux"))]
fn get_unlinked_shm_fd() -> Result<RawFd, Error> {
    use libc::{shm_open, shm_unlink, O_CREAT, O_EXCL, O_RDWR};
    let mut fd = -1;
    for i in 0..1000 {
        unsafe {
            // XXX predictable
            let shm_path = CString::new(format!("/mrb-{}-{}", getpid(), i)).unwrap();
            fd = shm_open(shm_path.as_ptr(), O_RDWR | O_CREAT | O_EXCL, 0);
            if fd >= 0 {
                shm_unlink(shm_path.as_ptr());
                break
            }
        }
    }
    if fd < 0 { return Err(Error::OS) }
    Ok(fd)
}


fn get_page_size() -> Result<usize, std::num::TryFromIntError> {
    unsafe { usize::try_from(sysconf(_SC_PAGESIZE)) }
}


impl Buf {
    /// Creates a new magic ringbuffer that can hold `desired_size`
    /// bytes at any time.
    ///
    /// Arbitrary sizes are permitted, but will be rounded up to the
    /// system page size, so n_free() may be surprising.
    ///
    /// Note that this makes many syscalls, so it's not cheap.
    pub fn with_capacity(desired_size: usize) -> Result<Self, Error> {
        unsafe {
            let pagesize = get_page_size()?;
            assert!(pagesize.is_power_of_two());

            let size = if desired_size != (desired_size & !(pagesize-1)) {
                (desired_size + pagesize) & !(pagesize-1)
            } else { desired_size };

            let checked_mmap = |ptr, size, prot, flags, fd: Option<RawFd>| {
                let p = mmap(ptr, size, prot, flags, fd.unwrap_or(-1), 0);
                if p == MAP_FAILED { return Err(Error::OS) }
                Ok(p)
            };

            // Under Linux, there's an unportable alternative to this
            // sequence of mmaps, remap_file_pages(2), but it's been
            // deprecated since 3.16, so we might as well do the
            // (slightly more) portable thing.
            let base_pointer = checked_mmap(ptr::null_mut(),
                                            2*size,
                                            PROT_NONE,
                                            MAP_ANONYMOUS | MAP_PRIVATE,
                                            None)?;

            let fd = get_unlinked_shm_fd()?;
            if 0 != ftruncate(fd, size as i64) { return Err(Error::OS) }

            // Der Welt Erbe gewänne zu eigen,
            // wer aus dem Rheingold schüfe den Ring,
            // der maßlose Macht ihm verlieh'.

            let primary = checked_mmap(base_pointer,
                                       size,
                                       PROT_READ | PROT_WRITE,
                                       MAP_FIXED | MAP_SHARED,
                                       Some(fd))?;
            checked_mmap(base_pointer.offset(size as isize),
                         size,
                         PROT_READ | PROT_WRITE,
                         MAP_FIXED | MAP_SHARED,
                         Some(fd))?;

            if 0 != close(fd) { return Err(Error::OS) }

            Ok(Buf {
                capacity: size,
                pointer: ptr::Unique::new(primary as *mut u8).ok_or(Error::OS)?,
                read_idx: 0,
                write_idx: 0,
            })
        }
    }

    /// Returns the number of bytes to be read from `self`.
    pub fn len(&self) -> usize {
        self.write_idx - self.read_idx
    }

    /// Returns `true` if there are no bytes in the buffer.
    pub fn is_empty(&self) -> bool {
        self.len() == 0
    }

    /// Returns the remaining capacity in bytes for `self`.
    pub fn n_free(&self) -> usize {
        self.capacity - self.len()
    }

    /// Resets `self` as if it contained nothing.
    pub fn clear(&mut self) {
        self.read_idx = 0;
        self.write_idx = 0;
    }

    /// Advances the write index by `n`.  Use this after writing bytes
    /// into the `writable_slice`.
    pub fn produce(&mut self, n: usize) -> Result<(), Error> {
        if self.len() + n > self.capacity {
            return Err(Error::Overflow);
        }
        self.write_idx += n;
        Ok(())
    }

    /// Advances the read index by `n`.  Use this after reading bytes
    /// out of the `readable_slice`.
    pub fn consume(&mut self, n: usize) -> Result<(), Error> {
        if self.read_idx + n > self.write_idx {
            return Err(Error::Underflow)
        }
        self.read_idx += n;
        // You may want to convince yourself of the truth of this
        // section: Since we can never operate on more than `capacity`
        // bytes at a time, we don't need to reduce these indices mod
        // n; and, the read index must always trail the write index.
        if self.read_idx > self.capacity {
            self.read_idx -= self.capacity;
            self.write_idx -= self.capacity;
        }
        Ok(())
    }

    /// Gets a slice of `self` which contains bytes that can be read.
    pub fn readable_slice(&self) -> &[u8] {
        unsafe {
            slice::from_raw_parts(self.pointer.as_ptr().offset(self.read_idx as isize),
                                  self.len())
        }
    }

    /// Gets a mutable slice of `self` to which one can write bytes.
    pub fn writable_slice(&mut self) -> &mut [u8] {
        unsafe {
            slice::from_raw_parts_mut(self.pointer.as_ptr().offset(self.write_idx as isize),
                                      self.n_free())
        }
    }

    /// Creates a `BufIter` to iterate over the currently readable
    /// bytes in `self`, consuming them as we go.
    pub fn iter(&mut self) -> BufIter {
        let (idx, end) = (self.read_idx, self.write_idx);
        BufIter {
            buf: self,
            idx: idx,
            end: end
        }
    }
}


impl<'a> Iterator for BufIter<'a> {
    type Item = u8;
    fn next(&mut self) -> Option<u8> {
        if self.idx >= self.end { return None }
        if Ok(()) != self.buf.consume(1) { return None }
        self.idx += 1;
        Some(unsafe {*self.buf.pointer.as_ptr().offset(self.idx as isize - 1)})
    }
}


impl Drop for Buf {
    fn drop(&mut self) {
        unsafe {
            // It's not clear what makes the most sense for handling
            // errors in `drop`, but the consensus seems to be either
            // ignore the error, or panic.
            if munmap(self.pointer.as_ptr().offset(0) as *mut c_void, 2*self.capacity) < 0 {
                panic!("munmap({:p}, {}) failed", self.pointer, 2*self.capacity)
            }
        }
    }
}


#[cfg(test)]
mod tests {
    use super::{Buf, get_page_size};
    use std::io::{Cursor, Read, Write};

    #[test]
    fn expect_empty_read_to_return_zero() {
        let buf = Buf::with_capacity(4096).unwrap();
        let slice = buf.readable_slice();
        assert_eq!(0, slice.len())
    }

    #[test]
    fn expect_writes_when_full_to_return_zero() {
        let mut buf = Buf::with_capacity(42).unwrap();
        let actual_size = buf.n_free();
        buf.produce(actual_size).unwrap();
        assert_eq!(0, buf.writable_slice().len())
    }

    #[test]
    #[should_panic]
    fn expect_excessive_consume_to_panic() {
        let mut buf = Buf::with_capacity(4096).unwrap();
        buf.consume(42).unwrap();
    }

    #[test]
    #[should_panic]
    fn expect_excessive_produce_to_panic() {
        let mut buf = Buf::with_capacity(4096).unwrap();
        let actual_size = buf.n_free();
        buf.produce(actual_size+1).unwrap();
    }

    #[test]
    fn copy_between_buffers() {
        let pagesize = get_page_size().unwrap();
        let mut buf = Buf::with_capacity(pagesize).unwrap();
        let mut from_v = Vec::new();
        for i in 0..10*pagesize {
            from_v.push(i as u8)
        }
        let mut from = Cursor::new(from_v);
        let mut to = Cursor::new(Vec::new());
        loop {
            let n = {
                let mut wslice = buf.writable_slice();
                let n = wslice.len();
                from.read(&mut wslice[0..n-1]).unwrap()
            };
            if n == 0 { break }
            assert!(n > 0);
            buf.produce(n).unwrap();
            let m = {
                let rslice = buf.readable_slice();
                to.write(&rslice[0..rslice.len()-1]).unwrap()
            };
            assert!(m > 0);
            buf.consume(m).unwrap();
        }
        let m = to.write(&buf.readable_slice()).unwrap();
        buf.consume(m).unwrap();
        assert_eq!(from.get_ref(), to.get_ref())
    }

    #[test]
    fn write_across_border() {
        let pagesize = get_page_size().unwrap();
        let mut buf = Buf::with_capacity(pagesize).unwrap();
        assert_eq!(buf.n_free(), pagesize);
        let ones = vec![1_u8; pagesize];
        let twos = vec![2_u8; pagesize];
        buf.writable_slice()[0..128].copy_from_slice(&ones[0..128]);
        buf.produce(128).unwrap();
        assert_eq!(&buf.readable_slice()[0..128], &ones[0..128]);
        buf.consume(128).unwrap();

        buf.writable_slice().copy_from_slice(&twos[0..pagesize]);
        buf.produce(pagesize).unwrap();

        assert_eq!(&buf.readable_slice()[0..pagesize-8], &twos[0..pagesize-8]);
        buf.consume(pagesize-8).unwrap();

        assert_eq!(&buf.readable_slice()[0..8], &twos[0..8]);
        buf.consume(8).unwrap();
    }

    #[test]
    fn basic_iterator() {
        let pagesize = get_page_size().unwrap();
        let mut buf = Buf::with_capacity(pagesize).unwrap();
        assert_eq!(buf.n_free(), pagesize);
        let ones = vec![1_u8; pagesize];
        let twos = vec![2_u8; pagesize];
        buf.writable_slice()[0..128].copy_from_slice(&ones[0..128]);
        buf.produce(128).unwrap();
        {
            let iter = buf.iter();
            let v = iter.take(128).collect::<Vec<_>>();
            assert_eq!(v, &ones[0..128]);
        }

        buf.writable_slice().copy_from_slice(&twos[0..pagesize]);
        buf.produce(pagesize).unwrap();
        assert_eq!(buf.len(), pagesize);

        {
            let iter = buf.iter();
            let v = iter.take(pagesize-8).collect::<Vec<_>>();
            assert_eq!(v, &twos[0..pagesize-8]);
        }

        {
            let iter = buf.iter();
            let v = iter.take(8).collect::<Vec<_>>();
            assert_eq!(v, &twos[0..8]);
        }

        assert_eq!(None, buf.iter().next());
    }
}
