use std::{
    ffi::{CStr, CString},
    fs::File,
    io,
    mem::MaybeUninit,
    os::fd::{AsRawFd, FromRawFd},
};

pub struct Stat {
    pub st: libc::stat,
}

pub fn stat(path_file: &impl AsRawFd) -> io::Result<Stat> {
    let mut st_ui = MaybeUninit::<libc::stat>::zeroed();

    let res = unsafe { libc::fstat(path_file.as_raw_fd(), st_ui.as_mut_ptr()) };
    if res >= 0 {
        let st = unsafe { st_ui.assume_init() };
        Ok(Stat { st })
    } else {
        Err(io::Error::last_os_error())
    }
}

pub fn open(path: &CStr, flags: libc::c_int, mode: u32) -> io::Result<File> {
    let path_cstr = CString::new(path.to_bytes()).expect("CString conversion failed");
    let fd = unsafe {
        if flags & libc::O_CREAT == libc::O_CREAT {
            libc::open(path_cstr.as_ptr(), flags, mode)
        } else {
            libc::open(path_cstr.as_ptr(), flags)
        }
    };

    if fd >= 0 {
        Ok(unsafe { File::from_raw_fd(fd) })
    } else {
        Err(io::Error::last_os_error())
    }
}
