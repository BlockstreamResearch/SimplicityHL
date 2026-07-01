//! Minimal cross-platform dynamic library loader.

use std::ffi::c_void;
use std::fmt;
use std::path::Path;

/// Error returned by dynamic library operations.
#[derive(Debug)]
pub struct Error(String);

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(&self.0)
    }
}

impl std::error::Error for Error {}

/// Handle to a dynamically loaded shared library.
///
/// The library is unloaded when this value is dropped.
#[derive(Clone)]
pub struct Library {
    handle: *mut c_void,
}

unsafe impl Send for Library {}
unsafe impl Sync for Library {}

impl Library {
    /// Load a shared library from the given filesystem path.
    ///
    /// # Safety
    ///
    /// The caller must ensure that the specified path is valid
    /// and points to shared library compatible with the current platform.
    pub unsafe fn load(path: &Path) -> Result<Self, Error> {
        imp::load(path).map(|handle| Self { handle })
    }

    /// Look up an exported symbol by name and return its address as a
    /// function pointer of type `F`.
    ///
    /// # Safety
    ///
    /// The caller is responsible for ensuring that the type `F` matches the
    /// actual signature of the symbol in the loaded library. Calling a
    /// function through a mismatched signature is undefined behavior.
    pub unsafe fn symbol<F: Copy>(&self, name: &str) -> Result<F, Error> {
        assert_eq!(
            std::mem::size_of::<F>(),
            std::mem::size_of::<*mut c_void>(),
            "symbol type must be pointer-sized (e.g. a function pointer)",
        );
        let ptr = imp::symbol(self.handle, name)?;
        // SAFETY: caller asserts that `F` matches the symbol signature, and
        // `F` is pointer-sized as checked above.
        Ok(std::mem::transmute_copy::<*mut c_void, F>(&ptr))
    }
}

impl Drop for Library {
    fn drop(&mut self) {
        unsafe { imp::close(self.handle) };
    }
}

#[cfg(unix)]
mod imp {
    use super::Error;
    use std::ffi::{c_void, CString};
    use std::path::Path;

    extern "C" {
        fn dlopen(filename: *const i8, flag: i32) -> *mut c_void;
        fn dlsym(handle: *mut c_void, symbol: *const i8) -> *mut c_void;
        fn dlclose(handle: *mut c_void) -> i32;
        fn dlerror() -> *const i8;
    }

    const RTLD_NOW: i32 = 2;
    const RTLD_LOCAL: i32 = 0;

    fn last_error(fallback: &str) -> Error {
        // SAFETY: `dlerror` returns either NULL or a pointer to a
        // NUL-terminated C string owned by libc; we copy it immediately.
        unsafe {
            let ptr = dlerror();
            if ptr.is_null() {
                return Error(fallback.to_owned());
            }
            let mut len = 0;
            while *ptr.add(len) != 0 {
                len += 1;
            }
            let bytes = std::slice::from_raw_parts(ptr.cast::<u8>(), len);
            Error(String::from_utf8_lossy(bytes).into_owned())
        }
    }

    pub(super) fn load(path: &Path) -> Result<*mut c_void, Error> {
        let path_str = path.to_str().ok_or_else(|| {
            Error(format!(
                "library path is not valid UTF-8: {}",
                path.display()
            ))
        })?;
        let c_path = CString::new(path_str)
            .map_err(|_| Error("library path contains an interior NUL byte".to_owned()))?;
        // Clear any stale error before the call so `dlerror` reflects this call.
        unsafe { dlerror() };
        let handle = unsafe { dlopen(c_path.as_ptr(), RTLD_NOW | RTLD_LOCAL) };
        if handle.is_null() {
            return Err(last_error("dlopen failed"));
        }
        Ok(handle)
    }

    pub(super) fn symbol(handle: *mut c_void, name: &str) -> Result<*mut c_void, Error> {
        let c_name = CString::new(name)
            .map_err(|_| Error(format!("symbol name contains a NUL byte: {name}")))?;
        unsafe { dlerror() };
        let ptr = unsafe { dlsym(handle, c_name.as_ptr()) };
        if ptr.is_null() {
            // A NULL return is only an error if `dlerror` reports one (a
            // symbol may legitimately resolve to NULL).
            let err = last_error("symbol not found");
            return Err(Error(format!("failed to load symbol '{name}': {err}")));
        }
        Ok(ptr)
    }

    pub(super) unsafe fn close(handle: *mut c_void) {
        let _ = dlclose(handle);
    }
}

#[cfg(windows)]
mod imp {
    use super::Error;
    use std::ffi::{c_void, CString};
    use std::path::Path;

    #[link(name = "kernel32")]
    extern "system" {
        fn LoadLibraryW(filename: *const u16) -> *mut c_void;
        fn GetProcAddress(module: *mut c_void, name: *const i8) -> *mut c_void;
        fn FreeLibrary(module: *mut c_void) -> i32;
        fn GetLastError() -> u32;
    }

    fn last_error(prefix: &str) -> Error {
        let code = unsafe { GetLastError() };
        Error(format!("{prefix} (Windows error {code})"))
    }

    pub(super) fn load(path: &Path) -> Result<*mut c_void, Error> {
        // Encode path as a NUL-terminated UTF-16 sequence for `LoadLibraryW`.
        use std::os::windows::ffi::OsStrExt;
        let mut wide: Vec<u16> = path.as_os_str().encode_wide().collect();
        wide.push(0);
        let handle = unsafe { LoadLibraryW(wide.as_ptr()) };
        if handle.is_null() {
            return Err(last_error(&format!(
                "LoadLibraryW failed for {}",
                path.display()
            )));
        }
        Ok(handle)
    }

    pub(super) fn symbol(handle: *mut c_void, name: &str) -> Result<*mut c_void, Error> {
        let c_name = CString::new(name)
            .map_err(|_| Error(format!("symbol name contains a NUL byte: {name}")))?;
        let ptr = unsafe { GetProcAddress(handle, c_name.as_ptr()) };
        if ptr.is_null() {
            return Err(last_error(&format!("failed to load symbol '{name}'")));
        }
        Ok(ptr)
    }

    pub(super) unsafe fn close(handle: *mut c_void) {
        let _ = FreeLibrary(handle);
    }
}
