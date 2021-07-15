// run-rustfix
// aux-build: macro_rules.rs

#![warn(clippy::macros_hiding_unsafe_code)]
// compiletest allows unused code by default. But we want to explicitely test
// for this lint here.
#![warn(unused_unsafe)]

extern crate macro_rules;

use macro_rules::unsafe_external_macro;

macro_rules! unsafe_macro {
    ($e:expr) => {
        unsafe { $e }
    };
    (NESTED $e:expr) => {
        unsafe { unsafe_function($e) }
    };
}

unsafe fn unsafe_function(x: *const usize) {
    let _ = std::ptr::read(x);
}

mod no_unsafe_op_in_unsafe_fn {
    use super::*;

    #[allow(unused_unsafe)]
    pub unsafe fn ok(x: *const usize) {
        unsafe_macro!(std::ptr::read(x));
        unsafe_external_macro!(std::ptr::read(x));
    }
}

mod unsafe_op_in_unsafe_fn {
    #![warn(unsafe_op_in_unsafe_fn)]

    use super::*;

    pub unsafe fn bad(x: *const usize) {
        unsafe_macro!(std::ptr::read(x));
        unsafe_macro!(NESTED std::ptr::read(&x));
        unsafe_external_macro!(std::ptr::read(x));
    }

    pub unsafe fn ok(x: *const usize) {
        #[allow(unused_unsafe)]
        unsafe {
            unsafe_macro!(std::ptr::read(x));
            unsafe_external_macro!(std::ptr::read(x));
        }
    }

    #[allow(unused_unsafe)]
    pub unsafe fn unused_unsafe_disabled(x: *const usize) {
        unsafe_macro!(std::ptr::read(x));
        unsafe_external_macro!(std::ptr::read(x));
    }
}

fn main() {
    unsafe {
        no_unsafe_op_in_unsafe_fn::ok(std::ptr::null());
        unsafe_op_in_unsafe_fn::bad(std::ptr::null());
        unsafe_op_in_unsafe_fn::ok(std::ptr::null());
        unsafe_op_in_unsafe_fn::unused_unsafe_disabled(std::ptr::null());
    }
}
