use std::fmt;
use std::ops::Deref;

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct P<T: ?Sized> {
    ptr: Box<T>,
}

#[allow(non_snake_case)]
pub fn P<T: 'static>(value: T) -> P<T> {
    P {
        ptr: Box::new(value),
    }
}

impl<T: fmt::Display> fmt::Display for P<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(&**self, f)
    }
}

impl<T: ?Sized> Deref for P<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.ptr
    }
}

static mut TYVAR_COUNTER: u64 = 0;
pub fn global_counter() -> u64 {
    unsafe {
        let tmp= TYVAR_COUNTER;
        TYVAR_COUNTER += 1;
        tmp
    }
}