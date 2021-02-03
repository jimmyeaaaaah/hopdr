use std::{fmt, rc::Rc};
use std::ops::Deref;

#[derive(Debug, Eq, PartialEq)]
pub struct P<T: ?Sized> {
    ptr: Rc<T>,
}

#[allow(non_snake_case)]
pub fn P<T: 'static>(value: T) -> P<T> {
    P {
        ptr: Rc::new(value),
    }
}

impl <T> P<T> {
    pub fn kind<'a>(&'a self) -> &'a T {
        &*self.ptr
    }
}

impl<T> P<T> {
    pub fn new(v: T) -> P<T> {
        P { ptr: Rc::new(v) } 
    }
}

impl<T: fmt::Display> fmt::Display for P<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.kind(), f)
    }
}

impl<T: ?Sized> Deref for P<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.ptr
    }
}

impl<T> Clone for P<T> {
    fn clone(&self) -> P<T> {
        P { ptr: self.ptr.clone() }
    }
}

macro_rules! rc_wrapper {
    ($element: ident: $ty: ty) => {
        pub struct $element {
            ptr: Rc<$ty>
        }
        impl $element {
            pub fn new(elem: $ty) -> $element {
                $element { ptr: Rc::new(elem) }
            }
        }

        impl<T: fmt::Display> fmt::Display for $element {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                fmt::Display::fmt(self.kind(), f)
            }
        }
        
        impl<T: ?Sized> Deref for $element {
            type Target = T;
        
            fn deref(&self) -> &T {
                &self.ptr
            }
        } 
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