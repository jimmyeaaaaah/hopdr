use std::marker::PhantomData;
use std::ops::Deref;
use std::sync::mpsc;
use std::thread;
use std::time;
use std::{fmt, rc::Rc};

//pub trait Kind {
//    type Ty;
//    fn kind<'a>(&'a self) -> &'a Self::Ty;
//}

// readonly pointer
#[derive(Debug, Eq, PartialEq, Hash)]
pub struct P<T: ?Sized> {
    ptr: Rc<T>,
}

#[allow(non_snake_case)]
pub fn P<T: 'static>(value: T) -> P<T> {
    P {
        ptr: Rc::new(value),
    }
}

impl<T> P<T> {
    pub fn kind<'a>(&'a self) -> &'a T {
        &*self.ptr
    }
    pub fn ptr_id(&self) -> usize {
        self.ptr.as_ref() as *const T as usize
    }
}

#[test]
fn test_id() {
    let x = P::new(1);
    let y = x.clone();
    let z = P::new(1);
    assert_eq!(x.ptr_id(), y.ptr_id());
    assert_ne!(x.ptr_id(), z.ptr_id())
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
        P {
            ptr: self.ptr.clone(),
        }
    }
}

impl<T> From<T> for P<T> {
    fn from(x: T) -> P<T> {
        P::new(x)
    }
}

// unique pointer
#[derive(Debug, Eq, PartialEq)]
pub struct Unique<T: ?Sized> {
    ptr: Box<T>,
}

#[allow(non_snake_case)]
pub fn Unique<T: 'static>(value: T) -> Unique<T> {
    Unique {
        ptr: Box::new(value),
    }
}

impl<T> Unique<T> {
    pub fn kind<'a>(&'a self) -> &'a T {
        &*self.ptr
    }
    pub fn into(self) -> T {
        *self.ptr
    }
}

impl<T> Unique<T> {
    pub fn new(v: T) -> Unique<T> {
        Unique { ptr: Box::new(v) }
    }
}

impl<T: fmt::Display> fmt::Display for Unique<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.kind(), f)
    }
}

impl<T: ?Sized> Deref for Unique<T> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.ptr
    }
}

// Phantom Pointer

#[derive(Debug, Eq, PartialEq, Hash)]
pub struct PhantomPtr<T: ?Sized, S> {
    ptr: Rc<T>,
    __phantom: PhantomData<S>,
}

#[allow(non_snake_case)]
pub fn PhantomPtr<T: 'static, S>(value: T) -> PhantomPtr<T, S> {
    PhantomPtr {
        ptr: Rc::new(value),
        __phantom: PhantomData,
    }
}

impl<T, S> PhantomPtr<T, S> {
    pub fn kind<'a>(&'a self) -> &'a T {
        &*self.ptr
    }
}

impl<T, S> PhantomPtr<T, S> {
    pub fn new(v: T) -> PhantomPtr<T, S> {
        PhantomPtr {
            ptr: Rc::new(v),
            __phantom: PhantomData,
        }
    }
}

impl<T: fmt::Display, S> fmt::Display for PhantomPtr<T, S> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.kind(), f)
    }
}

impl<T: ?Sized, S> Deref for PhantomPtr<T, S> {
    type Target = T;

    fn deref(&self) -> &T {
        &self.ptr
    }
}

impl<T, S> Clone for PhantomPtr<T, S> {
    fn clone(&self) -> PhantomPtr<T, S> {
        PhantomPtr {
            ptr: self.ptr.clone(),
            __phantom: PhantomData,
        }
    }
}

impl<T, S> From<T> for PhantomPtr<T, S> {
    fn from(x: T) -> PhantomPtr<T, S> {
        PhantomPtr::new(x)
    }
}

static mut TYVAR_COUNTER: u64 = 0;
pub fn global_counter() -> u64 {
    unsafe {
        let tmp = TYVAR_COUNTER;
        TYVAR_COUNTER += 1;
        tmp
    }
}
#[macro_export]
macro_rules! title {
    ($arg:tt) => {{
        use colored::Colorize;
        debug!("{}{}{}", "[".bold(), $arg.bold(), "]".bold());
    }};
}

// Function executor with timeouts
// idea taken from https://gist.github.com/junha1/8ebaf53f46ea6fc14ab6797b9939b0f8,

#[derive(Debug, Clone, Copy)]
pub enum ExecutionError {
    Timeout,
    Panic,
    Ctrlc,
}

enum ExecResult {
    Ctrlc,
    Succeeded,
    Panic,
}

const STACK_SIZE: usize = 4 * 1024 * 1024;

/// returns Some(x) if `f` finishes within `timeout`; None otherwise.
/// if timeout is None, the execution continues until ctrl-c or termination of the
/// given procedure.
pub fn executes_with_timeout_and_ctrlc<T: Send + 'static, F: FnOnce() -> T + Send + 'static>(
    f: F,
    timeout: Option<time::Duration>,
) -> Result<T, ExecutionError> {
    let (sender, recv) = mpsc::channel();
    // setting up ctrlc handler
    {
        let sender = sender.clone();
        ctrlc::set_handler(move || sender.clone().send(ExecResult::Ctrlc).unwrap())
            .expect("Error setting Ctrl-C handler");
    }
    // thread trampoline to handle panic in `f`
    let join_handler = thread::spawn(move || {
        let x = thread::Builder::new()
            .stack_size(STACK_SIZE)
            .spawn(move || f())
            .unwrap()
            .join();
        let s = match &x {
            Ok(_) => ExecResult::Succeeded,
            Err(_) => ExecResult::Panic,
        };
        sender.send(s).unwrap();
        x.unwrap()
    });
    let r = match timeout {
        Some(timeout) => recv.recv_timeout(timeout),
        None => recv
            .recv()
            .map_err(|_| mpsc::RecvTimeoutError::Disconnected),
    };
    match r {
        Ok(ExecResult::Ctrlc) => return Err(ExecutionError::Ctrlc),
        Ok(ExecResult::Succeeded) => (),
        Err(mpsc::RecvTimeoutError::Timeout) => return Err(ExecutionError::Timeout),
        Ok(ExecResult::Panic) | Err(mpsc::RecvTimeoutError::Disconnected) => {
            return Err(ExecutionError::Panic)
        }
    }
    join_handler.join().map_err(|_| ExecutionError::Panic)
}
