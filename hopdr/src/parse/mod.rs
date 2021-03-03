mod hes;
mod parse;

pub use hes::*;
pub use parse::parse;
use crate::util::P;

pub type Ident = P<String>;
