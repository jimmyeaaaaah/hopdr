mod hes;
mod parse;

use crate::util::P;
pub use hes::*;
pub use parse::parse;

pub type Ident = P<String>;
