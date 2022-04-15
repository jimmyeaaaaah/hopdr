extern crate lazy_static;
#[macro_use]
extern crate log;

pub mod formula;
pub mod parse;
pub mod pdr;
pub mod preprocess;
pub mod solver;
#[macro_use]
pub mod util;


#[cfg(test)]
#[ctor::ctor]
fn init() {
    env_logger::builder()
        .format_timestamp(None)
        .format_module_path(true)
        .format_level(false)
        .init();
}