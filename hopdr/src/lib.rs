extern crate lazy_static;
#[macro_use]
extern crate log;

pub mod formula;
pub mod parse;
pub mod pdr;
pub mod preprocess;
pub mod solver;
pub mod stat;
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

pub struct Configuration {
    pub inlining: bool,
    pub remove_disjunction: bool,
}

impl Default for Configuration {
    fn default() -> Self {
        Configuration {
            inlining: true,
            remove_disjunction: false,
        }
    }
}

impl Configuration {
    pub fn new() -> Self {
        Self::default()
    }

    /// set inlining
    pub fn inlining(mut self, inlining: bool) -> Self {
        self.inlining = inlining;
        self
    }

    /// set remove_disjunction
    pub fn remove_disjunction(mut self, remove_disjunction: bool) -> Self {
        self.remove_disjunction = remove_disjunction;
        self
    }
}
