pub mod derivation;
pub mod engine;
pub mod fml;
mod infer;
mod optimizer;
pub mod rtype;

pub use engine::run;
use std::fmt;

#[derive(Debug)]
pub enum VerificationResult {
    Valid(ValidCertificate),
    Invalid,
    Unknown,
}

#[derive(Debug)]
pub struct ValidCertificate {
    pub certificate: rtype::TypeEnvironment<rtype::PolymorphicType<rtype::Ty>>,
}
impl ValidCertificate {
    fn new(certificate: rtype::TypeEnvironment<rtype::PolymorphicType<rtype::Ty>>) -> Self {
        Self { certificate }
    }
}

impl fmt::Display for VerificationResult {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        use VerificationResult::*;
        write!(
            f,
            "{}",
            match self {
                Valid(_) => "valid",
                Invalid => "invalid",
                Unknown => "unknown",
            }
        )
    }
}

#[derive(Default)]
pub struct PDRConfig {
    dump_tex_progress: bool,
}

impl PDRConfig {
    pub fn new() -> Self {
        Self::default()
    }
    pub fn dump_tex_progress(mut self, dump_tex_progress: bool) -> Self {
        self.dump_tex_progress = dump_tex_progress;
        self
    }
}

//fn infer_nu_validity(vc: )
