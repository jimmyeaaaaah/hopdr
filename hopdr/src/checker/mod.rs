use crate::formula::hes::Problem;
use crate::formula::Constraint;
use crate::preprocess::Context;

pub struct Config {
    context: Context,
}

impl Config {
    pub fn new(context: Context) -> Self {
        Config { context }
    }
}

pub fn run(problem: Problem<Constraint>, config: &Config) {
    unimplemented!()
}
