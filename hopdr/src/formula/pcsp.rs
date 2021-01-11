use super::Constraint;

pub struct PCSP {
    body: Vec<Constraint>,
    head: Vec<Constraint>,
}