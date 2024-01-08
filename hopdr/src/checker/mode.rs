use crate::formula::Ident;
use crate::util::P;

use rpds::HashTrieMap;

#[derive(Clone, Debug)]
pub enum ModeKind {
    In,
    Out,
    InOut,
    Prop,
    Fun(Mode, Mode),
}

pub type Mode = P<ModeKind>;

impl Mode {
    pub fn is_in(&self) -> bool {
        matches!(self.kind(), ModeKind::In)
    }

    pub fn is_out(&self) -> bool {
        matches!(self.kind(), ModeKind::Out)
    }

    pub fn is_fun<'a>(&'a self) -> (&'a Mode, &'a Mode) {
        match self.kind() {
            ModeKind::Fun(t1, t2) => (t1, t2),
            _ => panic!("not a function type"),
        }
    }

    pub fn is_prop(&self) -> bool {
        matches!(self.kind(), ModeKind::Prop)
    }

    pub fn mk_in() -> Self {
        P(ModeKind::In)
    }

    pub fn mk_out() -> Self {
        P(ModeKind::Out)
    }

    pub fn mk_fun(t1: Self, t2: Self) -> Self {
        P(ModeKind::Fun(t1, t2))
    }
}

#[derive(Clone, Debug)]
pub struct ModeEnv {
    env: HashTrieMap<Ident, Mode>,
}

impl ModeEnv {
    pub fn new() -> Self {
        ModeEnv {
            env: HashTrieMap::new(),
        }
    }

    pub fn insert(&self, x: Ident, m: Mode) -> ModeEnv {
        ModeEnv {
            env: self.env.insert(x, m),
        }
    }

    pub fn get(&self, x: &Ident) -> Option<&Mode> {
        self.env.get(x)
    }

    pub fn iter(&self) -> impl Iterator<Item = (&Ident, &Mode)> {
        self.env.iter()
    }
}
