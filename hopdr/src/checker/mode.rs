use core::fmt;

use crate::formula::Ident;
use crate::util::P;

use rpds::HashTrieMap;

#[derive(Clone, Debug)]
pub enum ModeKind {
    Var(Ident),
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

    pub fn is_int(&self) -> bool {
        match self.kind() {
            ModeKind::In | ModeKind::Out | ModeKind::InOut | ModeKind::Var(_) => true,
            ModeKind::Prop | ModeKind::Fun(_, _) => false,
        }
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

    pub fn mk_prop() -> Self {
        P(ModeKind::Prop)
    }

    pub fn mk_inout() -> Self {
        P(ModeKind::InOut)
    }

    pub fn mk_fun(t1: Self, t2: Self) -> Self {
        P(ModeKind::Fun(t1, t2))
    }

    pub fn new_var() -> Self {
        let id = Ident::fresh();
        P(ModeKind::Var(id))
    }

    pub fn is_var(&self) -> bool {
        matches!(self.kind(), ModeKind::Var(_))
    }

    /// integers are all treated as `-`
    pub fn from_hflty(ty: &crate::formula::Type) -> Self {
        match ty.kind() {
            crate::formula::TypeKind::Proposition => Self::mk_prop(),
            crate::formula::TypeKind::Integer => Self::mk_in(),
            crate::formula::TypeKind::Arrow(t1, t2) => {
                let t1 = Self::from_hflty(t1);
                let t2 = Self::from_hflty(t2);
                Self::mk_fun(t1, t2)
            }
        }
    }
}

#[derive(Clone, Debug)]
pub struct ModeEnv {
    env: HashTrieMap<Ident, Mode>,
}

impl ModeEnv {
    #[allow(dead_code)]
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

impl std::iter::FromIterator<(Ident, Mode)> for ModeEnv {
    fn from_iter<T: IntoIterator<Item = (Ident, Mode)>>(iter: T) -> Self {
        ModeEnv {
            env: HashTrieMap::from_iter(iter),
        }
    }
}

impl fmt::Display for Mode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self.kind() {
            ModeKind::In => write!(f, "-"),
            ModeKind::Out => write!(f, "+"),
            ModeKind::InOut => write!(f, "-/+"),
            ModeKind::Prop => write!(f, "*"),
            ModeKind::Fun(t1, t2) => write!(f, "({} -> {})", t1, t2),
            ModeKind::Var(x) => write!(f, "{}", x),
        }
    }
}

impl fmt::Display for ModeEnv {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut first = true;
        for (x, m) in self.iter() {
            if first {
                first = false;
            } else {
                write!(f, ", ")?;
            }
            write!(f, "{}: {}", x, m)?;
        }
        Ok(())
    }
}
