use crate::util::P;

pub enum ModeKind {
    In,
    Out,
    Fun(Mode, Mode),
}

type Mode = P<ModeKind>;

impl Mode {
    pub fn is_in(&self) -> bool {
        matches!(self.kind(), ModeKind::In)
    }

    pub fn is_out(&self) -> bool {
        matches!(self.kind(), ModeKind::Out)
    }

    pub fn is_fun(&self) -> bool {
        matches!(self.kind(), ModeKind::Fun(_, _))
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
