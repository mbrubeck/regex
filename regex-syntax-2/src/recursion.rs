#[derive(Debug)]
pub enum Case<Base, Inductive> {
    Base(Base),
    Inductive(Inductive),
}

pub trait Recursion {
    type Value;
    type Base;
    type Inductive;

    fn induct(value: Value) -> Case<Self::Base, Self::Inductive>;
    fn pop(
        base: Self::Base,
        case: Case<Self::Base, Self::Inductive>,
    ) -> Case<Self::Base, Self::Inductive>;
}
