/// A simple binary sum type.
///
/// This is occasionally useful in an ad hoc fashion.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Either<Left, Right> {
    Left(Left),
    Right(Right),
}

impl<Left, Right> Either<Left, Right> {
    pub fn unwrap_left(self) -> Left {
        match self {
            Either::Left(left) => left,
            Either::Right(_) => panic!("unwrap_left but contained Right"),
        }
    }

    pub fn unwrap_right(self) -> Right {
        match self {
            Either::Left(_) => panic!("unwrap_right but contained Left"),
            Either::Right(right) => right,
        }
    }
}
