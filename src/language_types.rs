//! Helper types specific to Olea language constructs.

/// The presence or absence of the `anon` keyword in a function parameter or struct field.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IsAnon {
    /// Marked `anon`.
    Anon,
    /// Not marked `anon`.
    NotAnon,
}

impl From<bool> for IsAnon {
    fn from(b: bool) -> Self {
        if b { Self::Anon } else { Self::NotAnon }
    }
}

impl From<IsAnon> for bool {
    fn from(anon: IsAnon) -> Self {
        match anon {
            IsAnon::Anon => true,
            IsAnon::NotAnon => false,
        }
    }
}

impl From<&IsAnon> for bool {
    fn from(anon: &IsAnon) -> Self {
        Self::from(*anon)
    }
}
