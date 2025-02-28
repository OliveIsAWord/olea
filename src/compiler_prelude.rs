//! A collection of data types and functions used throughout the compiler.

/// A sorted map.
pub type Map<K, V> = std::collections::BTreeMap<K, V>;

/// A sorted set.
pub type Set<K> = std::collections::BTreeSet<K>;

/// An insertion order preserving map.
pub use indexmap::IndexMap;

// /// An insertion order preserving set.
// pub use indexmap::IndexSet;

/// An owned string type that is cheap to clone.
pub type Str = std::rc::Rc<str>;

/// A source span, a single subsection of a source file corresponding to an item.
pub type Span = core::ops::Range<usize>;

/// A string that carries its own span.
pub type Name = Spanned<Str>;

/// A wrapper type for associating an item with a source span. This type is generally aliased by an item type `Foo` wrapping around a `FooKind`.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Spanned<T> {
    /// The inner value.
    pub kind: T,
    /// The span corresponding to the inner value.
    pub span: Span,
}

/// "Zips" two iterators together, asserting that the two are equal in length.
pub fn zip<A, B>(a: A, b: B) -> impl Iterator<Item = (A::Item, B::Item)>
where
    A: IntoIterator,
    B: IntoIterator,
    A::IntoIter: ExactSizeIterator,
    B::IntoIter: ExactSizeIterator,
{
    let a = a.into_iter();
    let b = b.into_iter();
    assert_eq!(a.len(), b.len(), "zipped iterators of unequal length");
    std::iter::zip(a, b)
}

/// The kinds of comparison.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Cmp {
    Lt,
    Le,
    Eq,
    Ne,
    Gt,
    Ge,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum IsMut {
    Const,
    Mut,
}

impl From<bool> for IsMut {
    fn from(b: bool) -> Self {
        if b { Self::Mut } else { Self::Const }
    }
}

impl From<IsMut> for bool {
    fn from(is_mut: IsMut) -> Self {
        match is_mut {
            IsMut::Const => false,
            IsMut::Mut => true,
        }
    }
}

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
