//! A collection of data types used throughout the compiler.

/// A sorted map.
pub type Map<K, V> = std::collections::BTreeMap<K, V>;

/// A sorted set.
pub type Set<K> = std::collections::BTreeSet<K>;

/// An insertion order preserving map.
pub use indexmap::IndexMap;

/// An insertion order preserving set.
pub use indexmap::IndexSet;

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
