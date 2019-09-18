//! Parser-related stuff.

pub(crate) mod chars;

/// Parsing result of partially read content.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) struct Partial<T> {
    /// Parsed value.
    value: T,
    /// Byte index in the given string up to which the content is valid.
    ///
    /// In other words, `&source_str[..valid_up_to]` was successfully parsed.
    valid_up_to: usize,
}

impl<T> Partial<T> {
    /// Creates a new `Partial`.
    pub(crate) fn new(value: T, valid_up_to: usize) -> Self {
        Self { value, valid_up_to }
    }

    /// Maps the parsed value with the given function.
    pub(crate) fn valid_up_to(&self) -> usize {
        self.valid_up_to
    }
}

/// A trait to provide `.map_with_str()` for `Partial<T>` and `Option<Partial<T>>`.
pub(crate) trait PartialMapWithStr<'a, T, U: 'a> {
    /// Mapped type.
    type Target;

    /// Replaces the current value to the string mapped by the given function.
    fn map_with_str<F>(self, s: &'a str, op: F) -> Self::Target
    where
        F: FnOnce(T, &'a str) -> U;
}

impl<'a, T, U: 'a> PartialMapWithStr<'a, T, U> for Partial<T> {
    type Target = Partial<U>;

    fn map_with_str<F>(self, s: &'a str, op: F) -> Partial<U>
    where
        F: FnOnce(T, &'a str) -> U,
    {
        Partial {
            value: op(self.value, &s[..self.valid_up_to]),
            valid_up_to: self.valid_up_to,
        }
    }
}

impl<'a, T, U: 'a> PartialMapWithStr<'a, T, U> for Option<Partial<T>> {
    type Target = Option<Partial<U>>;

    fn map_with_str<F>(self, s: &'a str, op: F) -> Option<Partial<U>>
    where
        F: FnOnce(T, &'a str) -> U,
    {
        self.map(|partial| partial.map_with_str(s, op))
    }
}
