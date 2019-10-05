//! [`Name`].
//!
//! About `Name`, see [Extensible Markup Language (XML) 1.0 (Fifth Edition)][`Name`].
//!
//! [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name

use std::{convert::TryFrom, error, fmt};

use crate::parser::{
    chars::{is_name_char, is_name_start_char},
    Partial, PartialMapWithStr,
};

/// Parse result of `Name`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Empty value.
    Empty,
    /// Invalid character.
    InvalidCharacter(Option<Partial<T>>),
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, NameError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::Empty => Err(NameError::Empty),
            Self::InvalidCharacter(part) => Err(NameError::InvalidCharacter(
                part.map_or(0, |part| part.valid_up_to()),
            )),
        }
    }
}

/// Parses the given string as `Name`.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    let mut chars = s.char_indices();
    match chars.next() {
        Some((_, first)) if !is_name_start_char(first) => {
            return ParseResult::InvalidCharacter(None);
        }
        Some(_) => {}
        None => return ParseResult::Empty,
    }
    if let Some((pos, _)) = chars.find(|(_, c)| !is_name_char(*c)) {
        return ParseResult::InvalidCharacter(Some(Partial::new((), pos)));
    }

    ParseResult::Complete(())
}

/// Parses the given string as `Name`.
fn parse(s: &str) -> ParseResult<&NameStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => ParseResult::Complete(unsafe { NameStr::new_unchecked(s) }),
        ParseResult::Empty => ParseResult::Empty,
        ParseResult::InvalidCharacter(part) => ParseResult::InvalidCharacter(
            part.map_with_str(s, |_, s| unsafe { NameStr::new_unchecked(s) }),
        ),
    }
}

/// Error for `Name`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NameError {
    /// The string is empty.
    Empty,
    /// The string has an invaild character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
}

impl error::Error for NameError {}

impl fmt::Display for NameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NameError::Empty => write!(f, "empty string"),
            NameError::InvalidCharacter(pos) => write!(f, "invalid character at index {}", pos),
        }
    }
}

/// String slice for XML [`Name`].
///
/// [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NameStr(str);

impl NameStr {
    /// Creates a new `&NameStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::name::{NameError, NameStr};
    /// assert!(NameStr::new_checked("ValidName").is_ok());
    ///
    /// assert_eq!(NameStr::new_checked(""), Err(NameError::Empty));
    /// assert_eq!(NameStr::new_checked("012InvalidName"), Err(NameError::InvalidCharacter(0)));
    /// assert_eq!(NameStr::new_checked("foo bar"), Err(NameError::InvalidCharacter(3)));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, NameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&NameStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`Name`] string.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::name::NameStr;
    /// let name = NameStr::new("ValidName");
    /// ```
    ///
    /// [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `Name` string: {}", e))
    }

    /// Creates a new `&NameStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`Name`] string.
    ///
    /// [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for XML [`Name`].
///
/// [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NameString(Box<NameStr>);

impl_string_types! {
    owned: NameString,
    slice: NameStr,
    error_slice: NameError,
    parse: parse,
    slice_new_unchecked: NameStr::new_unchecked,
}

impl_string_cmp! {
    owned: NameString,
    slice: NameStr,
}

impl_string_cmp_to_string! {
    owned: NameString,
    slice: NameStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{Complete, Empty, InvalidCharacter};

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw("Valid-Name"), Complete(()));

        assert_eq!(parse_raw(""), Empty);
        assert_eq!(parse_raw("012InvalidName"), InvalidCharacter(None));
        assert_eq!(
            parse_raw("foo bar"),
            InvalidCharacter(Some(Partial::new((), 3)))
        );
        assert_eq!(
            parse_raw("foo>bar"),
            InvalidCharacter(Some(Partial::new((), 3)))
        );
        assert_eq!(
            parse_raw("foo<bar"),
            InvalidCharacter(Some(Partial::new((), 3)))
        );
        assert_eq!(
            parse_raw("foo&bar"),
            InvalidCharacter(Some(Partial::new((), 3)))
        );
    }
}
