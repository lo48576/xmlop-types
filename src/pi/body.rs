//! Body part (after PI target) of a processing instruction.

use std::{convert::TryFrom, error, fmt};

use crate::parser::{
    chars::{is_xml_char, is_xml_ws},
    Partial, PartialMapWithStr,
};

/// Parse result of PI body.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Invalid character.
    InvalidCharacter(Partial<T>),
    /// Missing leading whitespace.
    MissingLeadingWhitespace,
    /// PI closed.
    PiClosed(Partial<T>),
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, PiBodyError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::InvalidCharacter(part) => Err(PiBodyError::InvalidCharacter(part.valid_up_to())),
            Self::MissingLeadingWhitespace => Err(PiBodyError::MissingLeadingWhitespace),
            Self::PiClosed(part) => Err(PiBodyError::PiClosed(part.valid_up_to())),
        }
    }
}

/// Parses the given string as PI body.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    if s.is_empty() {
        return ParseResult::Complete(());
    }
    let mut chars = s.char_indices();
    match chars.find(|&(_, c)| !is_xml_ws(c)) {
        Some((0, _)) => {
            // No whitespaces.
            return ParseResult::MissingLeadingWhitespace;
        }
        Some(_) => {}
        None => {
            // All characters are whitespace.
            return ParseResult::Complete(());
        }
    };

    while let Some((pos, c)) = chars.next() {
        if !is_xml_char(c) {
            return ParseResult::InvalidCharacter(Partial::new((), pos));
        }
        if c == '?' && chars.as_str().starts_with('>') {
            return ParseResult::PiClosed(Partial::new((), pos));
        }
    }

    ParseResult::Complete(())
}

/// Parses the given string as PI body.
fn parse(s: &str) -> ParseResult<&PiBodyStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => ParseResult::Complete(unsafe { PiBodyStr::new_unchecked(s) }),
        ParseResult::InvalidCharacter(part) => ParseResult::InvalidCharacter(
            part.map_with_str(s, |_, s| unsafe { PiBodyStr::new_unchecked(s) }),
        ),
        ParseResult::MissingLeadingWhitespace => ParseResult::MissingLeadingWhitespace,
        ParseResult::PiClosed(part) => ParseResult::PiClosed(
            part.map_with_str(s, |_, s| unsafe { PiBodyStr::new_unchecked(s) }),
        ),
    }
}

/// Error for PI body.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PiBodyError {
    /// Found invalid character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
    /// Missing leading whitespace.
    MissingLeadingWhitespace,
    /// Found close marker of processing instruction.
    ///
    /// `usize` field is the first byte position of the closing sequence `?>`.
    PiClosed(usize),
}

impl error::Error for PiBodyError {}

impl fmt::Display for PiBodyError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PiBodyError::InvalidCharacter(pos) => write!(f, "Invalid character at index {}", pos),
            PiBodyError::MissingLeadingWhitespace => f.write_str("Missing leading whitespace"),
            PiBodyError::PiClosed(pos) => {
                write!(f, "Processing instruction is closed at index {}", pos)
            }
        }
    }
}

/// String slice for PI body.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PiBodyStr(str);

impl PiBodyStr {
    /// Creates a new `&PiBodyStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::pi::{PiBodyError, PiBodyStr};
    /// assert!(PiBodyStr::new_checked("").is_ok());
    /// assert!(PiBodyStr::new_checked(" valid pi body").is_ok());
    /// assert!(PiBodyStr::new_checked(" >foo?<&").is_ok());
    ///
    /// assert_eq!(PiBodyStr::new_checked("foo"), Err(PiBodyError::MissingLeadingWhitespace));
    /// assert_eq!(PiBodyStr::new_checked(" foo\u{B}bar"), Err(PiBodyError::InvalidCharacter(4)));
    /// assert_eq!(PiBodyStr::new_checked(" foo?>bar"), Err(PiBodyError::PiClosed(4)));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, PiBodyError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&PiBodyStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid PI body.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::pi::PiBodyStr;
    /// let s = PiBodyStr::new(" valid PI body");
    /// ```
    ///
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid PI body: {}", e))
    }

    /// Creates a new `&PiBodyStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid PI body.
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for PI body.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PiBodyString(Box<PiBodyStr>);

impl_string_types! {
    owned: PiBodyString,
    slice: PiBodyStr,
    error_slice: PiBodyError,
    parse: parse,
    slice_new_unchecked: PiBodyStr::new_unchecked,
}

impl_string_cmp! {
    owned: PiBodyString,
    slice: PiBodyStr,
}

impl_string_cmp_to_string! {
    owned: PiBodyString,
    slice: PiBodyStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{Complete, InvalidCharacter, MissingLeadingWhitespace, PiClosed};

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw(""), Complete(()));
        assert_eq!(parse_raw(" valid pi body"), Complete(()));
        assert_eq!(parse_raw(" >foo?<&"), Complete(()));

        assert_eq!(
            parse_raw(" foo\u{B}bar"),
            InvalidCharacter(Partial::new((), 4))
        );
        assert_eq!(parse_raw("foo"), MissingLeadingWhitespace);
        assert_eq!(parse_raw(" foo?>bar"), PiClosed(Partial::new((), 4)));
    }
}
