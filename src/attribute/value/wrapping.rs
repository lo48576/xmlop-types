//! Attribute value with wrapping quotes.

use std::{convert::TryFrom, error, fmt};

use crate::{
    attribute::{
        value::content::{parse_raw as parse_content, ParseResult as ContentResult},
        QuoteMark,
    },
    parser::{Partial, PartialMapWithStr},
    reference::ReferenceError,
};

/// Parse result of `AttValue`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Extra data follows.
    Extra(Partial<T>),
    /// Invalid Character.
    InvalidCharacter(usize),
    /// Invalid reference.
    InvalidReference(usize, ReferenceError),
    /// Missing closing quote.
    MissingClosing,
    /// Missing opening quote.
    MissingOpening,
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, AttributeValueError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::Extra(part) => Err(AttributeValueError::ExtraData(part.valid_up_to())),
            Self::InvalidCharacter(pos) => Err(AttributeValueError::InvalidCharacter(pos)),
            Self::InvalidReference(pos, e) => Err(AttributeValueError::InvalidReference(pos, e)),
            Self::MissingClosing => Err(AttributeValueError::MissingClosing),
            Self::MissingOpening => Err(AttributeValueError::MissingOpening),
        }
    }
}

/// Parses the given string as `AttValue`.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    let quote = match s.as_bytes().get(0).and_then(|&b| QuoteMark::from_ascii(b)) {
        Some(v) => v,
        None => return ParseResult::MissingOpening,
    };

    assert!(!s.is_empty());
    match parse_content(&s[1..], quote) {
        ContentResult::Complete(_) => ParseResult::MissingClosing,
        ContentResult::InvalidCharacter(part) => {
            ParseResult::InvalidCharacter(1 + part.valid_up_to())
        }
        ContentResult::InvalidReference(part, e) => {
            ParseResult::InvalidReference(1 + part.valid_up_to(), e)
        }
        ContentResult::UnexpectedQuote(part) => {
            let parsed_len = part.valid_up_to() + 2;
            if parsed_len == s.len() {
                ParseResult::Complete(())
            } else {
                ParseResult::Extra(Partial::new((), parsed_len))
            }
        }
    }
}

/// Parses the given string as `AttValue`.
fn parse(s: &str) -> ParseResult<&AttributeValueStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => {
            ParseResult::Complete(unsafe { AttributeValueStr::new_unchecked(s) })
        }
        ParseResult::Extra(part) => ParseResult::Extra(
            part.map_with_str(s, |_, s| unsafe { AttributeValueStr::new_unchecked(s) }),
        ),
        ParseResult::InvalidCharacter(pos) => ParseResult::InvalidCharacter(pos),
        ParseResult::InvalidReference(pos, e) => ParseResult::InvalidReference(pos, e),
        ParseResult::MissingClosing => ParseResult::MissingClosing,
        ParseResult::MissingOpening => ParseResult::MissingOpening,
    }
}

/// Error for `AttValue`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AttributeValueError {
    /// Extra data follows.
    ///
    /// `usize` field is the first byte position of the extra data after `]]>`.
    ExtraData(usize),
    /// Found invalid character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
    /// Found invalid reference.
    ///
    /// `usize` field is the first byte position of the invalid reference.
    InvalidReference(usize, ReferenceError),
    /// Missing closing quote.
    MissingClosing,
    /// Missing opening quote.
    MissingOpening,
}

impl error::Error for AttributeValueError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::InvalidReference(_, e) => Some(e),
            _ => None,
        }
    }
}

impl fmt::Display for AttributeValueError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::ExtraData(pos) => write!(f, "Extra following data at index {}", pos),
            Self::InvalidCharacter(pos) => write!(f, "Invalid character at index {}", pos),
            Self::InvalidReference(pos, e) => {
                write!(f, "Invalid reference at index {}: {}", pos, e)
            }
            Self::MissingClosing => f.write_str("Missing closing quote of an attribute value"),
            Self::MissingOpening => f.write_str("Missing opening quote of an attribute value"),
        }
    }
}

/// String slice for [`AttValue`].
///
/// [`AttValue`]: http://www.w3.org/TR/REC-xml/#NT-AttValue
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct AttributeValueStr(str);

impl AttributeValueStr {
    /// Creates a new `&AttributeValueStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::attribute::{AttributeValueError, AttributeValueStr};
    /// assert!(AttributeValueStr::new_checked("\"valid attribute value\"").is_ok());
    /// assert!(AttributeValueStr::new_checked("'valid attribute value'").is_ok());
    /// assert!(AttributeValueStr::new_checked("\"'\"").is_ok());
    /// assert!(AttributeValueStr::new_checked("'\"'").is_ok());
    /// assert!(AttributeValueStr::new_checked("'&quot;&apos;&amp;&#x3C;'").is_ok());
    ///
    /// assert_eq!(
    ///     AttributeValueStr::new_checked("'foo\u{B}bar'"),
    ///     Err(AttributeValueError::InvalidCharacter(4))
    /// );
    /// assert_eq!(
    ///     AttributeValueStr::new_checked("'foo<bar'"),
    ///     Err(AttributeValueError::InvalidCharacter(4))
    /// );
    /// assert_eq!(
    ///     AttributeValueStr::new_checked("'foo&bar'"),
    ///     Err(AttributeValueError::InvalidReference(
    ///         4,
    ///         xmlop_types::reference::ReferenceError::MissingSemicolon,
    ///     ))
    /// );
    /// assert_eq!(AttributeValueStr::new_checked(""), Err(AttributeValueError::MissingOpening));
    /// assert_eq!(AttributeValueStr::new_checked("foo"), Err(AttributeValueError::MissingOpening));
    /// assert_eq!(AttributeValueStr::new_checked("\"foo'"), Err(AttributeValueError::MissingClosing));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, AttributeValueError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&AttributeValueStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`AttValue`] string.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::attribute::AttributeValueStr;
    /// let s = AttributeValueStr::new("'valid attribute value'");
    /// ```
    ///
    /// [`AttValue`]: http://www.w3.org/TR/REC-xml/#NT-AttValue
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `AttValue` string: {}", e))
    }

    /// Creates a new `&AttributeValueStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`AttValue`] string.
    ///
    /// [`AttValue`]: http://www.w3.org/TR/REC-xml/#NT-AttValue
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }

    /// Returns the quotation mark.
    pub fn quotation(&self) -> QuoteMark {
        QuoteMark::from_ascii(self.as_str().as_bytes()[0])
            .expect("Should never fail: quote mark sholud be representable by `QuoteMark`")
    }
}

/// Owned string for [`AttValue`].
///
/// [`AttValue`]: http://www.w3.org/TR/REC-xml/#NT-AttValue
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AttributeValueString(Box<AttributeValueStr>);

impl_string_types! {
    owned: AttributeValueString,
    slice: AttributeValueStr,
    error_slice: AttributeValueError,
    parse: parse,
    slice_new_unchecked: AttributeValueStr::new_unchecked,
}

impl_string_cmp! {
    owned: AttributeValueString,
    slice: AttributeValueStr,
}

impl_string_cmp_to_string! {
    owned: AttributeValueString,
    slice: AttributeValueStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{
        Complete, Extra, InvalidCharacter, InvalidReference, MissingClosing, MissingOpening,
    };

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw("\"valid attribute value\""), Complete(()));
        assert_eq!(parse_raw("'valid attribute value'"), Complete(()));
        assert_eq!(parse_raw("\"'\""), Complete(()));
        assert_eq!(parse_raw("'\"'"), Complete(()));
        assert_eq!(parse_raw("'&quot;&apos;&amp;&#x3C;'"), Complete(()));

        assert_eq!(parse_raw("\"foo\"bar"), Extra(Partial::new((), 5)));
        assert_eq!(parse_raw("'foo'bar"), Extra(Partial::new((), 5)));
        assert_eq!(parse_raw("'foo\u{B}bar'"), InvalidCharacter(4));
        assert_eq!(
            parse_raw("'foo&bar'"),
            InvalidReference(4, ReferenceError::MissingSemicolon)
        );
        assert_eq!(parse_raw(""), MissingOpening);
        assert_eq!(parse_raw("'"), MissingClosing);
        assert_eq!(parse_raw("\""), MissingClosing);
        assert_eq!(parse_raw("'foo"), MissingClosing);
        assert_eq!(parse_raw("\"foo"), MissingClosing);
    }
}
