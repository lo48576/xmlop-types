//! [`CharData`], content of text node except CDATA section and references.
//!
//! About `CharData`, see [Extensible Markup Language (XML) 1.0 (Fifth Edition)][`CharData`].
//!
//! [`CharData`]: http://www.w3.org/TR/REC-xml/#NT-CharData

use std::{convert::TryFrom, error, fmt};

use crate::parser::{Partial, PartialMapWithStr};

/// Parse result of `CharData`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// CDATA section closed unexpectedly.
    CdataSectionClosed(Partial<T>),
    /// Unexpected ampersand.
    UnexpectedAmpersand(Partial<T>),
    /// Unexpected lt (`<`) symbol.
    UnexpectedLt(Partial<T>),
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, CharDataError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::CdataSectionClosed(part) => {
                Err(CharDataError::CdataSectionClosed(part.valid_up_to()))
            }
            Self::UnexpectedAmpersand(part) => {
                Err(CharDataError::UnexpectedAmpersand(part.valid_up_to()))
            }
            Self::UnexpectedLt(part) => Err(CharDataError::UnexpectedLt(part.valid_up_to())),
        }
    }
}

/// Parses the given string as `CharData`.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    // Existence of stray `>` is syntactically allowed by the spec (see [`CharData`]), but it is
    // strongly discouraged.
    //
    // > The right angle bracket (`>`) may be represented using the string "`&gt;`", and MUST, for
    // > compatibility, be escaped using either "`&gt;`" or a character reference when it appears in
    // > the string "`]]>`" in content, when that string is not marking the end of a CDATA section.
    // >
    // > --- <https://www.w3.org/TR/2008/REC-xml-20081126/#syntax>
    let mut rest = s;
    while let Some(rest_pos) = rest
        .as_bytes()
        .iter()
        .position(|&b| b == b'&' || b == b'<' || b == b']')
    {
        let pos = s.len() - rest.len() + rest_pos;
        match rest.as_bytes()[rest_pos] {
            b'&' => {
                return ParseResult::UnexpectedAmpersand(Partial::new((), pos));
            }
            b'<' => {
                let pos = s.len() - rest.len() + rest_pos;
                return ParseResult::UnexpectedLt(Partial::new((), pos));
            }
            b']' => {
                let next_rest = &s[(pos + 1)..];
                if next_rest.starts_with("]>") {
                    return ParseResult::CdataSectionClosed(Partial::new((), pos));
                }
                rest = next_rest;
            }
            _ => unreachable!("Not finding that"),
        }
    }

    ParseResult::Complete(())
}

/// Parses the given string as `CharData`.
fn parse(s: &str) -> ParseResult<&CharDataStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => {
            ParseResult::Complete(unsafe { CharDataStr::new_unchecked(s) })
        }
        ParseResult::CdataSectionClosed(part) => ParseResult::CdataSectionClosed(
            part.map_with_str(s, |_, s| unsafe { CharDataStr::new_unchecked(s) }),
        ),
        ParseResult::UnexpectedAmpersand(part) => ParseResult::UnexpectedAmpersand(
            part.map_with_str(s, |_, s| unsafe { CharDataStr::new_unchecked(s) }),
        ),
        ParseResult::UnexpectedLt(part) => ParseResult::UnexpectedLt(
            part.map_with_str(s, |_, s| unsafe { CharDataStr::new_unchecked(s) }),
        ),
    }
}

/// Error for `CharData`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CharDataError {
    /// CDATA section closed unexpectedly.
    ///
    /// `usize` field is the first byte position of the closing sequence `]]>`.
    CdataSectionClosed(usize),
    /// Unexpected ampersand.
    ///
    /// `usize` field is the first byte position of the character.
    UnexpectedAmpersand(usize),
    /// Unexpected lt (`<`) symbol.
    ///
    /// `usize` field is the first byte position of the character.
    UnexpectedLt(usize),
}

impl error::Error for CharDataError {}

impl fmt::Display for CharDataError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CharDataError::CdataSectionClosed(pos) => {
                write!(f, "CDATA section closed unexpectedly at index {}", pos)
            }
            CharDataError::UnexpectedAmpersand(pos) => {
                write!(f, "Unexpected ampersand character at index {}", pos)
            }
            CharDataError::UnexpectedLt(pos) => {
                write!(f, "Unexpected `<` character at index {}", pos)
            }
        }
    }
}

/// String slice for [`CharData`].
///
/// [`CharData`]: http://www.w3.org/TR/REC-xml/#NT-CharData
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CharDataStr(str);

impl CharDataStr {
    /// Creates a new `&CharDataStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::char_data::{CharDataError, CharDataStr};
    /// assert!(CharDataStr::new_checked("ValidCharData").is_ok());
    /// assert!(CharDataStr::new_checked("").is_ok());
    ///
    /// assert_eq!(CharDataStr::new_checked("]]>"), Err(CharDataError::CdataSectionClosed(0)));
    /// assert_eq!(
    ///     CharDataStr::new_checked("foo]]>bar"),
    ///     Err(CharDataError::CdataSectionClosed(3))
    /// );
    /// assert_eq!(
    ///     CharDataStr::new_checked("foo&bar"),
    ///     Err(CharDataError::UnexpectedAmpersand(3))
    /// );
    /// assert_eq!(CharDataStr::new_checked("foo<bar"), Err(CharDataError::UnexpectedLt(3)));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, CharDataError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&CharDataStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`CharData`] string.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::char_data::CharDataStr;
    /// let s = CharDataStr::new("ValidCharData");
    /// ```
    ///
    /// [`CharData`]: http://www.w3.org/TR/REC-xml/#NT-CharData
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `CharData` string: {}", e))
    }

    /// Creates a new `&CharDataStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`CharData`] string.
    ///
    /// [`CharData`]: http://www.w3.org/TR/REC-xml/#NT-CharData
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for [`CharData`].
///
/// [`CharData`]: http://www.w3.org/TR/REC-xml/#NT-CharData
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CharDataString(Box<CharDataStr>);

impl_string_types! {
    owned: CharDataString,
    slice: CharDataStr,
    error_slice: CharDataError,
    parse: parse,
    slice_new_unchecked: CharDataStr::new_unchecked,
}

impl_string_cmp! {
    owned: CharDataString,
    slice: CharDataStr,
}

impl_string_cmp_to_string! {
    owned: CharDataString,
    slice: CharDataStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{CdataSectionClosed, Complete, UnexpectedAmpersand, UnexpectedLt};

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw(""), Complete(()));
        assert_eq!(parse_raw("valid CharData"), Complete(()));
        // Existence of stray `>` is syntactically allowed by the spec (see [`CharData`]), but it is
        // strongly discouraged.
        //
        // > The right angle bracket (`>`) may be represented using the string "`&gt;`", and MUST,
        // > for compatibility, be escaped using either "`&gt;`" or a character reference when it
        // > appears in > the string "`]]>`" in content, when that string is not marking the end of
        // > a CDATA section.
        // >
        // > --- <https://www.w3.org/TR/2008/REC-xml-20081126/#syntax>
        assert_eq!(parse_raw("foo>bar"), Complete(()));
        assert_eq!(parse_raw("]>"), Complete(()));

        assert_eq!(parse_raw("]]>"), CdataSectionClosed(Partial::new((), 0)));
        assert_eq!(parse_raw("]]]>"), CdataSectionClosed(Partial::new((), 1)));
        assert_eq!(parse_raw("foo]]>"), CdataSectionClosed(Partial::new((), 3)));
        assert_eq!(parse_raw("&lt;"), UnexpectedAmpersand(Partial::new((), 0)));
        assert_eq!(
            parse_raw("foo&bar"),
            UnexpectedAmpersand(Partial::new((), 3))
        );
        assert_eq!(
            parse_raw("foo&lt;bar"),
            UnexpectedAmpersand(Partial::new((), 3))
        );
        assert_eq!(parse_raw("foo<bar"), UnexpectedLt(Partial::new((), 3)));
        assert_eq!(parse_raw("foo<elem />"), UnexpectedLt(Partial::new((), 3)));
        assert_eq!(parse_raw("foo<elem />"), UnexpectedLt(Partial::new((), 3)));
    }
}
