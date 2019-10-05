//! [`CData`], content inside a CDATA section.
//!
//! About `CData`, see [Extensible Markup Language (XML) 1.0 (Fifth Edition)][`CData`].
//!
//! [`CData`]: http://www.w3.org/TR/REC-xml/#NT-CData

use std::{convert::TryFrom, error, fmt};

use crate::parser::{chars::is_xml_char, Partial, PartialMapWithStr};

/// Parse result of `CData`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// CDATA section closed unexpectedly.
    CdataSectionClosed(Partial<T>),
    /// Invalid Character.
    InvalidCharacter(Partial<T>),
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, CdataError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::CdataSectionClosed(part) => {
                Err(CdataError::CdataSectionClosed(part.valid_up_to()))
            }
            Self::InvalidCharacter(part) => Err(CdataError::InvalidCharacter(part.valid_up_to())),
        }
    }
}

/// Parses the given string as `CData`.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    let mut chars = s.char_indices();
    while let Some((pos, c)) = chars.next() {
        if !is_xml_char(c) {
            return ParseResult::InvalidCharacter(Partial::new((), pos));
        }
        if c == ']' && chars.as_str().starts_with("]>") {
            return ParseResult::CdataSectionClosed(Partial::new((), pos));
        }
    }

    ParseResult::Complete(())
}

/// Parses the given string as `CData`.
fn parse(s: &str) -> ParseResult<&CdataStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => ParseResult::Complete(unsafe { CdataStr::new_unchecked(s) }),
        ParseResult::CdataSectionClosed(part) => ParseResult::CdataSectionClosed(
            part.map_with_str(s, |_, s| unsafe { CdataStr::new_unchecked(s) }),
        ),
        ParseResult::InvalidCharacter(part) => ParseResult::InvalidCharacter(
            part.map_with_str(s, |_, s| unsafe { CdataStr::new_unchecked(s) }),
        ),
    }
}

/// Error for `CData`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CdataError {
    /// CDATA section closed unexpectedly.
    ///
    /// `usize` field is the first byte position of the closing sequence `]]>`.
    CdataSectionClosed(usize),
    /// Found invalid character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
}

impl error::Error for CdataError {}

impl fmt::Display for CdataError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CdataError::CdataSectionClosed(pos) => {
                write!(f, "Unexpected closing sequence at index {}", pos)
            }
            CdataError::InvalidCharacter(pos) => write!(f, "Invalid character at index {}", pos),
        }
    }
}

/// String slice for [`CData`].
///
/// [`CData`]: http://www.w3.org/TR/REC-xml/#NT-CData
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CdataStr(str);

impl CdataStr {
    /// Creates a new `&CdataStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::cdata_section::{CdataError, CdataStr};
    /// assert!(CdataStr::new_checked("ValidCData").is_ok());
    /// assert!(CdataStr::new_checked("").is_ok());
    ///
    /// assert_eq!(CdataStr::new_checked("]]>"), Err(CdataError::CdataSectionClosed(0)));
    /// assert_eq!(
    ///     CdataStr::new_checked("foo]]>bar"),
    ///     Err(CdataError::CdataSectionClosed(3))
    /// );
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, CdataError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&CdataStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`CData`] string.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::cdata_section::CdataStr;
    /// let s = CdataStr::new("ValidCData");
    /// ```
    ///
    /// [`CData`]: http://www.w3.org/TR/REC-xml/#NT-CData
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `CData` string: {}", e))
    }

    /// Creates a new `&CdataStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`CData`] string.
    ///
    /// [`CData`]: http://www.w3.org/TR/REC-xml/#NT-CData
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for [`CData`].
///
/// [`CData`]: http://www.w3.org/TR/REC-xml/#NT-CData
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CdataString(Box<CdataStr>);

impl_string_types! {
    owned: CdataString,
    slice: CdataStr,
    error_slice: CdataError,
    parse: parse,
    slice_new_unchecked: CdataStr::new_unchecked,
}

impl_string_cmp! {
    owned: CdataString,
    slice: CdataStr,
}

impl_string_cmp_to_string! {
    owned: CdataString,
    slice: CdataStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{CdataSectionClosed, Complete, InvalidCharacter};

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw(""), Complete(()));
        assert_eq!(parse_raw("valid CData"), Complete(()));
        assert_eq!(parse_raw("foo<bar>baz&qux"), Complete(()));

        assert_eq!(parse_raw("]]>"), CdataSectionClosed(Partial::new((), 0)));
        assert_eq!(
            parse_raw("foo]]>bar"),
            CdataSectionClosed(Partial::new((), 3))
        );
        // Vertical tab is not allowed in CDATA section.
        assert_eq!(
            parse_raw("vertical\u{B}tab"),
            InvalidCharacter(Partial::new((), 8))
        );
    }
}
