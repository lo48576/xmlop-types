//! CDATA section.
//!
//! See [`CDSect`] in the XML spec.
//!
//! [`CDSect`]: https://www.w3.org/TR/xml/#NT-CDSect

use std::{convert::TryFrom, error, fmt};

use crate::{
    cdata_section::content::{parse_raw as parse_content, ParseResult as CdataResult},
    parser::{Partial, PartialMapWithStr},
};

/// Parse result of CDATA section.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Extra data follows.
    Extra(Partial<T>),
    /// Invalid character.
    InvalidCharacter(usize),
    /// CDATA section is not closed.
    MissingCloseDelimiter,
    /// CDATA section is not opened.
    MissingOpenDelimiter,
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, CdataSectionError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::Extra(part) => Err(CdataSectionError::ExtraData(part.valid_up_to())),
            Self::InvalidCharacter(pos) => Err(CdataSectionError::InvalidCharacter(pos)),
            Self::MissingCloseDelimiter => Err(CdataSectionError::MissingCloseDelimiter),
            Self::MissingOpenDelimiter => Err(CdataSectionError::MissingOpenDelimiter),
        }
    }
}

/// Parses the given string as `CDSect`.
///
/// This parses a CDATA section including `"<![CDATA["` and `"]]>"`.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    /// Length of `"<![CDATA["`.
    const CDATA_OPEN_LEN: usize = 9;
    /// Length of `"]]>"`.
    const CDATA_CLOSE_LEN: usize = 3;

    if !s.starts_with("<![CDATA[") {
        return ParseResult::MissingOpenDelimiter;
    }
    match parse_content(&s[CDATA_OPEN_LEN..]) {
        CdataResult::Complete(()) => ParseResult::MissingCloseDelimiter,
        CdataResult::CdataSectionClosed(part) if part.valid_up_to() == s.len() => {
            ParseResult::Complete(())
        }
        CdataResult::CdataSectionClosed(part) => {
            assert!(s[(CDATA_OPEN_LEN + part.valid_up_to())..].starts_with("]]>"));
            let section_len = CDATA_OPEN_LEN + part.valid_up_to() + CDATA_CLOSE_LEN;
            if s.len() == section_len {
                return ParseResult::Complete(());
            }
            ParseResult::Extra(Partial::new((), section_len))
        }
        CdataResult::InvalidCharacter(part) => {
            ParseResult::InvalidCharacter(CDATA_OPEN_LEN + part.valid_up_to())
        }
    }
}

/// Parses the given string as `CDSect`.
fn parse(s: &str) -> ParseResult<&CdataSectionStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => {
            ParseResult::Complete(unsafe { CdataSectionStr::new_unchecked(s) })
        }
        ParseResult::Extra(part) => ParseResult::Extra(
            part.map_with_str(s, |_, s| unsafe { CdataSectionStr::new_unchecked(s) }),
        ),
        ParseResult::InvalidCharacter(pos) => ParseResult::InvalidCharacter(pos),
        ParseResult::MissingCloseDelimiter => ParseResult::MissingCloseDelimiter,
        ParseResult::MissingOpenDelimiter => ParseResult::MissingOpenDelimiter,
    }
}

/// Error for CDATA section.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CdataSectionError {
    /// Extra data follows.
    ///
    /// `usize` field is the first byte position of the extra data after `]]>`.
    ExtraData(usize),
    /// Invalid character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
    /// CDATA section is not closed.
    MissingCloseDelimiter,
    /// Starting marker of CDATA section is not at the beginning of the string.
    MissingOpenDelimiter,
}

impl error::Error for CdataSectionError {}

impl fmt::Display for CdataSectionError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CdataSectionError::ExtraData(pos) => write!(f, "Extra following data at index {}", pos),
            CdataSectionError::InvalidCharacter(pos) => {
                write!(f, "Invalid character at index {}", pos)
            }
            CdataSectionError::MissingCloseDelimiter => {
                write!(f, "CDATA section close delimiter is missing")
            }
            CdataSectionError::MissingOpenDelimiter => write!(
                f,
                "CDATA section open delimiter is missing at the beginning of the string"
            ),
        }
    }
}

/// String slice for [`CDSect`].
///
/// [`CData`]: http://www.w3.org/TR/REC-xml/#NT-CDSect
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CdataSectionStr(str);

impl CdataSectionStr {
    /// Creates a new `&CdataSectionStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::cdata_section::{CdataSectionError, CdataSectionStr};
    /// assert!(CdataSectionStr::new_checked("<![CDATA[Valid CDATA section]]>").is_ok());
    /// assert!(CdataSectionStr::new_checked("<![CDATA[]]>").is_ok());
    /// assert!(CdataSectionStr::new_checked("<![CDATA[foo<bar>baz&qux]]>").is_ok());
    ///
    /// assert_eq!(
    ///     CdataSectionStr::new_checked("<![CDATA[foo]]>bar"),
    ///     Err(CdataSectionError::ExtraData(15))
    /// );
    /// // First `]]>` closes the whole CDATA section (started by the first `<![CDATA[`).
    /// assert_eq!(
    ///     CdataSectionStr::new_checked("<![CDATA[<![CDATA[]]>]]>"),
    ///     Err(CdataSectionError::ExtraData(21))
    /// );
    /// assert_eq!(
    ///     CdataSectionStr::new_checked("<![CDATA[\u{B}]]>"),
    ///     Err(CdataSectionError::InvalidCharacter(9))
    /// );
    /// assert_eq!(
    ///     CdataSectionStr::new_checked("<![CDATA["),
    ///     Err(CdataSectionError::MissingCloseDelimiter)
    /// );
    /// assert_eq!(CdataSectionStr::new_checked(""), Err(CdataSectionError::MissingOpenDelimiter));
    /// assert_eq!(CdataSectionStr::new_checked("foo"), Err(CdataSectionError::MissingOpenDelimiter));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, CdataSectionError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&CdataSectionStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`CDSect`] string.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::cdata_section::CdataSectionStr;
    /// let s = CdataSectionStr::new("<![CDATA[valid CDATA section]]>");
    /// ```
    ///
    /// [`CDSect`]: http://www.w3.org/TR/REC-xml/#NT-CDSect
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid CDATA section: {}", e))
    }

    /// Creates a new `&CdataSectionStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`CDSect`] string.
    ///
    /// [`CDSect`]: http://www.w3.org/TR/REC-xml/#NT-CDSect
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for [`CDSect`].
///
/// [`CDSect`]: http://www.w3.org/TR/REC-xml/#NT-CDSect
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CdataSectionString(Box<CdataSectionStr>);

impl_string_types! {
    owned: CdataSectionString,
    slice: CdataSectionStr,
    error_slice: CdataSectionError,
    parse: parse,
    slice_new_unchecked: CdataSectionStr::new_unchecked,
}

impl_string_cmp! {
    owned: CdataSectionString,
    slice: CdataSectionStr,
}

impl_string_cmp_to_string! {
    owned: CdataSectionString,
    slice: CdataSectionStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{
        Complete, Extra, InvalidCharacter, MissingCloseDelimiter, MissingOpenDelimiter,
    };

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw("<![CDATA[]]>"), Complete(()));
        assert_eq!(parse_raw("<![CDATA[valid CDATA section]]>"), Complete(()));
        assert_eq!(parse_raw("<![CDATA[foo<bar>baz&qux]]>"), Complete(()));

        assert_eq!(parse_raw("<![CDATA[]]>foo"), Extra(Partial::new((), 12)));
        assert_eq!(
            parse_raw("<![CDATA[<![CDATA[]]>]]>"),
            Extra(Partial::new((), 21))
        );
        assert_eq!(
            parse_raw("<![CDATA[Valid CDATA Section]]>foo"),
            Extra(Partial::new((), 31))
        );
        assert_eq!(
            parse_raw("<![CDATA[foo<bar>baz&qux]]>foo"),
            Extra(Partial::new((), 27))
        );

        assert_eq!(parse_raw("<![CDATA["), MissingCloseDelimiter);
        assert_eq!(parse_raw("<![CDATA[foo"), MissingCloseDelimiter);

        assert_eq!(parse_raw("foo"), MissingOpenDelimiter);
        assert_eq!(parse_raw("<elem>"), MissingOpenDelimiter);
        assert_eq!(parse_raw("<![CDATA"), MissingOpenDelimiter);

        // Vertical tab is not allowed in CDATA section.
        assert_eq!(
            parse_raw("<![CDATA[vertical\u{B}tab]]>"),
            InvalidCharacter(17)
        );
    }
}
