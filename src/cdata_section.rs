//! CDATA section.
//!
//! See [`CDSect`] in the XML spec.
//!
//! [`CDSect`]: https://www.w3.org/TR/xml/#NT-CDSect

use std::{error, fmt};

use crate::{
    cdata::{self, ParseResult as CdataResult},
    parser::Partial,
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

/// Parses the given string as `CharData`.
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
    match cdata::parse_raw(&s[CDATA_OPEN_LEN..]) {
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
