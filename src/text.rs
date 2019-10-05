//! String types for content of XML text nodes, including CDATA section and references.
//!
//! `TextStr` and `TextString` contains unprocessed valid `#PCDATA`, which consists of zero or more
//! entity references, character references, character data (`CData`s), and CDATA sections.
//!
//! The text type is subset of [`content`] in the XML spec.
//!
//! [`content`]: https://www.w3.org/TR/xml/#NT-content

use std::{convert::TryFrom, error, fmt};

use crate::{
    cdata_section::{self, ParseResult as CdataSectionResult},
    char_data::{self, ParseResult as CharDataResult},
    parser::{Partial, PartialMapWithStr},
    reference::{self, ParseResult as ReferenceResult},
};

/// Parse result of `Text`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// CDATA section closed unexpectedly (while not opened).
    CdataSectionClosed(Partial<T>),
    /// Invalid use of ampersand (`&`).
    ///
    /// This error can be caused by unclosed reference (entity reference and character reference)
    /// or invalid (non-`Name`) string following `&`.
    InvalidAmpersand(Partial<T>),
    /// Invalid character.
    InvalidCharacter(Partial<T>),
    /// Unclosed CDATA section.
    ///
    /// The first `usize` field is the byte position of the starting `<`.
    UnclosedCdataSection(Partial<T>),
    /// Unescaped lt (`<`).
    ///
    /// The first `usize` field is the byte position of the unescaped `<`.
    UnescapedLt(Partial<T>),
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, TextError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::CdataSectionClosed(part) => {
                Err(TextError::CdataSectionClosed(part.valid_up_to()))
            }
            Self::InvalidAmpersand(part) => Err(TextError::InvalidAmpersand(part.valid_up_to())),
            Self::InvalidCharacter(part) => Err(TextError::InvalidCharacter(part.valid_up_to())),
            Self::UnclosedCdataSection(part) => {
                Err(TextError::UnclosedCdataSection(part.valid_up_to()))
            }
            Self::UnescapedLt(part) => Err(TextError::UnescapedLt(part.valid_up_to())),
        }
    }
}

/// Parses the given string as text node.
fn parse_raw(s: &str) -> ParseResult<()> {
    if s.is_empty() {
        return ParseResult::Complete(());
    }
    let mut rest = s;
    loop {
        assert!(!rest.is_empty());
        let first = match rest.as_bytes().get(0) {
            Some(c) => *c,
            None => return ParseResult::Complete(()),
        };
        match first {
            b'&' => match reference::parse_raw(rest) {
                ReferenceResult::Complete(_) => return ParseResult::Complete(()),
                ReferenceResult::Extra(part) => rest = &rest[part.valid_up_to()..],
                _ => return ParseResult::InvalidAmpersand(Partial::new((), s.len() - rest.len())),
            },
            b'<' => match cdata_section::parse_raw(rest) {
                CdataSectionResult::Complete(_) => return ParseResult::Complete(()),
                CdataSectionResult::Extra(part) => rest = &rest[part.valid_up_to()..],
                CdataSectionResult::InvalidCharacter(pos) => {
                    return ParseResult::InvalidCharacter(Partial::new(
                        (),
                        s.len() - rest.len() + pos,
                    ))
                }
                CdataSectionResult::MissingCloseDelimiter => {
                    return ParseResult::UnclosedCdataSection(Partial::new(
                        (),
                        s.len() - rest.len(),
                    ))
                }
                CdataSectionResult::MissingOpenDelimiter => {
                    return ParseResult::UnescapedLt(Partial::new((), s.len() - rest.len()))
                }
            },
            _ => match char_data::parse_raw(rest) {
                CharDataResult::Complete(_) => return ParseResult::Complete(()),
                CharDataResult::CdataSectionClosed(part) => {
                    return ParseResult::CdataSectionClosed(Partial::new(
                        (),
                        s.len() - rest.len() + part.valid_up_to(),
                    ))
                }
                CharDataResult::InvalidCharacter(part) => {
                    return ParseResult::InvalidCharacter(Partial::new(
                        (),
                        s.len() - rest.len() + part.valid_up_to(),
                    ))
                }
                CharDataResult::UnexpectedAmpersand(part) | CharDataResult::UnexpectedLt(part) => {
                    rest = &rest[part.valid_up_to()..]
                }
            },
        }
    }
}

/// Parses the given string as XML text.
fn parse(s: &str) -> ParseResult<&TextStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => ParseResult::Complete(unsafe { TextStr::new_unchecked(s) }),
        ParseResult::CdataSectionClosed(part) => ParseResult::CdataSectionClosed(
            part.map_with_str(s, |_, s| unsafe { TextStr::new_unchecked(s) }),
        ),
        ParseResult::InvalidAmpersand(part) => ParseResult::InvalidAmpersand(
            part.map_with_str(s, |_, s| unsafe { TextStr::new_unchecked(s) }),
        ),
        ParseResult::InvalidCharacter(part) => ParseResult::InvalidCharacter(
            part.map_with_str(s, |_, s| unsafe { TextStr::new_unchecked(s) }),
        ),
        ParseResult::UnclosedCdataSection(part) => ParseResult::UnclosedCdataSection(
            part.map_with_str(s, |_, s| unsafe { TextStr::new_unchecked(s) }),
        ),
        ParseResult::UnescapedLt(part) => ParseResult::UnescapedLt(
            part.map_with_str(s, |_, s| unsafe { TextStr::new_unchecked(s) }),
        ),
    }
}

/// Error for text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TextError {
    /// CDATA section closed unexpectedly (while not opened).
    ///
    /// The first `usize` field is the first byte position of the CDATA section end delimiter
    /// `"]]>"`.
    CdataSectionClosed(usize),
    /// Invalid use of ampersand (`&`).
    ///
    /// This error can be caused by unclosed reference (entity reference and character reference)
    /// or invalid (non-`Name`) string following `&`.
    ///
    /// The first `usize` field is the byte position of the starting `&`.
    InvalidAmpersand(usize),
    /// Invalid character.
    ///
    /// The first `usize` field is the byte position of the invalid character.
    InvalidCharacter(usize),
    /// Unclosed CDATA section.
    ///
    /// The first `usize` field is the byte position of the starting `<`.
    UnclosedCdataSection(usize),
    /// Unescaped lt (`<`).
    ///
    /// The first `usize` field is the byte position of the unescaped `<`.
    UnescapedLt(usize),
}

impl error::Error for TextError {}

impl fmt::Display for TextError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TextError::CdataSectionClosed(pos) => {
                write!(f, "Unexpected CDATA section end delimiter at index {}", pos)
            }
            TextError::InvalidAmpersand(pos) => write!(f, "Invalid ampersand use at index {}", pos),
            TextError::InvalidCharacter(pos) => write!(f, "Invalid character at index {}", pos),
            TextError::UnclosedCdataSection(pos) => {
                write!(f, "Unclosed CDATA section at index {}", pos)
            }
            TextError::UnescapedLt(pos) => write!(f, "Unescaped `<` at index {}", pos),
        }
    }
}

/// String slice for text.
///
/// See module documentation for detail.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct TextStr(str);

impl TextStr {
    /// Creates a new `&TextStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::text::{TextError, TextStr};
    /// assert!(TextStr::new_checked("Valid text").is_ok());
    /// assert!(TextStr::new_checked("").is_ok());
    /// assert!(TextStr::new_checked("&lt;").is_ok());
    /// assert!(TextStr::new_checked("&#60;").is_ok());
    /// assert!(TextStr::new_checked("&#x3c;").is_ok());
    /// assert!(TextStr::new_checked("&#x3C;").is_ok());
    /// assert!(TextStr::new_checked("<![CDATA[foo]]>").is_ok());
    /// assert!(TextStr::new_checked("&lt;<![CDATA[&]]>&#x3c;").is_ok());
    ///
    /// assert_eq!(TextStr::new_checked("<"), Err(TextError::UnescapedLt(0)));
    /// assert_eq!(TextStr::new_checked("&"), Err(TextError::InvalidAmpersand(0)));
    /// assert_eq!(TextStr::new_checked("foo&bar"), Err(TextError::InvalidAmpersand(3)));
    /// assert_eq!(TextStr::new_checked("&foo bar;"), Err(TextError::InvalidAmpersand(0)));
    /// assert_eq!(TextStr::new_checked("&#3C;"), Err(TextError::InvalidAmpersand(0)));
    /// assert_eq!(TextStr::new_checked("&#xZ;"), Err(TextError::InvalidAmpersand(0)));
    /// assert_eq!(
    ///     TextStr::new_checked("<![CDATA[<![CDATA[]]>]]>"),
    ///     Err(TextError::CdataSectionClosed(21))
    /// );
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, TextError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&TextStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid text content.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::text::TextStr;
    /// let s = TextStr::new("Valid text");
    /// ```
    ///
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid text content: {}", e))
    }

    /// Creates a new `&TextStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid text content.
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for text.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TextString(Box<TextStr>);

impl_string_types! {
    owned: TextString,
    slice: TextStr,
    error_slice: TextError,
    parse: parse,
    slice_new_unchecked: TextStr::new_unchecked,
}

impl_string_cmp! {
    owned: TextString,
    slice: TextStr,
}

impl_string_cmp_to_string! {
    owned: TextString,
    slice: TextStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{
        CdataSectionClosed, Complete, InvalidAmpersand, InvalidCharacter, UnclosedCdataSection,
        UnescapedLt,
    };

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw(""), Complete(()));
        assert_eq!(parse_raw("Valid text"), Complete(()));
        assert_eq!(parse_raw("foo&amp;bar"), Complete(()));
        assert_eq!(parse_raw("&lt;&#60;&#x3c;&#x3C;"), Complete(()));
        assert_eq!(parse_raw("foo<![CDATA[bar]]>baz"), Complete(()));
        assert_eq!(parse_raw("foo<![CDATA[ ><& ]]>baz"), Complete(()));
        assert_eq!(parse_raw("foo<![CDATA[bar]]>&baz;qux"), Complete(()));
        // Existence of stray `>` is syntactically allowed by the spec (see [`CharData`]), but it is
        // strongly discouraged.
        //
        // > The right angle bracket (`>`) may be represented using the string "`&gt;`", and MUST,
        // > for compatibility, be escaped using either "`&gt;`" or a character reference when it
        // > appears in > the string "`]]>`" in content, when that string is not marking the end of
        // > a CDATA section.
        // >
        // > --- <https://www.w3.org/TR/2008/REC-xml-20081126/#syntax>
        assert_eq!(parse_raw("]>"), Complete(()));
        assert_eq!(parse_raw("foo>bar"), Complete(()));
        assert_eq!(parse_raw("fo]]]o>bar"), Complete(()));
        assert_eq!(parse_raw(">"), Complete(()));

        assert_eq!(parse_raw("]]>"), CdataSectionClosed(Partial::new((), 0)),);
        assert_eq!(parse_raw("]]]>"), CdataSectionClosed(Partial::new((), 1)),);
        assert_eq!(parse_raw("&"), InvalidAmpersand(Partial::new((), 0)),);
        assert_eq!(parse_raw("]]]&"), InvalidAmpersand(Partial::new((), 3)),);
        assert_eq!(parse_raw("foo&bar"), InvalidAmpersand(Partial::new((), 3)),);
        assert_eq!(
            parse_raw("foo]]]&bar"),
            InvalidAmpersand(Partial::new((), 6)),
        );
        // Vertical tab is not allowed.
        assert_eq!(
            parse_raw("foo\u{B}bar"),
            InvalidCharacter(Partial::new((), 3))
        );
        assert_eq!(
            parse_raw("<![CDATA[vertical\u{B}tab]]>bar"),
            InvalidCharacter(Partial::new((), 17))
        );
        assert_eq!(
            parse_raw("foo<![CDATA[bar"),
            UnclosedCdataSection(Partial::new((), 3)),
        );
        assert_eq!(
            parse_raw("foo]]]<![CDATA[bar"),
            UnclosedCdataSection(Partial::new((), 6))
        );
        assert_eq!(parse_raw("<elem>"), UnescapedLt(Partial::new((), 0)),);
        assert_eq!(parse_raw("]]]<elem>"), UnescapedLt(Partial::new((), 3)),);
    }
}
