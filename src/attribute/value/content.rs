//! Attribute value without wrapping quotes.

use std::{error, fmt};

use crate::{
    attribute::QuoteMark,
    parser::{chars::is_xml_char, Partial},
    reference::{parse_raw as parse_reference, ParseResult as ReferenceResult, ReferenceError},
};

pub(crate) mod apos;
pub(crate) mod quot;

/// Parse result of content of `AttValue`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Invalid Character.
    InvalidCharacter(Partial<T>),
    /// Invalid reference.
    InvalidReference(Partial<T>, ReferenceError),
    /// Unexpected quote character (apostrophy `'` or quotation mark `"`).
    UnexpectedQuote(Partial<T>),
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, AttributeContentError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::InvalidCharacter(part) => {
                Err(AttributeContentError::InvalidCharacter(part.valid_up_to()))
            }
            Self::InvalidReference(part, e) => Err(AttributeContentError::InvalidReference(
                part.valid_up_to(),
                e,
            )),
            Self::UnexpectedQuote(part) => {
                Err(AttributeContentError::UnexpectedQuote(part.valid_up_to()))
            }
        }
    }
}

/// Parses the given string as content of `AttValue`.
pub(crate) fn parse_raw(s: &str, quote: QuoteMark) -> ParseResult<()> {
    let mut rest = s;

    while let Some((rest_pos, c)) = rest
        .char_indices()
        .find(|&(_, c)| c == '<' || c == '&' || quote.is_quote(c) || !is_xml_char(c))
    {
        let pos = s.len() - rest.len() + rest_pos;
        match c {
            '&' => match parse_reference(&rest[rest_pos..]) {
                ReferenceResult::Complete(_) => return ParseResult::Complete(()),
                ReferenceResult::Extra(part) => {
                    rest = &rest[part.valid_up_to()..];
                    continue;
                }
                ReferenceResult::InvalidCharacterReference => {
                    return ParseResult::InvalidReference(
                        Partial::new((), pos),
                        ReferenceError::InvalidCharacterReference,
                    )
                }
                ReferenceResult::MissingAmpersand => {
                    return ParseResult::InvalidReference(
                        Partial::new((), pos),
                        ReferenceError::MissingAmpersand,
                    )
                }
                ReferenceResult::MissingCharacterCode => {
                    return ParseResult::InvalidReference(
                        Partial::new((), pos),
                        ReferenceError::MissingCharacterCode,
                    )
                }
                ReferenceResult::MissingName => {
                    return ParseResult::InvalidReference(
                        Partial::new((), pos),
                        ReferenceError::MissingName,
                    )
                }
                ReferenceResult::MissingSemicolon => {
                    return ParseResult::InvalidReference(
                        Partial::new((), pos),
                        ReferenceError::MissingSemicolon,
                    )
                }
            },
            '"' | '\'' => {
                assert!(quote.is_quote(c));
                return ParseResult::UnexpectedQuote(Partial::new((), pos));
            }
            _ => {
                debug_assert!(c == '<' || !is_xml_char(c));
                return ParseResult::InvalidCharacter(Partial::new((), pos));
            }
        }
    }

    ParseResult::Complete(())
}

/*
/// Parses the given string as a content of `AttValue`.
fn parse(s: &str) -> ParseResult<&CharDataStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => {
            ParseResult::Complete(unsafe { CharDataStr::new_unchecked(s) })
        }
        ParseResult::CdataSectionClosed(part) => ParseResult::CdataSectionClosed(
            part.map_with_str(s, |_, s| unsafe { CharDataStr::new_unchecked(s) }),
        ),
        ParseResult::InvalidCharacter(part) => ParseResult::InvalidCharacter(
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
*/

/// Error for content of `AttValue`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum AttributeContentError {
    /// Found invalid character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
    /// Found invalid reference.
    ///
    /// `usize` field is the first byte position of the invalid reference.
    InvalidReference(usize, ReferenceError),
    /// Unexpected quote.
    ///
    /// `usize` field is the first byte position of the unexpected quote.
    UnexpectedQuote(usize),
}

impl error::Error for AttributeContentError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::InvalidReference(_, e) => Some(e),
            _ => None,
        }
    }
}

impl fmt::Display for AttributeContentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::InvalidCharacter(pos) => write!(f, "Invalid character at index {}", pos),
            Self::InvalidReference(pos, e) => {
                write!(f, "Invalid reference at index {}: {}", pos, e)
            }
            Self::UnexpectedQuote(pos) => write!(f, "Unexpceted quote at index {}", pos),
        }
    }
}

/*
/// String slice for [`AttributeValueContent`].
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

    use ParseResult::{
        CdataSectionClosed, Complete, InvalidCharacter, UnexpectedAmpersand, UnexpectedLt,
    };

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
        assert_eq!(
            parse_raw("foo\u{B}bar"),
            InvalidCharacter(Partial::new((), 3))
        );
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
*/
