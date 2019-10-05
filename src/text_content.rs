//! String types for (unescaped) XML text data.
//!
//! Note that these types do not represent raw XML text nodes, but they represent "strings which can
//! be represented by XML".
//!
//! For example, `foo&]]><` can be representable by XML as `foo&amp;]]&gt;&lt;` (while the string
//! itself is invalid as XML text node), so `foo&]]><` is valid as `&TextContentStr`.
//!
//! ```
//! # use xmlop_types::text_content::TextContentStr;
//! // `foo&]]><` is invalid as XML text node, but representable in a valid XML document.
//! assert!(TextContentStr::new_checked("foo&]]><").is_ok());
//! ```
//!
//! Note that text content strings might be unable to use directly.
//! They should be escaped when they are written to XML documents.

use std::{convert::TryFrom, error, fmt};

use crate::parser::{chars::is_xml_char, Partial, PartialMapWithStr};

/// Parse result of `Text`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Invalid character.
    InvalidCharacter(Partial<T>),
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, TextContentError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::InvalidCharacter(part) => {
                Err(TextContentError::InvalidCharacter(part.valid_up_to()))
            }
        }
    }
}

/// Parses the given string as text content.
fn parse_raw(s: &str) -> ParseResult<()> {
    if let Some((pos, _)) = s.char_indices().find(|&(_, c)| !is_xml_char(c)) {
        return ParseResult::InvalidCharacter(Partial::new((), pos));
    }

    ParseResult::Complete(())
}

/// Parses the given string as XML text.
fn parse(s: &str) -> ParseResult<&TextContentStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => {
            ParseResult::Complete(unsafe { TextContentStr::new_unchecked(s) })
        }
        ParseResult::InvalidCharacter(part) => ParseResult::InvalidCharacter(
            part.map_with_str(s, |_, s| unsafe { TextContentStr::new_unchecked(s) }),
        ),
    }
}

/// Error for text content.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TextContentError {
    /// Invalid character.
    ///
    /// The first `usize` field is the byte position of the invalid character.
    InvalidCharacter(usize),
}

impl error::Error for TextContentError {}

impl fmt::Display for TextContentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TextContentError::InvalidCharacter(pos) => {
                write!(f, "Invalid character at index {}", pos)
            }
        }
    }
}

/// String slice for text content.
///
/// See module documentation for detail.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct TextContentStr(str);

impl TextContentStr {
    /// Creates a new `&TextContentStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::text_content::{TextContentError, TextContentStr};
    /// assert!(TextContentStr::new_checked("Valid text content").is_ok());
    /// assert!(TextContentStr::new_checked("").is_ok());
    /// assert!(TextContentStr::new_checked("<this-is-not-an-element-but-plain-text>").is_ok());
    /// assert!(TextContentStr::new_checked("&").is_ok());
    /// assert!(TextContentStr::new_checked("&this-is-not-a-reference-but-plain-text;").is_ok());
    /// assert!(TextContentStr::new_checked("&###;").is_ok());
    /// assert!(TextContentStr::new_checked("]]>").is_ok());
    /// assert!(TextContentStr::new_checked("(>_<;)").is_ok());
    ///
    /// // These characters are not allowed in XML document, even if they are escaped.
    /// assert_eq!(TextContentStr::new_checked("\u{0}"), Err(TextContentError::InvalidCharacter(0)));
    /// assert_eq!(
    ///     TextContentStr::new_checked("foo\u{B}bar"),
    ///     Err(TextContentError::InvalidCharacter(3))
    /// );
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, TextContentError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&TextContentStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid text content.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::text_content::TextContentStr;
    /// let s = TextContentStr::new("Valid text");
    /// ```
    ///
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid text content: {}", e))
    }

    /// Creates a new `&TextContentStr` without validation.
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

/// Owned string for text content.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct TextContentString(Box<TextContentStr>);

impl_string_types! {
    owned: TextContentString,
    slice: TextContentStr,
    error_slice: TextContentError,
    parse: parse,
    slice_new_unchecked: TextContentStr::new_unchecked,
}

impl_string_cmp! {
    owned: TextContentString,
    slice: TextContentStr,
}

impl_string_cmp_to_string! {
    owned: TextContentString,
    slice: TextContentStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{Complete, InvalidCharacter};

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw(""), Complete(()));
        assert_eq!(parse_raw("Valid text content"), Complete(()));
        assert_eq!(parse_raw(""), Complete(()));
        assert_eq!(
            parse_raw("<this-is-not-an-element-but-plain-text>"),
            Complete(())
        );
        assert_eq!(parse_raw("&"), Complete(()));
        assert_eq!(
            parse_raw("&this-is-not-a-reference-but-plain-text;"),
            Complete(())
        );
        assert_eq!(parse_raw("&###;"), Complete(()));
        assert_eq!(parse_raw("]]>"), Complete(()));
        assert_eq!(parse_raw("(>_<;)"), Complete(()));

        assert_eq!(parse_raw("\u{0}"), InvalidCharacter(Partial::new((), 0)));
        assert_eq!(
            parse_raw("foo\u{B}bar"),
            InvalidCharacter(Partial::new((), 3))
        );
    }
}
