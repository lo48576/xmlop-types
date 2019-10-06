//! [`AttValue`] inside apostrophies (`'`).
//!
//! About `AttValue`, see [Extensible Markup Language (XML) 1.0 (Fifth Edition)][`AttValue`].
//!
//! [`AttValue`]: http://www.w3.org/TR/REC-xml/#NT-AttValue

use std::convert::TryFrom;

use crate::{
    attribute::{
        value::content::{parse_raw as parse_content, ParseResult},
        AttributeContentError, QuoteMark,
    },
    parser::PartialMapWithStr,
};

/// Parses the given string as content of `AttValue` with apostrophy quotes.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    parse_content(s, QuoteMark::Apos)
}

/// Parses the given string as content of `AttValue` with apostrophy quotes.
fn parse(s: &str) -> ParseResult<&AposAttributeContentStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => {
            ParseResult::Complete(unsafe { AposAttributeContentStr::new_unchecked(s) })
        }
        ParseResult::InvalidCharacter(part) => {
            ParseResult::InvalidCharacter(part.map_with_str(s, |_, s| unsafe {
                AposAttributeContentStr::new_unchecked(s)
            }))
        }
        ParseResult::InvalidReference(part, e) => ParseResult::InvalidReference(
            part.map_with_str(s, |_, s| unsafe {
                AposAttributeContentStr::new_unchecked(s)
            }),
            e,
        ),
        ParseResult::UnexpectedQuote(part) => {
            ParseResult::UnexpectedQuote(part.map_with_str(s, |_, s| unsafe {
                AposAttributeContentStr::new_unchecked(s)
            }))
        }
    }
}

/// String slice for content of an attribute with apostrophy quotes (`'`).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct AposAttributeContentStr(str);

impl AposAttributeContentStr {
    /// Creates a new `&AposAttributeContentStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::attribute::{AposAttributeContentStr, AttributeContentError};
    /// assert!(AposAttributeContentStr::new_checked("Valid apos attribute value").is_ok());
    /// assert!(AposAttributeContentStr::new_checked("").is_ok());
    /// assert!(AposAttributeContentStr::new_checked("\"").is_ok());
    /// assert!(AposAttributeContentStr::new_checked("&apos;&quot;&amp;&#x3C;").is_ok());
    ///
    /// assert_eq!(
    ///     AposAttributeContentStr::new_checked("foo<bar"),
    ///     Err(AttributeContentError::InvalidCharacter(3))
    /// );
    /// assert_eq!(
    ///     AposAttributeContentStr::new_checked("foo&bar"),
    ///     Err(AttributeContentError::InvalidReference(
    ///         3,
    ///         xmlop_types::reference::ReferenceError::MissingSemicolon
    ///     ))
    /// );
    /// assert_eq!(
    ///     AposAttributeContentStr::new_checked("foo'bar"),
    ///     Err(AttributeContentError::UnexpectedQuote(3))
    /// );
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, AttributeContentError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&AposAttributeContentStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid content of an attribute with apostrophy quotes.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::attribute::AposAttributeContentStr;
    /// let s = AposAttributeContentStr::new("attribute content with &apos;");
    /// ```
    ///
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s).unwrap_or_else(|e| {
            panic!(
                "The given string is not valid content of attribute with apostrophy quotes: {}",
                e
            )
        })
    }

    /// Creates a new `&AposAttributeContentStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid content of an attribute with apostrophy quotes.
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for content of an attribute with apostrophy quotes (`'`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct AposAttributeContentString(Box<AposAttributeContentStr>);

impl_string_types! {
    owned: AposAttributeContentString,
    slice: AposAttributeContentStr,
    error_slice: AttributeContentError,
    parse: parse,
    slice_new_unchecked: AposAttributeContentStr::new_unchecked,
}

impl_string_cmp! {
    owned: AposAttributeContentString,
    slice: AposAttributeContentStr,
}

impl_string_cmp_to_string! {
    owned: AposAttributeContentString,
    slice: AposAttributeContentStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use crate::{parser::Partial, reference::ReferenceError};
    use ParseResult::{Complete, InvalidCharacter, InvalidReference, UnexpectedQuote};

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw("valid attribute"), Complete(()));
        assert_eq!(parse_raw(""), Complete(()));
        assert_eq!(parse_raw("\""), Complete(()));
        assert_eq!(parse_raw("&apos;&quot;&amp;&#x3C;"), Complete(()));

        assert_eq!(parse_raw("foo<bar"), InvalidCharacter(Partial::new((), 3)));
        assert_eq!(
            parse_raw("foo\u{B}bar"),
            InvalidCharacter(Partial::new((), 3))
        );
        assert_eq!(
            parse_raw("foo&bar"),
            InvalidReference(Partial::new((), 3), ReferenceError::MissingSemicolon)
        );
        assert_eq!(parse_raw("foo'bar"), UnexpectedQuote(Partial::new((), 3)));
    }
}
