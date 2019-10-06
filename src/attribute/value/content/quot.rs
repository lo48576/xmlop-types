//! [`AttValue`] inside quotation marks (`"`).
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

/// Parses the given string as content of `AttValue` with quotation marks.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    parse_content(s, QuoteMark::Quot)
}

/// Parses the given string as content of `AttValue` with quotation marks.
fn parse(s: &str) -> ParseResult<&QuotAttributeContentStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => {
            ParseResult::Complete(unsafe { QuotAttributeContentStr::new_unchecked(s) })
        }
        ParseResult::InvalidCharacter(part) => {
            ParseResult::InvalidCharacter(part.map_with_str(s, |_, s| unsafe {
                QuotAttributeContentStr::new_unchecked(s)
            }))
        }
        ParseResult::InvalidReference(part, e) => ParseResult::InvalidReference(
            part.map_with_str(s, |_, s| unsafe {
                QuotAttributeContentStr::new_unchecked(s)
            }),
            e,
        ),
        ParseResult::UnexpectedQuote(part) => {
            ParseResult::UnexpectedQuote(part.map_with_str(s, |_, s| unsafe {
                QuotAttributeContentStr::new_unchecked(s)
            }))
        }
    }
}

/// String slice for content of an attribute with quotation marks (`"`).
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct QuotAttributeContentStr(str);

impl QuotAttributeContentStr {
    /// Creates a new `&QuotAttributeContentStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::attribute::{QuotAttributeContentStr, AttributeContentError};
    /// assert!(QuotAttributeContentStr::new_checked("Valid quot attribute value").is_ok());
    /// assert!(QuotAttributeContentStr::new_checked("").is_ok());
    /// assert!(QuotAttributeContentStr::new_checked("'").is_ok());
    /// assert!(QuotAttributeContentStr::new_checked("&apos;&quot;&amp;&#x3C;").is_ok());
    ///
    /// assert_eq!(
    ///     QuotAttributeContentStr::new_checked("foo<bar"),
    ///     Err(AttributeContentError::InvalidCharacter(3))
    /// );
    /// assert_eq!(
    ///     QuotAttributeContentStr::new_checked("foo&bar"),
    ///     Err(AttributeContentError::InvalidReference(
    ///         3,
    ///         xmlop_types::reference::ReferenceError::MissingSemicolon
    ///     ))
    /// );
    /// assert_eq!(
    ///     QuotAttributeContentStr::new_checked("foo\"bar"),
    ///     Err(AttributeContentError::UnexpectedQuote(3))
    /// );
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, AttributeContentError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&QuotAttributeContentStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid content of an attribute with quotation marks.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::attribute::QuotAttributeContentStr;
    /// let s = QuotAttributeContentStr::new("attribute content with &quot;");
    /// ```
    ///
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s).unwrap_or_else(|e| {
            panic!(
                "The given string is not valid content of attribute with quotation marks: {}",
                e
            )
        })
    }

    /// Creates a new `&QuotAttributeContentStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid content of an attribute with quotation marks.
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for content of an attribute with quotation marks (`"`).
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QuotAttributeContentString(Box<QuotAttributeContentStr>);

impl_string_types! {
    owned: QuotAttributeContentString,
    slice: QuotAttributeContentStr,
    error_slice: AttributeContentError,
    parse: parse,
    slice_new_unchecked: QuotAttributeContentStr::new_unchecked,
}

impl_string_cmp! {
    owned: QuotAttributeContentString,
    slice: QuotAttributeContentStr,
}

impl_string_cmp_to_string! {
    owned: QuotAttributeContentString,
    slice: QuotAttributeContentStr,
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
        assert_eq!(parse_raw("'"), Complete(()));
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
        assert_eq!(parse_raw("foo\"bar"), UnexpectedQuote(Partial::new((), 3)));
    }
}
