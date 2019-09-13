//! String types for content of XML text nodes, including CDATA section and references.
//!
//! `TextStr` and `TextString` contains unprocessed valid `#PCDATA`, which consists of zero or more
//! entity references, character references, character data (`CData`s), and CDATA sections.

use std::{convert::TryFrom, error, fmt};

use crate::name::NameStr;

/// Error for text.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum TextError {
    /// Invalid use of ampersand (`&`).
    ///
    /// This error can be caused by unclosed reference (entity reference and character reference)
    /// or invalid (non-`Name`) string following `&`.
    ///
    /// The first `usize` field is the byte position of the starting `&`.
    InvalidAmpersand(usize),
    /// Unclosed CDATA section.
    ///
    /// The first `usize` field is the byte position of the starting `<`.
    UnclosedCdataSection(usize),
    /// Unescaped gt (`>`).
    ///
    /// The first `usize` field is the byte position of the unescaped `>`.
    UnescapedGt(usize),
    /// Unescaped lt (`<`).
    ///
    /// The first `usize` field is the byte position of the unescaped `<`.
    UnescapedLt(usize),
}

impl error::Error for TextError {}

impl fmt::Display for TextError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            TextError::InvalidAmpersand(pos) => {
                write!(f, "Found invalid ampersand use at index {}", pos)
            }
            TextError::UnclosedCdataSection(pos) => {
                write!(f, "Found unclosed CDATA section at index {}", pos)
            }
            TextError::UnescapedGt(pos) => write!(f, "Found unescaped `>` at index {}", pos),
            TextError::UnescapedLt(pos) => write!(f, "Found unescaped `<` at index {}", pos),
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
    /// Validates the given string, and returns `Ok(())` if the string is valid.
    fn validate(s: &str) -> Result<(), TextError> {
        let mut chars = s.chars();
        while let Some(first) = chars.next() {
            match first {
                '<' => {
                    let following = chars.as_str();
                    if !following.starts_with("![CDATA[") {
                        return Err(TextError::UnescapedLt(s.len() - following.len() - 1));
                    }
                    // `3`: `"]]>".len()`.
                    let pos_after_cdata_end = following.find("]]>").ok_or_else(|| {
                        TextError::UnclosedCdataSection(s.len() - following.len() - 1)
                    })? + 3;
                    chars = following[pos_after_cdata_end..].chars();
                }
                '>' => return Err(TextError::UnescapedGt(s.len() - chars.as_str().len() - 1)),
                '&' => {
                    let following = chars.as_str();
                    let semicolon_pos = following.find(';').ok_or_else(|| {
                        TextError::InvalidAmpersand(s.len() - following.len() - 1)
                    })?;
                    let before_semicolon = &following[..semicolon_pos];
                    let mut inner_chars = before_semicolon.chars();
                    match inner_chars.next() {
                        Some('#') => {
                            let after_hash = inner_chars.next().ok_or_else(|| {
                                TextError::InvalidAmpersand(s.len() - chars.as_str().len() - 1)
                            })?;
                            let is_valid_ref = if after_hash == 'x' {
                                // Expected `"&#x" [0-9a-fA-F]+ ";".
                                before_semicolon.len() > 1
                                    && inner_chars.all(|c| c.is_ascii_hexdigit())
                            } else if after_hash.is_ascii_digit() {
                                // Expected `"&#" [0-9]+ ";".
                                inner_chars.all(|c| c.is_ascii_digit())
                            } else {
                                false
                            };
                            if !is_valid_ref {
                                return Err(TextError::InvalidAmpersand(
                                    s.len() - chars.as_str().len() - 1,
                                ));
                            }
                        }
                        Some(_) => {
                            if <&NameStr>::try_from(before_semicolon).is_err() {
                                return Err(TextError::InvalidAmpersand(
                                    s.len() - chars.as_str().len() - 1,
                                ));
                            }
                        }
                        None => {
                            return Err(TextError::InvalidAmpersand(
                                s.len() - chars.as_str().len() - 1,
                            ))
                        }
                    }
                    // `1` is length of the following semicolon (`;`).
                    chars = following[(semicolon_pos + 1)..].chars();
                }
                _ => {}
            }
        }

        Ok(())
    }

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
    /// assert_eq!(TextStr::new_checked(">"), Err(TextError::UnescapedGt(0)));
    /// assert_eq!(TextStr::new_checked("<"), Err(TextError::UnescapedLt(0)));
    /// assert_eq!(TextStr::new_checked("&"), Err(TextError::InvalidAmpersand(0)));
    /// assert_eq!(TextStr::new_checked("foo&bar"), Err(TextError::InvalidAmpersand(3)));
    /// assert_eq!(TextStr::new_checked("&foo bar;"), Err(TextError::InvalidAmpersand(0)));
    /// assert_eq!(TextStr::new_checked("&#3C;"), Err(TextError::InvalidAmpersand(0)));
    /// assert_eq!(TextStr::new_checked("&#xZ;"), Err(TextError::InvalidAmpersand(0)));
    /// assert_eq!(
    ///     TextStr::new_checked("<![CDATA[<![CDATA[]]>]]>"),
    ///     Err(TextError::UnescapedGt(23))
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
    validate: TextStr::validate,
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
