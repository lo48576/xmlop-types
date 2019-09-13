//! [`CharData`], content of text node except CDATA section and references.
//!
//! About `CharData`, see [Extensible Markup Language (XML) 1.0 (Fifth Edition)][`CharData`].
//!
//! [`CharData`]: http://www.w3.org/TR/REC-xml/#NT-CharData

use std::{convert::TryFrom, error, fmt};

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
    /// Validates the given string, and returns `Ok(())` if the string is valid.
    fn validate(s: &str) -> Result<(), CharDataError> {
        let invalid_char = s.find(|c| c == '&' || c == '<');
        let cdata_section_close = s.find("]]>");

        match (invalid_char, cdata_section_close) {
            (None, Some(cdata_close_pos)) => {
                Err(CharDataError::CdataSectionClosed(cdata_close_pos))
            }
            (Some(char_pos), Some(cdata_close_pos)) if char_pos > cdata_close_pos => {
                Err(CharDataError::CdataSectionClosed(cdata_close_pos))
            }
            (Some(char_pos), _) => {
                let err = if s.as_bytes()[char_pos] == b'&' {
                    CharDataError::UnexpectedAmpersand(char_pos)
                } else {
                    CharDataError::UnexpectedLt(char_pos)
                };
                Err(err)
            }
            (None, None) => Ok(()),
        }
    }

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
    validate: CharDataStr::validate,
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
