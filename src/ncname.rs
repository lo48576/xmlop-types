//! `NCName`.
//!
//! About `NCName`, see [Namespaces in XML 1.0 (Third Edition)][`NCName`].
//!
//! [`NCName`]: https://www.w3.org/TR/xml-names/#NT-NCName

use std::{convert::TryFrom, error, fmt};

use crate::{
    name::{NameStr, NameString},
    parser::{
        chars::{is_name_char_except_colon, is_name_start_char_except_colon},
        Partial, PartialMapWithStr,
    },
    qname::{QnameStr, QnameString},
};

/// Parse result of `NCName`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Empty value.
    Empty,
    /// Invalid character.
    InvalidCharacter(Option<Partial<T>>),
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, NcnameError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::Empty => Err(NcnameError::Empty),
            Self::InvalidCharacter(part) => Err(NcnameError::InvalidCharacter(
                part.map_or(0, |part| part.valid_up_to()),
            )),
        }
    }
}

/// Parses the given string as `NCName`.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    let mut chars = s.char_indices();
    match chars.next() {
        Some((_, first)) if !is_name_start_char_except_colon(first) => {
            return ParseResult::InvalidCharacter(None)
        }
        Some(_) => {}
        None => return ParseResult::Empty,
    }
    if let Some((pos, _)) = chars.find(|(_, c)| !is_name_char_except_colon(*c)) {
        return ParseResult::InvalidCharacter(Some(Partial::new((), pos)));
    }

    ParseResult::Complete(())
}

/// Parses the given string as `NCName`.
fn parse(s: &str) -> ParseResult<&NcnameStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => ParseResult::Complete(unsafe { NcnameStr::new_unchecked(s) }),
        ParseResult::Empty => ParseResult::Empty,
        ParseResult::InvalidCharacter(part) => ParseResult::InvalidCharacter(
            part.map_with_str(s, |_, s| unsafe { NcnameStr::new_unchecked(s) }),
        ),
    }
}

/// Error for [`NcnameStr`].
///
/// [`NcnameStr`]: struct.NcnameStr.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NcnameError {
    /// The string is empty.
    Empty,
    /// The string has an invaild character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
}

impl error::Error for NcnameError {}

impl fmt::Display for NcnameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NcnameError::Empty => write!(f, "empty string"),
            NcnameError::InvalidCharacter(pos) => write!(f, "invalid character at index {}", pos),
        }
    }
}

/// String slice for XML [`NCName`].
///
/// [`NCName`]: https://www.w3.org/TR/xml-names/#NT-NCName
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NcnameStr(str);

impl NcnameStr {
    /// Creates a new `&NcnameStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::ncname::{NcnameError, NcnameStr};
    /// assert!(NcnameStr::new_checked("ValidNCName").is_ok());
    ///
    /// assert_eq!(NcnameStr::new_checked(""), Err(NcnameError::Empty));
    /// assert_eq!(NcnameStr::new_checked("012InvalidNCName"), Err(NcnameError::InvalidCharacter(0)));
    /// assert_eq!(NcnameStr::new_checked("foo bar"), Err(NcnameError::InvalidCharacter(3)));
    /// assert_eq!(NcnameStr::new_checked("foo:bar"), Err(NcnameError::InvalidCharacter(3)));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, NcnameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&NcnameStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`NCName`] string.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::ncname::NcnameStr;
    /// let name = NcnameStr::new("ValidNCName");
    /// ```
    ///
    /// [`NCName`]: http://www.w3.org/TR/REC-xml/#NT-NCName
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `NCName` string: {}", e))
    }

    /// Creates a new `&NcnameStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`NCName`] string.
    ///
    /// [`NCName`]: http://www.w3.org/TR/REC-xml/#NT-NCName
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }

    /// Converts the reference to [`&QnameStr`].
    ///
    /// [`&QnameStr`]: ../qname/struct.QnameStr.html
    pub fn as_qname(&self) -> &QnameStr {
        self.as_ref()
    }

    /// Converts the reference to [`&NameStr`].
    ///
    /// [`&NameStr`]: ../qname/struct.NameStr.html
    pub fn as_name(&self) -> &NameStr {
        self.as_ref()
    }
}

impl AsRef<QnameStr> for NcnameStr {
    fn as_ref(&self) -> &QnameStr {
        <&QnameStr>::try_from(self.as_str())
            .unwrap_or_else(|_| unreachable!("`NCName` is also valid `QName`"))
    }
}

impl<'a> From<&'a NcnameStr> for &'a QnameStr {
    fn from(s: &'a NcnameStr) -> &'a QnameStr {
        s.as_ref()
    }
}

impl AsRef<NameStr> for NcnameStr {
    fn as_ref(&self) -> &NameStr {
        <&NameStr>::try_from(self.as_str())
            .unwrap_or_else(|_| unreachable!("`NCName` is also valid `Name`"))
    }
}

impl<'a> From<&'a NcnameStr> for &'a NameStr {
    fn from(s: &'a NcnameStr) -> &'a NameStr {
        s.as_ref()
    }
}

/// Owned string for XML [`NCName`].
///
/// [`NCName`]: http://www.w3.org/TR/REC-xml/#NT-NCName
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NcnameString(Box<NcnameStr>);

impl AsRef<QnameStr> for NcnameString {
    fn as_ref(&self) -> &QnameStr {
        (*self.0).as_ref()
    }
}

impl From<NcnameString> for QnameString {
    fn from(s: NcnameString) -> QnameString {
        let s: String = s.into();
        Self::try_from(s).unwrap_or_else(|_| unreachable!("`NCName` is also valid `QName`"))
    }
}

impl AsRef<NameStr> for NcnameString {
    fn as_ref(&self) -> &NameStr {
        (*self.0).as_ref()
    }
}

impl From<NcnameString> for NameString {
    fn from(s: NcnameString) -> NameString {
        let s: String = s.into();
        Self::try_from(s).unwrap_or_else(|_| unreachable!("`NCName` is also valid `Name`"))
    }
}

impl_string_types! {
    owned: NcnameString,
    slice: NcnameStr,
    error_slice: NcnameError,
    parse: parse,
    slice_new_unchecked: NcnameStr::new_unchecked,
}

impl_string_cmp! {
    owned: NcnameString,
    slice: NcnameStr,
}

impl_string_cmp_to_string! {
    owned: NcnameString,
    slice: NcnameStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{Complete, Empty, InvalidCharacter};

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw("Valid-NCName"), Complete(()));

        assert_eq!(parse_raw(""), Empty);
        assert_eq!(parse_raw("012InvalidNCName"), InvalidCharacter(None));
        assert_eq!(
            parse_raw("foo:bar"),
            InvalidCharacter(Some(Partial::new((), 3)))
        );
        assert_eq!(
            parse_raw("foo bar"),
            InvalidCharacter(Some(Partial::new((), 3)))
        );
        assert_eq!(
            parse_raw("foo>bar"),
            InvalidCharacter(Some(Partial::new((), 3)))
        );
        assert_eq!(
            parse_raw("foo<bar"),
            InvalidCharacter(Some(Partial::new((), 3)))
        );
        assert_eq!(
            parse_raw("foo&bar"),
            InvalidCharacter(Some(Partial::new((), 3)))
        );
    }
}
