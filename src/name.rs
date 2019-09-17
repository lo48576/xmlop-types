//! [`Name`].
//!
//! About `Name`, see [Extensible Markup Language (XML) 1.0 (Fifth Edition)][`Name`].
//!
//! [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name

use std::{convert::TryFrom, error, fmt};

use crate::parser::chars::{is_name_char, is_name_start_char};

/// Error for `Name`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum NameError {
    /// The string is empty.
    Empty,
    /// The string has an invaild character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
}

impl error::Error for NameError {}

impl fmt::Display for NameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            NameError::Empty => write!(f, "empty string"),
            NameError::InvalidCharacter(pos) => write!(f, "invalid character at index {}", pos),
        }
    }
}

/// String slice for XML [`Name`].
///
/// [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct NameStr(str);

impl NameStr {
    /// Validates the given string, and returns `Ok(())` if the string is valid.
    fn validate(s: &str) -> Result<(), NameError> {
        let mut chars = s.char_indices();
        match chars.next() {
            Some((_index, first)) => {
                if !is_name_start_char(first) {
                    return Err(NameError::InvalidCharacter(0));
                }
            }
            None => return Err(NameError::Empty),
        }
        if let Some((index, _char)) = chars.find(|(_, c)| !is_name_char(*c)) {
            return Err(NameError::InvalidCharacter(index));
        }
        Ok(())
    }

    /// Creates a new `&NameStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::name::{NameError, NameStr};
    /// assert!(NameStr::new_checked("ValidName").is_ok());
    ///
    /// assert_eq!(NameStr::new_checked(""), Err(NameError::Empty));
    /// assert_eq!(NameStr::new_checked("012InvalidName"), Err(NameError::InvalidCharacter(0)));
    /// assert_eq!(NameStr::new_checked("foo bar"), Err(NameError::InvalidCharacter(3)));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, NameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&NameStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`Name`] string.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::name::NameStr;
    /// let name = NameStr::new("ValidName");
    /// ```
    ///
    /// [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `Name` string: {}", e))
    }

    /// Creates a new `&NameStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`Name`] string.
    ///
    /// [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for XML [`Name`].
///
/// [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct NameString(Box<NameStr>);

impl_string_types! {
    owned: NameString,
    slice: NameStr,
    error_slice: NameError,
    validate: NameStr::validate,
    slice_new_unchecked: NameStr::new_unchecked,
}

impl_string_cmp! {
    owned: NameString,
    slice: NameStr,
}

impl_string_cmp_to_string! {
    owned: NameString,
    slice: NameStr,
}
