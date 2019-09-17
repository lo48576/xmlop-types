//! `QName`.
//!
//! About `QName`, see [Namespaces in XML 1.0 (Third Edition)][`QName`].
//!
//! [`QName`]: https://www.w3.org/TR/xml-names/#NT-QName

use std::{convert::TryFrom, error, fmt};

use crate::{
    name::{NameStr, NameString},
    ncname::{NcnameStr, NcnameString},
    parser::chars::{is_name_char_except_colon, is_name_start_char_except_colon},
};

/// Error for [`QnameStr`].
///
/// [`QnameStr`]: struct.QnameStr.html
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum QnameError {
    /// The string is empty.
    Empty,
    /// The string has an invaild character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
    /// Extra colon is found.
    ///
    /// `usize` field is the first byte position of the second colon.
    ExtraColon(usize),
    /// Prefix is empty, i.e. the first character was colon.
    EmptyPrefix,
    /// Local part is empty, i.e. the last character was colon.
    EmptyLocalPart,
}

impl error::Error for QnameError {}

impl fmt::Display for QnameError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            QnameError::Empty => write!(f, "empty string"),
            QnameError::InvalidCharacter(pos) => write!(f, "invalid character at index {}", pos),
            QnameError::ExtraColon(pos) => write!(f, "extra colon found at index {}", pos),
            QnameError::EmptyPrefix => write!(f, "empty prefix"),
            QnameError::EmptyLocalPart => write!(f, "empty local part"),
        }
    }
}

/// String slice for XML [`QName`].
///
/// [`QName`]: https://www.w3.org/TR/xml-names/#NT-QName
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct QnameStr(str);

impl QnameStr {
    /// Validates the given string, and returns `Ok(())` if the string is valid.
    fn validate(s: &str) -> Result<(), QnameError> {
        let mut chars = s.char_indices();
        match chars.next() {
            Some((_index, first)) => {
                if first == ':' {
                    return Err(QnameError::EmptyPrefix);
                }
                if !is_name_start_char_except_colon(first) {
                    return Err(QnameError::InvalidCharacter(0));
                }
            }
            None => return Err(QnameError::Empty),
        }

        let mut found_colon = false;
        for (index, c) in chars {
            if c == ':' {
                if found_colon {
                    // This is the second colon.
                    return Err(QnameError::ExtraColon(index));
                }
                found_colon = true;
                continue;
            }
            if !is_name_char_except_colon(c) {
                return Err(QnameError::InvalidCharacter(index));
            }
        }

        let last = s
            .chars()
            .next_back()
            .unwrap_or_else(|| unreachable!("`s` is not empty"));
        if last == ':' {
            return Err(QnameError::EmptyLocalPart);
        }

        Ok(())
    }

    /// Creates a new `&QnameStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::qname::{QnameError, QnameStr};
    /// assert!(QnameStr::new_checked("ValidQName").is_ok());
    /// assert!(QnameStr::new_checked("foo:bar").is_ok());
    ///
    /// assert_eq!(QnameStr::new_checked(""), Err(QnameError::Empty));
    /// assert_eq!(QnameStr::new_checked("012InvalidQName"), Err(QnameError::InvalidCharacter(0)));
    /// assert_eq!(QnameStr::new_checked("foo bar"), Err(QnameError::InvalidCharacter(3)));
    /// assert_eq!(QnameStr::new_checked("foo:bar:baz"), Err(QnameError::ExtraColon(7)));
    /// assert_eq!(QnameStr::new_checked(":foo"), Err(QnameError::EmptyPrefix));
    /// assert_eq!(QnameStr::new_checked("foo:"), Err(QnameError::EmptyLocalPart));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, QnameError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&QnameStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`QName`] string.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::qname::QnameStr;
    /// let name = QnameStr::new("ValidQName");
    /// ```
    ///
    /// [`QName`]: https://www.w3.org/TR/xml-names/#NT-QName
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `QName` string: {}", e))
    }

    /// Creates a new `&QnameStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`QName`] string.
    ///
    /// [`QName`]: https://www.w3.org/TR/xml-names/#NT-QName
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }

    /// Converts the reference to [`&NameStr`].
    ///
    /// [`&NameStr`]: ../qname/struct.NameStr.html
    pub fn as_name(&self) -> &NameStr {
        self.as_ref()
    }

    /// Splits the `QName` into prefix and local part.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::{ncname::NcnameStr, qname::QnameStr};
    ///
    /// assert_eq!(QnameStr::new("foo").prefix_and_local_part(), (None, NcnameStr::new("foo")));
    /// assert_eq!(
    ///     QnameStr::new("foo:bar").prefix_and_local_part(),
    ///     (Some(NcnameStr::new("foo")), NcnameStr::new("bar"))
    /// );
    /// ```
    pub fn prefix_and_local_part(&self) -> (Option<&NcnameStr>, &NcnameStr) {
        match self.as_str().find(':') {
            Some(colon_pos) => {
                let (prefix, colon_and_local) = self.as_str().split_at(colon_pos);
                let local = &colon_and_local[1..];
                (
                    Some(<&NcnameStr>::try_from(prefix).unwrap_or_else(|_| {
                        unreachable!("Prefix of `QName` is also valid `NCName`")
                    })),
                    <&NcnameStr>::try_from(local).unwrap_or_else(|_| {
                        unreachable!("Local part of `QName` is also valid `NCName`")
                    }),
                )
            }
            None => (
                None,
                <&NcnameStr>::try_from(self.as_str()).unwrap_or_else(|_| {
                    unreachable!("`QName` without colon is also valid `NCName`")
                }),
            ),
        }
    }

    /// Returns the prefix of the `QName`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::{ncname::NcnameStr, qname::QnameStr};
    ///
    /// assert_eq!(QnameStr::new("foo").prefix(), None);
    /// assert_eq!(QnameStr::new("foo:bar").prefix(), Some(NcnameStr::new("foo")));
    /// ```
    pub fn prefix(&self) -> Option<&NcnameStr> {
        self.as_str().find(':').map(|colon_pos| {
            let prefix = &self.as_str()[..colon_pos];
            <&NcnameStr>::try_from(prefix)
                .unwrap_or_else(|_| unreachable!("Prefix of `QName` is also valid `NCName`"))
        })
    }

    /// Returns the local part of the `QName`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::{ncname::NcnameStr, qname::QnameStr};
    ///
    /// assert_eq!(QnameStr::new("foo").local_part(), NcnameStr::new("foo"));
    /// assert_eq!(QnameStr::new("foo:bar").local_part(), NcnameStr::new("bar"));
    /// ```
    pub fn local_part(&self) -> &NcnameStr {
        let local = self
            .as_str()
            .find(':')
            .map(|colon_pos| {
                // `colon_pos + 1` does not overflow because some characters must follow after the colon.
                &self.as_str()[(colon_pos + 1)..]
            })
            .unwrap_or_else(|| self.as_str());
        <&NcnameStr>::try_from(local)
            .unwrap_or_else(|_| unreachable!("Local part of `QName` is also valid `NCName`"))
    }
}

impl AsRef<NameStr> for QnameStr {
    fn as_ref(&self) -> &NameStr {
        <&NameStr>::try_from(self.as_str())
            .unwrap_or_else(|_| unreachable!("`QName` is also valid `Name`"))
    }
}

impl<'a> From<&'a QnameStr> for &'a NameStr {
    fn from(s: &'a QnameStr) -> &'a NameStr {
        s.as_ref()
    }
}

/// Owned string for XML [`QName`].
///
/// [`QName`]: https://www.w3.org/TR/xml-names/#NT-QName
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct QnameString(Box<QnameStr>);

impl QnameString {
    /// Splits the `QName` into prefix and local part.
    ///
    /// # Examples
    ///
    /// ```
    /// use std::convert::TryFrom;
    /// # use xmlop_types::{ncname::NcnameStr, qname::QnameString};
    ///
    /// let (foo_prefix, foo_local) = QnameString::try_from("foo")
    ///     .expect("Should never fail")
    ///     .into_prefix_and_local_part();
    /// assert_eq!(foo_prefix, None);
    /// assert_eq!(foo_local, NcnameStr::new("foo"));
    ///
    /// let (foo_bar_prefix, foo_bar_local) = QnameString::try_from("foo:bar")
    ///     .expect("Should never fail")
    ///     .into_prefix_and_local_part();
    /// assert_eq!(foo_bar_prefix.as_ref().map(AsRef::as_ref), Some(NcnameStr::new("foo")));
    /// assert_eq!(foo_bar_local, NcnameStr::new("bar"));
    /// ```
    pub fn into_prefix_and_local_part(self) -> (Option<NcnameString>, NcnameString) {
        match self.as_str().find(':') {
            Some(colon_pos) => {
                // `colon_pos + 1` does not overflow because some characters must follow after the colon.
                let local = self.as_str()[(colon_pos + 1)..].to_owned();
                let mut prefix: String = self.into();
                prefix.truncate(colon_pos);
                (
                    Some(NcnameString::try_from(prefix).unwrap_or_else(|_| {
                        unreachable!("Prefix of `QName` is also valid `NCName`")
                    })),
                    NcnameString::try_from(local).unwrap_or_else(|_| {
                        unreachable!("Local part of `QName` is also valid `NCName`")
                    }),
                )
            }
            None => (
                None,
                NcnameString::try_from(Into::<String>::into(self)).unwrap_or_else(|_| {
                    unreachable!("`QName` without colon is also valid `NCName`")
                }),
            ),
        }
    }
}

impl AsRef<NameStr> for QnameString {
    fn as_ref(&self) -> &NameStr {
        (*self.0).as_ref()
    }
}

impl From<QnameString> for NameString {
    fn from(s: QnameString) -> NameString {
        let s: String = s.into();
        Self::try_from(s).unwrap_or_else(|_| unreachable!("`QName` is also valid `Name`"))
    }
}

impl_string_types! {
    owned: QnameString,
    slice: QnameStr,
    error_slice: QnameError,
    validate: QnameStr::validate,
    slice_new_unchecked: QnameStr::new_unchecked,
}

impl_string_cmp! {
    owned: QnameString,
    slice: QnameStr,
}

impl_string_cmp_to_string! {
    owned: QnameString,
    slice: QnameStr,
}
