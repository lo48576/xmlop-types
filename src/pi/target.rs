//! [`PITarget`], target name of a processing instruction.
//!
//! About `PITarget`, see [Extensible Markup Language (XML) 1.0 (Fifth Edition)][`PITarget`].
//!
//! [`PITarget`]: http://www.w3.org/TR/REC-xml/#NT-PITarget

use std::{convert::TryFrom, error, fmt};

use crate::{
    name::{
        plain::{parse_raw as parse_name, ParseResult as NameResult},
        NameError,
    },
    parser::{Partial, PartialMapWithStr},
};

/// Parse result of `PITarget`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Invalid name.
    InvalidName(Option<Partial<T>>, NameError),
    /// Reserved name.
    ///
    /// Note that in this case `s[0..=2]` is valid `PItarget` (but this does not mean `s[0..=3]` is
    /// valid).
    ReservedName,
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, PiTargetError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::InvalidName(_, e) => Err(PiTargetError::InvalidName(e)),
            Self::ReservedName => Err(PiTargetError::ReservedName),
        }
    }
}

/// Parses the given string as `PITarget`.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    match parse_name(s) {
        NameResult::Complete(_) => {
            if s.eq_ignore_ascii_case("xml") {
                ParseResult::ReservedName
            } else {
                ParseResult::Complete(())
            }
        }
        NameResult::Empty => ParseResult::InvalidName(None, NameError::Empty),
        NameResult::InvalidCharacter(part) => {
            let part = match part {
                Some(v) => v,
                None => return ParseResult::InvalidName(None, NameError::InvalidCharacter(0)),
            };
            if s[..part.valid_up_to()].eq_ignore_ascii_case("xml") {
                ParseResult::ReservedName
            } else {
                ParseResult::InvalidName(
                    Some(part),
                    NameError::InvalidCharacter(part.valid_up_to()),
                )
            }
        }
    }
}

/// Parses the given string as `PITarget`.
fn parse(s: &str) -> ParseResult<&PiTargetStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => {
            ParseResult::Complete(unsafe { PiTargetStr::new_unchecked(s) })
        }
        ParseResult::InvalidName(part, e) => ParseResult::InvalidName(
            part.map_with_str(s, |_, s| unsafe { PiTargetStr::new_unchecked(s) }),
            e,
        ),
        ParseResult::ReservedName => ParseResult::ReservedName,
    }
}

/// Error for `PITarget`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum PiTargetError {
    /// Found invalid name.
    InvalidName(NameError),
    /// Reserved name.
    ///
    /// Note that extra data may follow after the reserved name.
    ReservedName,
}

impl error::Error for PiTargetError {
    fn source(&self) -> Option<&(dyn error::Error + 'static)> {
        match self {
            Self::InvalidName(e) => Some(e),
            _ => None,
        }
    }
}

impl fmt::Display for PiTargetError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            PiTargetError::InvalidName(e) => write!(f, "Invalid character as PITarget: {}", e),
            PiTargetError::ReservedName => f.write_str("Reserved (forbidden) PITarget name"),
        }
    }
}

/// String slice for [`PITarget`].
///
/// [`PITarget`]: http://www.w3.org/TR/REC-xml/#NT-PITarget
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct PiTargetStr(str);

impl PiTargetStr {
    /// Creates a new `&PiTargetStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::pi::{PiTargetError, PiTargetStr};
    /// assert!(PiTargetStr::new_checked("valid-pi-target").is_ok());
    /// assert!(PiTargetStr::new_checked("multiple:colons:are:ok").is_ok());
    /// assert!(PiTargetStr::new_checked("xml-prefix-is-ok").is_ok());
    ///
    /// assert_eq!(
    ///     PiTargetStr::new_checked("foo bar"),
    ///     Err(PiTargetError::InvalidName(xmlop_types::name::NameError::InvalidCharacter(3)))
    /// );
    /// assert_eq!(
    ///     PiTargetStr::new_checked(""),
    ///     Err(PiTargetError::InvalidName(xmlop_types::name::NameError::Empty))
    /// );
    /// assert_eq!(
    ///     PiTargetStr::new_checked("foo<bar"),
    ///     Err(PiTargetError::InvalidName(xmlop_types::name::NameError::InvalidCharacter(3)))
    /// );
    /// assert_eq!(PiTargetStr::new_checked("xml"), Err(PiTargetError::ReservedName));
    /// assert_eq!(PiTargetStr::new_checked("XmL"), Err(PiTargetError::ReservedName));
    /// assert_eq!(PiTargetStr::new_checked("xml foo"), Err(PiTargetError::ReservedName));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, PiTargetError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&PiTargetStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`PITarget`] string.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::pi::PiTargetStr;
    /// let s = PiTargetStr::new("valid-pi-target");
    /// ```
    ///
    /// [`PITarget`]: http://www.w3.org/TR/REC-xml/#NT-PITarget
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `PITarget` string: {}", e))
    }

    /// Creates a new `&PiTargetStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`PITarget`] string.
    ///
    /// [`PITarget`]: http://www.w3.org/TR/REC-xml/#NT-PITarget
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for [`PITarget`].
///
/// [`PITarget`]: http://www.w3.org/TR/REC-xml/#NT-PITarget
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct PiTargetString(Box<PiTargetStr>);

impl_string_types! {
    owned: PiTargetString,
    slice: PiTargetStr,
    error_slice: PiTargetError,
    parse: parse,
    slice_new_unchecked: PiTargetStr::new_unchecked,
}

impl_string_cmp! {
    owned: PiTargetString,
    slice: PiTargetStr,
}

impl_string_cmp_to_string! {
    owned: PiTargetString,
    slice: PiTargetStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{Complete, InvalidName, ReservedName};

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw("valid-pi-target"), Complete(()));
        assert_eq!(parse_raw("multiple:colons:are:ok"), Complete(()));
        assert_eq!(parse_raw("xml-prefix-is-ok"), Complete(()));

        assert_eq!(parse_raw(""), InvalidName(None, NameError::Empty));
        assert_eq!(
            parse_raw("foo bar"),
            InvalidName(Some(Partial::new((), 3)), NameError::InvalidCharacter(3))
        );
        assert_eq!(
            parse_raw("foo<bar"),
            InvalidName(Some(Partial::new((), 3)), NameError::InvalidCharacter(3))
        );
        assert_eq!(parse_raw("xml"), ReservedName);
        assert_eq!(parse_raw("XmL"), ReservedName);
        assert_eq!(parse_raw("xml foo"), ReservedName);
    }
}
