//! Entity reference and character reference.
//!
//! See <https://www.w3.org/TR/REC-xml/#NT-Reference>.

use std::{convert::TryFrom, error, fmt};

use crate::{
    name::{self, ParseResult as NameResult},
    parser::{Partial, PartialMapWithStr},
};

pub use self::entity::{EntityRefStr, EntityRefString};

mod entity;

/// Parse result of `Reference`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Extra data follows.
    Extra(Partial<T>),
    /// Missing the leading ampersand.
    MissingAmpersand,
    /// Missing character code.
    MissingCharacterCode,
    /// Missing entity name.
    MissingName,
    /// Missing the trailing semicolon.
    MissingSemicolon,
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, ReferenceError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::Extra(part) => Err(ReferenceError::ExtraData(part.valid_up_to())),
            Self::MissingAmpersand => Err(ReferenceError::MissingAmpersand),
            Self::MissingCharacterCode => Err(ReferenceError::MissingCharacterCode),
            Self::MissingName => Err(ReferenceError::MissingName),
            Self::MissingSemicolon => Err(ReferenceError::MissingSemicolon),
        }
    }
}

/// Parses the given string as reference.
pub(crate) fn parse_raw(s: &str) -> ParseResult<RefereneceType> {
    if s.as_bytes().get(0) != Some(&b'&') {
        return ParseResult::MissingAmpersand;
    }

    let (semicolon_pos, ty) = if s.as_bytes().get(1) == Some(&b'#') {
        /// Offset of decimal character code.
        ///
        /// 2: `"&#".len()`.
        const DEC_OFFSET: usize = 2;
        /// Offset of hexadecimal character code.
        ///
        /// 3: `"&#x".len()`.
        const HEX_OFFSET: usize = 3;

        match s.as_bytes().get(2) {
            Some(b'x') => match s[HEX_OFFSET..]
                .as_bytes()
                .iter()
                .position(|c| !c.is_ascii_hexdigit())
            {
                Some(0) => return ParseResult::MissingCharacterCode,
                Some(i) if s.as_bytes()[HEX_OFFSET + i] != b';' => {
                    return ParseResult::MissingSemicolon
                }
                Some(i) => (HEX_OFFSET + i, RefereneceType::Hex),
                None if s.len() == HEX_OFFSET => return ParseResult::MissingCharacterCode,
                None => return ParseResult::MissingSemicolon,
            },
            Some(_) => match s[DEC_OFFSET..]
                .as_bytes()
                .iter()
                .position(|c| !c.is_ascii_digit())
            {
                Some(0) => return ParseResult::MissingCharacterCode,
                Some(i) if s.as_bytes()[DEC_OFFSET + i] != b';' => {
                    return ParseResult::MissingSemicolon
                }
                Some(i) => (DEC_OFFSET + i, RefereneceType::Dec),
                None if s.len() == DEC_OFFSET => return ParseResult::MissingCharacterCode,
                None => return ParseResult::MissingSemicolon,
            },
            None => return ParseResult::MissingCharacterCode,
        }
    } else {
        // Expect `Name`.
        match name::parse_raw(&s[1..]) {
            NameResult::Complete(()) => return ParseResult::MissingSemicolon,
            NameResult::Empty | NameResult::InvalidCharacter(None) => {
                return ParseResult::MissingName
            }
            NameResult::InvalidCharacter(Some(part)) => {
                let expected_semicolon_pos = part.valid_up_to() + 1;
                if s.as_bytes()[expected_semicolon_pos] != b';' {
                    return ParseResult::MissingSemicolon;
                }
                (expected_semicolon_pos, RefereneceType::Entity)
            }
        }
    };
    assert_eq!(s.as_bytes()[semicolon_pos], b';');
    if semicolon_pos != s.len() - 1 {
        return ParseResult::Extra(Partial::new(ty, semicolon_pos + 1));
    }

    ParseResult::Complete(ty)
}

/// Parses the given string as `Reference`.
fn parse(s: &str) -> ParseResult<&ReferenceStr> {
    match parse_raw(s) {
        ParseResult::Complete(_) => {
            ParseResult::Complete(unsafe { ReferenceStr::new_unchecked(s) })
        }
        ParseResult::Extra(part) => ParseResult::Extra(
            part.map_with_str(s, |_, s| unsafe { ReferenceStr::new_unchecked(s) }),
        ),
        ParseResult::MissingAmpersand => ParseResult::MissingAmpersand,
        ParseResult::MissingCharacterCode => ParseResult::MissingCharacterCode,
        ParseResult::MissingName => ParseResult::MissingName,
        ParseResult::MissingSemicolon => ParseResult::MissingSemicolon,
    }
}

/// Type of character reference and entity reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[allow(dead_code)]
pub(crate) enum RefereneceType {
    /// Entity reference.
    Entity,
    /// Character reference with decimal.
    Dec,
    /// Character reference with hexadecimal.
    Hex,
}

/// Error for reference.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum ReferenceError {
    /// Extra data follows.
    ///
    /// `usize` field is the first byte position of the extra data after `]]>`.
    ExtraData(usize),
    /// Missing the leading ampersand.
    MissingAmpersand,
    /// Missing character code.
    MissingCharacterCode,
    /// Missing entity name.
    MissingName,
    /// Missing the trailing semicolon.
    MissingSemicolon,
}

impl error::Error for ReferenceError {}

impl fmt::Display for ReferenceError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            ReferenceError::ExtraData(pos) => write!(f, "Extra following data at index {}", pos),
            ReferenceError::MissingAmpersand => f.write_str("Missing ampersand"),
            ReferenceError::MissingCharacterCode => f.write_str("Missing character code"),
            ReferenceError::MissingName => f.write_str("Missing entity name"),
            ReferenceError::MissingSemicolon => f.write_str("Missing semicolon"),
        }
    }
}

/// String slice for `Reference`.
///
/// See module documentation for detail.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct ReferenceStr(str);

impl ReferenceStr {
    /// Creates a new `&ReferenceStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::reference::{ReferenceError, ReferenceStr};
    /// assert!(ReferenceStr::new_checked("&lt;").is_ok());
    /// assert!(ReferenceStr::new_checked("&valid-reference;").is_ok());
    /// assert!(ReferenceStr::new_checked("&#60;").is_ok());
    /// assert!(ReferenceStr::new_checked("&#x3c;").is_ok());
    /// assert!(ReferenceStr::new_checked("&#x3C;").is_ok());
    /// assert!(ReferenceStr::new_checked("&#x10FFFF;").is_ok());
    ///
    /// assert_eq!(ReferenceStr::new_checked("&lt;foo"), Err(ReferenceError::ExtraData(4)));
    /// assert_eq!(ReferenceStr::new_checked("&#60;foo"), Err(ReferenceError::ExtraData(5)));
    /// assert_eq!(ReferenceStr::new_checked("&#x3c;foo"), Err(ReferenceError::ExtraData(6)));
    /// assert_eq!(ReferenceStr::new_checked("&#x3C;foo"), Err(ReferenceError::ExtraData(6)));
    /// assert_eq!(ReferenceStr::new_checked(""), Err(ReferenceError::MissingAmpersand));
    /// assert_eq!(ReferenceStr::new_checked("foo"), Err(ReferenceError::MissingAmpersand));
    /// assert_eq!(ReferenceStr::new_checked("foo&bar;"), Err(ReferenceError::MissingAmpersand));
    /// assert_eq!(ReferenceStr::new_checked("&#zzz;"), Err(ReferenceError::MissingCharacterCode));
    /// assert_eq!(ReferenceStr::new_checked("&#xzzz;"), Err(ReferenceError::MissingCharacterCode));
    /// assert_eq!(ReferenceStr::new_checked("&"), Err(ReferenceError::MissingName));
    /// assert_eq!(ReferenceStr::new_checked("&;"), Err(ReferenceError::MissingName));
    /// assert_eq!(ReferenceStr::new_checked("& foo;"), Err(ReferenceError::MissingName));
    /// assert_eq!(ReferenceStr::new_checked("&foo"), Err(ReferenceError::MissingSemicolon));
    /// assert_eq!(ReferenceStr::new_checked("&a b;"), Err(ReferenceError::MissingSemicolon));
    /// assert_eq!(ReferenceStr::new_checked("&#6zzz;"), Err(ReferenceError::MissingSemicolon));
    /// assert_eq!(ReferenceStr::new_checked("&#xazzz;"), Err(ReferenceError::MissingSemicolon));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, ReferenceError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&ReferenceStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid reference.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::reference::ReferenceStr;
    /// let s = ReferenceStr::new("&valid-reference;");
    /// ```
    ///
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid reference: {}", e))
    }

    /// Creates a new `&ReferenceStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid reference content.
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for `Reference`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ReferenceString(Box<ReferenceStr>);

impl_string_types! {
    owned: ReferenceString,
    slice: ReferenceStr,
    error_slice: ReferenceError,
    parse: parse,
    slice_new_unchecked: ReferenceStr::new_unchecked,
}

impl_string_cmp! {
    owned: ReferenceString,
    slice: ReferenceStr,
}

impl_string_cmp_to_string! {
    owned: ReferenceString,
    slice: ReferenceStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{
        Complete, Extra, MissingAmpersand, MissingCharacterCode, MissingName, MissingSemicolon,
    };

    #[test]
    fn test_reference_parser() {
        assert_eq!(parse_raw("&lt;"), Complete(RefereneceType::Entity));
        assert_eq!(parse_raw("&#60;"), Complete(RefereneceType::Dec));
        assert_eq!(parse_raw("&#x3c;"), Complete(RefereneceType::Hex));
        assert_eq!(parse_raw("&#x3C;"), Complete(RefereneceType::Hex));

        assert_eq!(
            parse_raw("&lt;foo"),
            Extra(Partial::new(RefereneceType::Entity, 4))
        );
        assert_eq!(
            parse_raw("&#60;foo"),
            Extra(Partial::new(RefereneceType::Dec, 5))
        );
        assert_eq!(
            parse_raw("&#x3c;foo"),
            Extra(Partial::new(RefereneceType::Hex, 6))
        );
        assert_eq!(
            parse_raw("&#x3C;foo"),
            Extra(Partial::new(RefereneceType::Hex, 6))
        );

        assert_eq!(parse_raw(""), MissingAmpersand);
        assert_eq!(parse_raw("foo"), MissingAmpersand);
        assert_eq!(parse_raw("foo&bar;"), MissingAmpersand);
        assert_eq!(parse_raw("&#zzz;"), MissingCharacterCode);
        assert_eq!(parse_raw("&#xzzz;"), MissingCharacterCode);
        assert_eq!(parse_raw("&"), MissingName);
        assert_eq!(parse_raw("&;"), MissingName);
        assert_eq!(parse_raw("& foo;"), MissingName);
        assert_eq!(parse_raw("&foo"), MissingSemicolon);
        assert_eq!(parse_raw("&a b;"), MissingSemicolon);
        assert_eq!(parse_raw("&#6zzz;"), MissingSemicolon);
        assert_eq!(parse_raw("&#xazzz;"), MissingSemicolon);
    }
}
