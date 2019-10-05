//! Entity reference.
//!
//! See [`EntityRef`] in the XML spec.
//!
//! [`EntityRef`]: https://www.w3.org/TR/REC-xml/#NT-EntityRef

use std::convert::TryFrom;

use crate::{
    name::plain::{parse_raw as parse_name, ParseResult as NameResult},
    parser::{Partial, PartialMapWithStr},
    reference::{ParseResult, ReferenceError},
};

/// Parses the given string as entity reference.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    if s.as_bytes().get(0) != Some(&b'&') {
        return ParseResult::MissingAmpersand;
    }
    // Expect `Name`.
    let semicolon_pos = match parse_name(&s[1..]) {
        NameResult::Complete(()) => return ParseResult::MissingSemicolon,
        NameResult::Empty | NameResult::InvalidCharacter(None) => return ParseResult::MissingName,
        NameResult::InvalidCharacter(Some(part)) => part.valid_up_to() + 1,
    };
    if s.as_bytes()[semicolon_pos] != b';' {
        return ParseResult::MissingSemicolon;
    }
    if semicolon_pos != s.len() - 1 {
        return ParseResult::Extra(Partial::new((), semicolon_pos + 1));
    }

    ParseResult::Complete(())
}

/// Parses the given string as `EntityRef`.
fn parse(s: &str) -> ParseResult<&EntityRefStr> {
    match parse_raw(s) {
        ParseResult::Complete(_) => {
            ParseResult::Complete(unsafe { EntityRefStr::new_unchecked(s) })
        }
        ParseResult::Extra(part) => ParseResult::Extra(
            part.map_with_str(s, |_, s| unsafe { EntityRefStr::new_unchecked(s) }),
        ),
        ParseResult::InvalidCharacterReference => ParseResult::InvalidCharacterReference,
        ParseResult::MissingAmpersand => ParseResult::MissingAmpersand,
        ParseResult::MissingCharacterCode => {
            unreachable!("Should never happen: parsing entity reference")
        }
        ParseResult::MissingName => ParseResult::MissingName,
        ParseResult::MissingSemicolon => ParseResult::MissingSemicolon,
    }
}

/// String slice for `EntityRef`.
///
/// See module documentation for detail.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct EntityRefStr(str);

impl EntityRefStr {
    /// Creates a new `&EntityRef` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::reference::{EntityRefStr, ReferenceError};
    /// assert!(EntityRefStr::new_checked("&lt;").is_ok());
    /// assert!(EntityRefStr::new_checked("&valid-reference;").is_ok());
    ///
    /// assert_eq!(EntityRefStr::new_checked("&#60;"), Err(ReferenceError::MissingName));
    /// assert_eq!(EntityRefStr::new_checked("&#x3c;"), Err(ReferenceError::MissingName));
    /// assert_eq!(EntityRefStr::new_checked("&#x3C;"), Err(ReferenceError::MissingName));
    /// assert_eq!(EntityRefStr::new_checked("&#xEFFFF;"), Err(ReferenceError::MissingName));
    ///
    /// assert_eq!(EntityRefStr::new_checked("&lt;foo"), Err(ReferenceError::ExtraData(4)));
    /// assert_eq!(EntityRefStr::new_checked(""), Err(ReferenceError::MissingAmpersand));
    /// assert_eq!(EntityRefStr::new_checked("foo"), Err(ReferenceError::MissingAmpersand));
    /// assert_eq!(EntityRefStr::new_checked("foo&bar;"), Err(ReferenceError::MissingAmpersand));
    /// assert_eq!(EntityRefStr::new_checked("&"), Err(ReferenceError::MissingName));
    /// assert_eq!(EntityRefStr::new_checked("&;"), Err(ReferenceError::MissingName));
    /// assert_eq!(EntityRefStr::new_checked("& foo;"), Err(ReferenceError::MissingName));
    /// assert_eq!(EntityRefStr::new_checked("&#6zzz;"), Err(ReferenceError::MissingName));
    /// assert_eq!(EntityRefStr::new_checked("&#xazzz;"), Err(ReferenceError::MissingName));
    /// assert_eq!(EntityRefStr::new_checked("&foo"), Err(ReferenceError::MissingSemicolon));
    /// assert_eq!(EntityRefStr::new_checked("&a b;"), Err(ReferenceError::MissingSemicolon));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, ReferenceError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&EntityRefStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid entity reference.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::reference::EntityRefStr;
    /// let s = EntityRefStr::new("&valid-reference;");
    /// ```
    ///
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid reference: {}", e))
    }

    /// Creates a new `&EntityRefStr` without validation.
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

/// Owned string for `EntityRef`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct EntityRefString(Box<EntityRefStr>);

impl_string_types! {
    owned: EntityRefString,
    slice: EntityRefStr,
    error_slice: ReferenceError,
    parse: parse,
    slice_new_unchecked: EntityRefStr::new_unchecked,
}

impl_string_cmp! {
    owned: EntityRefString,
    slice: EntityRefStr,
}

impl_string_cmp_to_string! {
    owned: EntityRefString,
    slice: EntityRefStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{Complete, Extra, MissingAmpersand, MissingName, MissingSemicolon};

    #[test]
    fn test_reference_parser() {
        assert_eq!(parse_raw("&lt;"), Complete(()));
        assert_eq!(parse_raw("&entity-reference;"), Complete(()));

        assert_eq!(parse_raw("&#60;"), MissingName);
        assert_eq!(parse_raw("&#x3c;"), MissingName);
        assert_eq!(parse_raw("&#x3C;"), MissingName);

        assert_eq!(parse_raw("&lt;foo"), Extra(Partial::new((), 4)));

        assert_eq!(parse_raw(""), MissingAmpersand);
        assert_eq!(parse_raw("foo"), MissingAmpersand);
        assert_eq!(parse_raw("foo&bar;"), MissingAmpersand);
        assert_eq!(parse_raw("&"), MissingName);
        assert_eq!(parse_raw("&;"), MissingName);
        assert_eq!(parse_raw("& foo;"), MissingName);
        assert_eq!(parse_raw("&#zzz;"), MissingName);
        assert_eq!(parse_raw("&#xzzz;"), MissingName);
        assert_eq!(parse_raw("&#6zzz;"), MissingName);
        assert_eq!(parse_raw("&#xazzz;"), MissingName);
        assert_eq!(parse_raw("&foo"), MissingSemicolon);
        assert_eq!(parse_raw("&a b;"), MissingSemicolon);
    }
}
