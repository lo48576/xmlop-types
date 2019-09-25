//! Entity reference.
//!
//! See [`CharRef`] in the XML spec.
//!
//! [`CharRef`]: https://www.w3.org/TR/REC-xml/#NT-CharRef

use std::convert::TryFrom;

use crate::{
    parser::{Partial, PartialMapWithStr},
    reference::{is_xml_char_code_ref, ParseResult, ReferenceError},
};

/// Parses the given string as character reference.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    /// Offset of decimal character code.
    ///
    /// 2: `"&#".len()`.
    const DEC_OFFSET: usize = 2;
    /// Offset of hexadecimal character code.
    ///
    /// 3: `"&#x".len()`.
    const HEX_OFFSET: usize = 3;

    if s.as_bytes().get(0) != Some(&b'&') {
        return ParseResult::MissingAmpersand;
    }
    if s.as_bytes().get(1) != Some(&b'#') {
        return ParseResult::MissingCharacterCode;
    }
    // Expect character code.
    let semicolon_pos = match s.as_bytes().get(2) {
        Some(b'x') => match s[HEX_OFFSET..]
            .as_bytes()
            .iter()
            .position(|c| !c.is_ascii_hexdigit())
        {
            Some(0) => return ParseResult::MissingCharacterCode,
            Some(i) if s.as_bytes()[HEX_OFFSET + i] != b';' => {
                return ParseResult::MissingSemicolon
            }
            Some(i) => HEX_OFFSET + i,
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
            Some(i) => DEC_OFFSET + i,
            None if s.len() == DEC_OFFSET => return ParseResult::MissingCharacterCode,
            None => return ParseResult::MissingSemicolon,
        },
        None => return ParseResult::MissingCharacterCode,
    };
    if s.as_bytes()[semicolon_pos] != b';' {
        return ParseResult::MissingSemicolon;
    }
    if semicolon_pos != s.len() - 1 {
        return ParseResult::Extra(Partial::new((), semicolon_pos + 1));
    }

    // Check if the referred character code is valid XML `Char`.
    if !is_xml_char_code_ref(s) {
        return ParseResult::InvalidCharacterReference;
    }

    ParseResult::Complete(())
}

/// Parses the given string as `CharRef`.
fn parse(s: &str) -> ParseResult<&CharRefStr> {
    match parse_raw(s) {
        ParseResult::Complete(_) => ParseResult::Complete(unsafe { CharRefStr::new_unchecked(s) }),
        ParseResult::Extra(part) => {
            ParseResult::Extra(part.map_with_str(s, |_, s| unsafe { CharRefStr::new_unchecked(s) }))
        }
        ParseResult::InvalidCharacterReference => ParseResult::InvalidCharacterReference,
        ParseResult::MissingAmpersand => ParseResult::MissingAmpersand,
        ParseResult::MissingCharacterCode => ParseResult::MissingCharacterCode,
        ParseResult::MissingName => {
            unreachable!("Should never happen: parsing character reference")
        }
        ParseResult::MissingSemicolon => ParseResult::MissingSemicolon,
    }
}

/// String slice for `CharRef`.
///
/// See module documentation for detail.
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CharRefStr(str);

impl CharRefStr {
    /// Creates a new `&CharRef` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::reference::{CharRefStr, ReferenceError};
    /// assert!(CharRefStr::new_checked("&#60;").is_ok());
    /// assert!(CharRefStr::new_checked("&#x3c;").is_ok());
    /// assert!(CharRefStr::new_checked("&#x3C;").is_ok());
    /// assert!(CharRefStr::new_checked("&#xEFFFF;").is_ok());
    ///
    /// assert_eq!(CharRefStr::new_checked("&lt;"), Err(ReferenceError::MissingCharacterCode));
    /// assert_eq!(
    ///     CharRefStr::new_checked("&valid-reference;"),
    ///     Err(ReferenceError::MissingCharacterCode)
    /// );
    ///
    /// assert_eq!(CharRefStr::new_checked("&#60;foo"), Err(ReferenceError::ExtraData(5)));
    /// assert_eq!(
    ///     CharRefStr::new_checked("&#11;"),
    ///     Err(ReferenceError::InvalidCharacterReference)
    /// );
    /// assert_eq!(
    ///     CharRefStr::new_checked("&#xB;"),
    ///     Err(ReferenceError::InvalidCharacterReference)
    /// );
    /// assert_eq!(
    ///     CharRefStr::new_checked("&#xFFFFFFFFFFFF;"),
    ///     Err(ReferenceError::InvalidCharacterReference)
    /// );
    /// assert_eq!(CharRefStr::new_checked(""), Err(ReferenceError::MissingAmpersand));
    /// assert_eq!(CharRefStr::new_checked("foo"), Err(ReferenceError::MissingAmpersand));
    /// assert_eq!(CharRefStr::new_checked("foo&#60;"), Err(ReferenceError::MissingAmpersand));
    /// assert_eq!(CharRefStr::new_checked("&"), Err(ReferenceError::MissingCharacterCode));
    /// assert_eq!(CharRefStr::new_checked("&;"), Err(ReferenceError::MissingCharacterCode));
    /// assert_eq!(CharRefStr::new_checked("&#6zzz;"), Err(ReferenceError::MissingSemicolon));
    /// assert_eq!(CharRefStr::new_checked("&#xazzz;"), Err(ReferenceError::MissingSemicolon));
    /// assert_eq!(CharRefStr::new_checked("&#60"), Err(ReferenceError::MissingSemicolon));
    /// assert_eq!(CharRefStr::new_checked("&#60 0;"), Err(ReferenceError::MissingSemicolon));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, ReferenceError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&CharRefStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid entity reference.
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::reference::CharRefStr;
    /// let s0 = CharRefStr::new("&#60;");
    /// let s1 = CharRefStr::new("&#x3c;");
    /// let s2 = CharRefStr::new("&#x3C;");
    /// ```
    ///
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid reference: {}", e))
    }

    /// Creates a new `&CharRefStr` without validation.
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

/// Owned string for `CharRef`.
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CharRefString(Box<CharRefStr>);

impl_string_types! {
    owned: CharRefString,
    slice: CharRefStr,
    error_slice: ReferenceError,
    parse: parse,
    slice_new_unchecked: CharRefStr::new_unchecked,
}

impl_string_cmp! {
    owned: CharRefString,
    slice: CharRefStr,
}

impl_string_cmp_to_string! {
    owned: CharRefString,
    slice: CharRefStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{
        Complete, Extra, InvalidCharacterReference, MissingAmpersand, MissingCharacterCode,
        MissingSemicolon,
    };

    #[test]
    fn test_reference_parser() {
        assert_eq!(parse_raw("&#60;"), Complete(()));
        assert_eq!(parse_raw("&#x3c;"), Complete(()));
        assert_eq!(parse_raw("&#x3C;"), Complete(()));

        assert_eq!(parse_raw("&#60;foo"), Extra(Partial::new((), 5)));
        assert_eq!(parse_raw("&#x3c;foo"), Extra(Partial::new((), 6)));
        assert_eq!(parse_raw("&#x3C;foo"), Extra(Partial::new((), 6)));

        assert_eq!(parse_raw("&lt;"), MissingCharacterCode);

        assert_eq!(parse_raw("&#11;"), InvalidCharacterReference);
        assert_eq!(parse_raw("&#xB;"), InvalidCharacterReference);
        assert_eq!(parse_raw("&#xFFFFFFFFFFFF;"), InvalidCharacterReference);
        assert_eq!(parse_raw(""), MissingAmpersand);
        assert_eq!(parse_raw("foo"), MissingAmpersand);
        assert_eq!(parse_raw("foo&bar;"), MissingAmpersand);
        assert_eq!(parse_raw("&#zzz;"), MissingCharacterCode);
        assert_eq!(parse_raw("&#xzzz;"), MissingCharacterCode);
        assert_eq!(parse_raw("&"), MissingCharacterCode);
        assert_eq!(parse_raw("&;"), MissingCharacterCode);
        assert_eq!(parse_raw("& foo;"), MissingCharacterCode);
        assert_eq!(parse_raw("&foo"), MissingCharacterCode);
        assert_eq!(parse_raw("&a b;"), MissingCharacterCode);
        assert_eq!(parse_raw("&#6zzz;"), MissingSemicolon);
        assert_eq!(parse_raw("&#xazzz;"), MissingSemicolon);
    }
}
