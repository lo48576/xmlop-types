//! Entity reference and character reference.
//!
//! See <https://www.w3.org/TR/REC-xml/#NT-Reference>.

use crate::{
    name::{self, ParseResult as NameResult},
    parser::Partial,
};

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
