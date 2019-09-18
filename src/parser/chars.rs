//! Common utilities not to be exported outside of the crate.

/// Checks if the given character is [`Char`].
///
/// [`Char`]: https://www.w3.org/TR/xml/#NT-Char
pub(crate) fn is_xml_char(c: char) -> bool {
    match c {
        '\u{9}'
        | '\u{A}'
        | '\u{D}'
        | '\u{20}'..='\u{D7FF}'
        | '\u{E000}'..='\u{FFFD}'
        | '\u{10000}'..='\u{10FFFF}' => true,
        _ => false,
    }
}

/// Checks if the given character is [`NameChar`] but not a colon (`:`).
///
/// [`NameChar`]: https://www.w3.org/TR/xml/#NT-NameChar
pub(crate) fn is_name_char_except_colon(c: char) -> bool {
    match c {
        '-'
        | '.'
        | '0'..='9'
        | 'A'..='Z'
        | '_'
        | 'a'..='z'
        | '\u{B7}'
        | '\u{C0}'..='\u{D6}'
        | '\u{D8}'..='\u{F6}'
        | '\u{F8}'..='\u{37D}'
        | '\u{37F}'..='\u{1FFF}'
        | '\u{200C}'..='\u{200D}'
        | '\u{203F}'..='\u{2040}'
        | '\u{2070}'..='\u{218F}'
        | '\u{2C00}'..='\u{2FEF}'
        | '\u{3001}'..='\u{D7FF}'
        | '\u{F900}'..='\u{FDCF}'
        | '\u{FDF0}'..='\u{FFFD}'
        | '\u{10000}'..='\u{EFFFF}' => true,
        _ => false,
    }
}

/// Checks if the given character is [`NameChar`].
///
/// [`NameChar`]: https://www.w3.org/TR/xml/#NT-NameChar
pub(crate) fn is_name_char(c: char) -> bool {
    match c {
        '-'
        | '.'
        | '0'..='9'
        | ':'
        | 'A'..='Z'
        | '_'
        | 'a'..='z'
        | '\u{B7}'
        | '\u{C0}'..='\u{D6}'
        | '\u{D8}'..='\u{F6}'
        | '\u{F8}'..='\u{37D}'
        | '\u{37F}'..='\u{1FFF}'
        | '\u{200C}'..='\u{200D}'
        | '\u{203F}'..='\u{2040}'
        | '\u{2070}'..='\u{218F}'
        | '\u{2C00}'..='\u{2FEF}'
        | '\u{3001}'..='\u{D7FF}'
        | '\u{F900}'..='\u{FDCF}'
        | '\u{FDF0}'..='\u{FFFD}'
        | '\u{10000}'..='\u{EFFFF}' => true,
        _ => false,
    }
}

/// Checks if the given character is [`NameStartChar`] but not a colon (`:`).
///
/// [`NameChar`]: https://www.w3.org/TR/xml/#NT-NameChar
pub(crate) fn is_name_start_char_except_colon(c: char) -> bool {
    match c {
        'A'..='Z'
        | '_'
        | 'a'..='z'
        | '\u{C0}'..='\u{D6}'
        | '\u{D8}'..='\u{F6}'
        | '\u{F8}'..='\u{2FF}'
        | '\u{370}'..='\u{37D}'
        | '\u{37F}'..='\u{1FFF}'
        | '\u{200C}'..='\u{200D}'
        | '\u{2070}'..='\u{218F}'
        | '\u{2C00}'..='\u{2FEF}'
        | '\u{3001}'..='\u{D7FF}'
        | '\u{F900}'..='\u{FDCF}'
        | '\u{FDF0}'..='\u{FFFD}'
        | '\u{10000}'..='\u{EFFFF}' => true,
        _ => false,
    }
}

/// Checks if the given character is [`NameStartChar`].
///
/// [`NameStartChar`]: https://www.w3.org/TR/xml/#NT-NameStartChar
pub(crate) fn is_name_start_char(c: char) -> bool {
    match c {
        ':'
        | 'A'..='Z'
        | '_'
        | 'a'..='z'
        | '\u{C0}'..='\u{D6}'
        | '\u{D8}'..='\u{F6}'
        | '\u{F8}'..='\u{2FF}'
        | '\u{370}'..='\u{37D}'
        | '\u{37F}'..='\u{1FFF}'
        | '\u{200C}'..='\u{200D}'
        | '\u{2070}'..='\u{218F}'
        | '\u{2C00}'..='\u{2FEF}'
        | '\u{3001}'..='\u{D7FF}'
        | '\u{F900}'..='\u{FDCF}'
        | '\u{FDF0}'..='\u{FFFD}'
        | '\u{10000}'..='\u{EFFFF}' => true,
        _ => false,
    }
}
