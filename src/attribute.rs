//! String types for attributes of XML elements.

pub use self::value::{
    content::{
        apos::{AposAttributeContentStr, AposAttributeContentString},
        quot::{QuotAttributeContentStr, QuotAttributeContentString},
        AttributeContentError,
    },
    wrapping::{AttributeValueError, AttributeValueStr, AttributeValueString},
};

mod value;

/// Quote character of an attribute value.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum QuoteMark {
    /// Apostrophy (`'`).
    Apos,
    /// Quotation mark (`"`).
    Quot,
}

impl QuoteMark {
    /// Checks whether the given character is used as quote.
    fn is_quote(self, c: char) -> bool {
        (self == Self::Apos && c == '\'') || (self == Self::Quot && c == '"')
    }

    /// Creates a new `Quote` from the given ASCII character.
    fn from_ascii(c: u8) -> Option<Self> {
        match c {
            b'\'' => Some(Self::Apos),
            b'"' => Some(Self::Quot),
            _ => None,
        }
    }
}
