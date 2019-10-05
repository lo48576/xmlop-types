//! String types for [`Comment`] including wrapping `<!--` and `-->`.
//!
//! [`Comment`]: https://www.w3.org/TR/xml/#NT-Comment

use std::{convert::TryFrom, error, fmt};

use crate::{
    comment::content::{parse_raw as parse_content, ParseResult as ContentResult},
    parser::{Partial, PartialMapWithStr},
};

/// Parse result of `Comment`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Extra data follows.
    Extra(Partial<T>),
    /// Double hyphen in content part.
    ///
    /// `usize` field is the starting byte position of the double hyphen.
    DoubleHyphen(usize),
    /// Invalid character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
    /// Missing closing `-->`.
    MissingClosing,
    /// Missing opening `<!--`.
    MissingOpening,
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, CommentError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::Extra(part) => Err(CommentError::ExtraData(part.valid_up_to())),
            Self::DoubleHyphen(pos) => Err(CommentError::DoubleHyphen(pos)),
            Self::InvalidCharacter(pos) => Err(CommentError::InvalidCharacter(pos)),
            Self::MissingClosing => Err(CommentError::MissingClosing),
            Self::MissingOpening => Err(CommentError::MissingOpening),
        }
    }
}

/// Parses the given string as `Comment`.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    /// Comment opening.
    const COMMENT_OPEN: &str = "<!--";
    /// Length of the comment opening.
    const COMMENT_OPEN_LEN: usize = 4;

    if !s.starts_with(COMMENT_OPEN) {
        return ParseResult::MissingOpening;
    }
    match parse_content(&s[COMMENT_OPEN_LEN..]) {
        ContentResult::Complete(_) | ContentResult::TrailingHyphen(_) => {
            ParseResult::MissingClosing
        }
        ContentResult::DoubleHyphen(part) => {
            let double_hyphen_pos = COMMENT_OPEN_LEN + dbg!(part.valid_up_to());
            // 2: `"--".len()`.
            let rest = &s[(double_hyphen_pos + 2)..];
            if rest.as_bytes().get(0) != Some(&b'>') {
                return ParseResult::DoubleHyphen(double_hyphen_pos);
            }
            if rest.len() == 1 {
                ParseResult::Complete(())
            } else {
                // 3: `"-->".len()`.
                ParseResult::Extra(Partial::new((), double_hyphen_pos + 3))
            }
        }
        ContentResult::InvalidCharacter(part) => {
            ParseResult::InvalidCharacter(COMMENT_OPEN_LEN + part.valid_up_to())
        }
    }
}

/// Parses the given string as `Comment`.
fn parse(s: &str) -> ParseResult<&CommentStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => ParseResult::Complete(unsafe { CommentStr::new_unchecked(s) }),
        ParseResult::Extra(part) => {
            ParseResult::Extra(part.map_with_str(s, |_, s| unsafe { CommentStr::new_unchecked(s) }))
        }
        ParseResult::DoubleHyphen(pos) => ParseResult::DoubleHyphen(pos),
        ParseResult::InvalidCharacter(pos) => ParseResult::InvalidCharacter(pos),
        ParseResult::MissingClosing => ParseResult::MissingClosing,
        ParseResult::MissingOpening => ParseResult::MissingOpening,
    }
}

/// Error for `Comment`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CommentError {
    /// Found double hyphen.
    ///
    /// `usize` field is the byte position of the first hyphen.
    DoubleHyphen(usize),
    /// Extra data follows.
    ///
    /// `usize` field is the first byte position of the extra data after `]]>`.
    ExtraData(usize),
    /// Found invalid character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
    /// Missing closing `-->`.
    MissingClosing,
    /// Missing opening `<!--`.
    MissingOpening,
    /// Trailing hyphen.
    ///
    /// `usize` field is the byte position of the first hyphen.
    TrailingHyphen(usize),
}

impl error::Error for CommentError {}

impl fmt::Display for CommentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommentError::DoubleHyphen(pos) => write!(f, "Double hyphen at index {}", pos),
            CommentError::ExtraData(pos) => write!(f, "Extra following data at index {}", pos),
            CommentError::InvalidCharacter(pos) => write!(f, "Invalid character at index {}", pos),
            CommentError::MissingClosing => f.write_str("Missing comment closing"),
            CommentError::MissingOpening => f.write_str("Missing comment opening"),
            CommentError::TrailingHyphen(pos) => write!(f, "Trailing hyphen at index {}", pos),
        }
    }
}

/// String slice for content of [`Comment`].
///
/// [`Comment`]: http://www.w3.org/TR/REC-xml/#NT-Comment
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CommentStr(str);

impl CommentStr {
    /// Creates a new `&CommentStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::comment::{CommentError, CommentStr};
    /// assert!(CommentStr::new_checked("<!--Valid Comment-->").is_ok());
    /// assert!(CommentStr::new_checked("<!---->").is_ok());
    /// assert!(CommentStr::new_checked("<!--<foo> & <bar>-->").is_ok());
    /// assert!(CommentStr::new_checked("<!--foo-bar-->").is_ok());
    ///
    /// assert_eq!(CommentStr::new_checked("<!----->"), Err(CommentError::DoubleHyphen(4)));
    /// assert_eq!(CommentStr::new_checked("<!------>"), Err(CommentError::DoubleHyphen(4)));
    /// assert_eq!(
    ///     CommentStr::new_checked("<!--foo--bar-->"),
    ///     Err(CommentError::DoubleHyphen(7))
    /// );
    /// assert_eq!(CommentStr::new_checked("<!--foo"), Err(CommentError::MissingClosing));
    /// assert_eq!(CommentStr::new_checked(""), Err(CommentError::MissingOpening));
    /// assert_eq!(CommentStr::new_checked("foo"), Err(CommentError::MissingOpening));
    /// assert_eq!(CommentStr::new_checked("foo<!--"), Err(CommentError::MissingOpening));
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, CommentError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&CommentStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid [`Comment`].
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::comment::CommentStr;
    /// let s = CommentStr::new("<!--valid `Comment`-->");
    /// ```
    ///
    /// [`Comment`]: http://www.w3.org/TR/REC-xml/#NT-Comment
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `Comment`: {}", e))
    }

    /// Creates a new `&CommentStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`Comment`].
    ///
    /// [`Comment`]: http://www.w3.org/TR/REC-xml/#NT-Comment
    pub unsafe fn new_unchecked(s: &str) -> &Self {
        &*(s as *const str as *const Self)
    }

    /// Returns the string slice.
    pub fn as_str(&self) -> &str {
        self.as_ref()
    }
}

/// Owned string for [`Comment`].
///
/// [`Comment`]: http://www.w3.org/TR/REC-xml/#NT-Comment
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CommentString(Box<CommentStr>);

impl_string_types! {
    owned: CommentString,
    slice: CommentStr,
    error_slice: CommentError,
    parse: parse,
    slice_new_unchecked: CommentStr::new_unchecked,
}

impl_string_cmp! {
    owned: CommentString,
    slice: CommentStr,
}

impl_string_cmp_to_string! {
    owned: CommentString,
    slice: CommentStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{
        Complete, DoubleHyphen, Extra, InvalidCharacter, MissingClosing, MissingOpening,
    };

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw("<!--valid Comment-->"), Complete(()));
        assert_eq!(parse_raw("<!--<foo> & <bar>-->"), Complete(()));
        assert_eq!(parse_raw("<!--foo-bar-->"), Complete(()));
        assert_eq!(parse_raw("<!---->"), Complete(()));
        assert_eq!(parse_raw("<!---->foo"), Extra(Partial::new((), 7)));
        assert_eq!(parse_raw("<!--foo-->bar"), Extra(Partial::new((), 10)));

        assert_eq!(parse_raw("<!----->"), DoubleHyphen(4));
        assert_eq!(parse_raw("<!------>"), DoubleHyphen(4));
        assert_eq!(parse_raw("<!------->"), DoubleHyphen(4));
        assert_eq!(parse_raw("<!--foo--bar-->"), DoubleHyphen(7));
        assert_eq!(parse_raw("<!--\u{B}-->"), InvalidCharacter(4));
        assert_eq!(parse_raw("<!--"), MissingClosing);
        assert_eq!(parse_raw("<!--foo"), MissingClosing);
        assert_eq!(parse_raw(""), MissingOpening);
        assert_eq!(parse_raw("foo"), MissingOpening);
        assert_eq!(parse_raw("foo<!--"), MissingOpening);
    }
}
