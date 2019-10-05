//! Content of [`Comment`].
//!
//! For example, content of `<!--abc-->` is `abc`.
//!
//! [`Comment`]: https://www.w3.org/TR/xml/#NT-Comment

use std::{convert::TryFrom, error, fmt};

use crate::parser::{chars::is_xml_char, Partial, PartialMapWithStr};

/// Parse result of `CommentContent`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub(crate) enum ParseResult<T> {
    /// Completely parsed.
    Complete(T),
    /// Double hyphen.
    DoubleHyphen(Partial<T>),
    /// Invalid character.
    InvalidCharacter(Partial<T>),
    /// Trailing hyphen.
    TrailingHyphen(Partial<T>),
}

impl<T> ParseResult<T> {
    /// Returns the `Result` regarding only `Complete` as success.
    fn into_complete_result(self) -> Result<T, CommentContentError> {
        match self {
            Self::Complete(v) => Ok(v),
            Self::DoubleHyphen(part) => Err(CommentContentError::DoubleHyphen(part.valid_up_to())),
            Self::InvalidCharacter(part) => {
                Err(CommentContentError::InvalidCharacter(part.valid_up_to()))
            }
            Self::TrailingHyphen(part) => {
                Err(CommentContentError::TrailingHyphen(part.valid_up_to()))
            }
        }
    }
}

/// Parses the given string as `CommentContent`.
pub(crate) fn parse_raw(s: &str) -> ParseResult<()> {
    if s.is_empty() {
        return ParseResult::Complete(());
    }

    let len = s.len();
    assert!(len > 0);
    let mut rest = s;
    let mut prev_hyphen = None;
    while let Some((rest_pos, c)) = rest
        .char_indices()
        .find(|&(_, c)| c == '-' || !is_xml_char(c))
    {
        let pos = len - rest.len() + rest_pos;
        match c {
            '-' => {
                if pos > 0 && prev_hyphen == Some(pos - 1) {
                    return ParseResult::DoubleHyphen(Partial::new((), pos - 1));
                }
                prev_hyphen = Some(pos);
                rest = &rest[(rest_pos + 1)..];
            }
            _c => {
                debug_assert!(!is_xml_char(_c));
                return ParseResult::InvalidCharacter(Partial::new((), pos));
            }
        }
    }

    // This is safe because `len > 0`.
    let len_1 = len - 1;
    if s.as_bytes().get(len_1) == Some(&b'-') {
        return ParseResult::TrailingHyphen(Partial::new((), len_1));
    }

    ParseResult::Complete(())
}

/// Parses the given string as `CommentContent`.
fn parse(s: &str) -> ParseResult<&CommentContentStr> {
    match parse_raw(s) {
        ParseResult::Complete(()) => {
            ParseResult::Complete(unsafe { CommentContentStr::new_unchecked(s) })
        }
        ParseResult::DoubleHyphen(part) => ParseResult::DoubleHyphen(
            part.map_with_str(s, |_, s| unsafe { CommentContentStr::new_unchecked(s) }),
        ),
        ParseResult::InvalidCharacter(part) => ParseResult::InvalidCharacter(
            part.map_with_str(s, |_, s| unsafe { CommentContentStr::new_unchecked(s) }),
        ),
        ParseResult::TrailingHyphen(part) => ParseResult::TrailingHyphen(
            part.map_with_str(s, |_, s| unsafe { CommentContentStr::new_unchecked(s) }),
        ),
    }
}

/// Error for content of `Comment`.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub enum CommentContentError {
    /// Found double hyphen.
    ///
    /// `usize` field is the starting byte position of the double hyphen.
    DoubleHyphen(usize),
    /// Found invalid character.
    ///
    /// `usize` field is the first byte position of the invalid character.
    InvalidCharacter(usize),
    /// Trailing hyphen.
    ///
    /// `usize` field is the byte position of the first hyphen.
    TrailingHyphen(usize),
}

impl error::Error for CommentContentError {}

impl fmt::Display for CommentContentError {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            CommentContentError::DoubleHyphen(pos) => write!(f, "Double hyphen at index {}", pos),
            CommentContentError::InvalidCharacter(pos) => {
                write!(f, "Invalid character at index {}", pos)
            }
            CommentContentError::TrailingHyphen(pos) => {
                write!(f, "Trailing hyphen at index {}", pos)
            }
        }
    }
}

/// String slice for content of [`Comment`].
///
/// [`Comment`]: http://www.w3.org/TR/REC-xml/#NT-Comment
#[derive(Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[repr(transparent)]
pub struct CommentContentStr(str);

impl CommentContentStr {
    /// Creates a new `&CommentContentStr` if the given string is valid.
    ///
    /// ```
    /// # use xmlop_types::comment::{CommentContentError, CommentContentStr};
    /// assert!(CommentContentStr::new_checked("Valid Comment content").is_ok());
    /// assert!(CommentContentStr::new_checked("").is_ok());
    /// assert!(CommentContentStr::new_checked("<foo> & <bar>").is_ok());
    /// assert!(CommentContentStr::new_checked("foo-bar").is_ok());
    ///
    /// assert_eq!(
    ///     CommentContentStr::new_checked("--"),
    ///     Err(CommentContentError::DoubleHyphen(0))
    /// );
    /// assert_eq!(
    ///     CommentContentStr::new_checked("foo--bar"),
    ///     Err(CommentContentError::DoubleHyphen(3))
    /// );
    /// assert_eq!(
    ///     CommentContentStr::new_checked("---"),
    ///     Err(CommentContentError::DoubleHyphen(0))
    /// );
    /// assert_eq!(
    ///     CommentContentStr::new_checked("-"),
    ///     Err(CommentContentError::TrailingHyphen(0))
    /// );
    /// assert_eq!(
    ///     CommentContentStr::new_checked("foo-"),
    ///     Err(CommentContentError::TrailingHyphen(3))
    /// );
    /// ```
    pub fn new_checked(s: &str) -> Result<&Self, CommentContentError> {
        <&Self>::try_from(s)
    }

    /// Creates a new `&CommentContentStr` assuming the given string is valid.
    ///
    /// # Panics
    ///
    /// This panics if the given string is not valid content of [`Comment`].
    /// If you are not sure the string is valid, you should use [`new_checked()`].
    ///
    /// # Examples
    ///
    /// ```
    /// # use xmlop_types::comment::CommentContentStr;
    /// let s = CommentContentStr::new("valid `Comment` content");
    /// ```
    ///
    /// [`Comment`]: http://www.w3.org/TR/REC-xml/#NT-Comment
    /// [`new_checked()`]: #method.new_checked
    pub fn new(s: &str) -> &Self {
        <&Self>::try_from(s)
            .unwrap_or_else(|e| panic!("The given string is not valid `Comment` content: {}", e))
    }

    /// Creates a new `&CommentContentStr` without validation.
    ///
    /// # Safety
    ///
    /// The given string should be valid [`Comment`] content.
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

/// Owned string for [`Comment`] content.
///
/// [`Comment`]: http://www.w3.org/TR/REC-xml/#NT-Comment
#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct CommentContentString(Box<CommentContentStr>);

impl_string_types! {
    owned: CommentContentString,
    slice: CommentContentStr,
    error_slice: CommentContentError,
    parse: parse,
    slice_new_unchecked: CommentContentStr::new_unchecked,
}

impl_string_cmp! {
    owned: CommentContentString,
    slice: CommentContentStr,
}

impl_string_cmp_to_string! {
    owned: CommentContentString,
    slice: CommentContentStr,
}

#[cfg(test)]
mod tests {
    use super::*;

    use ParseResult::{Complete, DoubleHyphen, InvalidCharacter, TrailingHyphen};

    #[test]
    fn test_parser() {
        assert_eq!(parse_raw(""), Complete(()));
        assert_eq!(parse_raw("valid Comment content"), Complete(()));
        assert_eq!(parse_raw("<foo> & <bar>"), Complete(()));
        assert_eq!(parse_raw("foo-bar"), Complete(()));

        assert_eq!(parse_raw("--"), DoubleHyphen(Partial::new((), 0)));
        assert_eq!(parse_raw("foo--bar"), DoubleHyphen(Partial::new((), 3)));
        assert_eq!(parse_raw("---"), DoubleHyphen(Partial::new((), 0)));
        assert_eq!(
            parse_raw("foo\u{B}bar"),
            InvalidCharacter(Partial::new((), 3))
        );
        assert_eq!(parse_raw("-"), TrailingHyphen(Partial::new((), 0)));
        assert_eq!(parse_raw("foo-"), TrailingHyphen(Partial::new((), 3)));
    }
}
