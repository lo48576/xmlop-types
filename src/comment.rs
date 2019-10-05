//! [`Comment`] and its content.
//!
//! [`Comment`]: https://www.w3.org/TR/xml/#NT-Comment

pub use self::{
    content::{CommentContentError, CommentContentStr, CommentContentString},
    wrapping::{CommentError, CommentStr, CommentString},
};

mod content;
mod wrapping;
