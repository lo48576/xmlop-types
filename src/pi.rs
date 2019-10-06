//! Processing instructions.
//!
//! See [Extensible Markup Language (XML) 1.0 (Fifth Edition)][pi].
//!
//! [pi]: https://www.w3.org/TR/xml/#sec-pi

pub use self::{
    body::{PiBodyError, PiBodyStr, PiBodyString},
    target::{PiTargetError, PiTargetStr, PiTargetString},
};

mod body;
mod target;
