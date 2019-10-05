//! [`CDSect`] and its content ([`CData`]).
//!
//! [`CData`] is content inside a [CDATA section][`CDSect`].
//!
//! `CdataSectionStr` and `CdataSectionString` contains `CdataStr` and `CdataString` with wrapping
//! `<![CDATA[` and `]]>`.
//!
//! [`CData`]: http://www.w3.org/TR/REC-xml/#NT-CData
//! [`CDSect`]: https://www.w3.org/TR/xml/#NT-CDSect

pub use self::{
    content::{CdataError, CdataStr, CdataString},
    wrapping::{CdataSectionError, CdataSectionStr, CdataSectionString},
};

mod content;
pub(crate) mod wrapping;
