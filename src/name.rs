//! XML name types.
//!
//! About `Name`, see [Extensible Markup Language (XML) 1.0 (Fifth Edition)][`Name`].
//!
//! [`Name`]: http://www.w3.org/TR/REC-xml/#NT-Name

pub use self::{
    ncname::{NcnameError, NcnameStr, NcnameString},
    plain::{NameError, NameStr, NameString},
    qname::{QnameError, QnameStr, QnameString},
};

pub(crate) mod ncname;
pub(crate) mod plain;
mod qname;
