//! Types common for XML processing.
//!
//! References:
//!
//! * [Extensible Markup Language (XML) 1.0 (Fifth Edition)][XML10]
//! * [Namespaces in XML 1.0 (Third Edition)][XML-NAMES10]
//!
//! [XML10]: http://www.w3.org/TR/2008/REC-xml-20081126/
//! [XML-NAMES10]: http://www.w3.org/TR/2009/REC-xml-names-20091208/
#![warn(missing_docs)]
#![warn(clippy::missing_docs_in_private_items)]

#[macro_use]
mod macros;

pub mod attribute;
pub mod cdata_section;
pub mod char_data;
pub mod comment;
pub mod error;
pub mod name;
pub(crate) mod parser;
pub mod reference;
pub mod text_content;
pub mod text_node;
