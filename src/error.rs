//! Error types.

use std::{error, fmt};

/// Error and value of its cause.
#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct ErrorWithValue<E, T> {
    /// Error.
    error: E,
    /// Value.
    value: T,
}

impl<E, T> ErrorWithValue<E, T> {
    /// Creates a new error.
    pub(crate) fn new(error: E, value: T) -> Self {
        Self { error, value }
    }

    /// Returns a reference to the value not converted.
    pub fn as_value(&self) -> &T {
        &self.value
    }

    /// Returns the value not converted.
    pub fn into_value(self) -> T {
        self.value
    }

    /// Deconstructs the error.
    pub fn deconstruct(self) -> (E, T) {
        (self.error, self.value)
    }
}

impl<E: Clone, T> ErrorWithValue<E, T> {
    /// Returns the inner error.
    pub fn error(&self) -> E {
        self.error.clone()
    }
}

impl<E: fmt::Debug, T: fmt::Debug> error::Error for ErrorWithValue<E, T> {}

impl<E: fmt::Debug, T> fmt::Display for ErrorWithValue<E, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.error.fmt(f)
    }
}
