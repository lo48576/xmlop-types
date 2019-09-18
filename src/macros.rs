//! Macros.

/// Implement traits for string types.
///
/// Types specified as `slice` should be tuple struct and have `str` as the first (`.0`) field.
///
/// Types specified as `owned` should implement `From<&slice>`.
macro_rules! impl_string_types {
    (
        owned: $ty_owned:ty,
        slice: $ty_slice:ty,
        error_slice: $ty_error_slice:ty,
        parse: $parse:expr,
        slice_new_unchecked: $slice_new_unchecked:expr,
    ) => {
        impl_string_slice! {
            slice: $ty_slice,
            error_slice: $ty_error_slice,
            parse: $parse,
            slice_new_unchecked: $slice_new_unchecked,
        }

        impl_string_owned_by_box! {
            owned: $ty_owned,
            slice: $ty_slice,
            error_slice: $ty_error_slice,
        }
    };
}

/// Implement traits for string slice type.
///
/// Types specified as `slice` should:
///
/// * be tuple struct and have `str` as the first (`.0`) field, and
/// * have method with name given by `slice_new_unchecked`.
macro_rules! impl_string_slice {
    (
        slice: $ty_slice:ty,
        error_slice: $ty_error_slice:ty,
        parse: $parse:expr,
        slice_new_unchecked: $slice_new_unchecked:expr,
    ) => {
        impl<'a> std::convert::TryFrom<&'a str> for &'a $ty_slice {
            type Error = $ty_error_slice;

            fn try_from(s: &'a str) -> Result<Self, Self::Error> {
                $parse(s).into_complete_result()
            }
        }

        impl AsRef<$ty_slice> for $ty_slice {
            fn as_ref(&self) -> &Self {
                self
            }
        }

        impl AsRef<str> for $ty_slice {
            fn as_ref(&self) -> &str {
                &self.0
            }
        }

        impl Clone for Box<$ty_slice> {
            fn clone(&self) -> Self {
                Box::from(&**self)
            }
        }

        impl_smartptr_string_slice! {
            slice: $ty_slice,
            smartptr: std::boxed::Box<$ty_slice>,
            smartptr_inner: std::boxed::Box<str>,
        }

        impl_smartptr_string_slice! {
            slice: $ty_slice,
            smartptr: std::rc::Rc<$ty_slice>,
            smartptr_inner: std::rc::Rc<str>,
        }

        impl_smartptr_string_slice! {
            slice: $ty_slice,
            smartptr: std::sync::Arc<$ty_slice>,
            smartptr_inner: std::sync::Arc<str>,
        }
    };
}

/// Implement traits for string slice type.
///
/// Types specified as `slice` should:
///
/// * be tuple struct and have `str` as the first (`.0`) field, and
/// * have method with name given by `slice_new_unchecked`.
macro_rules! impl_smartptr_string_slice {
    (
        slice: $ty_slice:ty,
        smartptr: $ty_smartptr:ty,
        smartptr_inner: $ty_smartptr_inner:ty,
    ) => {
        impl From<&$ty_slice> for $ty_smartptr {
            fn from(s: &$ty_slice) -> Self {
                let buf = <$ty_smartptr_inner>::from(AsRef::<str>::as_ref(s));
                unsafe {
                    // This is safe because:
                    //
                    // * `Box::into_raw(buf) as *mut $ty_slice` has valid layout memory layout, and
                    // * the content is valid as `$ty_slice`.
                    <$ty_smartptr>::from_raw(<$ty_smartptr_inner>::into_raw(buf) as *mut $ty_slice)
                }
            }
        }
    };
}

/// Implement traits for owned string type using `Box<Slice>`.
///
/// Types specified as `slice` should implement some traits using `impl_string_slice!` macro.
///
/// Types specified as `owned` should be tuple struct and have `Box<str>` as the first (`.0`) field.
macro_rules! impl_string_owned_by_box {
    (
        owned: $ty_owned:ty,
        slice: $ty_slice:ty,
        error_slice: $ty_error_slice:ty,
    ) => {
        impl From<Box<$ty_slice>> for $ty_owned {
            fn from(s: Box<$ty_slice>) -> Self {
                Self(s)
            }
        }

        impl From<&$ty_slice> for $ty_owned {
            fn from(s: &$ty_slice) -> Self {
                Self(Box::from(s))
            }
        }

        impl std::convert::TryFrom<&str> for $ty_owned {
            type Error = $ty_error_slice;

            fn try_from(s: &str) -> Result<Self, Self::Error> {
                <&$ty_slice as std::convert::TryFrom<&str>>::try_from(s).map(Into::into)
            }
        }

        impl std::convert::TryFrom<Box<str>> for $ty_owned {
            type Error = crate::error::ErrorWithValue<$ty_error_slice, Box<str>>;

            fn try_from(s: Box<str>) -> Result<Self, Self::Error> {
                if let Err(e) = <&$ty_slice>::try_from(AsRef::<str>::as_ref(&s)) {
                    return Err(crate::error::ErrorWithValue::new(e, s));
                }
                let box_inner = unsafe {
                    // This is safe because:
                    //
                    // * `Box::into_raw(s) as *mut $ty_slice` has valid layout memory layout, and
                    // * the content is valid as `$ty_slice`.
                    Box::from_raw(Box::into_raw(s) as *mut $ty_slice)
                };
                Ok(Self(box_inner))
            }
        }

        impl std::convert::TryFrom<String> for $ty_owned {
            type Error = crate::error::ErrorWithValue<$ty_error_slice, String>;

            fn try_from(s: String) -> Result<Self, Self::Error> {
                if let Err(e) = <&$ty_slice>::try_from(AsRef::<str>::as_ref(&s)) {
                    return Err(crate::error::ErrorWithValue::new(e, s));
                }
                let s: Box<str> = s.into();
                let box_inner = unsafe {
                    // This is safe because:
                    //
                    // * `Box::into_raw(s) as *mut $ty_slice` has valid layout memory layout, and
                    // * the content is valid as `$ty_slice`.
                    Box::from_raw(Box::into_raw(s) as *mut $ty_slice)
                };
                Ok(Self(box_inner))
            }
        }

        impl From<$ty_owned> for Box<$ty_slice> {
            fn from(s: $ty_owned) -> Self {
                s.0
            }
        }

        impl std::ops::Deref for $ty_owned {
            type Target = $ty_slice;

            fn deref(&self) -> &Self::Target {
                &self.0
            }
        }

        impl From<$ty_owned> for Box<str> {
            fn from(s: $ty_owned) -> Self {
                unsafe {
                    // This is safe because:
                    //
                    // * `Box::into_raw(s.0) as *mut str` has valid layout memory layout, and
                    //     + (This is because `s.0` is always created from `Box<str>`.)
                    // * the content is valid as `str`.
                    Box::from_raw(Box::into_raw(s.0) as *mut str)
                }
            }
        }

        impl From<$ty_owned> for String {
            fn from(s: $ty_owned) -> Self {
                Into::<Box<str>>::into(s).into()
            }
        }

        impl AsRef<$ty_slice> for $ty_owned {
            fn as_ref(&self) -> &$ty_slice {
                &self.0
            }
        }

        impl AsRef<str> for $ty_owned {
            fn as_ref(&self) -> &str {
                AsRef::<str>::as_ref(&*self.0)
            }
        }

        impl std::borrow::Borrow<$ty_slice> for $ty_owned {
            fn borrow(&self) -> &$ty_slice {
                &self.0
            }
        }

        impl std::borrow::ToOwned for $ty_slice {
            type Owned = $ty_owned;

            fn to_owned(&self) -> Self::Owned {
                Box::<$ty_slice>::from(self).into()
            }
        }

        impl std::str::FromStr for $ty_owned {
            type Err = $ty_error_slice;

            fn from_str(s: &str) -> Result<Self, Self::Err> {
                <Self as std::convert::TryFrom<&str>>::try_from(s)
            }
        }
    };
}

/// Implement comparation for custom string types.
///
/// Types specified as `slice` should implement some traits using `impl_string_slice!` macro.
///
/// Types specified as `owned` should implement some traits using `impl_string_owned_by_box!` macro.
macro_rules! impl_string_cmp {
    (
        owned: $ty_owned:ty,
        slice: $ty_slice:ty,
    ) => {
        impl_string_cmp! {
            slice: $ty_slice,
            operands: ($ty_slice, $ty_owned),
        }
        impl_string_cmp! {
            slice: $ty_slice,
            operands: (&'_ $ty_slice, $ty_owned),
        }
        impl_string_cmp! {
            slice: $ty_slice,
            operands: ($ty_slice, std::borrow::Cow<'_, $ty_slice>),
        }
        impl_string_cmp! {
            slice: $ty_slice,
            operands: ($ty_owned, std::borrow::Cow<'_, $ty_slice>),
        }
    };
    (
        slice: $ty_slice:ty,
        operands: ($ty_lhs:ty, $ty_rhs:ty),
    ) => {
        impl PartialEq<$ty_rhs> for $ty_lhs {
            fn eq(&self, other: &$ty_rhs) -> bool {
                <$ty_slice as PartialEq<$ty_slice>>::eq(self.as_ref(), other.as_ref())
            }
        }
        impl PartialEq<$ty_lhs> for $ty_rhs {
            fn eq(&self, other: &$ty_lhs) -> bool {
                <$ty_slice as PartialEq<$ty_slice>>::eq(self.as_ref(), other.as_ref())
            }
        }

        impl PartialOrd<$ty_rhs> for $ty_lhs {
            fn partial_cmp(&self, other: &$ty_rhs) -> Option<std::cmp::Ordering> {
                <$ty_slice as PartialOrd<$ty_slice>>::partial_cmp(self.as_ref(), other.as_ref())
            }
        }
        impl PartialOrd<$ty_lhs> for $ty_rhs {
            fn partial_cmp(&self, other: &$ty_lhs) -> Option<std::cmp::Ordering> {
                <$ty_slice as PartialOrd<$ty_slice>>::partial_cmp(self.as_ref(), other.as_ref())
            }
        }
    };
}

/// Implement comparation to `str` for custom string types.
///
/// Types specified as `slice` should implement some traits using `impl_string_slice!` macro.
///
/// Types specified as `owned` should implement some traits using `impl_string_owned_by_box!` macro.
macro_rules! impl_string_cmp_to_string {
    (
        owned: $ty_owned:ty,
        slice: $ty_slice:ty,
    ) => {
        impl_string_cmp_to_string! {
            slice: $ty_slice,
            operands: (str, $ty_slice),
        }
        impl_string_cmp_to_string! {
            slice: $ty_slice,
            operands: (str, $ty_owned),
        }
        impl_string_cmp_to_string! {
            slice: $ty_slice,
            operands: (String, $ty_slice),
        }
        impl_string_cmp_to_string! {
            slice: $ty_slice,
            operands: (String, $ty_owned),
        }
    };
    (
        slice: $ty_slice:ty,
        operands: ($ty_lhs:ty, $ty_rhs:ty),
    ) => {
        impl PartialEq<$ty_rhs> for $ty_lhs {
            fn eq(&self, other: &$ty_rhs) -> bool {
                <str as PartialEq<str>>::eq(self.as_ref(), other.as_ref())
            }
        }
        impl PartialEq<$ty_lhs> for $ty_rhs {
            fn eq(&self, other: &$ty_lhs) -> bool {
                <str as PartialEq<str>>::eq(self.as_ref(), other.as_ref())
            }
        }

        impl PartialOrd<$ty_rhs> for $ty_lhs {
            fn partial_cmp(&self, other: &$ty_rhs) -> Option<std::cmp::Ordering> {
                <str as PartialOrd<str>>::partial_cmp(self.as_ref(), other.as_ref())
            }
        }
        impl PartialOrd<$ty_lhs> for $ty_rhs {
            fn partial_cmp(&self, other: &$ty_lhs) -> Option<std::cmp::Ordering> {
                <str as PartialOrd<str>>::partial_cmp(self.as_ref(), other.as_ref())
            }
        }
    };
}
