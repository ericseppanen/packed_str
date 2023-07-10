//! Packed Immutable Strings
//!
//! `PackedStr` is a replacement for `Vec<String>` when the strings are all
//! immutable.
//!
//! The benefit of using `PackedStr` is that all of the string data is stored
//! in a single heap allocation. This may save space compared to `Vec<String>`,
//! where each `String` has its own heap allocation, and associated costs (excess
//! `String` capacity, allocator metadata, heap fragmentation).
//!
//! In addition, each `String` stores its own size and capacity, which are not
//! necessary due to the `PackedStr` design.
//!
//! `PackedStr` is implemented as one large buffer containing all the string data,
//! and a list of indexes into the buffer. Each string slice can be reconstructed
//! from its index, and the index of the next string (or the end of the buffer,
//! for the last string).
//!

use std::fmt::Debug;
use std::ops::Index;

/// A packed array of immutable strings.
///
/// Strings are stored in the order they are added.
/// Empty strings are allowed.
///
/// # Examples
/// ```
/// # use packed_str::PackedStr;
/// let mut ps = PackedStr::new();
/// ps.push("hello");
/// ps.push("world");
/// assert_eq!(ps.get(0), Some("hello"));
/// assert_eq!(ps.get(1), Some("world"));
/// ```
///
#[derive(Default)]
pub struct PackedStr {
    indexes: Vec<usize>,
    str_data: Vec<u8>,
}

impl PackedStr {
    /// Create a new, empty `PackedStr`.
    pub const fn new() -> Self {
        Self {
            indexes: Vec::new(),
            str_data: Vec::new(),
        }
    }

    /// Create a new, empty `PackedStr` with capacity for `count` strings.
    ///
    /// Dynamic allocation will still take place for strings that are added.
    /// If the total size of all strings is known, `with_capacities` can be
    /// used instead.
    pub fn with_capacity(count: usize) -> Self {
        Self {
            indexes: Vec::with_capacity(count),
            str_data: Vec::new(),
        }
    }

    /// Create a new, empty `PackedStr` with capacity for `count` strings consuming `str_bytes` bytes.
    ///
    /// To avoid future allocations, set `str_bytes` to the total size of all
    /// strings that will be included.
    pub fn with_capacities(count: usize, str_bytes: usize) -> Self {
        Self {
            indexes: Vec::with_capacity(count),
            str_data: Vec::with_capacity(str_bytes),
        }
    }

    /// Create a new `PackedStr` from a slice of strings.
    ///
    /// # Examples
    /// ```
    /// # use packed_str::PackedStr;
    /// let inputs = vec!["a", "b", "c"];
    /// let ps = PackedStr::from_slice(&inputs);
    /// assert_eq!(&ps[1], "b");
    /// ```
    pub fn from_slice<S: AsRef<str>>(slice: &[S]) -> Self {
        let mut packed_str = PackedStr::with_capacity(slice.len());
        for s in slice {
            packed_str.push(s);
        }
        packed_str
    }

    /// Shrink allocated storage to the minimum size.
    pub fn shrink_to_fit(&mut self) {
        self.indexes.shrink_to_fit();
        self.str_data.shrink_to_fit();
    }

    /// Append a string to the `PackedStr`
    pub fn push(&mut self, string: impl AsRef<str>) {
        self.indexes.push(self.str_data.len());
        self.str_data.extend_from_slice(string.as_ref().as_bytes());
    }

    /// Return the number of elements in the `PackedStr`.
    pub fn len(&self) -> usize {
        self.indexes.len()
    }

    /// Return whether the `PackedStr` contains any strings.
    pub fn is_empty(&self) -> bool {
        self.indexes.is_empty()
    }

    /// Returns one string from the `PackedStr`.
    ///
    /// If the index is higher than the number of strings stored, `None` will be
    /// returned.
    pub fn get(&self, index: usize) -> Option<&str> {
        // We can always find the string start, assuming that `index` is valid.
        let str_start = *self.indexes.get(index)?;
        // The string end will either be the start of the next string, or the
        // end of the `str_data` array, if this string is the last one.
        let str_end = self
            .indexes
            .get(index + 1)
            .copied()
            .unwrap_or(self.str_data.len());

        debug_assert!(str_end >= str_start);

        let byte_slice = &self.str_data[str_start..str_end];
        // SAFETY: We are recovering a slice of bytes that was originally
        // passed to us as a valid str. We don't need to check whether it's
        // valid UTF-8 because we haven't modified the string contents or
        // changed its bounds.
        let result = unsafe { std::str::from_utf8_unchecked(byte_slice) };

        Some(result)
    }

    /// Return an iterator over all stored strings.
    pub fn iter(&self) -> Iter<'_> {
        Iter {
            parent: self,
            index: 0,
        }
    }

    /// Check if the `PackedStr` contains the given string.
    ///
    /// This operation takes O(n) time.
    pub fn contains<T>(&self, value: &T) -> bool
    where
        T: PartialEq<str>,
    {
        self.iter().any(|s| value == s)
    }
}

// FIXME: this is really weird: x[i] is sugar for *x.index(i).
// I can't return &&str because that would imply a temporary &str that gets dropped.
// End result is that callers need to use &x[i] instead.

impl Index<usize> for PackedStr {
    type Output = str;

    fn index(&self, index: usize) -> &Self::Output {
        self.get(index).unwrap_or_else(|| {
            panic!(
                "index ({}) out of bounds (size {})",
                index,
                self.indexes.len()
            );
        })
    }
}

impl Debug for PackedStr {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_list().entries(self.iter()).finish()
    }
}

/// An iterator over the strings inside a `PackedStr`.
pub struct Iter<'a> {
    parent: &'a PackedStr,
    index: usize,
}

impl<'a> Iterator for Iter<'a> {
    type Item = &'a str;

    fn next(&mut self) -> Option<Self::Item> {
        let index = self.index;
        self.index += 1;
        self.parent.get(index)
    }
}

impl<'a> IntoIterator for &'a PackedStr {
    type Item = &'a str;

    type IntoIter = Iter<'a>;

    fn into_iter(self) -> Self::IntoIter {
        self.iter()
    }
}

impl<'a> FromIterator<&'a str> for PackedStr {
    fn from_iter<T: IntoIterator<Item = &'a str>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (size, _) = iter.size_hint();
        let mut packed_str = PackedStr::with_capacity(size);
        for s in iter {
            packed_str.push(s);
        }
        packed_str
    }
}

// This is what is used when the input is &["a", "b"] or &vec!["a", "b"].

impl<'a> FromIterator<&'a &'a str> for PackedStr {
    fn from_iter<T: IntoIterator<Item = &'a &'a str>>(iter: T) -> Self {
        let iter = iter.into_iter();
        let (size, _) = iter.size_hint();
        let mut packed_str = PackedStr::with_capacity(size);
        for s in iter {
            packed_str.push(s);
        }
        packed_str
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn simple() {
        let mut ps = PackedStr::new();
        ps.push("hello");
        ps.push(String::from("world"));
        ps.push("");
        ps.push(String::new());
        assert_eq!(&ps[2], "");
        assert_eq!(&ps[1], "world");
        assert_eq!(&ps[0], "hello");
        assert_eq!(&ps[3], "");
        assert!(ps.get(4).is_none());

        let x: Vec<&str> = ps.iter().collect();
        assert_eq!(x.len(), 4);
        let all = x.join(",");
        assert_eq!(all, "hello,world,,");
    }

    #[test]
    fn debug_format() {
        let inputs = vec!["a", "b", "c"];
        let ps = PackedStr::from_slice(&inputs);
        let formatted = format!("{ps:?}");
        assert_eq!(formatted, r#"["a", "b", "c"]"#);
    }

    #[test]
    fn collect() {
        let ps = PackedStr::from_slice(&["abc", "def", "ghi"]);
        let mut it = ps.iter();
        assert_eq!(it.next(), Some("abc"));
        assert_eq!(it.next(), Some("def"));
        assert_eq!(it.next(), Some("ghi"));
        assert_eq!(it.next(), None);
    }

    #[test]
    fn empty() {
        let ps = PackedStr::default();
        assert!(ps.get(0).is_none());
        assert_eq!(ps.len(), 0);
        assert!(ps.iter().next().is_none());
    }
}
