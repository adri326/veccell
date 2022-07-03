use super::*;
use std::ops::RangeBounds;

/// Wraps a borrowed reference from a [`VecCell`].
#[derive(Clone)]
pub struct VecRef<'a, T: ?Sized> {
    borrows: VecRefBorrow<'a>,
    value: &'a T,
}

impl<'a, T: ?Sized> VecRef<'a, T> {
    pub(crate) fn new(vec: &'a VecCell<T>, index: usize) -> Option<Self>
    where
        T: Sized
    {
        if vec.mut_borrow.get() == Some(index) {
            return None
        }

        if index >= vec.len() {
            return None
        }

        Some(Self {
            borrows: VecRefBorrow::new(&vec.borrows)?,
            value: unsafe {
                // SAFETY: there are no mutable borrows of vec.inner[index]
                vec.get_unchecked(index)
            }
        })
    }

    fn from(value: &'a T, borrows: &'a Cell<usize>) -> Option<Self> {
        Some(Self {
            borrows: VecRefBorrow::new(borrows)?,
            value
        })
    }

    /// Returns a reference to the borrowed value.
    /// The reference may not outlive this `VecRef` instance.
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<String> = VecCell::new();
    ///
    /// vec.push(String::from("hello"));
    /// vec.push(String::from("world"));
    ///
    /// let guard = vec.get(0).unwrap();
    /// assert_eq!(guard.get(), "hello");
    /// ```
    pub fn get(&self) -> &T {
        &*self.value
    }

    /// Transforms a `VecRef<'_, T>` into a `VecRef<'_, U>` from a function that maps `&T` to `&U`.
    ///
    /// This function does not use `self` and must be called explicitly via `VecRef::map(value, function)`.
    ///
    /// # Examples
    ///
    /// This function comes in hand when you need to return a reference to a value in a [`VecCell`] from within a function/scope.
    /// For instance, the following is disallowed:
    ///
    /// ```compile_fail
    /// # use veccell::*;
    /// fn return_favorite_value<'a>(array: &'a VecCell<Vec<u8>>) -> &'a u8 {
    ///     &array.get(42).unwrap().get()[7]
    /// }
    /// ```
    ///
    /// Instead, you would write it as follows:
    ///
    /// ```
    /// # use veccell::*;
    /// fn return_favorite_value<'a>(array: &'a VecCell<Vec<u8>>) -> VecRef<'a, u8> {
    ///     VecRef::map(array.get(42).unwrap(), |vec| &vec[7])
    /// }
    /// ```
    pub fn map<'b, U: ?Sized, F>(original: VecRef<'b, T>, f: F) -> VecRef<'b, U>
    where
        F: FnOnce(&T) -> &U
    {
        VecRef::from(f(original.value), &original.borrows.0).expect("Error creating a new VecRef: integer overflow")
        // original is dropped here
    }
}

impl<'a, T: ?Sized> Deref for VecRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: Debug + Sized> Debug for VecRef<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VecRef")
            .field(self.value)
            .finish()
    }
}

impl<'a, T: PartialEq + ?Sized> PartialEq for VecRef<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<'a, T: PartialEq + ?Sized> PartialEq<T> for VecRef<'a, T> {
    fn eq(&self, other: &T) -> bool {
        self.get() == other
    }
}

struct VecRefBorrow<'a>(&'a Cell<usize>);

impl<'a> VecRefBorrow<'a> {
    fn new(cell: &'a Cell<usize>) -> Option<Self> {
        cell.set(cell.get().checked_add(1)?);
        Some(Self(cell))
    }
}

impl<'a> Clone for VecRefBorrow<'a> {
    fn clone(&self) -> Self {
        VecRefBorrow::new(&self.0).expect("Error creating a new VecRef: integer overflow")
    }
}

impl<'a> Drop for VecRefBorrow<'a> {
    #[inline]
    fn drop(&mut self) {
        debug_assert!(self.0.get() > 0, "Borrow count was null yet there was still a borrow!");
        self.0.set(self.0.get() - 1);
    }
}

/// Represents an immutable slice for a [`VecCell`].
///
/// # Guarantees
///
/// All of the elements of the VecRange are guaranteed to be immutable.
#[derive(Clone)]
pub struct VecRange<'a, T> {
    borrows: VecRefBorrow<'a>,
    range: &'a [UnsafeCell<T>],
}

impl<'a, T> VecRange<'a, T> {
    pub(crate) fn new<R: RangeBounds<usize>>(vec: &'a VecCell<T>, range: R) -> Option<VecRange<'a, T>>
    where
        T: Sized
    {
        match vec.mut_borrow() {
            Some(index) => {
                if range.contains(&index) {
                    return None; // There is still a mutable borrow to an index within the range
                }
            },
            None => {}
        }

        let low = range.start_bound().cloned();
        let high = range.end_bound().cloned();

        Some(VecRange {
            borrows: VecRefBorrow::new(&vec.borrows)?,
            range: &vec.inner[(low, high)],
        })
    }

    pub fn get(&self, index: usize) -> Option<&T> {
        Some(unsafe {
            // SAFETY: immutability is guaranteed by VecRange's type invariants
            self.range.get(index)?.get().as_ref().unwrap()
        })
    }
}

impl<'a, T> From<VecRange<'a, T>> for VecRef<'a, [UnsafeCell<T>]> {
    fn from(range: VecRange<'a, T>) -> Self {
        Self {
            borrows: range.borrows,
            value: range.range, // :3
        }
    }
}

impl<'a, T> std::ops::Index<usize> for VecRange<'a, T> {
    type Output = T;

    fn index(&self, index: usize) -> &Self::Output {
        unsafe {
            // SAFETY: immutability is guaranteed by VecRange's type invariants
            self.range[index].get().as_ref().unwrap()
        }
    }
}

impl<'a, T> IntoIterator for VecRange<'a, T> {
    type Item = &'a T;
    type IntoIter = VecRangeIter<'a, T>;

    fn into_iter(self) -> Self::IntoIter {
        VecRangeIter {
            iter: self.range.iter()
        }
    }
}

pub struct VecRangeIter<'a, T> {
    iter: std::slice::Iter<'a, UnsafeCell<T>>,
}

impl<'a, T> Iterator for VecRangeIter<'a, T> {
    type Item = &'a T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|x| {
            unsafe {
                // SAFETY: immutability is guaranteed by VecRange's type invariants
                x.get().as_ref().unwrap()
            }
        })
    }
}
