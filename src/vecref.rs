use super::*;
use std::ops::RangeBounds;

// `'self`: lifetime of `Self`

/// Wraps a borrowed reference from a [`VecCell`].
///
/// When an instance of `VecRef` is created, the immutable borrow counter of its parent [`VecCell`] is incremented.
/// Once that instance is [`Drop`ped](Drop), the immutable borrow counter is decremented.
#[derive(Clone)]
pub struct VecRef<'a, T: ?Sized> {
    borrows: VecRefBorrow<'a>,
    value: &'a T,
}

impl<'a, T: ?Sized> VecRef<'a, T> {
    /// # Guarantees
    ///
    /// If `Some(self)` is returned, then:
    /// - no mutable reference exist to `*self`
    /// - `∀ t: min('a, 'self)`, no new mutable reference can be made to `*self`
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

    fn from(value: &'a T, borrows: VecRefBorrow<'a>) -> Self {
        Self {
            borrows,
            value
        }
    }

    /// Returns a reference to the borrowed value.
    /// Equivalent to `&*vec_ref`.
    ///
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
    /// let guard = vec.borrow(0).unwrap();
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
    ///     VecRef::map(array.borrow(42).unwrap(), |vec| &vec[7])
    /// }
    /// ```
    pub fn map<'b, U: ?Sized, F>(original: VecRef<'b, T>, f: F) -> VecRef<'b, U>
    where
        F: FnOnce(&T) -> &U
    {
        VecRef::from(f(original.value), original.borrows.clone())
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
/// All of the elements of the VecRange are guaranteed to only be borrowed immutably.
pub struct VecRange<'a, T> {
    borrows: VecRefBorrow<'a>,
    range: &'a [UnsafeCell<T>],
}

impl<'a, T> VecRange<'a, T> {
    /// # Guarantees
    ///
    /// If `Some(self)` is returned, then:
    /// - no mutable reference exist to `∀ x ∈ self.range`
    /// - `∀ t ∈ min('a, 'self), ∀ x ∈ self.range`, no mutable borrow can be made to `x`
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

    /// Returns an immutable reference to the `index`-th element of the slice, if it is within bounds.
    ///
    /// The reference may not outlive this instance of `VecRange`.
    pub fn get<'b>(&'b self, index: usize) -> Option<&'b T> where 'a: 'b {
        let elem = self.range.get(index)?;
        Some(unsafe {
            // SAFETY: VecRange's type invariants guarantee that no mutable reference to self.range[index] exist now
            // elem.get() is a valid pointer
            // ('a: 'b) -> the &'b T reference cannot outlive 'a
            // (self.borrows: VecRefBorrow<'a>) -> no new mutable reference can be made for 'b to self.range[index]
            elem.get().as_ref().unwrap()
        })
    }

    /// Returns an immutable borrow to the `index`-th element of the slice, if it is within bounds.
    ///
    /// The returned [`VecRef`] increments the immutable reference counter of the parent [`VecCell`].
    pub fn borrow(self: &VecRange<'a, T>, index: usize) -> Option<VecRef<'a, T>> {
        let VecRange { borrows, range } = self.clone();
        let elem = range.get(index)?;

        Some(unsafe {
            // SAFETY: VecRange's type invariants guarantee that no mutable reference to self.range[index] exist now
            // elem.get() is a valid pointer
            // borrows: VecRefBorrow<'a>, thus under VecRef's invariants, no access beyond 'a to elem can be made
            VecRef::from(elem.get().as_ref().unwrap(), borrows)
        })
    }

    pub fn len(&self) -> usize {
        self.range.len()
    }
}

// TODO: use std::mem::transmute to implement From<VecRange<'a, T>> for VecRef<'a, [T]>?
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
        match self.get(index) {
            Some(elem) => elem,
            None => panic!("Index out of bounds: len is {} but index is {}", self.len(), index)
        }
    }
}

impl<'a, T> Clone for VecRange<'a, T> {
    /// The data pointed to by VecRange is already borrows immutably, so it can be safely cloned.
    fn clone(&self) -> Self {
        Self {
            borrows: self.borrows.clone(),
            range: self.range,
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
