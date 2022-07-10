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
    /// - `∀ t: min('a, 'self)`, no new mutable reference can be made to `*self` during `'t`
    pub(crate) fn new(vec: &'a VecCell<T>, index: usize) -> Option<Self>
    where
        T: Sized
    {
        if vec.mut_borrow.get() == Some(index) {
            // `vec[index]` is already borrowed mutably, return None
            return None
        }

        if index >= vec.len() {
            return None
        }

        Some(Self {
            borrows: VecRefBorrow::new(&vec.borrows)?,
            value: unsafe {
                // SAFETY: there are no mutable borrows of vec.inner[index] (from vec.mut_borrow == None)
                vec.get_unchecked(index)
            }
        })
    }

    pub(crate) fn from_range<R: RangeBounds<usize>>(vec: &'a VecCell<T>, range: R) -> Option<VecRef<'a, [T]>>
    where
        T: Sized
    {
        use std::mem::{size_of, align_of};

        match vec.mut_borrow() {
            Some(index) => {
                if range.contains(&index) {
                    // There is a mutable borrow to an index within the range, return None
                    return None;
                }
            },
            None => {}
        }

        let low = range.start_bound().cloned();
        let high = range.end_bound().cloned();

        let range: &[UnsafeCell<T>] = &vec.inner[(low, high)];
        let range: &[T] = unsafe {
            let ptr: *const UnsafeCell<T> = range.as_ptr();
            let len = range.len();

            assert!(ptr as *const () == UnsafeCell::raw_get(ptr) as *const ());
            assert!(size_of::<UnsafeCell<T>>() == size_of::<T>());
            assert!(align_of::<UnsafeCell<T>>() == align_of::<T>());

            // SAFETY:
            // - ptr is a valid pointer
            // - there are no mutable reference to any element within (low, high)
            // - ptr == old(ptr), since UnsafeCell has repr(transparent) (also asserted)
            let ptr: *mut T = UnsafeCell::raw_get(ptr);
            let ptr = ptr as *const T;

            // SAFETY:
            // - `ptr` is a valid pointer
            // - `ptr` points to an array of `len` elements of type `UnsafeCell<T>`
            // - UnsafeCell has repr(transparent)
            // - size_of(UnsafeCell<T>) == size_of(T)
            // - align_of(UnsafeCell<T>) == align_of(T)
            // - thus, [UnsafeCell<T>] and [T] have the same representation in memory
            // - thus, ptr points to an array of `len` elements of type `T`
            // - there are no mutable reference to any element of `slice`
            let slice: &[T] = std::slice::from_raw_parts(ptr, len);

            slice
        };

        Some(VecRef {
            borrows: VecRefBorrow::new(&vec.borrows)?,
            value: range,
        })
    }

    fn from(value: &'a T, borrows: VecRefBorrow<'a>) -> Self {
        Self {
            borrows,
            value
        }
    }

    // /// Returns a reference to the borrowed value.
    // /// Equivalent to `&*vec_ref`.
    // ///
    // /// The reference may not outlive this `VecRef` instance.
    // ///
    // /// # Example
    // ///
    // /// ```
    // /// # use veccell::*;
    // /// let mut vec: VecCell<String> = VecCell::new();
    // ///
    // /// vec.push(String::from("hello"));
    // /// vec.push(String::from("world"));
    // ///
    // /// let guard = vec.borrow(0).unwrap();
    // /// assert_eq!(guard.get(), "hello");
    // /// ```
    // pub fn get(&self) -> &T {
    //     &*self.value
    // }

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

    /// Variant of [`VecRef::map`], where the callback (`f`) may fail.
    ///
    /// `f` must return a `Result`; if it returns `Ok(x)`, then `try_map` returns `Ok(VecRef(x))`.
    /// Otherwise, it returns `Err(err)`.
    pub fn try_map<'b, U: ?Sized, F, E>(original: VecRef<'b, T>, f: F) -> Result<VecRef<'b, U>, E>
    where
        F: FnOnce(&T) -> Result<&U, E>
    {
        Ok(VecRef::from(f(original.value)?, original.borrows.clone()))
    }
}

impl<'a, T: Sized> VecRef<'a, [T]> {
    /// Returns an immutable borrow to the `index`-th element of the array.
    /// Returns `None` if `index` is out of bounds.
    pub fn borrow(&self, index: usize) -> Option<VecRef<'a, T>> {
        Some(VecRef::from(self.value.get(index)?, self.borrows.clone()))
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
        self.value == other.value
    }
}

impl<'a, T: PartialEq + ?Sized> PartialEq<T> for VecRef<'a, T> {
    fn eq(&self, other: &T) -> bool {
        self.value == other
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
