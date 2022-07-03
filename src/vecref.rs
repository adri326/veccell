use super::*;

/// Wraps a borrowed reference from a [`VecCell`].
pub struct VecRef<'a, T: ?Sized> {
    borrows: &'a Cell<usize>,
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

        vec.borrows.set(vec.borrows.get().checked_add(1)?);

        Some(Self {
            borrows: &vec.borrows,
            value: unsafe {
                // SAFETY: there are no mutable borrows of vec.inner[index]
                vec.get_unchecked(index)
            }
        })
    }

    fn from(value: &'a T, borrows: &'a Cell<usize>) -> Option<Self> {
        borrows.set(borrows.get().checked_add(1)?);

        Some(Self {
            borrows,
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
        VecRef::from(f(original.value), original.borrows).expect("Error creating a new VecRef: integer overflow")
        // original is dropped here
    }
}

impl<'a, T: ?Sized> Deref for VecRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized> Drop for VecRef<'a, T> {
    #[inline]
    fn drop(&mut self) {
        debug_assert!(self.borrows.get() > 0, "Borrow count was null yet there was still a borrow!");
        self.borrows.set(self.borrows.get() - 1);
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

impl<'a, T: ?Sized> Clone for VecRef<'a, T> {
    fn clone(&self) -> Self {
        Self::from(self.value, self.borrows).expect("Error creating a new VecRef: integer overflow")
    }
}
