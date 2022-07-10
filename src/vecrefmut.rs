use super::*;

// Lets us safely destructure VecRefMut while implementing the Drop logic
struct VecRefMutBorrow<'a>(&'a Cell<Option<usize>>);

/// Wraps a mutably borrowed value from a [`VecCell`].
pub struct VecRefMut<'a, T: ?Sized> {
    mut_borrow: VecRefMutBorrow<'a>,
    value: &'a mut T,
}

impl<'a, T: ?Sized> VecRefMut<'a, T> {
    /// # Safety
    ///
    /// If this function returns Some(ref), then there are no mutable borrows of ∀x, vec.inner[x]:
    /// by contradiction, let `B: 'b` be a mutable borrow of lifetime `'b`. By conjunction on (IV):
    ///     - either `B` had exclusive access, in which case calling `VecCell::borrow_mut` is UB
    ///     - either `B` was obtained from a guard `VecRefMut<'c>`, in which case `'c: 'b` and `vec.mut_borrow.is_some()`, which contradicts our assertion
    ///
    /// - The invariant (I) is upheld by the first assertion.
    /// - The invariant (II) is upheld by this function, as it sets `vec.mut_borrow` to `Some(index)`.
    pub(crate) fn new(vec: &'a VecCell<T>, index: usize) -> Option<Self>
    where
        T: Sized
    {
        if vec.borrows.get() > 0 || vec.mut_borrow.get().is_some() {
            return None
        }

        if index >= vec.len() {
            return None
        }

        vec.mut_borrow.set(Some(index));

        Some(Self {
            mut_borrow: VecRefMutBorrow(&vec.mut_borrow),
            value: unsafe {
                vec.get_mut_unchecked(index)
            }
        })
    }

    /// Returns an immutable reference to the borrowed value.
    /// The reference may not outlive this `VecRefMut` instance.
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
    /// let guard = vec.borrow_mut(0).unwrap();
    /// assert_eq!(guard.get(), "hello");
    /// ```
    pub fn get(&self) -> &T {
        &*self.value
    }

    /// Transforms a `VecRefMut<'_, T>` into a `VecRefMut<'_, U>` from a function that maps `&mut T` to `&mut U`.
    ///
    /// This function does not use `self` and must be called explicitly via `VecRefMut::map(value, function)`.
    ///
    /// # Examples
    ///
    /// ```
    /// # use veccell::*;
    /// fn return_favorite_value_mut<'a>(array: &'a VecCell<Vec<u8>>) -> VecRefMut<'a, u8> {
    ///     VecRefMut::map(array.borrow_mut(42).unwrap(), |vec| &mut vec[7])
    /// }
    /// ```
    pub fn map<'b, U: ?Sized, F>(original: VecRefMut<'b, T>, f: F) -> VecRefMut<'b, U>
    where
        F: FnOnce(&mut T) -> &mut U
    {
        let VecRefMut { value, mut_borrow } = original;
        VecRefMut {
            value: f(value),
            mut_borrow
        }
    }

    /// Variant of [`VecRefMut::map`], where the callback (`f`) may fail.
    ///
    /// `f` must return a `Result`; if it returns `Ok(x)`, then `try_map` returns `Ok(VecRefMut(x))`.
    /// Otherwise, it returns `Err(err)`.
    pub fn try_map<'b, U: ?Sized, F, E>(original: VecRefMut<'b, T>, f: F) -> Result<VecRefMut<'b, U>, E>
    where
        F: FnOnce(&mut T) -> Result<&mut U, E>
    {
        let VecRefMut { value, mut_borrow } = original;
        Ok(VecRefMut {
            value: f(value)?,
            mut_borrow: mut_borrow
        })
    }
}

impl<'a, T: ?Sized> Deref for VecRefMut<'a, T> {
    type Target = T;

    // SAFETY: Upholds invariant (IV)
    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T: ?Sized> DerefMut for VecRefMut<'a, T> {
    // SAFETY: Upholds invariant (IV)
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value
    }
}

impl<'a> Drop for VecRefMutBorrow<'a> {
    #[inline]
    fn drop(&mut self) {
        debug_assert!(self.0.get().is_some());
        self.0.set(None);
    }
}


impl<'a, T: Debug + ?Sized> Debug for VecRefMut<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VecRefMut")
            .field(&self.value)
            .finish()
    }
}

impl<'a, T: Display + ?Sized> Display for VecRefMut<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        <T as Display>::fmt(&self.value, f)
    }
}

impl<'a, T: PartialEq + ?Sized> PartialEq for VecRefMut<'a, T> {
    fn eq(&self, other: &Self) -> bool {
        self.get() == other.get()
    }
}

impl<'a, T: PartialEq + ?Sized> PartialEq<T> for VecRefMut<'a, T> {
    fn eq(&self, other: &T) -> bool {
        self.get() == other
    }
}
