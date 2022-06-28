use std::cell::{Cell, UnsafeCell};
use std::fmt::{self, Debug};

pub struct VecCell<T> {
    mut_borrow: Cell<Option<usize>>,
    borrows: Cell<usize>,
    inner: Vec<UnsafeCell<T>>,
}

impl<T> VecCell<T> {
    pub fn new() -> Self {
        Self {
            mut_borrow: Cell::new(None),
            borrows: Cell::new(0),
            inner: Vec::new(),
        }
    }

    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            mut_borrow: Cell::new(None),
            borrows: Cell::new(0),
            inner: Vec::with_capacity(capacity)
        }
    }

    pub fn into_raw_parts(self) -> (Vec<UnsafeCell<T>>, Option<usize>, usize) {
        (self.inner, self.mut_borrow.into_inner(), self.borrows.into_inner())
    }

    pub unsafe fn from_raw_parts(inner: Vec<UnsafeCell<T>>, mut_borrow: Option<usize>, borrows: usize) -> Self {
        Self {
            inner,
            borrows: Cell::new(borrows),
            mut_borrow: Cell::new(mut_borrow),
        }
    }

    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    pub fn borrows(&self) -> usize {
        self.borrows.get()
    }

    pub fn mut_borrow(&self) -> Option<usize> {
        self.mut_borrow.get()
    }

    pub fn push(&mut self, value: T) {
        self.inner.push(UnsafeCell::new(value));
    }

    pub fn pop(&mut self) -> Option<T> {
        debug_assert!(self.mut_borrow.get().is_none());
        self.inner.pop().map(UnsafeCell::into_inner)
    }

    pub fn get<'b>(&'b self, index: usize) -> Option<VecRef<'b, T>> {
        VecRef::new(self, index)
    }

    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        &*self.inner.get_unchecked(index).get()
    }

    pub fn borrow_mut<'b>(&'b self, index: usize) -> Option<VecRefMut<'b, T>> {
        VecRefMut::new(self, index)
    }

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.inner.get_mut(index).map(UnsafeCell::get_mut)
    }

    pub unsafe fn get_mut_unchecked(&self, index: usize) -> &mut T {
        &mut *self.inner.get_unchecked(index).get()
    }
}

pub struct VecRef<'a, T> {
    borrows: &'a Cell<usize>,
    value: &'a T,
}

impl<'a, T> VecRef<'a, T> {
    fn new(vec: &'a VecCell<T>, index: usize) -> Option<Self> {
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
}

impl<'a, T> std::ops::Deref for VecRef<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T> Drop for VecRef<'a, T> {
    #[inline]
    fn drop(&mut self) {
        debug_assert!(self.borrows.get() > 0, "Borrow count was null yet there was still a borrow!");
        self.borrows.set(self.borrows.get() - 1);
    }
}

impl<'a, T: Debug> Debug for VecRef<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VecRef")
            .field(self.value)
            .finish()
    }
}

pub struct VecRefMut<'a, T> {
    mut_borrow: &'a Cell<Option<usize>>,
    value: &'a mut T,
}

impl<'a, T> VecRefMut<'a, T> {
    fn new(vec: &'a VecCell<T>, index: usize) -> Option<Self> {
        if vec.borrows.get() > 0 || vec.mut_borrow.get().is_some() {
            return None
        }

        if index >= vec.len() {
            return None
        }

        vec.mut_borrow.set(Some(index));

        Some(Self {
            mut_borrow: &vec.mut_borrow,
            value: unsafe {
                // SAFETY: there are no mutable borrows of ∀x, vec.inner[x],
                // and we set vec.mut_borrow to Some(index), guaranteeing no further aliasing
                vec.get_mut_unchecked(index)
            }
        })
    }
}

impl<'a, T> std::ops::Deref for VecRefMut<'a, T> {
    type Target = T;

    fn deref(&self) -> &Self::Target {
        self.value
    }
}

impl<'a, T> std::ops::DerefMut for VecRefMut<'a, T> {
    fn deref_mut(&mut self) -> &mut Self::Target {
        self.value
    }
}

impl<'a, T> Drop for VecRefMut<'a, T> {
    #[inline]
    fn drop(&mut self) {
        debug_assert!(self.mut_borrow.get().is_some());
        self.mut_borrow.set(None);
    }
}

impl<'a, T: Debug> Debug for VecRefMut<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VecRefMut")
            .field(self.value)
            .finish()
    }
}
