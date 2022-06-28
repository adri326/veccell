#![feature(type_alias_impl_trait)]

use std::cell::{Cell, UnsafeCell};
use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};

///
/// # Safety
///
/// The following invariants are enforced by the code:
///
/// - (I) mutable guards (`RefMut`) may only be created if `vec.mut_borrow.is_none()` and `vec.borrows == 0`
/// - (II) when a mutable guard is created, `vec.mut_borrow` is set to `Some(index)`
/// - (III) when a mutable guard is dropped, `vec.mut_borrow` may be set back to `None`
/// - (IV) a mutable reference may only be created if:
///     - (IV-a) exclusive access to the `VecCell` is guaranteed (`&mut VecCell`)
///     - (IV-b) it is created from a mutable guard, and the mutable guard's lifetime does not exceed that of the mutable guard
#[derive(Debug)]
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

    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    #[inline]
    pub fn remove(&mut self, index: usize) -> T {
        self.inner.remove(index).into_inner()
    }

    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> T {
        self.inner.swap_remove(index).into_inner()
    }

    #[inline]
    pub fn inner(&self) -> &Vec<UnsafeCell<T>> {
        &self.inner
    }

    #[inline]
    pub fn inner_mut(&mut self) -> &mut Vec<UnsafeCell<T>> {
        &mut self.inner
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

    pub fn iter<'b>(&'b self) -> impl Iterator<Item = VecRef<'b, T>> {
        self.into_iter()
    }

    pub fn iter_mut<'b>(&'b mut self) -> impl Iterator<Item = &'b mut T> {
        self.inner.iter_mut().map(UnsafeCell::get_mut)
    }
}

impl<'a, T: 'a> IntoIterator for &'a VecCell<T> {
    type Item = VecRef<'a, T>;
    type IntoIter = impl Iterator<Item = Self::Item>;

    /// # Panics
    ///
    /// Panics if a value is currently mutably borrowed
    fn into_iter(self) -> Self::IntoIter {
        (0..self.len()).map(|index| {
            self.get(index).expect("An element of VecCell is currently mutably borrowed")
        })
    }
}

impl<T> IntoIterator for VecCell<T> {
    type Item = T;
    type IntoIter = impl Iterator<Item = Self::Item>;

    /// # Panics
    ///
    /// Panics if a value is currently mutably borrowed
    fn into_iter(self) -> Self::IntoIter {
        self.inner.into_iter().map(|x| x.into_inner())
    }
}

impl<T: Clone> Clone for VecCell<T> {
    /// # Panics
    ///
    /// Panics if a value is currently mutably borrowed
    fn clone(&self) -> Self {
        VecCell {
            inner: self.into_iter().map(|x| UnsafeCell::new((*x).clone())).collect::<Vec<_>>(),
            mut_borrow: Cell::new(None),
            borrows: Cell::new(0),
        }
    }
}

impl<T: PartialEq> PartialEq for VecCell<T> {
    /// # Panics
    ///
    /// Panics if a value in `self` or `other` is currently mutably borrowed when it is encountered in the comparison.
    fn eq(&self, other: &Self) -> bool {
        if self.len() != other.len() {
            return false
        }

        for (s, o) in self.iter().zip(other.iter()) {
            if *s != *o {
                return false
            }
        }

        true
    }
}

impl<T: PartialEq> PartialEq<Vec<T>> for VecCell<T> {
    /// # Panics
    ///
    /// Panics if a value in `self` is currently mutably borrowed when it is encountered in the comparison.
    fn eq(&self, other: &Vec<T>) -> bool {
        if self.len() != other.len() {
            return false
        }

        for (s, o) in self.iter().zip(other.iter()) {
            if *s != *o {
                return false
            }
        }

        true
    }
}

impl<T> From<Vec<T>> for VecCell<T> {
    fn from(vec: Vec<T>) -> Self {
        VecCell {
            inner: vec.into_iter().map(|x| UnsafeCell::new(x)).collect::<Vec<_>>(),
            mut_borrow: Cell::new(None),
            borrows: Cell::new(0),
        }
    }
}

pub struct VecRef<'a, T: ?Sized> {
    borrows: &'a Cell<usize>,
    value: &'a T,
}

impl<'a, T: ?Sized> VecRef<'a, T> {
    fn new(vec: &'a VecCell<T>, index: usize) -> Option<Self>
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

    pub fn get(&self) -> &T {
        &*self.value
    }

    pub fn map<'b, U: ?Sized, F>(original: VecRef<'b, T>, f: F) -> VecRef<'b, U>
    where
        F: FnOnce(&T) -> &U
    {
        VecRef {
            value: f(original.value),
            borrows: original.borrows
        }
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

pub struct VecRefMut<'a, T: ?Sized> {
    mut_borrow: &'a Cell<Option<usize>>,
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
    fn new(vec: &'a VecCell<T>, index: usize) -> Option<Self>
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
            mut_borrow: &vec.mut_borrow,
            value: unsafe {
                vec.get_mut_unchecked(index)
            }
        })
    }

    pub fn get(&self) -> &T {
        &*self.value
    }

    pub fn get_mut(&mut self) -> &mut T {
        &mut *self.value
    }

    // pub fn map<'b, U: ?Sized, F>(original: VecRefMut<'b, T>, f: F) -> VecRefMut<'b, U>
    // where
    //     F: FnOnce(&mut T) -> &mut U
    // {
    //     let VecRefMut { value, mut_borrow } = original;
    //     VecRefMut {
    //         value: f(value),
    //         mut_borrow
    //     }
    // }
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

impl<'a, T: ?Sized> Drop for VecRefMut<'a, T> {
    #[inline]
    fn drop(&mut self) {
        debug_assert!(self.mut_borrow.get().is_some());
        self.mut_borrow.set(None);
    }
}

impl<'a, T: Debug + Sized> Debug for VecRefMut<'a, T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_tuple("VecRefMut")
            .field(self.value)
            .finish()
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

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_create_vec() {
        let vec: VecCell<usize> = VecCell::new();
        assert_eq!(vec.len(), 0);
        let vec: VecCell<i8> = VecCell::new();
        assert_eq!(vec.len(), 0);
        let vec: VecCell<()> = VecCell::new();
        assert_eq!(vec.len(), 0);

        let vec: VecCell<usize> = VecCell::with_capacity(16);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), 16);
        let vec: VecCell<i8> = VecCell::with_capacity(16);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), 16);
        let vec: VecCell<()> = VecCell::with_capacity(16);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), usize::MAX);


        let vec: VecCell<usize> = VecCell::with_capacity(0);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), 0);
        let vec: VecCell<i8> = VecCell::with_capacity(0);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), 0);
        let vec: VecCell<()> = VecCell::with_capacity(0);
        assert_eq!(vec.len(), 0);
        assert_eq!(vec.capacity(), usize::MAX);
    }

    #[test]
    fn test_push() {
        let mut vec: VecCell<usize> = VecCell::with_capacity(1);
        vec.push(0);
        assert_eq!(vec.len(), 1);
        vec.push(1);
        assert_eq!(vec.len(), 2);
        vec.push(2);
        assert_eq!(vec.len(), 3);

        assert_eq!(vec, vec![0, 1, 2]);
    }

    #[test]
    fn test_pop() {
        let mut vec: VecCell<usize> = VecCell::new();
        vec.push(1);
        assert_eq!(vec.len(), 1);
        vec.push(2);
        assert_eq!(vec.len(), 2);

        assert_eq!(vec.pop(), Some(2));
        assert_eq!(vec.len(), 1);
        assert_eq!(vec.pop(), Some(1));
        assert_eq!(vec.len(), 0);
    }

    #[test]
    fn test_borrow() {
        let mut vec: VecCell<usize> = VecCell::new();
        vec.push(1);
        vec.push(2);

        let mut x = vec.borrow_mut(1).unwrap();

        assert_eq!(vec.get(0).unwrap(), 1);
        assert_eq!(vec.get(1), None);

        *x = 3;

        std::mem::drop(x);

        assert_eq!(vec.get(1).unwrap(), 3);
    }

    #[test]
    fn test_double_borrow() {
        let mut vec: VecCell<usize> = VecCell::new();
        vec.push(1);
        vec.push(2);

        let mut x = vec.borrow_mut(1).unwrap();
        let y = vec.borrow_mut(0);

        assert!(y.is_none());
        assert_eq!(vec.mut_borrow(), Some(1));
        assert!(vec.borrow_mut(1).is_none());
        assert_eq!(vec.mut_borrow(), Some(1));

        assert_eq!(vec.get(0).unwrap(), 1);
        assert_eq!(vec.get(1), None);

        *x = 3;

        std::mem::drop(x);
        std::mem::drop(y);

        assert_eq!(vec.mut_borrow(), None);
        assert_eq!(vec.get(1).unwrap(), 3);
    }

    #[test]
    fn test_out_of_bounds() {
        let mut vec: VecCell<usize> = VecCell::new();

        assert!(vec.get(0).is_none());

        vec.push(1);

        assert!(vec.get(0).is_some());
        assert!(vec.get(1).is_none());
    }
}
