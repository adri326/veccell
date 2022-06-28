//! # `VecCell`, a variant of `Vec` with interior mutability
//!
//! This crate contains the [`VecCell<T>`](VecCell) type, which implements a contiguous,
//! growable array (similar to [`Vec<T>`](Vec)) with interior mutability (similar to [`RefCell<T>`](std::cell::RefCell)).
//!
//! You would use this crate if:
//! - You need a `Vec` with [interior mutability](std::cell#when-to-choose-interior-mutability)
//! - You only want mutable access to one element at a time
//! - You need a constant memory cost
//!
//! You wouldn't need this crate if:
//! - You don't need interior mutability (use `Vec<T>`)
//! - You want mutable access to multiple elements at a time (use `Vec<RefCell<T>>`)
//! - You need to share the array across multiple threads (use `Vec<Mutex<T>>` or `Arc<Vec<Mutex<T>>>`)

#![feature(type_alias_impl_trait)]

use std::cell::{Cell, UnsafeCell};
use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};

/// A contiguous, growable array type with interior mutability.
///
/// This type allows to get a mutable reference ([`VecRefMut`]) to an index `i`, while letting you access immutably ([`VecRef`]) elements at indices `j != i`.
/// New mutable references may only be created if there are no active mutable *or immutable* references.
/// New immutable references may only be created for indices that aren't mutably borrowed.
///
/// - To borrow an item immutably, use [`VecCell::get`].
/// - To borrow an item mutably, use [`VecCell::borrow_mut`].
/// - If you have a mutable reference to the `VecCell`, then you may also use [`VecCell::get_mut`].
/// - You may access the internal `Vec<UnsafeCell<T>>` using [`VecCell::inner`] and [`VecCell::inner_mut`].
///
/// This type is essentially a more restricted version of `Vec<RefCell<T>>`,
/// with the benefit of having a lower memory footprint since we only need
/// `sizeof!(usize)+sizeof!(Option<usize>)` bytes instead of `N*sizeof!(usize)` bytes of memory to prevent aliasing.
///
/// # Examples
///
/// ```
/// use veccell::VecCell;
///
/// fn update(current: &mut usize, prev: &usize) {
///     *current += *prev;
/// }
///
/// // Create an empty vec
/// let mut vec: VecCell<usize> = VecCell::new();
///
/// // Add the numbers from 0 to 9 in vec
/// for n in 0..10 {
///     vec.push(n);
/// }
///
/// for index in 1..10 {
///     // Get a mutable reference *then* an immutable reference
///     // (would fail if the order was reversed)
///     let mut current = vec.borrow_mut(index).unwrap();
///     let prev = vec.get(index - 1).unwrap();
///
///     // Give both references to update
///     update(current.get_mut(), prev.get());
/// }
///
/// assert_eq!(vec, vec![0, 1, 3, 6, 10, 15, 21, 28, 36, 45]);
/// ```
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
pub struct VecCell<T> {
    mut_borrow: Cell<Option<usize>>,
    borrows: Cell<usize>,
    inner: Vec<UnsafeCell<T>>,
}

impl<T> VecCell<T> {
    /// Creates a new `VecCell`.
    pub fn new() -> Self {
        Self {
            mut_borrow: Cell::new(None),
            borrows: Cell::new(0),
            inner: Vec::new(),
        }
    }

    /// Creates a new `VecCell` with `capacity` as capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            mut_borrow: Cell::new(None),
            borrows: Cell::new(0),
            inner: Vec::with_capacity(capacity)
        }
    }

    /// Returns the raw parts of a `VecCell` in the format `(inner_vec, mut_borrow, borrows)`.
    /// If no reference was [forgotten](std::mem::forget), then `mut_borrow == None` and `borrows == 0`.
    pub fn into_raw_parts(self) -> (Vec<UnsafeCell<T>>, Option<usize>, usize) {
        (self.inner, self.mut_borrow.into_inner(), self.borrows.into_inner())
    }

    /// Returns the length of the `VecCell`, ie. the number of elements in the array.
    ///
    /// See [`Vec::len()`] for more information.
    #[inline]
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// Returns the capacity of the `VecCell`, ie. the number of elements that can be added before we need to realloc.
    /// The following holds true at any time: `vec.len() <= vec.capacity()`.
    ///
    /// See [`Vec::capacity()`] for more information.
    #[inline]
    pub fn capacity(&self) -> usize {
        self.inner.capacity()
    }

    /// Reserves space in the buffer for at least `additional` more elements.
    ///
    /// See [`Vec::reserve()`] for more information.
    #[inline]
    pub fn reserve(&mut self, additional: usize) {
        self.inner.reserve(additional);
    }

    /// Removes the element at index `index`, shifting the elements after it and returning that index.
    ///
    /// See [`Vec::remove()`] for more information.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.len()`.
    #[inline]
    pub fn remove(&mut self, index: usize) -> T {
        self.inner.remove(index).into_inner()
    }

    /// Removes the element at index `index`, replacing it with the last element.
    ///
    /// See [`Vec::swap_remove()`] for more information.
    ///
    /// # Panics
    ///
    /// Panics if `index >= self.len()`.
    #[inline]
    pub fn swap_remove(&mut self, index: usize) -> T {
        self.inner.swap_remove(index).into_inner()
    }

    /// Returns the number of immutable borrows to elements of the `VecCell`.
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new(0);
    ///
    /// vec.push(2);
    /// vec.push(5);
    /// vec.push(9);
    ///
    /// // There are no borrows at this point
    /// assert_eq!(x.borrows(), 0);
    ///
    /// let x = vec.get(1);
    ///
    /// // There is exactly one borrow at this point
    /// assert_eq!(x.borrows(), 1);
    ///
    /// std::mem::drop(x); // x lives up to here
    /// ```
    pub fn borrows(&self) -> usize {
        self.borrows.get()
    }

    /// Returns the index of the mutable borrows of the `VecCell`, if any.
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new(0);
    ///
    /// vec.push(2);
    /// vec.push(5);
    /// vec.push(9);
    ///
    /// // There is no mutable borrow at this point
    /// assert_eq!(x.mut_borrow(), None);
    ///
    /// let x = vec.get_mut(2);
    ///
    /// // There is a mutable borrow of element 2 at this point
    /// assert_eq!(x.mut_borrow(), Some(2));
    ///
    /// std::mem::drop(x); // x lives up to here
    /// ```
    pub fn mut_borrow(&self) -> Option<usize> {
        self.mut_borrow.get()
    }

    pub fn push(&mut self, value: T) {
        self.inner.push(UnsafeCell::new(value));
    }

    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop().map(UnsafeCell::into_inner)
    }

    pub fn get<'b>(&'b self, index: usize) -> Option<VecRef<'b, T>> {
        VecRef::new(self, index)
    }

    pub fn borrow_mut<'b>(&'b self, index: usize) -> Option<VecRefMut<'b, T>> {
        VecRefMut::new(self, index)
    }

    // TODO: reborrow_mut?

    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.inner.get_mut(index).map(UnsafeCell::get_mut)
    }

    pub fn iter<'b>(&'b self) -> impl Iterator<Item = VecRef<'b, T>> {
        self.into_iter()
    }

    pub fn iter_mut<'b>(&'b mut self) -> impl Iterator<Item = &'b mut T> {
        self.inner.iter_mut().map(UnsafeCell::get_mut)
    }

    pub fn try_iter<'b>(&'b self) -> impl Iterator<Item = Option<VecRef<'b, T>>> {
        (0..self.len()).map(|index| {
            self.get(index)
        })
    }

    /// Returns a reference to the inner buffer.
    /// You may safely perform immutable operations on it.
    #[inline]
    pub fn inner(&self) -> &Vec<UnsafeCell<T>> {
        &self.inner
    }

    /// Returns a mutable reference to the inner buffer.
    /// You may safely perform mutable operations on it.
    #[inline]
    pub fn inner_mut(&mut self) -> &mut Vec<UnsafeCell<T>> {
        &mut self.inner
    }

    // == Unsafe functions section ==

    /// Alternative to `get`, which skips all checks and returns a mutable reference.
    /// Neither the `mut_borrow`, nor the `borrows` buffer will be updated or read,
    /// so make sure that no exclusive reference to the element at `index` is made.
    ///
    /// If `index >= len`, then calling this function is undefined behavior.
    pub unsafe fn get_unchecked(&self, index: usize) -> &T {
        &*self.inner.get_unchecked(index).get()
    }

    /// Alternative to `borrow_mut`, which skips all checks and returns a mutable reference.
    /// Neither the `mut_borrow`, nor the `borrows` buffer will be updated or read,
    /// so make sure that this is the only reference to the element at `index`.
    ///
    /// If `index >= len`, then calling this function is undefined behavior.
    pub unsafe fn get_mut_unchecked(&self, index: usize) -> &mut T {
        &mut *self.inner.get_unchecked(index).get()
    }

    /// Constructs a `VecCell` from its raw parts.
    pub unsafe fn from_raw_parts(inner: Vec<UnsafeCell<T>>, mut_borrow: Option<usize>, borrows: usize) -> Self {
        Self {
            inner,
            borrows: Cell::new(borrows),
            mut_borrow: Cell::new(mut_borrow),
        }
    }
}

impl<T: fmt::Debug> fmt::Debug for VecCell<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        enum BorrowStatus<T> {
            Ok(T),
            Borrowed,
        }

        impl<T: Debug> fmt::Debug for BorrowStatus<VecRef<'_, T>> {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                match self {
                    BorrowStatus::Ok(x) => fmt::Debug::fmt(x.get(), f),
                    BorrowStatus::Borrowed => write!(f, "(borrowed)"),
                }
            }
        }

        f.debug_struct("VecCell")
            .field("borrows", &self.borrows.get())
            .field("mut_borrow", &self.mut_borrow.get())
            .field("inner", &self.try_iter().map(|x| {
                match x {
                    Some(y) => BorrowStatus::Ok(y),
                    None => BorrowStatus::Borrowed,
                }
            }).collect::<Box<[_]>>())
            .finish()
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
            match self.get(index) {
                Some(x) => x,
                None => panic!("Error while borrowing immutably element {} of VecCell: already mutably borrowed", index),
            }
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

/// Wraps a borrowed reference from a [`VecCell`].
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

    fn from(value: &'a T, borrows: &'a Cell<usize>) -> Option<Self> {
        borrows.set(borrows.get().checked_add(1)?);

        Some(Self {
            borrows,
            value
        })
    }

    pub fn get(&self) -> &T {
        &*self.value
    }

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

/// Wraps a mutably borrowed value from a [`VecCell`].
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

    #[test]
    fn test_borrow_clone() {
        let mut vec: VecCell<usize> = VecCell::new();

        vec.push(1);
        vec.push(2);

        let x = vec.get(0);
        assert_eq!(vec.borrows(), 1);
        assert_eq!(vec.borrows(), 1);
        assert_eq!(vec.mut_borrow(), None);

        let y = x.clone();

        assert_eq!(vec.borrows(), 2);
        assert_eq!(vec.borrows(), 2);
        assert_eq!(vec.mut_borrow(), None);

        assert_eq!(x, y);

        std::mem::drop(x);
        assert_eq!(vec.borrows(), 1);
        std::mem::drop(y);
        assert_eq!(vec.borrows(), 0);

        let x = vec.get(0);
        assert_eq!(vec.borrows(), 1);
        let y = vec.get(0);
        assert_eq!(vec.borrows(), 2);
        let z = x.clone();
        assert_eq!(vec.borrows(), 3);

        std::mem::drop(z);
        assert_eq!(vec.borrows(), 2);
        std::mem::drop(y);
        assert_eq!(vec.borrows(), 1);
        std::mem::drop(x);
        assert_eq!(vec.borrows(), 0);
    }

    #[test]
    fn test_borrow_mut() {
        let mut vec: VecCell<usize> = VecCell::new();

        vec.push(1);
        vec.push(2);

        let x = vec.get(0);
        assert!(x.is_some());

        let y = vec.borrow_mut(0);
        assert!(y.is_none());

        let y = vec.borrow_mut(1);
        assert!(y.is_none());

        std::mem::drop(x);

        let y = vec.borrow_mut(0);
        assert!(y.is_some());

        let z = vec.borrow_mut(1);
        assert!(z.is_none());

        std::mem::drop(y);
    }

    #[test]
    fn test_iter() {
        let mut vec: Vec<usize> = Vec::new();
        let mut vec2: VecCell<usize> = VecCell::new();

        for x in 0..10 {
            vec.push(x);
            vec2.push(x);
        }

        let vec3 = vec2.iter().map(|x| *x).collect::<Vec<_>>();

        assert_eq!(vec, vec3);
    }

    #[test]
    #[should_panic]
    fn test_iter_panic() {
        let mut vec: VecCell<usize> = VecCell::new();

        for x in 0..10 {
            vec.push(x);
        }

        let y = vec.borrow_mut(3);

        for _x in vec.iter() {
            // noop
        }

        std::mem::drop(y);
    }
}
