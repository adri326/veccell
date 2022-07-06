//! # `VecCell`, a variant of `Vec` with interior mutability
//!
//! This crate contains the [`VecCell<T>`](VecCell) type, which implements a contiguous,
//! growable array (similar to [`Vec<T>`](Vec)) with interior mutability (similar to [`RefCell<T>`](std::cell::RefCell)).
//!
//! You would use this crate if:
//! - You need a `Vec` with [interior mutability](std::cell#when-to-choose-interior-mutability)
//! - You only want mutable access to one element at a time
//! - You want immutable access to all other elements while an element is borrowed mutably
//! - You need a constant memory cost
//!
//! You would need something else if:
//! - You don't need interior mutability *(you may use `Vec<T>` instead)*
//! - While an element is borrowed mutably, you don't need to access the others *(you may use `RefCell<Vec<T>>` instead)*
//! - You want mutable access to multiple elements at a time *(you may use `Vec<RefCell<T>>` instead)*
//! - You need to share the array across multiple threads *(you may use `Vec<Mutex<T>>` or `Arc<Vec<Mutex<T>>>` instead)*

use std::cell::{Cell, UnsafeCell};
use std::fmt::{self, Debug};
use std::ops::{Deref, DerefMut};

mod vecref;
pub use vecref::{VecRef, VecRange, VecRangeIter};

mod vecrefmut;
pub use vecrefmut::VecRefMut;

/// A contiguous, growable array type with interior mutability.
///
/// This type allows to get a mutable reference ([`VecRefMut`]) to an index `i`, while letting you access immutably ([`VecRef`]) elements at indices `j != i`.
/// New mutable references may only be created if there are no active mutable *or immutable* references.
/// New immutable references may only be created for indices that aren't mutably borrowed.
///
/// - To borrow an item immutably, use [`borrow()`](VecCell::borrow).
/// - To borrow an item mutably, use [`borrow_mut()`](VecCell::borrow_mut).
/// - If you have a mutable reference to the `VecCell`, then you may also use [`get_mut()`](VecCell::get_mut).
/// - You may access the internal `Vec<UnsafeCell<T>>` using [`inner()`](VecCell::inner) and [`inner_mut()`](VecCell::inner_mut).
/// - To read the number of borrows, use [`borrows()`](VecCell::borrows) and [`mut_borrow()`](VecCell::mut_borrow)
///
/// This type is essentially a more restricted version of `Vec<RefCell<T>>`,
/// with the benefit of having a lower memory footprint since we only need
/// `sizeof!(usize) + sizeof!(Option<usize>)` bytes instead of `N*sizeof!(usize)` bytes of memory to prevent aliasing.
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
///     let prev = vec.borrow(index - 1).unwrap();
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
    /// Creates a new, empty `VecCell`.
    pub fn new() -> Self {
        Self {
            mut_borrow: Cell::new(None),
            borrows: Cell::new(0),
            inner: Vec::new(),
        }
    }

    /// Creates a new, empty `VecCell` with `capacity` as capacity.
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            mut_borrow: Cell::new(None),
            borrows: Cell::new(0),
            inner: Vec::with_capacity(capacity)
        }
    }

    /// Returns the length of the `VecCell`, ie. the number of elements in the array.
    ///
    /// See [`Vec::len()`] for more information.
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    /// assert_eq!(vec.len(), 0); // There are no elements
    ///
    /// vec.push(32);
    /// assert_eq!(vec.len(), 1); // There is one element: [32]
    ///
    /// vec.push(64);
    /// assert_eq!(vec.len(), 2); // There are two elements: [32, 64]
    ///
    /// vec.push(64);
    /// assert_eq!(vec.len(), 3); // There are three elements: [32, 64, 64]
    /// ```
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
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(4);
    /// vec.push(6);
    /// vec.push(8);
    /// vec.push(10);
    /// vec.push(12);
    ///
    /// vec.remove(0);
    ///
    /// assert_eq!(vec, vec![6, 8, 10, 12]);
    /// ```
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
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(4);
    /// vec.push(6);
    /// vec.push(8);
    /// vec.push(10);
    /// vec.push(12);
    ///
    /// vec.swap_remove(0);
    ///
    /// assert_eq!(vec, vec![12, 6, 8, 10]);
    /// ```
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
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(2);
    /// vec.push(5);
    /// vec.push(9);
    ///
    /// // There are no borrows at this point
    /// assert_eq!(vec.borrows(), 0);
    ///
    /// let x = vec.borrow(1);
    ///
    /// // There is exactly one borrow at this point
    /// assert_eq!(vec.borrows(), 1);
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
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(2);
    /// vec.push(5);
    /// vec.push(9);
    ///
    /// // There is no mutable borrow at this point
    /// assert_eq!(vec.mut_borrow(), None);
    ///
    /// let x = vec.borrow_mut(2);
    ///
    /// // There is a mutable borrow of element 2 at this point
    /// assert_eq!(vec.mut_borrow(), Some(2));
    ///
    /// std::mem::drop(x); // x lives up to here
    /// ```
    pub fn mut_borrow(&self) -> Option<usize> {
        self.mut_borrow.get()
    }

    /// Pushes a value at the end of the array.
    ///
    /// # Example
    ///
    /// ```
    /// use veccell::VecCell;
    ///
    /// let mut vec: VecCell<usize> = VecCell::new();
    /// assert_eq!(vec.len(), 0);
    ///
    /// vec.push(32);
    /// assert_eq!(vec.len(), 1);
    /// assert_eq!(vec.borrow(0).unwrap(), 32);
    ///
    /// vec.push(127);
    /// assert_eq!(vec.len(), 2);
    /// assert_eq!(vec.borrow(1).unwrap(), 127);
    /// ```
    pub fn push(&mut self, value: T) {
        self.inner.push(UnsafeCell::new(value));
    }

    /// Pops the last value of the array, if any.
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    ///
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(7);
    /// vec.push(15);
    /// vec.push(31);
    ///
    /// assert_eq!(vec.pop(), Some(31));
    /// assert_eq!(vec.len(), 2);
    ///
    /// assert_eq!(vec.pop(), Some(15));
    /// assert_eq!(vec.len(), 1);
    /// ```
    pub fn pop(&mut self) -> Option<T> {
        self.inner.pop().map(UnsafeCell::into_inner)
    }

    /// Borrows the `index`-th element immutably, if it exists and isn't already mutably borrowed.
    /// Returns `None` otherwise.
    ///
    /// To prevent aliasing, this function returns `None` if `self.mut_borrow() == Some(index)`.
    /// Otherwise, it returns `Some(VecRef(reference))` to make sure that the immutable borrow is well-tracked.
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let x = vec.borrow(1).unwrap();
    ///
    /// assert_eq!(*x, 2);
    ///
    /// let y = vec.borrow(1).unwrap();
    ///
    /// assert_eq!(x, y);
    ///
    /// // Manual drops for demonstration purposes
    /// std::mem::drop(x);
    /// std::mem::drop(y);
    /// ```
    pub fn borrow<'b>(&'b self, index: usize) -> Option<VecRef<'b, T>> {
        VecRef::new(self, index)
    }

    /// Borrows a range of elements, making sure that none of these elements are borrowed mutably already.
    /// Returns `Some(VecRef(slice))` on success.
    /// Returns `None` otherwise.
    ///
    /// To prevent aliasing, this function returns `None` if `self.mut_borrow().is_some()` and `self.mut_borrow().unwrap() ∈ range`.
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let s = vec.borrow_range(0..2).unwrap(); // Gets elements 0 and 1
    /// ```
    pub fn borrow_range<'b, R: std::ops::RangeBounds<usize>>(&'b self, range: R) -> Option<VecRange<'b, T>> {
        VecRange::new(self, range)
    }

    /// Borrows the `index`-th element mutably, if it exists and no mutable *or immutable* borrow are active.
    /// Returns `None` otherwise.
    ///
    /// To prevent aliasing, this function only returns `Some(VecRefMut(reference))` if `self.mut_borrow() == None` and `self.borrows() == 0`.
    /// The [`VecRefMut`] object sets `self.mut_borrow` to `Some(index)` and clears this field once it is dropped.
    ///
    /// If you need to borrow an element mutably and borrow another element immutably, then you must *first* borrow it mutably, then borrow it immutably.
    /// Otherwise, `borrow_mut` will not have the guarantee that its element isn't already being borrowed.
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let mut x = vec.borrow_mut(1).unwrap();
    /// let y = vec.borrow(2).unwrap();
    ///
    /// *x = *y;
    ///
    /// // Manual drops for demonstration purposes
    /// std::mem::drop(x);
    /// std::mem::drop(y);
    ///
    /// assert_eq!(vec.borrow(1).unwrap(), 3);
    /// ```
    pub fn borrow_mut<'b>(&'b self, index: usize) -> Option<VecRefMut<'b, T>> {
        VecRefMut::new(self, index)
    }

    // TODO: reborrow_mut? To extend a mutable borrow without needing to check anything?

    /// Returns a mutable reference to the `index`-th element, if it exists.
    /// Requires exclusive access to `self` (guaranteed by `&mut self`).
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let x = vec.get_mut(1).unwrap();
    /// *x = 5;
    ///
    /// assert_eq!(vec.borrow(1).unwrap(), 5);
    /// ```
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.inner.get_mut(index).map(UnsafeCell::get_mut)
    }

    // TODO: implement Drop on the iterator? This way the panic can be more thorough

    /// Returns an iterator of immutable borrows ([`VecRef`]).
    ///
    /// # Panics
    ///
    /// Panics if an element was mutably borrowed when the iterator yields it.
    ///
    /// # Examples
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(0);
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// for (index, guard) in vec.iter().enumerate() {
    ///     assert_eq!(index, *guard);
    /// }
    /// ```
    pub fn iter<'b>(&'b self) -> impl Iterator<Item = VecRef<'b, T>> {
        self.into_iter()
    }

    /// Returns an iterator of mutable references.
    /// Requires exclusive access to `self` (guaranteed by `&mut self`).
    ///
    /// # Examples
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(0);
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// for x in vec.iter_mut() {
    ///     *x += 1;
    /// }
    ///
    /// assert_eq!(vec, vec![1, 2, 3, 4]);
    /// ```
    pub fn iter_mut<'b>(&'b mut self) -> impl Iterator<Item = &'b mut T> {
        self.inner.iter_mut().map(UnsafeCell::get_mut)
    }

    /// Returns an iterator of immutable borrows ([`VecRef`]).
    /// Yields `None` for any element that was mutably borrowed when the iterator tried to yield it.
    ///
    /// Equivalent to calling `(0..self.len()).map(VecCell::get)`.
    /// Can be used in conjunction with [`Iterator::flatten()`] and [`<Option as IntoIterator>`](std::option::Option#impl-IntoIterator)
    ///
    /// # Examples
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(0);
    /// vec.push(1);
    /// vec.push(2);
    /// vec.push(3);
    ///
    /// let x = vec.borrow_mut(1);
    ///
    /// let vec2: Vec<_> = vec.try_iter().flatten().map(|x| *x).collect();
    /// assert_eq!(vec2, vec![0, 2, 3]); // Element 1 was skipped, as it was mutably borrowed
    ///
    /// // Manual drop for demonstration purposes
    /// std::mem::drop(x);
    /// ```
    pub fn try_iter<'b>(&'b self) -> impl Iterator<Item = Option<VecRef<'b, T>>> {
        (0..self.len()).map(|index| {
            self.borrow(index)
        })
    }

    /// Resets the [`borrows`](VecCell::borrows) and [`mut_borrow`](VecCell::mut_borrow) counters.
    /// Useful if a [`VecRef`] or [`VecRefMut`] was [forgotten without `Drop`ping it](std::mem::forget).
    ///
    /// Requires exclusive access to `self` (guaranteed by `&mut self`).
    ///
    /// # Example
    ///
    /// ```
    /// # use veccell::*;
    /// let mut vec: VecCell<usize> = VecCell::new();
    ///
    /// vec.push(0);
    /// vec.push(1);
    /// vec.push(2);
    ///
    /// let x = vec.borrow_mut(1);
    /// let y = vec.borrow(2);
    ///
    /// std::mem::forget(x);
    /// std::mem::forget(y);
    ///
    /// assert_eq!(vec.mut_borrow(), Some(1));
    /// assert_eq!(vec.borrows(), 1);
    ///
    /// vec.undo_leak();
    ///
    /// assert_eq!(vec.mut_borrow(), None);
    /// assert_eq!(vec.borrows(), 0);
    /// ```
    pub fn undo_leak(&mut self) {
        self.borrows.set(0);
        self.mut_borrow.set(None);
    }

    /// Returns a reference to the inner buffer, on which you may safely perform immutable operations.
    #[inline]
    pub fn inner(&self) -> &Vec<UnsafeCell<T>> {
        &self.inner
    }

    /// Returns a mutable reference to the inner buffer, on which you may safely perform mutable operations.
    /// Requires exclusive access to `self` (guaranteed by `&mut self`).
    #[inline]
    pub fn inner_mut(&mut self) -> &mut Vec<UnsafeCell<T>> {
        &mut self.inner
    }

    /// Returns the raw parts of a `VecCell` in the format `(inner_vec, mut_borrow, borrows)`.
    /// If no reference was [forgotten](std::mem::forget), then `mut_borrow == None` and `borrows == 0`.
    #[inline]
    pub fn into_raw_parts(self) -> (Vec<UnsafeCell<T>>, Option<usize>, usize) {
        (self.inner, self.mut_borrow.into_inner(), self.borrows.into_inner())
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
    type IntoIter = VecCellRefIter<'a, T>;

    /// # Panics
    ///
    /// Panics if a value is currently mutably borrowed
    fn into_iter(self) -> Self::IntoIter {
        VecCellRefIter {
            vec: self,
            index: 0
        }
    }
}

// TODO: remove once https://github.com/rust-lang/rust/issues/63063 is merged
/// Iterator returned by [`VecCell::iter`]
#[derive(Clone)]
pub struct VecCellRefIter<'a, T> {
    vec: &'a VecCell<T>,
    index: usize
}

impl<'a, T> Iterator for VecCellRefIter<'a, T> {
    type Item = VecRef<'a, T>;

    fn next(&mut self) -> Option<Self::Item> {
        if self.index >= self.vec.len() {
            return None
        }

        let res = match self.vec.borrow(self.index) {
            Some(x) => x,
            None => panic!("Error while borrowing immutably element {} of VecCell: already mutably borrowed", self.index),
        };
        self.index += 1;

        Some(res)
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        if self.index >= self.vec.len() {
            return (0, Some(0));
        }

        let remaining = self.vec.len() - self.index;

        (remaining, Some(remaining))
    }
}

impl<'a, T> ExactSizeIterator for VecCellRefIter<'a, T> {
    fn len(&self) -> usize {
        if self.index >= self.vec.len() {
            0
        } else {
            self.vec.len() - self.index
        }
    }
}

impl<'a, T> std::iter::FusedIterator for VecCellRefIter<'a, T> {}

impl<T> IntoIterator for VecCell<T> {
    type Item = T;
    type IntoIter = VecCellIntoIter<T>;

    /// # Panics
    ///
    /// Panics if a value is currently mutably borrowed
    fn into_iter(self) -> Self::IntoIter {
        VecCellIntoIter {
            iter: self.inner.into_iter()
        }
    }
}

// TODO: remove once https://github.com/rust-lang/rust/issues/63063 is merged
/// Iterator returned by [`VecCell::into_iter`]
pub struct VecCellIntoIter<T> {
    iter: std::vec::IntoIter<UnsafeCell<T>>,
}

impl<T> Iterator for VecCellIntoIter<T> {
    type Item = T;

    fn next(&mut self) -> Option<Self::Item> {
        self.iter.next().map(|x| x.into_inner())
    }

    fn size_hint(&self) -> (usize, Option<usize>) {
        self.iter.size_hint()
    }
}

impl<T> ExactSizeIterator for VecCellIntoIter<T> {
    fn len(&self) -> usize {
        self.iter.len()
    }
}

impl<T> std::iter::FusedIterator for VecCellIntoIter<T> {}

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

impl<T> From<VecCell<T>> for Vec<T> {
    fn from(veccell: VecCell<T>) -> Vec<T> {
        veccell.into_iter().collect::<Vec<_>>()
    }
}

#[cfg(test)]
mod test;

#[doc = include_str!("../README.md")]
#[cfg(doctest)]
pub struct ReadmeDoctests;
