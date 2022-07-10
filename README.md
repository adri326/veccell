# VecCell

A variant of `Vec`, with interior mutability, where one element may be borrowed mutably and several other elements may be borrowed immutably at the same time.

You would use this crate if:

- You need a `Vec` with interior mutability
- You only want mutable access to one element at a time
- You want immutable access to all other elements while an element is borrowed mutably
- You need a constant memory cost for the aliasing checks

You would need something else if:

- You don't need interior mutability *(you may use `Vec<T>` instead)*
- While an element is borrowed mutably, you don't need to access the others *(you may use `RefCell<Vec<T>>` instead)*
- You want mutable access to multiple elements at a time *(you may use `Vec<RefCell<T>>` instead)*
- You need to share the array across multiple threads *(you may use `Vec<Mutex<T>>` or `Arc<Vec<Mutex<T>>>` instead)*

## Installation

Run `cargo add veccell` or add the following in `Cargo.toml`:

```toml
[dependencies]
veccell = "0.1.0"
```

## Examples

`VecCell` allows an element to be borrowed mutably, and other elements to be accessed immutably:

```rust
use veccell::VecCell;

let mut arr: VecCell<usize> = VecCell::new();

arr.push(32);
arr.push(48);
arr.push(2);

let mut third = arr.borrow_mut(2).unwrap(); // Borrow the third element mutably
let first = arr.borrow(0).unwrap(); // Borrow the first element immutably

*third *= *first; // Multiply the third element by the first element

println!("{}", third); // Prints 64
std::mem::drop(third); // Drop the mutable borrow

println!("{}", arr.borrow(2).unwrap()); // Also prints 64
```

However, to prevent aliasing, while an element is borrowed mutably, it cannot be borrowed immutably:

```rust
use veccell::VecCell;

let mut arr: VecCell<usize> = VecCell::new();

arr.push(32);
arr.push(48);
arr.push(8);

let mut third = arr.borrow_mut(2).unwrap(); // Borrow the third element mutably

// Here, arr.borrow(2) returns None,
// because the third element is already borrowed mutably.
let third2 = arr.borrow(2);

assert!(third2.is_none());

std::mem::drop(third);
```

`VecCell` only stores two additional pieces of information:

- which element is currently borrowed mutably (accessible through `mut_borrow`)
- how many elements are borrowed immutably (accessible through `borrows`)

This has the advantage of putting all of its elements next to each other in memory, if their padding allows it, but has the disadvantage of having more restrictive rules than you'd expect:

To borrow an element mutably, no element must be borrowed mutably *or immutably*:

```rust
use veccell::VecCell;

let mut arr: VecCell<usize> = VecCell::new();

arr.push(32);
arr.push(48);
arr.push(8);

let second = arr.borrow(1).unwrap();

let third = arr.borrow_mut(2);

// VecCell has no way of telling that the existing immutable borrow (`second`)
// isn't borrowing the third element.
assert!(third.is_none());

std::mem::drop(third);

let first = arr.borrow_mut(0);

// VecCell can only allow one mutable borrow at a time
assert!(arr.borrow_mut(1).is_none());
```

## License

This project is dual-licensed under the MIT license and the Apache v2.0 license.
You may choose either of those when using this library.

Any contribution to this repository must be made available under both licenses.
