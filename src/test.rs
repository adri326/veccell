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

    assert_eq!(vec.borrow(0).unwrap(), 1);
    assert_eq!(vec.borrow(1), None);

    *x = 3;

    std::mem::drop(x);

    assert_eq!(vec.borrow(1).unwrap(), 3);
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

    assert_eq!(vec.borrow(0).unwrap(), 1);
    assert_eq!(vec.borrow(1), None);

    *x = 3;

    std::mem::drop(x);
    std::mem::drop(y);

    assert_eq!(vec.mut_borrow(), None);
    assert_eq!(vec.borrow(1).unwrap(), 3);
}

#[test]
fn test_out_of_bounds() {
    let mut vec: VecCell<usize> = VecCell::new();

    assert!(vec.borrow(0).is_none());

    vec.push(1);

    assert!(vec.borrow(0).is_some());
    assert!(vec.borrow(1).is_none());
}

#[test]
fn test_borrow_clone() {
    let mut vec: VecCell<usize> = VecCell::new();

    vec.push(1);
    vec.push(2);

    let x = vec.borrow(0);
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

    let x = vec.borrow(0);
    assert_eq!(vec.borrows(), 1);
    let y = vec.borrow(0);
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

    let x = vec.borrow(0);
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

#[test]
fn test_range() {
    let mut vec: VecCell<usize> = VecCell::new();

    for x in 0..10 {
        vec.push(x);
    }

    let mut_ref = vec.borrow_mut(3);

    // Check that it is impossible to reference the same element as mut_ref
    assert!(vec.borrow_range(0..10).is_none());
    assert!(vec.borrow_range(0..=3).is_none());
    assert!(vec.borrow_range(0..4).is_none());
    assert!(vec.borrow_range(3..4).is_none());
    assert!(vec.borrow_range(3..=3).is_none());
    assert!(vec.borrow_range(3..).is_none());
    assert!(vec.borrow_range(0..).is_none());
    assert!(vec.borrow_range(..4).is_none());
    assert!(vec.borrow_range(..=4).is_none());

    let range = vec.borrow_range(4..7).unwrap();

    for x in 0..5 {
        if x < 3 {
            assert!(range.get(x).is_some());
            assert!(range.borrow(x).is_some());
            assert_eq!(range[x], x + 4);
        } else {
            assert!(range.get(x).is_none());
            assert!(range.borrow(x).is_none());
        }
    }

    let range = vec.borrow_range(5..).unwrap();

    for x in 0..10 {
        if x < 5 {
            assert!(range.get(x).is_some());
            assert!(range.borrow(x).is_some());
            assert_eq!(range[x], x + 5);
        } else {
            assert!(range.get(x).is_none());
            assert!(range.borrow(x).is_none());
        }
    }

    let elem = vec.borrow_range(5..).unwrap().borrow(1).unwrap();

    assert_eq!(*elem, 6);

    std::mem::drop(mut_ref);

    assert!(vec.borrow_mut(1).is_none()); // elem is still borrowed

    std::mem::drop(elem);
}

#[test]
fn test_try_map() {
    let mut vec: VecCell<Box<i32>> = VecCell::new();

    for x in -10..10 {
        vec.push(Box::new(x));
    }

    let ref_mut = vec.borrow_mut(5).unwrap();
    assert!(VecRefMut::try_map(ref_mut, |_value| Err::<&mut (), ()>(())).is_err());

    let ref_mut = vec.borrow_mut(5).unwrap();
    let ref_mut: Result<VecRefMut<'_, i32>, ()> = VecRefMut::try_map(ref_mut, |value| Ok(value.as_mut()));
    assert!(ref_mut.is_ok());
    assert_eq!(ref_mut.unwrap(), -5);

    let borrow = vec.borrow(6).unwrap();
    assert!(VecRef::try_map(borrow, |_value| Err::<&(), ()>(())).is_err());

    let borrow = vec.borrow(4).unwrap();
    let borrow: Result<VecRef<'_, i32>, ()> = VecRef::try_map(borrow, |value| Ok(value.as_ref()));
    assert!(borrow.is_ok());
    assert_eq!(borrow.unwrap(), -6);
}
