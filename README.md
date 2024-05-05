# array-section

An array where only a (contiguous) subsection of the array may be viewed.

This can be useful in const functions that wish to return an array of size `N`,
but with some elements potentially unused.

`#![no_std]` compatible

 ```rust
/// Returns an array of the square numbers smaller than both x and N.
const fn squares_smaller_than<const N: usize>(x: usize) -> ArraySection<usize, N> {
    let mut i = 0;
    let mut ans = [0; N];
    while i * i < N && i * i < x {
        ans[i] = i * i;
        i += 1;
    }
    ArraySection::new(ans, 0..i)
}
assert_eq!(squares_smaller_than::<10>(16), [0, 1, 4, 9]);
```

## Features
`std`: derives the `Error` trait for the error types.  
`alloc`: enables conversion of the array section into `Vec`s and `Box`ed slices.
