# array-section

[![Crates.io Version](https://img.shields.io/crates/v/array_section?logo=rust)](https://crates.io/crates/array-section)
[![docs.rs](https://img.shields.io/docsrs/array-section?logo=docs.rs)](https://docs.rs/array-section/latest/array_section/)
[![GitHub Actions Workflow Status](https://img.shields.io/github/actions/workflow/status/JSorngard/array-section/rust.yml?logo=github&label=CI)](https://github.com/JSorngard/array-section/actions/workflows/rust.yml)

When you want to return a buffer of unknown size (but smaller than some limit) from/in a const context.
This crate defines a type backed by an array where only a (contiguous) subsection of the array may be viewed.

This can be useful in const functions that wish to return an array of size `N`,
but with some elements potentially unused.

The crate is `no_std` compatible.

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

## Feature flags

`std`: lets the error type provide a [`Backtrace`](https://doc.rust-lang.org/std/backtrace/struct.Backtrace.html).
When this feature is disabled the crate is `no_std` compatible. Enables the `alloc` feature.

`alloc`: enables conversion of the array section into `Vec`s and `Box`ed slices.

## License

Licensed under either of

- Apache License, Version 2.0 ([LICENSE-APACHE](LICENSE-APACHE) or <http://www.apache.org/licenses/LICENSE-2.0>)  
- MIT license ([LICENSE-MIT](LICENSE-MIT) or <http://opensource.org/licenses/MIT>)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
