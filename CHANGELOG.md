# Changelog

This document contains the changes to the crate since version 0.1.9.

## 0.2.1

- Make the crate derive the `Error` trait even in `no_std`.

## 0.2.0

- Add a `backtrace` function to `TryFromArraySectionError`.

### Breaking changes

- The `TryFromArraySectionError` type no longer implements `Clone` and `Copy`.
