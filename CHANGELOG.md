This document contains the changes to the crate since version 0.1.9.

# 0.2.0

 - Add a `backtrace` function to `TryFromArraySectionError`.

## Breaking changes

 - The `TryFromArraySectionError` type no longer implements `Clone` and `Copy`.