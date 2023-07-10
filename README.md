<!-- cargo-sync-readme start -->

Packed Immutable Strings

`PackedStr` is a replacement for `Vec<String>` when the strings are all
immutable.

The benefit of using `PackedStr` is that all of the string data is stored
in a single heap allocation. This may save space compared to `Vec<String>`,
where each `String` has its own heap allocation, and associated costs (excess
`String` capacity, allocator metadata, heap fragmentation).

In addition, each `String` stores its own size and capacity, which are not
necessary due to the `PackedStr` design.

`PackedStr` is implemented as one large buffer containing all the string data,
and a list of indexes into the buffer. Each string slice can be reconstructed
from its index, and the index of the next string (or the end of the buffer,
for the last string).


<!-- cargo-sync-readme end -->
