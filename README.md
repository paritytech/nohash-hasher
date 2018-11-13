# NoHashHasher

A `NoHashHasher<T>` where `T` is one of {`u8`, `u16`, `u32`, `u64`, `usize`, `i8`,
`i16`, `i32`, `i64`, `isize`} is a *stateless* implementation of `std::hash::Hasher`
which does not actually hash at all.

By itself this hasher is largely useless, but when used in `HashMap`s whose domain
matches `T` the resulting map operations involving hashing are faster than
with any other possible hashing algorithm.

Using this hasher, one must ensure that it is never used in a stateful way,
i.e. a *single* call to `write_*` must be followed by `finish`. Multiple
write-calls will cause errors (debug builds check this and panic if a violation
of this API contract is detected).

## License

Licensed under either of

 * Apache License, Version 2.0
   ([LICENSE-APACHE](LICENSE-APACHE) or http://www.apache.org/licenses/LICENSE-2.0)
 * MIT license
   ([LICENSE-MIT](LICENSE-MIT) or http://opensource.org/licenses/MIT)

at your option.

## Contribution

Unless you explicitly state otherwise, any contribution intentionally submitted
for inclusion in the work by you, as defined in the Apache-2.0 license, shall be
dual licensed as above, without any additional terms or conditions.
