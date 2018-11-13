// Copyright 2018 Parity Technologies (UK) Ltd.
//
// Licensed under the Apache License, Version 2.0 or MIT license, at your option.
//
// A copy of the Apache License, Version 2.0 is included in the software as
// LICENSE-APACHE and a copy of the MIT license is included in the software
// as LICENSE-MIT. You may also obtain a copy of the Apache License, Version 2.0
// at https://www.apache.org/licenses/LICENSE-2.0 and a copy of the MIT license
// at https://opensource.org/licenses/MIT.

use std::{hash::{BuildHasherDefault, Hasher}, marker::PhantomData};

/// A `HashMap` with an integer domain, using `NoHashHasher` to perform no hashing at all.
pub type IntMap<K, V> = std::collections::HashMap<K, V, BuildNoHashHasher<K>>;

/// A `HashSet` of integers, using `NoHashHasher` to perform no hashing at all.
pub type IntSet<T> = std::collections::HashSet<T, BuildNoHashHasher<T>>;

/// An alias for `BuildHasherDefault` for use with `NoHashHasher`.
pub type BuildNoHashHasher<T> = BuildHasherDefault<NoHashHasher<T>>;

/// A `NoHashHasher<T>` where `T` is one of
/// {`u8`, `u16`, `u32`, `u64`, `usize`, `i8`, `i16`, `i32`, `i64`, `isize`}
/// is a *stateless* implementation of `Hasher` which does not actually hash at all.
/// By itself this hasher is largely useless, but when used in `HashMap`s whose domain
/// matches `T` the resulting map operations involving hashing are faster than
/// with any other possible hashing algorithm.
///
/// Using this hasher, one must ensure that it is never used in a stateful way,
/// i.e. a *single* call to `write_*` must be followed by `finish`. Multiple
/// write-calls will cause errors (debug builds check this and panic if a violation
/// of this API contract is detected).
#[cfg(debug_assertions)]
#[derive(Copy, Clone, Debug, Default)]
pub struct NoHashHasher<T>(u64, bool, PhantomData<T>);

#[cfg(not(debug_assertions))]
#[derive(Copy, Clone, Debug, Default)]
pub struct NoHashHasher<T>(u64, PhantomData<T>);

impl Hasher for NoHashHasher<u8> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_u8(&mut self, n: u8) {
        assert!(!self.1, "NoHashHasher::write_u8 must be used only once.");
        self.0 = u64::from(n);
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_u8(&mut self, n: u8) {
        self.0 = u64::from(n)
    }
}

impl Hasher for NoHashHasher<u16> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_u16(&mut self, n: u16) {
        assert!(!self.1, "NoHashHasher::write_u16 must be used only once.");
        self.0 = u64::from(n);
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_u16(&mut self, n: u16) {
        self.0 = u64::from(n)
    }
}

impl Hasher for NoHashHasher<u32> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_u32(&mut self, n: u32) {
        assert!(!self.1, "NoHashHasher::write_u32 must be used only once.");
        self.0 = u64::from(n);
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_u32(&mut self, n: u32) {
        self.0 = u64::from(n)
    }
}

impl Hasher for NoHashHasher<u64> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_u64(&mut self, n: u64) {
        assert!(!self.1, "NoHashHasher::write_u64 must be used only once.");
        self.0 = n;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_u64(&mut self, n: u64) {
        self.0 = n
    }
}

impl Hasher for NoHashHasher<usize> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_usize(&mut self, n: usize) {
        assert!(!self.1, "NoHashHasher::write_usize must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_usize(&mut self, n: usize) {
        self.0 = n as u64
    }
}

impl Hasher for NoHashHasher<i8> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_i8(&mut self, n: i8) {
        assert!(!self.1, "NoHashHasher::write_i8 must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_i8(&mut self, n: i8) {
        self.0 = n as u64
    }
}

impl Hasher for NoHashHasher<i16> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_i16(&mut self, n: i16) {
        assert!(!self.1, "NoHashHasher::write_i16 must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_i16(&mut self, n: i16) {
        self.0 = n as u64
    }
}

impl Hasher for NoHashHasher<i32> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_i32(&mut self, n: i32) {
        assert!(!self.1, "NoHashHasher::write_i32 must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_i32(&mut self, n: i32) {
        self.0 = n as u64
    }
}

impl Hasher for NoHashHasher<i64> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_i64(&mut self, n: i64) {
        assert!(!self.1, "NoHashHasher::write_i64 must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_i64(&mut self, n: i64) {
        self.0 = n as u64
    }
}

impl Hasher for NoHashHasher<isize> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of NoHashHasher")
    }
    #[cfg(debug_assertions)]
    fn write_isize(&mut self, n: isize) {
        assert!(!self.1, "NoHashHasher::write_isize must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_isize(&mut self, n: isize) {
        self.0 = n as u64
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn ok() {
        let mut h1 = NoHashHasher::<u8>::default();
        h1.write_u8(42);
        assert_eq!(42, h1.finish());

        let mut h2 = NoHashHasher::<u16>::default();
        h2.write_u16(42);
        assert_eq!(42, h2.finish());

        let mut h3 = NoHashHasher::<u32>::default();
        h3.write_u32(42);
        assert_eq!(42, h3.finish());

        let mut h4 = NoHashHasher::<u64>::default();
        h4.write_u64(42);
        assert_eq!(42, h4.finish());

        let mut h5 = NoHashHasher::<usize>::default();
        h5.write_usize(42);
        assert_eq!(42, h5.finish());

        let mut h6 = NoHashHasher::<i8>::default();
        h6.write_i8(42);
        assert_eq!(42, h6.finish());

        let mut h7 = NoHashHasher::<i16>::default();
        h7.write_i16(42);
        assert_eq!(42, h7.finish());

        let mut h8 = NoHashHasher::<i32>::default();
        h8.write_i32(42);
        assert_eq!(42, h8.finish());

        let mut h9 = NoHashHasher::<i64>::default();
        h9.write_i64(42);
        assert_eq!(42, h9.finish());

        let mut h10 = NoHashHasher::<isize>::default();
        h10.write_isize(42);
        assert_eq!(42, h10.finish())
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u8_double_usage() {
        let mut h = NoHashHasher::<u8>::default();
        h.write_u8(42);
        h.write_u8(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u16_double_usage() {
        let mut h = NoHashHasher::<u16>::default();
        h.write_u16(42);
        h.write_u16(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u32_double_usage() {
        let mut h = NoHashHasher::<u32>::default();
        h.write_u32(42);
        h.write_u32(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u64_double_usage() {
        let mut h = NoHashHasher::<u64>::default();
        h.write_u64(42);
        h.write_u64(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn usize_double_usage() {
        let mut h = NoHashHasher::<usize>::default();
        h.write_usize(42);
        h.write_usize(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i8_double_usage() {
        let mut h = NoHashHasher::<i8>::default();
        h.write_i8(42);
        h.write_i8(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i16_double_usage() {
        let mut h = NoHashHasher::<i16>::default();
        h.write_i16(42);
        h.write_i16(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i32_double_usage() {
        let mut h = NoHashHasher::<i32>::default();
        h.write_i32(42);
        h.write_i32(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i64_double_usage() {
        let mut h = NoHashHasher::<i64>::default();
        h.write_i64(42);
        h.write_i64(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn isize_double_usage() {
        let mut h = NoHashHasher::<isize>::default();
        h.write_isize(42);
        h.write_isize(43);
    }
}

