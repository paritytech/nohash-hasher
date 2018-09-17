// Copyright 2018 Parity Technologies (UK) Ltd.
//
// Permission is hereby granted, free of charge, to any person obtaining a copy of
// this software and associated documentation files (the "Software"), to deal in
// the Software without restriction, including without limitation the rights to
// use, copy, modify, merge, publish, distribute, sublicense, and/or sell copies of
// the Software, and to permit persons to whom the Software is furnished to do so,
// subject to the following conditions:
//
// The above copyright notice and this permission notice shall be included in all
// copies or substantial portions of the Software.
//
// THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
// IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY, FITNESS
// FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS
// OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY,
// WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN
// CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.

//! An implementation of `std::hash::Hasher` for usage with `HashMap`s whose domain
//! are integer types, which do not require hashing at all.

use std::{hash::{BuildHasherDefault, Hasher}, marker::PhantomData};

pub type BuildIntHasher<T> =
    BuildHasherDefault<IntHasher<T>>;

/// Type alias which links the `HashMap`'s key type to the `IntHasher`.
pub type IntMap<K, V> =
    std::collections::HashMap<K, V, BuildIntHasher<K>>;

/// An `IntHasher` is a *stateless* implementation of `Hasher` which does
/// not actually hash at all. Using this hasher, one must ensure that it is
/// never used in a stateful way, i.e. a *single* call to `write_*` must be
/// followed by `finish`. Multiple write-calls will cause errors (debug
/// builds check this and panic if a violation of this API contract is
/// detected).
#[cfg(debug_assertions)]
#[derive(Copy, Clone, Debug, Default)]
pub struct IntHasher<T>(u64, bool, PhantomData<T>);

#[cfg(not(debug_assertions))]
#[derive(Copy, Clone, Debug, Default)]
pub struct IntHasher<T>(u64, PhantomData<T>);

impl Hasher for IntHasher<u8> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_u8(&mut self, n: u8) {
        assert!(!self.1, "IntHasher::write_u8 must be used only once.");
        self.0 = u64::from(n);
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_u8(&mut self, n: u8) {
        self.0 = u64::from(n)
    }
}

impl Hasher for IntHasher<u16> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_u16(&mut self, n: u16) {
        assert!(!self.1, "IntHasher::write_u16 must be used only once.");
        self.0 = u64::from(n);
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_u16(&mut self, n: u16) {
        self.0 = u64::from(n)
    }
}

impl Hasher for IntHasher<u32> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_u32(&mut self, n: u32) {
        assert!(!self.1, "IntHasher::write_u32 must be used only once.");
        self.0 = u64::from(n);
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_u32(&mut self, n: u32) {
        self.0 = u64::from(n)
    }
}

impl Hasher for IntHasher<u64> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_u64(&mut self, n: u64) {
        assert!(!self.1, "IntHasher::write_u64 must be used only once.");
        self.0 = n;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_u64(&mut self, n: u64) {
        self.0 = n
    }
}

impl Hasher for IntHasher<usize> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_usize(&mut self, n: usize) {
        assert!(!self.1, "IntHasher::write_usize must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_usize(&mut self, n: usize) {
        self.0 = n as u64
    }
}

impl Hasher for IntHasher<i8> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_i8(&mut self, n: i8) {
        assert!(!self.1, "IntHasher::write_i8 must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_i8(&mut self, n: i8) {
        self.0 = n as u64
    }
}

impl Hasher for IntHasher<i16> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_i16(&mut self, n: i16) {
        assert!(!self.1, "IntHasher::write_i16 must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_i16(&mut self, n: i16) {
        self.0 = n as u64
    }
}

impl Hasher for IntHasher<i32> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_i32(&mut self, n: i32) {
        assert!(!self.1, "IntHasher::write_i32 must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_i32(&mut self, n: i32) {
        self.0 = n as u64
    }
}

impl Hasher for IntHasher<i64> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_i64(&mut self, n: i64) {
        assert!(!self.1, "IntHasher::write_i64 must be used only once.");
        self.0 = n as u64;
        self.1 = true
    }
    #[cfg(not(debug_assertions))]
    fn write_i64(&mut self, n: i64) {
        self.0 = n as u64
    }
}

impl Hasher for IntHasher<isize> {
    fn finish(&self) -> u64 {
        self.0
    }
    fn write(&mut self, _: &[u8]) {
        panic!("Invalid use of IntHasher")
    }
    #[cfg(debug_assertions)]
    fn write_isize(&mut self, n: isize) {
        assert!(!self.1, "IntHasher::write_isize must be used only once.");
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
    use std::hash::BuildHasher;
    use super::*;

    #[test]
    fn u8() {
        let mut h = BuildIntHasher::<u8>::default().build_hasher();
        h.write_u8(42);
        assert_eq!(42, h.finish())
    }

    #[test]
    fn u16() {
        let mut h = BuildIntHasher::<u16>::default().build_hasher();
        h.write_u16(42);
        assert_eq!(42, h.finish())
    }

    #[test]
    fn u32() {
        let mut h = BuildIntHasher::<u32>::default().build_hasher();
        h.write_u32(42);
        assert_eq!(42, h.finish())
    }

    #[test]
    fn u64() {
        let mut h = BuildIntHasher::<u64>::default().build_hasher();
        h.write_u64(42);
        assert_eq!(42, h.finish())
    }

    #[test]
    fn usize() {
        let mut h = BuildIntHasher::<usize>::default().build_hasher();
        h.write_usize(42);
        assert_eq!(42, h.finish())
    }

    #[test]
    fn i8() {
        let mut h = BuildIntHasher::<i8>::default().build_hasher();
        h.write_i8(42);
        assert_eq!(42, h.finish())
    }

    #[test]
    fn i16() {
        let mut h = BuildIntHasher::<i16>::default().build_hasher();
        h.write_i16(42);
        assert_eq!(42, h.finish())
    }

    #[test]
    fn i32() {
        let mut h = BuildIntHasher::<i32>::default().build_hasher();
        h.write_i32(42);
        assert_eq!(42, h.finish())
    }

    #[test]
    fn i64() {
        let mut h = BuildIntHasher::<i64>::default().build_hasher();
        h.write_i64(42);
        assert_eq!(42, h.finish())
    }

    #[test]
    fn isize() {
        let mut h = BuildIntHasher::<isize>::default().build_hasher();
        h.write_isize(42);
        assert_eq!(42, h.finish())
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u8_panic() {
        let mut h = BuildIntHasher::<u8>::default().build_hasher();
        h.write_u8(42);
        h.write_u8(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u16_panic() {
        let mut h = BuildIntHasher::<u16>::default().build_hasher();
        h.write_u16(42);
        h.write_u16(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u32_panic() {
        let mut h = BuildIntHasher::<u32>::default().build_hasher();
        h.write_u32(42);
        h.write_u32(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u64_panic() {
        let mut h = BuildIntHasher::<u64>::default().build_hasher();
        h.write_u64(42);
        h.write_u64(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn usize_panic() {
        let mut h = BuildIntHasher::<usize>::default().build_hasher();
        h.write_usize(42);
        h.write_usize(43);
    }
}
