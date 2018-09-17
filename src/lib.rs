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

pub type BuildIntHasher<T> = BuildHasherDefault<IntHasher<T>>;

/// Type alias which links the `HashMap`'s key type to the `IntHasher`.
pub type IntMap<K, V> = std::collections::HashMap<K, V, BuildIntHasher<K>>;

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
    use super::*;

    #[test]
    fn ok() {
        let mut h1 = IntHasher::<u8>::default();
        h1.write_u8(42);
        assert_eq!(42, h1.finish());

        let mut h2 = IntHasher::<u16>::default();
        h2.write_u16(42);
        assert_eq!(42, h2.finish());

        let mut h3 = IntHasher::<u32>::default();
        h3.write_u32(42);
        assert_eq!(42, h3.finish());

        let mut h4 = IntHasher::<u64>::default();
        h4.write_u64(42);
        assert_eq!(42, h4.finish());

        let mut h5 = IntHasher::<usize>::default();
        h5.write_usize(42);
        assert_eq!(42, h5.finish());

        let mut h6 = IntHasher::<i8>::default();
        h6.write_i8(42);
        assert_eq!(42, h6.finish());

        let mut h7 = IntHasher::<i16>::default();
        h7.write_i16(42);
        assert_eq!(42, h7.finish());

        let mut h8 = IntHasher::<i32>::default();
        h8.write_i32(42);
        assert_eq!(42, h8.finish());

        let mut h9 = IntHasher::<i64>::default();
        h9.write_i64(42);
        assert_eq!(42, h9.finish());

        let mut h10 = IntHasher::<isize>::default();
        h10.write_isize(42);
        assert_eq!(42, h10.finish())
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u8_double_usage() {
        let mut h = IntHasher::<u8>::default();
        h.write_u8(42);
        h.write_u8(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u16_double_usage() {
        let mut h = IntHasher::<u16>::default();
        h.write_u16(42);
        h.write_u16(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u32_double_usage() {
        let mut h = IntHasher::<u32>::default();
        h.write_u32(42);
        h.write_u32(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn u64_double_usage() {
        let mut h = IntHasher::<u64>::default();
        h.write_u64(42);
        h.write_u64(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn usize_double_usage() {
        let mut h = IntHasher::<usize>::default();
        h.write_usize(42);
        h.write_usize(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i8_double_usage() {
        let mut h = IntHasher::<i8>::default();
        h.write_i8(42);
        h.write_i8(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i16_double_usage() {
        let mut h = IntHasher::<i16>::default();
        h.write_i16(42);
        h.write_i16(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i32_double_usage() {
        let mut h = IntHasher::<i32>::default();
        h.write_i32(42);
        h.write_i32(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn i64_double_usage() {
        let mut h = IntHasher::<i64>::default();
        h.write_i64(42);
        h.write_i64(43);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic]
    fn isize_double_usage() {
        let mut h = IntHasher::<isize>::default();
        h.write_isize(42);
        h.write_isize(43);
    }
}

