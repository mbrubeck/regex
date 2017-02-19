// Copyright 2017 The Rust Project Developers. See the COPYRIGHT
// file at the top-level directory of this distribution and at
// http://rust-lang.org/COPYRIGHT.
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

#![allow(dead_code, unused_variables)]
#![deny(missing_docs)]

/*!
TODO.
*/

extern crate ucd_util;

pub use parse::*;
pub use translate::*;

/// This module defines a regular expression abstract syntax.
pub mod ast;
mod either;
#[allow(missing_docs)]
pub mod hir;
#[allow(missing_docs)]
mod interval;
mod parse;
#[allow(missing_docs)]
mod translate;
mod unicode;
mod unicode_tables;
