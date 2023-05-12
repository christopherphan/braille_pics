// This file is part of braille_pics
// Copyright © 2023, Christopher Phan <https://chrisphan.com>
//
// Offered under your choice of MIT or Apache-2.0 licenses.
// (See the files LICENSE-MIT.txt and LICENSE-APACHE-2.0.txt in root directory of this repository.)
//
//
//! # braille_pics
//!
//! `braille_pics` provides a struct, `BraillePic`, to represent and produce text-art made of
//! Braille characers.
//!
//! License: MIT OR Apache-2.0

/* TO DO:
 *
 * - Add tests
 * - Better comments!
 *
 * */

use std::cmp;
use std::fmt;
use std::ops;

/* This constant array is used in the function BraillePic::_raw_braille_remap.
 * See the long comment before that function for an explaination. */
const BRAILLE_POS: [usize; 8] = [7, 6, 5, 2, 4, 1, 3, 0];

/// Representation of a text-art picture made of Braille characters.
///
/// Implements the `Display` trait to produce the text-art as a `String`.
///
/// # Examples
///
/// ```
/// use braille_pics::BraillePic;
///
/// let bp = BraillePic::from_func(|(x, y)| x + y <= 11, 12, 12);
/// let s = (
///     "⣿⣿⣿⣿⡿⠋\n".to_owned() +
///     "⣿⣿⡿⠋⠀⠀\n" +
///     "⡿⠋⠀⠀⠀⠀"
/// ); // Blank spaces are U+2800, not U+0020
/// assert_eq!(
///     (
///         "\u{28ff}\u{28ff}\u{28ff}\u{28ff}\u{287f}\u{280b}\n".to_owned() +
///         "\u{28ff}\u{28ff}\u{287f}\u{280b}\u{2800}\u{2800}\n" +
///         "\u{287f}\u{280b}\u{2800}\u{2800}\u{2800}\u{2800}"
///     ),
///     s
/// );
/// assert_eq!(bp.to_string(), s);
///
///
/// let house_s = (
///     "⣠⣊⣢⡀\n".to_owned() +
///     "⢸⣀⣸\u{2800}"
/// );
/// let house_bp = BraillePic::from_data(
///     &[
///         0b00000111, 0b01100011, 0b00100111, 0b00000010,
///         0b01010101, 0b00000011, 0b01010111, 0
///     ],
///     4
/// );
/// assert_eq!(house_bp.to_string(), house_s);
///
///
/// /* Make an image of the Mandelbrot set */
///
/// let mandelbrot_bp = BraillePic::from_func(
///     |(col, row)| {
///         let c: (f64, f64) = (
///             // Representing the complex number a + bi as (a, b)
///             3.0 * (col as f64) / 120.0 - 2.0, // viewing window: [-2, 1] x [-1, 1]
///             -2.0 * (row as f64) / 100.0 + 1.0, // 120 bits x 100 bits
///         );
///         let mut z: (f64, f64) = (0.0, 0.0);
///         for _ in 0..500 {
///             z = (z.0 * z.0 - z.1 * z.1 + c.0, 2.0 * z.0 * z.1 + c.1); // z = z**2 + c
///             if z.0 * z.0 + z.1 * z.1 >= 16.0 {
///                 // test bailout condition |z|**2 >= 16
///                 return false;
///             }
///         }
///         true // assume bounded
///     },
///     120,
///     100,
/// );
///
/// let mandelbrot_s = (
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n".to_owned() +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣴⣶⣶⡄⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣿⣿⣿⡗⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⡀⣀⣠⣬⣿⣯⣤⣀⡀⢀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢼⣷⣠⣶⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣦⡀⣴⣤⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣴⣾⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣟⠃⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢙⣾⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣧⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢐⣾⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡾⠂⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣶⣠⣤⣧⣤⣀⠀⠀⠀⣽⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣧⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣰⣿⣿⣿⣿⣿⣿⣧⡀⢰⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣟⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢰⣿⣿⣿⣿⣿⣿⣿⣿⣷⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠃⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⣿⣿⣾⣿⣿⣿⣿⣿⣿⣿⣿⣿⢼⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣟⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠉⠉⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣷⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢻⣿⣿⣿⣿⣿⣿⡿⠃⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣗⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣿⠻⠿⡿⠿⠛⠁⠀⠀⢿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡿⠂⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠁⠀⠀⠀⠀⠀⢙⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣧⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢘⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡿⠈⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠉⠈⢿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣟⡁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢴⣾⠻⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡿⠋⢿⠷⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠁⠀⠐⠋⠛⠻⠿⣿⡿⠿⠛⠋⠙⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣾⣿⣿⣆⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢿⣿⣿⠇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠰⠂⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀"
/// ); // Blank spaces are U+2800, not U+0020
///
/// assert_eq!(mandelbrot_bp.to_string(), mandelbrot_s);
///
/// /* Bitwise and, or, xor, not all operate on individual dots. */
///
/// let bp2a = BraillePic::from_func(|(x, _)| x < 6, 12, 8);
/// let s2a = (
///     "⣿⣿⣿⠀⠀⠀\n".to_owned() +
///     "⣿⣿⣿⠀⠀⠀"
/// ); // Blank spaces are U+2800, not U+0020
/// assert_eq!(
///     (
///         "\u{28ff}\u{28ff}\u{28ff}\u{2800}\u{2800}\u{2800}\n".to_owned() +
///         "\u{28ff}\u{28ff}\u{28ff}\u{2800}\u{2800}\u{2800}"
///     ),
///     s2a
/// );
/// assert_eq!(bp2a.to_string(), s2a);
///
/// let bp2b = BraillePic::from_func(|(_, y)| y < 4, 12, 8);
/// let s2b = (
///     "⣿⣿⣿⣿⣿⣿\n".to_owned() +
///     "⠀⠀⠀⠀⠀⠀"
/// ); // Blank spaces are U+2800, not U+0020
/// assert_eq!(
///     (
///         "\u{28ff}\u{28ff}\u{28ff}\u{28ff}\u{28ff}\u{28ff}\n".to_owned() +
///         "\u{2800}\u{2800}\u{2800}\u{2800}\u{2800}\u{2800}"
///     ),
///     s2b
/// );
/// assert_eq!(bp2b.to_string(), s2b);
///
///
/// let bp2a_and_b = BraillePic::from_func(|(x, y)| x < 6 && y < 4, 12, 8);
/// assert_eq!(bp2a.clone() & bp2b.clone(), bp2a_and_b);
/// let s2a_and_b = (
///     "⣿⣿⣿⠀⠀⠀\n".to_owned() +
///     "⠀⠀⠀⠀⠀⠀"
/// ); // Blank spaces are U+2800, not U+0020
/// assert_eq!(
///     (
///         "\u{28ff}\u{28ff}\u{28ff}\u{2800}\u{2800}\u{2800}\n".to_owned() +
///         "\u{2800}\u{2800}\u{2800}\u{2800}\u{2800}\u{2800}"
///     ),
///     s2a_and_b
/// );
/// assert_eq!((bp2a.clone() & bp2b.clone()).to_string(), s2a_and_b);
///
/// let bp2a_or_b = BraillePic::from_func(|(x, y)| x < 6 || y < 4, 12, 8);
/// assert_eq!(bp2a.clone() | bp2b.clone(), bp2a_or_b);
/// let s2a_or_b = (
///     "⣿⣿⣿⣿⣿⣿\n".to_owned() +
///     "⣿⣿⣿⠀⠀⠀"
/// ); // Blank spaces are U+2800, not U+0020
/// assert_eq!(
///     (
///         "\u{28ff}\u{28ff}\u{28ff}\u{28ff}\u{28ff}\u{28ff}\n".to_owned() +
///         "\u{28ff}\u{28ff}\u{28ff}\u{2800}\u{2800}\u{2800}"
///     ),
///     s2a_or_b
/// );
/// assert_eq!((bp2a.clone() | bp2b.clone()).to_string(), s2a_or_b);
///
/// let bp2a_xor_b = BraillePic::from_func(|(x, y)| (x < 6 && y >= 4) || (x >=6 && y < 4), 12, 8);
/// assert_eq!(bp2a.clone() ^ bp2b.clone(), bp2a_xor_b);
/// let s2a_xor_b = (
///     "⠀⠀⠀⣿⣿⣿\n".to_owned() +
///     "⣿⣿⣿⠀⠀⠀"
/// ); // Blank spaces are U+2800, not U+0020
/// assert_eq!(
///     (
///         "\u{2800}\u{2800}\u{2800}\u{28ff}\u{28ff}\u{28ff}\n".to_owned() +
///         "\u{28ff}\u{28ff}\u{28ff}\u{2800}\u{2800}\u{2800}"
///     ),
///     s2a_xor_b
/// );
/// assert_eq!((bp2a.clone() ^ bp2b.clone()).to_string(), s2a_xor_b);
///
/// let not_bp2a = BraillePic::from_func(|(x, _)| x >= 6, 12, 8);
/// assert_eq!(!bp2a.clone(), not_bp2a);
/// let s2not_a = (
///     "⠀⠀⠀⣿⣿⣿\n".to_owned() +
///     "⠀⠀⠀⣿⣿⣿"
/// ); // Blank spaces are U+2800, not U+0020
/// assert_eq!(
///     (
///         "\u{2800}\u{2800}\u{2800}\u{28ff}\u{28ff}\u{28ff}\n".to_owned() +
///         "\u{2800}\u{2800}\u{2800}\u{28ff}\u{28ff}\u{28ff}"
///     ),
///     s2not_a
/// );
/// assert_eq!((!bp2a.clone()).to_string(), s2not_a);
/// ```
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct BraillePic {
    width: usize, // number of Braille chars, i.e. (true width) / 2
    data: Vec<u8>, // each integer represents 4-row by 2-column rectangle of bits, i.e. a
                  // Braille character
}

impl BraillePic {
    /// Creates a new blank `BraillePic` object of the specified size.
    ///
    /// Note that `width` and `height` are given in characters, not dots.
    ///
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    ///
    /// let bp = BraillePic::new(5, 5);
    ///
    /// assert_eq!(bp.char_dimensions(), (5, 5));
    /// assert_eq!(bp.bit_dimensions(), (10, 20));
    ///
    /// let s = ("\u{2800}".repeat(5) + "\n").repeat(4) + &"\u{2800}".repeat(5);
    /// assert_eq!(bp.to_string(), s);
    ///
    /// for r in 0..20 {
    ///     for c in 0..10 {
    ///         assert!(!bp.get_bit(c, r));
    ///     }
    /// }
    /// ```
    pub fn new(width: usize, height: usize) -> Self {
        let data: Vec<u8> = (0..width * height).map(|_| 0).collect();
        Self { width, data }
    }

    /* Returns the height of the BraillePic in characters */
    fn _char_height(&self) -> usize {
        self.data.len() / self.width + usize::from(self.data.len() % self.width > 0)
    }

    /// Returns the dimensions (width, height) of the picture in characters.
    ///
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    ///
    /// let bp = BraillePic::from_func(|(x, y)| x + y <= 11, 12, 12);
    /// let s = (
    ///     "\u{28ff}\u{28ff}\u{28ff}\u{28ff}\u{287f}\u{280b}\n".to_owned() +
    ///     "\u{28ff}\u{28ff}\u{287f}\u{280b}\u{2800}\u{2800}\n" +
    ///     "\u{287f}\u{280b}\u{2800}\u{2800}\u{2800}\u{2800}"
    /// );
    /// assert_eq!(bp.to_string(), s);
    /// assert_eq!(bp.char_dimensions(), (6, 3));
    ///
    ///
    /// let bp2 = BraillePic::new(70, 24);
    /// assert_eq!(bp2.char_dimensions(), (70, 24));
    /// ```
    pub fn char_dimensions(&self) -> (usize, usize) {
        (self.width, self._char_height())
    }

    /// Returns the dimensions (width, height) of the picture in dots.
    ///
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    ///
    /// let bp = BraillePic::from_func(|(x, y)| x + y <= 11, 12, 12);
    /// let s = (
    ///     "\u{28ff}\u{28ff}\u{28ff}\u{28ff}\u{287f}\u{280b}\n".to_owned() +
    ///     "\u{28ff}\u{28ff}\u{287f}\u{280b}\u{2800}\u{2800}\n" +
    ///     "\u{287f}\u{280b}\u{2800}\u{2800}\u{2800}\u{2800}"
    /// );
    /// assert_eq!(bp.to_string(), s);
    /// assert_eq!(bp.bit_dimensions(), (12, 12));
    ///
    /// let bp2 = BraillePic::new(20, 30);
    ///
    /// assert_eq!(bp2.bit_dimensions(), (40, 120));
    /// ```
    pub fn bit_dimensions(&self) -> (usize, usize) {
        (self.width * 2, self._char_height() * 4)
    }

    /* Given coordinates (in characters), returns the corresponding position in the data vector. */
    fn _coords_to_data_pos(&self, col: usize, row: usize) -> Option<usize> {
        if col >= self.width || row >= self._char_height() {
            return None;
        }
        Some(row * self.width + col)
    }

    /// Returns the raw data at a given position in the picture.
    ///
    /// If the position is outside the dimensions of the picture, `0_u8` is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    /// let house_s = (
    ///     "⣠⣊⣢⡀\n".to_owned() +
    ///     "⢸⣀⣸\u{2800}"
    /// );
    /// let house_bp = BraillePic::from_data(
    ///     &[
    ///         0b00000111, 0b01100011, 0b00100111, 0b00000010,
    ///         0b01010101, 0b00000011, 0b01010111, 0
    ///     ],
    ///     4
    /// );
    /// assert_eq!(house_bp.to_string(), house_s);
    ///
    /// assert_eq!(house_bp.get_data(2, 0), 0b00100111);
    /// assert_eq!(house_bp.get_data(8, 0), 0); // out of bounds
    /// ```
    pub fn get_data(&self, col: usize, row: usize) -> u8 {
        match self._coords_to_data_pos(col, row) {
            Some(k) => *self.data.get(k).unwrap_or(&0),
            None => 0,
        }
    }

    /// Returns the value of the bit (as a `bool`) at given position (given in terms of dots, not
    /// characters).
    ///
    /// If the position is outside the dimensions of the picture, then `false` is returned.
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    /// let house_s = (
    ///     "⣠⣊⣢⡀\n".to_owned() +
    ///     "⢸⣀⣸\u{2800}"
    /// );
    /// let house_bp = BraillePic::from_data(
    ///     &[
    ///         0b00000111, 0b01100011, 0b00100111, 0b00000010,
    ///         0b01010101, 0b00000011, 0b01010111, 0
    ///     ],
    ///     4
    /// );
    /// assert_eq!(house_bp.to_string(), house_s);
    ///
    /// assert!(house_bp.get_bit(3, 0));
    /// assert!(house_bp.get_bit(4, 3));
    /// assert!(!(house_bp.get_bit(4, 5)));
    /// assert!(!(house_bp.get_bit(20, 6))); // out of bounds
    /// ```
    pub fn get_bit(&self, bit_col: usize, bit_row: usize) -> bool {
        if let Some((pos, bitpos)) = self._bit_coords_to_data_pos(bit_col, bit_row) {
            (self.data.get(pos).unwrap_or(&0_u8) >> bitpos) % 2 == 1
        } else {
            false
        }
    }

    /// Returns the Unicode codepoint for the Braille character at a given position in the picture.
    ///
    /// The Braille characters have codepoints between U+2800 and U+28FF, inclusively. _However_,
    /// the mapping from codepoints to bits in each character is different than how they are stored
    /// as data.
    ///
    /// If the position is outside the dimensions of the picture, `0x2800_u32` (the codepoint for
    /// the blank Braille characer) is returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    ///
    /// let house_s = (
    ///     "⣠⣊⣢⡀\n".to_owned() +
    ///     "⢸⣀⣸\u{2800}"
    /// );
    /// let house_bp = BraillePic::from_data(
    ///     &[
    ///         0b00000111, 0b01100011, 0b00100111, 0b00000010,
    ///         0b01010101, 0b00000011, 0b01010111, 0
    ///     ],
    ///     4
    /// );
    /// assert_eq!(house_bp.to_string(), house_s);
    ///
    /// assert_eq!(house_bp.get_codepoint(2, 1), 0x28f8);
    /// assert_eq!(house_bp.get_codepoint(0, 0), 0x28e0);
    /// assert_eq!(house_bp.get_codepoint(5, 0), 0x2800); // out of bounds
    /// ```
    pub fn get_codepoint(&self, col: usize, row: usize) -> u32 {
        0x2800 + Self::_raw_braille_remap(self.get_data(col, row))
    }

    /// Returns the Braille character at a given position in the picture.
    ///
    /// If the position is outside the dimensions, the blank Braille character (`⠀`, U+2800) is
    /// returned.
    ///
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    ///
    /// let house_s = (
    ///     "⣠⣊⣢⡀\n".to_owned() +
    ///     "⢸⣀⣸\u{2800}"
    /// );
    /// let house_bp = BraillePic::from_data(
    ///     &[
    ///         0b00000111, 0b01100011, 0b00100111, 0b00000010,
    ///         0b01010101, 0b00000011, 0b01010111, 0
    ///     ],
    ///     4
    /// );
    /// assert_eq!(house_bp.to_string(), house_s);
    ///
    /// assert_eq!(house_bp.get_char(2, 1), '⣸');
    /// assert_eq!(house_bp.get_char(0, 0), '⣠');
    /// assert_eq!(house_bp.get_char(5, 0), '\u{2800}'); // out of bounds
    /// ```
    pub fn get_char(&self, col: usize, row: usize) -> char {
        char::from_u32(self.get_codepoint(col, row))
            .expect("will be valid codepoint because it lands between 0x2800 and 0x28ff")
    }

    /* Converts a function f: [0, 4] x [0, 2] -> {0, 1} into a u8 data element */
    fn _bools_to_data<F>(func: F) -> u8
    where
        F: Fn((u8, u8)) -> bool,
    {
        let mut output: u8 = 0;
        for row in 0..4 {
            for col in 0..2 {
                output <<= 1;
                output += u8::from(func((col, row)));
            }
        }
        output
    }

    /* Converts a position in the data vector to coordinates in bits */
    fn _pos_to_offset(pos: usize, width: usize) -> (usize, usize) {
        (2 * (pos % width), 4 * (pos / width))
    }

    /* Converts coordinates in bits to a position in the data vector */
    fn _bit_coords_to_data_pos(&self, bit_col: usize, bit_row: usize) -> Option<(usize, usize)> {
        /* output: (position, bit number) (0 is least significant) */
        if bit_col / 2 < self.width && bit_row / 4 < self._char_height() {
            Some((
                (bit_row / 4) * self.width + (bit_col / 2),
                2 * (3 - (bit_row % 4)) + 1 - bit_col % 2,
            ))
        } else {
            None
        }
    }

    /* In Unicode, the Braille characters occupy codepoints between 0x2800 and 0x28ff,
     * inclusive. However, the dot positions are not intuitive:
     *
     *  ┌─────────┐
     *  │ ┌─┐ ┌─┐ │
     *  │ │1│ │4│ │
     *  │ └─┘ └─┘ │            Code point for characters:
     *  │ ┌─┐ ┌─┐ │
     *  │ │2│ │5│ │   Suppose a[j] = 0 if dot j is not raised or j == 0, 1 if
     *  │ └─┘ └─┘ │      dot j is raised. Then the code point is:
     *  │ ┌─┐ ┌─┐ │
     *  │ │3│ │6│ │       0x2800
     *  │ └─┘ └─┘ │           + (1..9)
     *  │ ┌─┐ ┌─┐ │               .map(|j| a[j] as u32 * 2_u32.pow((j - 1) as u32))
     *  │ │7│ │8│ │               .sum::<u32>()
     *  │ └─┘ └─┘ │
     *  └─────────┘
     *
     *  The dot numbers come from the Unicode descriptions, e.g.
     *  e.g. ⢏ is BRAILLE PATTERN DOTS-12348 and is at codepoint
     *  0x2800 + 0b10001111 = 0x288F.
     *
     *  If we relabel the dots by the power of two they contribute to the codepoint,
     *  i.e. dot j raised means adding 2.pow(j) to the codepoint, we get:
     *
     *  ┌─────────┐
     *  │ ┌─┐ ┌─┐ │
     *  │ │0│ │3│ │
     *  │ └─┘ └─┘ │
     *  │ ┌─┐ ┌─┐ │
     *  │ │1│ │4│ │
     *  │ └─┘ └─┘ │
     *  │ ┌─┐ ┌─┐ │
     *  │ │2│ │5│ │
     *  │ └─┘ └─┘ │
     *  │ ┌─┐ ┌─┐ │
     *  │ │6│ │7│ │
     *  │ └─┘ └─┘ │
     *  └─────────┘
     *
     *  (A good reference for this is Wikipedia: https://en.wikipedia.org/wiki/Braille_Patterns )
     *
     *  For the data vector, we use this arrangment instead (with the convention in the above
     *  diagram, i.e. dot j raised means adding 2.pow(j)):
     *
     *  ┌─────────┐
     *  │ ┌─┐ ┌─┐ │
     *  │ │7│ │6│ │
     *  │ └─┘ └─┘ │
     *  │ ┌─┐ ┌─┐ │
     *  │ │5│ │4│ │
     *  │ └─┘ └─┘ │
     *  │ ┌─┐ ┌─┐ │
     *  │ │3│ │2│ │
     *  │ └─┘ └─┘ │
     *  │ ┌─┐ ┌─┐ │
     *  │ │1│ │0│ │
     *  │ └─┘ └─┘ │
     *  └─────────┘
     *
     *  e.g. ⢏ has (new labelling) dots 0, 3, 5, 6, and 7 raised, so it would be represented by
     *  0b11101001 = 0xe9.
     *
     *  This function converts between the convention used in the data vector and the Unicode
     *  codepoints.
     * */
    fn _raw_braille_remap(raw: u8) -> u32 {
        let mut output: u32 = 0;
        for (k, shift) in BRAILLE_POS.iter().enumerate() {
            output += (((raw >> k) % 2) as u32) << shift
        }
        output
    }

    /* Converts from the convention used in the data vector to the Braille character itself */
    fn _raw_to_braille(raw: u8) -> char {
        char::from_u32(0x2800 + Self::_raw_braille_remap(raw)).expect(
            "will land between 0x2800 and 0x28ff, inclusive, which are all valid codepoints",
        )
    }

    /// Creates a `BraillePic` object from a slice of `u8` values representing the raised dots in
    /// each character.
    ///
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    ///
    /// let house_s = (
    ///     "⣠⣊⣢⡀\n".to_owned() +
    ///     "⢸⣀⣸\u{2800}"
    /// );
    /// let house_bp = BraillePic::from_data(
    ///     &[
    ///         0b00000111, 0b01100011, 0b00100111, 0b00000010,
    ///         0b01010101, 0b00000011, 0b01010111, 0
    ///     ],
    ///     4
    /// );
    ///
    /// assert_eq!(house_bp.to_string(), house_s);
    /// ```
    pub fn from_data(raw_data: &[u8], width: usize) -> Self {
        let data: Vec<u8> = raw_data.to_vec();
        Self { width, data }
    }

    /// Creates a `BraillePic` object from a vector of `u8` values representing the raised dots in
    /// each character.
    ///
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    ///
    /// let house_s = (
    ///     "⣠⣊⣢⡀\n".to_owned() +
    ///     "⢸⣀⣸\u{2800}"
    /// );
    /// let house_bp = BraillePic::from_data_vec(
    ///     vec![
    ///         0b00000111, 0b01100011, 0b00100111, 0b00000010,
    ///         0b01010101, 0b00000011, 0b01010111, 0
    ///     ],
    ///     4
    /// );
    ///
    /// assert_eq!(house_bp.to_string(), house_s);
    /// ```
    pub fn from_data_vec(data: Vec<u8>, width: usize) -> Self {
        Self { width, data }
    }

    /// Creates a `BraillePic` object from a function or closure. The _dot_ at `(col, row)` is
    /// raised if `func((col, row)) == true`.
    ///
    /// # Examples
    ///
    /// ```
    /// use braille_pics::BraillePic;
    ///
    /// let bp = BraillePic::from_func(|(x, y)| x + y <= 11, 12, 12);
    /// let s = (
    ///     "⣿⣿⣿⣿⡿⠋\n".to_owned() +
    ///     "⣿⣿⡿⠋⠀⠀\n" +
    ///     "⡿⠋⠀⠀⠀⠀"
    /// ); // Blank spaces are U+2800, not U+0020
    /// assert_eq!(
    ///     (
    ///         "\u{28ff}\u{28ff}\u{28ff}\u{28ff}\u{287f}\u{280b}\n".to_owned() +
    ///         "\u{28ff}\u{28ff}\u{287f}\u{280b}\u{2800}\u{2800}\n" +
    ///         "\u{287f}\u{280b}\u{2800}\u{2800}\u{2800}\u{2800}"
    ///     ),
    ///     s
    /// );
    /// assert_eq!(bp.to_string(), s);
    ///
    /// /* Make an image of the Mandelbrot set */
    ///
    /// let mandelbrot_bp = BraillePic::from_func(
    ///     |(col, row)| {
    ///         let c: (f64, f64) = (
    ///             // Representing the complex number a + bi as (a, b)
    ///             3.0 * (col as f64) / 120.0 - 2.0, // viewing window: [-2, 1] x [-1, 1]
    ///             -2.0 * (row as f64) / 100.0 + 1.0, // 120 bits x 100 bits
    ///         );
    ///         let mut z: (f64, f64) = (0.0, 0.0);
    ///         for _ in 0..500 {
    ///             z = (z.0 * z.0 - z.1 * z.1 + c.0, 2.0 * z.0 * z.1 + c.1); // z = z**2 + c
    ///             if z.0 * z.0 + z.1 * z.1 >= 16.0 {
    ///                 // test bailout condition |z|**2 >= 16
    ///                 return false;
    ///             }
    ///         }
    ///         true // assume bounded
    ///     },
    ///     120,
    ///     100,
    /// );
    ///
    /// let mandelbrot_s = (
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n".to_owned() +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣴⣶⣶⡄⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣿⣿⣿⡗⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⡀⣀⣠⣬⣿⣯⣤⣀⡀⢀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢼⣷⣠⣶⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣦⡀⣴⣤⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣴⣾⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣟⠃⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢙⣾⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣧⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢐⣾⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡾⠂⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣶⣠⣤⣧⣤⣀⠀⠀⠀⣽⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣧⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣰⣿⣿⣿⣿⣿⣿⣧⡀⢰⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣟⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢰⣿⣿⣿⣿⣿⣿⣿⣿⣷⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⠃⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⠤⣿⣿⣾⣿⣿⣿⣿⣿⣿⣿⣿⣿⢼⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣟⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠉⠉⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣷⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢻⣿⣿⣿⣿⣿⣿⡿⠃⢸⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣗⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣿⠻⠿⡿⠿⠛⠁⠀⠀⢿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡿⠂⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠁⠀⠀⠀⠀⠀⢙⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣧⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢘⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡿⠈⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠉⠈⢿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣟⡁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢴⣾⠻⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⣿⡿⠋⢿⠷⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠁⠀⠐⠋⠛⠻⠿⣿⡿⠿⠛⠋⠙⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣾⣿⣿⣆⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢿⣿⣿⠇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠰⠂⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀\n" +
    ///     "⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀"
    /// ); // Blank spaces are U+2800, not U+0020
    ///
    /// assert_eq!(mandelbrot_bp.to_string(), mandelbrot_s);
    /// ```
    pub fn from_func<F>(func: F, bit_width: usize, bit_height: usize) -> Self
    where
        F: Fn((usize, usize)) -> bool,
    {
        let width = bit_width / 2 + bit_width % 2;
        let height = bit_height / 4 + usize::from(bit_height % 4 > 0);
        let data: Vec<u8> = (0..width * height)
            .map(|pos| Self::_pos_to_offset(pos, width))
            .map(|(c, r)| Self::_bools_to_data(|(x, y)| func((x as usize + c, y as usize + r))))
            .collect();
        Self { width, data }
    }
}

impl fmt::Display for BraillePic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let mut out_str = String::new();
        for (pos, x) in self.data.iter().enumerate() {
            if pos > 0 && pos % self.width == 0 {
                out_str.push('\n');
            }
            out_str.push(Self::_raw_to_braille(*x));
        }
        write!(f, "{}", out_str)
    }
}

impl ops::BitAnd for BraillePic {
    type Output = Self;

    fn bitand(self, rhs: Self) -> Self::Output {
        let (self_bit_width, self_bit_height) = self.bit_dimensions();
        let (rhs_bit_width, rhs_bit_height) = rhs.bit_dimensions();
        let output_bit_width = cmp::min(self_bit_width, rhs_bit_width);
        let output_bit_height = cmp::min(self_bit_height, rhs_bit_height);
        Self::from_func(
            |(col, row)| self.get_bit(col, row) && rhs.get_bit(col, row),
            output_bit_width,
            output_bit_height,
        )
    }
}

impl ops::BitAndAssign for BraillePic {
    fn bitand_assign(&mut self, rhs: Self) {
        let (self_bit_width, self_bit_height) = self.bit_dimensions();
        let (rhs_bit_width, rhs_bit_height) = rhs.bit_dimensions();
        let output_bit_width = cmp::min(self_bit_width, rhs_bit_width);
        let output_bit_height = cmp::min(self_bit_height, rhs_bit_height);
        *self = Self::from_func(
            |(col, row)| self.get_bit(col, row) && rhs.get_bit(col, row),
            output_bit_width,
            output_bit_height,
        )
    }
}

impl ops::BitOr for BraillePic {
    type Output = Self;

    fn bitor(self, rhs: Self) -> Self::Output {
        let (self_bit_width, self_bit_height) = self.bit_dimensions();
        let (rhs_bit_width, rhs_bit_height) = rhs.bit_dimensions();
        let output_bit_width = cmp::max(self_bit_width, rhs_bit_width);
        let output_bit_height = cmp::max(self_bit_height, rhs_bit_height);
        Self::from_func(
            |(col, row)| self.get_bit(col, row) || rhs.get_bit(col, row),
            output_bit_width,
            output_bit_height,
        )
    }
}

impl ops::BitOrAssign for BraillePic {
    fn bitor_assign(&mut self, rhs: Self) {
        let (self_bit_width, self_bit_height) = self.bit_dimensions();
        let (rhs_bit_width, rhs_bit_height) = rhs.bit_dimensions();
        let output_bit_width = cmp::max(self_bit_width, rhs_bit_width);
        let output_bit_height = cmp::max(self_bit_height, rhs_bit_height);
        *self = Self::from_func(
            |(col, row)| self.get_bit(col, row) || rhs.get_bit(col, row),
            output_bit_width,
            output_bit_height,
        )
    }
}

impl ops::BitXor for BraillePic {
    type Output = Self;

    fn bitxor(self, rhs: Self) -> Self::Output {
        let (self_bit_width, self_bit_height) = self.bit_dimensions();
        let (rhs_bit_width, rhs_bit_height) = rhs.bit_dimensions();
        let output_bit_width = cmp::max(self_bit_width, rhs_bit_width);
        let output_bit_height = cmp::max(self_bit_height, rhs_bit_height);
        Self::from_func(
            |(col, row)| self.get_bit(col, row) ^ rhs.get_bit(col, row),
            output_bit_width,
            output_bit_height,
        )
    }
}

impl ops::BitXorAssign for BraillePic {
    fn bitxor_assign(&mut self, rhs: Self) {
        let (self_bit_width, self_bit_height) = self.bit_dimensions();
        let (rhs_bit_width, rhs_bit_height) = rhs.bit_dimensions();
        let output_bit_width = cmp::max(self_bit_width, rhs_bit_width);
        let output_bit_height = cmp::max(self_bit_height, rhs_bit_height);
        *self = Self::from_func(
            |(col, row)| self.get_bit(col, row) ^ rhs.get_bit(col, row),
            output_bit_width,
            output_bit_height,
        )
    }
}

impl ops::Not for BraillePic {
    type Output = Self;

    fn not(self) -> Self::Output {
        let (bit_width, bit_height) = self.bit_dimensions();
        Self::from_func(|(col, row)| !self.get_bit(col, row), bit_width, bit_height)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    /* testing BraillePic::new() */

    #[test]
    fn test_new_1() {
        let bp = BraillePic::new(80, 45);
        assert_eq!(bp.width, 80);
        assert_eq!(bp.data.len(), 80 * 45);
        for k in bp.data.iter() {
            assert_eq!(*k, 0);
        }
    }

    #[test]
    fn test_new_2() {
        let bp = BraillePic::new(7, 12);
        for c in bp.to_string().chars() {
            assert!(c == '\u{2800}' || c == '\n');
        }
    }

    /* testing BraillePic::char_dimensions() */

    #[test]
    fn test_char_dim_1() {
        let bp = BraillePic {
            width: 30,
            data: (0..1500_u16)
                .map(|k| u8::try_from(k % 256).expect("k % 256 between 0 and 255, inclusive"))
                .collect(),
        };
        assert_eq!(bp.char_dimensions(), (30, 50));
    }

    #[test]
    fn test_char_dim_2() {
        // case where array is not completely full
        let bp = BraillePic {
            width: 30,
            data: (0..1475_u16)
                .map(|k| u8::try_from(k % 256).expect("k % 256 between 0 and 255, inclusive"))
                .collect(),
        };
        assert_eq!(bp.char_dimensions(), (30, 50));
    }

    /* testing BraillePic::bit_dimensions() */

    #[test]
    fn test_bit_dim_1() {
        let bp = BraillePic {
            width: 30,
            data: (0..1500_u16)
                .map(|k| u8::try_from(k % 256).expect("k % 256 between 0 and 255, inclusive"))
                .collect(),
        };
        assert_eq!(bp.bit_dimensions(), (60, 200));
    }

    #[test]
    fn test_bit_dim_2() {
        // case where array is not completely full
        let bp = BraillePic {
            width: 30,
            data: (0..1475_u16)
                .map(|k| u8::try_from(k % 256).expect("k % 256 between 0 and 255, inclusive"))
                .collect(),
        };
        assert_eq!(bp.bit_dimensions(), (60, 200));
    }

    /* testing BraillePic::get_data() */

    #[test]
    fn test_get_data_1() {
        let data: Vec<u8> = (0..1387_u16)
            .map(|k| {
                u8::try_from((3 * k + 7) % 256).expect("value will be between 0 and 255, inclusive")
            })
            .collect();
        let bp = BraillePic { width: 73, data };
        for row in 0..19 {
            for col in 0..73 {
                assert_eq!(
                    (col, row, bp.get_data(col, row)),
                    (
                        col,
                        row,
                        u8::try_from((3 * (row * 73 + col) + 7) % 256)
                            .expect("value will be between 0 and 255, inclusive")
                    )
                );
            }
        }
    }

    #[test]
    fn test_get_data_2() {
        // test if returns correct value outside the bounds or where the array is short
        let data: Vec<u8> = (0..1377_u16)
            .map(|k| {
                u8::try_from((3 * k + 7) % 256).expect("value will be between 0 and 255, inclusive")
            })
            .collect();
        let bp = BraillePic { width: 73, data };
        for row in 0..21 {
            for col in 0..75 {
                let k = row * 73 + col;
                assert_eq!(
                    (col, row, bp.get_data(col, row)),
                    (
                        col,
                        row,
                        if row < 19 && col < 73 && k < 1377 {
                            u8::try_from((3 * k + 7) % 256)
                                .expect("value will be between 0 and 255, inclusive")
                        } else {
                            0_u8
                        }
                    )
                );
            }
        }
    }

    /* testing BraillePic::get_bit() */

    #[test]
    fn test_get_bit_1() {
        let data: Vec<u8> = (0..1387_u16)
            .map(|k| u8::try_from(1 << ((3 * k + 5) % 7)).expect("will fit in 8 bits"))
            .collect();
        let bp = BraillePic { width: 73, data };

        for bit_row in 0..76 {
            for bit_col in 0..146 {
                // Recover character row, col
                let row = bit_row / 4;
                let col = bit_col / 2;
                let k = row * 73 + col;
                let bit_row_offset = bit_row % 4;
                let bit_col_offset = bit_col % 2;
                let dot_num = (3 - bit_row_offset) * 2 + (1 - bit_col_offset);
                assert_eq!(
                    (
                        bit_col,
                        bit_row,
                        col,
                        row,
                        k,
                        dot_num,
                        (3 * k + 5) % 7,
                        bp.get_bit(bit_col, bit_row)
                    ),
                    (
                        bit_col,
                        bit_row,
                        col,
                        row,
                        k,
                        dot_num,
                        (3 * k + 5) % 7,
                        dot_num == (3 * k + 5) % 7
                    )
                );
            }
        }
    }

    #[test]
    fn test_get_bit_2() {
        let data: Vec<u8> = (0..1377_u16) // test out of bounds, array falls short
            .map(|k| u8::try_from(1 << ((3 * k + 5) % 7)).expect("will fit in 8 bits"))
            .collect();
        let bp = BraillePic { width: 73, data };

        for bit_row in 0..80 {
            for bit_col in 0..150 {
                // Recover character row, col
                let row = bit_row / 4;
                let col = bit_col / 2;
                let k = row * 73 + col;
                let bit_row_offset = bit_row % 4;
                let bit_col_offset = bit_col % 2;
                let dot_num = (3 - bit_row_offset) * 2 + (1 - bit_col_offset);
                assert_eq!(
                    (
                        bit_col,
                        bit_row,
                        col,
                        row,
                        k,
                        dot_num,
                        (3 * k + 5) % 7,
                        bp.get_bit(bit_col, bit_row)
                    ),
                    (
                        bit_col,
                        bit_row,
                        col,
                        row,
                        k,
                        dot_num,
                        (3 * k + 5) % 7,
                        row < 19 && col < 73 && k < 1377 && (dot_num == (3 * k + 5) % 7)
                    )
                );
            }
        }
    }

    /* testing BraillePic::get_codepoint() */

    #[test]
    fn test_get_codepoint_1() {
        let data: Vec<u8> = (0..989)
            .map(|k| {
                u8::try_from((9 * k + 5) % 256).expect("value will be between 0 and 255, inclusive")
            })
            .collect();
        let bp = BraillePic { width: 23, data };
        for row in 0..43 {
            let bit_row = row * 4;
            for col in 0..23 {
                let bit_col = col * 2;
                assert_eq!(
                    (col, row, bp.get_codepoint(col, row)),
                    (
                        col,
                        row,
                        // conversion from the way we store our data and Unicode codepoints
                        // for braille characters
                        0x2800
                            + u32::from(bp.get_bit(bit_col, bit_row))
                            + (u32::from(bp.get_bit(bit_col, bit_row + 1)) << 1)
                            + (u32::from(bp.get_bit(bit_col, bit_row + 2)) << 2)
                            + (u32::from(bp.get_bit(bit_col + 1, bit_row)) << 3)
                            + (u32::from(bp.get_bit(bit_col + 1, bit_row + 1)) << 4)
                            + (u32::from(bp.get_bit(bit_col + 1, bit_row + 2)) << 5)
                            + (u32::from(bp.get_bit(bit_col, bit_row + 3)) << 6)
                            + (u32::from(bp.get_bit(bit_col + 1, bit_row + 3)) << 7)
                    )
                );
            }
        }
    }

    #[test]
    fn test_get_codepoint_2() {
        let data: Vec<u8> = (0..954) // test out of bounds, when array falls short
            .map(|k| {
                u8::try_from((9 * k + 5) % 256).expect("value will be between 0 and 255, inclusive")
            })
            .collect();
        let bp = BraillePic { width: 23, data };
        for row in 0..45 {
            let bit_row = row * 4;
            for col in 0..26 {
                let bit_col = col * 2;
                assert_eq!(
                    (col, row, bp.get_codepoint(col, row)),
                    (
                        col,
                        row,
                        // conversion from the way we store our data and Unicode codepoints
                        // for braille characters
                        0x2800
                            + if row < 43 && col < 23 && row * 23 + col < 954 {
                                u32::from(bp.get_bit(bit_col, bit_row))
                                    + (u32::from(bp.get_bit(bit_col, bit_row + 1)) << 1)
                                    + (u32::from(bp.get_bit(bit_col, bit_row + 2)) << 2)
                                    + (u32::from(bp.get_bit(bit_col + 1, bit_row)) << 3)
                                    + (u32::from(bp.get_bit(bit_col + 1, bit_row + 1)) << 4)
                                    + (u32::from(bp.get_bit(bit_col + 1, bit_row + 2)) << 5)
                                    + (u32::from(bp.get_bit(bit_col, bit_row + 3)) << 6)
                                    + (u32::from(bp.get_bit(bit_col + 1, bit_row + 3)) << 7)
                            } else {
                                0
                            }
                    )
                );
            }
        }
    }

    #[test]
    fn test_get_char_1() {
        let data: Vec<u8> = (0..989)
            .map(|k| {
                u8::try_from((9 * k + 5) % 256).expect("value will be between 0 and 255, inclusive")
            })
            .collect();
        let bp = BraillePic { width: 23, data };
        for row in 0..43 {
            let bit_row = row * 4;
            for col in 0..23 {
                let bit_col = col * 2;
                assert_eq!(
                    (col, row, bp.get_char(col, row)),
                    (
                        col,
                        row,
                        // conversion from the way we store our data and Unicode codepoints
                        // for braille characters
                        char::try_from(
                            0x2800
                                + u32::from(bp.get_bit(bit_col, bit_row))
                                + (u32::from(bp.get_bit(bit_col, bit_row + 1)) << 1)
                                + (u32::from(bp.get_bit(bit_col, bit_row + 2)) << 2)
                                + (u32::from(bp.get_bit(bit_col + 1, bit_row)) << 3)
                                + (u32::from(bp.get_bit(bit_col + 1, bit_row + 1)) << 4)
                                + (u32::from(bp.get_bit(bit_col + 1, bit_row + 2)) << 5)
                                + (u32::from(bp.get_bit(bit_col, bit_row + 3)) << 6)
                                + (u32::from(bp.get_bit(bit_col + 1, bit_row + 3)) << 7)
                        )
                        .expect(
                            "between 0x2800 and 0x28FF inclusive, which are all valid codepoints"
                        )
                    )
                );
            }
        }
    }

    #[test]
    fn test_get_char_2() {
        let data: Vec<u8> = (0..954) // test out of bounds, when array falls short
            .map(|k| {
                u8::try_from((9 * k + 5) % 256).expect("value will be between 0 and 255, inclusive")
            })
            .collect();
        let bp = BraillePic { width: 23, data };
        for row in 0..45 {
            let bit_row = row * 4;
            for col in 0..26 {
                let bit_col = col * 2;
                assert_eq!(
                    (col, row, bp.get_char(col, row)),
                    (
                        col,
                        row,
                        // conversion from the way we store our data and Unicode codepoints
                        // for braille characters
                        char::try_from(
                            0x2800
                                + if row < 43 && col < 23 && row * 23 + col < 954 {
                                    u32::from(bp.get_bit(bit_col, bit_row))
                                        + (u32::from(bp.get_bit(bit_col, bit_row + 1)) << 1)
                                        + (u32::from(bp.get_bit(bit_col, bit_row + 2)) << 2)
                                        + (u32::from(bp.get_bit(bit_col + 1, bit_row)) << 3)
                                        + (u32::from(bp.get_bit(bit_col + 1, bit_row + 1)) << 4)
                                        + (u32::from(bp.get_bit(bit_col + 1, bit_row + 2)) << 5)
                                        + (u32::from(bp.get_bit(bit_col, bit_row + 3)) << 6)
                                        + (u32::from(bp.get_bit(bit_col + 1, bit_row + 3)) << 7)
                                } else {
                                    0
                                }
                        )
                        .expect(
                            "between 0x2800 and 0x28FF inclusive, which are all valid codepoints"
                        )
                    )
                );
            }
        }
    }

    /* testing BraillePic::from_data() */

    #[test]
    fn test_from_data_1() {
        let mut data: [u8; 391] = [0; 391];
        for k in 0..391_usize {
            data[k] =
                u8::try_from(256 - ((2 * k + 1) % 256)).expect("value will always be at most 255");
        }
        let bp = BraillePic::from_data(&data, 17);
        assert_eq!(data.to_vec(), bp.data);
        assert_eq!(data.len(), bp.data.len());
        assert_eq!(bp.width, 17);
    }

    #[test]
    fn test_from_data_2() {
        let mut data: [u8; 386] = [0; 386]; // last row incomplete
        for k in 0..386_usize {
            data[k] =
                u8::try_from(256 - ((2 * k + 1) % 256)).expect("value will always be at most 255");
        }
        let bp = BraillePic::from_data(&data, 17);
        assert_eq!(data.to_vec(), bp.data);
        assert_eq!(data.len(), bp.data.len());
        assert_eq!(bp.width, 17);
    }

    /* testing BraillePic::from_data_vec() */
    #[test]
    fn test_from_data_vec_1() {
        let data: Vec<u8> = (0..576)
            .map(|k| u8::try_from((7 * k + 2) % 256).expect("value will be at most 255"))
            .collect();
        let data2 = data.clone();
        let bp = BraillePic::from_data_vec(data, 32);
        assert_eq!(data2, bp.data);
        assert_eq!(data2.len(), bp.data.len());
        assert_eq!(bp.width, 32);
    }

    #[test]
    fn test_from_data_vec_2() {
        let data: Vec<u8> = (0..571) // last row incomplete
            .map(|k| u8::try_from((7 * k + 2) % 256).expect("value will be at most 255"))
            .collect();
        let data2 = data.clone();
        let bp = BraillePic::from_data_vec(data, 32);
        assert_eq!(data2, bp.data);
        assert_eq!(data2.len(), bp.data.len());
        assert_eq!(bp.width, 32);
    }

    /* testing BraillePic::from_func() */

    fn func1(p: (usize, usize)) -> bool {
        p.0.pow(2) + p.1.pow(2) < 900
    }

    fn func2(p: (usize, usize)) -> bool {
        p.0 + 3 < p.1
    }

    #[test]
    fn test_from_func_1() {
        let bp = BraillePic::from_func(func1, 30, 30);
        for bit_row in 0..30 {
            for bit_col in 0..30 {
                let char_row = bit_row / 4;
                let char_col = bit_col / 2;
                let bit_row_off = bit_row % 4;
                let bit_col_off = bit_col % 2;
                let data_pos = 15 * char_row + char_col;
                assert_eq!(
                    (
                        bit_col,
                        bit_row,
                        (bp.data[data_pos] >> ((3 - bit_row_off) * 2 + (1 - bit_col_off))) % 2 != 0
                    ),
                    (bit_col, bit_row, func1((bit_col, bit_row)))
                );
            }
        }
    }

    #[test]
    fn test_from_func_2() {
        let bp = BraillePic::from_func(func2, 11, 9);
        for bit_row in 0..11 {
            for bit_col in 0..9 {
                let char_row = bit_row / 4;
                let char_col = bit_col / 2;
                let bit_row_off = bit_row % 4;
                let bit_col_off = bit_col % 2;
                let data_pos = 6 * char_row + char_col;
                assert_eq!(
                    (
                        bit_col,
                        bit_row,
                        (bp.data[data_pos] >> ((3 - bit_row_off) * 2 + (1 - bit_col_off))) % 2 != 0
                    ),
                    (bit_col, bit_row, func2((bit_col, bit_row)))
                );
            }
        }
    }

    /* testing bitwise operations */

    #[test]
    fn test_bitwise() {
        let bp1 = BraillePic::from_func(func1, 30, 30);
        let bp2 = BraillePic::from_func(func2, 30, 30);
        let bp_and = bp1.clone() & bp2.clone();
        let bp_or = bp1.clone() | bp2.clone();
        let bp_xor = bp1.clone() ^ bp2.clone();
        let bp_not = !(bp1.clone());

        for row in 0..30 {
            for col in 0..30 {
                let a = func1((col, row));
                let b = func2((col, row));
                assert_eq!((col, row, bp_and.get_bit(col, row)), (col, row, a && b));
                assert_eq!((col, row, bp_or.get_bit(col, row)), (col, row, a || b));
                assert_eq!(
                    (col, row, bp_xor.get_bit(col, row)),
                    (col, row, (a || b) && !(a && b))
                );
                assert_eq!((col, row, bp_not.get_bit(col, row)), (col, row, !a));
            }
        }
    }
}
