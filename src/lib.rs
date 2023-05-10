//! # braille_pics
//!
//! `braille_pics` provides a struct, `BraillePic`, to represent and produce text-art made of
//! Braille characers.
//!
//! License: MIT OR Apache-2.0

/****************************************************************
 * braille_pics
 *
 * src/lib.rs
 *
 * Christopher Phan, <https://chrisphan.com>
 *
 * Copyright 2023. License: MIT OR Apache-2.0
 *
 ****************************************************************/

/* TO DO:
 *
 * - Add tests
 * - Better comments!
 *
 * */

use std::cmp;
use std::fmt;
use std::ops;

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
            Some(k) => self.data[k],
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
            .expect("should be a valid character because it lands between 0x2800 and 0x28ff")
    }

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

    fn _pos_to_offset(pos: usize, width: usize) -> (usize, usize) {
        (2 * (pos % width), 4 * (pos / width))
    }

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

    fn _raw_braille_remap(raw: u8) -> u32 {
        let mut output: u32 = 0;
        for (k, shift) in BRAILLE_POS.iter().enumerate() {
            output += (((raw >> k) % 2) as u32) << shift
        }
        output
    }

    fn _raw_to_braille(raw: u8) -> char {
        char::from_u32(0x2800 + Self::_raw_braille_remap(raw)).expect("should be ok")
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

    fn _as_string(&self) -> String {
        let mut out_str = String::new();
        for (pos, x) in self.data.iter().enumerate() {
            if pos > 0 && pos % self.width == 0 {
                out_str.push('\n');
            }
            out_str.push(Self::_raw_to_braille(*x));
        }
        out_str
    }
}

impl fmt::Display for BraillePic {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "{}", self._as_string())
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
