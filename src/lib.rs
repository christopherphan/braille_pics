//! # braille_pics
//!
//! `braille_pics` provides a struct, `BraillePic`, to represent and produce text-art made of
//! Braille characers.
//!
//! License: MIT OR Apache-2.0

/****************************************************************
 * braillepics
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

/// Representation of a text-art picture made of Braille characters
#[derive(Debug, PartialEq, Eq)]
pub struct BraillePic {
    width: usize, // number of Braille chars, i.e. (true width) / 2
    data: Vec<u8>, // each integer represents 4-row by 2-column rectangle of bits, i.e. a
                  // Braille character
}

impl BraillePic {
    /// Creates a new blank `BraillePic` object of the specified size.
    ///
    /// Note that `width` and `height` are given in characters, not dots.
    pub fn new(width: usize, height: usize) -> Self {
        let data: Vec<u8> = (0..width * height).map(|_| 0).collect();
        Self { width, data }
    }

    fn _char_height(&self) -> usize {
        self.data.len() / self.width + usize::from(self.data.len() % self.width > 0)
    }

    /// Returns the dimensions (width, height) of the picture in characters.
    pub fn char_dimensions(&self) -> (usize, usize) {
        (self.width, self._char_height())
    }

    /// Returns the dimensions (width, height) of the picture in dots.
    pub fn bit_dimensions(&self) -> (usize, usize) {
        (self.width * 2, self._char_height() * 4)
    }

    fn _coords_to_data_pos(&self, col: usize, row: usize) -> Option<usize> {
        if col >= self.width || row >= self._char_height() {
            return None;
        }
        Some(row * self.width + col)
    }

    /// Returns the raw data at a given position in the picture.
    ///
    /// If the position is outside the dimensions of the picture, `0_u8` is returned.
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
    pub fn get_bit(&self, bit_col: usize, bit_row: usize) -> bool {
        if let Some((pos, bitpos)) = self._bit_coords_to_data_pos(bit_col, bit_row) {
            (self.data.get(pos).unwrap_or(&0_u8) >> bitpos) % 2 == 1
        } else {
            false
        }
    }

    /// Returns the Unicode codepoint for the Braille character at a given position in the picture.
    ///
    /// If the position is outside the dimensions of the picture, `0x2800_u32` (the codepoint for
    /// the blank Braille characer) is returned.
    pub fn get_codepoint(&self, col: usize, row: usize) -> u32 {
        0x2800 + Self::_raw_braille_remap(self.get_data(col, row))
    }

    /// Returns the Braille character at a given position in the picture.
    ///
    /// If the position is outside the dimensions, the blank Braille character (`⠀`, U+2800) is returned.
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
    pub fn from_data(raw_data: &[u8], width: usize) -> Self {
        let data: Vec<u8> = raw_data.to_vec();
        Self { width, data }
    }

    /// Creates a `BraillePic` object from a vector of `u8` values representing the raised dots in
    /// each character.
    pub fn from_data_vec(data: Vec<u8>, width: usize) -> Self {
        Self { width, data }
    }

    /// Creates a `BraillePic` object from a function or closure. The _dot_ at `(col, row)` is raised
    /// if `func((col, row)) == true`.
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
