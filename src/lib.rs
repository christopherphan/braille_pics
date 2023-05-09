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
pub use braille_pics::BraillePic;

pub mod braille_pics {

    /* The BraillePic stuff should be seperated out and put into a crate for sharing!
     * TO DO:
     *
     * - Add documentation
     * - Add tests
     * - Better comments!
     *
     * */

    use std::fmt;

    const BRAILLE_POS: [usize; 8] = [7, 6, 5, 2, 4, 1, 3, 0];

    pub struct BraillePic {
        width: usize, // number of Braille chars, i.e. (true width) / 2
        data: Vec<u8>, // each integer represents 4-row by 2-column rectangle of bits, i.e. a
                      // Braille character
    }

    impl BraillePic {
        pub fn new(width: usize, height: usize) -> Self {
            let data: Vec<u8> = (0..width * height).map(|_| 0).collect();
            Self { width, data }
        }

        fn _bools_to_data<F>(func: F) -> u8
        where
            F: Fn((u8, u8)) -> bool,
        {
            let mut output: u8 = 0;
            for row in 0..4 {
                for col in 0..2 {
                    output <<= 1;
                    output += if func((col, row)) { 1 } else { 0 };
                }
            }
            output
        }

        fn _pos_to_offset(pos: usize, width: usize) -> (usize, usize) {
            (2 * (pos % width), 4 * (pos / width))
        }

        fn _raw_braille_remap(raw: u8) -> u32 {
            let mut output: u32 = 0;
            for k in 0..8 {
                output += (((raw >> k) % 2) as u32) << BRAILLE_POS[k];
            }
            output
        }

        fn _raw_to_braille(raw: u8) -> char {
            char::from_u32(0x2800 + Self::_raw_braille_remap(raw)).expect("should be ok")
        }

        pub fn from_raw(raw_data: &[u8], width: usize) -> Self {
            let hangover = raw_data.len() % width;
            let mut data: Vec<u8> = raw_data.iter().map(|x| *x).collect();
            for _ in 0..(width - hangover) {
                data.push(0);
            }
            Self { width, data }
        }

        pub fn from_data_vec(data: Vec<u8>, width: usize) -> Self {
            Self { width, data }
        }

        pub fn from_func<F>(func: F, bit_width: usize, bit_height: usize) -> Self
        where
            F: Fn((usize, usize)) -> bool,
        {
            let width = bit_width / 2 + bit_width % 2;
            let height = bit_height / 4 + if bit_height % 4 > 0 { 1 } else { 0 };
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
}
