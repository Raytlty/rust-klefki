// Copyright © 2016–2019 University of Malta

// This program is free software: you can redistribute it and/or
// modify it under the terms of the GNU Lesser General Public License
// as published by the Free Software Foundation, either version 3 of
// the License, or (at your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU Lesser General Public
// License and a copy of the GNU General Public License along with
// this program. If not, see <https://www.gnu.org/licenses/>.

use crate::{
    complex::big::{self, Format},
    ext::xmpc::{ordering2, raw_round2, Ordering2, Round2},
    float::{big::ExpFormat, Round, Special},
    ops::AssignRound,
    Assign, Complex, Float,
};
use gmp_mpfr_sys::mpc::{self, mpc_t};
use std::{
    cmp::Ordering,
    fmt::{
        Alignment, Binary, Debug, Display, Formatter, LowerExp, LowerHex, Octal,
        Result as FmtResult, UpperExp, UpperHex,
    },
    mem,
};

impl Clone for Complex {
    #[inline]
    fn clone(&self) -> Complex {
        let prec = self.prec();
        let mut ret = Complex::new(prec);
        ret.assign(self);
        ret
    }

    #[inline]
    fn clone_from(&mut self, source: &Complex) {
        self.assign(source);
    }
}

impl Drop for Complex {
    #[inline]
    fn drop(&mut self) {
        unsafe {
            mpc::clear(self.as_raw_mut());
        }
    }
}

impl<Re> From<Re> for Complex
where
    Float: From<Re>,
{
    #[inline]
    fn from(re: Re) -> Self {
        unsafe {
            let_uninit_ptr!(dst: Complex, dst_ptr);
            let inner_ptr = cast_ptr_mut!(dst_ptr, mpc_t);
            let real = cast_ptr_mut!(mpc::realref(inner_ptr), Float);
            real.write(Float::from(re));
            let imag = cast_ptr_mut!(mpc::imagref(inner_ptr), Float);
            imag.write(Float::new((*real).prec()));
            assume_init!(dst)
        }
    }
}

impl<Re, Im> From<(Re, Im)> for Complex
where
    Float: From<Re> + From<Im>,
{
    #[inline]
    fn from((re, im): (Re, Im)) -> Self {
        unsafe {
            let_uninit_ptr!(dst: Complex, dst_ptr);
            let inner_ptr = cast_ptr_mut!(dst_ptr, mpc_t);
            let real = cast_ptr_mut!(mpc::realref(inner_ptr), Float);
            real.write(Float::from(re));
            let imag = cast_ptr_mut!(mpc::imagref(inner_ptr), Float);
            imag.write(Float::from(im));
            assume_init!(dst)
        }
    }
}

impl Display for Complex {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let format = Format {
            exp: ExpFormat::Point,
            ..Format::default()
        };
        fmt_radix(self, f, format)
    }
}

impl Debug for Complex {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let format = Format {
            exp: ExpFormat::Point,
            ..Format::default()
        };
        fmt_radix(self, f, format)
    }
}

impl LowerExp for Complex {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let format = Format {
            exp: ExpFormat::Exp,
            ..Format::default()
        };
        fmt_radix(self, f, format)
    }
}

impl UpperExp for Complex {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let format = Format {
            to_upper: true,
            exp: ExpFormat::Point,
            ..Format::default()
        };
        fmt_radix(self, f, format)
    }
}

impl Binary for Complex {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let format = Format {
            radix: 2,
            prefix: "0b",
            exp: ExpFormat::Exp,
            ..Format::default()
        };
        fmt_radix(self, f, format)
    }
}

impl Octal for Complex {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let format = Format {
            radix: 8,
            prefix: "0o",
            exp: ExpFormat::Point,
            ..Format::default()
        };
        fmt_radix(self, f, format)
    }
}

impl LowerHex for Complex {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let format = Format {
            radix: 16,
            prefix: "0x",
            exp: ExpFormat::Point,
            ..Format::default()
        };
        fmt_radix(self, f, format)
    }
}

impl UpperHex for Complex {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let format = Format {
            radix: 16,
            to_upper: true,
            prefix: "0x",
            exp: ExpFormat::Point,
            ..Format::default()
        };
        fmt_radix(self, f, format)
    }
}

impl<T> Assign<T> for Complex
where
    Self: AssignRound<T, Round = Round2, Ordering = Ordering2>,
{
    #[inline]
    fn assign(&mut self, src: T) {
        self.assign_round(src, (Round::Nearest, Round::Nearest));
    }
}

impl AssignRound for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: Complex, round: Round2) -> Ordering2 {
        let (dst_real, dst_imag) = self.as_mut_real_imag();
        let (src_real, src_imag) = src.into_real_imag();
        let real_ord = if dst_real.prec() == src_real.prec() {
            drop(mem::replace(dst_real, src_real));
            Ordering::Equal
        } else {
            dst_real.assign_round(src_real, round.0)
        };
        let imag_ord = if dst_imag.prec() == src_imag.prec() {
            drop(mem::replace(dst_imag, src_imag));
            Ordering::Equal
        } else {
            dst_imag.assign_round(src_imag, round.1)
        };
        (real_ord, imag_ord)
    }
}

impl AssignRound<&Complex> for Complex {
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: &Complex, round: Round2) -> Ordering2 {
        let ret = unsafe { mpc::set(self.as_raw_mut(), src.as_raw(), raw_round2(round)) };
        ordering2(ret)
    }
}

impl<Re> AssignRound<Re> for Complex
where
    Float: AssignRound<Re, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: Re, round: Round2) -> Ordering2 {
        let real_ord = self.mut_real().assign_round(src, round.0);
        Assign::<Special>::assign(self.mut_imag(), Special::Zero);
        (real_ord, Ordering::Equal)
    }
}

impl<Re, Im> AssignRound<(Re, Im)> for Complex
where
    Float: AssignRound<Re, Round = Round, Ordering = Ordering>
        + AssignRound<Im, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: (Re, Im), round: Round2) -> Ordering2 {
        let real_ord = self.mut_real().assign_round(src.0, round.0);
        let imag_ord = self.mut_imag().assign_round(src.1, round.1);
        (real_ord, imag_ord)
    }
}

impl<'a, Re, Im> AssignRound<&'a (Re, Im)> for Complex
where
    Float: AssignRound<&'a Re, Round = Round, Ordering = Ordering>
        + AssignRound<&'a Im, Round = Round, Ordering = Ordering>,
{
    type Round = Round2;
    type Ordering = Ordering2;
    #[inline]
    fn assign_round(&mut self, src: &'a (Re, Im), round: Round2) -> Ordering2 {
        let real_ord = self.mut_real().assign_round(&src.0, round.0);
        let imag_ord = self.mut_imag().assign_round(&src.1, round.1);
        (real_ord, imag_ord)
    }
}

// * overwrites format.precision with fmt.precision()
// * overwrites format.sign_plus with fmt.sign_plus()
// * overwrites prefix with "" if not fmt.alternate()
fn fmt_radix(c: &Complex, fmt: &mut Formatter<'_>, format: Format) -> FmtResult {
    let format = Format {
        precision: fmt.precision(),
        sign_plus: fmt.sign_plus(),
        prefix: if fmt.alternate() { format.prefix } else { "" },
        ..format
    };
    let mut s = String::new();
    big::append_to_string(&mut s, c, format);
    // s is ascii only, so just take len for character count
    let count = s.len();
    let padding = match fmt.width() {
        Some(width) if width > count => width - count,
        _ => return fmt.write_str(&s),
    };
    let (padding_left, padding_right) = match fmt.align() {
        Some(Alignment::Left) => (0, padding),
        Some(Alignment::Right) | None => (padding, 0),
        Some(Alignment::Center) => (padding / 2, padding - padding / 2),
    };
    let mut fill_buf = String::with_capacity(4);
    fill_buf.push(fmt.fill());
    for _ in 0..padding_left {
        fmt.write_str(&fill_buf)?;
    }
    fmt.write_str(&s)?;
    for _ in 0..padding_right {
        fmt.write_str(&fill_buf)?;
    }
    Ok(())
}

unsafe impl Send for Complex {}
unsafe impl Sync for Complex {}

#[cfg(test)]
mod tests {
    use crate::{
        float::{self, FreeCache, Round},
        ops::AssignRound,
        Assign, Complex,
    };
    use std::cmp::Ordering;

    #[test]
    fn check_assign() {
        let nearest = (Round::Nearest, Round::Nearest);
        let mut c = Complex::with_val(4, (1.0, 2.0));
        assert_eq!(c, (1.0, 2.0));

        let other = Complex::with_val(53, (14.75, 15.25));
        let mut dir = c.assign_round(&other, nearest);
        assert_eq!(c, (15.0, 15.0));
        assert_eq!(dir, (Ordering::Greater, Ordering::Less));

        dir = c.assign_round(3.0, nearest);
        assert_eq!(c, (3.0, 0.0));
        assert_eq!(dir, (Ordering::Equal, Ordering::Equal));

        c.assign(other);
        assert_eq!(c, (15.0, 15.0));

        float::free_cache(FreeCache::All);
    }
}
