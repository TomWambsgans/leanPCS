// Part of this repository. The additive transform's layers are domain.rs's (adapted there from leanVM's branch
// PCS-openings-aggregation, commit 651453c6), in the same order; the lane-wise carry-less product and its reduction
// are those of crates/vendor/leanvm-c445e3d5/primitives/src/field/{x8,gf2_64x3,gf2_64}.rs (vendored from leanVM c445e3d5, credit binius64).
// MIT OR Apache-2.0; see AGENTS.md.
//! [`crate::domain`]'s transforms on rows of eight words, a row's eight products one AVX-512 carry-less product (two
//! AVX2 + VPCLMULQDQ ones, or NEON PMULLs) where
//! the build has it (for `crates/leanvm/univariate`'s prover):
//!
//! - a batch ([`K8`]): eight K-columns, row `i` their entries at position `i`, every layer between rows;
//! - one K-column, eight positions a row: its layers from 3 up between rows, layers 0..3 inside a row.
//!
//! The additive transform has `quotient::domain`'s layers in its order, so the same values. Also here: the fold of a
//! polynomial onto a smaller coset, the shifted cube, and the interpolation from the first points of an extension
//! coset (`D_M`'s first `Σ 2^(e_j)` points, for a polynomial of degree below their count).

use std::ops::{Add, Mul};

use parallel::SendPtr;
use primitives::field::{F64, F192};

use crate::domain::{chain, point};

use lanes::{
    U, V, clmul_u, from_array, load, mask_add, mul, reduce_u, splat, store, swap, transpose, xor, xor_u, zero_u,
};

/// Eight K-columns' entries at one position: a row of a batch.
#[derive(Clone, Copy, Debug, Default, PartialEq, Eq)]
#[repr(C, align(64))]
pub struct K8(pub [F64; 8]);

impl K8 {
    pub const ZERO: Self = Self([F64::ZERO; 8]);
}

/// Rows one worker transforms whole (256 KiB), and rows one tile of the wider layers holds.
const LEAF_ROWS: usize = 1 << 12;
const TILE_ROWS: usize = 1 << 12;
/// The most of the wider layers one pass over memory takes.
const GROUP: usize = 6;

#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
mod lanes {
    use core::arch::x86_64::*;

    /// Eight K elements in one register.
    #[derive(Clone, Copy)]
    pub struct V(__m512i);

    /// # Safety
    /// `p` points to eight readable words.
    #[inline(always)]
    pub unsafe fn load(p: *const u64) -> V {
        // SAFETY: the caller's eight words; the module's cfg enables avx512f.
        unsafe { V(_mm512_loadu_si512(p.cast())) }
    }

    /// # Safety
    /// `p` points to eight writable words.
    #[inline(always)]
    pub unsafe fn store(p: *mut u64, v: V) {
        // SAFETY: the caller's eight words.
        unsafe { _mm512_storeu_si512(p.cast(), v.0) }
    }

    #[inline(always)]
    pub fn splat(x: u64) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { V(_mm512_set1_epi64(x as i64)) }
    }

    #[inline(always)]
    pub fn from_array(x: [u64; 8]) -> V {
        // SAFETY: eight words on the stack.
        unsafe { load(x.as_ptr()) }
    }

    #[inline(always)]
    pub fn xor(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { V(_mm512_xor_si512(a.0, b.0)) }
    }

    /// Lane-wise carry-less products, unreduced: the even lanes' 128-bit products, and the odd lanes'.
    #[derive(Clone, Copy)]
    pub struct U(__m512i, __m512i);

    #[inline(always)]
    pub fn zero_u() -> U {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { U(_mm512_setzero_si512(), _mm512_setzero_si512()) }
    }

    #[inline(always)]
    pub fn clmul_u(a: V, b: V) -> U {
        // SAFETY: the module's cfg enables avx512f and vpclmulqdq.
        unsafe {
            U(
                _mm512_clmulepi64_epi128::<0x00>(a.0, b.0),
                _mm512_clmulepi64_epi128::<0x11>(a.0, b.0),
            )
        }
    }

    #[inline(always)]
    pub fn xor_u(a: U, b: U) -> U {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { U(_mm512_xor_si512(a.0, b.0), _mm512_xor_si512(a.1, b.1)) }
    }

    /// Lane `i` reduced: the reduction of `gf2_64x3::x86_64::reduce_lanes512`. With GFNI its shifts are byte maps
    /// (`gfni_reduce`, from the vendored `pcs`'s `additive_ntt_f64.rs`): a high half has at most 63 bits (a sum of
    /// products of two 64-bit factors), so `g(hi ^ spill) = L(hi) ^ rotl8(H(hi)) ^ T(hi >> 56)`.
    #[cfg(target_feature = "gfni")]
    #[inline(always)]
    pub fn reduce_u(p: U) -> V {
        use super::gfni_reduce::{H, L, T};
        // SAFETY: the module's cfg enables avx512f, and this function's gfni.
        unsafe {
            let (lo, hi) = (_mm512_unpacklo_epi64(p.0, p.1), _mm512_unpackhi_epi64(p.0, p.1));
            let low = _mm512_gf2p8affine_epi64_epi8::<0>(hi, _mm512_set1_epi64(L));
            let high = _mm512_rol_epi64::<8>(_mm512_gf2p8affine_epi64_epi8::<0>(hi, _mm512_set1_epi64(H)));
            let spill = _mm512_gf2p8affine_epi64_epi8::<0>(_mm512_srli_epi64::<56>(hi), _mm512_set1_epi64(T));
            V(_mm512_xor_si512(lo, _mm512_ternarylogic_epi64::<0x96>(low, high, spill)))
        }
    }

    /// Lane `i` reduced: the reduction of `gf2_64x3::x86_64::reduce_lanes512`.
    #[cfg(not(target_feature = "gfni"))]
    #[inline(always)]
    pub fn reduce_u(p: U) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            let (lo, hi) = (_mm512_unpacklo_epi64(p.0, p.1), _mm512_unpackhi_epi64(p.0, p.1));
            // The bits of `hi * 0x1B` past x^63, then lo ^ f(hi ^ spill), f(v) = v ^ v<<1 ^ v<<3 ^ v<<4.
            let spill = _mm512_ternarylogic_epi64::<0x96>(
                _mm512_srli_epi64::<63>(hi),
                _mm512_srli_epi64::<61>(hi),
                _mm512_srli_epi64::<60>(hi),
            );
            let v = _mm512_xor_si512(hi, spill);
            let f = _mm512_ternarylogic_epi64::<0x96>(v, _mm512_slli_epi64::<1>(v), _mm512_slli_epi64::<3>(v));
            V(_mm512_ternarylogic_epi64::<0x96>(lo, f, _mm512_slli_epi64::<4>(v)))
        }
    }

    /// Lane `i` is `a_i b_i` in K.
    #[inline(always)]
    pub fn mul(a: V, b: V) -> V {
        reduce_u(clmul_u(a, b))
    }

    /// The 8 x 8 transpose: lane `p` of output `c` is lane `c` of input `p`.
    #[inline(always)]
    pub fn transpose(r: [V; 8]) -> [V; 8] {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            let pick = |a: __m512i, b: __m512i, i: [i64; 8]| {
                _mm512_permutex2var_epi64(a, _mm512_set_epi64(i[7], i[6], i[5], i[4], i[3], i[2], i[1], i[0]), b)
            };
            let x: [__m512i; 8] = std::array::from_fn(|k| {
                let (a, b) = (r[k & !1].0, r[k | 1].0);
                if k & 1 == 0 {
                    _mm512_unpacklo_epi64(a, b)
                } else {
                    _mm512_unpackhi_epi64(a, b)
                }
            });
            let (lo2, hi2) = ([0, 1, 8, 9, 4, 5, 12, 13], [2, 3, 10, 11, 6, 7, 14, 15]);
            let y = [
                pick(x[0], x[2], lo2),
                pick(x[1], x[3], lo2),
                pick(x[0], x[2], hi2),
                pick(x[1], x[3], hi2),
                pick(x[4], x[6], lo2),
                pick(x[5], x[7], lo2),
                pick(x[4], x[6], hi2),
                pick(x[5], x[7], hi2),
            ];
            let (lo4, hi4) = ([0, 1, 2, 3, 8, 9, 10, 11], [4, 5, 6, 7, 12, 13, 14, 15]);
            std::array::from_fn(|c| V(pick(y[c & 3], y[4 + (c & 3)], if c < 4 { lo4 } else { hi4 })))
        }
    }

    /// The even lanes of `a` then of `b`, and the odd ones.
    #[inline(always)]
    pub fn evens_odds(a: V, b: V) -> (V, V) {
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            let evens = _mm512_set_epi64(14, 12, 10, 8, 6, 4, 2, 0);
            let odds = _mm512_set_epi64(15, 13, 11, 9, 7, 5, 3, 1);
            (V(_mm512_permutex2var_epi64(a.0, evens, b.0)), V(_mm512_permutex2var_epi64(a.0, odds, b.0)))
        }
    }

    /// Lane `i` is `a_(i ^ S)`.
    #[inline(always)]
    pub fn swap<const S: usize>(a: V) -> V {
        let s = S as i64;
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            let index = _mm512_set_epi64(7 ^ s, 6 ^ s, 5 ^ s, 4 ^ s, 3 ^ s, 2 ^ s, 1 ^ s, s);
            V(_mm512_permutexvar_epi64(index, a.0))
        }
    }

    /// `a`, with `b` added on the lanes of `mask`.
    #[inline(always)]
    pub fn mask_add(a: V, mask: u8, b: V) -> V {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { V(_mm512_mask_xor_epi64(a.0, mask, a.0, b.0)) }
    }
}

/// The byte maps of the AVX-512 reduction on GFNI, as `vgf2p8affineqb` matrices (the vendored `pcs`'s
/// `additive_ntt_f64.rs`, `gfni_reduce`). Byte by byte, `b · 0x1B` is twelve bits: its low byte `L(b)` stays in place
/// and its high nibble `H(b)` moves a byte up; the top byte's nibble moves out, the spill, which the rotation brings
/// to byte 0 once, so `T(b) = H(b) · 0x1A` adds the rest of its product.
#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx512f",
    target_feature = "vpclmulqdq",
    target_feature = "gfni"
))]
mod gfni_reduce {
    /// The carry-less product of two 16-bit polynomials, truncated.
    const fn clmul16(a: u16, b: u16) -> u16 {
        let mut acc = 0;
        let mut j = 0;
        while j < 16 {
            if (b >> j) & 1 == 1 {
                acc ^= a << j;
            }
            j += 1;
        }
        acc
    }

    /// The byte map `which` (0: L, 1: H, 2: T) of one byte.
    const fn map(which: u8, b: u8) -> u8 {
        let p = clmul16(b as u16, 0x1B);
        match which {
            0 => p as u8,
            1 => (p >> 8) as u8,
            _ => clmul16(p >> 8, 0x1A) as u8,
        }
    }

    /// The matrix of byte map `which`: output bit `i` is the parity of the input under byte `7 - i`.
    const fn matrix(which: u8) -> i64 {
        let mut m = 0u64;
        let mut i = 0;
        while i < 8 {
            let mut row = 0u64;
            let mut j = 0;
            while j < 8 {
                if (map(which, 1 << j) >> i) & 1 == 1 {
                    row |= 1 << j;
                }
                j += 1;
            }
            m |= row << (8 * (7 - i));
            i += 1;
        }
        m as i64
    }

    pub(super) const L: i64 = matrix(0);
    pub(super) const H: i64 = matrix(1);
    pub(super) const T: i64 = matrix(2);
}

#[cfg(all(target_arch = "aarch64", target_feature = "aes"))]
mod lanes {
    use core::arch::aarch64::*;
    use primitives::field::gf2_64::aarch64::{pmull_hi_asm, pmull_lo_asm, reduce_pair_pmull4};

    /// Eight K elements in four NEON registers, lanes `2 j` and `2 j + 1` in register `j`.
    #[derive(Clone, Copy)]
    pub struct V([uint64x2_t; 4]);

    /// # Safety
    /// `p` points to eight readable words.
    #[inline(always)]
    pub unsafe fn load(p: *const u64) -> V {
        // SAFETY: the caller's eight words; NEON is baseline on aarch64.
        V(std::array::from_fn(|j| unsafe { vld1q_u64(p.add(2 * j)) }))
    }

    /// # Safety
    /// `p` points to eight writable words.
    #[inline(always)]
    pub unsafe fn store(p: *mut u64, v: V) {
        // Four stores, not one `vst1q_u64_x4`: through those LLVM sees a row stored to a local and read back
        // (`Kx8::to_row`) as the registers themselves.
        for (j, &x) in v.0.iter().enumerate() {
            // SAFETY: the caller's eight words.
            unsafe { vst1q_u64(p.add(2 * j), x) }
        }
    }

    #[inline(always)]
    pub fn splat(x: u64) -> V {
        // SAFETY: NEON is baseline on aarch64.
        V([unsafe { vdupq_n_u64(x) }; 4])
    }

    #[inline(always)]
    pub fn from_array(x: [u64; 8]) -> V {
        // SAFETY: eight words on the stack.
        unsafe { load(x.as_ptr()) }
    }

    #[inline(always)]
    pub fn xor(a: V, b: V) -> V {
        // SAFETY: NEON is baseline on aarch64.
        V(std::array::from_fn(|j| unsafe { veorq_u64(a.0[j], b.0[j]) }))
    }

    /// Lane-wise carry-less products, unreduced: lane `i`'s 128-bit product in register `i`.
    #[derive(Clone, Copy)]
    pub struct U([uint64x2_t; 8]);

    #[inline(always)]
    pub fn zero_u() -> U {
        // SAFETY: NEON is baseline on aarch64.
        U([unsafe { vdupq_n_u64(0) }; 8])
    }

    /// One PMULL a lane (PMULL2 for the odd lanes), on the registers as they are.
    #[inline(always)]
    pub fn clmul_u(a: V, b: V) -> U {
        // SAFETY: the module's cfg enables aes (PMULL).
        U(std::array::from_fn(|i| unsafe {
            let (x, y) = (a.0[i / 2], b.0[i / 2]);
            if i & 1 == 0 {
                pmull_lo_asm(x, y)
            } else {
                pmull_hi_asm(x, y)
            }
        }))
    }

    #[inline(always)]
    pub fn xor_u(a: U, b: U) -> U {
        // SAFETY: NEON is baseline on aarch64.
        U(std::array::from_fn(|i| unsafe { veorq_u64(a.0[i], b.0[i]) }))
    }

    /// Lane `i` reduced: two folds by `0x1B` with PMULL, a pair of lanes at a time
    /// (`gf2_64::aarch64::reduce_pair_pmull4`).
    #[inline(always)]
    pub fn reduce_u(p: U) -> V {
        // SAFETY: the module's cfg enables aes.
        V(std::array::from_fn(|j| unsafe {
            reduce_pair_pmull4(p.0[2 * j], p.0[2 * j + 1])
        }))
    }

    /// Lane `i` is `a_i b_i` in K.
    #[inline(always)]
    pub fn mul(a: V, b: V) -> V {
        reduce_u(clmul_u(a, b))
    }

    /// The 8 x 8 transpose: lane `p` of output `c` is lane `c` of input `p`.
    #[inline(always)]
    pub fn transpose(r: [V; 8]) -> [V; 8] {
        // SAFETY: NEON is baseline on aarch64.
        std::array::from_fn(|c| {
            V(std::array::from_fn(|j| unsafe {
                let (a, b) = (r[2 * j].0[c / 2], r[2 * j + 1].0[c / 2]);
                if c & 1 == 0 { vzip1q_u64(a, b) } else { vzip2q_u64(a, b) }
            }))
        })
    }

    /// Lane `i` is `a_(i ^ S)`.
    #[inline(always)]
    pub fn swap<const S: usize>(a: V) -> V {
        V(std::array::from_fn(|j| {
            let x = a.0[j ^ (S >> 1)];
            // SAFETY: NEON is baseline on aarch64.
            if S & 1 == 1 { unsafe { vextq_u64::<1>(x, x) } } else { x }
        }))
    }

    /// `a`, with `b` added on the lanes of `mask`.
    #[inline(always)]
    pub fn mask_add(a: V, mask: u8, b: V) -> V {
        // SAFETY: NEON is baseline on aarch64.
        V(std::array::from_fn(|j| unsafe {
            let (x, y) = (a.0[j], b.0[j]);
            match mask >> (2 * j) & 3 {
                0 => x,
                3 => veorq_u64(x, y),
                m => {
                    let keep = vcombine_u64(
                        vcreate_u64(if m & 1 == 1 { u64::MAX } else { 0 }),
                        vcreate_u64(if m & 2 == 2 { u64::MAX } else { 0 }),
                    );
                    veorq_u64(x, vandq_u64(y, keep))
                }
            }
        }))
    }
}

#[cfg(all(
    target_arch = "x86_64",
    target_feature = "avx2",
    target_feature = "vpclmulqdq",
    not(target_feature = "avx512f")
))]
mod lanes {
    //! AVX2 + VPCLMULQDQ: eight K elements in two registers, lanes `0..4` and `4..8`; the products and the
    //! reduction are the AVX-512 module's, on each half (no ternary logic: plain XORs).
    use core::arch::x86_64::*;

    /// Eight K elements in two registers.
    #[derive(Clone, Copy)]
    pub struct V([__m256i; 2]);

    /// # Safety
    /// `p` points to eight readable words.
    #[inline(always)]
    pub unsafe fn load(p: *const u64) -> V {
        // SAFETY: the caller's eight words.
        unsafe { V([_mm256_loadu_si256(p.cast()), _mm256_loadu_si256(p.add(4).cast())]) }
    }

    /// # Safety
    /// `p` points to eight writable words.
    #[inline(always)]
    pub unsafe fn store(p: *mut u64, v: V) {
        // SAFETY: the caller's eight words.
        unsafe {
            _mm256_storeu_si256(p.cast(), v.0[0]);
            _mm256_storeu_si256(p.add(4).cast(), v.0[1]);
        }
    }

    #[inline(always)]
    pub fn splat(x: u64) -> V {
        // SAFETY: the module's cfg enables avx2.
        let h = unsafe { _mm256_set1_epi64x(x as i64) };
        V([h, h])
    }

    #[inline(always)]
    pub fn from_array(x: [u64; 8]) -> V {
        // SAFETY: eight words on the stack.
        unsafe { load(x.as_ptr()) }
    }

    #[inline(always)]
    pub fn xor(a: V, b: V) -> V {
        // SAFETY: the module's cfg enables avx2.
        unsafe { V([_mm256_xor_si256(a.0[0], b.0[0]), _mm256_xor_si256(a.0[1], b.0[1])]) }
    }

    /// Lane-wise carry-less products, unreduced: each half's even lanes' 128-bit products, and its odd lanes'.
    #[derive(Clone, Copy)]
    pub struct U([__m256i; 4]);

    #[inline(always)]
    pub fn zero_u() -> U {
        // SAFETY: the module's cfg enables avx2.
        let z = unsafe { _mm256_setzero_si256() };
        U([z; 4])
    }

    #[inline(always)]
    pub fn clmul_u(a: V, b: V) -> U {
        // SAFETY: the module's cfg enables avx2 and vpclmulqdq.
        unsafe {
            U([
                _mm256_clmulepi64_epi128::<0x00>(a.0[0], b.0[0]),
                _mm256_clmulepi64_epi128::<0x11>(a.0[0], b.0[0]),
                _mm256_clmulepi64_epi128::<0x00>(a.0[1], b.0[1]),
                _mm256_clmulepi64_epi128::<0x11>(a.0[1], b.0[1]),
            ])
        }
    }

    #[inline(always)]
    pub fn xor_u(a: U, b: U) -> U {
        // SAFETY: the module's cfg enables avx2.
        unsafe { U(std::array::from_fn(|i| _mm256_xor_si256(a.0[i], b.0[i]))) }
    }

    /// One half reduced: `lo ^ f(hi ^ spill)`, as in the AVX-512 module.
    #[inline(always)]
    fn reduce_half(even: __m256i, odd: __m256i) -> __m256i {
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            let (lo, hi) = (_mm256_unpacklo_epi64(even, odd), _mm256_unpackhi_epi64(even, odd));
            let spill = _mm256_xor_si256(
                _mm256_xor_si256(_mm256_srli_epi64::<63>(hi), _mm256_srli_epi64::<61>(hi)),
                _mm256_srli_epi64::<60>(hi),
            );
            let v = _mm256_xor_si256(hi, spill);
            let f = _mm256_xor_si256(
                _mm256_xor_si256(v, _mm256_slli_epi64::<1>(v)),
                _mm256_xor_si256(_mm256_slli_epi64::<3>(v), _mm256_slli_epi64::<4>(v)),
            );
            _mm256_xor_si256(lo, f)
        }
    }

    #[inline(always)]
    pub fn reduce_u(p: U) -> V {
        V([reduce_half(p.0[0], p.0[1]), reduce_half(p.0[2], p.0[3])])
    }

    /// Lane `i` is `a_i b_i` in K.
    #[inline(always)]
    pub fn mul(a: V, b: V) -> V {
        reduce_u(clmul_u(a, b))
    }

    /// The 8 x 8 transpose: lane `p` of output `c` is lane `c` of input `p`.
    #[inline(always)]
    pub fn transpose(r: [V; 8]) -> [V; 8] {
        let mut m = [[0u64; 8]; 8];
        // SAFETY: eight words a row, on the stack.
        unsafe {
            for (row, v) in m.iter_mut().zip(r) {
                store(row.as_mut_ptr(), v);
            }
        }
        std::array::from_fn(|c| from_array(std::array::from_fn(|p| m[p][c])))
    }

    /// Lane `i` is `a_(i ^ S)`.
    #[inline(always)]
    pub fn swap<const S: usize>(a: V) -> V {
        let [mut x, mut y] = a.0;
        if S & 4 != 0 {
            (x, y) = (y, x);
        }
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            if S & 2 != 0 {
                (x, y) = (_mm256_permute4x64_epi64::<0x4E>(x), _mm256_permute4x64_epi64::<0x4E>(y));
            }
            if S & 1 != 0 {
                (x, y) = (_mm256_permute4x64_epi64::<0xB1>(x), _mm256_permute4x64_epi64::<0xB1>(y));
            }
        }
        V([x, y])
    }

    /// `a`, with `b` added on the lanes of `mask`.
    #[inline(always)]
    pub fn mask_add(a: V, mask: u8, b: V) -> V {
        let bit = |i: u32| -(((mask >> i) & 1) as i64);
        // SAFETY: the module's cfg enables avx2.
        unsafe {
            let m0 = _mm256_set_epi64x(bit(3), bit(2), bit(1), bit(0));
            let m1 = _mm256_set_epi64x(bit(7), bit(6), bit(5), bit(4));
            V([
                _mm256_xor_si256(a.0[0], _mm256_and_si256(b.0[0], m0)),
                _mm256_xor_si256(a.0[1], _mm256_and_si256(b.0[1], m1)),
            ])
        }
    }
}

#[cfg(not(any(
    all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"),
    all(
        target_arch = "x86_64",
        target_feature = "avx2",
        target_feature = "vpclmulqdq",
        not(target_feature = "avx512f")
    ),
    all(target_arch = "aarch64", target_feature = "aes")
)))]
mod lanes {
    use primitives::field::F64;

    /// Eight K elements.
    #[derive(Clone, Copy)]
    pub struct V([u64; 8]);

    /// # Safety
    /// `p` points to eight readable words.
    #[inline(always)]
    pub unsafe fn load(p: *const u64) -> V {
        // SAFETY: the caller's eight words.
        unsafe { V(p.cast::<[u64; 8]>().read_unaligned()) }
    }

    /// # Safety
    /// `p` points to eight writable words.
    #[inline(always)]
    pub unsafe fn store(p: *mut u64, v: V) {
        // SAFETY: the caller's eight words.
        unsafe { p.cast::<[u64; 8]>().write_unaligned(v.0) }
    }

    #[inline(always)]
    pub fn splat(x: u64) -> V {
        V([x; 8])
    }

    #[inline(always)]
    pub fn from_array(x: [u64; 8]) -> V {
        V(x)
    }

    #[inline(always)]
    pub fn xor(a: V, b: V) -> V {
        V(std::array::from_fn(|i| a.0[i] ^ b.0[i]))
    }

    #[inline(always)]
    pub fn mul(a: V, b: V) -> V {
        V(std::array::from_fn(|i| (F64(a.0[i]) * F64(b.0[i])).0))
    }

    /// Products, here reduced at once.
    pub type U = V;

    #[inline(always)]
    pub fn zero_u() -> U {
        V([0; 8])
    }

    #[inline(always)]
    pub fn clmul_u(a: V, b: V) -> U {
        mul(a, b)
    }

    #[inline(always)]
    pub fn xor_u(a: U, b: U) -> U {
        xor(a, b)
    }

    #[inline(always)]
    pub fn reduce_u(p: U) -> V {
        p
    }

    #[inline(always)]
    pub fn transpose(r: [V; 8]) -> [V; 8] {
        std::array::from_fn(|c| V(std::array::from_fn(|p| r[p].0[c])))
    }

    #[inline(always)]
    pub fn swap<const S: usize>(a: V) -> V {
        V(std::array::from_fn(|i| a.0[i ^ S]))
    }

    #[inline(always)]
    pub fn mask_add(a: V, mask: u8, b: V) -> V {
        V(std::array::from_fn(|i| {
            if mask >> i & 1 == 1 { a.0[i] ^ b.0[i] } else { a.0[i] }
        }))
    }
}

/// A transform's layers: the twiddle of a pair of rows, their butterfly, and a row's own layers 0..3 (one column).
trait Kind: Sync {
    /// Whether the layers run from the highest down.
    const DOWN: bool;
    /// The twiddle of position layer `k`'s block `block` (a position `>> (k + 1)`).
    fn twiddle(&self, k: usize, block: usize) -> F64;
    /// `twiddle(k, b + j) - twiddle(k, b)` for `b` a multiple of a power of two above `j`.
    fn step(&self, j: usize) -> F64;
    fn butterfly(a: V, b: V, t: V) -> (V, V);
    /// Layers 0..3 of row `row`, eight consecutive positions of one column.
    fn lanes(&self, row: usize, x: V) -> V;
    /// [`Self::lanes`] on the `size` rows at `base`, rows `first..first + size` of the column.
    ///
    /// # Safety
    /// `base` holds `8 size` words of the caller's own.
    #[inline(always)]
    unsafe fn own_rows(&self, base: *mut u64, first: usize, size: usize) {
        for r in 0..size {
            // SAFETY: row `r < size` of the caller's.
            unsafe {
                let p = base.add(8 * r);
                store(p, self.lanes(first + r, load(p)));
            }
        }
    }
}

/// `ω_(2 j)`, from a table below a leaf's blocks.
#[inline(always)]
fn evens(j: usize) -> F64 {
    static TABLE: std::sync::OnceLock<Vec<F64>> = std::sync::OnceLock::new();
    let table = TABLE.get_or_init(|| (0..LEAF_ROWS).map(|j| point(2 * j)).collect());
    table.get(j).copied().unwrap_or_else(|| point(2 * j))
}

/// The additive transform's twiddles: `w_k` of the offset, and a row's lane twiddles' constant parts.
struct Twiddles {
    offsets: Vec<F64>,
    c1: V,
    c0: V,
}

impl Twiddles {
    fn new(offset: F64, layers: usize) -> Self {
        let p = |i: usize| point(i).0;
        Self {
            offsets: chain(offset, layers.max(3)),
            c1: from_array([0, 0, 0, 0, p(2), p(2), p(2), p(2)]),
            c0: from_array([0, 0, p(2), p(2), p(4), p(4), p(6), p(6)]),
        }
    }

    /// Row `row`'s twiddles at layers 2, 1, 0: `w_k` at each pair's low position.
    #[inline(always)]
    fn row(&self, row: usize) -> [V; 3] {
        let o = &self.offsets;
        [
            splat((o[2] + point(2 * row)).0),
            xor(splat((o[1] + point(4 * row)).0), self.c1),
            xor(splat((o[0] + point(8 * row)).0), self.c0),
        ]
    }
}

/// Coefficients to values (`crate::domain::values`): `a += λ b; b += a`, the layers from the highest down.
struct Forward(Twiddles);

impl Kind for Forward {
    const DOWN: bool = true;
    #[inline(always)]
    unsafe fn own_rows(&self, base: *mut u64, first: usize, size: usize) {
        // SAFETY: the caller's rows.
        unsafe { own_stepped(self, base, first, size) }
    }
    #[inline(always)]
    fn twiddle(&self, k: usize, block: usize) -> F64 {
        self.0.offsets[k] + point(2 * block)
    }
    #[inline(always)]
    fn step(&self, j: usize) -> F64 {
        evens(j)
    }
    #[inline(always)]
    fn butterfly(a: V, b: V, t: V) -> (V, V) {
        let a = xor(a, mul(b, t));
        (a, xor(b, a))
    }
    #[inline(always)]
    fn lanes(&self, row: usize, x: V) -> V {
        let [t2, t1, t0] = self.0.row(row);
        let x = mask_add(x, 0x0F, mul(swap::<4>(x), t2));
        let x = mask_add(x, 0xF0, swap::<4>(x));
        let x = mask_add(x, 0x33, mul(swap::<2>(x), t1));
        let x = mask_add(x, 0xCC, swap::<2>(x));
        let x = mask_add(x, 0x55, mul(swap::<1>(x), t0));
        mask_add(x, 0xAA, swap::<1>(x))
    }
}

/// Values to coefficients (`crate::domain::coefficients`): `b += a; a += λ b`, the layers from 0 up.
struct Inverse(Twiddles);

impl Kind for Inverse {
    const DOWN: bool = false;
    #[inline(always)]
    unsafe fn own_rows(&self, base: *mut u64, first: usize, size: usize) {
        // SAFETY: the caller's rows.
        unsafe { own_stepped(self, base, first, size) }
    }
    #[inline(always)]
    fn twiddle(&self, k: usize, block: usize) -> F64 {
        self.0.offsets[k] + point(2 * block)
    }
    #[inline(always)]
    fn step(&self, j: usize) -> F64 {
        evens(j)
    }
    #[inline(always)]
    fn butterfly(a: V, b: V, t: V) -> (V, V) {
        let b = xor(b, a);
        (xor(a, mul(b, t)), b)
    }
    #[inline(always)]
    fn lanes(&self, row: usize, x: V) -> V {
        let [t2, t1, t0] = self.0.row(row);
        let x = mask_add(x, 0xAA, swap::<1>(x));
        let x = mask_add(x, 0x55, mul(swap::<1>(x), t0));
        let x = mask_add(x, 0xCC, swap::<2>(x));
        let x = mask_add(x, 0x33, mul(swap::<2>(x), t1));
        let x = mask_add(x, 0xF0, swap::<4>(x));
        mask_add(x, 0x0F, mul(swap::<4>(x), t2))
    }
}

/// The multilinear extension on a shifted cube: per variable `l`, `(v_0, v_1) ↦ (v_0 + δ_l s, v_1 + δ_l s)`,
/// `s = v_0 + v_1`. The variables' maps commute.
struct Cube {
    delta: Vec<F64>,
}

impl Kind for Cube {
    const DOWN: bool = true;
    #[inline(always)]
    fn twiddle(&self, k: usize, _: usize) -> F64 {
        self.delta[k]
    }
    #[inline(always)]
    fn step(&self, _: usize) -> F64 {
        F64::ZERO
    }
    #[inline(always)]
    fn butterfly(a: V, b: V, t: V) -> (V, V) {
        let s = mul(xor(a, b), t);
        (xor(a, s), xor(b, s))
    }
    #[inline(always)]
    fn lanes(&self, _: usize, x: V) -> V {
        let x = xor(x, mul(xor(x, swap::<1>(x)), splat(self.delta[0].0)));
        let x = xor(x, mul(xor(x, swap::<2>(x)), splat(self.delta[1].0)));
        xor(x, mul(xor(x, swap::<4>(x)), splat(self.delta[2].0)))
    }
}

/// `len` row pairs, `lo` and `hi`, through the butterfly with twiddle `t`.
///
/// # Safety
/// `lo` and `hi` point to `len` rows each, of the caller's own.
#[inline(always)]
unsafe fn pairs<T: Kind>(lo: *mut u64, hi: *mut u64, len: usize, t: V) {
    for i in 0..len {
        // SAFETY: rows `i < len` of the caller's.
        unsafe {
            let (pa, pb) = (lo.add(8 * i), hi.add(8 * i));
            let (a, b) = T::butterfly(load(pa), load(pb), t);
            store(pa, a);
            store(pb, b);
        }
    }
}

/// Two layers at once on four runs of `len` rows (`p[0..4]`): the higher layer pairs `p[0]` with `p[2]` and `p[1]`
/// with `p[3]` at twiddle `t1`, the lower `p[0]` with `p[1]` at `t2a` and `p[2]` with `p[3]` at `t2b`, in `T`'s order
/// (the higher first going down): [`pairs`] twice, with one load and one store a row rather than two.
///
/// # Safety
/// The four point to `len` rows each, of the caller's own, disjoint.
#[inline(always)]
unsafe fn quads<T: Kind>(p: [*mut u64; 4], len: usize, t1: V, t2a: V, t2b: V) {
    // `C` rows of each run at a time, their butterflies interleaved: a row's four are two dependent layers, too short
    // a chain for the out-of-order window to overlap the next row's on its own.
    #[inline(always)]
    unsafe fn rows<T: Kind, const C: usize>(at: [*mut u64; 4], t1: V, t2a: V, t2b: V) {
        // SAFETY: the caller's `C` rows of each run.
        unsafe {
            let mut x: [[V; 4]; C] = std::array::from_fn(|c| at.map(|q| load(q.add(8 * c))));
            let pair = |x: &mut [[V; 4]; C], a: usize, b: usize, t: V| {
                for col in x.iter_mut() {
                    (col[a], col[b]) = T::butterfly(col[a], col[b], t);
                }
            };
            if T::DOWN {
                pair(&mut x, 0, 2, t1);
                pair(&mut x, 1, 3, t1);
                pair(&mut x, 0, 1, t2a);
                pair(&mut x, 2, 3, t2b);
            } else {
                pair(&mut x, 0, 1, t2a);
                pair(&mut x, 2, 3, t2b);
                pair(&mut x, 0, 2, t1);
                pair(&mut x, 1, 3, t1);
            }
            for (c, col) in x.iter().enumerate() {
                for (q, &v) in at.iter().zip(col) {
                    store(q.add(8 * c), v);
                }
            }
        }
    }
    let mut i = 0;
    // SAFETY: rows `i .. i + C <= len` of the caller's.
    unsafe {
        while i + 2 <= len {
            rows::<T, 2>(p.map(|q| q.add(8 * i)), t1, t2a, t2b);
            i += 2;
        }
        if i < len {
            rows::<T, 1>(p.map(|q| q.add(8 * i)), t1, t2a, t2b);
        }
    }
}

/// The order a pass runs its layers `0..n` in: `(layer, fused)`, `fused` meaning `layer` with `layer - 1` at once
/// ([`quads`]), the highest first going down, else the lowest; the first layer alone when it reads a source.
fn layer_steps(n: usize, down: bool, from_src: bool) -> Vec<(usize, bool)> {
    let mut steps = Vec::new();
    if down {
        let mut top = n;
        if from_src && top > 0 {
            steps.push((top - 1, false));
            top -= 1;
        }
        while top >= 2 {
            steps.push((top - 1, true));
            top -= 2;
        }
        if top == 1 {
            steps.push((0, false));
        }
    } else {
        let mut low = 0;
        if from_src && n > 0 {
            steps.push((0, false));
            low = 1;
        }
        while low + 1 < n {
            steps.push((low + 1, true));
            low += 2;
        }
        if low < n {
            steps.push((low, false));
        }
    }
    steps
}

/// Layers `a..a + g` (position layers `a + shift..`) of `kind` on one tile, its `2^g` lines `line(u)` each a run of
/// `width` rows of `data`, two at a time where they pair ([`quads`]): [`pairs`] layer by layer, in fewer passes over
/// the tile. The same butterflies, so the same values. With `from_src`, the first layer (the highest going down, else
/// the lowest) is the caller's, run already from a source.
///
/// # Safety
/// The tile's rows are the caller's own.
#[inline(always)]
#[allow(clippy::too_many_arguments)]
unsafe fn tile_layers<T: Kind>(
    kind: &T,
    data: SendPtr<u64>,
    line: &impl Fn(usize) -> usize,
    a: usize,
    g: usize,
    width: usize,
    shift: usize,
    from_src: bool,
) {
    let lines = 1usize << g;
    // SAFETY: the tile's rows, the caller's.
    unsafe {
        let layer = |j: usize| {
            let k = a + j;
            let hs = 1usize << j;
            for ub in (0..lines).step_by(2 * hs) {
                let t = splat(kind.twiddle(k + shift, line(ub) >> (k + 1)).0);
                for u in ub..ub + hs {
                    pairs::<T>(data.add(8 * line(u)), data.add(8 * line(u + hs)), width, t);
                }
            }
        };
        // Layers `j` and `j - 1` at once: each block of `2 hs` lines of layer `j`, its two halves layer `j - 1`'s.
        let fused = |j: usize| {
            let k = a + j;
            let (hs, q) = (1usize << j, 1usize << (j - 1));
            for ub in (0..lines).step_by(2 * hs) {
                let t1 = splat(kind.twiddle(k + shift, line(ub) >> (k + 1)).0);
                let t2a = splat(kind.twiddle(k - 1 + shift, line(ub) >> k).0);
                let t2b = splat(kind.twiddle(k - 1 + shift, line(ub + hs) >> k).0);
                for u in ub..ub + q {
                    let p = [u, u + q, u + hs, u + hs + q].map(|v| data.add(8 * line(v)));
                    quads::<T>(p, width, t1, t2a, t2b);
                }
            }
        };
        // The steps but the source's layer, which is the first.
        for (j, two) in layer_steps(g, T::DOWN, from_src).into_iter().skip(usize::from(from_src)) {
            match two {
                true => fused(j),
                false => layer(j),
            }
        }
    }
}

/// [`pairs`] read from `src_lo` and `src_hi` (another buffer's rows), written to `lo` and `hi`: a first layer's
/// butterflies that also copy.
///
/// # Safety
/// The four point to `len` rows each, the sources readable, `lo` and `hi` of the caller's own.
#[inline(always)]
unsafe fn pairs_from<T: Kind>(src_lo: *const u64, src_hi: *const u64, lo: *mut u64, hi: *mut u64, len: usize, t: V) {
    for i in 0..len {
        // SAFETY: rows `i < len` of the caller's.
        unsafe {
            let (a, b) = T::butterfly(load(src_lo.add(8 * i)), load(src_hi.add(8 * i)), t);
            store(lo.add(8 * i), a);
            store(hi.add(8 * i), b);
        }
    }
}

/// `kind`'s layers on the `rows` rows of eight words at `data`, read first from `src` if given: position layer `k` is
/// row layer `k - shift`, and the layers below `shift` (0 or 3) are inside the rows. With `runs`, every eight rows
/// are transposed last ([`values_batch`]).
///
/// # Safety
/// `data` holds `8 rows` words, and `src` (if given) as many, disjoint from `data`.
unsafe fn run<T: Kind>(data: *mut u64, src: Option<*const u64>, rows: usize, shift: usize, kind: &T, runs: bool) {
    // SAFETY: the caller's.
    unsafe { run_on(data, src, rows, shift, kind, runs, false) }
}

/// `f(i)` for every `i < n`: by the pool, or by the calling worker alone (`serial`), in the same order of results.
/// Many tasks go by [`affine`] ranges.
#[inline(always)]
fn tasks(n: usize, serial: bool, f: impl Fn(usize) + Sync) {
    if serial {
        (0..n).for_each(f);
    } else if n >= 4 * parallel::num_threads() {
        affine(n, f);
    } else {
        parallel::for_each(n, f);
    }
}

/// `f(i)` for every `i < n` by the pool, in one contiguous range of tasks a worker, each range first offered to the
/// same thread on every call ([`parallel::for_each_affine`]). A column's passes split their tasks in order of rows, so
/// a transform's leaves and its next wide pass (and back-to-back transforms' last and first passes) give each thread
/// the rows it wrote last: in its own L2 or its CCD's L3. With the pool's shared claims, rows land on any thread, and a
/// column about as large as the L3s together (`2^25` words, 256 MiB on the 8-CCD Zen 5 here) is read mostly from other
/// CCDs' L3s, slower than from memory. One column's transforms back to back, 64 threads: `2^25` words 9.8–10.3 →
/// 4.4–5.5 ms, `2^24` 3.7 → 2.0–3.0 ms, `2^26` 11–14 → 10 ms. The same tasks, so the same values.
fn affine(n: usize, f: impl Fn(usize) + Sync) {
    parallel::for_each_affine(n, |lo, hi| (lo..hi).for_each(&f));
}

/// [`run`], by the pool or by the calling worker alone (`serial`, for a caller that runs many transforms at once,
/// one a worker): the same layers in the same order, so the same values.
///
/// # Safety
/// As [`run`]'s.
unsafe fn run_on<T: Kind>(
    data: *mut u64,
    src: Option<*const u64>,
    rows: usize,
    shift: usize,
    kind: &T,
    runs: bool,
    serial: bool,
) {
    let col = Col {
        data: SendPtr(data),
        src: src.map(|s| SendPtr(s.cast_mut())),
    };
    // SAFETY: the caller's.
    unsafe { run_cols(&[col], rows, shift, kind, runs, serial) }
}

/// A column a transform writes (`data`), read first from `src` if given.
#[derive(Clone, Copy)]
struct Col {
    data: SendPtr<u64>,
    src: Option<SendPtr<u64>>,
}

/// [`run_on`] on several columns of `rows` rows at once, each pass's tasks for every column in one dispatch: the
/// same values as one column at a time.
///
/// # Safety
/// Each column's `data` holds `8 rows` words, its `src` (if given) as many; all disjoint.
unsafe fn run_cols<T: Kind>(cols: &[Col], rows: usize, shift: usize, kind: &T, runs: bool, serial: bool) {
    // SAFETY: the caller's.
    unsafe { run_cols_each(cols, std::slice::from_ref(kind), rows, shift, runs, serial) }
}

/// [`run_cols`], column `c` by its own kind `kinds[c]` (or all by `kinds[0]`, one given): columns of one length
/// on different cosets in the same dispatches.
///
/// # Safety
/// As [`run_cols`]'s.
unsafe fn run_cols_each<T: Kind>(cols: &[Col], kinds: &[T], rows: usize, shift: usize, runs: bool, serial: bool) {
    assert!(kinds.len() == 1 || kinds.len() == cols.len());
    assert!(rows.is_power_of_two());
    let mr = rows.trailing_zeros() as usize;
    let leaf = mr.min(LEAF_ROWS.trailing_zeros() as usize);
    // The wider layers in groups, the highest first.
    let mut groups = Vec::new();
    let mut top = mr;
    while top > leaf {
        let a = top.saturating_sub(GROUP).max(leaf);
        groups.push((a, top - a));
        top = a;
    }
    if T::DOWN {
        let mut from = true;
        for &(a, g) in &groups {
            wide(cols, std::mem::take(&mut from), rows, a, g, shift, kinds, serial);
        }
        leaves(cols, from, rows, leaf, shift, kinds, runs, serial);
    } else {
        leaves(cols, true, rows, leaf, shift, kinds, runs, serial);
        for &(a, g) in groups.iter().rev() {
            wide(cols, false, rows, a, g, shift, kinds, serial);
        }
    }
}

/// Row layers `0..leaf`, and the rows' own layers, on each block of `2^leaf` rows by one worker.
#[allow(clippy::too_many_arguments)]
fn leaves<T: Kind>(
    cols: &[Col],
    from_src: bool,
    rows: usize,
    leaf: usize,
    shift: usize,
    kinds: &[T],
    runs: bool,
    serial: bool,
) {
    let size = 1usize << leaf;
    let per = rows >> leaf;
    tasks(per * cols.len(), serial, |t| {
        let (Col { data, src }, task) = (cols[t / per], t % per);
        let kind = &kinds[if kinds.len() == 1 { 0 } else { t / per }];
        let src = if from_src { src } else { None };
        let first = task << leaf;
        // SAFETY: a task touches its own `size` rows from `first`.
        unsafe {
            let base = data.add(8 * first);
            // The first layer reads the source itself where it is a layer between rows (not the rows' own layers).
            let fused = leaf > 0 && (T::DOWN || shift == 0);
            let mut src = src;
            if let Some(s) = src.filter(|_| !fused) {
                std::ptr::copy_nonoverlapping(s.add(8 * first), base, 8 * size);
                src = None;
            }
            let own = |base: *mut u64| {
                if shift == 3 {
                    kind.own_rows(base, first, size);
                }
            };
            if !T::DOWN {
                own(base);
            }
            let layer = |k: usize, from: Option<SendPtr<u64>>| {
                let half = 1usize << k;
                // The blocks' twiddles: the first's, plus `step(j)` (the block indices' bits are disjoint).
                let t0 = kind.twiddle(k + shift, first >> (k + 1));
                for j in 0..size >> (k + 1) {
                    let row = first + 2 * half * j;
                    let t = splat((t0 + kind.step(j)).0);
                    let (lo, hi) = (data.add(8 * row), data.add(8 * (row + half)));
                    match from {
                        Some(s) => pairs_from::<T>(s.add(8 * row), s.add(8 * (row + half)), lo, hi, half, t),
                        None => pairs::<T>(lo, hi, half, t),
                    }
                }
            };
            // Layers `k` and `k - 1` at once: each block of layer `k`, its two halves layer `k - 1`'s blocks.
            let fused = |k: usize| {
                let h = 1usize << (k - 1);
                let (t_hi, t_lo) = (kind.twiddle(k + shift, first >> (k + 1)), kind.twiddle(k - 1 + shift, first >> k));
                for j in 0..size >> (k + 1) {
                    let row = first + 4 * h * j;
                    let (t1, t2a, t2b) = (
                        splat((t_hi + kind.step(j)).0),
                        splat((t_lo + kind.step(2 * j)).0),
                        splat((t_lo + kind.step(2 * j + 1)).0),
                    );
                    quads::<T>([0, 1, 2, 3].map(|q| data.add(8 * (row + q * h))), h, t1, t2a, t2b);
                }
            };
            for (k, two) in layer_steps(leaf, T::DOWN, src.is_some()) {
                match two {
                    true => fused(k),
                    false => layer(k, if k + 1 == leaf && T::DOWN || k == 0 && !T::DOWN { src } else { None }),
                }
            }
            if T::DOWN {
                own(base);
            }
            if runs {
                for g in 0..size / 8 {
                    let p = base.add(64 * g);
                    let t = transpose(std::array::from_fn(|q| load(p.add(8 * q))));
                    (0..8).for_each(|q| store(p.add(8 * q), t[q]));
                }
            }
        }
    });
}

/// Row layers `a..a + g` in one pass: tiles of `2^g` lines `2^a` rows apart, each line a run of rows.
#[allow(clippy::too_many_arguments)]
fn wide<T: Kind>(
    cols: &[Col],
    from_src: bool,
    rows: usize,
    a: usize,
    g: usize,
    shift: usize,
    kinds: &[T],
    serial: bool,
) {
    let lines = 1usize << g;
    let width = (TILE_ROWS >> g).clamp(1, 1 << a);
    let per_group = (1usize << a) / width;
    let per = (rows >> (a + g)) * per_group;
    tasks(per * cols.len(), serial, |t| {
        let (Col { data, src }, task) = (cols[t / per], t % per);
        let kind = &kinds[if kinds.len() == 1 { 0 } else { t / per }];
        let src = if from_src { src } else { None };
        let row0 = ((task / per_group) << (a + g)) + (task % per_group) * width;
        let line = |u: usize| row0 + (u << a);
        // SAFETY: a task touches rows `line(u) + [0, width)`, `u < lines`: its own.
        unsafe {
            // The first layer reads the source itself: each line is in one of its pairs.
            if let Some(s) = src {
                let j = if T::DOWN { g - 1 } else { 0 };
                let (k, hs) = (a + j, 1usize << j);
                for ub in (0..lines).step_by(2 * hs) {
                    let t = splat(kind.twiddle(k + shift, line(ub) >> (k + 1)).0);
                    for u in ub..ub + hs {
                        let (lo, hi) = (data.add(8 * line(u)), data.add(8 * line(u + hs)));
                        pairs_from::<T>(s.add(8 * line(u)), s.add(8 * line(u + hs)), lo, hi, width, t);
                    }
                }
            }
            tile_layers(kind, data, &line, a, g, width, shift, src.is_some());
        }
    });
}

fn words(data: &mut [K8]) -> *mut u64 {
    data.as_mut_ptr().cast()
}

/// `crate::domain::values` on a batch: row `i` becomes the eight columns at `offset + ω_i`; with `runs` (and eight
/// rows or more), each eight rows transposed: row `8 j + l` is column `l` at the points `8 j..8 j + 8` ([`Kx8::row`]).
pub fn values_batch(data: &mut [K8], offset: F64, runs: bool) {
    assert!(!runs || data.len() >= 8);
    let kind = Forward(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    // SAFETY: `data`'s own rows.
    unsafe { run(words(data), None, data.len(), 0, &kind, runs) }
}

/// [`values_batch`] of `src`, written to `dst`.
pub fn values_batch_from(src: &[K8], dst: &mut [K8], offset: F64, runs: bool) {
    assert_eq!(src.len(), dst.len());
    assert!(!runs || dst.len() >= 8);
    let kind = Forward(Twiddles::new(offset, dst.len().trailing_zeros() as usize));
    // SAFETY: `dst`'s own rows, read first from `src`'s.
    unsafe { run(words(dst), Some(src.as_ptr().cast()), dst.len(), 0, &kind, runs) }
}

/// A batch of novel coefficients on the coset `ω_first + V_e` (`8 ≤ 2^e ≤ src.len()`), into a new batch, each eight
/// rows transposed if `runs`: [`values_batch_from`], or [`fold_batch`] then [`values_batch`], without zeroing the
/// output first.
pub fn on_coset_batch(src: &[K8], first: usize, e: usize, runs: bool) -> Vec<K8> {
    let size = 1usize << e;
    assert!(size >= 8 && src.len().is_multiple_of(size));
    // SAFETY: both ways write every row first (the transform's first pass reads `src`; the fold's tasks cover every
    // row).
    let mut out: Vec<K8> = unsafe { primitives::uninit_vec(size) };
    if size == src.len() {
        values_batch_from(src, &mut out, point(first), runs);
    } else {
        fold_batch(src, first, &mut out);
        values_batch(&mut out, point(first), runs);
    }
    out
}

/// [`values_batch_from`] by the calling worker alone (no dispatch to the pool): for a caller that transforms many
/// batches at once, one a worker. The same values.
pub fn values_batch_from_serial(src: &[K8], dst: &mut [K8], offset: F64, runs: bool) {
    assert_eq!(src.len(), dst.len());
    assert!(!runs || dst.len() >= 8);
    let kind = Forward(Twiddles::new(offset, dst.len().trailing_zeros() as usize));
    // SAFETY: `dst`'s own rows, read first from `src`'s.
    unsafe { run_on(words(dst), Some(src.as_ptr().cast()), dst.len(), 0, &kind, runs, true) }
}

/// [`values_batch`] by the calling worker alone.
pub fn values_batch_serial(data: &mut [K8], offset: F64, runs: bool) {
    assert!(!runs || data.len() >= 8);
    let kind = Forward(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    // SAFETY: `data`'s own rows.
    unsafe { run_on(words(data), None, data.len(), 0, &kind, runs, true) }
}

/// [`fold_batch`] by the calling worker alone.
pub fn fold_batch_serial(src: &[K8], first: usize, dst: &mut [K8]) {
    let rows = dst.len();
    assert_eq!(src.len() % rows, 0);
    let len = src.len() / rows;
    let e = rows.trailing_zeros() as usize;
    // The weights `Π w_(e + b)(ω_first)` over the bits `b` of the block (`novel_weights`), built as `tensor` builds
    // them: the same products in the same order.
    let mut weights = vec![F64::ONE];
    let mut b = 0;
    while weights.len() < len {
        let one = point(first >> (e + b));
        let half = weights.len();
        for h in 0..half {
            let w = weights[h] * one;
            weights.push(w);
        }
        b += 1;
    }
    // `fold_rows`' sum, row by row, in its order of terms.
    let src: *const u64 = src.as_ptr().cast();
    let dst = words(dst);
    for i in 0..rows {
        // SAFETY: rows `i + h rows` of `src` (`len` blocks of `rows`), and row `i` of `dst`.
        unsafe {
            let mut acc = load(src.add(8 * i));
            if weights[0] != F64::ONE {
                acc = mul(acc, splat(weights[0].0));
            }
            for (h, &w) in weights.iter().enumerate().skip(1) {
                acc = xor(acc, mul(load(src.add(8 * (i + h * rows))), splat(w.0)));
            }
            store(dst.add(8 * i), acc);
        }
    }
}

/// Each eight rows transposed, as [`values_batch`]'s `runs` leaves them (`data.len()` a multiple of 8).
pub fn transpose_runs(data: &mut [K8]) {
    for group in data.chunks_exact_mut(8) {
        let rows: [V; 8] = std::array::from_fn(|q| Kx8::row(&group[q]).0);
        for (row, t) in group.iter_mut().zip(transpose(rows)) {
            *row = Kx8(t).to_row();
        }
    }
}

/// `crate::domain::coefficients` on a batch.
pub fn coefficients_batch(data: &mut [K8], offset: F64) {
    let kind = Inverse(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    // SAFETY: `data`'s own rows.
    unsafe { run(words(data), None, data.len(), 0, &kind, false) }
}

/// `crate::domain::values` on one column.
pub fn values(data: &mut [F64], offset: F64) {
    if data.len() < 8 {
        return crate::domain::values(data, offset);
    }
    let kind = Forward(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    // SAFETY: `data`'s own words, eight a row.
    unsafe { run(data.as_mut_ptr().cast(), None, data.len() / 8, 3, &kind, false) }
}

/// [`values`] of `src`, written to `dst`.
pub fn values_from(src: &[F64], dst: &mut [F64], offset: F64) {
    assert_eq!(src.len(), dst.len());
    if dst.len() < 8 {
        dst.copy_from_slice(src);
        return crate::domain::values(dst, offset);
    }
    let kind = Forward(Twiddles::new(offset, dst.len().trailing_zeros() as usize));
    // SAFETY: `dst`'s own words, eight a row, read first from `src`'s.
    unsafe {
        run(
            dst.as_mut_ptr().cast(),
            Some(src.as_ptr().cast()),
            dst.len() / 8,
            3,
            &kind,
            false,
        )
    }
}

/// [`coefficients`] of `src`, written to `dst`.
pub fn coefficients_from(src: &[F64], dst: &mut [F64], offset: F64) {
    assert_eq!(src.len(), dst.len());
    if dst.len() < 8 {
        dst.copy_from_slice(src);
        return crate::domain::coefficients(dst, offset);
    }
    let kind = Inverse(Twiddles::new(offset, dst.len().trailing_zeros() as usize));
    // SAFETY: `dst`'s own words, eight a row, read first from `src`'s.
    unsafe {
        run(
            dst.as_mut_ptr().cast(),
            Some(src.as_ptr().cast()),
            dst.len() / 8,
            3,
            &kind,
            false,
        )
    }
}

/// `crate::domain::coefficients` on one column.
pub fn coefficients(data: &mut [F64], offset: F64) {
    if data.len() < 8 {
        return crate::domain::coefficients(data, offset);
    }
    let kind = Inverse(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    // SAFETY: `data`'s own words, eight a row.
    unsafe { run(data.as_mut_ptr().cast(), None, data.len() / 8, 3, &kind, false) }
}

/// Eight K elements in a register: a column at eight consecutive points.
#[derive(Clone, Copy)]
pub struct Kx8(V);

impl Kx8 {
    /// A row of a batch, as [`values_batch`]'s `runs` leaves it.
    #[inline(always)]
    pub fn row(x: &K8) -> Self {
        // SAFETY: a row's eight words.
        Self(unsafe { load(x.0.as_ptr().cast()) })
    }

    /// The first eight of `x`.
    #[inline(always)]
    pub fn load(x: &[F64]) -> Self {
        assert!(x.len() >= 8);
        // SAFETY: eight words of `x`.
        Self(unsafe { load(x.as_ptr().cast()) })
    }

    #[inline(always)]
    pub fn new(x: [F64; 8]) -> Self {
        Self(from_array(x.map(|v| v.0)))
    }

    #[inline(always)]
    pub fn splat(x: F64) -> Self {
        Self(splat(x.0))
    }

    /// Lane `l` is lane `l ^ x`'s (`x < 8`).
    #[inline(always)]
    pub fn xor_lanes(self, x: usize) -> Self {
        let mut v = self.0;
        if x & 1 != 0 {
            v = swap::<1>(v);
        }
        if x & 2 != 0 {
            v = swap::<2>(v);
        }
        if x & 4 != 0 {
            v = swap::<4>(v);
        }
        Self(v)
    }

    /// The even lanes `self`'s, the odd ones `odd`'s.
    #[inline(always)]
    pub fn odd_from(self, odd: Self) -> Self {
        Self(mask_add(self.0, 0xAA, xor(self.0, odd.0)))
    }

    /// `a`'s even lanes then `b`'s, and their odd ones: `(x_0, x_2, .., y_0, y_2, ..)` and `(x_1, x_3, ..)`.
    #[inline(always)]
    pub fn evens_odds(a: Self, b: Self) -> (Self, Self) {
        #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
        {
            let (e, o) = lanes::evens_odds(a.0, b.0);
            (Self(e), Self(o))
        }
        #[cfg(not(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq")))]
        {
            let (x, y) = (a.to_row().0, b.to_row().0);
            let pick = |o: usize| Self::new(std::array::from_fn(|l| if l < 4 { x[2 * l + o] } else { y[2 * (l - 4) + o] }));
            (pick(0), pick(1))
        }
    }

    /// Eight registers transposed: lane `l` of output `i` is lane `i` of input `l`.
    #[inline(always)]
    pub fn transpose8(rows: [Self; 8]) -> [Self; 8] {
        transpose(rows.map(|r| r.0)).map(Self)
    }

    #[inline(always)]
    pub fn to_row(self) -> K8 {
        let mut out = K8::ZERO;
        // SAFETY: a row's eight words.
        unsafe { store(out.0.as_mut_ptr().cast(), self.0) };
        out
    }

    /// Its eight lanes into the first words of `dst`, cut at its length.
    #[inline(always)]
    pub fn store_to(self, dst: &mut [F64]) {
        if dst.len() >= 8 {
            // SAFETY: eight words of `dst`.
            unsafe { store(dst.as_mut_ptr().cast(), self.0) }
        } else {
            let row = self.to_row();
            dst.copy_from_slice(&row.0[..dst.len()]);
        }
    }
}

impl Add for Kx8 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self(xor(self.0, rhs.0))
    }
}

impl Mul for Kx8 {
    type Output = Self;
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        Self(mul(self.0, rhs.0))
    }
}

/// Eight K products, unreduced: a sum of them is reduced once ([`Kx8U::reduce`]).
#[derive(Clone, Copy)]
pub struct Kx8U(U);

impl Kx8U {
    #[inline(always)]
    pub fn zero() -> Self {
        Self(zero_u())
    }

    /// `a b`, unreduced.
    #[inline(always)]
    pub fn product(a: Kx8, b: Kx8) -> Self {
        Self(clmul_u(a.0, b.0))
    }

    #[inline(always)]
    pub fn reduce(self) -> Kx8 {
        Kx8(reduce_u(self.0))
    }
}

impl Add for Kx8U {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self(xor_u(self.0, rhs.0))
    }
}

/// Eight E elements in three registers, limb by limb.
#[derive(Clone, Copy)]
pub struct Ex8([V; 3]);

impl Ex8 {
    #[inline(always)]
    pub fn splat(x: F192) -> Self {
        Self([splat(x.c0), splat(x.c1), splat(x.c2)])
    }

    #[inline(always)]
    pub fn from_limbs(l: [Kx8; 3]) -> Self {
        Self(l.map(|k| k.0))
    }

    /// K lanes as E lanes.
    #[inline(always)]
    pub fn from_k(k: Kx8) -> Self {
        Self([k.0, splat(0), splat(0)])
    }

    #[inline(always)]
    pub fn limbs(self) -> [Kx8; 3] {
        self.0.map(Kx8)
    }

    /// The eight elements.
    #[inline(always)]
    pub fn to_array(self) -> [F192; 8] {
        let [a, b, c] = self.0.map(|l| Kx8(l).to_row());
        std::array::from_fn(|p| F192::new(a.0[p].0, b.0[p].0, c.0[p].0))
    }

    /// Lane `i` is lane `i ^ 1`'s.
    #[inline(always)]
    pub fn swap_pairs(self) -> Self {
        Self(self.0.map(swap::<1>))
    }

    /// The even lanes `self`'s, the odd ones `odd`'s.
    #[inline(always)]
    pub fn odd_from(self, odd: Self) -> Self {
        Self(std::array::from_fn(|l| mask_add(self.0[l], 0xAA, xor(self.0[l], odd.0[l]))))
    }

    /// Lane `i` times `k_i` in K.
    #[inline(always)]
    pub fn mul_k(self, k: Kx8) -> Self {
        Self(self.0.map(|l| mul(l, k.0)))
    }
}

impl Add for Ex8 {
    type Output = Self;
    #[inline(always)]
    fn add(self, rhs: Self) -> Self {
        Self([
            xor(self.0[0], rhs.0[0]),
            xor(self.0[1], rhs.0[1]),
            xor(self.0[2], rhs.0[2]),
        ])
    }
}

impl Mul for Ex8 {
    type Output = Self;
    /// Karatsuba's six lane products, then the fold of `y^3 = y + 1` (`gf2_64x3::x86_64::fold`), three reductions.
    #[inline(always)]
    fn mul(self, rhs: Self) -> Self {
        let ([a0, a1, a2], [b0, b1, b2]) = (self.0, rhs.0);
        let (p0, p1, p2) = (clmul_u(a0, b0), clmul_u(a1, b1), clmul_u(a2, b2));
        let p01 = clmul_u(xor(a0, a1), xor(b0, b1));
        let p02 = clmul_u(xor(a0, a2), xor(b0, b2));
        let p12 = clmul_u(xor(a1, a2), xor(b1, b2));
        let d0 = xor_u(xor_u(p0, p1), xor_u(p2, p12));
        let d1 = xor_u(xor_u(p0, p01), p12);
        let d2 = xor_u(xor_u(p0, p1), p02);
        Self([reduce_u(d0), reduce_u(d1), reduce_u(d2)])
    }
}

/// An E constant in every lane, for [`MixedSum::add`].
#[derive(Clone, Copy)]
pub struct ESplat([V; 3]);

impl ESplat {
    pub fn new(c: F192) -> Self {
        Self([splat(c.c0), splat(c.c1), splat(c.c2)])
    }
}

/// `Σ c k` over E constants `c` and K lanes `k`, unreduced until [`MixedSum::reduce`].
#[derive(Clone, Copy)]
pub struct MixedSum([U; 3]);

impl Default for MixedSum {
    fn default() -> Self {
        Self([zero_u(), zero_u(), zero_u()])
    }
}

impl MixedSum {
    #[inline(always)]
    pub fn add(&mut self, c: &ESplat, k: Kx8) {
        for (acc, &l) in self.0.iter_mut().zip(&c.0) {
            *acc = xor_u(*acc, clmul_u(l, k.0));
        }
    }

    /// `Σ e k` lane by lane: lane `i` adds `e_i k_i`.
    #[inline(always)]
    pub fn add_lanes(&mut self, e: Ex8, k: Kx8) {
        for (acc, &l) in self.0.iter_mut().zip(&e.0) {
            *acc = xor_u(*acc, clmul_u(l, k.0));
        }
    }

    #[inline(always)]
    pub fn reduce(self) -> Ex8 {
        Ex8(self.0.map(reduce_u))
    }
}

/// `out[k][8 j + p]` is limb `k` of `f(j)`'s lane `p`, the last run cut at the outputs' length.
pub fn fill_limbs8(out: [&mut [F64]; 3], f: impl Fn(usize) -> Ex8 + Sync) {
    let len = out[0].len();
    assert!(out.iter().all(|o| o.len() == len));
    let ptrs = out.map(|o| SendPtr(o.as_mut_ptr()));
    let runs = len.div_ceil(8);
    const BLOCK: usize = 128;
    parallel::for_each(runs.div_ceil(BLOCK), |b| {
        for j in b * BLOCK..((b + 1) * BLOCK).min(runs) {
            let limbs = f(j).0;
            for (ptr, limb) in ptrs.iter().zip(limbs) {
                // SAFETY: a task writes its own runs of the three outputs, each `len` long.
                unsafe {
                    if 8 * j + 8 <= len {
                        store(ptr.add(8 * j).cast(), limb);
                    } else {
                        let row = Kx8(limb).to_row();
                        std::ptr::copy_nonoverlapping(row.0.as_ptr(), ptr.add(8 * j), len - 8 * j);
                    }
                }
            }
        }
    });
}

/// `out[k][i]` is limb `k` of `f(i)`, in parallel blocks of `block` entries.
pub fn fill_limbs(out: [&mut [F64]; 3], block: usize, f: impl Fn(usize) -> F192 + Sync) {
    let len = out[0].len();
    assert!(out.iter().all(|o| o.len() == len));
    let ptrs = out.map(|o| SendPtr(o.as_mut_ptr()));
    parallel::for_each(len.div_ceil(block), |b| {
        for i in b * block..((b + 1) * block).min(len) {
            let v = f(i);
            // SAFETY: a task writes its own block of the three outputs, each `len` long.
            unsafe {
                *ptrs[0].add(i) = F64(v.c0);
                *ptrs[1].add(i) = F64(v.c1);
                *ptrs[2].add(i) = F64(v.c2);
            }
        }
    });
}

/// Columns (at most eight, of one length) as a batch, the absent lanes zero.
pub fn pack(columns: &[&[F64]]) -> Vec<K8> {
    assert!(columns.len() <= 8);
    let n = columns.first().map_or(0, |c| c.len());
    assert!(columns.iter().all(|c| c.len() == n));
    parallel::map_collect(n, |i| {
        K8(std::array::from_fn(|l| columns.get(l).map_or(F64::ZERO, |c| c[i])))
    })
}

/// `Π_(bits b of h) c[b]` for every `h < len` (the weights of a fold): `c[b]` for the bits of `h`, ...
fn tensor(len: usize, factor: impl Fn(usize, bool) -> F64) -> Vec<F64> {
    // The products over the low bits and over the high bits, each by doubling, then (long ones) every entry the
    // product of one of each in one dispatch: the same products (the field's are exact).
    let doubled = |from: usize, bits: usize| {
        let mut out = vec![F64::ONE];
        for b in from..from + bits {
            let (zero, one) = (factor(b, false), factor(b, true));
            let high: Vec<F64> = out.iter().map(|&l| l * one).collect();
            if zero != F64::ONE {
                out.iter_mut().for_each(|x| *x *= zero);
            }
            out.extend(high);
        }
        out
    };
    let bits = len.max(1).next_power_of_two().trailing_zeros() as usize;
    let low_bits = bits.min(12);
    let mut low = doubled(0, low_bits);
    if bits == low_bits {
        low.truncate(len);
        return low;
    }
    let high = doubled(low_bits, bits - low_bits);
    let mask = (1usize << low_bits) - 1;
    parallel::map_collect(len, |h| low[h & mask] * high[h >> low_bits])
}

/// `len` zeros, a long column's pages written in parallel (not by one thread's `memset`).
pub fn zeros(len: usize) -> Vec<F64> {
    if len < 1 << 16 {
        vec![F64::ZERO; len]
    } else {
        parallel::map_collect(len, |_| F64::ZERO)
    }
}

/// `len` words to be written whole before any is read (a transform's or a fold's output).
///
/// # Safety
/// The caller writes every word before reading it.
unsafe fn unwritten(len: usize) -> Vec<F64> {
    // SAFETY: the caller's.
    unsafe { primitives::uninit_vec(len) }
}

/// The weights folding a polynomial's novel coefficients (`len` blocks of `2^e`) onto the coset `ω_first + V_e`:
/// `Π w_(e + b)(ω_first)` over the bits `b` of the block, since `w_l` is constant there for `l ≥ e`.
fn novel_weights(len: usize, first: usize, e: usize) -> Vec<F64> {
    tensor(len, |b, bit| if bit { point(first >> (e + b)) } else { F64::ONE })
}

/// `dst` row `i` is `Σ_h weights[h] src[i + h dst_rows]`.
///
/// # Safety
/// `src` holds `weights.len() dst_rows` rows, `dst` `dst_rows`, disjoint.
unsafe fn fold_rows(src: *const u64, dst: *mut u64, dst_rows: usize, weights: &[F64]) {
    let (src, dst) = (SendPtr(src.cast_mut()), SendPtr(dst));
    if dst_rows < 64 {
        // Few rows: the blocks `h` split among the workers, their partial sums added.
        let per = weights.len().div_ceil(64).max(1);
        let sum = parallel::map_reduce(
            weights.len().div_ceil(per),
            || vec![K8::ZERO; dst_rows],
            |task| {
                let mut acc = vec![K8::ZERO; dst_rows];
                for h in task * per..((task + 1) * per).min(weights.len()) {
                    let w = splat(weights[h].0);
                    for (i, a) in acc.iter_mut().enumerate() {
                        let p: *mut u64 = a.0.as_mut_ptr().cast();
                        // SAFETY: row `i + h dst_rows` of `src`, and the accumulator's own row.
                        unsafe { store(p, xor(load(p), mul(load(src.add(8 * (i + h * dst_rows))), w))) }
                    }
                }
                acc
            },
            |mut a, b| {
                for (x, y) in a.iter_mut().zip(&b) {
                    x.0.iter_mut().zip(&y.0).for_each(|(x, &y)| *x += y);
                }
                a
            },
        );
        // SAFETY: `dst_rows` rows of `dst`.
        unsafe { std::ptr::copy_nonoverlapping(sum.as_ptr().cast::<u64>(), dst.add(0), 8 * dst_rows) };
        return;
    }
    let chunk = (dst_rows / 128).clamp(1, 64);
    parallel::for_each(dst_rows / chunk, |task| {
        // SAFETY: a task writes its own `chunk` rows of `dst` and reads `src`.
        unsafe {
            for i in task * chunk..(task + 1) * chunk {
                let mut acc = load(src.add(8 * i));
                if weights[0] != F64::ONE {
                    acc = mul(acc, splat(weights[0].0));
                }
                for (h, &w) in weights.iter().enumerate().skip(1) {
                    acc = xor(acc, mul(load(src.add(8 * (i + h * dst_rows))), splat(w.0)));
                }
                store(dst.add(8 * i), acc);
            }
        }
    });
}

/// A batch of novel coefficients folded onto the coset `ω_first + V_e` (`2^e ≤ src.len()`), into `dst`.
pub fn fold_batch(src: &[K8], first: usize, dst: &mut [K8]) {
    let rows = dst.len();
    assert_eq!(src.len() % rows, 0);
    let weights = novel_weights(src.len() / rows, first, rows.trailing_zeros() as usize);
    // SAFETY: `src` is `weights.len()` blocks of `dst`'s rows.
    unsafe { fold_rows(src.as_ptr().cast(), words(dst), rows, &weights) }
}

/// The column with `weights`' fold onto `2^e` entries: `out[i] = Σ_h weights[h] data[i + h 2^e]`.
fn fold_column(data: &[F64], e: usize, weights: &[F64]) -> Vec<F64> {
    let size = 1usize << e;
    assert_eq!(data.len(), weights.len() * size);
    if size < 8 {
        let per = weights.len().div_ceil(64).max(1);
        return parallel::map_reduce(
            weights.len().div_ceil(per),
            || vec![F64::ZERO; size],
            |task| {
                let mut acc = vec![F64::ZERO; size];
                for h in task * per..((task + 1) * per).min(weights.len()) {
                    acc.iter_mut()
                        .zip(&data[h * size..])
                        .for_each(|(a, &x)| *a += weights[h] * x);
                }
                acc
            },
            |mut a, b| {
                a.iter_mut().zip(&b).for_each(|(x, &y)| *x += y);
                a
            },
        );
    }
    // SAFETY (x2): `fold_rows` writes every row of `out`; `data` is `weights.len()` blocks of its rows.
    let mut out = unsafe { unwritten(size) };
    unsafe { fold_rows(data.as_ptr().cast(), out.as_mut_ptr().cast(), size / 8, weights) }
    out
}

/// The values on the coset `ω_first + V_e` of the column of novel coefficients `novel` (any multiple of `2^e` of
/// them, `2^e | first`).
pub fn on_coset_prefix(novel: &[F64], first: usize, e: usize) -> Vec<F64> {
    let size = 1usize << e;
    if novel.len() == size {
        // SAFETY: `values_from` writes every word first.
        let mut out = unsafe { unwritten(size) };
        values_from(novel, &mut out, point(first));
        return out;
    }
    let mut out = fold_column(novel, e, &novel_weights(novel.len() / size, first, e));
    values(&mut out, point(first));
    out
}

/// `ṽ(bits(i) + δ)` for every `i < 2^e`, `ṽ` the multilinear of `values` (`2^r` of them, `e ≤ r`): the top `r - e`
/// variables at `δ` (a fold), then the shifted cube of the rest.
pub fn shifted_cube(values: &[F64], delta: &[F64], e: usize) -> Vec<F64> {
    let r = values.len().trailing_zeros() as usize;
    assert!(e <= r && delta.len() >= r);
    let mut out = if e == r {
        values.to_vec()
    } else {
        let weights = tensor(
            1 << (r - e),
            |b, bit| if bit { delta[e + b] } else { F64::ONE + delta[e + b] },
        );
        fold_column(values, e, &weights)
    };
    if out.len() < 8 {
        for (l, &d) in delta[..e].iter().enumerate() {
            let half = 1usize << l;
            for pair in out.chunks_exact_mut(2 * half) {
                let (lo, hi) = pair.split_at_mut(half);
                for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                    let t = d * (*a + *b);
                    *a += t;
                    *b += t;
                }
            }
        }
        return out;
    }
    let kind = Cube {
        delta: delta[..e].to_vec(),
    };
    // SAFETY: `out`'s own words, eight a row.
    unsafe { run(out.as_mut_ptr().cast(), None, out.len() / 8, 3, &kind, false) }
    out
}

/// [`shifted_cube`] by the calling worker alone: the same values.
pub fn shifted_cube_serial(values: &[F64], delta: &[F64], e: usize) -> Vec<F64> {
    let r = values.len().trailing_zeros() as usize;
    assert!(e <= r && delta.len() >= r);
    let size = 1usize << e;
    let mut out = if e == r {
        values.to_vec()
    } else {
        // `tensor`'s weights (the same products), then `fold_column`'s sums.
        let mut weights = vec![F64::ONE];
        for b in 0..r - e {
            let (zero, one) = (F64::ONE + delta[e + b], delta[e + b]);
            let high: Vec<F64> = weights.iter().map(|&w| w * one).collect();
            weights.iter_mut().for_each(|w| *w *= zero);
            weights.extend(high);
        }
        (0..size)
            .map(|i| weights.iter().enumerate().fold(F64::ZERO, |acc, (h, &w)| acc + w * values[i + h * size]))
            .collect()
    };
    if out.len() < 8 {
        for (l, &d) in delta[..e].iter().enumerate() {
            let half = 1usize << l;
            for pair in out.chunks_exact_mut(2 * half) {
                let (lo, hi) = pair.split_at_mut(half);
                for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                    let t = d * (*a + *b);
                    *a += t;
                    *b += t;
                }
            }
        }
        return out;
    }
    let kind = Cube {
        delta: delta[..e].to_vec(),
    };
    // SAFETY: `out`'s own words, eight a row.
    unsafe { run_on(out.as_mut_ptr().cast(), None, out.len() / 8, 3, &kind, false, true) }
    out
}

/// Columns of one length, each eight words a row, as [`run_cols`] takes them (read first from `srcs` if given).
fn column_cols(dsts: &mut [&mut [F64]], srcs: Option<&[&[F64]]>) -> Vec<Col> {
    let len = dsts.first().map_or(0, |d| d.len());
    assert!(dsts.iter().all(|d| d.len() == len));
    dsts.iter_mut()
        .enumerate()
        .map(|(c, d)| Col {
            data: SendPtr(d.as_mut_ptr().cast()),
            src: srcs.map(|s| {
                assert_eq!(s[c].len(), len);
                SendPtr(s[c].as_ptr().cast::<u64>().cast_mut())
            }),
        })
        .collect()
}

/// [`values`] on several columns of one length at once: each pass's tasks for all of them in one dispatch.
pub fn values_cols(cols: &mut [&mut [F64]], offset: F64) {
    let len = cols.first().map_or(0, |c| c.len());
    if len < 8 {
        return cols.iter_mut().for_each(|c| values(c, offset));
    }
    let kind = Forward(Twiddles::new(offset, len.trailing_zeros() as usize));
    let cols = column_cols(cols, None);
    // SAFETY: the columns' own words, eight a row, disjoint (distinct `&mut`).
    unsafe { run_cols(&cols, len / 8, 3, &kind, false, false) }
}

/// [`coefficients`] on several columns of one length at once.
pub fn coefficients_cols(cols: &mut [&mut [F64]], offset: F64) {
    let len = cols.first().map_or(0, |c| c.len());
    if len < 8 {
        return cols.iter_mut().for_each(|c| coefficients(c, offset));
    }
    let kind = Inverse(Twiddles::new(offset, len.trailing_zeros() as usize));
    let cols = column_cols(cols, None);
    // SAFETY: the columns' own words, eight a row, disjoint.
    unsafe { run_cols(&cols, len / 8, 3, &kind, false, false) }
}

/// [`values_from`] on several columns of one length at once.
pub fn values_from_cols(srcs: &[&[F64]], dsts: &mut [&mut [F64]], offset: F64) {
    let len = dsts.first().map_or(0, |c| c.len());
    if len < 8 {
        return dsts.iter_mut().zip(srcs).for_each(|(d, s)| values_from(s, d, offset));
    }
    let kind = Forward(Twiddles::new(offset, len.trailing_zeros() as usize));
    let cols = column_cols(dsts, Some(srcs));
    // SAFETY: the destinations' own words, eight a row, read first from their sources'.
    unsafe { run_cols(&cols, len / 8, 3, &kind, false, false) }
}

/// [`coefficients_from`] on several columns of one length at once.
pub fn coefficients_from_cols(srcs: &[&[F64]], dsts: &mut [&mut [F64]], offset: F64) {
    let len = dsts.first().map_or(0, |c| c.len());
    if len < 8 {
        return dsts.iter_mut().zip(srcs).for_each(|(d, s)| coefficients_from(s, d, offset));
    }
    let kind = Inverse(Twiddles::new(offset, len.trailing_zeros() as usize));
    let cols = column_cols(dsts, Some(srcs));
    // SAFETY: the destinations' own words, eight a row, read first from their sources'.
    unsafe { run_cols(&cols, len / 8, 3, &kind, false, false) }
}

/// [`coefficients_from_cols`] into new columns.
pub fn coefficients_cols_of(srcs: &[&[F64]], offset: F64) -> Vec<Vec<F64>> {
    let len = srcs.first().map_or(0, |c| c.len());
    assert!(srcs.iter().all(|c| c.len() == len));
    // SAFETY: the transform writes every word first (its first pass reads the sources).
    let mut out: Vec<Vec<F64>> = srcs.iter().map(|_| unsafe { unwritten(len) }).collect();
    coefficients_from_cols(srcs, &mut out.iter_mut().map(|o| &mut o[..]).collect::<Vec<_>>(), offset);
    out
}

/// [`subset_sums_many`] into new columns, each its source's length (a power of two).
pub fn subset_sums_of_cols(srcs: &[&[F64]]) -> Vec<Vec<F64>> {
    // SAFETY: the sums write every word first (each block copied from its source).
    let mut out: Vec<Vec<F64>> = srcs.iter().map(|s| unsafe { unwritten(s.len()) }).collect();
    let mut jobs: Vec<(&[F64], &mut [F64])> = srcs.iter().copied().zip(out.iter_mut().map(|o| &mut o[..])).collect();
    subset_sums_many(&mut jobs);
    out
}

/// [`values_from`] by the calling worker alone.
pub fn values_from_serial(src: &[F64], dst: &mut [F64], offset: F64) {
    assert_eq!(src.len(), dst.len());
    if dst.len() < 8 {
        dst.copy_from_slice(src);
        return crate::domain::values(dst, offset);
    }
    let kind = Forward(Twiddles::new(offset, dst.len().trailing_zeros() as usize));
    // SAFETY: `dst`'s own words, eight a row, read first from `src`'s.
    unsafe {
        run_on(
            dst.as_mut_ptr().cast(),
            Some(src.as_ptr().cast()),
            dst.len() / 8,
            3,
            &kind,
            false,
            true,
        )
    }
}

/// [`on_coset_prefix`] of `novel` into `out` (`2^e` words), by the calling worker alone.
pub fn on_coset_prefix_serial(novel: &[F64], first: usize, out: &mut [F64]) {
    let size = out.len();
    assert!(size.is_power_of_two() && novel.len().is_multiple_of(size));
    let e = size.trailing_zeros() as usize;
    if novel.len() == size {
        return values_from_serial(novel, out, point(first));
    }
    // `novel_weights`' products in `tensor`'s order, then `fold_rows`' (or `fold_column`'s) sums: the same values.
    let blocks = novel.len() / size;
    let mut weights = vec![F64::ONE];
    let mut b = 0;
    while weights.len() < blocks {
        let one = point(first >> (e + b));
        let half = weights.len();
        for h in 0..half {
            let w = weights[h] * one;
            weights.push(w);
        }
        b += 1;
    }
    for (i, o) in out.iter_mut().enumerate() {
        *o = (0..blocks).fold(F64::ZERO, |acc, h| acc + weights[h] * novel[i + h * size]);
    }
    if size < 8 {
        return crate::domain::values(out, point(first));
    }
    let kind = Forward(Twiddles::new(point(first), e));
    // SAFETY: `out`'s own words, eight a row.
    unsafe { run_on(out.as_mut_ptr().cast(), None, size / 8, 3, &kind, false, true) }
}

/// [`on_coset_prefix`] of several columns of one length at once.
pub fn on_coset_prefix_cols(novels: &[&[F64]], first: usize, e: usize) -> Vec<Vec<F64>> {
    let size = 1usize << e;
    let len = novels.first().map_or(0, |n| n.len());
    assert!(novels.iter().all(|n| n.len() == len) && len.is_multiple_of(size));
    // SAFETY: both ways below write every word of every output first (`values_from_cols`, or the fold's tasks, which
    // cover every row).
    let mut out: Vec<Vec<F64>> = novels.iter().map(|_| unsafe { unwritten(size) }).collect();
    if len == size {
        let mut dsts: Vec<&mut [F64]> = out.iter_mut().map(|o| &mut o[..]).collect();
        values_from_cols(novels, &mut dsts, point(first));
        return out;
    }
    if size < 64 {
        // Few rows: as one column at a time.
        return novels.iter().map(|n| on_coset_prefix(n, first, e)).collect();
    }
    let weights = novel_weights(len / size, first, e);
    let rows = size / 8;
    let chunk = (rows / 128).clamp(1, 64);
    let per = rows / chunk;
    let dsts: Vec<SendPtr<u64>> = out.iter_mut().map(|o| SendPtr(o.as_mut_ptr().cast())).collect();
    // `fold_rows`' sums, its tasks for every column in one dispatch.
    parallel::for_each(per * novels.len(), |t| {
        let (c, task) = (t / per, t % per);
        let src: *const u64 = novels[c].as_ptr().cast();
        // SAFETY: a task writes its own `chunk` rows of column `c`'s output and reads its source.
        unsafe {
            for i in task * chunk..(task + 1) * chunk {
                let mut acc = load(src.add(8 * i));
                if weights[0] != F64::ONE {
                    acc = mul(acc, splat(weights[0].0));
                }
                for (h, &w) in weights.iter().enumerate().skip(1) {
                    acc = xor(acc, mul(load(src.add(8 * (i + h * rows))), splat(w.0)));
                }
                store(dsts[c].add(8 * i), acc);
            }
        }
    });
    let mut dsts: Vec<&mut [F64]> = out.iter_mut().map(|o| &mut o[..]).collect();
    values_cols(&mut dsts, point(first));
    out
}

/// [`interpolate_prefix`] on several columns at once (one length, the same blocks), each step's dispatches for all
/// of them: the same values.
pub fn interpolate_prefix_cols(data: &mut [&mut [F64]], sizes: &[usize], base: usize) {
    let total: usize = sizes.iter().map(|&e| 1usize << e).sum();
    assert!(data.iter().all(|d| d.len() == total));
    assert!(sizes.windows(2).all(|w| w[0] > w[1]) && base % (2 << sizes[0]) == 0);
    let starts = prefix_starts(sizes, base);
    let ptrs: Vec<SendPtr<F64>> = data.iter_mut().map(|d| SendPtr(d.as_mut_ptr())).collect();
    // Column `c`'s words `at..at + len`.
    // SAFETY (all uses): each call's ranges are disjoint from the others' live at once, inside `data[c]`.
    let range = |c: usize, at: usize, len: usize| -> &mut [F64] { unsafe { ptrs[c].slice(at, len) } };
    let n = data.len();
    // Each block's inverse transform, which needs no other block's.
    for j in 0..sizes.len() {
        let (at, e) = (starts[j] - base, sizes[j]);
        let mut us: Vec<&mut [F64]> = (0..n).map(|c| range(c, at, 1 << e)).collect();
        coefficients_cols(&mut us, point(starts[j]));
    }
    // `U_j` plus the earlier `U_i`'s folds onto block `j`.
    for j in 1..sizes.len() {
        let (at, e) = (starts[j] - base, sizes[j]);
        let folds = earlier_folds(&starts, sizes, base, j);
        let size = 1usize << e;
        let rows = size.div_ceil(8);
        let chunk = (rows / 128).clamp(1, 64);
        let per = rows.div_ceil(chunk);
        parallel::for_each(per * n, |t| {
            let (c, k) = (t / per, t % per);
            let (lo, hi) = (k * chunk, ((k + 1) * chunk).min(rows));
            // SAFETY: the block's rows `lo..hi` of column `c` are this task's; the earlier blocks are only read.
            unsafe { add_folds(ptrs[c].0, at, size, lo..hi, &folds) }
        });
    }
    back_substitute(&ptrs, n, &starts, sizes, base, total);
}

/// The earlier blocks' folds onto block `j`: each block `i < j`'s first word (from `base`) and the weights of its
/// `2^(e_i - e_j)` runs of `2^(e_j)` words ([`novel_weights`] onto block `j`'s coset).
fn earlier_folds(starts: &[usize], sizes: &[usize], base: usize, j: usize) -> Vec<(usize, Vec<F64>)> {
    let e = sizes[j];
    (0..j)
        .map(|i| (starts[i] - base, novel_weights(1 << (sizes[i] - e), starts[j], e)))
        .collect()
}

/// Rows `rows` (of eight words, or the block's words if fewer) of the `size` words at `data + at` plus each fold's
/// `Σ_h weights[h] data[from + h size + ·]`.
///
/// # Safety
/// The words read and written are in the column, the rows written no other task's.
unsafe fn add_folds(data: *mut F64, at: usize, size: usize, rows: std::ops::Range<usize>, folds: &[(usize, Vec<F64>)]) {
    // SAFETY (all): the caller's.
    unsafe {
        if size < 8 {
            for i in 0..size {
                let mut acc = *data.add(at + i);
                for (from, weights) in folds {
                    for (h, &w) in weights.iter().enumerate() {
                        acc += w * *data.add(from + h * size + i);
                    }
                }
                *data.add(at + i) = acc;
            }
            return;
        }
        let words = data.cast::<u64>();
        for r in rows {
            let i = 8 * r;
            let mut acc = load(words.add(at + i));
            for (from, weights) in folds {
                for (h, &w) in weights.iter().enumerate() {
                    acc = xor(acc, mul(load(words.add(from + h * size + i)), splat(w.0)));
                }
            }
            store(words.add(at + i), acc);
        }
    }
}

/// [`interpolate_prefix`]'s last step on columns: `Q_j = U_j + λ_j R_(j+1)` from the end.
fn back_substitute(ptrs: &[SendPtr<F64>], n: usize, starts: &[usize], sizes: &[usize], base: usize, total: usize) {
    // SAFETY (all uses): each call's ranges are disjoint from the others' live at once, inside the columns.
    let range = |c: usize, at: usize, len: usize| -> &mut [F64] { unsafe { ptrs[c].slice(at, len) } };
    for j in (0..sizes.len().saturating_sub(1)).rev() {
        let (at, e) = (starts[j] - base, sizes[j]);
        let lambda = point(starts[j] >> e);
        let len = total - at - (1 << e);
        const CHUNK: usize = 1 << 14;
        let per = len.div_ceil(CHUNK);
        parallel::for_each(per * n, |t| {
            let (c, k) = (t / per, t % per);
            let (lo, hi) = (k * CHUNK, ((k + 1) * CHUNK).min(len));
            let q = range(c, at + lo, hi - lo);
            let r = range(c, at + (1 << e) + lo, hi - lo);
            q.iter_mut().zip(r.iter()).for_each(|(x, &y)| *x += lambda * y);
        });
    }
}

/// [`coefficients_cols`] with each column on its own coset (`offsets[c]` for column `c`), all of one length: every
/// pass's tasks for all of them in one dispatch.
pub fn coefficients_cols_each(cols: &mut [&mut [F64]], offsets: &[F64]) {
    assert_eq!(cols.len(), offsets.len());
    let len = cols.first().map_or(0, |c| c.len());
    if len < 8 {
        return cols.iter_mut().zip(offsets).for_each(|(c, &o)| coefficients(c, o));
    }
    let kinds: Vec<Inverse> = offsets
        .iter()
        .map(|&o| Inverse(Twiddles::new(o, len.trailing_zeros() as usize)))
        .collect();
    let cols = column_cols(cols, None);
    // SAFETY: the columns' own words, eight a row, disjoint (distinct `&mut`).
    unsafe { run_cols_each(&cols, &kinds, len / 8, 3, false, false) }
}

/// One quotient's columns for [`interpolate_prefix_many`]: their values at `ω_(base + i)` (one length, `Σ 2^sizes`),
/// as [`interpolate_prefix_cols`] takes them.
pub struct PrefixCols<'a> {
    pub cols: Vec<&'a mut [F64]>,
    pub sizes: Vec<usize>,
    pub base: usize,
}

/// A step's tasks over several parts, `counts[k]` of them part `k`'s: a task's part and its index there.
struct Spans(Vec<usize>);

impl Spans {
    fn new(counts: impl IntoIterator<Item = usize>) -> Self {
        let mut firsts = vec![0];
        for c in counts {
            firsts.push(firsts[firsts.len() - 1] + c);
        }
        Self(firsts)
    }

    fn total(&self) -> usize {
        self.0[self.0.len() - 1]
    }

    #[inline]
    fn locate(&self, t: usize) -> (usize, usize) {
        let k = self.0.partition_point(|&f| f <= t) - 1;
        (k, t - self.0[k])
    }
}

/// [`interpolate_prefix_cols`] on several quotients at once, each step's tasks for all of them in one dispatch: every
/// block's inverse transform (the blocks of one size together, each on its coset), then the earlier blocks' folds
/// block index by block index, then the back substitution from each quotient's end. The same values.
pub fn interpolate_prefix_many(jobs: &mut [PrefixCols<'_>]) {
    struct Job {
        ptrs: Vec<SendPtr<F64>>,
        starts: Vec<usize>,
        sizes: Vec<usize>,
        base: usize,
        total: usize,
    }
    let js: Vec<Job> = jobs
        .iter_mut()
        .map(|j| {
            let total: usize = j.sizes.iter().map(|&e| 1usize << e).sum();
            assert!(j.cols.iter().all(|d| d.len() == total));
            assert!(j.sizes.windows(2).all(|w| w[0] > w[1]) && j.base % (2 << j.sizes[0]) == 0);
            Job {
                ptrs: j.cols.iter_mut().map(|d| SendPtr(d.as_mut_ptr())).collect(),
                starts: prefix_starts(&j.sizes, j.base),
                sizes: j.sizes.clone(),
                base: j.base,
                total,
            }
        })
        .collect();
    // 1. Each block's inverse transform, which needs no other block's: the blocks of one size in one call.
    let mut by_size: std::collections::BTreeMap<usize, (Vec<&mut [F64]>, Vec<F64>)> = Default::default();
    for job in &js {
        for (j, &e) in job.sizes.iter().enumerate() {
            let at = job.starts[j] - job.base;
            for ptr in &job.ptrs {
                let entry = by_size.entry(e).or_default();
                // SAFETY: block `j` of a column, disjoint from every other entry's.
                entry.0.push(unsafe { ptr.slice(at, 1 << e) });
                entry.1.push(point(job.starts[j]));
            }
        }
    }
    for (_, (mut cols, offsets)) in by_size.into_iter().rev() {
        coefficients_cols_each(&mut cols, &offsets);
    }
    // 2. `U_j` plus the earlier `U_i`'s folds onto block `j`, block index by block index.
    let most = js.iter().map(|j| j.sizes.len()).max().unwrap_or(0);
    for j in 1..most {
        struct Part {
            q: usize,
            at: usize,
            size: usize,
            rows: usize,
            chunk: usize,
            per: usize,
            folds: Vec<(usize, Vec<F64>)>,
        }
        let parts: Vec<Part> = js
            .iter()
            .enumerate()
            .filter(|(_, job)| job.sizes.len() > j)
            .map(|(q, job)| {
                let (at, e) = (job.starts[j] - job.base, job.sizes[j]);
                let size = 1usize << e;
                let rows = size.div_ceil(8);
                let chunk = (rows / 128).clamp(1, 64);
                Part {
                    q,
                    at,
                    size,
                    rows,
                    chunk,
                    per: rows.div_ceil(chunk),
                    folds: earlier_folds(&job.starts, &job.sizes, job.base, j),
                }
            })
            .collect();
        let spans = Spans::new(parts.iter().map(|p| p.per * js[p.q].ptrs.len()));
        parallel::for_each(spans.total(), |t| {
            let (k, i) = spans.locate(t);
            let p = &parts[k];
            let (c, i) = (i / p.per, i % p.per);
            let (lo, hi) = (i * p.chunk, ((i + 1) * p.chunk).min(p.rows));
            // SAFETY: the block's rows `lo..hi` of column `c` of quotient `p.q` are this task's; the earlier blocks
            // are only read.
            unsafe { add_folds(js[p.q].ptrs[c].0, p.at, p.size, lo..hi, &p.folds) }
        });
    }
    // 3. `Q_j = U_j + λ_j R_(j+1)` from each quotient's end: step `k` is block `len - 2 - k` of each.
    const CHUNK: usize = 1 << 14;
    for k in 0..most.saturating_sub(1) {
        // (quotient, the block's first word, its size's log, λ, the words added)
        let parts: Vec<(usize, usize, usize, F64, usize)> = js
            .iter()
            .enumerate()
            .filter(|(_, job)| job.sizes.len() >= k + 2)
            .map(|(q, job)| {
                let j = job.sizes.len() - 2 - k;
                let (at, e) = (job.starts[j] - job.base, job.sizes[j]);
                (q, at, e, point(job.starts[j] >> e), job.total - at - (1 << e))
            })
            .collect();
        let spans = Spans::new(parts.iter().map(|p| p.4.div_ceil(CHUNK) * js[p.0].ptrs.len()));
        parallel::for_each(spans.total(), |t| {
            let (p, i) = spans.locate(t);
            let (q, at, e, lambda, len) = parts[p];
            let per = len.div_ceil(CHUNK);
            let (c, i) = (i / per, i % per);
            let (lo, hi) = (i * CHUNK, ((i + 1) * CHUNK).min(len));
            // SAFETY: the task's words of block `j` are its own; the later blocks' (`R_(j+1)`) are only read.
            let (x, y) = unsafe {
                (
                    js[q].ptrs[c].slice(at + lo, hi - lo),
                    js[q].ptrs[c].slice(at + (1 << e) + lo, hi - lo),
                )
            };
            x.iter_mut().zip(y.iter()).for_each(|(x, &y)| *x += lambda * y);
        });
    }
}

/// [`on_coset_prefix`] of several columns at once, column `c` on its own small coset `ω_(first_c) + V_(e_c)` (`e_c ≤
/// 6`, `2^(e_c)` dividing its length and `first_c`): the folds' partial sums for all of them in one dispatch, each
/// task over `2^12` of a column's blocks; then each column's sum and transform.
pub fn on_coset_prefix_each(cols: &[(&[F64], usize, usize)]) -> Vec<Vec<F64>> {
    const LOW: usize = 12;
    // Per column: its blocks of `2^e` words, the weights of the low bits of a block's index and the factors of its
    // high ones: `novel_weights`' products, `point(first >> (e + b))` over the bits `b` of the block's index.
    struct Part<'a> {
        data: &'a [F64],
        size: usize,
        blocks: usize,
        low: Vec<F64>,
        high: Vec<F64>,
    }
    let parts: Vec<Part> = cols
        .iter()
        .map(|&(data, first, e)| {
            let size = 1usize << e;
            assert!(e <= 6 && data.len().is_multiple_of(size) && first.is_multiple_of(size));
            let blocks = data.len() / size;
            let bits = blocks.max(1).next_power_of_two().trailing_zeros() as usize;
            let factor = |b: usize| point(first >> (e + b));
            let mut low = vec![F64::ONE];
            for b in 0..bits.min(LOW) {
                let one = factor(b);
                let high: Vec<F64> = low.iter().map(|&l| l * one).collect();
                low.extend(high);
            }
            let high = (LOW..bits.max(LOW)).map(factor).collect();
            Part {
                data,
                size,
                blocks,
                low,
                high,
            }
        })
        .collect();
    let spans = Spans::new(parts.iter().map(|p| p.blocks.div_ceil(1 << LOW)));
    let partial: Vec<Vec<F64>> = parallel::map_collect(spans.total(), |t| {
        let (k, i) = spans.locate(t);
        let p = &parts[k];
        // The high bits' factor of this task's blocks.
        let high = p
            .high
            .iter()
            .enumerate()
            .filter(|&(b, _)| i >> b & 1 == 1)
            .fold(F64::ONE, |acc, (_, &f)| acc * f);
        let mut acc = vec![F64::ZERO; p.size];
        for h in i << LOW..((i + 1) << LOW).min(p.blocks) {
            let w = p.low[h & ((1 << LOW) - 1)] * high;
            acc.iter_mut().zip(&p.data[h * p.size..]).for_each(|(a, &x)| *a += w * x);
        }
        acc
    });
    parts
        .iter()
        .enumerate()
        .map(|(k, p)| {
            let mut out = vec![F64::ZERO; p.size];
            for acc in &partial[spans.0[k]..spans.0[k + 1]] {
                out.iter_mut().zip(acc).for_each(|(o, &a)| *o += a);
            }
            crate::domain::values(&mut out, point(cols[k].1));
            out
        })
        .collect()
}

/// The interpolation blocks: `count` rounded up to a multiple of `2^grain`, in binary, largest first.
pub fn prefix_sizes(count: u64, grain: usize) -> Vec<usize> {
    let units = count.max(1).div_ceil(1 << grain);
    (0..64)
        .rev()
        .filter(|&b| units >> b & 1 == 1)
        .map(|b| b + grain)
        .collect()
}

/// The first point of each block, from `base`: block `j` is the coset `ω_(starts[j]) + V_(sizes[j])`.
pub fn prefix_starts(sizes: &[usize], base: usize) -> Vec<usize> {
    let mut at = base;
    sizes
        .iter()
        .map(|&e| {
            let s = at;
            at += 1 << e;
            s
        })
        .collect()
}

/// The novel coefficients of the polynomial of degree `< T = Σ 2^(sizes[j])` whose values at `ω_(base + i)`, `i < T`,
/// are `data` (in place). `sizes` decrease strictly and `2^(sizes[0] + 1) | base`.
///
/// With `R_0 = Q` and `R_j = Q_j + w_(e_j) R_(j+1)`, `deg Q_j < 2^(e_j)`: on block `j`, `w_(e_j)` is a constant
/// `λ_j`, so the inverse transform there gives `U_j = Q_j + λ_j R_(j+1)`; on the later blocks `w_(e_j) = λ_j + 1`, so
/// `R_(j+1) = R_j + U_j` there. Last, `Q_j = U_j + λ_j R_(j+1)` from the end, and `Q = [Q_0, Q_1, ...]` (since
/// `X_(2^e + k) = w_e X_k`).
///
/// Block `j`'s values of `R_j` are its values of `Q` plus every earlier `U_i`'s there, so its inverse transform is that
/// of `Q`'s values plus each `U_i`'s fold onto its coset (the inverse of [`on_coset_prefix`]): every block's transform
/// on `Q`'s values first, then the folds added, no forward transform.
pub fn interpolate_prefix(data: &mut [F64], sizes: &[usize], base: usize) {
    interpolate_prefix_cols(&mut [data], sizes, base);
}

/// Novel to `B` coefficients (or back), in place: `b_k = Σ_(j ⊆ k) a_j`. The low variables on blocks of 256 KiB
/// one worker holds, then the rest a few at a time on tiles. The variables' maps commute.
pub fn subset_sums<M: Copy + Send + Sync + Add<Output = M> + Default>(data: &mut [M]) {
    subset_sums_of(data, None);
}

/// [`subset_sums`] of `src` (zero past its end, `src.len() ≤ dst.len()`), written to `dst`.
pub fn subset_sums_from<M: Copy + Send + Sync + Add<Output = M> + Default>(src: &[M], dst: &mut [M]) {
    assert!(src.len() <= dst.len());
    subset_sums_of(dst, Some(src));
}

/// The variables [`subset_sums`] takes on blocks one worker holds (256 KiB).
fn subset_leaf<M>(m: usize) -> usize {
    m.min(((1usize << 18) / std::mem::size_of::<M>()).max(2).ilog2() as usize)
}

/// [`subset_sums`]' low variables on block `b` (of `2^leaf`) of a column, read first from `src` (zero past its end).
fn subset_block<M: Copy + Add<Output = M> + Default>(block: &mut [M], b: usize, leaf: usize, src: Option<&[M]>) {
    if let Some(src) = src {
        let at = (b << leaf).min(src.len());
        let have = (src.len() - at).min(block.len());
        block[..have].copy_from_slice(&src[at..at + have]);
        block[have..].fill(M::default());
    }
    let mut half = 1;
    while half < block.len() {
        for pair in block.chunks_exact_mut(2 * half) {
            let (lo, hi) = pair.split_at_mut(half);
            for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                *h = *h + l;
            }
        }
        half *= 2;
    }
}

/// [`subset_sums_from`] of several columns (any lengths, each `src` at most its `dst`): every column's blocks in one
/// dispatch, then each longer column's upper variables. The same values.
pub fn subset_sums_many<M: Copy + Send + Sync + Add<Output = M> + Default>(jobs: &mut [(&[M], &mut [M])]) {
    // (job, block, the block's length): every column's low variables.
    let mut blocks: Vec<(usize, usize, usize)> = Vec::new();
    for (k, (src, dst)) in jobs.iter().enumerate() {
        let n = dst.len();
        assert!(n.is_power_of_two() && src.len() <= n);
        let leaf = subset_leaf::<M>(n.trailing_zeros() as usize);
        blocks.extend((0..n >> leaf).map(|b| (k, b, leaf)));
    }
    let dsts: Vec<SendPtr<M>> = jobs.iter_mut().map(|(_, d)| SendPtr(d.as_mut_ptr())).collect();
    let srcs: Vec<&[M]> = jobs.iter().map(|(s, _)| *s).collect();
    tasks(blocks.len(), false, |t| {
        let (k, b, leaf) = blocks[t];
        // SAFETY: task `t` writes block `b` of column `k` alone, inside it.
        let block = unsafe { dsts[k].slice(b << leaf, 1 << leaf) };
        subset_block(block, b, leaf, Some(srcs[k]));
    });
    // The longer columns' upper variables, the columns of one length together.
    let mut lengths: Vec<usize> = jobs.iter().map(|(_, d)| d.len()).collect();
    lengths.sort_unstable();
    lengths.dedup();
    for len in lengths {
        let m = len.trailing_zeros() as usize;
        let leaf = subset_leaf::<M>(m);
        if leaf < m {
            let bases: Vec<SendPtr<M>> = jobs
                .iter_mut()
                .filter(|(_, d)| d.len() == len)
                .map(|(_, d)| SendPtr(d.as_mut_ptr()))
                .collect();
            subset_upper_of(&bases, len, leaf);
        }
    }
}

/// What [`filled_column`] writes in a block.
#[derive(Clone, Copy, Debug)]
pub enum Fill<'a> {
    /// The `B` coefficients of these novel ones (at most the block's length, zero past their end):
    /// [`subset_sums_from`].
    Sums(&'a [F64]),
    /// These words as they are (the block's length).
    Words(&'a [F64]),
    /// These 64-bit words as field words (the block's length).
    Raw(&'a [u64]),
}

/// A new column of `len` words: each job's block (`offset`, `2^k` words) holding its [`Fill`], every other word zero;
/// the blocks disjoint. As zeros then [`subset_sums_many`] and copies, but each word written once, not zeroed first:
/// the blocks' low variables (and the copies, and the zeros between and after the blocks) in one dispatch, then the
/// longer blocks' upper variables. A prover's stack of columns (620 MB for π1's C1 at the reference shape: its
/// zeroing pass took the workers 2.9 ms).
pub fn filled_column(len: usize, jobs: &[(usize, usize, Fill<'_>)]) -> Vec<F64> {
    /// Words a copy or a zeroing task takes.
    const RUN: usize = 1 << 16;
    #[derive(Clone, Copy)]
    enum Task {
        /// Block `b` (of `2^leaf`) of job `k`'s subset sums.
        Sums { k: usize, b: usize, leaf: usize },
        /// Words `at..at + n` of job `k`, copied.
        Copy { k: usize, at: usize, n: usize },
        /// Words `at..at + n` of the column, zero.
        Zero { at: usize, n: usize },
    }
    let mut order: Vec<usize> = (0..jobs.len()).collect();
    order.sort_by_key(|&k| jobs[k].0);
    let mut list: Vec<Task> = Vec::new();
    let zeros = |list: &mut Vec<Task>, from: usize, to: usize| {
        list.extend((from..to).step_by(RUN).map(|at| Task::Zero { at, n: RUN.min(to - at) }));
    };
    let mut cursor = 0;
    for &k in &order {
        let (offset, n, fill) = jobs[k];
        assert!(n.is_power_of_two() && offset >= cursor && offset + n <= len, "disjoint blocks in the column");
        zeros(&mut list, cursor, offset);
        let copies = |list: &mut Vec<Task>| list.extend((0..n).step_by(RUN).map(|at| Task::Copy { k, at, n: RUN.min(n - at) }));
        match fill {
            Fill::Sums(src) => {
                assert!(src.len() <= n);
                let leaf = subset_leaf::<F64>(n.trailing_zeros() as usize);
                list.extend((0..n >> leaf).map(|b| Task::Sums { k, b, leaf }));
            }
            Fill::Words(src) => {
                assert_eq!(src.len(), n);
                copies(&mut list);
            }
            Fill::Raw(src) => {
                assert_eq!(src.len(), n);
                copies(&mut list);
            }
        }
        cursor = offset + n;
    }
    zeros(&mut list, cursor, len);
    // SAFETY: the tasks tile the column (every block, every word between and after them), each word written below
    // before any is read.
    let mut out = unsafe { unwritten(len) };
    let base = SendPtr(out.as_mut_ptr());
    tasks(list.len(), false, |t| match list[t] {
        Task::Sums { k, b, leaf } => {
            let (offset, _, fill) = jobs[k];
            let Fill::Sums(src) = fill else { unreachable!("a sums job") };
            // SAFETY: task `t` alone writes these words of job `k`'s block.
            subset_block(unsafe { base.slice(offset + (b << leaf), 1 << leaf) }, b, leaf, Some(src));
        }
        Task::Copy { k, at, n } => {
            let (offset, _, fill) = jobs[k];
            // SAFETY: as above.
            let dst = unsafe { base.slice(offset + at, n) };
            match fill {
                Fill::Words(src) => dst.copy_from_slice(&src[at..at + n]),
                Fill::Raw(src) => dst.iter_mut().zip(&src[at..at + n]).for_each(|(d, &x)| *d = F64(x)),
                Fill::Sums(_) => unreachable!("a copy job"),
            }
        }
        // SAFETY: as above.
        Task::Zero { at, n } => unsafe { base.slice(at, n) }.fill(F64::ZERO),
    });
    // The longer blocks' upper variables, the blocks of one length together.
    let mut lengths: Vec<usize> = jobs.iter().filter(|j| matches!(j.2, Fill::Sums(_))).map(|j| j.1).collect();
    lengths.sort_unstable();
    lengths.dedup();
    for n in lengths {
        let leaf = subset_leaf::<F64>(n.trailing_zeros() as usize);
        if (1 << leaf) < n {
            let bases: Vec<SendPtr<F64>> = jobs
                .iter()
                .filter(|j| j.1 == n && matches!(j.2, Fill::Sums(_)))
                // SAFETY: inside `out`, each the start of a block of its own.
                .map(|j| SendPtr(unsafe { base.add(j.0) }))
                .collect();
            subset_upper_of(&bases, n, leaf);
        }
    }
    out
}

fn subset_sums_of<M: Copy + Send + Sync + Add<Output = M> + Default>(data: &mut [M], src: Option<&[M]>) {
    let n = data.len();
    assert!(n.is_power_of_two());
    let m = n.trailing_zeros() as usize;
    let leaf = subset_leaf::<M>(m);
    let base = SendPtr(data.as_mut_ptr());
    tasks(n >> leaf, false, |b| {
        // SAFETY: task `b` writes block `b` alone, inside `data`.
        subset_block(unsafe { base.slice(b << leaf, 1 << leaf) }, b, leaf, src)
    });
    subset_upper(data, leaf);
}

/// The most variables a pass of [`subset_upper_of`] takes, on tiles of `2^g` runs (of `2^(leaf - g)` words, 256 KiB
/// a tile): ten rather than eight, so that a column of `2^24` or `2^25` words takes one pass above its leaves, not two
/// (one column of `2^24` words, 64 threads: 3.0 → 2.2 ms; `2^25` 5.8 → 5.4 ms).
const SUBSET_GROUP: usize = 10;

/// [`subset_sums`]' variables from `leaf` up, a few at a time on tiles.
fn subset_upper<M: Copy + Send + Sync + Add<Output = M> + Default>(data: &mut [M], leaf: usize) {
    let n = data.len();
    subset_upper_of(&[SendPtr(data.as_mut_ptr())], n, leaf);
}

/// [`subset_upper`] of several columns of `n` words at `bases` (disjoint), each pass's tasks for all in one dispatch.
/// Up to [`SUBSET_GROUP`] variables a pass: one pass above the leaves up to `2^25` words of eight bytes.
fn subset_upper_of<M: Copy + Send + Sync + Add<Output = M> + Default>(bases: &[SendPtr<M>], n: usize, leaf: usize) {
    let m = n.trailing_zeros() as usize;
    let mut a = leaf;
    while a < m {
        let g = (m - a).min(SUBSET_GROUP);
        let lines = 1usize << g;
        let width = ((1usize << leaf) >> g).clamp(1, 1 << a);
        let per_group = (1usize << a) / width;
        let per = (n >> (a + g)) * per_group;
        tasks(per * bases.len(), false, |t| {
            let (base, task) = (bases[t / per], t % per);
            let e0 = ((task / per_group) << (a + g)) + (task % per_group) * width;
            for j in 0..g {
                let hs = 1usize << j;
                for ub in (0..lines).step_by(2 * hs) {
                    for u in ub..ub + hs {
                        // SAFETY: a task touches the runs `e0 + (u << a) + [0, width)`, `u < lines`: its own; the
                        // two runs here are distinct.
                        let (lo, hi) = unsafe {
                            (
                                base.slice(e0 + (u << a), width),
                                base.slice(e0 + ((u + hs) << a), width),
                            )
                        };
                        for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                            *h = *h + l;
                        }
                    }
                }
            }
        });
        a += g;
    }
}

// ---------------------------------------------------------------------------------------------------------------
// Split column transforms (`crate::protocol`'s reduction): the layers above a leaf on a whole column, and one
// leaf's own layers on one block, so that a caller can fuse its own pointwise work between a forward transform's
// last layers and an inverse transform's first, a block in cache, rather than make a pass over memory for each.
// [`values`] is [`values_upper`] then [`values_leaf`] on each block of [`LEAF_WORDS`]; [`coefficients`] is
// [`coefficients_leaf`] on each block then [`coefficients_upper`].
// ---------------------------------------------------------------------------------------------------------------

/// The rows of a leaf of the split transforms.
const SPLIT_LEAF_ROWS: usize = LEAF_ROWS;

/// The words of a leaf: the block [`values_leaf`] and [`coefficients_leaf`] take.
pub const LEAF_WORDS: usize = 8 * SPLIT_LEAF_ROWS;

/// The most of the layers above a leaf that one pass over memory takes in [`values_upper`] and
/// [`coefficients_upper`], and the rows of one of its tiles.
const UPPER_GROUP: usize = GROUP;
const UPPER_TILE_ROWS: usize = TILE_ROWS;

/// The groups of row layers above a leaf, the highest first: `(lowest layer, layers)`.
fn upper_groups(rows: usize) -> Vec<(usize, usize)> {
    let mr = rows.trailing_zeros() as usize;
    let leaf = mr.min(SPLIT_LEAF_ROWS.trailing_zeros() as usize);
    let mut groups = Vec::new();
    let mut top = mr;
    while top > leaf {
        let a = top.saturating_sub(UPPER_GROUP).max(leaf);
        groups.push((a, top - a));
        top = a;
    }
    groups
}

/// [`wide`] with [`UPPER_TILE_ROWS`].
fn upper<T: Kind>(data: SendPtr<u64>, src: Option<SendPtr<u64>>, rows: usize, a: usize, g: usize, kind: &T) {
    let lines = 1usize << g;
    let width = (UPPER_TILE_ROWS >> g).clamp(1, 1 << a);
    let per_group = (1usize << a) / width;
    tasks((rows >> (a + g)) * per_group, false, |task| {
        let row0 = ((task / per_group) << (a + g)) + (task % per_group) * width;
        let line = |u: usize| row0 + (u << a);
        // SAFETY: a task touches rows `line(u) + [0, width)`, `u < lines`: its own.
        unsafe {
            if let Some(s) = src {
                for u in 0..lines {
                    std::ptr::copy_nonoverlapping(s.add(8 * line(u)), data.add(8 * line(u)), 8 * width);
                }
            }
            tile_layers(kind, data, &line, a, g, width, 3, false);
        }
    });
}

/// The forward transform's layers above a leaf, on the column `dst` (a power of two, at least eight words), read
/// first from `src` if given (of `dst`'s length): with [`values_leaf`] on every block, [`values`] (`values_from`).
pub fn values_upper(src: Option<&[F64]>, dst: &mut [F64], offset: F64) {
    assert!(dst.len().is_power_of_two() && dst.len() >= 8);
    if let Some(s) = src {
        assert_eq!(s.len(), dst.len());
    }
    let rows = dst.len() / 8;
    let kind = Forward(Twiddles::new(offset, dst.len().trailing_zeros() as usize));
    let data = SendPtr(dst.as_mut_ptr().cast::<u64>());
    let mut from = src.map(|s| SendPtr(s.as_ptr().cast::<u64>().cast_mut()));
    let groups = upper_groups(rows);
    if groups.is_empty() {
        if let Some(s) = src {
            dst.copy_from_slice(s);
        }
        return;
    }
    for (a, g) in groups {
        upper(data, from.take(), rows, a, g, &kind);
    }
}

/// [`values_upper`] into each of `dsts` (all of `src`'s length) at its offset (`offsets[i]` for `dsts[i]`) of `src`
/// with `heads[i]` added to its leading words: the first pass reads each run of `src` once for all of them (from
/// cache for all but the first), the rest are each column's. The same values as one [`values_upper`] a column.
pub fn values_upper_many(src: &[F64], heads: &[&[F64]], dsts: &mut [&mut [F64]], offsets: &[F64]) {
    assert!(dsts.len() == offsets.len() && dsts.len() == heads.len());
    assert!(src.len().is_power_of_two() && src.len() >= 8);
    assert!(dsts.iter().all(|d| d.len() == src.len()));
    let rows = src.len() / 8;
    let groups = upper_groups(rows);
    if groups.is_empty() {
        for (d, head) in dsts.iter_mut().zip(heads) {
            d.copy_from_slice(src);
            d.iter_mut().zip(*head).for_each(|(w, &h)| *w += h);
        }
        return;
    }
    let log = src.len().trailing_zeros() as usize;
    let kinds: Vec<Forward> = offsets.iter().map(|&o| Forward(Twiddles::new(o, log))).collect();
    let datas: Vec<SendPtr<u64>> = dsts.iter_mut().map(|d| SendPtr(d.as_mut_ptr().cast::<u64>())).collect();
    let from = SendPtr(src.as_ptr().cast::<u64>().cast_mut());
    let (a, g) = groups[0];
    upper_from_many(&datas, from, heads, rows, a, g, &kinds);
    for &(a, g) in &groups[1..] {
        for (data, kind) in datas.iter().zip(&kinds) {
            upper(*data, None, rows, a, g, kind);
        }
    }
}

/// [`upper`] read from `src` into every column of `datas` (each with its kind, and its head added to its leading
/// words), a task's lines of `src` read once for all of them.
fn upper_from_many<T: Kind>(
    datas: &[SendPtr<u64>],
    src: SendPtr<u64>,
    heads: &[&[F64]],
    rows: usize,
    a: usize,
    g: usize,
    kinds: &[T],
) {
    let lines = 1usize << g;
    let width = (UPPER_TILE_ROWS >> g).clamp(1, 1 << a);
    let per_group = (1usize << a) / width;
    assert!(heads.iter().all(|h| h.len() <= 8 * width), "a head inside the first task's first line");
    tasks((rows >> (a + g)) * per_group, false, |task| {
        let row0 = ((task / per_group) << (a + g)) + (task % per_group) * width;
        let line = |u: usize| row0 + (u << a);
        for ((&data, kind), head) in datas.iter().zip(kinds).zip(heads) {
            // SAFETY: a task touches rows `line(u) + [0, width)`, `u < lines`, of each column: its own; the head's
            // words are the first of line 0 of task 0.
            unsafe {
                for u in 0..lines {
                    std::ptr::copy_nonoverlapping(src.add(8 * line(u)), data.add(8 * line(u)), 8 * width);
                }
                if row0 == 0 {
                    for (i, h) in head.iter().enumerate() {
                        *data.add(i) ^= h.0;
                    }
                }
                tile_layers(kind, data, &line, a, g, width, 3, false);
            }
        }
    });
}

/// The inverse transform's layers above a leaf, on the column `data`, after [`coefficients_leaf`] on every block.
pub fn coefficients_upper(data: &mut [F64], offset: F64) {
    assert!(data.len().is_power_of_two() && data.len() >= 8);
    let rows = data.len() / 8;
    let kind = Inverse(Twiddles::new(offset, data.len().trailing_zeros() as usize));
    let ptr = SendPtr(data.as_mut_ptr().cast::<u64>());
    for (a, g) in upper_groups(rows).into_iter().rev() {
        upper(ptr, None, rows, a, g, &kind);
    }
}

/// A transform whose rows' own layers take their twiddles given ([`Twiddles::row`]'s), for [`leaf`], which steps
/// them from row to row rather than computing each row's.
trait RowLanes: Kind {
    fn twiddles(&self) -> &Twiddles;
    fn lanes_with(t: [V; 3], x: V) -> V;
    /// [`Self::lanes_with`] on two rows. With AVX-512, a layer's products of both rows are one product (each row
    /// needs only half its lanes'): [`paired`].
    #[inline(always)]
    fn lanes_with2(tx: [V; 3], ty: [V; 3], x: V, y: V) -> (V, V) {
        (Self::lanes_with(tx, x), Self::lanes_with(ty, y))
    }
}

/// Two rows' half-products of a row's own layer as one product (AVX-512): lanes `l` with bit `L` clear of `x` and
/// `y` take lane `l + L`'s times their twiddle's lane `l`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
mod paired {
    use super::lanes::{V, load, mul, store};
    use core::arch::x86_64::*;

    #[inline(always)]
    fn raw(v: V) -> __m512i {
        let mut a = [0u64; 8];
        // SAFETY: eight words on the stack; the module's cfg enables avx512f.
        unsafe {
            store(a.as_mut_ptr(), v);
            _mm512_loadu_si512(a.as_ptr().cast())
        }
    }

    #[inline(always)]
    fn wrap(x: __m512i) -> V {
        let mut a = [0u64; 8];
        // SAFETY: as above.
        unsafe {
            _mm512_storeu_si512(a.as_mut_ptr().cast(), x);
            load(a.as_ptr())
        }
    }

    #[inline(always)]
    fn idx(i: [i64; 8]) -> __m512i {
        // SAFETY: the module's cfg enables avx512f.
        unsafe { _mm512_loadu_si512(i.as_ptr().cast()) }
    }

    #[inline(always)]
    pub fn mul_add<const L: usize>(x: V, y: V, tx: V, ty: V) -> (V, V) {
        let (dst, mask): ([i64; 4], u8) = match L {
            4 => ([0, 1, 2, 3], 0x0F),
            2 => ([0, 1, 4, 5], 0x33),
            _ => ([0, 2, 4, 6], 0x55),
        };
        let both = |off: i64| std::array::from_fn::<i64, 8, _>(|j| dst[j % 4] + off + 8 * (j / 4) as i64);
        // Lane `dst[j]` of a row gets lane `j` (x) or `4 + j` (y) of the product.
        let mut back = ([0i64; 8], [0i64; 8]);
        for (j, &d) in dst.iter().enumerate() {
            back.0[d as usize] = j as i64;
            back.1[d as usize] = 4 + j as i64;
        }
        let (x, y, tx, ty) = (raw(x), raw(y), raw(tx), raw(ty));
        // SAFETY: the module's cfg enables avx512f.
        unsafe {
            let p = _mm512_permutex2var_epi64(x, idx(both(L as i64)), y);
            let t = _mm512_permutex2var_epi64(tx, idx(both(0)), ty);
            let m = raw(mul(wrap(p), wrap(t)));
            (
                wrap(_mm512_mask_xor_epi64(x, mask, x, _mm512_permutexvar_epi64(idx(back.0), m))),
                wrap(_mm512_mask_xor_epi64(y, mask, y, _mm512_permutexvar_epi64(idx(back.1), m))),
            )
        }
    }
}

impl RowLanes for Forward {
    fn twiddles(&self) -> &Twiddles {
        &self.0
    }
    /// [`Forward::lanes`], its twiddles given.
    #[inline(always)]
    fn lanes_with([t2, t1, t0]: [V; 3], x: V) -> V {
        let x = mask_add(x, 0x0F, mul(swap::<4>(x), t2));
        let x = mask_add(x, 0xF0, swap::<4>(x));
        let x = mask_add(x, 0x33, mul(swap::<2>(x), t1));
        let x = mask_add(x, 0xCC, swap::<2>(x));
        let x = mask_add(x, 0x55, mul(swap::<1>(x), t0));
        mask_add(x, 0xAA, swap::<1>(x))
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    #[inline(always)]
    fn lanes_with2([x2, x1, x0]: [V; 3], [y2, y1, y0]: [V; 3], x: V, y: V) -> (V, V) {
        let (x, y) = paired::mul_add::<4>(x, y, x2, y2);
        let (x, y) = (mask_add(x, 0xF0, swap::<4>(x)), mask_add(y, 0xF0, swap::<4>(y)));
        let (x, y) = paired::mul_add::<2>(x, y, x1, y1);
        let (x, y) = (mask_add(x, 0xCC, swap::<2>(x)), mask_add(y, 0xCC, swap::<2>(y)));
        let (x, y) = paired::mul_add::<1>(x, y, x0, y0);
        (mask_add(x, 0xAA, swap::<1>(x)), mask_add(y, 0xAA, swap::<1>(y)))
    }
}

impl RowLanes for Inverse {
    fn twiddles(&self) -> &Twiddles {
        &self.0
    }
    /// [`Inverse::lanes`], its twiddles given.
    #[inline(always)]
    fn lanes_with([t2, t1, t0]: [V; 3], x: V) -> V {
        let x = mask_add(x, 0xAA, swap::<1>(x));
        let x = mask_add(x, 0x55, mul(swap::<1>(x), t0));
        let x = mask_add(x, 0xCC, swap::<2>(x));
        let x = mask_add(x, 0x33, mul(swap::<2>(x), t1));
        let x = mask_add(x, 0xF0, swap::<4>(x));
        mask_add(x, 0x0F, mul(swap::<4>(x), t2))
    }
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    #[inline(always)]
    fn lanes_with2([x2, x1, x0]: [V; 3], [y2, y1, y0]: [V; 3], x: V, y: V) -> (V, V) {
        let (x, y) = (mask_add(x, 0xAA, swap::<1>(x)), mask_add(y, 0xAA, swap::<1>(y)));
        let (x, y) = paired::mul_add::<1>(x, y, x0, y0);
        let (x, y) = (mask_add(x, 0xCC, swap::<2>(x)), mask_add(y, 0xCC, swap::<2>(y)));
        let (x, y) = paired::mul_add::<2>(x, y, x1, y1);
        let (x, y) = (mask_add(x, 0xF0, swap::<4>(x)), mask_add(y, 0xF0, swap::<4>(y)));
        paired::mul_add::<4>(x, y, x2, y2)
    }
}

/// A leaf's own layers (row layers below the leaf's, and each row's), on `block`: the words `start..` of a column
/// of `len` words (`start` a multiple of `block.len()`, which is [`LEAF_WORDS`] or the whole column), on one
/// thread.
/// The twiddle steps of [`own_stepped`]: from row `r` to `r + 1` the row's twiddles move by `B(2 d), B(4 d),
/// B(8 d)`, `d = r ^ (r + 1)`, which is `2^(z + 1) - 1` for `z` the trailing ones of `r` (`B` is linear); entry `z`.
fn row_steps() -> &'static [[u64; 3]; 32] {
    static STEPS: std::sync::OnceLock<[[u64; 3]; 32]> = std::sync::OnceLock::new();
    STEPS.get_or_init(|| {
        std::array::from_fn(|z| {
            let d = (2usize << z) - 1;
            [point(2 * d).0, point(4 * d).0, point(8 * d).0]
        })
    })
}

/// A row's own layers on the `size` rows at `base` (rows `first..` of the column), their twiddles stepped from row
/// to row rather than computed for each, two rows at a time ([`RowLanes::lanes_with2`]).
///
/// # Safety
/// `base` holds `8 size` words of the caller's own.
#[inline(always)]
unsafe fn own_stepped<T: RowLanes>(kind: &T, base: *mut u64, first: usize, size: usize) {
    #[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
    if size.is_multiple_of(8) {
        // SAFETY: forwarded; `first` is a multiple of `size`, so of eight.
        return unsafe { own_transposed(kind, base, first, size) };
    }
    let steps = row_steps();
    let mut t = kind.twiddles().row(first);
    let advance = |t: [V; 3], r: usize| {
        let step = &steps[r.trailing_ones() as usize];
        [xor(t[0], splat(step[0])), xor(t[1], splat(step[1])), xor(t[2], splat(step[2]))]
    };
    // SAFETY: rows below `size` of the caller's.
    unsafe {
        if size == 1 {
            store(base, T::lanes_with(t, load(base)));
            return;
        }
        for r in (0..size).step_by(2) {
            let tx = t;
            let ty = advance(tx, r);
            let (p, q) = (base.add(8 * r), base.add(8 * (r + 1)));
            let (x, y) = T::lanes_with2(tx, ty, load(p), load(q));
            store(p, x);
            store(q, y);
            if r + 2 < size {
                t = advance(ty, r + 1);
            }
        }
    }
}

/// [`own_transposed`]'s twiddle steps: from row `8 q` to `8 (q + 1)` a row's twiddles move by `B(2 d), B(4 d), B(8 d)`,
/// `d = 8 (q ^ (q + 1)) = 8 (2^(z + 1) - 1)` for `z` the trailing ones of `q` (`B` is linear); entry `z`.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
fn group_steps() -> &'static [[u64; 3]; 32] {
    static STEPS: std::sync::OnceLock<[[u64; 3]; 32]> = std::sync::OnceLock::new();
    STEPS.get_or_init(|| {
        std::array::from_fn(|z| {
            let d = 8 * ((2usize << z) - 1);
            // Past the domain's points (`z` above 28), steps no column of positions below `2^EXT_BASIS` takes.
            match (8 * d) >> crate::domain::EXT_BASIS {
                0 => [point(2 * d).0, point(4 * d).0, point(8 * d).0],
                _ => [0; 3],
            }
        })
    })
}

/// [`own_stepped`] eight rows at a time, transposed (AVX-512): lane `k` of vector `j` is row `R + k`'s word `j`, so a
/// row's butterflies (between its words) are butterflies between whole vectors, each vector's twiddles the eight
/// rows' (row `R + k`'s are row `R`'s plus `k`'s: `B` is linear). Each layer's products are then whole vector
/// products rather than half of [`paired`]'s, and the swaps between lanes two transposes. The same butterflies, so
/// the same values. [Added here: the rows' own layers took about a third of a transform's time.]
///
/// # Safety
/// `base` holds `8 size` words of the caller's own, `size` and `first` multiples of eight.
#[cfg(all(target_arch = "x86_64", target_feature = "avx512f", target_feature = "vpclmulqdq"))]
#[inline(always)]
unsafe fn own_transposed<T: RowLanes>(kind: &T, base: *mut u64, first: usize, size: usize) {
    debug_assert!(size.is_multiple_of(8) && first.is_multiple_of(8));
    let o = &kind.twiddles().offsets;
    // Lane `k` of `steps(s)` is `B(s k)`, row `k`'s part of a twiddle `B(s (R + k)) = B(s R) + B(s k)`.
    let steps = |s: usize| from_array(std::array::from_fn(|k| point(s * k).0));
    let (s2, s4, s8) = (steps(2), steps(4), steps(8));
    // The lanes' constant parts of layers 1 and 0 (`Twiddles`' `c1`, `c0`): `B(2)` past lane 4, `B(2 (i / 2))` at lane
    // `i`.
    let [c2, c4, c6] = [2, 4, 6].map(|x| splat(point(x).0));
    // Row `R`'s twiddles' scalar parts, stepped from group to group: from `R = 8 q` to `R + 8` they move by
    // `B(2 d), B(4 d), B(8 d)`, `d = 8 (q ^ (q + 1))` ([`group_steps`]).
    let mut b = [o[2] + point(2 * first), o[1] + point(4 * first), o[0] + point(8 * first)];
    let steps8 = group_steps();
    for g in (0..size).step_by(8) {
        let [b2, b1, b0] = b;
        let step = &steps8[((first + g) / 8).trailing_ones() as usize];
        b = [b2 + F64(step[0]), b1 + F64(step[1]), b0 + F64(step[2])];
        let t2 = xor(splat(b2.0), s2);
        let t1 = xor(splat(b1.0), s4);
        let t0 = xor(splat(b0.0), s8);
        let (t1, t0) = ([t1, xor(t1, c2)], [t0, xor(t0, c2), xor(t0, c4), xor(t0, c6)]);
        // SAFETY: rows `g..g + 8` of the caller's.
        unsafe {
            let p = base.add(8 * g);
            let mut v = transpose(std::array::from_fn(|q| load(p.add(8 * q))));
            let layer2 = |v: &mut [V; 8]| {
                for i in 0..4 {
                    (v[i], v[i + 4]) = T::butterfly(v[i], v[i + 4], t2);
                }
            };
            let layer1 = |v: &mut [V; 8]| {
                for (i, t) in [(0, t1[0]), (1, t1[0]), (4, t1[1]), (5, t1[1])] {
                    (v[i], v[i + 2]) = T::butterfly(v[i], v[i + 2], t);
                }
            };
            let layer0 = |v: &mut [V; 8]| {
                for (h, t) in t0.iter().enumerate() {
                    (v[2 * h], v[2 * h + 1]) = T::butterfly(v[2 * h], v[2 * h + 1], *t);
                }
            };
            if T::DOWN {
                layer2(&mut v);
                layer1(&mut v);
                layer0(&mut v);
            } else {
                layer0(&mut v);
                layer1(&mut v);
                layer2(&mut v);
            }
            for (q, x) in transpose(v).into_iter().enumerate() {
                store(p.add(8 * q), x);
            }
        }
    }
}

fn leaf<T: RowLanes>(block: &mut [F64], start: usize, kind: &T) {
    assert!(block.len().is_power_of_two() && block.len() >= 8 && start.is_multiple_of(block.len()));
    let size = block.len() / 8;
    let leaf = size.trailing_zeros() as usize;
    let first = start / 8;
    let base = block.as_mut_ptr().cast::<u64>();
    // SAFETY: the block's own `size` rows.
    unsafe {
        let own = || own_stepped(kind, base, first, size);
        if !T::DOWN {
            own();
        }
        let layer = |k: usize| {
            let half = 1usize << k;
            let t0 = kind.twiddle(k + 3, first >> (k + 1));
            for j in 0..size >> (k + 1) {
                let row = 2 * half * j;
                let t = splat((t0 + kind.step(j)).0);
                pairs::<T>(base.add(8 * row), base.add(8 * (row + half)), half, t);
            }
        };
        // Layers `k` and `k - 1` at once ([`quads`]), as [`leaves`] runs them.
        let fused = |k: usize| {
            let h = 1usize << (k - 1);
            let (t_hi, t_lo) = (kind.twiddle(k + 3, first >> (k + 1)), kind.twiddle(k + 2, first >> k));
            for j in 0..size >> (k + 1) {
                let row = 4 * h * j;
                let (t1, t2a, t2b) = (
                    splat((t_hi + kind.step(j)).0),
                    splat((t_lo + kind.step(2 * j)).0),
                    splat((t_lo + kind.step(2 * j + 1)).0),
                );
                quads::<T>([0, 1, 2, 3].map(|q| base.add(8 * (row + q * h))), h, t1, t2a, t2b);
            }
        };
        for (k, two) in layer_steps(leaf, T::DOWN, false) {
            match two {
                true => fused(k),
                false => layer(k),
            }
        }
        if T::DOWN {
            own();
        }
    }
}

/// The forward transform's leaf layers on `block`, words `start..start + block.len()` of a column of `len` words
/// at `offset`: `block.len()` is [`LEAF_WORDS`], or `len` if that is smaller.
pub fn values_leaf(block: &mut [F64], start: usize, len: usize, offset: F64) {
    assert_eq!(block.len(), LEAF_WORDS.min(len));
    leaf(block, start, &Forward(Twiddles::new(offset, len.trailing_zeros() as usize)));
}

/// The inverse transform's leaf layers on `block`, as [`values_leaf`].
pub fn coefficients_leaf(block: &mut [F64], start: usize, len: usize, offset: F64) {
    assert_eq!(block.len(), LEAF_WORDS.min(len));
    leaf(block, start, &Inverse(Twiddles::new(offset, len.trailing_zeros() as usize)));
}

#[cfg(test)]
mod tests {
    use super::*;

    fn rng(seed: u64) -> impl FnMut() -> u64 {
        let mut state = seed | 1;
        move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        }
    }

    /// The transforms are `quotient::domain`'s, on one column and on a batch, at every size up to two wide passes.
    #[test]
    fn transforms_are_the_domains() {
        transforms_are_the_domains_at(&[0, 1, 2, 3, 4, 5, 9, 12, 13, 17, 19]);
    }

    /// Small shapes for Miri (`cargo +nightly miri test --target x86_64-unknown-linux-gnu -p quotient --lib
    /// miri_`, its portable lanes): the fused layers' pointer arithmetic ([`quads`]) on leaves, and
    /// [`leaf`]'s, against the domain's transforms.
    #[test]
    fn miri_fused_layers_are_the_domains() {
        transforms_are_the_domains_at(&[3, 6, 7, 8]);
        let mut next = rng(5);
        for m in [6usize, 7] {
            let offset = point(1 << 21) + point(3 << m);
            let column: Vec<F64> = (0..1usize << m).map(|_| F64(next())).collect();
            let mut want = column.clone();
            crate::domain::values(&mut want, offset);
            let mut got = column.clone();
            values_leaf(&mut got, 0, column.len(), offset);
            assert_eq!(got, want, "leaf values, 2^{m}");
            coefficients_leaf(&mut got, 0, column.len(), offset);
            assert_eq!(got, column, "leaf coefficients, 2^{m}");
        }
    }

    fn transforms_are_the_domains_at(sizes: &[usize]) {
        let mut next = rng(3);
        for &m in sizes {
            let offset = point(1 << 21) + point(5 << m);
            let column: Vec<F64> = (0..1usize << m).map(|_| F64(next())).collect();
            let mut want = column.clone();
            crate::domain::values(&mut want, offset);
            let mut got = column.clone();
            values(&mut got, offset);
            assert_eq!(got, want, "values, 2^{m}");
            coefficients(&mut got, offset);
            assert_eq!(got, column, "coefficients, 2^{m}");
            let mut want_inv = column.clone();
            crate::domain::coefficients(&mut want_inv, offset);
            let mut got_inv = column.clone();
            coefficients(&mut got_inv, offset);
            assert_eq!(got_inv, want_inv, "coefficients of values, 2^{m}");

            let columns: Vec<Vec<F64>> = (0..5)
                .map(|_| (0..1usize << m).map(|_| F64(next())).collect())
                .collect();
            let refs: Vec<&[F64]> = columns.iter().map(|c| &c[..]).collect();
            let batch = pack(&refs);
            let mut out = vec![K8::ZERO; batch.len()];
            if batch.len() >= 8 {
                values_batch_from(&batch, &mut out, offset, true);
                transpose_runs(&mut out);
                let mut again = batch.clone();
                values_batch(&mut again, offset, false);
                assert_eq!(again, out, "batch values in place, 2^{m}");
            }
            values_batch_from(&batch, &mut out, offset, false);
            for (l, c) in columns.iter().enumerate() {
                let mut w = c.clone();
                crate::domain::values(&mut w, offset);
                assert!(out.iter().zip(&w).all(|(row, &x)| row.0[l] == x), "batch values, 2^{m}");
            }
            assert!(out.iter().all(|row| row.0[5..].iter().all(|x| x.is_zero())));
            coefficients_batch(&mut out, offset);
            assert_eq!(out, batch, "batch coefficients, 2^{m}");
        }
    }

    /// The fold onto a smaller coset, the shifted cube and the subset sums against their direct definitions.
    #[test]
    fn folds_and_cubes() {
        let mut next = rng(5);
        let r = 12;
        let novel: Vec<F64> = (0..1usize << r).map(|_| F64(next())).collect();
        let first = (1 << 20) + (3 << 9);
        for e in [0usize, 2, 3, 9, 12] {
            let first = first & !((1usize << e) - 1);
            let got = on_coset_prefix(&novel, first, e);
            // Against the whole transform on the aligned coset of V_r holding it.
            let big = first & !((1usize << r) - 1);
            let mut all = novel.clone();
            crate::domain::values(&mut all, point(big));
            assert_eq!(
                got,
                all[first - big..first - big + (1 << e)].to_vec(),
                "fold onto 2^{e}"
            );
        }
        let table: Vec<F64> = (0..1usize << r).map(|_| F64(next())).collect();
        let delta: Vec<F64> = (0..r).map(|_| F64(next())).collect();
        let mut full = table.clone();
        for (l, &d) in delta.iter().enumerate() {
            let half = 1usize << l;
            for pair in full.chunks_exact_mut(2 * half) {
                let (lo, hi) = pair.split_at_mut(half);
                for (a, b) in lo.iter_mut().zip(hi.iter_mut()) {
                    let t = d * (*a + *b);
                    *a += t;
                    *b += t;
                }
            }
        }
        for e in [0usize, 2, 3, 7, 12] {
            assert_eq!(shifted_cube(&table, &delta, e), full[..1 << e].to_vec(), "cube, 2^{e}");
        }
        for m in [0usize, 3, 15, 16, 23] {
            let data: Vec<F64> = (0..1usize << m).map(|_| F64(next())).collect();
            let mut want = data.clone();
            let mut half = 1;
            while half < want.len() {
                for pair in want.chunks_exact_mut(2 * half) {
                    let (lo, hi) = pair.split_at_mut(half);
                    for (h, &l) in hi.iter_mut().zip(lo.iter()) {
                        *h += l;
                    }
                }
                half *= 2;
            }
            let mut from = vec![F64(next()); data.len()];
            let cut = data.len() - data.len() / 3;
            subset_sums_from(&data[..cut], &mut from);
            let mut padded = data.clone();
            padded[cut..].fill(F64::ZERO);
            subset_sums(&mut padded);
            assert_eq!(from, padded, "subset sums from a shorter source, 2^{m}");
            let mut got = data;
            subset_sums(&mut got);
            assert_eq!(got, want, "subset sums, 2^{m}");
        }
    }

    /// The lane types are the field's, lane by lane; the runs' transpose is a transpose.
    #[test]
    fn lanes_are_the_fields() {
        let mut next = rng(11);
        let mut e = || F192::new(next(), next(), next());
        let a: [F192; 8] = std::array::from_fn(|_| e());
        let b: [F192; 8] = std::array::from_fn(|_| e());
        let c = e();
        let limbs = |x: &[F192; 8]| -> [Kx8; 3] {
            [0, 1, 2].map(|k| Kx8::new(std::array::from_fn(|p| F64([x[p].c0, x[p].c1, x[p].c2][k]))))
        };
        let back = |x: Ex8| -> [F192; 8] {
            let l = x.limbs().map(|k| k.to_row());
            std::array::from_fn(|p| F192::new(l[0].0[p].0, l[1].0[p].0, l[2].0[p].0))
        };
        let (va, vb) = (Ex8::from_limbs(limbs(&a)), Ex8::from_limbs(limbs(&b)));
        assert_eq!(back(va * vb), std::array::from_fn(|p| a[p] * b[p]));
        assert_eq!(back(va + vb), std::array::from_fn(|p| a[p] + b[p]));
        let k = limbs(&b)[1];
        let kr = k.to_row();
        assert_eq!(back(va.mul_k(k)), std::array::from_fn(|p| a[p].mul_base(kr.0[p])));
        let mut sum = MixedSum::default();
        sum.add(&ESplat::new(c), k);
        sum.add(&ESplat::new(a[3]), k * k);
        let want: [F192; 8] = std::array::from_fn(|p| c.mul_base(kr.0[p]) + a[3].mul_base(kr.0[p] * kr.0[p]));
        assert_eq!(back(sum.reduce() + Ex8::splat(F192::ZERO)), want);
        assert_eq!(back(Ex8::from_k(k)), std::array::from_fn(|p| F192::from(kr.0[p])));
        assert_eq!(back(va.swap_pairs()), std::array::from_fn(|p| a[p ^ 1]));
        let mut rows: Vec<K8> = (0..16).map(|_| K8(std::array::from_fn(|_| F64(next())))).collect();
        let before = rows.clone();
        transpose_runs(&mut rows);
        for g in 0..2 {
            for (l, row) in rows[8 * g..8 * g + 8].iter().enumerate() {
                assert!((0..8).all(|p| row.0[p] == before[8 * g + p].0[l]));
            }
        }
        let mut out: [Vec<F64>; 3] = std::array::from_fn(|_| vec![F64::ZERO; 13]);
        let [o0, o1, o2] = &mut out;
        fill_limbs8([o0, o1, o2], |j| Ex8::splat(F192::new(j as u64, 7, 9)));
        assert!(out[0].iter().enumerate().all(|(i, x)| x.0 == (i / 8) as u64) && out[2].iter().all(|x| x.0 == 9));
    }

    /// The interpolation from the first points of `D_M` is the whole coset's, for a polynomial of the degree.
    #[test]
    fn prefix_interpolation() {
        let mut next = rng(7);
        for (count, grain) in [
            (1usize, 0usize),
            (5, 0),
            (1000, 3),
            (1 << 10, 4),
            (5000, 6),
            (37_000, 10),
        ] {
            let sizes = prefix_sizes(count as u64, grain);
            let total: usize = sizes.iter().map(|&e| 1usize << e).sum();
            assert!(total >= count);
            let m = sizes[0] + 1;
            let novel: Vec<F64> = (0..total)
                .map(|i| if i < count { F64(next()) } else { F64::ZERO })
                .collect();
            let mut all = novel.clone();
            all.resize(1 << m, F64::ZERO);
            crate::domain::values(&mut all, point(1 << m));
            let mut got = all[..total].to_vec();
            interpolate_prefix(&mut got, &sizes, 1 << m);
            assert_eq!(got, novel, "count {count}, blocks {sizes:?}");
        }
    }

    /// The several-column and one-worker transforms, folds and interpolation are the one-column ones.
    #[test]
    fn columns_at_once_and_serial_are_one_at_a_time() {
        let mut next = rng(11);
        for m in [0usize, 2, 3, 4, 9, 12, 13, 16, 19] {
            let offset = point(3 << 21) + point(7 << m);
            let columns: Vec<Vec<F64>> = (0..3).map(|_| (0..1usize << m).map(|_| F64(next())).collect()).collect();
            let refs: Vec<&[F64]> = columns.iter().map(|c| &c[..]).collect();
            let one = |f: fn(&mut [F64], F64)| -> Vec<Vec<F64>> {
                columns
                    .iter()
                    .map(|c| {
                        let mut c = c.clone();
                        f(&mut c, offset);
                        c
                    })
                    .collect()
            };
            let (want_v, want_c) = (one(values), one(coefficients));
            let mut got = columns.clone();
            values_cols(&mut got.iter_mut().map(|c| &mut c[..]).collect::<Vec<_>>(), offset);
            assert_eq!(got, want_v, "values_cols, 2^{m}");
            let mut got = columns.clone();
            coefficients_cols(&mut got.iter_mut().map(|c| &mut c[..]).collect::<Vec<_>>(), offset);
            assert_eq!(got, want_c, "coefficients_cols, 2^{m}");
            let mut got: Vec<Vec<F64>> = columns.iter().map(|c| vec![F64::ZERO; c.len()]).collect();
            values_from_cols(&refs, &mut got.iter_mut().map(|c| &mut c[..]).collect::<Vec<_>>(), offset);
            assert_eq!(got, want_v, "values_from_cols, 2^{m}");
            let mut got = vec![F64::ZERO; 1 << m];
            values_from_serial(&columns[0], &mut got, offset);
            assert_eq!(got, want_v[0], "values_from_serial, 2^{m}");
            for e in [0, 1, 3, 6, 7, 9].into_iter().filter(|&e| e <= m) {
                let first = (5 << 22) + (3 << e);
                let want: Vec<Vec<F64>> = refs.iter().map(|c| on_coset_prefix(c, first, e)).collect();
                assert_eq!(on_coset_prefix_cols(&refs, first, e), want, "on_coset_prefix_cols, 2^{m} onto 2^{e}");
                let mut got = vec![F64::ZERO; 1 << e];
                on_coset_prefix_serial(&columns[1], first, &mut got);
                assert_eq!(got, want[1], "on_coset_prefix_serial, 2^{m} onto 2^{e}");
            }
        }
        for (count, grain) in [(1u64, 0usize), (5, 0), (1000, 3), (5000, 6), (37_000, 10), (300_000, 13)] {
            let sizes = prefix_sizes(count, grain);
            let total: usize = sizes.iter().map(|&e| 1usize << e).sum();
            let base = 2 << sizes[0];
            let columns: Vec<Vec<F64>> = (0..3).map(|_| (0..total).map(|_| F64(next())).collect()).collect();
            let want: Vec<Vec<F64>> = columns
                .iter()
                .map(|c| {
                    let mut c = c.clone();
                    interpolate_prefix(&mut c, &sizes, base);
                    c
                })
                .collect();
            let mut got = columns.clone();
            interpolate_prefix_cols(&mut got.iter_mut().map(|c| &mut c[..]).collect::<Vec<_>>(), &sizes, base);
            assert_eq!(got, want, "interpolate_prefix_cols, blocks {sizes:?}");
        }
    }

    /// The batched helpers (several quotients' interpolations, columns on their own cosets, small cosets of several
    /// columns, a batch on a coset) are the one-at-a-time ones.
    #[test]
    fn many_at_once_are_one_at_a_time() {
        let mut next = rng(29);
        // Several quotients of different blocks, base and columns.
        let shapes = [(1u64, 0usize), (1000, 3), (37_000, 10), (300_000, 13), (5000, 6), (300_001, 13)];
        let mut all: Vec<(Vec<Vec<F64>>, Vec<usize>, usize)> = shapes
            .iter()
            .enumerate()
            .map(|(i, &(count, grain))| {
                let sizes = prefix_sizes(count, grain);
                let total: usize = sizes.iter().map(|&e| 1usize << e).sum();
                let base = (2 + 2 * (i % 2)) << sizes[0];
                ((0..1 + i % 3).map(|_| (0..total).map(|_| F64(next())).collect()).collect(), sizes, base)
            })
            .collect();
        let want: Vec<Vec<Vec<F64>>> = all
            .iter()
            .map(|(cols, sizes, base)| {
                let mut cols = cols.clone();
                interpolate_prefix_cols(&mut cols.iter_mut().map(|c| &mut c[..]).collect::<Vec<_>>(), sizes, *base);
                cols
            })
            .collect();
        let mut jobs: Vec<PrefixCols> = all
            .iter_mut()
            .map(|(cols, sizes, base)| PrefixCols {
                cols: cols.iter_mut().map(|c| &mut c[..]).collect(),
                sizes: sizes.clone(),
                base: *base,
            })
            .collect();
        interpolate_prefix_many(&mut jobs);
        drop(jobs);
        assert!(all.iter().map(|a| &a.0).eq(want.iter()), "interpolate_prefix_many");
        for m in [0usize, 3, 4, 12, 16] {
            let columns: Vec<Vec<F64>> = (0..4).map(|_| (0..1usize << m).map(|_| F64(next())).collect()).collect();
            let offsets: Vec<F64> = (0..4).map(|c| point((c + 1) << 20) + point(c << m)).collect();
            let want: Vec<Vec<F64>> = columns
                .iter()
                .zip(&offsets)
                .map(|(c, &o)| {
                    let mut c = c.clone();
                    coefficients(&mut c, o);
                    c
                })
                .collect();
            let mut got = columns.clone();
            coefficients_cols_each(&mut got.iter_mut().map(|c| &mut c[..]).collect::<Vec<_>>(), &offsets);
            assert_eq!(got, want, "coefficients_cols_each, 2^{m}");
            let at: Vec<(&[F64], usize, usize)> = columns
                .iter()
                .enumerate()
                .flat_map(|(c, col)| {
                    [0, 3, 6].into_iter().filter(move |&e| e <= m).map(move |e| (&col[..], (7 << 21) + (c << e), e))
                })
                .collect();
            let want: Vec<Vec<F64>> = at.iter().map(|&(c, first, e)| on_coset_prefix(c, first, e)).collect();
            assert_eq!(on_coset_prefix_each(&at), want, "on_coset_prefix_each, 2^{m}");
            if m >= 3 {
                let refs: Vec<&[F64]> = columns.iter().map(|c| &c[..]).collect();
                let batch = pack(&refs);
                for e in (3..=m).step_by(3) {
                    let first = (5 << 22) + (3 << e);
                    let mut want = vec![K8::ZERO; 1 << e];
                    fold_batch(&batch, first, &mut want);
                    values_batch(&mut want, point(first), true);
                    assert_eq!(on_coset_batch(&batch, first, e, true), want, "on_coset_batch, 2^{m} onto 2^{e}");
                }
            }
        }
    }

    /// The lane-wise mixed sums and the lanes' blends are the scalar ones.
    #[test]
    fn lane_sums_and_blends() {
        let mut next = rng(23);
        let e: Vec<F192> = (0..16).map(|_| F192::new(next(), next(), next())).collect();
        let k: Vec<F64> = (0..16).map(|_| F64(next())).collect();
        let ex = |o: usize| Ex8::from_limbs([0, 1, 2].map(|l| Kx8::new(std::array::from_fn(|i| F64([e[o + i].c0, e[o + i].c1, e[o + i].c2][l])))));
        let kx = |o: usize| Kx8::new(std::array::from_fn(|i| k[o + i]));
        let mut sum = MixedSum::default();
        sum.add_lanes(ex(0), kx(0));
        sum.add_lanes(ex(8), kx(8));
        let got = sum.reduce().to_array();
        for i in 0..8 {
            assert_eq!(got[i], e[i].mul_base(k[i]) + e[8 + i].mul_base(k[8 + i]));
        }
        let (ev, od) = Kx8::evens_odds(kx(0), kx(8));
        for l in 0..8 {
            let src = if l < 4 { 2 * l } else { 8 + 2 * (l - 4) };
            assert_eq!((ev.to_row().0[l], od.to_row().0[l]), (k[src], k[src + 1]));
        }
        let rows: [Kx8; 8] = std::array::from_fn(|r| Kx8::new(std::array::from_fn(|l| k[(r + l) % 16])));
        let t = Kx8::transpose8(rows);
        for (i, t) in t.iter().enumerate() {
            for l in 0..8 {
                assert_eq!(t.to_row().0[l], rows[l].to_row().0[i]);
            }
        }
        let blend = ex(0).odd_from(ex(8)).to_array();
        let kb = kx(0).odd_from(kx(8)).to_row();
        for i in 0..8 {
            assert_eq!(blend[i], e[if i % 2 == 1 { 8 + i } else { i }]);
            assert_eq!(kb.0[i], k[if i % 2 == 1 { 8 + i } else { i }]);
        }
    }

    /// The one-worker shifted cube is the pool's.
    #[test]
    fn serial_cube_is_the_pools() {
        let mut next = rng(31);
        for r in [0usize, 2, 3, 9, 13, 15] {
            let values: Vec<F64> = (0..1usize << r).map(|_| F64(next())).collect();
            let delta: Vec<F64> = (0..r).map(|_| F64(next())).collect();
            for e in 0..=r {
                assert_eq!(shifted_cube_serial(&values, &delta, e), shifted_cube(&values, &delta, e), "2^{r} onto 2^{e}");
            }
        }
    }

    /// The fold weights in one dispatch are the doubling's.
    #[test]
    fn tensor_is_doubling() {
        for len in [1usize, 2, 3, 100, 4096, 4097, 1 << 15, (1 << 17) + 5] {
            let factor = |b: usize, bit: bool| if bit { point(5 + 3 * b) } else { point(1 << 20) + point(b) };
            let mut want = vec![F64::ONE];
            let mut b = 0;
            while want.len() < len {
                let half = want.len();
                for h in 0..half {
                    want.push(want[h] * factor(b, true));
                }
                for x in &mut want[..half] {
                    *x *= factor(b, false);
                }
                b += 1;
            }
            want.truncate(len);
            assert_eq!(tensor(len, factor), want, "{len}");
        }
        let mut next = rng(19);
        let srcs: Vec<Vec<F64>> = (0..3).map(|_| (0..1 << 13).map(|_| F64(next())).collect()).collect();
        let refs: Vec<&[F64]> = srcs.iter().map(|s| &s[..]).collect();
        let want: Vec<Vec<F64>> = srcs
            .iter()
            .map(|s| {
                let mut c = s.clone();
                coefficients(&mut c, point(7));
                c
            })
            .collect();
        assert_eq!(coefficients_cols_of(&refs, point(7)), want);
        let want: Vec<Vec<F64>> = srcs
            .iter()
            .map(|s| {
                let mut c = s.clone();
                subset_sums(&mut c);
                c
            })
            .collect();
        assert_eq!(subset_sums_of_cols(&refs), want);
        assert_eq!(zeros(1 << 17), vec![F64::ZERO; 1 << 17]);
    }

    /// Several columns' subset sums at once are each one's.
    /// A filled column is zeros, then each block's subset sums or copy, whatever the blocks' order and gaps.
    #[test]
    fn filled_column_is_zeros_then_each_block() {
        let mut next = rng(23);
        // (offset, block, source length or none for a copy, raw words)
        let blocks = [
            (1usize << 18, 1usize << 18, Some(3usize << 15), false),
            (0, 1 << 16, Some(1 << 16), false),
            (1 << 16, 1 << 15, None, false),
            (3 << 15, 1 << 10, None, true),
            (7 << 15, 8, Some(5), false),
            (1 << 20, 1 << 20, Some(1000), false),
            ((1 << 21) + 3, 1, Some(1), false),
        ];
        let len = (1 << 21) + (1 << 17);
        let srcs: Vec<Vec<F64>> = blocks
            .iter()
            .map(|&(_, n, s, _)| (0..s.unwrap_or(n)).map(|_| F64(next())).collect())
            .collect();
        let raws: Vec<Vec<u64>> = srcs.iter().map(|s| s.iter().map(|x| x.0).collect()).collect();
        let mut want = vec![F64::ZERO; len];
        for (&(offset, n, s, _), src) in blocks.iter().zip(&srcs) {
            match s {
                Some(_) => subset_sums_from(src, &mut want[offset..offset + n]),
                None => want[offset..offset + n].copy_from_slice(src),
            }
        }
        let jobs: Vec<(usize, usize, Fill)> = blocks
            .iter()
            .zip(srcs.iter().zip(&raws))
            .map(|(&(offset, n, s, raw), (src, words))| {
                let fill = match (s, raw) {
                    (Some(_), _) => Fill::Sums(src),
                    (None, false) => Fill::Words(src),
                    (None, true) => Fill::Raw(words),
                };
                (offset, n, fill)
            })
            .collect();
        assert!(filled_column(len, &jobs) == want);
    }

    #[test]
    fn subset_sums_many_is_each() {
        let mut next = rng(17);
        let lens = [(1usize, 1usize), (8, 5), (1 << 10, 1 << 10), (1 << 15, 1000), (1 << 16, 1 << 16), (1 << 18, 3 << 15)];
        let srcs: Vec<Vec<F64>> = lens.iter().map(|&(_, s)| (0..s).map(|_| F64(next())).collect()).collect();
        let want: Vec<Vec<F64>> = lens
            .iter()
            .zip(&srcs)
            .map(|(&(n, _), src)| {
                let mut d = vec![F64::ZERO; n];
                subset_sums_from(src, &mut d);
                d
            })
            .collect();
        let mut got: Vec<Vec<F64>> = lens.iter().map(|&(n, _)| vec![F64(next()); n]).collect();
        let mut jobs: Vec<(&[F64], &mut [F64])> = srcs.iter().map(|s| &s[..]).zip(got.iter_mut().map(|g| &mut g[..])).collect();
        subset_sums_many(&mut jobs);
        assert_eq!(got, want);
        let mut got: Vec<Vec<F64>> = srcs.iter().map(|s| vec![F64::ZERO; s.len().next_power_of_two()]).collect();
        let want: Vec<Vec<F64>> = srcs
            .iter()
            .map(|s| {
                let mut d = vec![F64::ZERO; s.len().next_power_of_two()];
                coefficients_from(&{
                    let mut v = s.clone();
                    v.resize(d.len(), F64::ZERO);
                    v
                }, &mut d, point(1 << 20));
                d
            })
            .collect();
        for (g, s) in got.iter_mut().zip(&srcs).filter(|(g, _)| g.len() >= 8) {
            let mut padded = s.clone();
            padded.resize(g.len(), F64::ZERO);
            coefficients_from_cols(&[&padded], &mut [&mut g[..]], point(1 << 20));
        }
        for (g, w) in got.iter().zip(&want).filter(|(g, _)| g.len() >= 8) {
            assert_eq!(g, w);
        }
    }

    /// The one-worker batch transforms and fold are the pool's.
    #[test]
    fn serial_batches_are_the_pools() {
        let mut next = rng(13);
        for m in [3usize, 4, 9, 12, 13, 15, 16] {
            let columns: Vec<Vec<F64>> = (0..8).map(|_| (0..1usize << m).map(|_| F64(next())).collect()).collect();
            let refs: Vec<&[F64]> = columns.iter().map(|c| &c[..]).collect();
            let batch = pack(&refs);
            for runs in [false, true] {
                let offset = point(9 << 20);
                let mut want = vec![K8::ZERO; batch.len()];
                values_batch_from(&batch, &mut want, offset, runs);
                let mut got = vec![K8::ZERO; batch.len()];
                values_batch_from_serial(&batch, &mut got, offset, runs);
                assert!(got == want, "values_batch_from_serial, 2^{m}");
                let mut got = batch.clone();
                values_batch_serial(&mut got, offset, runs);
                assert!(got == want, "values_batch_serial, 2^{m}");
            }
            for e in (0..=m).step_by(3) {
                let first = (3 << 22) + (5 << e);
                let mut want = vec![K8::ZERO; 1 << e];
                fold_batch(&batch, first, &mut want);
                let mut got = vec![K8::ZERO; 1 << e];
                fold_batch_serial(&batch, first, &mut got);
                assert!(got == want, "fold_batch_serial, 2^{m} onto 2^{e}");
            }
        }
    }

    /// The split transforms are the whole ones: the upper layers, then each leaf block's (forward); each leaf
    /// block's, then the upper layers (inverse); at sizes of no, one and two upper passes, in place and from a
    /// source.
    #[test]
    fn split_transforms_are_the_whole() {
        let mut next = rng(5);
        for m in [3usize, 4, 9, 15, 16, 19, 22, 25] {
            let len = 1usize << m;
            let offset = point(1 << 29) + point(3 << m);
            let column: Vec<F64> = (0..len).map(|_| F64(next())).collect();
            let mut want = column.clone();
            values(&mut want, offset);
            let block = LEAF_WORDS.min(len);
            let mut got = vec![F64::ZERO; len];
            values_upper(Some(&column), &mut got, offset);
            for (b, chunk) in got.chunks_exact_mut(block).enumerate() {
                values_leaf(chunk, b * block, len, offset);
            }
            assert_eq!(got, want, "values, 2^{m}");
            let mut again = column.clone();
            values_upper(None, &mut again, offset);
            for (b, chunk) in again.chunks_exact_mut(block).enumerate() {
                values_leaf(chunk, b * block, len, offset);
            }
            assert_eq!(again, want, "values in place, 2^{m}");
            for (b, chunk) in got.chunks_exact_mut(block).enumerate() {
                coefficients_leaf(chunk, b * block, len, offset);
            }
            coefficients_upper(&mut got, offset);
            assert_eq!(got, column, "coefficients, 2^{m}");
        }
    }
}

/// The NEON lanes against scalar `F64` arithmetic.
#[cfg(all(test, target_arch = "aarch64", target_feature = "aes"))]
mod neon_tests {
    use super::lanes::*;
    use primitives::field::F64;

    fn words(v: V) -> [u64; 8] {
        let mut out = [0u64; 8];
        // SAFETY: eight words on the stack.
        unsafe { store(out.as_mut_ptr(), v) };
        out
    }

    #[test]
    fn neon_lanes_are_scalar() {
        let mut state = 0x9E37_79B9_7F4A_7C15u64;
        let mut next = move || {
            state ^= state << 13;
            state ^= state >> 7;
            state ^= state << 17;
            state
        };
        // Random words, and operands that exercise the reduction's spill.
        let corners = [0, 1, u64::MAX, 1 << 63, 0xF000_0000_0000_0000, 0x1B];
        for round in 0..2000 {
            let terms = 1 + round % 9;
            let a: Vec<[u64; 8]> = (0..terms)
                .map(|_| std::array::from_fn(|i| if round < 6 { corners[(round + i) % 6] } else { next() }))
                .collect();
            let b: Vec<[u64; 8]> = (0..terms)
                .map(|_| {
                    std::array::from_fn(|i| {
                        if round < 6 {
                            corners[(round + i + 3) % 6]
                        } else {
                            next()
                        }
                    })
                })
                .collect();
            let (va, vb) = (from_array(a[0]), from_array(b[0]));
            let scalar_mul: [u64; 8] = std::array::from_fn(|i| (F64(a[0][i]) * F64(b[0][i])).0);
            assert_eq!(words(mul(va, vb)), scalar_mul);
            // A sum of unreduced products, reduced once.
            let mut acc = zero_u();
            for (x, y) in a.iter().zip(&b) {
                acc = xor_u(acc, clmul_u(from_array(*x), from_array(*y)));
            }
            let want: [u64; 8] = std::array::from_fn(|i| {
                a.iter()
                    .zip(&b)
                    .fold(F64::ZERO, |s, (x, y)| s + F64(x[i]) * F64(y[i]))
                    .0
            });
            assert_eq!(words(reduce_u(acc)), want);
            assert_eq!(words(splat(a[0][1])), [a[0][1]; 8]);
            assert_eq!(words(xor(va, vb)), std::array::from_fn(|i| a[0][i] ^ b[0][i]));
            assert_eq!(words(swap::<1>(va)), std::array::from_fn(|i| a[0][i ^ 1]));
            assert_eq!(words(swap::<2>(va)), std::array::from_fn(|i| a[0][i ^ 2]));
            assert_eq!(words(swap::<4>(va)), std::array::from_fn(|i| a[0][i ^ 4]));
            let mask = (round % 256) as u8;
            let masked: [u64; 8] =
                std::array::from_fn(|i| if mask >> i & 1 == 1 { a[0][i] ^ b[0][i] } else { a[0][i] });
            assert_eq!(words(mask_add(va, mask, vb)), masked);
            let rows: [[u64; 8]; 8] = std::array::from_fn(|_| std::array::from_fn(|_| next()));
            let t = transpose(rows.map(from_array)).map(words);
            assert_eq!(t, std::array::from_fn(|c| std::array::from_fn(|p| rows[p][c])));
        }
    }
}
