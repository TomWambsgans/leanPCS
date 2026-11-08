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
#[inline(always)]
fn tasks(n: usize, serial: bool, f: impl Fn(usize) + Sync) {
    if serial {
        (0..n).for_each(f);
    } else {
        parallel::for_each(n, f);
    }
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
            wide(cols, std::mem::take(&mut from), rows, a, g, shift, kind, serial);
        }
        leaves(cols, from, rows, leaf, shift, kind, runs, serial);
    } else {
        leaves(cols, true, rows, leaf, shift, kind, runs, serial);
        for &(a, g) in groups.iter().rev() {
            wide(cols, false, rows, a, g, shift, kind, serial);
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
    kind: &T,
    runs: bool,
    serial: bool,
) {
    let size = 1usize << leaf;
    let per = rows >> leaf;
    tasks(per * cols.len(), serial, |t| {
        let (Col { data, src }, task) = (cols[t / per], t % per);
        let src = if from_src { src } else { None };
        let first = task << leaf;
        // SAFETY: a task touches its own `size` rows from `first`.
        unsafe {
            let base = data.add(8 * first);
            if let Some(s) = src {
                std::ptr::copy_nonoverlapping(s.add(8 * first), base, 8 * size);
            }
            let own = |base: *mut u64| {
                if shift == 3 {
                    kind.own_rows(base, first, size);
                }
            };
            if !T::DOWN {
                own(base);
            }
            let layer = |k: usize| {
                let half = 1usize << k;
                // The blocks' twiddles: the first's, plus `step(j)` (the block indices' bits are disjoint).
                let t0 = kind.twiddle(k + shift, first >> (k + 1));
                for j in 0..size >> (k + 1) {
                    let row = first + 2 * half * j;
                    let t = splat((t0 + kind.step(j)).0);
                    pairs::<T>(data.add(8 * row), data.add(8 * (row + half)), half, t);
                }
            };
            if T::DOWN {
                (0..leaf).rev().for_each(layer);
                own(base);
            } else {
                (0..leaf).for_each(layer);
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
    kind: &T,
    serial: bool,
) {
    let lines = 1usize << g;
    let width = (TILE_ROWS >> g).clamp(1, 1 << a);
    let per_group = (1usize << a) / width;
    let per = (rows >> (a + g)) * per_group;
    tasks(per * cols.len(), serial, |t| {
        let (Col { data, src }, task) = (cols[t / per], t % per);
        let src = if from_src { src } else { None };
        let row0 = ((task / per_group) << (a + g)) + (task % per_group) * width;
        let line = |u: usize| row0 + (u << a);
        // SAFETY: a task touches rows `line(u) + [0, width)`, `u < lines`: its own.
        unsafe {
            if let Some(s) = src {
                for u in 0..lines {
                    std::ptr::copy_nonoverlapping(s.add(8 * line(u)), data.add(8 * line(u)), 8 * width);
                }
            }
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
            if T::DOWN {
                (0..g).rev().for_each(layer);
            } else {
                (0..g).for_each(layer);
            }
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

    #[inline(always)]
    pub fn to_row(self) -> K8 {
        let mut out = K8::ZERO;
        // SAFETY: a row's eight words.
        unsafe { store(out.0.as_mut_ptr().cast(), self.0) };
        out
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
    let mut out = vec![F64::ONE];
    let mut b = 0;
    while out.len() < len {
        let (zero, one) = (factor(b, false), factor(b, true));
        let half = out.len();
        out.resize(2 * half, F64::ZERO);
        let (low, high) = out.split_at_mut(half);
        parallel::chunks_mut_zip(high, low, 1 << 12, |_, h, l| {
            h.iter_mut().zip(l).for_each(|(h, &l)| *h = l * one)
        });
        if zero != F64::ONE {
            parallel::chunks_mut(low, 1 << 12, |_, l| l.iter_mut().for_each(|x| *x *= zero));
        }
        b += 1;
    }
    out.truncate(len);
    out
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
    let mut out = vec![F64::ZERO; size];
    // SAFETY: `data` is `weights.len()` blocks of `out`'s rows.
    unsafe { fold_rows(data.as_ptr().cast(), out.as_mut_ptr().cast(), size / 8, weights) }
    out
}

/// The values on the coset `ω_first + V_e` of the column of novel coefficients `novel` (any multiple of `2^e` of
/// them, `2^e | first`).
pub fn on_coset_prefix(novel: &[F64], first: usize, e: usize) -> Vec<F64> {
    let size = 1usize << e;
    if novel.len() == size {
        let mut out = vec![F64::ZERO; size];
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
    let mut out: Vec<Vec<F64>> = novels.iter().map(|_| vec![F64::ZERO; size]).collect();
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
    for j in 0..sizes.len() {
        let (at, e) = (starts[j] - base, sizes[j]);
        let mut us: Vec<&mut [F64]> = (0..n).map(|c| range(c, at, 1 << e)).collect();
        coefficients_cols(&mut us, point(starts[j]));
        let us: Vec<&[F64]> = us.into_iter().map(|u| &*u).collect();
        for l in j + 1..sizes.len() {
            let adds = on_coset_prefix_cols(&us, starts[l], sizes[l]);
            let from = starts[l] - base;
            const CHUNK: usize = 1 << 14;
            let len = 1usize << sizes[l];
            let per = len.div_ceil(CHUNK);
            parallel::for_each(per * n, |t| {
                let (c, k) = (t / per, t % per);
                let (lo, hi) = (k * CHUNK, ((k + 1) * CHUNK).min(len));
                let block = range(c, from + lo, hi - lo);
                block.iter_mut().zip(&adds[c][lo..hi]).for_each(|(x, &y)| *x += y);
            });
        }
    }
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
pub fn interpolate_prefix(data: &mut [F64], sizes: &[usize], base: usize) {
    let total: usize = sizes.iter().map(|&e| 1usize << e).sum();
    assert_eq!(data.len(), total);
    assert!(sizes.windows(2).all(|w| w[0] > w[1]) && base % (2 << sizes[0]) == 0);
    let starts = prefix_starts(sizes, base);
    for j in 0..sizes.len() {
        let (at, e) = (starts[j] - base, sizes[j]);
        let (head, tail) = data.split_at_mut(at + (1 << e));
        let u = &mut head[at..];
        coefficients(u, point(starts[j]));
        for l in j + 1..sizes.len() {
            let mut add = on_coset_prefix(u, starts[l], sizes[l]);
            let from = starts[l] - starts[j] - (1 << e);
            let block = &mut tail[from..from + (1 << sizes[l])];
            parallel::chunks_mut_zip(block, &add, 1 << 14, |_, b, a| {
                b.iter_mut().zip(a).for_each(|(x, &y)| *x += y)
            });
            add.clear();
        }
    }
    for j in (0..sizes.len().saturating_sub(1)).rev() {
        let (at, e) = (starts[j] - base, sizes[j]);
        let lambda = point(starts[j] >> e);
        let (q, rest) = data.split_at_mut(at + (1 << e));
        let q = &mut q[at..at + rest.len()];
        parallel::chunks_mut_zip(q, rest, 1 << 14, |_, q, r| {
            q.iter_mut().zip(r).for_each(|(x, &y)| *x += lambda * y)
        });
    }
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

fn subset_sums_of<M: Copy + Send + Sync + Add<Output = M> + Default>(data: &mut [M], src: Option<&[M]>) {
    let n = data.len();
    assert!(n.is_power_of_two());
    let m = n.trailing_zeros() as usize;
    let leaf = m.min(((1usize << 18) / std::mem::size_of::<M>()).max(2).ilog2() as usize);
    parallel::chunks_mut(data, 1 << leaf, |b, block| {
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
    });
    let base = SendPtr(data.as_mut_ptr());
    let mut a = leaf;
    while a < m {
        let g = (m - a).min(8);
        let lines = 1usize << g;
        let width = ((1usize << leaf) >> g).clamp(1, 1 << a);
        let per_group = (1usize << a) / width;
        parallel::for_each((n >> (a + g)) * per_group, |task| {
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
    parallel::for_each((rows >> (a + g)) * per_group, |task| {
        let row0 = ((task / per_group) << (a + g)) + (task % per_group) * width;
        let line = |u: usize| row0 + (u << a);
        // SAFETY: a task touches rows `line(u) + [0, width)`, `u < lines`: its own.
        unsafe {
            if let Some(s) = src {
                for u in 0..lines {
                    std::ptr::copy_nonoverlapping(s.add(8 * line(u)), data.add(8 * line(u)), 8 * width);
                }
            }
            let layer = |j: usize| {
                let k = a + j;
                let hs = 1usize << j;
                for ub in (0..lines).step_by(2 * hs) {
                    let t = splat(kind.twiddle(k + 3, line(ub) >> (k + 1)).0);
                    for u in ub..ub + hs {
                        pairs::<T>(data.add(8 * line(u)), data.add(8 * line(u + hs)), width, t);
                    }
                }
            };
            if T::DOWN {
                (0..g).rev().for_each(layer);
            } else {
                (0..g).for_each(layer);
            }
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
        if T::DOWN {
            (0..leaf).rev().for_each(layer);
            own();
        } else {
            (0..leaf).for_each(layer);
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
        let mut next = rng(3);
        for m in [0usize, 1, 2, 3, 4, 5, 9, 12, 13, 17, 19] {
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
