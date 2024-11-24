use std::array::from_fn;

use itertools::Itertools;
use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::field::types::Field as PlonkyField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use crate::vtfhe::eval_le_sum_ext;
use crate::{
    ntt::{eval_ntt_backward, eval_ntt_backward_ext},
    vtfhe::{eval_le_sum, NUM_BITS},
};
pub const MODULUS_U8: [u8; 64] = [
    1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0,
    1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1,
];
pub fn eval_plus_or_minus<P: PackedField>(
    yield_constr: &mut ConstraintConsumer<P>,
    b: P,
    x: P,
) -> P {
    yield_constr.constraint(b * b - b);

    let x_neg = -x;

    b * (x_neg - x) + x
}

pub fn eval_plus_or_minus_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    b: ExtensionTarget<D>,
    x: ExtensionTarget<D>,
) -> ExtensionTarget<D> {
    let one = builder.one_extension();
    let constr = builder.mul_sub_extension(b, b, b);
    yield_constr.constraint(builder, constr);

    let x_neg = builder.mul_extension(x, one);
    let diff = builder.sub_extension(x_neg, x);
    builder.mul_add_extension(b, diff, x)
}

pub fn eval_two_s_comp<P: PackedField>(bits: Vec<P>) -> Vec<P> {
    let one = P::ONES;
    let zero = P::ZEROS;

    let one_s = bits
        .into_iter()
        .map(|bit| (one - bit) + bit * zero)
        .collect_vec();

    let mut carry = one;
    let mut out = Vec::new();

    for bit in one_s.into_iter() {
        let (sum, c_out) = eval_half_adder(bit, carry);
        carry = c_out;
        out.push(sum);
    }

    out
}
pub fn eval_two_s_comp_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    bits: Vec<ExtensionTarget<D>>,
) -> Vec<ExtensionTarget<D>> {
    let one = builder.one_extension();
    let zero = builder.zero_extension();

    let one_s = bits
        .into_iter()
        .map(|bit| {
            let comp = builder.sub_extension(one, bit);
            builder.mul_add_extension(bit, zero, comp)
        })
        .collect_vec();

    let mut carry = one;
    let mut out = Vec::new();

    for bit in one_s.into_iter() {
        let (sum, c_out) = eval_half_adder_ext(builder, bit, carry);
        carry = c_out;
        out.push(sum);
    }

    out
}

//Returns -int mod p = (p - (int mod p))
pub fn eval_neg_ele<P: PackedField>(int: Vec<P>) -> Vec<P> {
    let neg_int = eval_two_s_comp(int);
    let modulus = MODULUS_U8.map(|bit| P::from(P::Scalar::from_canonical_u8(bit)));

    assert_eq!(neg_int.len(), modulus.len());

    let mut c_in = P::ZEROS;

    let mut neg_int_mod = Vec::new();

    for (i, bit) in neg_int.into_iter().enumerate() {
        let (sum, c_out) = eval_full_adder(bit, modulus[i], c_in);
        neg_int_mod.push(sum);
        c_in = c_out;
    }
    neg_int_mod
}

pub fn eval_neg_ele_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    int: Vec<ExtensionTarget<D>>,
) -> Vec<ExtensionTarget<D>> {
    let neg_int = eval_two_s_comp_ext(builder, int);
    let modulus =
        MODULUS_U8.map(|bit| builder.constant_extension(F::Extension::from_canonical_u8(bit)));

    assert_eq!(neg_int.len(), modulus.len());

    let mut c_in = builder.zero_extension();

    let mut neg_int_mod = Vec::new();

    for (i, bit) in neg_int.into_iter().enumerate() {
        let (sum, c_out) = eval_full_adder_ext(builder, bit, modulus[i], c_in);
        neg_int_mod.push(sum);
        c_in = c_out;
    }
    neg_int_mod
}

//select flag = 1 -> vec_a
// s * (a - b) + b
pub fn eval_select_vec<P: PackedField>(select_flag: P, vec_a: Vec<P>, vec_b: Vec<P>) -> Vec<P> {
    vec_a
        .into_iter()
        .zip(vec_b.into_iter())
        .map(|(a, b)| select_flag * (a - b) + b)
        .collect_vec()
}

pub fn eval_select_vec_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    select_flag: ExtensionTarget<D>,
    vec_a: Vec<ExtensionTarget<D>>,
    vec_b: Vec<ExtensionTarget<D>>,
) -> Vec<ExtensionTarget<D>> {
    vec_a
        .into_iter()
        .zip(vec_b.into_iter())
        .map(|(a, b)| {
            let diff = builder.sub_extension(a, b);
            builder.mul_add_extension(select_flag, diff, b)
        })
        .collect_vec()
}

pub fn eval_decompose<P: PackedField, const LOGB: usize>(
    yield_constr: &mut ConstraintConsumer<P>,
    x: P,
    x_bit_dec: Vec<P>,
    num_limbs: usize,
) -> Vec<P> {
    assert_eq!(x_bit_dec.len(), num_limbs * LOGB);
    let cal_x = eval_le_sum(x_bit_dec.clone());
    yield_constr.constraint(x - cal_x);

    let neg_x_bit_dec = eval_neg_ele(x_bit_dec.clone());
    let sgn = &x_bit_dec.last().unwrap();

    let bits_centered = eval_select_vec(**sgn, neg_x_bit_dec, x_bit_dec.clone());

    let zero = P::ZEROS;
    let base = P::from(P::Scalar::from_canonical_u64(1u64 << LOGB));
    bits_centered
        .chunks(LOGB)
        .scan(zero, |carry, limb| {
            let k = eval_le_sum(limb.to_vec());
            let k_w_carry = k + *carry;
            *carry = *limb.last().unwrap();
            let balancer = *carry * base;
            let balanced_k = k_w_carry - balancer;
            Some(eval_plus_or_minus(yield_constr, **sgn, balanced_k))
        })
        .collect()
}
pub fn eval_decompose_ext<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    x: ExtensionTarget<D>,
    x_bit_dec: Vec<ExtensionTarget<D>>,
    num_limbs: usize,
) -> Vec<ExtensionTarget<D>> {
    assert_eq!(x_bit_dec.len(), num_limbs * LOGB);
    let cal_x = eval_le_sum_ext(builder, x_bit_dec.clone());
    let constr = builder.sub_extension(x, cal_x);
    yield_constr.constraint(builder, constr);

    let neg_x_bit_dec = eval_neg_ele_ext(builder, x_bit_dec.clone());
    let sgn = &x_bit_dec.last().unwrap();

    let bits_centered = eval_select_vec_ext(builder, **sgn, neg_x_bit_dec, x_bit_dec.clone());

    let zero = builder.zero_extension();
    let base = builder.constant_extension(F::Extension::from_canonical_u64(1u64 << LOGB));
    bits_centered
        .chunks(LOGB)
        .scan(zero, |carry, limb| {
            let k = eval_le_sum_ext(builder, limb.to_vec());
            let k_w_carry = builder.add_extension(k, *carry);
            *carry = *limb.last().unwrap();
            let balancer = builder.mul_extension(*carry, base);
            let balanced_k = builder.sub_extension(k_w_carry, balancer);
            Some(eval_plus_or_minus_ext(
                builder,
                yield_constr,
                **sgn,
                balanced_k,
            ))
        })
        .collect()
}

//TODO: Add constrain a , b, c_in are bits
fn eval_half_adder<P: PackedField>(a: P, b: P) -> (P, P) {
    let two = P::Scalar::from_canonical_u8(2);
    let c_out = a * b;
    let sum = a + b - two * c_out;

    (sum, c_out)
}
fn eval_half_adder_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: ExtensionTarget<D>,
    b: ExtensionTarget<D>,
) -> (ExtensionTarget<D>, ExtensionTarget<D>) {
    let two = builder.constant_extension(F::Extension::from_canonical_u8(2));
    let c_out = builder.mul_extension(a, b);
    let a_or_b = builder.add_extension(a, b);
    let two_and_c_out = builder.mul_extension(two, c_out);
    let sum = builder.sub_extension(a_or_b, two_and_c_out);
    (sum, c_out)
}
//TODO: Add constrain a , b, c_in are bits
fn eval_full_adder<P: PackedField>(a: P, b: P, c_in: P) -> (P, P) {
    let two = P::Scalar::from_canonical_u8(2);
    let a_and_b = a * b;
    let a_xor_b = a + b - two * a_and_b;

    let sum = a_xor_b + c_in - two * a_xor_b * c_in;
    let c_out = (a_xor_b * c_in) + a_and_b;

    (sum, c_out)
}

fn eval_full_adder_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    a: ExtensionTarget<D>,
    b: ExtensionTarget<D>,
    c_in: ExtensionTarget<D>,
) -> (ExtensionTarget<D>, ExtensionTarget<D>) {
    let two = builder.constant_extension(F::Extension::from_canonical_u8(2));

    let a_or_b = builder.add_extension(a, b);
    let a_and_b = builder.mul_extension(a, b);
    let two_and_a_b = builder.mul_extension(two, a_and_b);
    let a_xor_b = builder.sub_extension(a_or_b, two_and_a_b);

    let a_xor_b_or_cin = builder.add_extension(a_xor_b, c_in);
    let a_xor_b_or_cin_and_c_in = builder.mul_extension(a_xor_b, c_in);
    let two_or_a_xor_b_and_cin = builder.mul_extension(two, a_xor_b_or_cin_and_c_in);
    let sum = builder.sub_extension(a_xor_b_or_cin, two_or_a_xor_b_and_cin);

    let c_out = builder.mul_add_extension(a_xor_b, c_in, a_and_b);

    (sum, c_out)
}

#[derive(Debug)]
pub struct GlwePolyExp<const N: usize, T> {
    pub coeffs: [T; N],
}
impl<const N: usize, T> GlwePolyExp<N, T> {
    pub fn num_targets() -> usize {
        N
    }
}

impl<const N: usize, P: PackedField> GlwePolyExp<N, P> {
    pub fn flatten(&self) -> Vec<P> {
        self.coeffs.to_vec()
    }

    pub fn add(&self, other: &GlwePolyExp<N, P>) -> GlwePolyExp<N, P> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePolyExp {
            coeffs: range.map(|i| self.coeffs[i] + other.coeffs[i]),
        }
    }

    pub fn sub(&self, other: &GlwePolyExp<N, P>) -> GlwePolyExp<N, P> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePolyExp {
            coeffs: range.map(|i| self.coeffs[i] - other.coeffs[i]),
        }
    }

    pub fn ntt_backward(&self) -> GlwePolyExp<N, P> {
        GlwePolyExp {
            coeffs: eval_ntt_backward(&self.coeffs.to_vec()).try_into().unwrap(),
        }
    }

    pub fn rotate(&self, shift: usize) -> GlwePolyExp<N, P> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePolyExp {
            coeffs: range.map(|i| {
                if i < shift {
                    -self.coeffs[N - shift + i]
                } else {
                    self.coeffs[i - shift]
                }
            }),
        }
    }

    pub fn eval_decompose<const LOGB: usize>(
        &self,
        yield_constr: &mut ConstraintConsumer<P>,
        coeffs_bit_dec: [Vec<P>; N],
        num_limbs: usize,
    ) -> Vec<Vec<P>> {
        let decomps = self.coeffs.iter().enumerate().map(|(i, xi)| {
            eval_decompose::<P, LOGB>(yield_constr, *xi, coeffs_bit_dec[i].clone(), num_limbs)
        });
        let mut acc = vec![Vec::new(); num_limbs];
        for t in decomps {
            for i in 0..num_limbs {
                acc[i].push(t[i])
            }
        }
        acc
    }
}
impl<const N: usize, const D: usize> GlwePolyExp<N, ExtensionTarget<D>> {
    pub fn flatten_ext(&self) -> Vec<ExtensionTarget<D>> {
        self.coeffs.to_vec()
    }

    pub fn add_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        other: &GlwePolyExp<N, ExtensionTarget<D>>,
    ) -> GlwePolyExp<N, ExtensionTarget<D>> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePolyExp {
            coeffs: range.map(|i| builder.add_extension(self.coeffs[i], other.coeffs[i])),
        }
    }

    pub fn sub_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        other: &GlwePolyExp<N, ExtensionTarget<D>>,
    ) -> GlwePolyExp<N, ExtensionTarget<D>> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePolyExp {
            coeffs: range.map(|i| builder.sub_extension(self.coeffs[i], other.coeffs[i])),
        }
    }

    pub fn ntt_backward_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> GlwePolyExp<N, ExtensionTarget<D>> {
        GlwePolyExp {
            coeffs: eval_ntt_backward_ext(builder, &self.coeffs.to_vec())
                .try_into()
                .unwrap(),
        }
    }

    pub fn rotate_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        shift: usize,
    ) -> GlwePolyExp<N, ExtensionTarget<D>> {
        let range: [usize; N] = from_fn(|i| i);
        let neg_one = builder.neg_one_extension();
        GlwePolyExp {
            coeffs: range.map(|i| {
                if i < shift {
                    builder.mul_extension(neg_one, self.coeffs[N - shift + i])
                } else {
                    self.coeffs[i - shift]
                }
            }),
        }
    }
    pub fn eval_decompose_ext<F: RichField + Extendable<D>, const LOGB: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        coeffs_bit_dec: [Vec<ExtensionTarget<D>>; N],
        num_limbs: usize,
    ) -> Vec<Vec<ExtensionTarget<D>>> {
        let decomps = self.coeffs.iter().enumerate().map(|(i, xi)| {
            eval_decompose_ext::<F, D, LOGB>(
                builder,
                yield_constr,
                *xi,
                coeffs_bit_dec[i].clone(),
                num_limbs,
            )
        });
        let mut acc = vec![Vec::new(); num_limbs];
        for t in decomps {
            for i in 0..num_limbs {
                acc[i].push(t[i])
            }
        }
        acc
    }
}
