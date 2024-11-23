use std::array::from_fn;

use plonky2::field::packable::Packable;
use plonky2::field::packed::PackedField;
use plonky2::field::types::Field as PlonkyField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;
use plonky2::plonk::config::GenericConfig;
use plonky2::{field::extension::Extendable, plonk::config::PoseidonGoldilocksConfig};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use crate::vtfhe::eval_le_sum_ext;
use crate::{
    ntt::{eval_ntt_backward, eval_ntt_backward_ext},
    vtfhe::{eval_le_sum, NUM_BITS},
};

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

pub fn eval_decompose<P: PackedField, const D: usize, const LOGB: usize>(
    yield_constr: &mut ConstraintConsumer<P>,
    x: P,
    x_bit_dec: Vec<P>,
    bits_centered: Vec<P>,
    num_limbs: usize,
) -> Vec<P> {
    assert_eq!(x_bit_dec.len(), num_limbs * LOGB);
    assert_eq!(bits_centered.len(), x_bit_dec.len());
    let cal_x = eval_le_sum(x_bit_dec.clone());
    yield_constr.constraint(x - cal_x);

    let sgn = x_bit_dec.last().unwrap();
    let x_centered_lift = eval_plus_or_minus(yield_constr, *sgn, x);
    let cal_x_centered_lift = eval_le_sum(bits_centered.clone());
    yield_constr.constraint(x_centered_lift - cal_x_centered_lift);

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
            Some(eval_plus_or_minus(yield_constr, *sgn, balanced_k))
        })
        .collect()
}
pub fn eval_decompose_ext<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    x: ExtensionTarget<D>,
    x_bit_dec: Vec<ExtensionTarget<D>>,
    bits_centered: Vec<ExtensionTarget<D>>,
    num_limbs: usize,
) -> Vec<ExtensionTarget<D>> {
    assert_eq!(x_bit_dec.len(), num_limbs * LOGB);
    assert_eq!(bits_centered.len(), x_bit_dec.len());
    let cal_x = eval_le_sum_ext(builder, x_bit_dec.clone());
    let constr = builder.sub_extension(x, cal_x);
    yield_constr.constraint(builder, constr);

    let sgn = x_bit_dec.last().unwrap();
    let x_centered_lift = eval_plus_or_minus_ext(builder, yield_constr, *sgn, x);
    let cal_x_centered_lift = eval_le_sum_ext(builder, bits_centered.clone());
    let constr = builder.sub_extension(x_centered_lift, cal_x_centered_lift);
    yield_constr.constraint(builder, constr);

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
                *sgn,
                balanced_k,
            ))
        })
        .collect()
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
}
#[test]
fn test_decompose_ext() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type FF = <C as GenericConfig<D>>::FE;
}
