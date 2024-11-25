use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
    util::ceil_div_usize,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use crate::{
    ntt::{eval_ntt_forward, eval_ntt_forward_ext},
    vec_arithmetic::{eval_vec_inner, eval_vec_inner_ext},
};

use super::{glwe_ct::GlweCtExp, glwe_poly::GlwePolyExp};

#[derive(Debug)]
pub struct GlevCtExp<const N: usize, const K: usize, const ELL: usize, T> {
    pub glwe_cts: [GlweCtExp<N, K, T>; ELL],
}

impl<const N: usize, const K: usize, const ELL: usize, T> GlevCtExp<N, K, ELL, T>
where
    T: Clone,
{
    pub fn get_row(&self, index: usize) -> Vec<Vec<T>> {
        self.glwe_cts
            .iter()
            .map(|ct| ct.polys[index].coeffs.to_vec())
            .into_iter()
            .collect()
    }

    pub fn num_targets() -> usize {
        K * N * ELL
    }
}

impl<const N: usize, const K: usize, const ELL: usize, P: PackedField> GlevCtExp<N, K, ELL, P> {
    pub fn flatten(&self) -> Vec<P> {
        self.glwe_cts
            .iter()
            .flat_map(|glwe| glwe.flatten())
            .collect()
    }

    pub fn eval_mul<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(
        &self,
        yield_constr: &mut ConstraintConsumer<P>,
        glwe_poly: &GlwePolyExp<N, P>,
        coeffs_bit_dec: &[Vec<P>; N],
    ) -> GlweCtExp<N, K, P> {
        let num_limbs = ceil_div_usize(F::BITS, LOGB);
        let limbs = glwe_poly.eval_decompose::<LOGB>(yield_constr, coeffs_bit_dec, num_limbs);
        let limbs_hat = &limbs[num_limbs - ELL..]
            .iter()
            .map(|limb| eval_ntt_forward(&limb))
            .collect();
        let range: [usize; K] = core::array::from_fn(|i| i);
        let polys = range.map(|index| GlwePolyExp {
            coeffs: eval_vec_inner(limbs_hat, &self.get_row(index))
                .try_into()
                .unwrap(),
        });
        GlweCtExp { polys }
    }
}

impl<const D: usize, const N: usize, const K: usize, const ELL: usize>
    GlevCtExp<N, K, ELL, ExtensionTarget<D>>
{
    pub fn flatten_ext(&self) -> Vec<ExtensionTarget<D>> {
        self.glwe_cts
            .iter()
            .flat_map(|glwe| glwe.flatten_ext())
            .collect()
    }

    pub fn eval_mul_ext<F: RichField + Extendable<D>, const LOGB: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        glwe_poly: &GlwePolyExp<N, ExtensionTarget<D>>,
        coeffs_bit_dec: &[Vec<ExtensionTarget<D>>; N],
    ) -> GlweCtExp<N, K, ExtensionTarget<D>> {
        let num_limbs = ceil_div_usize(F::BITS, LOGB);
        let limbs = glwe_poly.eval_decompose_ext::<F, LOGB>(
            builder,
            yield_constr,
            coeffs_bit_dec,
            num_limbs,
        );
        let limbs_hat = &limbs[num_limbs - ELL..]
            .iter()
            .map(|limb| eval_ntt_forward_ext(builder, &limb))
            .collect();
        let range: [usize; K] = core::array::from_fn(|i| i);
        let polys = range.map(|index| GlwePolyExp {
            coeffs: eval_vec_inner_ext(builder, limbs_hat, &self.get_row(index))
                .try_into()
                .unwrap(),
        });
        GlweCtExp { polys }
    }
}
