use std::array::from_fn;

use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
    util::ceil_div_usize,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use crate::{
    ntt::{eval_ntt_forward, eval_ntt_forward_ext, ntt_forward_native},
    vec_arithmetic::{eval_vec_inner, eval_vec_inner_ext, vec_inner_native},
    vtfhe::{
        crypto::{glev::Glev, glwe::Glwe},
        NUM_BITS,
    },
};

use super::{
    glwe_ct::{GlweCtExp, GlweCtNative},
    glwe_poly::{GlwePolyExp, GlwePolyNative},
};

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

    pub fn eval_mul<const LOGB: usize>(
        &self,
        yield_constr: &mut ConstraintConsumer<P>,
        glwe_poly: &GlwePolyExp<N, P>,
        coeffs_bit_dec: &[Vec<P>; N],
    ) -> GlweCtExp<N, K, P> {
        let num_limbs = ceil_div_usize(NUM_BITS, LOGB);
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
#[derive(Debug)]
pub struct GlevCtNative<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
    const ELL: usize,
> {
    pub glwe_cts: [GlweCtNative<F, D, N, K>; ELL],
}

impl<
        F: RichField + Extendable<D>,
        const D: usize,
        const N: usize,
        const K: usize,
        const ELL: usize,
    > GlevCtNative<F, D, N, K, ELL>
{
    pub fn flatten(&self) -> Vec<F> {
        self.glwe_cts
            .iter()
            .flat_map(|glwe| glwe.flatten())
            .collect()
    }
    pub fn get_row(&self, index: usize) -> Vec<Vec<F>> {
        self.glwe_cts
            .iter()
            .map(|ct| ct.polys[index].coeffs.to_vec())
            .into_iter()
            .collect()
    }

    pub fn num_targets() -> usize {
        K * N * ELL
    }

    pub fn mul<const LOGB: usize>(
        &self,
        glwe_poly: &GlwePolyNative<F, D, N>,
        coeffs_bit_dec: &[[F; NUM_BITS]; N],
        neg_coeffs_bit_dec: &[[F; NUM_BITS]; N],
    ) -> GlweCtNative<F, D, N, K> {
        let num_limbs = ceil_div_usize(NUM_BITS, LOGB);
        let limbs = glwe_poly.decompose::<LOGB>(
            coeffs_bit_dec.clone(),
            neg_coeffs_bit_dec.clone(),
            num_limbs,
        );
        let limbs_hat = &limbs[num_limbs - ELL..]
            .iter()
            .map(|limb| ntt_forward_native(&limb))
            .collect();
        let range: [usize; K] = core::array::from_fn(|i| i);
        let polys = range.map(|index| GlwePolyNative {
            coeffs: vec_inner_native(limbs_hat, &self.get_row(index))
                .try_into()
                .unwrap(),
        });
        GlweCtNative { polys }
    }
    pub fn dummy_ct() -> Self {
        GlevCtNative {
            glwe_cts: from_fn(|_| GlweCtNative::dummy_ct()),
        }
    }
    pub fn from_glev(input: &Glev<F, D, N, K, ELL>) -> Self {
        GlevCtNative {
            glwe_cts: input
                .glwes
                .clone()
                .map(|glwe| GlweCtNative::from_glwe(&glwe)),
        }
    }
}
