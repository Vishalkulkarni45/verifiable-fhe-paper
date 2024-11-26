use std::array::from_fn;

use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use super::{glev_ct::GlevCtExp, glwe_ct::GlweCtExp, glwe_poly::GlwePolyExp};

pub fn eval_glwe_add_many<const N: usize, const K: usize, P: PackedField>(
    glwes: &[GlweCtExp<N, K, P>],
) -> GlweCtExp<N, K, P> {
    let range: [usize; K] = from_fn(|i| i);
    let init = GlweCtExp {
        polys: range.map(|_| GlwePolyExp {
            coeffs: [P::ZEROS; N],
        }),
    };

    glwes.into_iter().fold(init, |acc, t| acc.add(&t))
}

pub fn eval_glwe_add_many_ext<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    glwes: &[GlweCtExp<N, K, ExtensionTarget<D>>],
) -> GlweCtExp<N, K, ExtensionTarget<D>> {
    let range: [usize; K] = from_fn(|i| i);
    let zero = builder.zero_extension();
    let init = GlweCtExp {
        polys: range.map(|_| GlwePolyExp { coeffs: [zero; N] }),
    };

    glwes
        .into_iter()
        .fold(init, |acc, t| acc.add_ext(builder, &t))
}

#[derive(Debug)]
pub struct GgswCtExp<const N: usize, const K: usize, const ELL: usize, T> {
    pub glev_cts: [GlevCtExp<N, K, ELL, T>; K],
}

impl<const N: usize, const K: usize, const ELL: usize, T> GgswCtExp<N, K, ELL, T> {
    pub fn num_targets() -> usize {
        K * K * N * ELL
    }
}

impl<const N: usize, const K: usize, const ELL: usize, P: PackedField> GgswCtExp<N, K, ELL, P> {
    pub fn flatten(&self) -> Vec<P> {
        self.glev_cts
            .iter()
            .flat_map(|glev| glev.flatten())
            .collect()
    }

    //TODO: I think by using mul_add togther we can reduce no of operations, rather than doing first mul and then adding them togehter
    pub fn eval_external_product<const LOGB: usize>(
        &self,
        yield_constr: &mut ConstraintConsumer<P>,
        glwe: &GlweCtExp<N, K, P>,
        glwe_poly_coeffs_bit_dec: [[Vec<P>; N]; K],
    ) -> GlweCtExp<N, K, P> {
        let glev_muls: Vec<GlweCtExp<N, K, P>> = glwe
            .polys
            .iter()
            .zip(self.glev_cts.iter())
            .enumerate()
            .map(|(i, (glwe_poly, glev))| {
                glev.eval_mul::<LOGB>(yield_constr, &glwe_poly, &glwe_poly_coeffs_bit_dec[i])
            })
            .collect();
        let sum_polys = eval_glwe_add_many(&glev_muls[..K - 1]);
        // sum_polys.sub(cb, &glev_muls[K - 1]).ntt_backward(cb)
        glev_muls[K - 1].sub(&sum_polys).ntt_backward()
    }
}
impl<const D: usize, const N: usize, const K: usize, const ELL: usize>
    GgswCtExp<N, K, ELL, ExtensionTarget<D>>
{
    pub fn eval_flatten(&self) -> Vec<ExtensionTarget<D>> {
        self.glev_cts
            .iter()
            .flat_map(|glev| glev.flatten_ext())
            .collect()
    }

    pub fn eval_external_product_ext<F: RichField + Extendable<D>, const LOGB: usize>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
        glwe: &GlweCtExp<N, K, ExtensionTarget<D>>,
        glwe_poly_coeffs_bit_dec: [[Vec<ExtensionTarget<D>>; N]; K],
    ) -> GlweCtExp<N, K, ExtensionTarget<D>> {
        let glev_muls: Vec<GlweCtExp<N, K, ExtensionTarget<D>>> = glwe
            .polys
            .iter()
            .zip(self.glev_cts.iter())
            .enumerate()
            .map(|(i, (glwe_poly, glev))| {
                glev.eval_mul_ext::<F, LOGB>(
                    builder,
                    yield_constr,
                    &glwe_poly,
                    &glwe_poly_coeffs_bit_dec[i],
                )
            })
            .collect();
        let sum_polys = eval_glwe_add_many_ext(builder, &glev_muls[..K - 1]);
        // sum_polys.sub(cb, &glev_muls[K - 1]).ntt_backward(cb)
        glev_muls[K - 1]
            .sub_ext(builder, &sum_polys)
            .ntt_backward_ext(builder)
    }
}
