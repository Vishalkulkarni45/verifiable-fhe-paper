use std::array::from_fn;

use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use super::glwe_poly::GlwePolyExp;

#[derive(Debug)]
pub struct GlweCtExp<const N: usize, const K: usize, T> {
    pub polys: [GlwePolyExp<N, T>; K],
}

impl<const N: usize, const K: usize, T> GlweCtExp<N, K, T> {
    pub fn num_targets() -> usize {
        K * N
    }
}

impl<const N: usize, const K: usize, P: PackedField> GlweCtExp<N, K, P> {
    pub fn flatten(&self) -> Vec<P> {
        self.polys.iter().flat_map(|poly| poly.flatten()).collect()
    }

    pub fn add(&self, other: &GlweCtExp<N, K, P>) -> GlweCtExp<N, K, P> {
        let range: [usize; K] = from_fn(|i| i);
        GlweCtExp {
            polys: range.map(|i| self.polys[i].add(&other.polys[i])),
        }
    }

    pub fn sub<F: RichField + Extendable<D>, const D: usize>(
        &self,
        other: &GlweCtExp<N, K, P>,
    ) -> GlweCtExp<N, K, P> {
        let range: [usize; K] = from_fn(|i| i);
        GlweCtExp {
            polys: range.map(|i| self.polys[i].sub(&other.polys[i])),
        }
    }

    pub fn ntt_backward(&self) -> GlweCtExp<N, K, P> {
        GlweCtExp {
            polys: self
                .polys
                .iter()
                .map(|poly| poly.ntt_backward())
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }
}

impl<const N: usize, const K: usize, const D: usize> GlweCtExp<N, K, ExtensionTarget<D>> {
    pub fn flatten_ext(&self) -> Vec<ExtensionTarget<D>> {
        self.polys
            .iter()
            .flat_map(|poly| poly.flatten_ext())
            .collect()
    }

    pub fn add_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        other: &GlweCtExp<N, K, ExtensionTarget<D>>,
    ) -> GlweCtExp<N, K, ExtensionTarget<D>> {
        let range: [usize; K] = from_fn(|i| i);
        GlweCtExp {
            polys: range.map(|i| self.polys[i].add_ext(builder, &other.polys[i])),
        }
    }

    pub fn sub_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        other: &GlweCtExp<N, K, ExtensionTarget<D>>,
    ) -> GlweCtExp<N, K, ExtensionTarget<D>> {
        let range: [usize; K] = from_fn(|i| i);
        GlweCtExp {
            polys: range.map(|i| self.polys[i].sub_ext(builder, &other.polys[i])),
        }
    }

    pub fn ntt_backward_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> GlweCtExp<N, K, ExtensionTarget<D>> {
        GlweCtExp {
            polys: self
                .polys
                .iter()
                .map(|poly| poly.ntt_backward_ext(builder))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }
}
