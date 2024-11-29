use std::array::from_fn;

use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};

use crate::vtfhe::{crypto::glwe::Glwe, NUM_BITS};

use super::glwe_poly::{GlwePolyExp, GlwePolyNative};

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

    pub fn sub(&self, other: &GlweCtExp<N, K, P>) -> GlweCtExp<N, K, P> {
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
pub fn decimal_to_binary<F: RichField + Extendable<D>, const D: usize>(
    number: u64,
) -> [F; NUM_BITS] {
    let mut binary = [F::ZERO; NUM_BITS];
    let mut num = number;

    let mut i = 0;
    while num > 0 {
        let bit = num % 2;
        binary[i] = F::from_canonical_u64(bit);
        num /= 2;
        i += 1;
    }

    binary
}

#[derive(Debug, Clone, PartialEq)]
pub struct GlweCtNative<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
> {
    pub polys: [GlwePolyNative<F, D, N>; K],
}

impl<F: RichField + Extendable<D>, const D: usize, const N: usize, const K: usize>
    GlweCtNative<F, D, N, K>
{
    pub fn flatten(&self) -> Vec<F> {
        self.polys.iter().flat_map(|poly| poly.flatten()).collect()
    }

    pub fn new_from_slice(input: &[F]) -> Self {
        let poly_targets = GlwePolyNative::<F, D, N>::num_targets();
        assert_eq!(
            input.len(),
            K * poly_targets,
            "Incorrect number of targets to construct GlweCtNative."
        );
        GlweCtNative {
            polys: input
                .chunks(poly_targets)
                .map(|t| GlwePolyNative::<F, D, N>::new_from_slice(t))
                .collect::<Vec<_>>()
                .try_into()
                .unwrap(),
        }
    }

    pub fn get_pos_bit_dec(&self) -> [[[F; NUM_BITS]; N]; K] {
        let coeffs_u64: Vec<Vec<u64>> = self
            .polys
            .iter()
            .map(|poly| {
                poly.coeffs
                    .iter()
                    .map(|coeff| coeff.to_canonical_u64())
                    .collect()
            })
            .collect();
        assert_eq!(coeffs_u64.len(), K);
        assert_eq!(coeffs_u64[0].len(), N);

        let pos_bit_dec: [[[F; NUM_BITS]; N]; K] = std::array::from_fn(|i| {
            std::array::from_fn(|j| decimal_to_binary::<F, D>(coeffs_u64[i][j]))
        });
        pos_bit_dec
    }

    pub fn get_neg_bit_dec(&self) -> [[[F; NUM_BITS]; N]; K] {
        let coeffs_u64: Vec<Vec<u64>> = self
            .polys
            .iter()
            .map(|poly| {
                poly.coeffs
                    .iter()
                    .map(|coeff| (-*coeff).to_canonical_u64())
                    .collect()
            })
            .collect();
        assert_eq!(coeffs_u64.len(), K);
        assert_eq!(coeffs_u64[0].len(), N);

        let neg_bit_dec: [[[F; NUM_BITS]; N]; K] = std::array::from_fn(|i| {
            std::array::from_fn(|j| decimal_to_binary::<F, D>(coeffs_u64[i][j]))
        });

        neg_bit_dec
    }

    pub fn dummy_ct() -> Self {
        GlweCtNative {
            polys: from_fn(|_| GlwePolyNative::dummy_ct()),
        }
    }

    pub fn from_glwe(input: &Glwe<F, D, N, K>) -> Self {
        GlweCtNative {
            polys: input
                .polys
                .clone()
                .map(|poly| GlwePolyNative::from_poly(&poly)),
        }
    }
    pub fn add(&self, other: &GlweCtNative<F, D, N, K>) -> GlweCtNative<F, D, N, K> {
        let range: [usize; K] = from_fn(|i| i);
        GlweCtNative {
            polys: range.map(|i| self.polys[i].add(&other.polys[i])),
        }
    }

    pub fn sub(&self, other: &GlweCtNative<F, D, N, K>) -> GlweCtNative<F, D, N, K> {
        let range: [usize; K] = from_fn(|i| i);
        GlweCtNative {
            polys: range.map(|i| self.polys[i].sub(&other.polys[i])),
        }
    }

    pub fn ntt_backward(&self) -> GlweCtNative<F, D, N, K> {
        GlweCtNative {
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
