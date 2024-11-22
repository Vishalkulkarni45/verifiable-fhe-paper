use std::array::from_fn;

use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::ntt::{eval_ntt_backward, eval_ntt_backward_ext};

//TODO: Give better name to GlwePolyExp

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
