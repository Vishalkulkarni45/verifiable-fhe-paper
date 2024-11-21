use std::array::from_fn;

use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::plonk::circuit_builder::CircuitBuilder;

use crate::ntt::{eval_ntt_backward, eval_ntt_backward_ext};

#[derive(Debug)]
pub struct GlwePoly<const N: usize, T> {
    pub coeffs: [T; N],
}

impl<const N: usize, P: PackedField> GlwePoly<N, P> {
    pub fn flatten(&self) -> Vec<P> {
        self.coeffs.to_vec()
    }

    pub fn add(&self, other: &GlwePoly<N, P>) -> GlwePoly<N, P> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePoly {
            coeffs: range.map(|i| self.coeffs[i] + other.coeffs[i]),
        }
    }

    pub fn sub(&self, other: &GlwePoly<N, P>) -> GlwePoly<N, P> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePoly {
            coeffs: range.map(|i| self.coeffs[i] - other.coeffs[i]),
        }
    }

    pub fn ntt_backward(&self) -> GlwePoly<N, P> {
        GlwePoly {
            coeffs: eval_ntt_backward(&self.coeffs.to_vec()).try_into().unwrap(),
        }
    }

    pub fn rotate(&self, shift: usize) -> GlwePoly<N, P> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePoly {
            coeffs: range.map(|i| {
                if i < shift {
                    -self.coeffs[N - shift + i]
                } else {
                    self.coeffs[i - shift]
                }
            }),
        }
    }

    pub fn num_targets() -> usize {
        N
    }
}
impl<const N: usize, const D: usize> GlwePoly<N, ExtensionTarget<D>> {
    pub fn flatten_ext(&self) -> Vec<ExtensionTarget<D>> {
        self.coeffs.to_vec()
    }

    pub fn add_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        other: &GlwePoly<N, ExtensionTarget<D>>,
    ) -> GlwePoly<N, ExtensionTarget<D>> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePoly {
            coeffs: range.map(|i| builder.add_extension(self.coeffs[i], other.coeffs[i])),
        }
    }

    pub fn sub_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        other: &GlwePoly<N, ExtensionTarget<D>>,
    ) -> GlwePoly<N, ExtensionTarget<D>> {
        let range: [usize; N] = from_fn(|i| i);
        GlwePoly {
            coeffs: range.map(|i| builder.sub_extension(self.coeffs[i], other.coeffs[i])),
        }
    }

    pub fn ntt_backward_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
    ) -> GlwePoly<N, ExtensionTarget<D>> {
        GlwePoly {
            coeffs: eval_ntt_backward_ext(builder, &self.coeffs.to_vec())
                .try_into()
                .unwrap(),
        }
    }

    pub fn rotate_ext<F: RichField + Extendable<D>>(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        shift: usize,
    ) -> GlwePoly<N, ExtensionTarget<D>> {
        let range: [usize; N] = from_fn(|i| i);
        let neg_one = builder.neg_one_extension();
        GlwePoly {
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
