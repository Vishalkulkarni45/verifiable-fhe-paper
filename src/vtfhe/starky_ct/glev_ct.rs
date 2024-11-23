// use plonky2::{
//     field::{extension::Extendable, packed::PackedField},
//     hash::hash_types::RichField,
//     iop::{target::Target, witness::PartialWitness},
//     plonk::circuit_builder::CircuitBuilder,
//     util::ceil_div_usize,
// };

// use crate::{ntt::ntt_forward, vec_arithmetic::vec_inner};

// use super::{glwe_ct::GlweCtExp, glwe_poly::GlwePolyExp};

// #[derive(Debug)]
// pub struct GlevCtExp<const N: usize, const K: usize, const ELL: usize,T> {
//     pub glwe_cts: [GlweCtExp<N, K,T>; ELL],
// }

// impl<const N: usize, const K: usize, const ELL: usize,P:PackedField> GlevCtExp<N, K, ELL,P> {

//     pub fn flatten(&self) -> Vec<P> {
//         self.glwe_cts
//             .iter()
//             .flat_map(|glwe| glwe.flatten())
//             .collect()
//     }

//     // pub fn num_targets() -> usize {
//     //     K * N * ELL
//     // }

//     pub fn mul<F: RichField + Extendable<D>, const D: usize, const LOGB: usize>(
//         &self,
//         cb: &mut CircuitBuilder<F, D>,
//         glwe_poly: &GlwePolyExp<N,P>,
//     ) -> GlweCtExp<N, K,P> {
//         let num_limbs = ceil_div_usize(F::BITS, LOGB);
//         let limbs = glwe_poly.decompose::<F, D, LOGB>(cb, num_limbs);
//         let limbs_hat = &limbs[num_limbs - ELL..]
//             .iter()
//             .map(|limb| ntt_forward(cb, &limb))
//             .collect();
//         let range: [usize; K] = core::array::from_fn(|i| i);
//         let polys = range.map(|index| GlwePoly {
//             coeffs: vec_inner(cb, limbs_hat, &self.get_row(index))
//                 .try_into()
//                 .unwrap(),
//         });
//         GlweCt { polys: polys }
//     }
// }
