//| cur_acc_in |      ggsw_ct     | mask_ele | mask_ele_bit_dec |   xprod_in_bit_dec  | non_pad_flag | is_first_row | is_last_non_pad_row |
//|    N * K   |  K * K * N * ELL |     1    |     NUM_BITS     |   NUM_BITS * N * K  |       1      |       1      |          1          |
//|    GLWE    |       GGSW       |
use crate::{
    ntt::params::N,
    vtfhe::{
        crypto::{compute_bsk, ggsw::Ggsw, glwe::Glwe, lwe::encrypt, poly::Poly},
        starky_ct::{generate_build_circuit_input, ggsw_ct::GgswCtNative, glwe_ct::GlweCtNative},
        NUM_BITS,
    },
};
use std::{array::from_fn, marker::PhantomData};

use itertools::Itertools;
use plonky2::{
    field::{
        extension::{Extendable, FieldExtension},
        packed::PackedField,
    },
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
    util::log2_ceil,
};
use rand::random;
use starky::{
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    evaluation_frame::StarkFrame,
    stark::Stark,
};

const LOGB: usize = 8;
const ELL: usize = 8;
const K: usize = 2;
const D: usize = 2;
const n: usize = 1;

const VPBS_COLUMNS: usize = N * K + K * K * N * ELL + 1 + NUM_BITS + NUM_BITS * N * K + 3 * 1;
const VPBS_PUBLIC_INPUT: usize = 0;

#[derive(Clone, Copy)]
pub struct VpbsStark<F: RichField + Extendable<D>, const D: usize> {
    pub num_rows: usize,
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> VpbsStark<F, D> {
    fn generate_trace(&self) {
        let mut lv = vec![F::ZERO; VPBS_COLUMNS];

        let num_rows = 1 << (64 - ((n + 2) - 1).leading_zeros());

        let s_to = Glwe::<F, D, N, K>::partial_key(n);
        let s_lwe = Glwe::<F, D, N, K>::flatten_partial_key(&s_to, n);
        println!("s_lwe: {:?}", s_lwe);
        let s_glwe = Glwe::<F, D, N, K>::key_gen();
        let bsk = compute_bsk::<F, D, N, K, ELL, LOGB>(&s_lwe, &s_glwe, 0f64);

        let ksk = Ggsw::<F, D, N, K, ELL>::compute_ksk::<LOGB>(&s_to, &s_glwe, 0f64);

        let testv = Poly::<F, D, N> {
            coeffs: from_fn(|i| F::from_canonical_usize(i)),
        };
        println!("testv: {:?}", testv);
        let delta = F::from_noncanonical_biguint(F::order() >> log2_ceil(2 * N));
        let m = F::from_canonical_u64(random::<u64>() % (N as u64));
        println!("message: {delta} * {m} = {}", delta * m);
        let ct = encrypt::<F, D, n>(&s_lwe, &(delta * m), 0f64);

        let coeffs = vec![F::ZERO; N * (K - 1)]
            .into_iter()
            .chain(testv.coeffs.into_iter())
            .collect_vec();
        let mut current_acc_in = GlweCtNative::new_from_slice(&coeffs);
        let dummy_ggsw_ct = GgswCtNative::<F, D, N, K, ELL>::dummy_ct();
        current_acc_in = generate_build_circuit_input::<F, D, n, N, K, ELL, LOGB>(
            &current_acc_in,
            dummy_ggsw_ct,
            ct[n],
            F::ONE,
        );

        for x in 0..n {
            let counter = F::from_canonical_usize(x + 2);

            let ggsw_ct = GgswCtNative::from_ggsw(&bsk[x]);
            current_acc_in = generate_build_circuit_input::<F, D, n, N, K, ELL, LOGB>(
                &current_acc_in,
                ggsw_ct,
                ct[x],
                counter,
            );
        }

        let ksk_native = GgswCtNative::from_ggsw(&ksk);

        let counter = F::from_canonical_usize(n + 2);
        current_acc_in = generate_build_circuit_input::<F, D, n, N, K, ELL, LOGB>(
            &current_acc_in,
            ksk_native,
            F::ZERO,
            counter,
        );
    }
}

impl<F: RichField + Extendable<D>, const D: usize> Stark<F, D> for VpbsStark<F, D> {
    type EvaluationFrame<FE, P, const D2: usize>
        = StarkFrame<P, P::Scalar, VPBS_COLUMNS, VPBS_PUBLIC_INPUT>
    where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>;

    type EvaluationFrameTarget =
        StarkFrame<ExtensionTarget<D>, ExtensionTarget<D>, VPBS_COLUMNS, VPBS_PUBLIC_INPUT>;

    fn eval_packed_generic<FE, P, const D2: usize>(
        &self,
        vars: &Self::EvaluationFrame<FE, P, D2>,
        yield_constr: &mut ConstraintConsumer<P>,
    ) where
        FE: FieldExtension<D2, BaseField = F>,
        P: PackedField<Scalar = FE>,
    {
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: &Self::EvaluationFrameTarget,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
    }

    fn constraint_degree(&self) -> usize {
        3
    }
}
