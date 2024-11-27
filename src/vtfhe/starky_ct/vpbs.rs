//| cur_acc_in |      ggsw_ct     | mask_ele | mask_ele_bit_dec |   xprod_in_bit_dec  | non_pad_flag | is_first_row | is_last_non_pad_row |
//|    N * K   |  K * K * N * ELL |     1    |     NUM_BITS     |   NUM_BITS * N * K  |       1      |       1      |          1          |
//|    GLWE    |       GGSW       |
use crate::{
    ntt::params::N,
    vtfhe::{
        crypto::{compute_bsk, ggsw::Ggsw, glwe::Glwe, lwe::encrypt, poly::Poly},
        NUM_BITS,
    },
};
use std::{array::from_fn, marker::PhantomData};

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
