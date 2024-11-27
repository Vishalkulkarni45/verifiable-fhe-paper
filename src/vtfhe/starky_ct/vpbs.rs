//| cur_acc_in |      ggsw_ct     | mask_ele | mask_ele_bit_dec |   xprod_in_bit_dec  | non_pad_flag | is_first_row | is_last_non_pad_row |
//|    N * K   |  K * K * N * ELL |     1    |     NUM_BITS     |   NUM_BITS * N * K  |       1      |       1      |          1          |

use crate::{ntt::params::N, vtfhe::NUM_BITS};
use std::marker::PhantomData;

use plonky2::{
    field::{
        extension::{Extendable, FieldExtension},
        packed::PackedField,
    },
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};
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
