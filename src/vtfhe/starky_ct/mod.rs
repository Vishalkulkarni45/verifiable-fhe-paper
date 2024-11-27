use ggsw_ct::GgswCtExp;
use glwe_ct::GlweCtExp;
use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use super::{
    eval_glwe_select, eval_glwe_select_ext, eval_rotate_glwe, eval_rotate_glwe_ext, NUM_BITS,
};

pub mod ggsw_ct;
pub mod glev_ct;
pub mod glwe_ct;
pub mod glwe_poly;
pub mod vpbs;

pub fn eval_step_circuit<
    P: PackedField,
    const N: usize,
    const K: usize,
    const ELL: usize,
    const LOGB: usize,
>(
    yield_constr: &mut ConstraintConsumer<P>,
    current_acc_in: GlweCtExp<N, K, P>,
    ggsw_ct: GgswCtExp<N, K, ELL, P>,
    mask_element: P,
    mask_ele_bit_dec: [P; NUM_BITS],
    xprod_in_bit_dec: [[Vec<P>; N]; K],
    non_pad_flag: P,
    is_first_row: P,
    is_last_non_pad_row: P,
) -> GlweCtExp<N, K, P> {
    let neg_mask = -mask_element;

    let first_negated_mask = is_first_row * (neg_mask - mask_element) + mask_element;

    let shifted_glwe = eval_rotate_glwe(
        yield_constr,
        non_pad_flag,
        &current_acc_in,
        first_negated_mask,
        mask_ele_bit_dec,
    );

    let diff_glwe = shifted_glwe.sub(&current_acc_in);
    let xprod_in = eval_glwe_select(is_last_non_pad_row, &current_acc_in, &diff_glwe);
    let xprod_out =
        ggsw_ct.eval_external_product::<LOGB>(yield_constr, &xprod_in, xprod_in_bit_dec);
    let cmux_out = xprod_out.add(&current_acc_in);

    // in the last step we don't do a cmux, but just an external product for key switch
    let cmux_or_exprod = eval_glwe_select(is_last_non_pad_row, &xprod_out, &cmux_out);

    // in the first step (body) we don't apply the full CMUX, just the rotation
    let current_acc_out = eval_glwe_select(is_first_row, &shifted_glwe, &cmux_or_exprod);

    current_acc_out
}

pub fn eval_step_circuit_ext<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
    const ELL: usize,
    const LOGB: usize,
>(
    builder: &mut CircuitBuilder<F, D>,
    yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    current_acc_in: GlweCtExp<N, K, ExtensionTarget<D>>,
    ggsw_ct: GgswCtExp<N, K, ELL, ExtensionTarget<D>>,
    mask_element: ExtensionTarget<D>,
    mask_ele_bit_dec: [ExtensionTarget<D>; NUM_BITS],
    xprod_in_bit_dec: [[Vec<ExtensionTarget<D>>; N]; K],
    non_pad_flag: ExtensionTarget<D>,
    is_first_row: ExtensionTarget<D>,
    is_last_non_pad_row: ExtensionTarget<D>,
) -> GlweCtExp<N, K, ExtensionTarget<D>> {
    let one = builder.one_extension();
    let neg_mask = builder.mul_extension(one, mask_element);
    let diff = builder.sub_extension(neg_mask, mask_element);
    let first_negated_mask = builder.mul_add_extension(is_first_row, diff, mask_element);

    let shifted_glwe = eval_rotate_glwe_ext(
        builder,
        yield_constr,
        non_pad_flag,
        &current_acc_in,
        first_negated_mask,
        mask_ele_bit_dec,
    );

    let diff_glwe = shifted_glwe.sub_ext(builder, &current_acc_in);
    let xprod_in = eval_glwe_select_ext(builder, is_last_non_pad_row, &current_acc_in, &diff_glwe);
    let xprod_out = ggsw_ct.eval_external_product_ext::<F, LOGB>(
        builder,
        yield_constr,
        &xprod_in,
        xprod_in_bit_dec,
    );
    let cmux_out = xprod_out.add_ext(builder, &current_acc_in);

    // in the last step we don't do a cmux, but just an external product for key switch
    let cmux_or_exprod = eval_glwe_select_ext(builder, is_last_non_pad_row, &xprod_out, &cmux_out);

    // in the first step (body) we don't apply the full CMUX, just the rotation
    let current_acc_out =
        eval_glwe_select_ext(builder, is_first_row, &shifted_glwe, &cmux_or_exprod);

    current_acc_out
}
