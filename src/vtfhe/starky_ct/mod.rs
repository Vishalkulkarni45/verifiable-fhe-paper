use core::fmt;

use ggsw_ct::{GgswCtExp, GgswCtNative};
use glev_ct::{GlevCtExp, GlevCtNative};
use glwe_ct::{decimal_to_binary, GlweCtExp, GlweCtNative};
use glwe_poly::{GlwePolyExp, GlwePolyNative};
use itertools::Itertools;
use plonky2::{
    field::{extension::Extendable, packed::PackedField},
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::circuit_builder::CircuitBuilder,
};
use starky::constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer};

use super::{
    eval_glwe_select, eval_glwe_select_ext, eval_rotate_glwe, eval_rotate_glwe_ext,
    rotate_glwe_native, NUM_BITS,
};

pub mod ggsw_ct;
pub mod glev_ct;
pub mod glwe_ct;
pub mod glwe_poly;
pub mod vpbs;

pub fn generate_build_circuit_input<
    F: RichField + Extendable<D>,
    const D: usize,
    const n: usize,
    const N: usize,
    const K: usize,
    const ELL: usize,
    const LOGB: usize,
>(
    current_acc_in: &GlweCtNative<F, D, N, K>,
    ggsw_ct: &GgswCtNative<F, D, N, K, ELL>,
    mask_ele: F,
    counter: F,
) -> (GlweCtNative<F, D, N, K>, [[[F; 64]; N]; K]) {
    let first_neg_mask = if counter == F::ONE {
        -mask_ele
    } else {
        mask_ele
    };

    let mask_ele_bit_dec = decimal_to_binary(first_neg_mask.to_canonical_u64());

    let shifted_glwe = rotate_glwe_native(current_acc_in, mask_ele_bit_dec);

    let diff_glwe = shifted_glwe.sub(&current_acc_in);

    let xprod_in = if counter == F::from_canonical_usize(n + 2) {
        current_acc_in.clone()
    } else {
        diff_glwe
    };

    let xprod_in_pos_bit_dec = xprod_in.get_pos_bit_dec();
    let xprod_in_neg_bit_dec = xprod_in.get_neg_bit_dec();

    let xprod_out =
        ggsw_ct.external_product::<LOGB>(&xprod_in, xprod_in_pos_bit_dec, xprod_in_neg_bit_dec);

    let cmux_out = xprod_out.add(&current_acc_in);

    let cmux_or_exprod = if counter == F::from_canonical_usize(n + 2) {
        xprod_out
    } else {
        cmux_out
    };

    let current_acc_out = if counter == F::ONE {
        shifted_glwe
    } else {
        cmux_or_exprod
    };

    (current_acc_out, xprod_in_pos_bit_dec)
}

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
    xprod_in_bit_dec: [[[P; NUM_BITS]; N]; K],
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
    let xprod_out = ggsw_ct.eval_external_product::<LOGB>(
        yield_constr,
        non_pad_flag,
        &xprod_in,
        xprod_in_bit_dec,
    );
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
    xprod_in_bit_dec: [[[ExtensionTarget<D>; NUM_BITS]; N]; K],
    non_pad_flag: ExtensionTarget<D>,
    is_first_row: ExtensionTarget<D>,
    is_last_non_pad_row: ExtensionTarget<D>,
) -> GlweCtExp<N, K, ExtensionTarget<D>> {
    let neg_one = builder.neg_one_extension();
    let neg_mask = builder.mul_extension(neg_one, mask_element);
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
        non_pad_flag,
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

pub fn write_array<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    lv: &mut [F],
    cur_col: &mut usize,
    input: &[F; N],
) {
    lv[*cur_col..*cur_col + N].copy_from_slice(input);
    *cur_col += N;
}

pub fn read_array<F: Clone + fmt::Debug, const N: usize>(lv: &[F], cur_col: &mut usize) -> [F; N] {
    let output = lv[*cur_col..*cur_col + N].to_vec();
    *cur_col += N;
    output.try_into().unwrap()
}

/// N
pub fn write_glwe_poly<F: RichField + Extendable<D>, const D: usize, const N: usize>(
    lv: &mut [F],
    input: &GlwePolyNative<F, D, N>,
    cur_col: &mut usize,
) {
    let coeff = input.coeffs;
    lv[*cur_col..*cur_col + N].copy_from_slice(&coeff);
    *cur_col += N;
}

pub fn read_glwe_poly<F: Clone + fmt::Debug, const N: usize>(
    lv: &[F],
    cur_col: &mut usize,
) -> GlwePolyExp<N, F> {
    let coeffs: [F; N] = lv[*cur_col..*cur_col + N].to_vec().try_into().unwrap();
    *cur_col += N;

    GlwePolyExp { coeffs }
}

/// N * K
pub fn write_glwe_ct<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
>(
    lv: &mut [F],
    input: &GlweCtNative<F, D, N, K>,
    cur_col: &mut usize,
) {
    input
        .polys
        .iter()
        .for_each(|poly| write_glwe_poly(lv, &poly, cur_col));
}

pub fn read_glwe_ct<F: Clone + fmt::Debug, const N: usize, const K: usize>(
    lv: &[F],
    cur_col: &mut usize,
) -> GlweCtExp<N, K, F> {
    let polys: [GlwePolyExp<N, F>; K] = (0..K)
        .map(|_| read_glwe_poly(lv, cur_col))
        .collect_vec()
        .try_into()
        .unwrap();

    GlweCtExp { polys }
}

// K * N * ELL
pub fn write_glev_ct<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
    const ELL: usize,
>(
    lv: &mut [F],
    input: &GlevCtNative<F, D, N, K, ELL>,
    cur_col: &mut usize,
) {
    let _ = input
        .glwe_cts
        .iter()
        .for_each(|glwe_ct| write_glwe_ct(lv, glwe_ct, cur_col));
}

pub fn read_glev_ct<F: Clone + fmt::Debug, const N: usize, const K: usize, const ELL: usize>(
    lv: &[F],
    cur_col: &mut usize,
) -> GlevCtExp<N, K, ELL, F> {
    let glwe_cts: [GlweCtExp<N, K, F>; ELL] = (0..ELL)
        .map(|_| read_glwe_ct(lv, cur_col))
        .collect_vec()
        .try_into()
        .unwrap();

    GlevCtExp { glwe_cts }
}

//K * K * N * ELL
pub fn write_ggsw_ct<
    F: RichField + Extendable<D>,
    const D: usize,
    const N: usize,
    const K: usize,
    const ELL: usize,
>(
    lv: &mut [F],
    input: &GgswCtNative<F, D, N, K, ELL>,
    cur_col: &mut usize,
) {
    input
        .glev_cts
        .iter()
        .for_each(|glwe_ct| write_glev_ct(lv, &glwe_ct, cur_col));
}

pub fn read_ggsw_ct<F: Clone + fmt::Debug, const N: usize, const K: usize, const ELL: usize>(
    lv: &[F],
    cur_col: &mut usize,
) -> GgswCtExp<N, K, ELL, F> {
    let glev_cts: [GlevCtExp<N, K, ELL, F>; K] = (0..K)
        .map(|_| read_glev_ct(lv, cur_col))
        .collect_vec()
        .try_into()
        .unwrap();

    GgswCtExp { glev_cts }
}
