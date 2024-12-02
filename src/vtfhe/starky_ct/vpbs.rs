//| cur_acc_in |      ggsw_ct     | mask_ele | mask_ele_bit_dec |   xprod_in_bit_dec  | non_pad_flag | is_first_row | is_last_non_pad_row |
//|    N * K   |  K * K * N * ELL |     1    |     NUM_BITS     |   NUM_BITS * N * K  |       1      |       1      |          1          |
//|    GLWE    |       GGSW       |
use crate::{
    ntt::params::N,
    vtfhe::{
        crypto::{compute_bsk, ggsw::Ggsw, glwe::Glwe, lwe::encrypt, poly::Poly},
        starky_ct::{
            generate_build_circuit_input, ggsw_ct::GgswCtNative, glwe_ct::GlweCtNative,
            glwe_poly::le_sum_native,
        },
        NUM_BITS,
    },
};
use std::{array::from_fn, marker::PhantomData, time::Instant};

use itertools::Itertools;
use plonky2::field::types::{Field, PrimeField64};
use plonky2::{
    field::{
        extension::{Extendable, FieldExtension},
        packed::PackedField,
        polynomial::PolynomialValues,
    },
    hash::hash_types::RichField,
    iop::ext_target::ExtensionTarget,
    plonk::{
        circuit_builder::CircuitBuilder,
        config::{GenericConfig, PoseidonGoldilocksConfig},
    },
    util::{log2_ceil, timing::TimingTree, transpose},
};

use rand::random;
use starky::{
    config::StarkConfig,
    constraint_consumer::{ConstraintConsumer, RecursiveConstraintConsumer},
    evaluation_frame::{StarkEvaluationFrame, StarkFrame},
    prover::prove,
    stark::Stark,
    stark_testing::test_stark_circuit_constraints,
    verifier::verify_stark_proof,
};

use super::{
    eval_step_circuit, eval_step_circuit_ext, glwe_ct::decimal_to_binary, read_array, read_ggsw_ct,
    read_glwe_ct, write_array, write_ggsw_ct, write_glwe_ct,
};

const LOGB: usize = 8;
const ELL: usize = 8;
const K: usize = 2;
const D: usize = 2;
const n: usize = 4;

const VPBS_COLUMNS: usize = N * K + K * K * N * ELL + 1 + NUM_BITS + NUM_BITS * N * K + 3 * 1;
const VPBS_PUBLIC_INPUT: usize = 0;

#[derive(Clone, Copy)]
pub struct VpbsStark<F: RichField + Extendable<D>, const D: usize> {
    _phantom: PhantomData<F>,
}

impl<F: RichField + Extendable<D>, const D: usize> VpbsStark<F, D> {
    pub fn fill_row(
        &self,
        lv: &mut [F],
        cur_col: &mut usize,
        cur_acc_in: &GlweCtNative<F, D, N, K>,
        ggsw_ct: &GgswCtNative<F, D, N, K, ELL>,
        mask_ele: F,
        xprod_in_bit_dec: &[[[F; NUM_BITS]; N]; K],
        counter: F,
    ) {
        write_glwe_ct(lv, cur_acc_in, cur_col);
        assert_eq!(*cur_col, N * K);

        write_ggsw_ct(lv, ggsw_ct, cur_col);

        assert_eq!(*cur_col, N * K + K * K * N * ELL);

        lv[*cur_col] = mask_ele;
        *cur_col += 1;

        let neg_first_mask = if counter == F::ONE {
            -mask_ele
        } else {
            mask_ele
        };

        let mask_bit_dec = decimal_to_binary::<F, D>(neg_first_mask.to_canonical_u64());

        write_array(lv, cur_col, &mask_bit_dec);

        assert_eq!(*cur_col, N * K + K * K * N * ELL + 1 + NUM_BITS);

        for poly in xprod_in_bit_dec {
            for coeff_bit in poly {
                write_array(lv, cur_col, coeff_bit);
            }
        }
    }

    fn generate_trace(&self) -> Vec<PolynomialValues<F>> {
        let mut lv = vec![F::ZERO; VPBS_COLUMNS];

        let mut num_rows = 1 << (64 - ((n + 2) - 1).leading_zeros());
        if num_rows < 8 {
            num_rows = 8;
        }

        let mut trace_rows = Vec::<Vec<F>>::new();

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

        let mut cur_col = 0;

        let coeffs = vec![F::ZERO; N * (K - 1)]
            .into_iter()
            .chain(testv.coeffs.into_iter())
            .collect_vec();
        let mut current_acc_in = GlweCtNative::new_from_slice(&coeffs);

        let mut prev_acc_in = current_acc_in;
        let dummy_ggsw_ct = GgswCtNative::<F, D, N, K, ELL>::dummy_ct();
        let mut xprod_in_bit_dec = [[[F::ZERO; 64]; N]; K];

        (current_acc_in, xprod_in_bit_dec) = generate_build_circuit_input::<F, D, n, N, K, ELL, LOGB>(
            &prev_acc_in,
            &dummy_ggsw_ct,
            ct[n],
            F::ONE,
        );

        //Fill 1st row
        self.fill_row(
            &mut lv,
            &mut cur_col,
            &prev_acc_in,
            &dummy_ggsw_ct,
            ct[n],
            &xprod_in_bit_dec,
            F::ONE,
        );

        //non_pad_flag
        lv[cur_col] = F::ONE;
        cur_col += 1;
        //is_first_row
        lv[cur_col] = F::ONE;
        cur_col += 1;
        //is_last_non_pad_row
        lv[cur_col] = F::ZERO;
        cur_col += 1;
        assert_eq!(cur_col, VPBS_COLUMNS);

        trace_rows.push(lv);

        prev_acc_in = current_acc_in.clone();

        for x in 0..n {
            let mut lv = vec![F::ZERO; VPBS_COLUMNS];
            cur_col = 0;

            let counter = F::from_canonical_usize(x + 2);

            let ggsw_ct = GgswCtNative::from_ggsw(&bsk[x]);
            (current_acc_in, xprod_in_bit_dec) =
                generate_build_circuit_input::<F, D, n, N, K, ELL, LOGB>(
                    &prev_acc_in,
                    &ggsw_ct,
                    ct[x],
                    counter,
                );

            self.fill_row(
                &mut lv,
                &mut cur_col,
                &prev_acc_in,
                &ggsw_ct,
                ct[x],
                &xprod_in_bit_dec,
                counter,
            );

            //non_pad_flag
            lv[cur_col] = F::ONE;
            cur_col += 1;
            //is_first_row
            lv[cur_col] = F::ZERO;
            cur_col += 1;
            //is_last_non_pad_row
            lv[cur_col] = F::ZERO;
            cur_col += 1;
            assert_eq!(cur_col, VPBS_COLUMNS);

            trace_rows.push(lv);

            prev_acc_in = current_acc_in.clone();
        }

        let ksk_native = GgswCtNative::from_ggsw(&ksk);

        let counter = F::from_canonical_usize(n + 2);
        (current_acc_in, xprod_in_bit_dec) = generate_build_circuit_input::<F, D, n, N, K, ELL, LOGB>(
            &prev_acc_in,
            &ksk_native,
            F::ZERO,
            counter,
        );

        let mut lv = vec![F::ZERO; VPBS_COLUMNS];
        cur_col = 0;

        self.fill_row(
            &mut lv,
            &mut cur_col,
            &prev_acc_in,
            &ksk_native,
            F::ZERO,
            &xprod_in_bit_dec,
            counter,
        );

        //non_pad_flag
        lv[cur_col] = F::ONE;
        cur_col += 1;
        //is_first_row
        lv[cur_col] = F::ZERO;
        cur_col += 1;
        //is_last_non_pad_row
        lv[cur_col] = F::ONE;
        cur_col += 1;

        assert_eq!(cur_col, VPBS_COLUMNS);

        trace_rows.push(lv);

        assert_eq!(trace_rows.len(), n + 2);

        for _ in trace_rows.len()..num_rows {
            let lv = vec![F::ZERO; VPBS_COLUMNS];
            trace_rows.push(lv);
        }

        for i in 0..num_rows {
            let mut col = 0;

            let lv = &trace_rows[i];

            let current_acc_in = read_glwe_ct::<F, N, K>(lv, &mut col);
            let ggsw_ct = read_ggsw_ct::<F, N, K, ELL>(lv, &mut col);

            let mask_element = lv[col];
            col += 1;

            let mask_ele_bit_dec = read_array::<F, NUM_BITS>(lv, &mut col);

            let clone_mask_ele = if i == 0 {
                -mask_element.clone()
            } else {
                mask_element
            };

            let trace_xprod_in_bit_dec: [[[F; NUM_BITS]; N]; K] =
                from_fn(|_| from_fn(|_| read_array::<F, NUM_BITS>(lv, &mut col)));

            for i in 0..K {
                for j in 0..N {
                    trace_xprod_in_bit_dec[i][j].into_iter().for_each(|bit| {
                        assert_eq!(bit * bit - bit, F::ZERO);
                    });
                }
            }

            let check_mask = le_sum_native(mask_ele_bit_dec.to_vec());

            let non_pad_flag = lv[col];
            col += 1;

            let is_first_row = lv[col];
            col += 1;

            let is_last_non_pad_row = lv[col];

            let constr = non_pad_flag * (check_mask - clone_mask_ele);
            assert!(constr == F::ZERO, "fail at row {} ", i);
        }

        let trace_cols = transpose(&trace_rows.iter().map(|v| v.to_vec()).collect_vec());

        println!("non_pad_flag {:?}", trace_cols[VPBS_COLUMNS - 3]);
        println!("is_first_row {:?}", trace_cols[VPBS_COLUMNS - 2]);
        println!("is_last_non_pad_row {:?}", trace_cols[VPBS_COLUMNS - 1]);

        trace_cols
            .into_iter()
            .map(|column| PolynomialValues::new(column))
            .collect()
    }

    fn generate_public_inputs(&self) {}
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
        let lv = vars.get_local_values();
        let mut cur_col = 0;

        let current_acc_in = read_glwe_ct(lv, &mut cur_col);
        let ggsw_ct = read_ggsw_ct(lv, &mut cur_col);
        let mask_element = lv[cur_col];
        cur_col += 1;

        let mask_ele_bit_dec = read_array(lv, &mut cur_col);

        let xprod_in_bit_dec: [[[P; NUM_BITS]; N]; K] =
            from_fn(|_| from_fn(|_| read_array::<P, NUM_BITS>(lv, &mut cur_col)));

        let non_pad_flag = lv[cur_col];
        cur_col += 1;

        let is_first_row = lv[cur_col];
        cur_col += 1;

        let is_last_non_pad_row = lv[cur_col];

        assert_eq!(cur_col + 1, VPBS_COLUMNS);

        let exp_cipher = eval_step_circuit::<P, N, K, ELL, LOGB>(
            yield_constr,
            current_acc_in,
            ggsw_ct,
            mask_element,
            mask_ele_bit_dec,
            xprod_in_bit_dec,
            non_pad_flag,
            is_first_row,
            is_last_non_pad_row,
        );
    }

    fn eval_ext_circuit(
        &self,
        builder: &mut CircuitBuilder<F, D>,
        vars: &Self::EvaluationFrameTarget,
        yield_constr: &mut RecursiveConstraintConsumer<F, D>,
    ) {
        let lv = vars.get_local_values();
        let mut cur_col = 0;

        let current_acc_in = read_glwe_ct(lv, &mut cur_col);
        let ggsw_ct = read_ggsw_ct(lv, &mut cur_col);
        let mask_element = lv[cur_col];
        cur_col += 1;

        let mask_ele_bit_dec = read_array(lv, &mut cur_col);

        let xprod_in_bit_dec: [[[ExtensionTarget<D>; NUM_BITS]; N]; K] =
            from_fn(|_| from_fn(|_| read_array::<ExtensionTarget<D>, NUM_BITS>(lv, &mut cur_col)));

        let non_pad_flag = lv[cur_col];
        cur_col += 1;

        let is_first_row = lv[cur_col];
        cur_col += 1;

        let is_last_non_pad_row = lv[cur_col];

        assert_eq!(cur_col + 1, VPBS_COLUMNS);

        eval_step_circuit_ext::<F, D, N, K, ELL, LOGB>(
            builder,
            yield_constr,
            current_acc_in,
            ggsw_ct,
            mask_element,
            mask_ele_bit_dec,
            xprod_in_bit_dec,
            non_pad_flag,
            is_first_row,
            is_last_non_pad_row,
        );
    }

    fn constraint_degree(&self) -> usize {
        7
    }
}

#[test]

fn test_vpbs() {
    const D: usize = 2;
    type C = PoseidonGoldilocksConfig;
    type F = <C as GenericConfig<D>>::F;
    type S = VpbsStark<F, D>;
    let stark = VpbsStark::<F, D> {
        _phantom: PhantomData,
    };

    let mut config = StarkConfig::standard_fast_config();
    config.fri_config.rate_bits = 4;
    println!("start stark proof generation");
    let now = Instant::now();
    let trace = stark.generate_trace();
    let inner_proof =
        prove::<F, C, S, D>(stark, &config, trace, &[], &mut TimingTree::default()).unwrap();
    verify_stark_proof(stark, inner_proof.clone(), &config).unwrap();
    println!("end stark proof generation: {:?}", now.elapsed());
}
