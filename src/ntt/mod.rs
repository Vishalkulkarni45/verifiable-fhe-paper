use plonky2::field::extension::Extendable;
use plonky2::field::packed::PackedField;
use plonky2::field::types::Field as PlonkyField;
use plonky2::hash::hash_types::RichField;
use plonky2::iop::ext_target::ExtensionTarget;
use plonky2::iop::target::Target;
use plonky2::plonk::circuit_builder::CircuitBuilder;

// use this path to set the ring dimension N (i.e. for N=512 set the path to "params_512.rs")
// make sure to adjust the value of circuit_size in line 57 of "ivc_based_vpbs.rs" if
// using a value other than 8 or 1024
#[path = "params_1024.rs"]
pub mod params;

fn ntt_fw_update<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    input: &Vec<Target>,
    m: usize,
) -> Vec<Target> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    for i in 0..m {
        let j1 = 2 * i * t;
        let j2 = j1 + t;
        let root = params::ROOTS[m + i];
        let s = cb.constant(F::from_canonical_u64(root));
        for j in j1..j2 {
            let u = a[j];
            let v = cb.mul(a[j + t], s);
            a[j] = cb.add(u, v);
            a[j + t] = cb.sub(u, v);
        }
    }
    a
}
fn ntt_fw_update_native<F: RichField + Extendable<D>, const D: usize>(
    input: &Vec<F>,
    m: usize,
) -> Vec<F> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    for i in 0..m {
        let j1 = 2 * i * t;
        let j2 = j1 + t;
        let root = params::ROOTS[m + i];
        let s = F::from_canonical_u64(root);
        for j in j1..j2 {
            let u = a[j];
            let v = a[j + t] * s;
            a[j] = u + v;
            a[j + t] = u - v;
        }
    }
    a
}

fn eval_ntt_fw_update<P: PackedField>(input: &Vec<P>, m: usize) -> Vec<P> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    for i in 0..m {
        let j1 = 2 * i * t;
        let j2 = j1 + t;
        let root = params::ROOTS[m + i];
        let s = P::from(P::Scalar::from_canonical_u64(root));
        for j in j1..j2 {
            let u = a[j];
            let v = a[j + t] * s;
            a[j] = u + v;
            a[j + t] = u - v;
        }
    }
    a
}

fn eval_ntt_fw_update_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input: &Vec<ExtensionTarget<D>>,
    m: usize,
) -> Vec<ExtensionTarget<D>> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    for i in 0..m {
        let j1 = 2 * i * t;
        let j2 = j1 + t;
        let root = params::ROOTS[m + i];
        let s = builder.constant_extension(F::Extension::from_canonical_u64(root));
        for j in j1..j2 {
            let u = a[j];
            let v = builder.mul_extension(a[j + t], s);
            a[j] = builder.add_extension(u, v);
            a[j + t] = builder.sub_extension(u, v);
        }
    }
    a
}

pub fn ntt_forward<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    input: &Vec<Target>,
) -> Vec<Target> {
    let mut current = input.clone();
    for m in (0..params::LOGN).map(|i| 2usize.pow(i)) {
        current = ntt_fw_update(cb, &current, m);
    }

    current
}

pub fn ntt_forward_native<F: RichField + Extendable<D>, const D: usize>(input: &Vec<F>) -> Vec<F> {
    let mut current = input.clone();
    for m in (0..params::LOGN).map(|i| 2usize.pow(i)) {
        current = ntt_fw_update_native(&current, m);
    }
    current
}

pub fn eval_ntt_forward<P: PackedField>(input: &Vec<P>) -> Vec<P> {
    let mut current = input.clone();
    for m in (0..params::LOGN).map(|i| 2usize.pow(i)) {
        current = eval_ntt_fw_update(&current, m);
    }

    current
}

pub fn eval_ntt_forward_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input: &Vec<ExtensionTarget<D>>,
) -> Vec<ExtensionTarget<D>> {
    let mut current = input.clone();
    for m in (0..params::LOGN).map(|i| 2usize.pow(i)) {
        current = eval_ntt_fw_update_ext(builder, &current, m);
    }

    current
}

fn ntt_bw_update<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    input: &Vec<Target>,
    m: usize,
) -> Vec<Target> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    let mut j1 = 0usize;
    for i in 0..m {
        let j2 = j1 + t;
        let root = params::INVROOTS[m + i];
        let s = cb.constant(F::from_canonical_u64(root));
        for j in j1..j2 {
            let u = a[j];
            let v = a[j + t];
            a[j] = cb.add(u, v);
            let w = cb.sub(u, v);
            a[j + t] = cb.mul(w, s);
        }
        j1 += 2 * t;
    }
    a
}
fn ntt_bw_update_native<F: RichField + Extendable<D>, const D: usize>(
    input: &Vec<F>,
    m: usize,
) -> Vec<F> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    let mut j1 = 0usize;
    for i in 0..m {
        let j2 = j1 + t;
        let root = params::INVROOTS[m + i];
        let s = F::from_canonical_u64(root);
        for j in j1..j2 {
            let u = a[j];
            let v = a[j + t];
            a[j] = u + v;
            let w = u - v;
            a[j + t] = w * s;
        }
        j1 += 2 * t;
    }
    a
}

pub fn eval_ntt_bw_update<P: PackedField>(input: &Vec<P>, m: usize) -> Vec<P> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    let mut j1 = 0usize;
    for i in 0..m {
        let j2 = j1 + t;
        let root = params::INVROOTS[m + i];
        let s = P::from(P::Scalar::from_canonical_u64(root));
        for j in j1..j2 {
            let u = a[j];
            let v = a[j + t];
            a[j] = u + v;
            let w = u - v;
            a[j + t] = w * s;
        }
        j1 += 2 * t;
    }
    a
}

pub fn eval_ntt_bw_update_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input: &Vec<ExtensionTarget<D>>,
    m: usize,
) -> Vec<ExtensionTarget<D>> {
    let mut a = input.clone();
    let t = params::N / (2 * m);
    let mut j1 = 0usize;
    for i in 0..m {
        let j2 = j1 + t;
        let root = params::INVROOTS[m + i];
        let s = builder.constant_extension(F::Extension::from_canonical_u64(root));
        for j in j1..j2 {
            let u = a[j];
            let v = a[j + t];
            a[j] = builder.add_extension(u, v);
            let w = builder.sub_extension(u, v);
            a[j + t] = builder.mul_extension(w, s);
        }
        j1 += 2 * t;
    }
    a
}

pub fn ntt_backward<F: RichField + Extendable<D>, const D: usize>(
    cb: &mut CircuitBuilder<F, D>,
    input: &Vec<Target>,
) -> Vec<Target> {
    let mut current = input.clone();
    for m in (0..params::LOGN).rev().map(|i| 2usize.pow(i)) {
        current = ntt_bw_update(cb, &current, m);
    }

    let n_inv = cb.constant(F::from_canonical_u64(params::NINV));
    current.into_iter().map(|g| cb.mul(g, n_inv)).collect()
}

pub fn ntt_backward_native<F: RichField + Extendable<D>, const D: usize>(input: &Vec<F>) -> Vec<F> {
    let mut current = input.clone();
    for m in (0..params::LOGN).rev().map(|i| 2usize.pow(i)) {
        current = ntt_bw_update_native(&current, m);
    }

    let n_inv = F::from_canonical_u64(params::NINV);
    current.into_iter().map(|g| g * n_inv).collect()
}

pub fn eval_ntt_backward<P: PackedField>(input: &Vec<P>) -> Vec<P> {
    let mut current = input.clone();
    for m in (0..params::LOGN).rev().map(|i| 2usize.pow(i)) {
        current = eval_ntt_bw_update(&current, m);
    }

    let n_inv = P::from(P::Scalar::from_canonical_u64(params::NINV));
    current.into_iter().map(|g| g * n_inv).collect()
}

pub fn eval_ntt_backward_ext<F: RichField + Extendable<D>, const D: usize>(
    builder: &mut CircuitBuilder<F, D>,
    input: &Vec<ExtensionTarget<D>>,
) -> Vec<ExtensionTarget<D>> {
    let mut current = input.clone();
    for m in (0..params::LOGN).rev().map(|i| 2usize.pow(i)) {
        current = eval_ntt_bw_update_ext(builder, &current, m);
    }

    let n_inv = builder.constant_extension(F::Extension::from_canonical_u64(params::NINV));
    current
        .into_iter()
        .map(|g| builder.mul_extension(g, n_inv))
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    use plonky2::field::types::Field;
    use plonky2::iop::witness::{PartialWitness, WitnessWrite};
    use plonky2::plonk::circuit_builder::CircuitBuilder;
    use plonky2::plonk::circuit_data::CircuitConfig;
    use plonky2::plonk::config::{GenericConfig, PoseidonGoldilocksConfig};

    #[test]
    fn test_ntt_forward() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let N = params::N;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x = builder.add_virtual_targets(N);

        let z = ntt_forward(&mut builder, &x);
        builder.register_public_inputs(&x);
        builder.register_public_inputs(&z);
        let mut pw = PartialWitness::new();
        pw.set_target_arr(&x, &params::TESTG.map(|g| F::from_canonical_u64(g)));

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        let out = &proof.public_inputs[N..2 * N];

        for (&actual, expected) in out.into_iter().zip(params::TESTGHAT) {
            assert_eq!(actual, F::from_canonical_u64(expected));
        }

        let _ = data.verify(proof).unwrap();
    }

    #[test]
    fn test_ntt_backward() {
        const D: usize = 2;
        type C = PoseidonGoldilocksConfig;
        type F = <C as GenericConfig<D>>::F;
        let N = params::N;

        let config = CircuitConfig::standard_recursion_config();
        let mut builder = CircuitBuilder::<F, D>::new(config);
        let x = builder.add_virtual_targets(N);

        let z = ntt_backward(&mut builder, &x);
        // Public inputs are the initial value (provided below) and the result (which is generated).
        builder.register_public_inputs(&x);
        builder.register_public_inputs(&z);
        let mut pw = PartialWitness::new();
        pw.set_target_arr(&x, &params::TESTGHAT.map(|g| F::from_canonical_u64(g)));

        let data = builder.build::<C>();
        let proof = data.prove(pw).unwrap();
        let out = &proof.public_inputs[N..2 * N];

        for (&actual, expected) in out.into_iter().zip(params::TESTG) {
            assert_eq!(actual, F::from_canonical_u64(expected));
        }

        let _ = data.verify(proof).unwrap();
    }
}
