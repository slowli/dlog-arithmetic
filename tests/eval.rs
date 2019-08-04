use assert_matches::assert_matches;
use curve25519::{
    constants::ED25519_BASEPOINT_POINT, edwards::EdwardsPoint, scalar::Scalar, traits::Identity,
};
use ed25519::{PublicKey, Signature};
use rand::thread_rng;

use eccalc::{functions::*, parser::Statement, Ed25519, EvalError, Scope, Value};

#[test]
fn eval_arithmetic() {
    //! Checks that the evaluation order of arithmetic operations is as expected:
    //! operations with the same priority are performed from left to right.

    let mut state = Scope::new(Ed25519);
    let statements = Statement::list_from_str("1 - 2 + 3 - 4").unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(-Scalar::from(2_u64)));

    let statements = Statement::list_from_str("1 / 2 * 3 / 4").unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(
        result,
        Value::Scalar(Scalar::from(3_u64) * Scalar::from(8_u64).invert())
    );

    let statements = Statement::list_from_str("1 / (2 * 3) / 4").unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(Scalar::from(24_u64).invert()));

    let statements = Statement::list_from_str("1 + 2*3 - 4").unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(Scalar::from(3_u64)));
}

#[test]
fn eval_tuples() {
    let mut state = Scope::new(Ed25519);
    state.insert_constant("G", Value::Element(ED25519_BASEPOINT_POINT));
    let statements = Statement::list_from_str("(5 + 6/2) * (1/2, [3]G)").unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(
        result,
        Value::Tuple(vec![
            Value::Scalar(Scalar::from(4_u64)),
            Value::Element(ED25519_BASEPOINT_POINT * Scalar::from(24_u64)),
        ])
    );

    let statements = Statement::list_from_str("(1/2, G) + (3, [4]G) / 2").unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(
        result,
        Value::Tuple(vec![
            Value::Scalar(Scalar::from(2_u64)),
            Value::Element(ED25519_BASEPOINT_POINT * Scalar::from(3_u64)),
        ])
    );

    let statements = Statement::list_from_str("(X, _) = 5 * ([2]G, 2 + 3)").unwrap();
    state.evaluate(&statements).unwrap();
    assert_eq!(
        *state.get_var("X").unwrap(),
        Value::Element(ED25519_BASEPOINT_POINT * Scalar::from(10_u64))
    );
    assert!(state.get_var("_").is_none());
}

#[test]
fn partially_valid_assignment() {
    let mut state = Scope::new(Ed25519);
    let statements = Statement::list_from_str("(x, (y, z)) = (1, 2)").unwrap();
    assert!(state.evaluate(&statements).is_err());
    assert_eq!(
        *state.get_var("x").unwrap(),
        Value::Scalar(Scalar::from(1_u64))
    );
    assert!(state.get_var("y").is_none());
    assert!(state.get_var("z").is_none());
}

#[test]
fn eval_ed25519() {
    const PROGRAM: &str = r#"
        x = :sc_rand(); A = [x]G; # Keypair

        # Schnorr signature generation
        r = :sc_rand(); R = [r]G;
        c = :sc_sha512(R, A, 0x414243); # 0x414243 is hex-encoded b"ABC"
        s = r + c * x;
        # (R, s) is the signature

        # Verification
        [s]G ?= R + [c]A
    "#;
    let statements = Statement::list_from_str(PROGRAM).unwrap();

    let mut state = Scope::new(Ed25519);
    state
        .insert_fn("sc_rand", Rand(thread_rng()))
        .insert_fn("sc_sha512", FromSha512)
        .insert_constant("G", Value::Element(ED25519_BASEPOINT_POINT));
    state.evaluate(&statements).unwrap();

    let public_key = state.get_var("A").unwrap().as_element().unwrap();
    let public_key = PublicKey::from_bytes(public_key.compress().as_bytes()).unwrap();

    let signature_r = state.get_var("R").unwrap().as_element().unwrap();
    let signature_s = state.get_var("s").unwrap().as_scalar().unwrap();
    let mut signature = [0_u8; 64];
    signature[..32].copy_from_slice(signature_r.compress().as_bytes());
    signature[32..].copy_from_slice(signature_s.as_bytes());
    let signature = Signature::from_bytes(&signature[..]).unwrap();
    assert!(public_key.verify(b"ABC", &signature).is_ok());
}

#[test]
fn eval_ed25519_chaum_pedersen_proof() {
    //! Chaum - Pedersen proof of equality of 2 discrete logs in different bases.
    //! Here, we use it to prove an ElGamal-encrypted value.

    const PROGRAM: &str = r#"
        K = [:sc_rand()]G; # Public encryption key

        m = 100; # Encrypted value
        r = :sc_rand();
        enc = r * (G, K) + (O, [m]G);
        # enc is the ElGamal encryption of m

        x = :sc_rand();
        c = :sc_sha512(K, enc, [x]G, [x]K);
        # Not committing to the encryption can lead to vulnerabilities, see
        # https://people.eng.unimelb.edu.au/vjteague/HowNotToProveElectionOutcome.pdf
        s = x + c * r;
        # `(c, s)` is the proof that `enc` decrypts to `m`

        # Verification
        powers = s * (G, K) - c * (enc - (O, [m]G));
        c ?= :sc_sha512(K, enc, powers)
    "#;
    let statements = Statement::list_from_str(PROGRAM).unwrap();

    let mut state = Scope::new(Ed25519);
    state
        .insert_fn("sc_rand", Rand(thread_rng()))
        .insert_fn("sc_sha512", FromSha512)
        .insert_constant("O", Value::Element(EdwardsPoint::identity()))
        .insert_constant("G", Value::Element(ED25519_BASEPOINT_POINT));
    state.evaluate(&statements).unwrap();

    const PROGRAM_CONT: &str = r#"
        # If we change the encrypted value, the proof predictably fails to verify.
        m = 200;
        (R, E) = enc;
        c ?= :sc_sha512(K, R, E, [s]G - [c]R, [s]K - [c](E - [m]G))
    "#;
    let statements = Statement::list_from_str(PROGRAM_CONT).unwrap();
    assert_matches!(
        state.evaluate(&statements).unwrap_err().extra,
        EvalError::AssertionFail
    );
}
