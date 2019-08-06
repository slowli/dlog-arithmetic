use assert_matches::assert_matches;
use curve25519::{
    constants::ED25519_BASEPOINT_POINT, edwards::EdwardsPoint, scalar::Scalar, traits::Identity,
};
use ed25519::{PublicKey, Signature};
use rand::thread_rng;
use sha2::{Digest, Sha512};

use eccalc::{functions::*, Code, Context, Ed25519, EvalError, Value};

#[test]
fn eval_arithmetic() {
    //! Checks that the evaluation order of arithmetic operations is as expected:
    //! operations with the same priority are performed from left to right.

    let code = Code::new();
    let mut state = Context::new(Ed25519);
    let statements = code.add_statements("1 - 2 + 3 - 4".to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(-Scalar::from(2_u64)));

    let statements = code.add_statements("1 / 2 * 3 / 4".to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(
        result,
        Value::Scalar(Scalar::from(3_u64) * Scalar::from(8_u64).invert())
    );

    let statements = code.add_statements("1 / (2 * 3) / 4".to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(Scalar::from(24_u64).invert()));

    let statements = code.add_statements("1 + 2*3 - 4".to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(Scalar::from(3_u64)));
}

#[test]
fn eval_tuples() {
    let code = Code::new();
    let mut state = Context::new(Ed25519);
    state
        .innermost_scope()
        .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT));
    let statements = code
        .add_statements("(5 + 6/2) * (1/2, [3]G)".to_owned())
        .unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(
        result,
        Value::Tuple(vec![
            Value::Scalar(Scalar::from(4_u64)),
            Value::Element(ED25519_BASEPOINT_POINT * Scalar::from(24_u64)),
        ])
    );

    let statements = code
        .add_statements("(1/2, G) + (3, [4]G) / 2".to_owned())
        .unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(
        result,
        Value::Tuple(vec![
            Value::Scalar(Scalar::from(2_u64)),
            Value::Element(ED25519_BASEPOINT_POINT * Scalar::from(3_u64)),
        ])
    );

    let statements = code
        .add_statements("(X, _) = 5 * ([2]G, 2 + 3)".to_owned())
        .unwrap();
    state.evaluate(&statements).unwrap();
    assert_eq!(
        *state.get_var("X").unwrap(),
        Value::Element(ED25519_BASEPOINT_POINT * Scalar::from(10_u64))
    );
    assert!(state.get_var("_").is_none());
}

#[test]
fn partially_valid_assignment() {
    let code = Code::new();
    let mut state = Context::new(Ed25519);
    let statements = code
        .add_statements("(x, (y, z)) = (1, 2)".to_owned())
        .unwrap();
    assert!(state.evaluate(&statements).is_err());
    assert_eq!(
        *state.get_var("x").unwrap(),
        Value::Scalar(Scalar::from(1_u64))
    );
    assert!(state.get_var("y").is_none());
    assert!(state.get_var("z").is_none());
}

#[test]
fn scope_lookup() {
    let code = Code::new();
    let mut state = Context::new(Ed25519);
    state
        .innermost_scope()
        .insert_var("x", Value::Scalar(Scalar::from(1_u64)));
    state.create_scope();
    state
        .innermost_scope()
        .insert_var("x", Value::Scalar(Scalar::from(2_u64)));
    assert_eq!(
        *state.get_var("x").unwrap(),
        Value::Scalar(Scalar::from(2_u64))
    );

    let statements = code.add_statements("x + 3".to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(Scalar::from(5_u64)));
}

#[test]
fn block_creates_new_variable_space() {
    const PROGRAM: &str = r#"
        x = { x = 5; x + 2 };
        { y = 8; x * y }
    "#;
    let code = Code::new();
    let mut state = Context::new(Ed25519);

    let statements = code.add_statements(PROGRAM.to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(Scalar::from(56_u8)));
    assert_eq!(
        *state.get_var("x").unwrap(),
        Value::Scalar(Scalar::from(7_u64)),
    );
    assert!(state.get_var("y").is_none());
}

#[test]
fn block_as_function_arg() {
    const PROGRAM: &str = r#":sc_sha512({
        x = 10000;
        x * (1, G)
    }, 0x_abcdef)"#;
    let code = Code::new();
    let mut state = Context::new(Ed25519);
    state
        .innermost_scope()
        .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT))
        .insert_fn("sc_sha512", FromSha512);
    let statements = code.add_statements(PROGRAM.to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();

    let mut hash = Sha512::default();
    let x = Scalar::from(10_000_u64);
    hash.input(x.as_bytes());
    hash.input((ED25519_BASEPOINT_POINT * x).compress().as_bytes());
    hash.input(&[0xab, 0xcd, 0xef]);
    let expected_scalar = Scalar::from_hash(hash);
    assert_eq!(result, Value::Scalar(expected_scalar));
}

#[test]
fn function_basics() {
    const PROGRAM: &str = r#"
        fn foo(x, y) {
            x + y
        }
        :foo(3, 5)
    "#;
    let code = Code::new();
    let mut state = Context::new(Ed25519);
    let statements = code.add_statements(PROGRAM.to_owned()).unwrap();
    state
        .innermost_scope()
        .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT));
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(Scalar::from(8_u64)));

    let statements = code.add_statements(":foo([3]G, [7]G)".to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(
        result,
        Value::Element(ED25519_BASEPOINT_POINT * Scalar::from(10_u64))
    );
}

#[test]
fn function_capturing_vars() {
    const PROGRAM: &str = r#"
        x = 3;
        fn foo(y) { x + y }
        :foo(5)
    "#;
    let code = Code::new();
    let mut state = Context::new(Ed25519);
    let statements = code.add_statements(PROGRAM.to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(Scalar::from(8_u64)));

    // The captured variable should be copied into the scope.
    let statements = code.add_statements("x = 10; :foo(9)".to_owned()).unwrap();
    let result = state.evaluate(&statements).unwrap();
    assert_eq!(result, Value::Scalar(Scalar::from(12_u64)));
}

#[test]
fn function_capturing_functions() {
    const PROGRAM: &str = r#"
        fn keypair() { :sc_rand() * (1, G) }
        :keypair()
    "#;

    let code = Code::new();
    let mut state = Context::new(Ed25519);
    let statements = code.add_statements(PROGRAM.to_owned()).unwrap();
    state
        .innermost_scope()
        .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT))
        .insert_fn("sc_rand", Rand::new(thread_rng()));
    state.create_scope();
    let result = state.evaluate(&statements).unwrap();
    if let Value::Tuple(ref fragments) = result {
        if let [Value::Scalar(x), Value::Element(key)] = fragments[..] {
            assert_eq!(x * ED25519_BASEPOINT_POINT, key);
        } else {
            panic!("Unexpected return value: {:?}", result);
        }
    } else {
        panic!("Unexpected return value: {:?}", result);
    }

    const PROGRAM_WITH_REDEFINED_FN: &str = r#"
        fn foo(x) { 2 * x }
        fn bar() { :foo(25) }
        :bar() ?= 50;
        fn foo(x) { 3 * x }
        :bar() ?= 50; # `bar()` should capture first `foo()` definition.
    "#;
    state.pop_scope();
    state.create_scope();
    let statements = code
        .add_statements(PROGRAM_WITH_REDEFINED_FN.to_owned())
        .unwrap();
    assert!(state.evaluate(&statements).is_ok());
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
    let code = Code::new();
    let statements = code.add_statements(PROGRAM.to_owned()).unwrap();

    let mut state = Context::new(Ed25519);
    state
        .innermost_scope()
        .insert_fn("sc_rand", Rand::new(thread_rng()))
        .insert_fn("sc_sha512", FromSha512)
        .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT));
    state.create_scope();
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
fn ed25519_as_functions() {
    const FUNCTIONS: &str = r#"
        # Key generation
        fn gen() { :sc_rand() * (1, G) }

        # Signing
        fn sign(x, msg) {
            (r, R) = :gen();
            c = :sc_sha512(R, [x]G, msg);
            (R, r + c * x)
        }

        # Verification
        fn verify(K, (R, s), msg) {
            c = :sc_sha512(R, K, msg);
            [s]G ?= R + [c]K
        }
    "#;
    let code = Code::new();
    let statements = code.add_statements(FUNCTIONS.to_owned()).unwrap();

    let mut state = Context::new(Ed25519);
    state
        .innermost_scope()
        .insert_fn("sc_rand", Rand::new(thread_rng()))
        .insert_fn("sc_sha512", FromSha512)
        .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT));
    state.create_scope();
    assert!(state.evaluate(&statements).is_ok());

    const EVAL_PROGRAM: &str = r#"
        (x, K) = :gen();
        signature = :sign(x, m);
        :verify(K, signature, m);
    "#;
    let statements = code.add_statements(EVAL_PROGRAM.to_owned()).unwrap();
    for message in &[b"ABC" as &[_], b"message", b"!!!"] {
        state
            .innermost_scope()
            .insert_var("m", Value::Buffer(message.to_vec()));
        state.evaluate(&statements).unwrap();
    }
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
    let code = Code::new();
    let statements = code.add_statements(PROGRAM.to_owned()).unwrap();

    let mut state = Context::new(Ed25519);
    state
        .innermost_scope()
        .insert_fn("sc_rand", Rand::new(thread_rng()))
        .insert_fn("sc_sha512", FromSha512)
        .insert_var("O", Value::Element(EdwardsPoint::identity()))
        .insert_var("G", Value::Element(ED25519_BASEPOINT_POINT));
    state.create_scope();
    state.evaluate(&statements).unwrap();

    const PROGRAM_CONT: &str = r#"
        # If we change the encrypted value, the proof predictably fails to verify.
        m = 200;
        (R, E) = enc;
        c ?= :sc_sha512(K, R, E, [s]G - [c]R, [s]K - [c](E - [m]G))
    "#;
    let statements = code.add_statements(PROGRAM_CONT.to_owned()).unwrap();
    assert_matches!(
        state.evaluate(&statements).unwrap_err().extra,
        EvalError::AssertionFail
    );
}
