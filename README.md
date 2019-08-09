# Arithmetic interpreter for discrete log crypto

Here lies a Rust interpreter of arithmetic expressions in finite [cyclic groups] in which
the [discrete logarithm problem][dlog] is believed to be hard. Such groups
are extensively used in cryptography; for example, they form the basis of
[ElGamal][elgamal-sig] and [elliptic curve] signature systems,
[ElGamal encryption] system, various [zero-knowledge proofs],
and higher-level protocols (such as [transparent e-voting][benaloh]).

The arithmetic expression language used in the interpreter allows
to succinctly describe and tinker with cryptographic protocols.

## Why?

- Resulting protocol expressions are group-independent (if literals are not involved)
  and require little cognitive overhead.
- Writing interpreters is fun.

## Interpreter features

- [x] Functions and Rust-style blocks
- [x] Capturing of vars / functions by functions
- [ ] [Hindley-Milner type inference](https://en.wikipedia.org/wiki/Hindley%E2%80%93Milner_type_system)
- [ ] Support of toy groups (prime-order subgroup of the multiplicative group of integers modulo `p`,
      where `p` is a safe prime)
- [ ] Web app (via a WASM module)

[cyclic groups]: http://mathworld.wolfram.com/CyclicGroup.html
[dlog]: https://en.wikipedia.org/wiki/Discrete_logarithm
[elgamal-sig]: http://cacr.uwaterloo.ca/hac/about/chap11.pdf
[elliptic-curve]: https://en.wikipedia.org/wiki/Elliptic-curve_cryptography
[ElGamal encryption]: http://cacr.uwaterloo.ca/hac/about/chap8.pdf
[zero-knowledge proofs]: http://pages.cs.wisc.edu/~mkowalcz/628.pdf
[benaloh]: http://static.usenix.org/event/evt06/tech/full_papers/benaloh/benaloh.pdf
