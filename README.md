# AES mixing: 14.3 + 73.1k

A Lean proof of the following strict bounds for every natural `k` and `r >= 4 + 4*k`:

```
epsilon(r) < (2^(-12)/5) * (2^(-64)/560)^k < 2^(-14.3 - 73.1*k).
```

The decimal exponents denote the exact rationals `143/10` and `731/10`.
The sufficient round counts for `2^-128`, `2^-192`, and `2^-256` are 12, 16, and 20.

## Model and entry points

`AESMixing.AES.encrypt` uses the concrete AES byte operations, initial whitening,
and a final round without MixColumns. Its round keys are independent uniform
128-bit states, sampled once and retained across evaluations. This is the
independent-round-key model; it does not use the standard AES key schedule.
`AESMixing.AES.epsilon` is the maximum half-l1 total variation distance over
ordered distinct plaintext pairs from the uniform ordered-distinct output law.

Import `AESMixingProof`:

- `AESMixingProof.pair_mixing`: the complete bound above, with no analytic premise.
- `AESMixingProof.rounds_128`, `rounds_192`, `rounds_256`: the round corollaries.
- `AESPaper.FullPermutationOutput.output_tv_bound`: finite stopped programs using
  zero, one, or two adaptive classical forward queries, including repeats,
  against one uniformly sampled and retained full permutation. The private seed
  (randomness and prior information) is finite and independent of the oracle;
  the output type is finite.
- `AESPaper.FullPermutationOutput.postprocessed_tv_bound`: further finite
  deterministic postprocessing.

Intermediate modules expose reusable conditional interfaces. The final theorem
instantiates their initialization, operator, and physical-law requirements.

## Build

Install [elan](https://github.com/leanprover/elan), Git, and the usual Lean system
prerequisites. From this directory:

```sh
lake exe cache get
lake build
lake env lean Audit.lean
```

`lean-toolchain` pins Lean 4.32.2; the Lake files pin Mathlib and all its package
revisions. Internet access is needed for the first dependency/toolchain setup.
All project-specific Lean sources, including the generated finite rank
certificates, are included. No other research checkout, private cache, external
certificate archive, absolute workspace path, or prebuilt project object is
required. The standard Lean/Mathlib dependencies are installed separately by Lake.

`AESMixing/` contains the finite AES and analytic foundation; `AESConcrete/`
contains concrete word estimates; `AESPaper/` contains the fixed mixing proof and
its query/output consequences. `AESMixingProof.lean` is the public entry point.
