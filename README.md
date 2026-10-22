# AES mixing in Lean

This repository formalizes

$$
\varepsilon_{8+2k}<7\,2^{-95-41k}\qquad(k\in\mathbb N),
$$

its 10/14/16-round corollaries, and the adaptive two-forward-query consequence.
Here `epsilon` measures the largest total-variation distance for distinct
plaintext pairs from a uniformly random ordered pair of distinct ciphertexts.
The model uses independent uniform round keys, sampled once and reused across
evaluations, initial whitening, and omitted final MixColumns. The standard AES
key schedule is outside this model.

The main declaration is
[`AES8.PaperAESFromCompleteEntries.epsilon_eight_plus_two`](AES8/Consequences/PaperAESFromCompleteEntries.lean).
The full proof and a replay of retained proof artifacts were checked using only
`propext`, `Classical.choice`, and `Quot.sound`, with no external AES entry-bound
premise. The finite certificates prove the sufficient entry inequalities used
here; they do not prove Keliher–Sui's exact maxima or reproduce its internal proof.

## Generate and check

Git contains the proof library, shared checker sources, and a compact generator.
The approximately **7.43 GB** of generated Lean certificate sources are ignored
by Git. Generate them locally with Python 3.6+ and a C++11 GCC or Clang compiler
supporting `__int128`:

```sh
git clone https://github.com/chongxuren/aes-mixing-lean.git
cd aes-mixing-lean
python3 generators/generate.py --jobs 8
```

Choose `--jobs` for the available machine; the default is one worker.
Generation verifies source hashes. **Lean proof checking is a separate step.**
The generator was tested on all 69,913 certificate modules: every file matched
the accepted proof sources byte for byte.
See [GENERATING.md](GENERATING.md) for dependencies, resuming interrupted work,
partial generation, the Linux runtime helper, and the complete build and audit
commands. Lean `v4.32.2` and Mathlib revision
`905b95818eb32af7874a58b427f50c1711a5e96c` are pinned.

The full theorem was previously checked on 64-bit Linux with glibc. A complete
clean build of this combined repository layout has not been validated.

## Source layout

- [`AES8/`](AES8/): the `8 + 2*k` theorem, paper lemmas, and adaptive consequence,
  including stopping, repeated queries, and independent finite private randomness.
- [`AESMixingProof.lean`](AESMixingProof.lean): the earlier `14.3 + 73.1k` bound.
- `AESMixing/`, `AESConcrete/`, `AESPaper/`, `AESRound/`: shared mathematical
  foundations, the AES model, concrete estimates, and recurrence bounds.
- [`generators/`](generators/): deterministic finite-certificate generation.
- [`checks/Endpoint.lean`](checks/Endpoint.lean): final theorem and axiom checks.

After installing [elan](https://github.com/leanprover/elan), a smaller independent
check is:

```sh
lake exe cache get
lake build +AES8.Math.PaperWeightedSchur
```
