# AES mixing in Lean

These formalizations use independent uniform AES round keys, sampled once and
reused across evaluations, with initial whitening and omitted final MixColumns.
They do not cover the standard AES key schedule.

- `AESMixingProof.lean`: the original `14.3 + 73.1k` mixing bound.
- `AES8/`: the bound `epsilon(8 + 2*k) < 7 / 2^(95 + 41*k)`, its
  10/14/16-round corollaries, and the adaptive two-forward-query consequence.
- `AESMixing/`, `AESConcrete/`, `AESPaper/`, `AESRound/`: shared mathematical
  foundations, concrete AES estimates, and recurrence bounds.

The new main declaration is
`AES8.PaperAESFromCompleteEntries.epsilon_eight_plus_two`, in
`AES8/Consequences/PaperAESFromCompleteEntries.lean`. Its complete proof and
retained-artifact replay were checked using only `propext`, `Classical.choice`,
and `Quot.sound`.

**Source scope:** this compact update omits the large generated finite-certificate
Lean sources for the new theorem. Rebuilding its unconditional endpoint requires
those omitted sources; this checkout alone is insufficient. The earlier theorem's
sources remain included. No complete rebuild of this compact layout is claimed.

Lean and Mathlib versions are pinned by the existing Lake configuration. After
installing [elan](https://github.com/leanprover/elan), build the earlier theorem:

```sh
lake exe cache get
lake build AESMixingProof
```

Individual new modules without the omitted dependencies can be checked separately,
for example `lake build +AES8.Math.PaperWeightedSchur`.
