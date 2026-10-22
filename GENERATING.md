# Regenerating and checking the Lean proof

Run the commands below from the repository root. Source generation, source
identity verification, and Lean proof checking are separate operations.

## Requirements

For certificate generation, install Python **3.6 or later** and a GCC or Clang
C++ compiler supporting **C++11 and `__int128`**. Python uses only its standard
library. The generator compiles its C++ arithmetic helper with `-std=c++11 -O2`;
no additional Python packages or OpenMP runtime are required.

For Lean, install Git, [elan](https://github.com/leanprover/elan), and the usual
Lean system prerequisites. The repository pins:

- Lean: `leanprover/lean4:v4.32.2` in `lean-toolchain`.
- Mathlib: `905b95818eb32af7874a58b427f50c1711a5e96c` in `lakefile.toml` and
  `lake-manifest.json`.

Keep these files unchanged when reproducing the proof. Obtain the pinned
dependency cache with:

```sh
lake exe cache get
```

The complete finite import was checked on **64-bit Linux with glibc** using the
included runtime helper. Its build requires a C11 compiler and glibc headers;
the command below uses GCC. Full proof checking on other operating systems or
allocators has not been validated.

Allow approximately **7.43 GB** for generated Lean source files. Previously
checked project objects occupied approximately **40.6 GB**, in addition to source
files, dependency caches, and further build outputs. These are storage figures;
they do not establish a minimum physical-memory requirement or clean-build wall
time. Each active generator worker also uses temporary storage for its row data.
The temporary directory selected by Python, including `TMPDIR` when set, must
have enough free space and allow execution of the compiled helper. The output
filesystem must support hard links, which install each source without replacing
an existing file.

## Generate the certificate sources

```sh
python3 generators/generate.py --jobs 8
```

`--jobs` selects the maximum number of independent row workers. Its default is
one; choose a value supported by the machine's CPU, memory, and storage. The
generator processes the 255 nonzero input rows, with 255 entries per row, and
emits the Lean sources and assembly modules. It checks their sizes and SHA-256
identities against `generators/expected.json`.

The complete certificate collection has **69,913 Lean modules**: 280 shared
modules already tracked in Git and 69,633 generated modules. The latter are
ignored by `.gitignore`; they are created in `AES8/Estimates/Word/`.

Use another compatible compiler through `--cxx` or `CXX`:

```sh
python3 generators/generate.py --jobs 8 --cxx clang++
```

The compiler argument is an executable name or path, rather than a shell command
containing flags. The temporary compiled helper is removed after the run.

For a limited generation, supply comma-separated row numbers from 1 through 255:

```sh
python3 generators/generate.py --rows 1,13,255 --jobs 3
```

Every generation also emits the complete-inventory assembly modules. A partial
run leaves their other row imports missing; it cannot support the full theorem.
Run without `--rows` to finish all rows. Row 13 retains the original unpadded
`PaperSharpEntriesPairB1` through `PaperSharpEntriesPairB255` names; the other rows
use names such as `PaperSharpEntriesPairA001B001`.

`--output PATH` selects a different project root. That root must already contain
the tracked shared checker sources; this option does not copy the proof library.
The default is the checkout containing `generators/generate.py`.

## Resume or verify existing sources

Run the same generation command after an interruption. Complete rows whose
identities match are verified and skipped. An incomplete row is regenerated;
already present identical files are kept. Each new source is installed
atomically. The generator refuses to overwrite a file with different contents
and refuses symlink destinations when writing.

If a conflict is reported, preserve any edits you need and restore or remove the
identified conflicting file before rerunning. There is no force-overwrite option.
An interrupted run may leave an unused `.aes8-source-*` temporary file beside
its destination; only remove such temporary files after generation has stopped.

To verify existing sources without compiling the C++ helper or generating files:

```sh
python3 generators/generate.py --verify-only
```

With `--rows`, this checks the shared sources, the selected rows, and the
complete-inventory assembly modules:

```sh
python3 generators/generate.py --verify-only --rows 1,13,255
```

Missing or changed files cause verification to fail. The expected group hashes
bind each source path, byte length, and SHA-256 digest in sorted order.
**Matching these hashes checks source identity, not mathematical validity.**
Neither successful generation nor `--verify-only` runs Lean or replaces the
proof checks below.

## Build and check the full theorem

First complete source generation and fetch the pinned Mathlib cache. On 64-bit
Linux with glibc, build the runtime helper:

```sh
gcc -std=c11 -O2 -fPIC -shared -fno-builtin-malloc -fno-builtin-free \
  -Wall -Wextra -Werror -o runtime/heap_reserve.so runtime/heap_reserve.c
```

The launcher applies the allocator settings used for the large finite import.
For Lean processes, the helper reserves and frees 24 GiB of address space in the
glibc main heap and checks that it remains available to that heap. It does not
override allocator or loader symbols. Failure to obtain this layout stops the
process with an `AES8_HEAP_RESERVE_FAIL` diagnostic.

Build the theorem library, audit its axioms, inspect the theorem interfaces, and
run the final endpoint check:

```sh
sh runtime/with_heap_reserve.sh lake build AES8 +AES8.Audit +AES8.CheckInterfaces
sh runtime/with_heap_reserve.sh lake env lean -j1 -DElab.async=false \
  -DmaxHeartbeats=4000000 checks/Endpoint.lean
```

`AES8.Audit` checks declaration axioms. `AES8.CheckInterfaces` prints theorem
hypotheses. `checks/Endpoint.lean` checks the final mixing theorem, the round-count
and adaptive consequences, and the audited declarations together. Check command
exit statuses and diagnostics; successful source generation alone is insufficient.

The library configuration uses one Lean task thread and synchronous declaration
elaboration per compiler process. Lake can build independent modules in parallel;
the generator's `--jobs` setting does not configure Lake's parallelism.

The main declaration is
`AES8.PaperAESFromCompleteEntries.epsilon_eight_plus_two`. It states
`AES.epsilon (8+2*k) < 7 / (2 : ℝ)^(95+41*k)` for every natural `k`, with no
external AES entry-bound premise. The full proof and a replay of retained proof
artifacts were previously checked using only `propext`, `Classical.choice`, and
`Quot.sound`. A complete clean build of this combined repository layout has not
been validated. The generator was run on all 255 rows using Python 3.6.8 and
GCC 4.8.5 on Linux. All 69,913 certificate sources, including the tracked shared
modules, matched the accepted proof inventory in path, byte count, and SHA-256.
Partial generation, resuming complete rows, and rejection of a changed source
were also checked. These checks validate regeneration; they do not constitute a
new Lean compilation.

The AES experiment uses independent uniform round keys sampled once and retained
across evaluations, initial whitening, and omitted final MixColumns. The adaptive
consequence covers at most two classical forward queries, including stopping,
repeated queries, arbitrary finite outputs, and independent normalized finite
private randomness. It does not cover the standard AES key schedule. The finite
entry proofs establish the sufficient inequalities consumed by this theorem;
Keliher–Sui's exact maxima and original internal proof are outside their scope.

## Smaller checks

The earlier mixing theorem and an independent mathematical leaf can be checked
without generating the new finite certificates:

```sh
lake exe cache get
lake build AESMixingProof
lake env lean Audit.lean
lake build +AES8.Math.PaperWeightedSchur
```

These checks cover their named targets; they do not check the full `8 + 2*k`
theorem.
