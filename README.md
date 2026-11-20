# riemann-hypothesis

## Reusing the compiled proof

This fork publishes Linux x86-64 Lake build products in GitHub Releases. The
`Lean release build` workflow walks the local imports reachable from `Main`.
Each shard key includes its source blobs, all prerequisite shard keys, the Lake
configuration, the pinned toolchain and the package manifest. Successful shards
survive new workflows and expiration of the Actions cache.

On Linux x86-64, check out the desired commit, install its pinned Lean
toolchain, and run these commands with GitHub CLI, Python 3.12+, curl and zstd:

```sh
lake exe cache get
python3 ci/parts.py restore Main
```

You can replace `Main` with any released module, for example `Statements`.
The command selects its import closure, verifies GitHub's SHA-256 for each
downloaded archive and finishes with `lake --no-build build`. Downloads are
reusable before the entire proof has built. The `lean-parts-v1-*` prereleases
hold compiled parts. A final `build-<commit>` release includes the dependency
plan, the checksums and URLs of all parts, and the axiom report for the five
statements. The final job imports the compiled `Main` on a fresh runner.

Start or resume the default branch build with
`gh workflow run lean-parts.yml -R the-omega-institute/riemann-hypothesis`.
The scheduler discovers ready work from the published dependency hashes once a
minute and dispatches it across independent Actions matrices. Each completed
shard publishes immediately. The first 17 compilation keys are retained from
the initial run. On this source tree there are 8,490 shards, 36 dependency
levels and 529 independently eligible jobs immediately after the foundations.
GitHub allocates the available runners. Longer remaining paths to Main are
dispatched first. A single active workflow per shard hash and a Release lookup
before toolchain installation let overlapping runs reuse completed work.
The coordinator retries missing parts, rolls over before the hosted job time
limit and reconstructs progress from Releases and active Actions batches.
A new manual dispatch resumes after an interrupted coordinator.
The default runner is Ubuntu 24.04 x86-64. The repository variable
`RH_LINUX_RUNNER` can select a Linux x86-64 runner with more memory or disk.

## Upstream verification project

[![checks](https://github.com/Deicyde/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/Deicyde/riemann-hypothesis/actions/workflows/checks.yml)

A [Comparator](https://github.com/leanprover/comparator) setup for the Lean formalization
claiming a proof of the Riemann Hypothesis and of GRH for Dirichlet L-functions, announced on
2026-11-20 at <https://alpo.ge/remark.pdf>.

The submission ships no challenge file that imports only Mathlib and no Comparator config.
This repository is the submission, unmodified, plus those two files:

- [`src/Challenge.lean`](src/Challenge.lean) imports only Mathlib and states the five theorems.
- [`comparator.json`](comparator.json) is the Comparator config. The solution module is the submission's `Main`.

Everything else we wrote is in [`verification/`](verification/NOTES.md).

## Status

| Check | Result |
|---|---|
| Source is identical to the published tarball | pass (CI) |
| Challenge compiles against Mathlib alone | pass (CI) |
| No `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `opaque` in the source | pass ([scan](verification/static-scan.txt)) |
| All nine dependency pins are official upstream commits | pass ([notes](verification/NOTES.md#dependencies)) |
| The Comparator route below, on a Mathlib-sized test | pass ([notes](verification/NOTES.md#smoke-test)) |
| **Comparator on the submission** | **not yet run**; the build is in progress and takes hours |

## The statements

`riemannHypothesis : RiemannHypothesis` uses Mathlib's own definition. The other four theorems
use four short definitions that `Challenge.lean` copies from the submission's `Statements.lean`:

- `riemannZeta_eq_zero_re`: RH again, written out.
- `LFunction_ne_zero_of_half_lt_re`: L(χ, s) ≠ 0 for Re s > 1/2, for every modulus and every
  Dirichlet character, except the trivial character at s = 1.
- `LFunction_eq_zero_re`: every zero of every L(χ, s) with 0 < Re s < 1 has Re s = 1/2.
- `LFunction_eq_zero_re_of_isPrimitive`: the same for primitive characters.

"GRH" here means Dirichlet L-functions only.

## Running Comparator

The project is pinned to Lean `v4.33.1`, and `lake comparator` exists only from Lean 4.35. So
the check has three steps: build with the project's own Lean, export the challenge and the
solution, and judge the two exports with Lean `v4.36.0`.

**1. Build**, with Lean `v4.33.1`, in a sandbox with no network (hours; read
[the build notes](verification/NOTES.md#building) first):

```bash
lake exe cache get          # Mathlib's official build cache; needs the network
lake build Main Challenge
```

**2. Export**, with [lean4export](https://github.com/leanprover/lean4export) at tag `v4.33.0`,
built with Lean `v4.33.1`:

```bash
THEOREMS="riemannHypothesis riemannZeta_eq_zero_re LFunction_ne_zero_of_half_lt_re LFunction_eq_zero_re LFunction_eq_zero_re_of_isPrimitive"
PRELUDE="propext Quot.sound Classical.choice Nat.add Nat.sub Nat.mul Nat.pow Nat.gcd Nat.div Nat.mod Nat.beq Nat.ble Nat.land Nat.lor Nat.xor Nat.shiftLeft Nat.shiftRight String.ofList Char.ofNat List eagerReduce Nat String String.mk Char optParam autoParam semiOutParam outParam"

lake env lean4export Challenge -- Quot Quot.mk Quot.lift Quot.ind $THEOREMS $PRELUDE > challenge.export
lake env lean4export Main      -- Quot Quot.mk Quot.lift Quot.ind $THEOREMS $PRELUDE > solution.export
```

**3. Judge**, with the official Lean `v4.36.0` toolchain on `PATH`, from an empty directory:

```bash
lake comparator --config comparator.json \
  --challenge-from-export challenge.export --solution-from-export solution.export
```

Comparator checks that the five statements match, that the proofs use only the three permitted
axioms, and that the proof is accepted by Lean's kernel and by the four checkers named in
`comparator.json`: Lean paranoid, nanoda, con-leche and con-ron.

### Why not `--paranoid`

`lake comparator --paranoid` runs those same four checkers plus lean4lean. Lean 4.36's lean4lean
rejects every export made by Lean 4.33.1 with `unknown constant 'Decidable.intro'`, because
4.36 redefined `Decidable` in the core library. The flag therefore fails on this project
whatever the proof contains. `comparator.json` names the other four checkers directly, and
lean4lean is run separately, built with Lean `v4.33.1`
([notes](verification/NOTES.md#lean4lean)).

## Limits

- Comparator checks the challenge and the solution against the same Mathlib, so it cannot
  detect a modified Mathlib. The pin here is Mathlib's official `v4.33.1` tag.
- The exports are made by Lean 4.33.1 and judged by Lean 4.36.0. Lean's help text lists exports
  made elsewhere as an intended use, and the export format version is the same (3.1.0), but
  this is not the common path.
- Lean 4.33.1 predates several kernel and runtime fixes
  ([notes](verification/NOTES.md#lean-version)), which is why the judging uses 4.36.0 and
  independent checkers.
- A passing run still trusts the checkers, Mathlib's definitions, Mathlib's official build
  cache, the exporter, and the sandboxes.

## License

The submission belongs to its author and was published without a license. It is mirrored here
unmodified, for verification only.
