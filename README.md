# Riemann hypothesis · reproducible Lean builds

Levent Alpöge proved the Riemann hypothesis in Lean. His library also contains results on zeros of Dirichlet L-functions. **The Omega Institute builds and distributes that source in reusable pieces so others can check it on their own machines.** Deicyde mirrored the original archive and supplied the independent Comparator challenge. The proof declarations are in `src/Main.lean`. [Author’s announcement](https://alpo.ge/remark.pdf) · [Upstream verification project](https://github.com/Deicyde/riemann-hypothesis) · [Main.lean](src/Main.lean)

## Companion book

The Omega Institute’s *Symmetry on the Critical Line: How the Riemann Hypothesis Is Proved* is a bilingual guide to Alpöge’s Lean formalization. The English edition follows the argument from symmetry about the critical line to Dirichlet L-functions, with worked examples and interactive figures. Its final chapter explains how to trace a theorem to its Lean declaration and what an independent kernel replay checks.

[Read the English edition](https://rh.trureturing.org/riemann-hypothesis/en/) · [Book source on GitHub](https://github.com/the-omega-institute/riemann-hypothesis-book)

## Public kernel replay results

On 21 November 2026 the Lean and Mathlib communities certified Alpöge’s proof of Mathlib’s `RiemannHypothesis`. Their joint statement, endorsed by the Lean FRO and the Mathlib Initiative, reports that both Comparator and con-leche matched the proved theorem to the Mathlib statement. [Joint statement](https://leanprover-community.github.io/blog/posts/riemann-hypothesis/)

Independent reports recorded successful kernel checks of the five declarations in `Main.lean`, covering Mathlib’s Riemann hypothesis and the corresponding results for Dirichlet L-functions. The published axiom audit lists only `propext`, `Classical.choice`, and `Quot.sound` for each declaration. [Five-theorem audit](https://math.mit.edu/~drew/grh/audit.log)

| Public run | Input and result | Primary evidence |
|---|---|---|
| Andrew Sutherland (MIT) | Lean’s `leanchecker` replayed all 175,187 compiled project modules with zero rejections. `lean4lean` also accepted every module, including five that needed a higher step limit. | [Run report](https://math.mit.edu/~drew/grh/) · [Five reruns](https://math.mit.edu/~drew/grh/lean4lean-raised-fuel.log) |
| Sutherland, exported proof | The independent Rust kernel nanoda and `con-leche --verified` accepted the full solution export. In a separate comparison against the Mathlib-only challenge, con-leche identified all five requested theorems as “justified by the solution.” | [nanoda](https://math.mit.edu/~drew/grh/nanoda.log) · [con-leche](https://math.mit.edu/~drew/grh/con-leche-master.log) · [Statement comparison](https://math.mit.edu/~drew/grh/con-leche-compare.log) |
| `mrubinst/grh-lean-verification` | A second build replayed each module’s declarations through Lean 4.33.1 using `replayFromImports`. The sets of compiled and successfully replayed modules matched exactly, with 175,187 entries each. | [Replay summary](https://github.com/mrubinst/grh-lean-verification/blob/cd2dad86c884ab17f348189edae2e5c3248533a9/replay_summary.txt) |
| Elliot Arledge and Luis Rivera, separate builds | Their five-theorem exports have the same SHA-256 (`4301ce48…3072e7e`). Each nanoda log records 1,484,729 declarations checked with zero errors. Rivera also published a con-leche comparison against a Mathlib-only challenge that lists all five theorems as justified. | [Arledge’s receipt](https://github.com/Infatoshi/rh-verification-receipts/blob/ac99f18cef21952de094234fab95db342ed16638/VERIFICATION_RESULT.txt) · [Rivera’s checksum](https://github.com/chubakueno/riemann-lean-verification/blob/975074872445beee5af4ea2d8e296b4b59f1d592/evidence/export/main.ndjson.sha256) · [Rivera’s nanoda output](https://github.com/chubakueno/riemann-lean-verification/blob/975074872445beee5af4ea2d8e296b4b59f1d592/evidence/nanoda/nanoda-out.txt) · [Rivera’s comparison](https://github.com/chubakueno/riemann-lean-verification/blob/975074872445beee5af4ea2d8e296b4b59f1d592/evidence/con-leche-compare/compare-out-windows.txt) |

Sutherland’s 09:30 UTC report still listed the end-to-end `lake comparator` run on the full submission as in progress. The LUMI team separately reported a sandboxed build of all 175,187 modules and a matching `Main.olean` hash. This fork publishes its own build and audit results through GitHub Actions and Releases. [MIT status](https://math.mit.edu/~drew/grh/) · [LUMI build record](https://github.com/aapolipponen/rh-lean-check-lumi/blob/82d91dbbd04d71f2cb45c3f2898f421b91c1c9d7/results/build-summary.json) · [Omega build](https://github.com/the-omega-institute/riemann-hypothesis/actions/workflows/lean-parts.yml)

## Verify locally

Use x86-64 Linux with Git, Python 3.12 or later, curl, zstd, and the `lake` command from Lean 4.33.1 on your PATH. You can install it with elan or use the pinned native Lean distribution. Public Release downloads work without a GitHub account. The coverage command also works on macOS. [Install elan](https://lean-lang.org/install/)

```sh
git clone --depth 1 https://github.com/the-omega-institute/riemann-hypothesis.git
cd riemann-hypothesis
./verify --status Main
./verify Main
```

`--status` reports the source commit, how many required shards are available, and their total compressed size. At partial coverage, the default verification command exits before downloading the proof. You can check a small published module immediately, or explicitly choose to build the missing part of `Main`.

```sh
./verify BuildAid.D1           # Small environment setup module for testing the full restore and replay path
./verify --build-missing Main  # Restore published dependencies, then compile the missing modules locally
```

The script fetches the pinned Mathlib build cache, checks each downloaded shard against its GitHub Release SHA-256, and restores the files needed by the selected module. It then runs `lake --no-build build` and `lake env leanchecker --fresh`. The latter replays declarations from the module and its imports in an empty Lean environment on your machine. Restored files persist in `.lake/` for later invocations. The complete `Main` replay covers the full proof and Mathlib and can require substantial memory and disk. [Upstream build observations](verification/NOTES.md#building)

For `Main`, the script also checks the five headline declarations against the allowed axioms `propext`, `Classical.choice`, and `Quot.sound`. It writes the output to `.lake/parts/axioms.txt`. A success message names the exact module replayed. For the independent multi-checker route, see [Running Comparator](#running-comparator).

## How the fork publishes compiled shards

CI partitions the actual import closure of `Main`. Each shard key covers the source blobs, prerequisite shard keys, build configuration, toolchain, and pinned packages. The `lean-parts-v1-*` prereleases hold compiled Linux x86-64 outputs. You can reuse them as soon as they appear, including across unchanged portions of different commits. The final `build-<commit>` release contains the complete dependency plan, shard URLs and checksums, and the five-theorem axiom report. [Live build](https://github.com/the-omega-institute/riemann-hypothesis/actions/workflows/lean-parts.yml) · [Release assets](https://github.com/the-omega-institute/riemann-hypothesis/releases)

Start or resume the default branch build with
`gh workflow run lean-parts.yml -R the-omega-institute/riemann-hypothesis`.
The scheduler discovers ready work from the published dependency hashes once a
minute and dispatches it across independent Actions matrices. Each completed
shard publishes immediately. The first 17 compilation keys are retained from
the initial run. On this source tree there are 8,490 shards, 36 dependency
levels and 529 independently eligible jobs immediately after the foundations.
Jobs run as matching self-hosted workers become available. Longer remaining paths to Main are
dispatched first. A single active workflow per shard hash and a Release lookup
before toolchain installation let overlapping runs reuse completed work.
The coordinator retries missing parts, rolls over before the hosted job time
limit and reconstructs progress from Releases and active Actions batches.
A new manual dispatch resumes after an interrupted coordinator.

Near the end of a build, some modules in a blocked shard already have every
external import available. Set the repository variable `RH_GROUP_SHARDS` to a
JSON array of the selected shard numbers, then dispatch `early-groups.yml`
with the shard's `number` and its full `key` from the plan. The workflow
queues independent groups for the available workers and publishes each verified archive
under a content-derived Release key. A later group can restore these modules
even while their parent shard is incomplete. When a connected group has an
unavailable import, the workflow publishes any individual members whose imports
are ready. The later group restores those members before building the rest.
The parent restores its groups,
runs Lake's no-build check, and packages the full shard at its original key.
If an independent full build produces different binary hashes for those modules,
the Release can also hold a full archive assembled from the published groups.
Its filename includes the SHA-256 of the independent archive. CI and `./verify`
select the assembled archive so downstream Lake traces see the original group outputs.
The early workflow and the parent share a concurrency lock.

Each compiler job uses a self-hosted Linux x86-64 runner. Shards, early groups,
module replays, the Challenge check and the final five-theorem audit all use the
same runner labels. Planning, source comparison and Release uploads run on
GitHub-hosted workers. Pull requests from forks receive the source comparison,
and the merged revision receives the self-hosted Challenge check.

CI sets Lake's task thread count to the available CPU count reported by `nproc`.
A runner service can set `LEAN_NUM_THREADS` to override this default. Toolchain
setup logs both counts. Lake can schedule independent imports together. A
module starts compiling once its prerequisites are ready.

The runner keeps the pinned native Lean toolchain and Python under
`_work/rh-tools/`. Actions caches Mathlib separately by toolchain and package
manifest. If a Release download exhausts its retries, CI can recover the same
shard from the original build artifact during its one-day retention and verify
the Release SHA-256.
Self-hosted runners keep verified Release archives in `rh-release-cache/` next
to the runner's temporary directory (typically `_work/rh-release-cache/`).
Fresh checkouts share the files on that machine. Each restore verifies the
archive against the published SHA-256 and downloads a replacement if needed.
Set `RH_RELEASE_CACHE_DIR` in the runner environment to use a mounted disk,
or set it when running `./verify` locally to share archives across clones.

## Upstream verification project

[![checks](https://github.com/Deicyde/riemann-hypothesis/actions/workflows/checks.yml/badge.svg)](https://github.com/Deicyde/riemann-hypothesis/actions/workflows/checks.yml)

The upstream project supplies a [Comparator](https://github.com/leanprover/comparator) setup for Alpöge’s Lean formalization
of the Riemann hypothesis and GRH for Dirichlet L-functions, announced on
2026-11-20 at <https://alpo.ge/remark.pdf>.

The submission ships no challenge file that imports only Mathlib and no Comparator config.
This repository is the submission, unmodified, plus those two files:

- [`src/Challenge.lean`](src/Challenge.lean) imports only Mathlib and states the five theorems.
- [`comparator.json`](comparator.json) is the Comparator config. The solution module is the submission's `Main`.

Upstream’s verification notes are in [`verification/`](verification/NOTES.md).

## Upstream verification status

| Check | Result |
|---|---|
| Source is identical to the published tarball | pass (CI) |
| Challenge compiles against Mathlib alone | pass (CI) |
| No `sorry`, `axiom`, `native_decide`, `unsafe`, `implemented_by` or `opaque` in the source | pass ([scan](verification/static-scan.txt)) |
| All nine dependency pins are official upstream commits | pass ([notes](verification/NOTES.md#dependencies)) |
| The Comparator route below, on a Mathlib-sized test | pass ([notes](verification/NOTES.md#smoke-test)) |
| Upstream’s end-to-end Comparator on the submission | Upstream reported its build in progress on 21 November 2026. [Upstream run notes](https://github.com/leanprover-community/riemann-hypothesis/blob/6b1e1b8e9d683841024757f158fda63a32bbeae7/verification/NOTES.md#results) |

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
