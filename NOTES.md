# Notes: what is proved and how it was checked (13 November 2026)

## What is proved

Proved in Lean 4 (v4.35.0, Mathlib v4.35.0) with no `sorry`, no `native_decide` and only the axioms
`propext`, `Classical.choice` and `Quot.sound`. The statements of record are in `Challenge.lean`;
`comparator.json` names the two compared theorems.

- `MatMul9x11x11.exists_tensor_decomposition`: 708 triples `(u i, v i, w i)` of rational matrices of
  sizes 9 × 11, 11 × 11, 9 × 11 with `∑ i, u i a b * v i c d * w i e f = if b = c ∧ a = e ∧ d = f then 1
  else 0` for all indices, i.e. `R(⟨9, 11, 11⟩) ≤ 708` over ℚ.
- `MatMul9x11x11.exists_bilinear_algorithm`: such triples with
  `A * B = ∑ i, ((∑ a, ∑ b, u i a b * A a b) * (∑ c, ∑ d, v i c d * B c d)) • w i` for every field `K`
  of characteristic zero (any universe) and all `A : Matrix (Fin 9) (Fin 11) K`,
  `B : Matrix (Fin 11) (Fin 11) K`, the coefficients cast from ℚ.

The kernel checks (`decide +kernel`): `chunk_0` … `chunk_98` (one per entry `x` of the first factor:
the packed slice `∑ᵢ uᵢ[x] (∑_y vᵢ[y] X^y)(∑_z wᵢ[z] X^(121 z))`, `X = 2⁴⁰`, equals the packed
slice of `D` times the tensor, `D = dU dV dW = 32,768`), `range_ok`, `bound_ok`
(`∑ᵢ ‖uᵢ‖₁ ‖vᵢ‖₁ ‖wᵢ‖₁ + D = 151,988,203,520 < 2⁴⁰`) and `terms_length`.
`MatMul9x11x11/Sound.lean` proves for every input that these checks give the integer identity
(`tensor_of_checks`); the scheme is untrusted data. `scripts/make_data.py` checked the scheme
file's SHA-256 (`ccce4b416505a7af69338709bb4a332f2c87875009e9ff27cce600e97c228d74`) and all 1,185,921
coefficient equations in exact integer arithmetic before writing the data; the Lean proof does not
rely on either.

## Line counts

| File | Lines |
|---|---|
| `Challenge.lean` | 65 (3,244 bytes) |
| `Solution.lean` | 34 |
| `MatMul9x11x11.lean` | 7 |
| `MatMul9x11x11/Check.lean` | 80 |
| `MatMul9x11x11/Data.lean` | 2,157 (generated; 39,620 nonzero coefficients) |
| `MatMul9x11x11/Chunks.lean` | 417 (generated) |
| `MatMul9x11x11/Sound.lean` | 377 |
| `MatMul9x11x11/Bridge.lean` | 112 |
| `scripts/CheckAxioms.lean` | 14 |

Every `.lean` file starts with `module`; `Challenge.lean` imports only Mathlib
(`Mathlib.Data.Matrix.Mul`, `Mathlib.Data.Rat.Cast.CharZero`).

## Checks run (Mac, Apple silicon, Lean v4.35.0, machine load about 50 to 60)

All on a fresh clone of commit `a006e1a35a1661ba8dfe595b8b12bf7604e669d2` (the commit before this
file was added; no Lean file changed since), with the Lake packages of the pinned Mathlib checkout
and the project's own modules built from scratch.

1. `lake build`: every module built; `MatMul9x11x11.Chunks` (the 99 kernel checks) 47 s (the whole
   build peaked at 2.0 GB in a separate build of the same modules). `Challenge` warns twice
   (declarations use `sorry`, as intended).
2. `lake env lean scripts/CheckAxioms.lean`: both theorems
   `depend on axioms: [propext, Classical.choice, Quot.sound]`.
3. `lake comparator` needs bubblewrap (Linux namespaces) and does not run on macOS; the
   `--inadvisably-no-sandbox` mode was not used. Palomar's preflight workflow runs it on Linux after a
   push. In its place, steps 4 and 6 were run by hand.
4. Statement comparison: every constant reachable from the types of the compared theorems
   (following definition values, not proofs) was printed with `pp.all` and hashes in the Challenge and
   in the Solution environment. The two outputs (2 roots, 632 constants) are identical.
5. Red controls (each must fail, and does): one coefficient of term 0 increased by one in the first,
   the second and the third factor (slice 0 fails each time); a zero coefficient of the second factor
   of term 0 made 1 (slice 0 fails); the last term dropped, i.e. rank 707 claimed (some slice fails);
   the bound check with 37-bit slots; the range check for the format 9 × 11 × 10. The unchanged
   slice 0, checked in the same file, passes. `scripts/make_data.py` also fails on a changed scheme
   file (SHA-256) and would fail on a wrong coefficient (its own exact check).
6. Kernel replays: `leanexport` wrote both modules with the compared theorems as targets; the
   Solution export (32.1 MB) was replayed through every kernel bundled with the toolchain, each run
   stopped if it passed 7 GB of memory, and con-ron also after 30 minutes:

   ```
   leanchecker            rc 0    57 s   1.4 GB
   nanoda                 rc 0    14 s   1.7 GB
   con-ron --jobs=1       stopped after 30 minutes without a verdict (1.3 GB)
   leanchecker-paranoid   rc 0    72 s   1.5 GB
   lean4lean              rc 0    66 s   1.5 GB   checked 7341 declarations
   con-leche              rc 0    23 s   5.7 GB   accepted 7344 declarations (--verified)
   ```

   con-ron reported no error but did not finish: the large-integer arithmetic of the 99 slice checks
   is slow for it (on the 9 × 10 × 11 scheme its default parallel mode passed 7.8 GB). The other five
   kernels finish in under two minutes each.

   NanoDa with unpermitted axioms as a hard error: Solution export exit 0; Challenge export exit 1
   (`export file declares unpermitted axiom "sorryAx"`), as it should. `Lean.ofReduceBool` does not
   occur in the Solution export. SHA-256 of the exports: `solution.ndjson`
   `3e1542884cb82a17beb0a279add02e6c32b99b2cf8eb0b9cdf347f179e444c49`, `challenge.ndjson`
   `393339a0383b128b0cf88f9830369041e0a85ac79db042eda7a485452df03676`.

## What remains

- Palomar's mechanical preflight (the workflow above, on GitHub's Linux runners) has not run: it needs
  the repository to be public on GitHub. Its advisory con-ron replay may not finish there either; the
  Lean kernel and NanoDa replays, which it requires, use under 2 GB.
- No review outside Quantavane's agents.
- Not formalized: tensor rank as a definition, positive characteristic, recursive use on blocks,
  lower bounds.
