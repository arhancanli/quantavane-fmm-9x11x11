# Multiplying 9 × 11 by 11 × 11 matrices with 708 multiplications

A Lean 4 proof, with Mathlib, that the matrix multiplication tensor `⟨9, 11, 11⟩` has rank at most
708 over the rationals: there is a bilinear algorithm with 708 multiplications for the product of a
`9 × 11` matrix by an `11 × 11` matrix, with rational coefficients, valid over every field of
characteristic zero. The smallest rank listed for this format in the Lille catalogue of fast matrix
multiplication algorithms was 710 when this was written. It is laid out for registration on
[Palomar](https://palomar-registry.org): `Challenge.lean` states the results, `Solution.lean` proves
them, and `comparator.json` names the compared theorems.

## The result

A bilinear algorithm of length `r` for `n × m` by `m × p` matrices is a list of `r` triples
`(uᵢ, vᵢ, wᵢ)` of matrices of sizes `n × m`, `m × p` and `n × p` such that, for all `A` and `B`,

```
A * B = ∑ᵢ (∑ₐ ∑_b uᵢ[a, b] A[a, b]) * (∑_c ∑_d vᵢ[c, d] B[c, d]) • wᵢ.
```

Each term costs one multiplication of a linear form in the entries of `A` by one in the entries of
`B`. Equivalently, the triples decompose the matrix multiplication tensor:
`∑ᵢ uᵢ[a, b] vᵢ[c, d] wᵢ[e, f]` is `1` when `b = c`, `a = e` and `d = f`, and `0` otherwise. The least
such `r` is the tensor rank `R(⟨n, m, p⟩)`. Because the entries of `A` and `B` never need to commute
with each other, such an algorithm can be applied to blocks of larger matrices.

**Theorem.** There are 708 triples of rational matrices that decompose `⟨9, 11, 11⟩`, and the same
triples give `A * B` for all `9 × 11` matrices `A` and `11 × 11` matrices `B` over any field of
characteristic zero. Hence `R(⟨9, 11, 11⟩) ≤ 708` over ℚ.

## What is compared (`comparator.json`)

| Lean name | What it says |
|---|---|
| `MatMul9x11x11.exists_tensor_decomposition` | There are `u : Fin 708 → Matrix (Fin 9) (Fin 11) ℚ`, `v : Fin 708 → Matrix (Fin 11) (Fin 11) ℚ` and `w : Fin 708 → Matrix (Fin 9) (Fin 11) ℚ` with `∑ i, u i a b * v i c d * w i e f = if b = c ∧ a = e ∧ d = f then 1 else 0` for all indices. |
| `MatMul9x11x11.exists_bilinear_algorithm` | There are such `u`, `v`, `w` with `A * B = ∑ i, ((∑ a, ∑ b, u i a b * A a b) * (∑ c, ∑ d, v i c d * B c d)) • w i` for every field `K` of characteristic zero and all `A`, `B` over `K` (coefficients cast from ℚ to `K`). |

`definition_names` is empty: the statements use only Mathlib's matrices, sums and casts.

## How the proof goes

- **The data** (`MatMul9x11x11/Data.lean`). The scheme, with its coefficients scaled to integers:
  each factor is multiplied by the least common multiple of the denominators of all its entries,
  `dU = 512`, `dV = 8` and `dW = 8`. Term `i` is stored as sparse lists of
  (position, absolute value) pairs for the positive and the negative entries of each factor.
  `scripts/make_data.py` wrote the file from the scheme file and checked the scheme first, in exact
  integer arithmetic. The Lean proof does not rely on that check or on the script.
- **The check** (`MatMul9x11x11/Check.lean`). For each entry `x` of the first factor (99 in all),
  the slice `∑ᵢ uᵢ[x] vᵢ[y] wᵢ[z]` over all `(y, z)` is computed as one integer: the coefficients are
  packed in base `X = 2⁴⁰`, `vᵢ` at `X^y` and `wᵢ` at `X^(121 z)`, so that one product of two
  integers computes `vᵢ[y] wᵢ[z]` for all `(y, z)` at once. The slice is compared with the packed
  slice of `dU dV dW` times the tensor. The checks use only operations on natural numbers and
  integers that Lean's kernel performs with GMP.
- **The kernel checks** (`MatMul9x11x11/Chunks.lean`). `decide +kernel` makes Lean's kernel run the
  check for each of the 99 slices (one theorem each, about 50 s in all), the range check (every
  position is inside its factor) and the bound check (`range_ok`, `bound_ok` in `Bridge.lean`).
- **Soundness** (`MatMul9x11x11/Sound.lean`), proved for every input, so the coefficients are
  untrusted data. A packed slice is the double sum `∑_z ∑_y C(x, y, z) X^y (X^121)^z`. The bound
  check gives `|C(x, y, z) - D T(x, y, z)| < X` for every coefficient, with `D = dU dV dW`, because
  `∑ᵢ ‖uᵢ‖₁ ‖vᵢ‖₁ ‖wᵢ‖₁ + D < 2⁴⁰`; and an integer `∑ₖ dₖ Xᵏ` with `|dₖ| < X` vanishes only if
  every `dₖ` does (`digits_zero`). So equal packed slices have equal coefficients
  (`tensor_of_checks`): `∑ᵢ uᵢ[a, b] vᵢ[c, d] wᵢ[e, f] = D [b = c ∧ a = e ∧ d = f]`.
- **The statements** (`MatMul9x11x11/Bridge.lean`). `u`, `v`, `w` are the integer factors divided
  by `dU`, `dV`, `dW`; dividing the identity by `D` gives the decomposition (`rat_identity`), and
  expanding `A * B` entrywise gives the bilinear algorithm over any field of characteristic zero
  (`bilinear`).

No `sorry` outside `Challenge.lean`, no `native_decide`, no extra axioms:
`lake env lean scripts/CheckAxioms.lean` prints `[propext, Classical.choice, Quot.sound]` for both
compared theorems.

## Why it is of interest

The rank of small matrix multiplication tensors is a central question of algebraic complexity
(Strassen 1969); schemes for small formats are used as building blocks for larger products and are
collected in the catalogue of fast matrix multiplication algorithms of the University of Lille
(A. Sedoglavic, <https://fmm.univ-lille.fr/>). Upper bounds there come from computer searches,
recently flip-graph methods (Kauers and Moosbauer; Arai, Ichikawa and Hukushima; Kauers and Wood;
Perminov). A scheme is a large finite object whose correctness is usually established by running a
program; here the identity is checked in Lean's kernel with a checker proved sound in Lean, so
correctness does not depend on the program that found the scheme or on our checking scripts. The
coefficients have denominators dividing `2⁹`, so the same identity holds over any field of
characteristic other than 2; only characteristic zero is formalized here.

## Provenance, literature and novelty

The scheme was found by Quantavane's computer search on 11 November 2026. It is M. Stoch's rank-710
scheme for this format (repository `cloudroom-math`, October 2026; the catalogue's entry, read as
`schemes/known/cloudroom-math/9x11x11_rank710.json` in A. I. Perminov's repository
`dronperminov/FastMatrixMultiplication`) improved in two steps, 710 to 709 (36 terms replaced by 35)
and 709 to 708 (46 terms replaced by 45). Each step was a flip-graph walk on the scheme's image
modulo 3 (flips of Kauers and Moosbauer with the plus transitions of Arai, Ichikawa and Hukushima)
followed by a 3-adic lift of the changed terms back to the rationals; 628 of the 708 terms are
Stoch's, unchanged.
Before this formalization the scheme was checked exactly by three separately written programs, each
of which rejects a copy with one coefficient changed.

When this was written (November 2026), the Lille catalogue listed `⟨9, 11, 11⟩` at rank 710
(Stoch 2026), and Perminov's repository, which collects published schemes, listed 710 over ℚ for
this format; a search of arXiv on 12 November 2026 found no newer work on upper bounds for
rectangular formats. We know of no smaller published rank, but the search was limited to these
sources, so novelty is our reading of it, not an established fact.

Data: `MatMul9x11x11/Data.lean` was generated by `scripts/make_data.py` from the scheme file
`9x11x11_708_tensor.mpl`, in the catalogue's Maple layout
`A . B = ∑ᵢ Trace(Pᵢᵀ A) Trace(Qᵢᵀ B) Rᵢᵀ` (SHA-256
`ccce4b416505a7af69338709bb4a332f2c87875009e9ff27cce600e97c228d74`); `uᵢ = Pᵢ`, `vᵢ = Qᵢ`,
`wᵢ = Rᵢᵀ`.

## Authorship and the role of AI

Author and maintainer: Arhan Canli (Quantavane), who takes responsibility for the result.

The search, the checks, the checker, its soundness proof and every line of Lean here were produced
by AI agents (Claude, by Anthropic) working for Quantavane under Arhan Canli's direction. No
mathematician outside Quantavane has reviewed the proof.

## Checking it

Lean `v4.35.0` (`lean-toolchain`) and Mathlib `v4.35.0`
(`56a005855ea17e0b0958f73ec801ae140b0a1679`, pinned in `lake-manifest.json`).

```sh
lake exe cache get        # prebuilt Mathlib
lake build                # MatMul9x11x11, Challenge, Solution (the kernel checks take about a minute)
lake env lean scripts/CheckAxioms.lean
lake comparator           # Linux with bubblewrap: compares Challenge and Solution and replays the proofs
python3 scripts/make_data.py 9x11x11_708_tensor.mpl .   # regenerates Data.lean and Chunks.lean
```

`.github/workflows/palomar-preflight.yml` runs Palomar's own mechanical check
(`PalomarRegistry/PalomarSubmission`, pinned commit) on every push to `main`.

## Files

- `Challenge.lean`: the statement of record (Mathlib imports only).
- `Solution.lean`: the two compared theorems with proofs.
- `MatMul9x11x11/Check.lean`: the kernel-evaluated checks (Lean core only).
- `MatMul9x11x11/Data.lean`: the scheme, scaled to integers (generated).
- `MatMul9x11x11/Chunks.lean`: the 99 kernel checks of the slices (generated).
- `MatMul9x11x11/Sound.lean`: soundness of the checks for every input.
- `MatMul9x11x11/Bridge.lean`: the range and bound checks, and the two statements.
- `comparator.json`, `formalization.yaml`, `scripts/CheckAxioms.lean`, `scripts/make_data.py`.

## Licence

Apache-2.0 (`LICENSE`).
