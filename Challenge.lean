module

public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.CharZero

@[expose] public section

/-!
# Multiplying a `9 × 11` matrix by an `11 × 11` matrix with 708 multiplications: the statement

This file is the statement of record. It imports only Mathlib and states the results with `sorry`.
`Solution.lean` proves them; `comparator.json` names the compared theorems. No definitions of our
own are used.

## Bilinear algorithms and tensor rank

A *bilinear algorithm* of length `r` for the product of an `n × m` matrix `A` by an `m × p` matrix
`B` consists of `r` triples `(uᵢ, vᵢ, wᵢ)` of matrices of sizes `n × m`, `m × p` and `n × p` with

  `A * B = ∑ᵢ (∑ₐ ∑_b uᵢ[a, b] A[a, b]) * (∑_c ∑_d vᵢ[c, d] B[c, d]) • wᵢ`.

Each term needs one multiplication of a linear form in the entries of `A` by a linear form in the
entries of `B`, so the product takes `r` such multiplications (the schoolbook method takes
`n * m * p`). Equivalently, the triples decompose the matrix multiplication tensor `⟨n, m, p⟩`:

  `∑ᵢ uᵢ[a, b] * vᵢ[c, d] * wᵢ[e, f] = 1` if `b = c`, `a = e` and `d = f`, and `0` otherwise.

The least such `r` is the rank `R(⟨n, m, p⟩)` of the tensor; an algorithm of length `r` with
rational coefficients shows `R(⟨n, m, p⟩) ≤ r` over ℚ, and, applied recursively to blocks, it
multiplies matrices over any field of characteristic zero. Schemes of this kind for small formats
are collected in the catalogue of fast matrix multiplication algorithms of the University of Lille
(<https://fmm.univ-lille.fr/>).

## The results

* `exists_tensor_decomposition`: 708 triples of rational matrices decompose `⟨9, 11, 11⟩`. Hence
  `R(⟨9, 11, 11⟩) ≤ 708` over ℚ (the schoolbook method uses 1,089 products).
* `exists_bilinear_algorithm`: 708 triples of rational matrices form a bilinear algorithm for the
  product of `9 × 11` by `11 × 11` matrices over every field of characteristic zero.

Before this scheme the smallest rank listed in the Lille catalogue for the format `9 × 11 × 11` was
710 (M. Stoch, 2026).
-/

namespace MatMul9x11x11

/-- **A rank-708 decomposition of the matrix multiplication tensor `⟨9, 11, 11⟩` over ℚ.** -/
theorem exists_tensor_decomposition :
    ∃ (u : Fin 708 → Matrix (Fin 9) (Fin 11) ℚ) (v : Fin 708 → Matrix (Fin 11) (Fin 11) ℚ)
      (w : Fin 708 → Matrix (Fin 9) (Fin 11) ℚ),
      ∀ a b c d e f, ∑ i, u i a b * v i c d * w i e f = if b = c ∧ a = e ∧ d = f then 1 else 0 := by
  sorry

/-- **A bilinear algorithm with 708 multiplications for `9 × 11` by `11 × 11` matrices.** Its
coefficients are rational, and it computes the product over every field of characteristic zero. -/
theorem exists_bilinear_algorithm :
    ∃ (u : Fin 708 → Matrix (Fin 9) (Fin 11) ℚ) (v : Fin 708 → Matrix (Fin 11) (Fin 11) ℚ)
      (w : Fin 708 → Matrix (Fin 9) (Fin 11) ℚ),
      ∀ (K : Type*) [Field K] [CharZero K] (A : Matrix (Fin 9) (Fin 11) K)
        (B : Matrix (Fin 11) (Fin 11) K),
        A * B = ∑ i, ((∑ a, ∑ b, (u i a b : K) * A a b) * (∑ c, ∑ d, (v i c d : K) * B c d)) •
          (w i).map (fun x : ℚ => (x : K)) := by
  sorry

end MatMul9x11x11
