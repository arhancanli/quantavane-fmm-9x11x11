module

public import MatMul9x11x11.Sound
public import MatMul9x11x11.Chunks
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.Rat.Cast.CharZero
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Rat.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

@[expose] public section

/-!
# From the kernel checks to the statements

* `range_ok`, `bound_ok` (kernel checks) and `slices_ok` (`MatMul9x11x11.Chunks`) give, by
  `tensor_of_checks`, the integer identity `int_identity`:
  `∑ₜ uₜ[a, b] vₜ[c, d] wₜ[e, f] = dU dV dW [b = c ∧ a = e ∧ d = f]`.
* `u`, `v`, `w` are the scheme's matrices over ℚ (the integer entries divided by `dU`, `dV`, `dW`);
  `rat_identity` is the tensor decomposition and `bilinear` the bilinear algorithm over any field of
  characteristic zero.
-/

namespace MatMul9x11x11

open Finset

theorem range_ok : rangeOk 9 11 11 terms = true := by decide +kernel

theorem bound_ok : boundOk 40 (dU * dV * dW) terms = true := by decide +kernel

theorem terms_length : terms.length = 708 := by decide +kernel

/-- The integer identity of the scheme. -/
theorem int_identity : ∀ a < 9, ∀ b < 11, ∀ c < 11, ∀ d < 11, ∀ e < 9, ∀ f < 11,
    C terms (a * 11 + b) (c * 11 + d) (e * 11 + f) =
      if b = c ∧ a = e ∧ d = f then ((dU * dV * dW : ℕ) : ℤ) else 0 :=
  tensor_of_checks 9 11 11 40 (dU * dV * dW) terms range_ok bound_ok slices_ok

/-- The empty term. -/
def zeroTerm : Term := ⟨[], [], [], [], [], []⟩

/-- Term `i` of the scheme. -/
noncomputable def term (i : ℕ) : Term := terms.getD i zeroTerm

theorem sum_map_eq_sum_range {α : Type*} (g : α → ℤ) (z : α) : ∀ l : List α,
    (l.map g).sum = ∑ i ∈ range l.length, g (l.getD i z) := by
  intro l
  induction l with
  | nil => simp
  | cons x l ih => rw [List.map_cons, List.sum_cons, ih, List.length_cons, sum_range_succ']; simp [add_comm]

/-- The first factors, over ℚ. -/
noncomputable def u (i : Fin 708) : Matrix (Fin 9) (Fin 11) ℚ :=
  fun a b => (cu (term i) (a * 11 + b) : ℚ) / dU

/-- The second factors, over ℚ. -/
noncomputable def v (i : Fin 708) : Matrix (Fin 11) (Fin 11) ℚ :=
  fun c d => (cv (term i) (c * 11 + d) : ℚ) / dV

/-- The third factors, over ℚ. -/
noncomputable def w (i : Fin 708) : Matrix (Fin 9) (Fin 11) ℚ :=
  fun e f => (cw (term i) (e * 11 + f) : ℚ) / dW

/-- **The tensor decomposition.** -/
theorem rat_identity (a : Fin 9) (b : Fin 11) (c : Fin 11) (d : Fin 11) (e : Fin 9) (f : Fin 11) :
    ∑ i, u i a b * v i c d * w i e f = if b = c ∧ a = e ∧ d = f then 1 else 0 := by
  have hD : ((dU * dV * dW : ℕ) : ℚ) ≠ 0 := by norm_num [dU, dV, dW]
  have hsum : ∑ i, u i a b * v i c d * w i e f =
      (C terms (a * 11 + b) (c * 11 + d) (e * 11 + f) : ℚ) / ((dU * dV * dW : ℕ) : ℚ) := by
    rw [C, sum_map_eq_sum_range _ zeroTerm, terms_length, Int.cast_sum, Finset.sum_div, Finset.sum_range]
    refine sum_congr rfl fun i _ => ?_
    simp only [u, v, w, term, Int.cast_mul, Nat.cast_mul]
    field_simp
  rw [hsum, int_identity a a.2 b b.2 c c.2 d d.2 e e.2 f f.2]
  simp only [Fin.val_inj]
  split
  · rw [Int.cast_natCast]; exact div_self hD
  · simp

/-- **The bilinear algorithm**, over any field of characteristic zero. -/
theorem bilinear (K : Type*) [Field K] [CharZero K] (A : Matrix (Fin 9) (Fin 11) K)
    (B : Matrix (Fin 11) (Fin 11) K) :
    A * B = ∑ i, ((∑ a, ∑ b, (u i a b : K) * A a b) * (∑ c, ∑ d, (v i c d : K) * B c d)) •
      (w i).map (fun x : ℚ => (x : K)) := by
  ext e f
  rw [Matrix.mul_apply, Matrix.sum_apply]
  simp only [Matrix.smul_apply, Matrix.map_apply, smul_eq_mul]
  have key : ∀ i : Fin 708, (∑ a, ∑ b, (u i a b : K) * A a b) * (∑ c, ∑ d, (v i c d : K) * B c d) *
      (w i e f : K) = ∑ a, ∑ b, ∑ c, ∑ d, A a b * B c d * ((u i a b * v i c d * w i e f : ℚ) : K) := by
    intro i
    simp only [sum_mul]
    simp only [mul_sum, sum_mul, Rat.cast_mul]
    refine sum_congr rfl fun a _ => sum_congr rfl fun b _ => sum_congr rfl fun c _ =>
      sum_congr rfl fun d _ => by ring
  rw [sum_congr rfl fun i _ => key i]
  have swap : ∀ F : Fin 708 → Fin 9 → Fin 11 → Fin 11 → Fin 11 → K,
      ∑ i, ∑ a, ∑ b, ∑ c, ∑ d, F i a b c d = ∑ a, ∑ b, ∑ c, ∑ d, ∑ i, F i a b c d := by
    intro F
    rw [sum_comm]; refine sum_congr rfl fun a _ => ?_
    rw [sum_comm]; refine sum_congr rfl fun b _ => ?_
    rw [sum_comm]; refine sum_congr rfl fun c _ => ?_
    rw [sum_comm]
  rw [swap]
  simp only [← mul_sum, ← Rat.cast_sum, rat_identity, apply_ite (fun x : ℚ => (x : K)), Rat.cast_one,
    Rat.cast_zero, mul_ite, mul_one, mul_zero, ite_and]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']

end MatMul9x11x11
