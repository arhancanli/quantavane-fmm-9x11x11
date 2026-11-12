module

public import MatMul9x11x11.Check
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

@[expose] public section

/-!
# Soundness of the packed check, for every input

The checks of `MatMul9x11x11.Check` run on any list of terms. This file proves, for every list,
that if the range check, the bound check and all slice checks succeed, then the integer
coefficients satisfy the equations of the matrix multiplication tensor:

  `∑ₜ uₜ[a m + b] vₜ[c p + d] wₜ[e p + f] = D` if `b = c`, `a = e`, `d = f`, and `0` otherwise
  (`tensor_of_checks`).

The packed integers are sums `∑ c * X ^ k` with `X = 2 ^ s`. A slice check compares two such sums
in two levels (`X` and `Y = X ^ (m p)`), and the bound check makes every difference of
coefficients smaller than `X` in absolute value, so equal sums have equal coefficients
(`digits_zero`, `digits_zero₂`).
-/

namespace MatMul9x11x11

open Finset

/-! ## Base-`X` expansions with small digits -/

theorem digits_bound (X : ℤ) (hX : 0 < X) (d : ℕ → ℤ) :
    ∀ N : ℕ, (∀ k < N, |d k| < X) → |∑ k ∈ range N, d k * X ^ k| < X ^ N := by
  intro N
  induction N with
  | zero => intro _; simp
  | succ N ih =>
    intro hd
    rw [sum_range_succ, pow_succ]
    have h1 := ih (fun k hk => hd k (by omega))
    have h2 := hd N (by omega)
    have hXN : 0 < X ^ N := pow_pos hX N
    have h1' : |∑ k ∈ range N, d k * X ^ k| ≤ X ^ N - 1 := by linarith [Int.add_one_le_iff.mpr h1]
    have h2' : |d N| ≤ X - 1 := by linarith [Int.add_one_le_iff.mpr h2]
    have h3 : |d N| * X ^ N ≤ (X - 1) * X ^ N := mul_le_mul_of_nonneg_right h2' hXN.le
    calc |∑ k ∈ range N, d k * X ^ k + d N * X ^ N|
        ≤ |∑ k ∈ range N, d k * X ^ k| + |d N * X ^ N| := abs_add_le _ _
      _ = |∑ k ∈ range N, d k * X ^ k| + |d N| * X ^ N := by rw [abs_mul, abs_of_pos hXN]
      _ < X ^ N * X := by nlinarith

theorem digits_zero (X : ℤ) (hX : 0 < X) (d : ℕ → ℤ) :
    ∀ N : ℕ, (∀ k < N, |d k| < X) → ∑ k ∈ range N, d k * X ^ k = 0 → ∀ k < N, d k = 0 := by
  intro N
  induction N with
  | zero => intro _ _ k hk; omega
  | succ N ih =>
    intro hd hs
    rw [sum_range_succ] at hs
    have hb := digits_bound X hX d N (fun k hk => hd k (by omega))
    have hXN : 0 < X ^ N := pow_pos hX N
    have hdN : d N = 0 := by
      by_contra hne
      have h1 : X ^ N ≤ |d N * X ^ N| := by
        rw [abs_mul, abs_of_pos hXN]
        have : 1 ≤ |d N| := Int.one_le_abs hne
        nlinarith
      have h2 : |∑ k ∈ range N, d k * X ^ k| = |d N * X ^ N| := by
        rw [show ∑ k ∈ range N, d k * X ^ k = -(d N * X ^ N) by linarith, abs_neg]
      linarith
    rw [hdN, zero_mul, add_zero] at hs
    intro k hk
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | hk
    · exact ih (fun k hk => hd k (by omega)) hs k hk
    · exact hk ▸ hdN

/-- Two levels: digits `d y z` at `X ^ y * (X ^ M) ^ z`. -/
theorem digits_zero₂ (X : ℤ) (hX : 0 < X) (M N : ℕ) (d : ℕ → ℕ → ℤ)
    (hd : ∀ y < M, ∀ z < N, |d y z| < X)
    (hs : ∑ z ∈ range N, ∑ y ∈ range M, d y z * X ^ y * (X ^ M) ^ z = 0) :
    ∀ y < M, ∀ z < N, d y z = 0 := by
  have hXM : 0 < X ^ M := pow_pos hX M
  have hs' : ∑ z ∈ range N, (∑ y ∈ range M, d y z * X ^ y) * (X ^ M) ^ z = 0 := by
    rw [← hs]; exact sum_congr rfl fun z _ => by rw [sum_mul]
  have hz := digits_zero (X ^ M) hXM (fun z => ∑ y ∈ range M, d y z * X ^ y) N
    (fun z hz => digits_bound X hX (fun y => d y z) M (fun y hy => hd y hy z hz)) hs'
  intro y hy z hz'
  exact digits_zero X hX (fun y => d y z) M (fun y hy => hd y hy z hz') (hz z hz') y hy

/-! ## The sparse lists -/

theorem coefN_cons (k : ℕ) (e : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    coefN k (e :: l) = (if e.1 = k then e.2 else 0) + coefN k l := by
  simp only [coefN]
  cases h : Nat.beq e.1 k with
  | true => simp [Nat.eq_of_beq_eq_true h, Nat.add_eq]
  | false => simp [Nat.ne_of_beq_eq_false h]

theorem packN_cons (sh : ℕ) (e : ℕ × ℕ) (l : List (ℕ × ℕ)) :
    packN sh (e :: l) = e.2 * 2 ^ (sh * e.1) + packN sh l := by
  simp only [packN]
  show e.2 <<< (sh * e.1) + packN sh l = _
  rw [Nat.shiftLeft_eq]

/-- A packed list is the base-`2 ^ sh` expansion of its coefficients. -/
theorem packN_eq (sh N : ℕ) : ∀ l : List (ℕ × ℕ), (∀ e ∈ l, e.1 < N) →
    (packN sh l : ℤ) = ∑ k ∈ range N, (coefN k l : ℤ) * ((2 : ℤ) ^ sh) ^ k := by
  intro l
  induction l with
  | nil => intro _; simp [packN, coefN]
  | cons e l ih =>
    intro hl
    have he : e.1 < N := hl e List.mem_cons_self
    simp only [packN_cons, coefN_cons, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ite,
      Nat.cast_zero, add_mul, sum_add_distrib, ite_mul, zero_mul, sum_ite_eq, mem_range, he,
      ite_true, Nat.cast_ofNat]
    rw [ih (fun e' he' => hl e' (List.mem_cons_of_mem _ he')), pow_mul]

/-- The integer coefficient at position `k` of a factor given by its positive and negative
entries. -/
def cz (lp ln : List (ℕ × ℕ)) (k : ℕ) : ℤ := (coefN k lp : ℤ) - coefN k ln

/-- The coefficients of the three factors of a term. -/
def cu (t : Term) (k : ℕ) : ℤ := cz t.up t.un k
def cv (t : Term) (k : ℕ) : ℤ := cz t.vp t.vn k
def cw (t : Term) (k : ℕ) : ℤ := cz t.wp t.wn k

theorem pack_eq (sh N : ℕ) (lp ln : List (ℕ × ℕ)) (hp : ∀ e ∈ lp, e.1 < N)
    (hn : ∀ e ∈ ln, e.1 < N) :
    Int.subNatNat (packN sh lp) (packN sh ln) = ∑ k ∈ range N, cz lp ln k * ((2 : ℤ) ^ sh) ^ k := by
  rw [Int.subNatNat_eq_coe, packN_eq sh N lp hp, packN_eq sh N ln hn, ← sum_sub_distrib]
  exact sum_congr rfl fun k _ => by rw [cz, sub_mul]

/-! ## The range check -/

/-- The positions of a term are inside the three factors. -/
def TermRange (n m p : ℕ) (t : Term) : Prop :=
  (∀ e ∈ t.up, e.1 < n * m) ∧ (∀ e ∈ t.un, e.1 < n * m) ∧ (∀ e ∈ t.vp, e.1 < m * p) ∧
    (∀ e ∈ t.vn, e.1 < m * p) ∧ (∀ e ∈ t.wp, e.1 < n * p) ∧ (∀ e ∈ t.wn, e.1 < n * p)

theorem posLt_iff (N : ℕ) (l : List (ℕ × ℕ)) : posLt N l = true ↔ ∀ e ∈ l, e.1 < N := by
  simp [posLt, List.all_eq_true, Nat.blt_eq]

theorem termRange_of_rangeOk (n m p : ℕ) (ts : List Term) (h : rangeOk n m p ts = true) :
    ∀ t ∈ ts, TermRange n m p t := by
  intro t ht
  have := List.all_eq_true.mp h t ht
  simp only [termOk, Bool.and_eq_true, posLt_iff] at this
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := this
  exact ⟨h1, h2, h3, h4, h5, h6⟩

/-! ## The slice -/

/-- The coefficient of the scheme at `(x, y, z)`: `∑ₜ uₜ[x] vₜ[y] wₜ[z]`. -/
def C (ts : List Term) (x y z : ℕ) : ℤ := (ts.map fun t => cu t x * cv t y * cw t z).sum

theorem slice_eq (n m p s x : ℕ) : ∀ ts : List Term, (∀ t ∈ ts, TermRange n m p t) →
    slice s (m * p) x ts = ∑ z ∈ range (n * p), ∑ y ∈ range (m * p),
      C ts x y z * ((2 : ℤ) ^ s) ^ y * (((2 : ℤ) ^ s) ^ (m * p)) ^ z := by
  intro ts
  induction ts with
  | nil => intro _; simp [slice, C]
  | cons t ts ih =>
    intro hts
    obtain ⟨_, _, hvp, hvn, hwp, hwn⟩ := hts t List.mem_cons_self
    have ih' := ih (fun t' h' => hts t' (List.mem_cons_of_mem _ h'))
    have hV : Int.subNatNat (packN s t.vp) (packN s t.vn) =
        ∑ k ∈ range (m * p), cv t k * ((2 : ℤ) ^ s) ^ k := pack_eq s (m * p) t.vp t.vn hvp hvn
    have hW : Int.subNatNat (packN (s * (m * p)) t.wp) (packN (s * (m * p)) t.wn) =
        ∑ k ∈ range (n * p), cw t k * (((2 : ℤ) ^ s) ^ (m * p)) ^ k := by
      rw [← pow_mul]; exact pack_eq (s * (m * p)) (n * p) t.wp t.wn hwp hwn
    have hsplit : ∀ y z, C (t :: ts) x y z = cu t x * cv t y * cw t z + C ts x y z := by
      intro y z; simp [C]
    simp only [hsplit, add_mul, sum_add_distrib]
    rw [← ih']
    have key : cu t x * ((∑ y ∈ range (m * p), cv t y * ((2 : ℤ) ^ s) ^ y) *
        (∑ z ∈ range (n * p), cw t z * (((2 : ℤ) ^ s) ^ (m * p)) ^ z)) =
        ∑ z ∈ range (n * p), ∑ y ∈ range (m * p),
          cu t x * cv t y * cw t z * ((2 : ℤ) ^ s) ^ y * (((2 : ℤ) ^ s) ^ (m * p)) ^ z := by
      rw [sum_mul_sum, mul_sum, sum_comm]
      refine sum_congr rfl fun z _ => ?_
      rw [mul_sum]
      refine sum_congr rfl fun y _ => ?_
      ring
    rw [← key, ← hV, ← hW]
    simp only [slice]
    cases h : Nat.beq (coefN x t.up) (coefN x t.un) with
    | true =>
      have h0 : cu t x = 0 := by simp [cu, cz, Nat.eq_of_beq_eq_true h]
      simp [h0]
    | false =>
      simp only [Bool.cond_false]
      rw [show Int.subNatNat (coefN x t.up) (coefN x t.un) = cu t x by
        rw [Int.subNatNat_eq_coe]; rfl]
      rfl

/-! ## The expected slice -/

theorem expectN_eq (s D mp p a b : ℕ) : ∀ k : ℕ,
    (expectN s D mp p a b k : ℤ) =
      ∑ d ∈ range k, (D : ℤ) * ((2 : ℤ) ^ s) ^ (b * p + d) * (((2 : ℤ) ^ s) ^ mp) ^ (a * p + d) := by
  intro k
  induction k with
  | zero => simp [expectN]
  | succ k ih =>
    rw [sum_range_succ, ← ih]
    simp only [expectN]
    show ((D <<< (s * ((b * p + k) + mp * (a * p + k))) + expectN s D mp p a b k : ℕ) : ℤ) = _
    rw [Nat.shiftLeft_eq]
    push_cast
    ring

/-- A sum over `range (m * p)` as a double sum. -/
theorem sum_range_mul (m p : ℕ) (g : ℕ → ℤ) :
    ∑ y ∈ range (m * p), g y = ∑ c ∈ range m, ∑ d ∈ range p, g (c * p + d) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

/-- The matrix multiplication tensor at `x = a * m + b`, `y = c * p + d`, `z = e * p + f`. -/
def T (m p x y z : ℕ) : ℤ := if x % m = y / p ∧ x / m = z / p ∧ y % p = z % p then 1 else 0

theorem T_apply (m p a b c d e f : ℕ) (hb : b < m) (hd : d < p) (hf : f < p) :
    T m p (a * m + b) (c * p + d) (e * p + f) = if b = c ∧ a = e ∧ d = f then 1 else 0 := by
  have hm : 0 < m := by omega
  have hp : 0 < p := by omega
  have e1 : (a * m + b) % m = b := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  have e2 : (a * m + b) / m = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hb, Nat.zero_add]
  have e3 : (c * p + d) / p = c := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hd, Nat.zero_add]
  have e4 : (e * p + f) / p = e := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hp, Nat.div_eq_of_lt hf, Nat.zero_add]
  have e5 : (c * p + d) % p = d := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hd]
  have e6 : (e * p + f) % p = f := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hf]
  simp only [T, e1, e2, e3, e4, e5, e6]

theorem expect_eq (n m p s D a b : ℕ) (ha : a < n) (hb : b < m) :
    (expectN s D (m * p) p a b p : ℤ) = ∑ z ∈ range (n * p), ∑ y ∈ range (m * p),
      (D : ℤ) * T m p (a * m + b) y z * ((2 : ℤ) ^ s) ^ y * (((2 : ℤ) ^ s) ^ (m * p)) ^ z := by
  rw [expectN_eq, sum_range_mul n p]
  simp only [sum_range_mul m p]
  -- the inner sums: only `c = b`, `d = f` contribute
  have inner : ∀ e < n, ∀ f < p, ∑ c ∈ range m, ∑ d ∈ range p,
      (D : ℤ) * T m p (a * m + b) (c * p + d) (e * p + f) * ((2 : ℤ) ^ s) ^ (c * p + d) *
        (((2 : ℤ) ^ s) ^ (m * p)) ^ (e * p + f) =
      if a = e then (D : ℤ) * ((2 : ℤ) ^ s) ^ (b * p + f) * (((2 : ℤ) ^ s) ^ (m * p)) ^ (e * p + f)
        else 0 := by
    intro e _ f hf
    have hT : ∀ c ∈ range m, ∀ d ∈ range p, (D : ℤ) * T m p (a * m + b) (c * p + d) (e * p + f) *
        ((2 : ℤ) ^ s) ^ (c * p + d) * (((2 : ℤ) ^ s) ^ (m * p)) ^ (e * p + f) =
        if d = f then (if b = c then (if a = e then (D : ℤ) * ((2 : ℤ) ^ s) ^ (c * p + d) *
          (((2 : ℤ) ^ s) ^ (m * p)) ^ (e * p + f) else 0) else 0) else 0 := by
      intro c _ d hd
      rw [T_apply m p a b c d e f hb (mem_range.mp hd) hf]
      by_cases h1 : b = c <;> by_cases h2 : a = e <;> by_cases h3 : d = f <;> simp [h1, h2, h3]
    rw [sum_congr rfl fun c hc => sum_congr rfl fun d hd => hT c hc d hd]
    simp only [sum_ite_eq', sum_ite_eq, mem_range, hb, hf, ite_true]
  rw [sum_congr rfl fun e he => sum_congr rfl fun f hf => inner e (mem_range.mp he) f (mem_range.mp hf)]
  rw [sum_comm]
  simp only [sum_ite_eq, mem_range, ha, ite_true]

/-! ## The bound -/

theorem coefN_le_l1 (k : ℕ) : ∀ l : List (ℕ × ℕ), coefN k l ≤ l1 l := by
  intro l
  induction l with
  | nil => simp [coefN, l1]
  | cons e l ih =>
    rw [coefN_cons]
    simp only [l1]
    show _ ≤ e.2 + l1 l
    split <;> omega

theorem abs_cz_le (lp ln : List (ℕ × ℕ)) (k : ℕ) : |cz lp ln k| ≤ ((l1 lp + l1 ln : ℕ) : ℤ) := by
  have h1 := coefN_le_l1 k lp
  have h2 := coefN_le_l1 k ln
  rw [cz, abs_le]
  push_cast
  constructor <;> omega

theorem abs_C_le (x y z : ℕ) : ∀ ts : List Term, |C ts x y z| ≤ (bnd ts : ℤ) := by
  intro ts
  induction ts with
  | nil => simp [C, bnd]
  | cons t ts ih =>
    have hsplit : C (t :: ts) x y z = cu t x * cv t y * cw t z + C ts x y z := by simp [C]
    rw [hsplit]
    simp only [bnd]
    show _ ≤ (((l1 t.up + l1 t.un) * (l1 t.vp + l1 t.vn) * (l1 t.wp + l1 t.wn) + bnd ts : ℕ) : ℤ)
    push_cast
    have hu := abs_cz_le t.up t.un x
    have hv := abs_cz_le t.vp t.vn y
    have hw := abs_cz_le t.wp t.wn z
    push_cast at hu hv hw
    have hprod : |cu t x * cv t y * cw t z| ≤
        ((l1 t.up : ℤ) + l1 t.un) * ((l1 t.vp : ℤ) + l1 t.vn) * ((l1 t.wp : ℤ) + l1 t.wn) := by
      rw [abs_mul, abs_mul]
      exact mul_le_mul (mul_le_mul hu hv (abs_nonneg _) (by positivity)) hw (abs_nonneg _)
        (by positivity)
    calc |cu t x * cv t y * cw t z + C ts x y z|
        ≤ |cu t x * cv t y * cw t z| + |C ts x y z| := abs_add_le _ _
      _ ≤ _ := add_le_add hprod ih

/-! ## Soundness -/

theorem intEq_eq : ∀ a b : ℤ, intEq a b = true → a = b
  | .ofNat a, .ofNat b, h => by simp only [intEq] at h; rw [Nat.eq_of_beq_eq_true h]
  | .negSucc a, .negSucc b, h => by simp only [intEq] at h; rw [Nat.eq_of_beq_eq_true h]
  | .ofNat _, .negSucc _, h => by simp [intEq] at h
  | .negSucc _, .ofNat _, h => by simp [intEq] at h

/-- **Soundness.** If the range check, the bound check and the slice checks for all `x < n * m`
succeed, then the scheme satisfies every equation of the matrix multiplication tensor, scaled by
`D`. -/
theorem tensor_of_checks (n m p s D : ℕ) (ts : List Term)
    (hr : rangeOk n m p ts = true) (hbd : boundOk s D ts = true)
    (hc : ∀ x, x < n * m → sliceOk m p s D ts x = true) :
    ∀ a < n, ∀ b < m, ∀ c < m, ∀ d < p, ∀ e < n, ∀ f < p,
      C ts (a * m + b) (c * p + d) (e * p + f) = if b = c ∧ a = e ∧ d = f then (D : ℤ) else 0 := by
  intro a ha b hb c hc' d hd e he f hf
  have hm : 0 < m := by omega
  have hrange := termRange_of_rangeOk n m p ts hr
  have hX : (0 : ℤ) < 2 ^ s := by positivity
  have hB : (bnd ts : ℤ) + D < 2 ^ s := by
    have h : Nat.blt (bnd ts + D) (1 <<< s) = true := hbd
    rw [Nat.blt_eq, Nat.shiftLeft_eq, Nat.one_mul] at h
    exact_mod_cast h
  have hx : a * m + b < n * m := by
    calc a * m + b < a * m + m := by omega
      _ = (a + 1) * m := by ring
      _ ≤ n * m := Nat.mul_le_mul_right m ha
  have hslice0 : intEq (slice s (m * p) (a * m + b) ts)
      (Int.ofNat (expectN s D (m * p) p ((a * m + b) / m) ((a * m + b) % m) p)) = true :=
    hc (a * m + b) hx
  have hslice := intEq_eq _ _ hslice0
  have hdiv : (a * m + b) / m = a := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hm, Nat.div_eq_of_lt hb, Nat.zero_add]
  have hmod : (a * m + b) % m = b := by rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hb]
  rw [hdiv, hmod] at hslice
  rw [slice_eq n m p s (a * m + b) ts hrange] at hslice
  have hE := expect_eq n m p s D a b ha hb
  rw [show (Int.ofNat (expectN s D (m * p) p a b p) : ℤ) = (expectN s D (m * p) p a b p : ℤ) from rfl,
    hE, ← sub_eq_zero, ← sum_sub_distrib] at hslice
  have hzero := digits_zero₂ (2 ^ s) hX (m * p) (n * p)
    (fun y z => C ts (a * m + b) y z - D * T m p (a * m + b) y z)
    (by
      intro y _ z _
      have h1 := abs_C_le (a * m + b) y z ts
      have h2 : |(D : ℤ) * T m p (a * m + b) y z| ≤ D := by
        unfold T; split <;> simp
      calc |C ts (a * m + b) y z - D * T m p (a * m + b) y z|
          ≤ |C ts (a * m + b) y z| + |(D : ℤ) * T m p (a * m + b) y z| := abs_sub _ _
        _ ≤ bnd ts + D := add_le_add h1 h2
        _ < 2 ^ s := hB)
    (by
      rw [← hslice]
      refine sum_congr rfl fun z _ => ?_
      rw [← sum_sub_distrib]
      exact sum_congr rfl fun y _ => by ring)
  have hy : c * p + d < m * p := by
    calc c * p + d < c * p + p := by omega
      _ = (c + 1) * p := by ring
      _ ≤ m * p := Nat.mul_le_mul_right p hc'
  have hz : e * p + f < n * p := by
    calc e * p + f < e * p + p := by omega
      _ = (e + 1) * p := by ring
      _ ≤ n * p := Nat.mul_le_mul_right p he
  have := hzero (c * p + d) hy (e * p + f) hz
  rw [sub_eq_zero, T_apply m p a b c d e f hb hd hf] at this
  rw [this]
  split <;> simp

end MatMul9x11x11
