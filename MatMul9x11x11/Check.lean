module

@[expose] public section

namespace MatMul9x11x11

/-- One term of a scheme in sparse form. Each factor is given by two lists of pairs
`(position, absolute value)`: its positive entries and its negative entries. -/
structure Term where
  up : List (Nat × Nat)
  un : List (Nat × Nat)
  vp : List (Nat × Nat)
  vn : List (Nat × Nat)
  wp : List (Nat × Nat)
  wn : List (Nat × Nat)

/-- The packed integer `∑ c * 2 ^ (sh * k)` over the entries `(k, c)` of a list. -/
def packN (sh : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | e :: l => Nat.add (Nat.shiftLeft e.2 (Nat.mul sh e.1)) (packN sh l)

/-- The sum of the entries listed at position `k`. -/
def coefN (k : Nat) : List (Nat × Nat) → Nat
  | [] => 0
  | e :: l => cond (Nat.beq e.1 k) (Nat.add e.2 (coefN k l)) (coefN k l)

/-- Equality test of integers. -/
def intEq : Int → Int → Bool
  | .ofNat a, .ofNat b => Nat.beq a b
  | .negSucc a, .negSucc b => Nat.beq a b
  | _, _ => false

/-- The slice of a scheme at position `x` of the first factor, packed:
`∑ᵢ uᵢ[x] * (∑_y vᵢ[y] 2^(s y)) * (∑_z wᵢ[z] 2^(s mp z))`. Terms with `uᵢ[x] = 0` are skipped. -/
def slice (s mp x : Nat) : List Term → Int
  | [] => 0
  | t :: ts =>
    cond (Nat.beq (coefN x t.up) (coefN x t.un)) (slice s mp x ts)
      (Int.add (Int.mul (Int.subNatNat (coefN x t.up) (coefN x t.un))
          (Int.mul (Int.subNatNat (packN s t.vp) (packN s t.vn))
            (Int.subNatNat (packN (Nat.mul s mp) t.wp) (packN (Nat.mul s mp) t.wn))))
        (slice s mp x ts))

/-- The packed slice of `D` times the matrix multiplication tensor at position `x = a * m + b`:
the entries `y = b * p + d`, `z = a * p + d` for `d < p`. -/
def expectN (s D mp p a b : Nat) : Nat → Nat
  | 0 => 0
  | d + 1 => Nat.add (Nat.shiftLeft D (Nat.mul s (Nat.add (Nat.add (Nat.mul b p) d)
      (Nat.mul mp (Nat.add (Nat.mul a p) d))))) (expectN s D mp p a b d)

/-- The check of the slice at position `x`. -/
def sliceOk (m p s D : Nat) (ts : List Term) (x : Nat) : Bool :=
  intEq (slice s (Nat.mul m p) x ts) (.ofNat (expectN s D (Nat.mul m p) p (Nat.div x m) (Nat.mod x m) p))

/-- Every position of the list is below `N`. -/
def posLt (N : Nat) (l : List (Nat × Nat)) : Bool := l.all fun e => Nat.blt e.1 N

/-- The positions of a term are inside the factors: `n * m`, `m * p` and `n * p` entries. -/
def termOk (n m p : Nat) (t : Term) : Bool :=
  posLt (Nat.mul n m) t.up && posLt (Nat.mul n m) t.un && posLt (Nat.mul m p) t.vp &&
    posLt (Nat.mul m p) t.vn && posLt (Nat.mul n p) t.wp && posLt (Nat.mul n p) t.wn

/-- The range check of all terms. -/
def rangeOk (n m p : Nat) (ts : List Term) : Bool := ts.all (termOk n m p)

/-- The sum of the absolute values listed. -/
def l1 : List (Nat × Nat) → Nat
  | [] => 0
  | e :: l => Nat.add e.2 (l1 l)

/-- `∑ₜ ‖uₜ‖₁ ‖vₜ‖₁ ‖wₜ‖₁`, a bound for every coefficient of the expanded scheme. -/
def bnd : List Term → Nat
  | [] => 0
  | t :: ts => Nat.add (Nat.mul (Nat.mul (Nat.add (l1 t.up) (l1 t.un)) (Nat.add (l1 t.vp) (l1 t.vn)))
      (Nat.add (l1 t.wp) (l1 t.wn))) (bnd ts)

/-- The bound check: `bnd + D < 2 ^ s`, so that no slot of the packed integers overflows. -/
def boundOk (s D : Nat) (ts : List Term) : Bool := Nat.blt (Nat.add (bnd ts) D) (Nat.shiftLeft 1 s)

end MatMul9x11x11
