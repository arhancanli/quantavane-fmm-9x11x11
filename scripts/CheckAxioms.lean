module

import Solution

/-!
# Axiom check

`lake env lean scripts/CheckAxioms.lean` (after `lake build`) prints the axioms that the compared
theorems of `Solution.lean` depend on. Palomar permits only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms MatMul9x11x11.exists_tensor_decomposition
#print axioms MatMul9x11x11.exists_bilinear_algorithm
