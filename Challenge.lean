import Mathlib

open scoped ArithmeticFunction.Moebius BigOperators

/-!
This file is the trusted, mathlib-only statement presented to a reviewer or to
`leanprover/comparator`.  The `sorry` is intentional: the proof lives in
`Solution.lean`, which states exactly the same theorem.
-/

/-- Moser--MacLeod's estimate for the error in counting squarefree integers. -/
theorem MoserMacLeod.squarefree_error_lt_sqrt (x : ℝ) (hx : 0 < x) :
    |((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n) ^ 2 : ℤ) : ℝ) -
        6 / Real.pi ^ 2 * x| < √x := by
  sorry
