import MoserMacLeod

open scoped ArithmeticFunction.Moebius BigOperators

/-!
This is the proved counterpart of `Challenge.lean`.  Comparator checks that
the declaration below has exactly the challenge's type and uses only the
permitted axioms listed in `comparator.json`.
-/

/-- Moser--MacLeod's estimate for the error in counting squarefree integers. -/
theorem MoserMacLeod.squarefree_error_lt_sqrt (x : ℝ) (hx : 0 < x) :
    |((∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (μ n) ^ 2 : ℤ) : ℝ) -
        6 / Real.pi ^ 2 * x| < √x := by
  rw [MoserMacLeod.sum_moebius_sq_eq_squarefreeCountNat]
  simpa [MoserMacLeod.R, MoserMacLeod.squarefreeCount,
    MoserMacLeod.density] using MoserMacLeod.abs_R_lt_sqrt x hx
