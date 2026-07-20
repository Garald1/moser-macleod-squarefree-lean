import MoserMacLeod.FiniteTable

/-!
# Assembly lemmas for the Moser--MacLeod estimate

This file consumes the separately compiled finite certificate and then develops
those estimates from the paper which depend on it.  No computation is performed
here.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction ArithmeticFunction.Moebius BigOperators LSeries.notation
open Finset

noncomputable section

/-- The finite part of the real-variable theorem.  Notice that this is a
finite check of cells, not a check of individual real numbers. -/
theorem abs_R_lt_sqrt_of_lt_401 (x : ℝ) (hx : 1 ≤ x) (hx401 : x < 401) :
    |R x| < Real.sqrt x := by
  let N := ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hN1 : 1 ≤ N := by
    apply Nat.le_floor
    norm_num
    exact hx
  have hN401 : N < 401 := (Nat.floor_lt hx0).2 hx401
  have hNmem : N ∈ Icc 1 400 := by simp only [mem_Icc]; omega
  rcases finite_endpoint_certificate N hNmem with ⟨hleft, hright⟩
  have hleft' := endpointOK_sound (Nat.zero_lt_of_lt hN1) hleft
  have hright' := endpointOK_sound (Nat.succ_pos N) hright
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hcpos : 0 < density := density_bounds.1.trans' (by norm_num [densityLower])
  have hsmono : Real.sqrt (N : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
  have hupper : (squarefreeCountNat N : ℝ) - density * x < Real.sqrt x := by
    have := (abs_lt.mp hleft').2
    nlinarith
  have hsx1 : 1 ≤ Real.sqrt x := by
    simpa using Real.sqrt_le_sqrt hx
  have hsbx : Real.sqrt x ≤ Real.sqrt ((N : ℝ) + 1) :=
    Real.sqrt_le_sqrt hxN.le
  have hsb1 : 1 ≤ Real.sqrt ((N : ℝ) + 1) := by linarith
  have hsx2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  have hsb2 : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 :=
    Real.sq_sqrt (by positivity)
  have hfac :
      (Real.sqrt ((N : ℝ) + 1) - Real.sqrt x) *
          (Real.sqrt ((N : ℝ) + 1) + Real.sqrt x) = (N : ℝ) + 1 - x := by
    nlinarith
  have hdiff :
      Real.sqrt ((N : ℝ) + 1) - Real.sqrt x ≤ ((N : ℝ) + 1 - x) / 2 := by
    have hp := mul_le_mul_of_nonneg_left
      (show (2 : ℝ) ≤ Real.sqrt ((N : ℝ) + 1) + Real.sqrt x by linarith)
      (sub_nonneg.mpr hsbx)
    nlinarith
  have hcdiff :
      Real.sqrt ((N : ℝ) + 1) - Real.sqrt x ≤
        density * ((N : ℝ) + 1 - x) := by
    have hc : (1 / 2 : ℝ) < density := by
      have := density_bounds.1
      norm_num [densityLower] at this ⊢
      linarith
    have hnonneg : 0 ≤ (N : ℝ) + 1 - x := by linarith
    nlinarith [mul_nonneg (sub_nonneg.mpr hc.le) hnonneg]
  have hlower : -Real.sqrt x < (squarefreeCountNat N : ℝ) - density * x := by
    have := (abs_lt.mp hright').1
    norm_num [Nat.cast_succ] at this
    nlinarith
  change |(squarefreeCount x : ℝ) - density * x| < Real.sqrt x
  rw [abs_lt]
  simpa [squarefreeCount, N] using And.intro hlower hupper

/-- A variant of the Moser--MacLeod partial-sum estimate, obtained from the
simple bound `squarefreeCountNat_le_three_quarters`. -/
theorem abs_mertens_add_one_le (N : ℕ) (hN : 2 ≤ N) :
    |mertens N + 1| ≤ (N : ℝ) / 8 + 3 / 4 := by
  rw [mertens_eq_intCast]
  by_cases hlarge : 30 ≤ N
  · have hcount := abs_mertensInt_add_one_le_count N hlarge
    have hcount' : |(mertensInt N : ℝ) + 1| ≤ squarefreeCountNat (N / 6) := by
      exact_mod_cast hcount
    have hq := squarefreeCountNat_le_three_quarters (N / 6)
    have hdiv : (6 : ℝ) * (N / 6 : ℕ) ≤ N := by
      exact_mod_cast Nat.mul_div_le N 6
    nlinarith
  · have hsmall : (8 : ℤ) * |mertensInt N + 1| ≤ (N : ℤ) + 6 := by
      exact small_mertens_bound N hN (by omega)
    have hsmall' : (8 : ℝ) * |(mertensInt N : ℝ) + 1| ≤ (N : ℝ) + 6 := by
      exact_mod_cast hsmall
    nlinarith

theorem abs_mertens_le (N : ℕ) (hN : 1 ≤ N) :
    |mertens N| ≤ (N : ℝ) / 8 + 7 / 4 := by
  by_cases h : N = 1
  · subst N
    norm_num [mertens, muR, ArithmeticFunction.moebius_apply_one]
  · have h2 : 2 ≤ N := by omega
    have hM := abs_mertens_add_one_le N h2
    calc
      |mertens N| = |(mertens N + 1) - 1| := by ring_nf
      _ ≤ |mertens N + 1| + |(1 : ℝ)| := abs_sub _ _
      _ ≤ (N : ℝ) / 8 + 7 / 4 := by norm_num at ⊢; linarith

theorem sum_abs_muR_eq_count (N : ℕ) :
    (∑ d ∈ Icc 1 N, |muR d|) = squarefreeCountNat N := by
  simp only [squarefreeCountNat, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  apply sum_congr rfl
  intro d hd
  rcases ArithmeticFunction.moebius_eq_or d with h0 | h1 | hn
  · simp [muR, h0]
  · simp [muR, h1]
  · simp [muR, hn]

/-- If `0 ≤ θ_d ≤ 1`, the weighted Möbius sum is bounded by the
larger of the numbers of `+1` and `-1` values. -/
theorem abs_sum_muR_mul_le (N : ℕ) (theta : ℕ → ℝ)
    (htheta : ∀ d ∈ Icc 1 N, 0 ≤ theta d ∧ theta d ≤ 1) :
    |∑ d ∈ Icc 1 N, muR d * theta d| ≤
      squarefreeCountNat N / 2 + |mertens N| / 2 := by
  have hupper :
      (∑ d ∈ Icc 1 N, muR d * theta d) ≤
        ∑ d ∈ Icc 1 N, (|muR d| + muR d) / 2 := by
    apply sum_le_sum
    intro d hd
    rcases ArithmeticFunction.moebius_eq_or d with h0 | h1 | hn
    · simp [muR, h0]
    · simp [muR, h1]
      exact (htheta d hd).2
    · simp [muR, hn]
      exact (htheta d hd).1
  have hlower :
      -(∑ d ∈ Icc 1 N, (|muR d| - muR d) / 2) ≤
        ∑ d ∈ Icc 1 N, muR d * theta d := by
    rw [← sum_neg_distrib]
    apply sum_le_sum
    intro d hd
    rcases ArithmeticFunction.moebius_eq_or d with h0 | h1 | hn
    · simp [muR, h0]
    · simp [muR, h1]
      exact (htheta d hd).1
    · simp [muR, hn]
      exact (htheta d hd).2
  have hQ := sum_abs_muR_eq_count N
  have hM : (∑ d ∈ Icc 1 N, muR d) = mertens N := rfl
  have hplus :
      (∑ d ∈ Icc 1 N, (|muR d| + muR d) / 2) =
        squarefreeCountNat N / 2 + mertens N / 2 := by
    calc
      _ = ∑ d ∈ Icc 1 N, (|muR d| / 2 + muR d / 2) := by
        apply sum_congr rfl
        intro d hd
        ring
      _ = (∑ d ∈ Icc 1 N, |muR d|) / 2 +
          (∑ d ∈ Icc 1 N, muR d) / 2 := by
        simp only [sum_add_distrib, sum_div]
      _ = _ := by rw [hQ, hM]
  have hminus :
      (∑ d ∈ Icc 1 N, (|muR d| - muR d) / 2) =
        squarefreeCountNat N / 2 - mertens N / 2 := by
    calc
      _ = ∑ d ∈ Icc 1 N, (|muR d| / 2 - muR d / 2) := by
        apply sum_congr rfl
        intro d hd
        ring
      _ = (∑ d ∈ Icc 1 N, |muR d|) / 2 -
          (∑ d ∈ Icc 1 N, muR d) / 2 := by
        simp only [sum_sub_distrib, sum_div]
      _ = _ := by rw [hQ, hM]
  rw [abs_le]
  constructor
  · calc
      -(squarefreeCountNat N / 2 + |mertens N| / 2) ≤
          -(∑ d ∈ Icc 1 N, (|muR d| - muR d) / 2) := by
        rw [hminus]
        nlinarith [neg_le_abs (mertens N)]
      _ ≤ _ := hlower
  · calc
      _ ≤ ∑ d ∈ Icc 1 N, (|muR d| + muR d) / 2 := hupper
      _ ≤ squarefreeCountNat N / 2 + |mertens N| / 2 := by
        rw [hplus]
        nlinarith [le_abs_self (mertens N)]

end
end MoserMacLeod
