import MoserMacLeod.Infrastructure

/-!
# Completion of the Moser--MacLeod square-root estimate

This file proves the explicit Mobius-series tail bound, the square-divisor
formula for the squarefree count, the exact error decomposition, and the final
real-variable theorem. See `MOSER_MACLEOD_LEAN_COMPANION.md` for a complete
human proof and a theorem-by-theorem correspondence with the 1966 paper.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction ArithmeticFunction.Moebius BigOperators
open Filter Finset

def augMu (n : ℕ) : ℝ := if n = 0 then 1 else muR n

theorem sum_range_augMu (n : ℕ) (hn : 1 ≤ n) :
    (∑ i ∈ range n, augMu i) = mertens (n - 1) + 1 := by
  have hset : range n = insert 0 (Icc 1 (n - 1)) := by
    ext i
    simp only [mem_range, mem_insert, mem_Icc]
    omega
  rw [hset, sum_insert (by simp)]
  simp only [augMu, if_pos, mertens]
  have hsum :
      (∑ i ∈ Icc 1 (n - 1), if i = 0 then 1 else muR i) =
        ∑ i ∈ Icc 1 (n - 1), muR i := by
    apply sum_congr rfl
    intro i hi
    rw [if_neg]
    exact (Nat.zero_lt_of_lt (mem_Icc.mp hi).1).ne'
  rw [hsum]
  ring

theorem diff_sq_nonneg (i : ℕ) (hi : 1 ≤ i) :
    0 ≤ (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) := by
  have hp : (0 : ℝ) < i := by exact_mod_cast (Nat.zero_lt_of_lt hi)
  have hp1 : (0 : ℝ) < i + 1 := by positivity
  apply sub_nonneg.mpr
  gcongr
  exact Nat.le_succ i

theorem sum_Ico_diff (f : ℕ → ℝ) (a b : ℕ) (hab : a ≤ b) :
    (∑ i ∈ Ico a b, (f i - f (i + 1))) = f a - f b := by
  rw [sum_Ico_eq_sub (fun i ↦ f i - f (i + 1)) hab]
  rw [sum_range_sub', sum_range_sub']
  ring

theorem inv_sq_le_telescoping (i : ℕ) (hi : 2 ≤ i) :
    1 / (i : ℝ) ^ 2 ≤ 1 / ((i - 1 : ℕ) : ℝ) - 1 / (i : ℝ) := by
  have hi0 : (0 : ℝ) < i := by positivity
  have him10 : (0 : ℝ) < (i - 1 : ℕ) := by exact_mod_cast (by omega : 0 < i - 1)
  have hcast : ((i - 1 : ℕ) : ℝ) = (i : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]
    norm_num
  have heq :
      1 / ((i - 1 : ℕ) : ℝ) - 1 / (i : ℝ) =
        1 / ((i : ℝ) * (i - 1 : ℕ)) := by
    field_simp
    nlinarith [hcast]
  rw [heq]
  apply (div_le_div_iff₀ (sq_pos_of_pos hi0) (mul_pos hi0 him10)).2
  nlinarith [him10]

theorem sum_Ico_inv_sq_le (a b : ℕ) (ha : 2 ≤ a) :
    (∑ i ∈ Ico a b, 1 / (i : ℝ) ^ 2) ≤ 1 / ((a - 1 : ℕ) : ℝ) := by
  by_cases hab : a ≤ b
  · calc
      _ ≤ ∑ i ∈ Ico a b,
          (1 / ((i - 1 : ℕ) : ℝ) - 1 / (i : ℝ)) := by
        apply sum_le_sum
        intro i hi
        exact inv_sq_le_telescoping i (ha.trans (mem_Ico.mp hi).1)
      _ = 1 / ((a - 1 : ℕ) : ℝ) - 1 / ((b - 1 : ℕ) : ℝ) := by
        simpa using sum_Ico_diff (fun i ↦ 1 / ((i - 1 : ℕ) : ℝ)) a b hab
      _ ≤ 1 / ((a - 1 : ℕ) : ℝ) := by
        have : 0 ≤ 1 / ((b - 1 : ℕ) : ℝ) := by positivity
        linarith
  · rw [Ico_eq_empty (by omega)]
    positivity

theorem sum_Ico_diff_sq_le (a b : ℕ) (ha : 1 ≤ a) :
    (∑ i ∈ Ico a b,
      (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) ≤
        1 / (a : ℝ) ^ 2 := by
  by_cases hab : a ≤ b
  · rw [sum_Ico_diff (fun i ↦ 1 / (i : ℝ) ^ 2) a b hab]
    have : 0 ≤ 1 / (b : ℝ) ^ 2 := by positivity
    linarith
  · rw [Ico_eq_empty (by omega)]
    positivity

theorem mul_diff_sq_identity (i : ℕ) (hi : 1 ≤ i) :
    (i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) =
      (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ)) +
        1 / ((i + 1 : ℕ) : ℝ) ^ 2 := by
  have hi0 : (i : ℝ) ≠ 0 := by positivity
  have hi10 : ((i + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp
  norm_num [Nat.cast_add, Nat.cast_one]
  ring

theorem sum_Ico_mul_diff_sq_le (a b : ℕ) (ha : 1 ≤ a) :
    (∑ i ∈ Ico a b,
      (i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) ≤
        2 / (a : ℝ) := by
  have hrewrite :
      (∑ i ∈ Ico a b,
        (i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) =
      (∑ i ∈ Ico a b, (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ))) +
        ∑ i ∈ Ico a b, 1 / ((i + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    exact mul_diff_sq_identity i (ha.trans (mem_Ico.mp hi).1)
  rw [hrewrite]
  by_cases hab : a ≤ b
  · have htel :
        (∑ i ∈ Ico a b, (1 / (i : ℝ) - 1 / ((i + 1 : ℕ) : ℝ))) =
          1 / (a : ℝ) - 1 / (b : ℝ) :=
      sum_Ico_diff (fun i ↦ 1 / (i : ℝ)) a b hab
    have hsquare :
        (∑ i ∈ Ico a b, 1 / ((i + 1 : ℕ) : ℝ) ^ 2) ≤ 1 / (a : ℝ) := by
      rw [Finset.sum_Ico_add' (α := ℕ) (fun i ↦ 1 / (i : ℝ) ^ 2) a b 1]
      simpa [Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using
        sum_Ico_inv_sq_le (a + 1) (b + 1) (by omega)
    rw [htel]
    have hb0 : 0 ≤ 1 / (b : ℝ) := by positivity
    have htwo : 2 / (a : ℝ) = 1 / (a : ℝ) + 1 / (a : ℝ) := by ring
    rw [htwo]
    linarith
  · rw [Ico_eq_empty (by omega)]
    simp
    positivity

theorem weighted_diff_sq_le (a b : ℕ) (ha : 1 ≤ a) :
    (∑ i ∈ Ico a b,
      (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
        ((i : ℝ) / 8 + 3 / 4)) ≤
      1 / (4 * (a : ℝ)) + 3 / (4 * (a : ℝ) ^ 2) := by
  have hrewrite :
      (∑ i ∈ Ico a b,
        (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
          ((i : ℝ) / 8 + 3 / 4)) =
        (∑ i ∈ Ico a b,
          (i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) / 8 +
        3 * (∑ i ∈ Ico a b,
          (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) / 4 := by
    calc
      _ = ∑ i ∈ Ico a b,
          ((i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) / 8 +
            3 * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) / 4) := by
        apply sum_congr rfl
        intro i hi
        ring
      _ = _ := by
        rw [sum_add_distrib]
        have hfirst :
            (∑ i ∈ Ico a b,
              ((i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) / 8)) =
              (∑ i ∈ Ico a b,
                (i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) / 8 := by
          rw [sum_div]
        have hsecond :
            (∑ i ∈ Ico a b,
              (3 * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) / 4)) =
              3 * (∑ i ∈ Ico a b,
                (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) / 4 := by
          calc
            _ = (∑ i ∈ Ico a b,
                3 * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) / 4 := by
              rw [sum_div]
            _ = _ := by rw [mul_sum]
        rw [hfirst, hsecond]
  rw [hrewrite]
  have h1 := sum_Ico_mul_diff_sq_le a b ha
  have h2 := sum_Ico_diff_sq_le a b ha
  have ha0 : (0 : ℝ) < a := by positivity
  calc
    _ ≤ (2 / (a : ℝ)) / 8 + 3 * (1 / (a : ℝ) ^ 2) / 4 := by
      gcongr
    _ = 1 / (4 * (a : ℝ)) + 3 / (4 * (a : ℝ) ^ 2) := by ring

theorem finite_tail_bound (m n : ℕ) (hm : 2 ≤ m) (hmn : m + 1 < n) :
    |∑ i ∈ Ico (m + 1) n, muR i / (i : ℝ) ^ 2| ≤
      (((n - 1 : ℕ) : ℝ) / 8 + 3 / 4) / ((n - 1 : ℕ) : ℝ) ^ 2 +
        3 / (8 * ((m + 1 : ℕ) : ℝ)) +
          3 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2) := by
  have hparts := Finset.sum_Ico_by_parts
    (fun i : ℕ ↦ 1 / (i : ℝ) ^ 2) augMu hmn
  simp only [smul_eq_mul] at hparts
  rw [sum_range_augMu n (by omega), sum_range_augMu (m + 1) (by omega)] at hparts
  have hsumpart :
      (∑ i ∈ Ico (m + 1) (n - 1),
        (1 / ((i + 1 : ℕ) : ℝ) ^ 2 - 1 / (i : ℝ) ^ 2) *
          ∑ j ∈ range (i + 1), augMu j) =
      ∑ i ∈ Ico (m + 1) (n - 1),
        (1 / ((i + 1 : ℕ) : ℝ) ^ 2 - 1 / (i : ℝ) ^ 2) *
          (mertens i + 1) := by
    apply sum_congr rfl
    intro i hi
    rw [sum_range_augMu (i + 1) (by omega)]
    simp
  rw [hsumpart] at hparts
  have hlhs :
      (∑ i ∈ Ico (m + 1) n, (1 / (i : ℝ) ^ 2) * augMu i) =
        ∑ i ∈ Ico (m + 1) n, muR i / (i : ℝ) ^ 2 := by
    apply sum_congr rfl
    intro i hi
    have hi0 : i ≠ 0 :=
      (lt_of_lt_of_le (Nat.zero_lt_succ m) (mem_Ico.mp hi).1).ne'
    rw [augMu, if_neg hi0]
    ring
  rw [hlhs] at hparts
  have hsumflip :
      -(∑ i ∈ Ico (m + 1) (n - 1),
        (1 / ((i + 1 : ℕ) : ℝ) ^ 2 - 1 / (i : ℝ) ^ 2) *
          (mertens i + 1)) =
      ∑ i ∈ Ico (m + 1) (n - 1),
        (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
          (mertens i + 1) := by
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  have hid :
      (∑ i ∈ Ico (m + 1) n, muR i / (i : ℝ) ^ 2) =
        (1 / ((n - 1 : ℕ) : ℝ) ^ 2) * (mertens (n - 1) + 1) -
        (1 / ((m + 1 : ℕ) : ℝ) ^ 2) * (mertens m + 1) +
        ∑ i ∈ Ico (m + 1) (n - 1),
          (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
            (mertens i + 1) := by
    rw [hparts]
    simp only [Nat.add_sub_cancel]
    rw [sub_eq_add_neg, hsumflip]
  rw [hid]
  have hn1 : 2 ≤ n - 1 := by omega
  have hboundary := abs_mertens_add_one_le (n - 1) hn1
  have hbase := abs_mertens_add_one_le m hm
  have hsumabs :
      |∑ i ∈ Ico (m + 1) (n - 1),
        (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
          (mertens i + 1)| ≤
      ∑ i ∈ Ico (m + 1) (n - 1),
        (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
          ((i : ℝ) / 8 + 3 / 4) := by
    calc
      _ ≤ ∑ i ∈ Ico (m + 1) (n - 1),
          |(1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
            (mertens i + 1)| := abs_sum_le_sum_abs _ _
      _ ≤ _ := by
        apply sum_le_sum
        intro i hi
        have hmi : m + 1 ≤ i := (mem_Ico.mp hi).1
        have hi2 : 2 ≤ i := hm.trans ((Nat.le_succ m).trans hmi)
        have hdiff := diff_sq_nonneg i (by omega)
        rw [abs_mul, abs_of_nonneg hdiff]
        exact mul_le_mul_of_nonneg_left (abs_mertens_add_one_le i hi2) hdiff
  have hweighted := weighted_diff_sq_le (m + 1) (n - 1) (by omega)
  have hboundary' :
      |(1 / ((n - 1 : ℕ) : ℝ) ^ 2) * (mertens (n - 1) + 1)| ≤
        (((n - 1 : ℕ) : ℝ) / 8 + 3 / 4) / ((n - 1 : ℕ) : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / ((n - 1 : ℕ) : ℝ) ^ 2)]
    calc
      _ ≤ (1 / ((n - 1 : ℕ) : ℝ) ^ 2) *
          (((n - 1 : ℕ) : ℝ) / 8 + 3 / 4) := by
        exact mul_le_mul_of_nonneg_left hboundary (by positivity)
      _ = _ := by ring
  have hbase' :
      |(1 / ((m + 1 : ℕ) : ℝ) ^ 2) * (mertens m + 1)| ≤
        ((m : ℝ) / 8 + 3 / 4) / ((m + 1 : ℕ) : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / ((m + 1 : ℕ) : ℝ) ^ 2)]
    calc
      _ ≤ (1 / ((m + 1 : ℕ) : ℝ) ^ 2) * ((m : ℝ) / 8 + 3 / 4) := by
        exact mul_le_mul_of_nonneg_left hbase (by positivity)
      _ = _ := by ring
  have htri :
      |(1 / ((n - 1 : ℕ) : ℝ) ^ 2) * (mertens (n - 1) + 1) -
          (1 / ((m + 1 : ℕ) : ℝ) ^ 2) * (mertens m + 1) +
          ∑ i ∈ Ico (m + 1) (n - 1),
            (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
              (mertens i + 1)| ≤
        |(1 / ((n - 1 : ℕ) : ℝ) ^ 2) * (mertens (n - 1) + 1)| +
        |(1 / ((m + 1 : ℕ) : ℝ) ^ 2) * (mertens m + 1)| +
        |∑ i ∈ Ico (m + 1) (n - 1),
          (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
            (mertens i + 1)| := by
    calc
      _ ≤ |(1 / ((n - 1 : ℕ) : ℝ) ^ 2) * (mertens (n - 1) + 1) -
          (1 / ((m + 1 : ℕ) : ℝ) ^ 2) * (mertens m + 1)| +
          |∑ i ∈ Ico (m + 1) (n - 1),
            (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
              (mertens i + 1)| := abs_add_le _ _
      _ ≤ _ := by
        gcongr
        exact abs_sub _ _
  calc
    _ ≤ _ := htri
    _ ≤ (((n - 1 : ℕ) : ℝ) / 8 + 3 / 4) / ((n - 1 : ℕ) : ℝ) ^ 2 +
        (((m : ℝ) / 8 + 3 / 4) / ((m + 1 : ℕ) : ℝ) ^ 2) +
        (1 / (4 * ((m + 1 : ℕ) : ℝ)) +
          3 / (4 * ((m + 1 : ℕ) : ℝ) ^ 2)) := by
      exact add_le_add (add_le_add hboundary' hbase') (hsumabs.trans hweighted)
    _ ≤ _ := by
      have hm0 : (0 : ℝ) < m + 1 := by positivity
      have hrem :
          (((m : ℝ) / 8 + 3 / 4) / ((m + 1 : ℕ) : ℝ) ^ 2) +
            (1 / (4 * ((m + 1 : ℕ) : ℝ)) +
              3 / (4 * ((m + 1 : ℕ) : ℝ) ^ 2)) ≤
            3 / (8 * ((m + 1 : ℕ) : ℝ)) +
              3 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2) := by
        norm_num [Nat.cast_add, Nat.cast_one]
        field_simp
        nlinarith
      linarith

theorem hasSum_mu_tail (m : ℕ) :
    HasSum (fun k : ℕ ↦ muR (k + (m + 1)) / ((k + (m + 1) : ℕ) : ℝ) ^ 2)
      (density - ∑ i ∈ Icc 1 m, muR i / (i : ℝ) ^ 2) := by
  have h := (hasSum_nat_add_iff' (m + 1)).2 hasSum_mu_div_sq
  convert h using 1
  · have hset : range (m + 1) = insert 0 (Icc 1 m) := by
      ext i
      simp only [mem_range, mem_insert, mem_Icc]
      omega
    rw [hset, sum_insert (by simp)]
    simp only [if_pos, zero_add]
    congr 1
    apply sum_congr rfl
    intro i hi
    rw [if_neg]
    exact (Nat.zero_lt_of_lt (mem_Icc.mp hi).1).ne'

theorem abs_mu_tail_le (m : ℕ) (hm : 2 ≤ m) :
    |density - ∑ i ∈ Icc 1 m, muR i / (i : ℝ) ^ 2| ≤
      3 / (8 * ((m + 1 : ℕ) : ℝ)) +
        3 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2) := by
  let C : ℝ := 3 / (8 * ((m + 1 : ℕ) : ℝ)) +
    3 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2)
  let s : ℕ → ℝ := fun k ↦ muR (k + (m + 1)) / ((k + (m + 1) : ℕ) : ℝ) ^ 2
  have hs : HasSum s (density - ∑ i ∈ Icc 1 m, muR i / (i : ℝ) ^ 2) := by
    exact hasSum_mu_tail m
  have hpartial (n : ℕ) :
      (∑ k ∈ range n, s k) =
        ∑ i ∈ Ico (m + 1) (n + (m + 1)), muR i / (i : ℝ) ^ 2 := by
    simpa only [range_eq_Ico, zero_add, s] using
      (Finset.sum_Ico_add' (α := ℕ)
        (fun i ↦ muR i / (i : ℝ) ^ 2) 0 n (m + 1))
  have hleft :
      Tendsto (fun n ↦ |∑ k ∈ range n, s k|) atTop
        (nhds |density - ∑ i ∈ Icc 1 m, muR i / (i : ℝ) ^ 2|) :=
    hs.tendsto_sum_nat.abs
  have hk : Tendsto (fun n : ℕ ↦ (n : ℝ) + m) atTop atTop :=
    Filter.tendsto_atTop_add_const_right atTop (m : ℝ) tendsto_natCast_atTop_atTop
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ) + m)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hk
  have hboundary :
      Tendsto (fun n : ℕ ↦
        (((n : ℝ) + m) / 8 + 3 / 4) / ((n : ℝ) + m) ^ 2) atTop (nhds 0) := by
    have hc1 : Tendsto (fun _ : ℕ ↦ (1 / 8 : ℝ)) atTop (nhds (1 / 8 : ℝ)) :=
      tendsto_const_nhds
    have hc2 : Tendsto (fun _ : ℕ ↦ (3 / 4 : ℝ)) atTop (nhds (3 / 4 : ℝ)) :=
      tendsto_const_nhds
    have hlim := (hc1.mul hinv).add (hc2.mul (hinv.pow 2))
    convert hlim using 1
    · funext n
      by_cases hn : (n : ℝ) + m = 0
      · simp [hn]
      · field_simp
    · norm_num
  have hright :
      Tendsto (fun n : ℕ ↦
        (((n : ℝ) + m) / 8 + 3 / 4) / ((n : ℝ) + m) ^ 2 + C)
        atTop (nhds C) := by
    convert hboundary.add tendsto_const_nhds using 1
    all_goals simp
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hpartial]
  have hfin := finite_tail_bound m (n + (m + 1)) hm (by omega)
  change |∑ i ∈ Ico (m + 1) (n + (m + 1)), muR i / (i : ℝ) ^ 2| ≤
    (((n : ℝ) + m) / 8 + 3 / 4) / ((n : ℝ) + m) ^ 2 + C
  convert hfin using 1
  all_goals norm_num [C, Nat.cast_add, Nat.cast_one]
  all_goals ring

theorem sum_moebius_square_divisors (n : ℕ) (hn : 0 < n) :
    (∑ d ∈ n.divisors, if d * d ∣ n then ArithmeticFunction.moebius d else 0) =
      if Squarefree n then 1 else 0 := by
  classical
  let s := n.divisors.filter (fun d ↦ Squarefree d ∧ d * d ∣ n)
  have hreduce :
      (∑ d ∈ n.divisors, if d * d ∣ n then ArithmeticFunction.moebius d else 0) =
        ∑ d ∈ s, ArithmeticFunction.moebius d := by
    rw [sum_ite]
    simp only [sum_const_zero, add_zero, s]
    symm
    apply sum_subset
    · intro d hd
      simp only [mem_filter] at hd ⊢
      exact ⟨hd.1, hd.2.2⟩
    · intro d hdall hdnot
      simp only [mem_filter] at hdall hdnot
      apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
      intro hsd
      exact hdnot ⟨hdall.1, hsd, hdall.2⟩
  rw [hreduce]
  by_cases hsqn : Squarefree n
  · rw [if_pos hsqn]
    have hsone : s = {1} := by
      ext d
      simp only [s, mem_filter, Nat.mem_divisors, mem_singleton]
      constructor
      · rintro ⟨hddiv, hsd, hd2⟩
        exact Nat.isUnit_iff.mp (hsqn d (by simpa [pow_two] using hd2))
      · rintro rfl
        simp [hn.ne']
    rw [hsone]
    simp
  · rw [if_neg hsqn]
    rw [Nat.squarefree_iff_prime_squarefree] at hsqn
    push_neg at hsqn
    obtain ⟨p, hp, hp2n⟩ := hsqn
    let g : (d : ℕ) → d ∈ s → ℕ := fun d _ ↦ if p ∣ d then d / p else p * d
    apply Finset.sum_involution g
    · intro d hd
      have hdm := mem_filter.mp hd
      have hsd : Squarefree d := hdm.2.1
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hdm.1
      by_cases hpd : p ∣ d
      · have hcop : p.Coprime (d / p) := by
          apply Nat.coprime_of_squarefree_mul
          rw [Nat.mul_div_cancel' hpd]
          exact hsd
        have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
        simp only [g, hpd, ↓reduceIte]
        have hdEq : d = p * (d / p) := (Nat.mul_div_cancel' hpd).symm
        have hmud : ArithmeticFunction.moebius d =
            ArithmeticFunction.moebius (p * (d / p)) := congrArg _ hdEq
        rw [hmud, hmu, ArithmeticFunction.moebius_apply_prime hp]
        ring
      · have hcop : p.Coprime d := (hp.coprime_iff_not_dvd).2 hpd
        have hmu := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop
        simp only [g, hpd, ↓reduceIte, hmu, ArithmeticFunction.moebius_apply_prime hp]
        ring
    · intro d hd hmu
      have hdm := mem_filter.mp hd
      have hdpos : 0 < d := Nat.pos_of_mem_divisors hdm.1
      by_cases hpd : p ∣ d
      · simp only [g, hpd, ↓reduceIte]
        exact ne_of_lt (Nat.div_lt_self hdpos hp.one_lt)
      · simp only [g, hpd, ↓reduceIte]
        exact ne_of_gt (lt_mul_of_one_lt_left hdpos hp.one_lt)
    · intro d hd
      have hdm := mem_filter.mp hd
      have hsd : Squarefree d := hdm.2.1
      by_cases hpd : p ∣ d
      · have hcop : p.Coprime (d / p) := by
          apply Nat.coprime_of_squarefree_mul
          rw [Nat.mul_div_cancel' hpd]
          exact hsd
        have hnpdiv : ¬p ∣ d / p := (hp.coprime_iff_not_dvd).1 hcop
        change (if p ∣ (if p ∣ d then d / p else p * d) then
          (if p ∣ d then d / p else p * d) / p
          else p * (if p ∣ d then d / p else p * d)) = d
        simp [hpd, hnpdiv, Nat.mul_div_cancel' hpd]
      · have hpdiv : p ∣ p * d := dvd_mul_right p d
        change (if p ∣ (if p ∣ d then d / p else p * d) then
          (if p ∣ d then d / p else p * d) / p
          else p * (if p ∣ d then d / p else p * d)) = d
        simp [hpd, hpdiv, Nat.mul_div_cancel_left d hp.pos]
    · intro d hd
      have hdm := mem_filter.mp hd
      have hsd : Squarefree d := hdm.2.1
      have hd2n : d * d ∣ n := hdm.2.2
      have hn0 : n ≠ 0 := hn.ne'
      by_cases hpd : p ∣ d
      · have hdiv : d / p ∣ d := Nat.div_dvd_of_dvd hpd
        have hsq : Squarefree (d / p) := hsd.squarefree_of_dvd hdiv
        have hg2n : (d / p) * (d / p) ∣ n :=
          (mul_dvd_mul hdiv hdiv).trans hd2n
        have hgdn : d / p ∣ n :=
          (dvd_mul_right (d / p) (d / p)).trans hg2n
        simp only [g, hpd, ↓reduceIte]
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hgdn, hn0⟩, hsq, hg2n⟩
      · have hcop : p.Coprime d := (hp.coprime_iff_not_dvd).2 hpd
        have hsq : Squarefree (p * d) := (Nat.squarefree_mul hcop).2 ⟨hp.squarefree, hsd⟩
        have hcop2 : (p * p).Coprime (d * d) := by
          simpa [pow_two] using hcop.pow 2 2
        have hg2n : (p * d) * (p * d) ∣ n := by
          have hprod := hcop2.mul_dvd_of_dvd_of_dvd hp2n hd2n
          simpa [mul_assoc, mul_left_comm, mul_comm] using hprod
        have hgdn : p * d ∣ n := (dvd_mul_right (p * d) (p * d)).trans hg2n
        simp only [g, hpd, ↓reduceIte]
        exact mem_filter.mpr ⟨Nat.mem_divisors.mpr ⟨hgdn, hn0⟩, hsq, hg2n⟩

theorem squarefreeCountNat_floor_formula (N : ℕ) :
    (squarefreeCountNat N : ℤ) =
      ∑ d ∈ Icc 1 N.sqrt,
        ArithmeticFunction.moebius d * (N / (d * d) : ℕ) := by
  classical
  have hq :
      (squarefreeCountNat N : ℤ) =
        ∑ n ∈ Icc 1 N, if Squarefree n then 1 else 0 := by
    simp only [squarefreeCountNat, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
    apply sum_congr rfl
    intro n hn
    by_cases hs : Squarefree n
    · simp [hs]
    · simp [hs]
  have hinner (n : ℕ) (hnmem : n ∈ Icc 1 N) :
      (∑ d ∈ Icc 1 N.sqrt,
        if d * d ∣ n then ArithmeticFunction.moebius d else 0) =
        if Squarefree n then 1 else 0 := by
    have hnpos : 0 < n := Nat.zero_lt_of_lt (mem_Icc.mp hnmem).1
    rw [← sum_moebius_square_divisors n hnpos]
    rw [sum_ite, sum_ite]
    simp only [sum_const_zero, add_zero]
    apply sum_congr
    · ext d
      simp only [mem_filter, mem_Icc, Nat.mem_divisors]
      constructor
      · rintro ⟨⟨hdpos, hdsqrt⟩, hd2⟩
        have hdn : d ∣ n := (dvd_mul_right d d).trans hd2
        exact ⟨⟨hdn, hnpos.ne'⟩, hd2⟩
      · rintro ⟨⟨hdn, hn0⟩, hd2⟩
        have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdn hnpos
        have hd2le : d * d ≤ N :=
          (Nat.le_of_dvd hnpos hd2).trans (mem_Icc.mp hnmem).2
        exact ⟨⟨hdpos, Nat.le_sqrt.mpr hd2le⟩, hd2⟩
    · intro d hd
      rfl
  have hrow (d : ℕ) :
      ArithmeticFunction.moebius d * (N / (d * d) : ℕ) =
        ∑ n ∈ Icc 1 N,
          if d * d ∣ n then ArithmeticFunction.moebius d else 0 := by
    rw [show Icc 1 N = Ioc 0 N by
      simpa using (Icc_add_one_left_eq_Ioc (0 : ℕ) N)]
    rw [← Nat.Ioc_filter_dvd_card_eq_div N (d * d)]
    simp only [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    ring
  rw [hq]
  calc
    (∑ n ∈ Icc 1 N, if Squarefree n then 1 else 0) =
        ∑ n ∈ Icc 1 N, ∑ d ∈ Icc 1 N.sqrt,
          if d * d ∣ n then ArithmeticFunction.moebius d else 0 := by
      exact sum_congr rfl fun n hn ↦ (hinner n hn).symm
    _ = ∑ d ∈ Icc 1 N.sqrt, ∑ n ∈ Icc 1 N,
          if d * d ∣ n then ArithmeticFunction.moebius d else 0 := by
      rw [sum_comm]
    _ = ∑ d ∈ Icc 1 N.sqrt,
        ArithmeticFunction.moebius d * (N / (d * d) : ℕ) := by
      exact sum_congr rfl fun d hd ↦ (hrow d).symm

noncomputable def theta (N d : ℕ) : ℝ := (N % (d * d) : ℕ) / (d * d : ℕ)

theorem theta_bounds (N d : ℕ) (hd : 1 ≤ d) :
    0 ≤ theta N d ∧ theta N d ≤ 1 := by
  have hd2 : 0 < d * d := Nat.mul_pos (Nat.zero_lt_of_lt hd) (Nat.zero_lt_of_lt hd)
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · exact (div_le_one (by positivity : (0 : ℝ) < (d * d : ℕ))).2 (by
      exact_mod_cast (Nat.le_of_lt (Nat.mod_lt N hd2)))

theorem cast_div_eq_div_sub_theta (N d : ℕ) (hd : 1 ≤ d) :
    ((N / (d * d) : ℕ) : ℝ) = (N : ℝ) / (d * d : ℕ) - theta N d := by
  have hd2 : 0 < d * d := Nat.mul_pos (Nat.zero_lt_of_lt hd) (Nat.zero_lt_of_lt hd)
  have hdiv := Nat.div_add_mod N (d * d)
  have hdivR :
      ((d * d : ℕ) : ℝ) * (N / (d * d) : ℕ) + (N % (d * d) : ℕ) = N := by
    exact_mod_cast hdiv
  norm_num [theta, Nat.cast_add, Nat.cast_mul] at hdivR ⊢
  field_simp
  nlinarith [hdivR]

theorem nat_sqrt_real_bounds (N : ℕ) :
    (N.sqrt : ℝ) ≤ Real.sqrt N ∧ Real.sqrt N < (N.sqrt : ℝ) + 1 := by
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hs0 : 0 ≤ Real.sqrt (N : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hN0
  have hlow : (N.sqrt : ℝ) ^ 2 ≤ N := by
    have h : ((N.sqrt * N.sqrt : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast Nat.sqrt_le N
    simpa [pow_two] using h
  have hupp : (N : ℝ) < ((N.sqrt : ℝ) + 1) ^ 2 := by
    have h : (N : ℝ) < ((N.sqrt + 1) * (N.sqrt + 1) : ℕ) := by
      exact_mod_cast Nat.lt_succ_sqrt N
    norm_num [Nat.cast_add, Nat.cast_one, pow_two] at h ⊢
    exact h
  constructor <;> nlinarith

theorem R_nat_eq (N : ℕ) :
    R (N : ℝ) =
      -(∑ d ∈ Icc 1 N.sqrt, muR d * theta N d) -
        (N : ℝ) *
          (density - ∑ d ∈ Icc 1 N.sqrt, muR d / (d : ℝ) ^ 2) := by
  have hfloor : ⌊(N : ℝ)⌋₊ = N := by simp
  have hformula :
      (squarefreeCountNat N : ℝ) =
        ∑ d ∈ Icc 1 N.sqrt, muR d * (N / (d * d) : ℕ) := by
    have hZ := congrArg (fun z : ℤ ↦ (z : ℝ)) (squarefreeCountNat_floor_formula N)
    simpa [muR] using hZ
  have hrewrite :
      (∑ d ∈ Icc 1 N.sqrt, muR d * (N / (d * d) : ℕ)) =
        (N : ℝ) * (∑ d ∈ Icc 1 N.sqrt, muR d / (d : ℝ) ^ 2) -
          ∑ d ∈ Icc 1 N.sqrt, muR d * theta N d := by
    calc
      _ = ∑ d ∈ Icc 1 N.sqrt,
          muR d * ((N : ℝ) / (d * d : ℕ) - theta N d) := by
        apply sum_congr rfl
        intro d hd
        rw [cast_div_eq_div_sub_theta N d (mem_Icc.mp hd).1]
      _ = ∑ d ∈ Icc 1 N.sqrt,
          ((N : ℝ) * (muR d / (d : ℝ) ^ 2) - muR d * theta N d) := by
        apply sum_congr rfl
        intro d hd
        norm_num [Nat.cast_mul, pow_two]
        ring
      _ = _ := by
        rw [sum_sub_distrib, mul_sum]
  simp only [R, squarefreeCount, hfloor]
  rw [hformula, hrewrite]
  ring

theorem abs_R_nat_lt_coarse (N : ℕ) (hN : 401 ≤ N) :
    |R (N : ℝ)| < 13 / 16 * Real.sqrt N + 11 / 4 := by
  let m := N.sqrt
  have hm : 2 ≤ m := by
    dsimp [m]
    exact Nat.le_sqrt.mpr (by omega)
  have hm1 : 1 ≤ m := by omega
  have hsqrt := nat_sqrt_real_bounds N
  have hms : (m : ℝ) ≤ Real.sqrt N := by simpa [m] using hsqrt.1
  have hsma : Real.sqrt N < (m : ℝ) + 1 := by simpa [m] using hsqrt.2
  have htheta : ∀ d ∈ Icc 1 m, 0 ≤ theta N d ∧ theta N d ≤ 1 := by
    intro d hd
    exact theta_bounds N d (mem_Icc.mp hd).1
  have hfrac0 := abs_sum_muR_mul_le m (theta N) htheta
  have hq := squarefreeCountNat_le_three_quarters m
  have hM := abs_mertens_le m hm1
  have hfrac :
      |∑ d ∈ Icc 1 m, muR d * theta N d| ≤
        7 / 16 * Real.sqrt N + 5 / 4 := by
    calc
      _ ≤ squarefreeCountNat m / 2 + |mertens m| / 2 := hfrac0
      _ ≤ 7 / 16 * (m : ℝ) + 5 / 4 := by nlinarith
      _ ≤ 7 / 16 * Real.sqrt N + 5 / 4 := by nlinarith
  let T : ℝ := density - ∑ d ∈ Icc 1 m, muR d / (d : ℝ) ^ 2
  let C : ℝ := 3 / (8 * ((m + 1 : ℕ) : ℝ)) +
    3 / (2 * ((m + 1 : ℕ) : ℝ) ^ 2)
  have hT : |T| ≤ C := by
    exact abs_mu_tail_le m hm
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have hs0 : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.2 (by positivity)
  have ha0 : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hs2 : Real.sqrt (N : ℝ) ^ 2 = N := Real.sq_sqrt hN0
  have hdiv1 : (N : ℝ) / ((m : ℝ) + 1) < Real.sqrt N := by
    apply (div_lt_iff₀ ha0).2
    nlinarith
  have hdiv2 : (N : ℝ) / ((m : ℝ) + 1) ^ 2 < 1 := by
    apply (div_lt_iff₀ (sq_pos_of_pos ha0)).2
    nlinarith
  have hNC : (N : ℝ) * C < 3 / 8 * Real.sqrt N + 3 / 2 := by
    have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by norm_num
    dsimp [C]
    rw [hcast]
    calc
      (N : ℝ) * (3 / (8 * ((m : ℝ) + 1)) +
          3 / (2 * ((m : ℝ) + 1) ^ 2)) =
        3 / 8 * ((N : ℝ) / ((m : ℝ) + 1)) +
          3 / 2 * ((N : ℝ) / ((m : ℝ) + 1) ^ 2) := by
        field_simp
      _ < 3 / 8 * Real.sqrt N + 3 / 2 := by nlinarith
  have hNT : |(N : ℝ) * T| < 3 / 8 * Real.sqrt N + 3 / 2 := by
    rw [abs_mul, abs_of_nonneg hN0]
    calc
      (N : ℝ) * |T| ≤ (N : ℝ) * C := mul_le_mul_of_nonneg_left hT hN0
      _ < _ := hNC
  rw [R_nat_eq N]
  have htri :
      |-(∑ d ∈ Icc 1 N.sqrt, muR d * theta N d) - (N : ℝ) *
          (density - ∑ d ∈ Icc 1 N.sqrt, muR d / (d : ℝ) ^ 2)| ≤
        |∑ d ∈ Icc 1 N.sqrt, muR d * theta N d| +
          |(N : ℝ) *
            (density - ∑ d ∈ Icc 1 N.sqrt, muR d / (d : ℝ) ^ 2)| := by
    calc
      _ ≤ |-(∑ d ∈ Icc 1 N.sqrt, muR d * theta N d)| +
          |(N : ℝ) *
            (density - ∑ d ∈ Icc 1 N.sqrt, muR d / (d : ℝ) ^ 2)| := abs_sub _ _
      _ = _ := by rw [abs_neg]
  calc
    _ ≤ _ := htri
    _ < (7 / 16 * Real.sqrt N + 5 / 4) +
        (3 / 8 * Real.sqrt N + 3 / 2) := by
      exact add_lt_add_of_le_of_lt (by simpa [m] using hfrac) (by simpa [T, m] using hNT)
    _ = _ := by ring

/-- Moser--MacLeod's estimate on the range treated explicitly in their proof. -/
theorem abs_R_lt_sqrt_of_one_le (x : ℝ) (hx : 1 ≤ x) :
    |R x| < Real.sqrt x := by
  by_cases hx401 : x < 401
  · exact abs_R_lt_sqrt_of_lt_401 x hx hx401
  · have hxlarge : 401 ≤ x := le_of_not_gt hx401
    let N := ⌊x⌋₊
    have hx0 : 0 ≤ x := by linarith
    have hN : 401 ≤ N := by
      apply Nat.le_floor
      exact hxlarge
    have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
    have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
    have hcount : squarefreeCount x = squarefreeCount (N : ℝ) := by
      simp [squarefreeCount, N]
    have hReq : R x = R (N : ℝ) - density * (x - N) := by
      rw [R, R, hcount]
      ring
    have hcoarse := abs_R_nat_lt_coarse N hN
    have hsmono : Real.sqrt (N : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
    have hcpos : 0 < density := density_bounds.1.trans' (by norm_num [densityLower])
    have hclt : density < 1 := density_bounds.2.trans (by norm_num [densityUpper])
    have ht0 : 0 ≤ x - (N : ℝ) := sub_nonneg.mpr hNx
    have ht1 : x - (N : ℝ) < 1 := by linarith
    have hdt : density * (x - (N : ℝ)) < 1 := by
      have hnonneg : 0 ≤ (1 - density) * (x - (N : ℝ)) :=
        mul_nonneg (sub_nonneg.mpr hclt.le) ht0
      nlinarith
    have hlargebound : |R x| < 13 / 16 * Real.sqrt x + 15 / 4 := by
      rw [hReq]
      calc
        _ ≤ |R (N : ℝ)| + |density * (x - (N : ℝ))| := abs_sub _ _
        _ = |R (N : ℝ)| + density * (x - (N : ℝ)) := by
          rw [abs_mul, abs_of_pos hcpos, abs_of_nonneg ht0]
        _ < (13 / 16 * Real.sqrt N + 11 / 4) +
            density * (x - (N : ℝ)) := by linarith
        _ ≤ 13 / 16 * Real.sqrt x + 11 / 4 +
            density * (x - (N : ℝ)) := by nlinarith
        _ < 13 / 16 * Real.sqrt x + 15 / 4 := by linarith
    have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
    have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
    have hs20 : 20 < Real.sqrt x := by nlinarith
    nlinarith

/-- Moser--MacLeod's square-root estimate.  The paper states the result for
positive real `x`; the interval `0 < x < 1` follows immediately because the
squarefree count vanishes there. -/
theorem abs_R_lt_sqrt (x : ℝ) (hx : 0 < x) :
    |R x| < √x := by
  by_cases hx1 : 1 ≤ x
  · exact abs_R_lt_sqrt_of_one_le x hx1
  · have hxlt : x < 1 := lt_of_not_ge hx1
    have hfloor : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr hxlt
    have hcount : squarefreeCount x = 0 := by
      simp [squarefreeCount, hfloor, squarefreeCountNat]
    have hcpos : 0 < density :=
      density_bounds.1.trans' (by norm_num [densityLower])
    have hclt : density < 1 :=
      density_bounds.2.trans (by norm_num [densityUpper])
    have hspos : 0 < √x := Real.sqrt_pos.2 hx
    have hs2 : (√x) ^ 2 = x := Real.sq_sqrt hx.le
    rw [R, hcount]
    simp only [Nat.cast_zero, zero_sub, abs_neg, abs_mul,
      abs_of_pos hcpos, abs_of_pos hx]
    nlinarith [mul_pos (sub_pos.mpr hclt) hx]

#print axioms abs_R_lt_sqrt

end MoserMacLeod
