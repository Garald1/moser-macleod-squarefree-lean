import MoserMacLeod.Proof

/-!
# A sharpened leading constant for the Moser--MacLeod error estimate

`MoserMacLeod/Proof.lean` proves the headline bound `|R x| < √x` for `x > 0`, and
along the way establishes the coarse large-`x` estimate
`|R N| < 13/16 · √N + 11/4`.  The leading constant `13/16` comes from two
elementary inputs: the sieve bound `Q(N) ≤ 3/4·N` (a squarefree integer is not
divisible by `4`) and the Mertens bound `|M(N)+1| ≤ N/8`.

Here we sharpen the sieve input by also excluding multiples of `9`
(`Q(N) ≤ 2/3·N + O(1)`), which improves the Mertens bound to `|M(N)+1| ≤ N/9 + O(1)`
and pushes the leading constant down to `13/18`.  The whole tail argument is
generalized in the two weight constants `c₁, c₀`, so the existing `13/16` proof is
left completely untouched.

The public result is `abs_R_lt_thirteen_eighteenths_sqrt`.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction ArithmeticFunction.Moebius BigOperators
open Filter Finset

noncomputable section

/-- Sharper elementary squarefree-count bound: a squarefree integer is divisible
by neither `4` nor `9`, so its density is at most `2/3`. -/
theorem squarefreeCountNat_le_two_thirds (N : ℕ) :
    (squarefreeCountNat N : ℝ) ≤ (2 / 3 : ℝ) * N + 59 / 36 := by
  classical
  let U := Ioc 0 N
  let S := U.filter fun n ↦ ArithmeticFunction.moebius n ≠ 0
  let A := U.filter fun n ↦ 4 ∣ n
  let B := U.filter fun n ↦ 9 ∣ n
  have hq : squarefreeCountNat N = #S := by
    simp only [squarefreeCountNat, S, U]
    rw [← Icc_add_one_left_eq_Ioc]
    simpa [ite_not] using
      (sum_boole (R := ℕ) (fun n ↦ ArithmeticFunction.moebius n ≠ 0) (Icc 1 N))
  have hSsub : S ⊆ U \ (A ∪ B) := by
    intro n hn
    simp only [S, A, B, U, mem_filter, mem_sdiff, mem_union, mem_Ioc] at hn ⊢
    refine ⟨hn.1, ?_⟩
    rintro (h4 | h9)
    · have hsq : Squarefree n :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hn.2
      have hu := hsq 2 (by simpa [pow_two] using h4.2)
      norm_num at hu
    · have hsq : Squarefree n :=
        ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hn.2
      have hu := hsq 3 (by simpa [pow_two] using h9.2)
      norm_num at hu
  have hAU : A ⊆ U := filter_subset _ _
  have hBU : B ⊆ U := filter_subset _ _
  have hcardA : #A = N / 4 := by
    simpa [A, U] using Nat.Ioc_filter_dvd_card_eq_div N 4
  have hcardB : #B = N / 9 := by
    simpa [B, U] using Nat.Ioc_filter_dvd_card_eq_div N 9
  have hAB : A ∩ B = U.filter fun n ↦ 36 ∣ n := by
    ext n
    simp only [A, B, mem_inter, mem_filter]
    constructor
    · rintro ⟨⟨hnU, h4⟩, _, h9⟩
      exact ⟨hnU, by omega⟩
    · rintro ⟨hnU, h36⟩
      exact ⟨⟨hnU, by omega⟩, hnU, by omega⟩
  have hcardAB : #(A ∩ B) = N / 36 := by
    rw [hAB]; simpa [U] using Nat.Ioc_filter_dvd_card_eq_div N 36
  have hunion : #(A ∪ B) = N / 4 + N / 9 - N / 36 := by
    have := Finset.card_union_add_card_inter A B
    rw [hcardA, hcardB, hcardAB] at this
    omega
  have hcardU : #U = N := by simp [U]
  have hsub : #S ≤ #(U \ (A ∪ B)) := card_le_card hSsub
  have hsdiff : #(U \ (A ∪ B)) + #(A ∪ B) = N := by
    rw [Finset.card_sdiff_add_card_eq_card (union_subset hAU hBU), hcardU]
  have hnat : 36 * squarefreeCountNat N ≤ 24 * N + 59 := by
    rw [hq]
    have h4 := Nat.div_add_mod N 4
    have h9 := Nat.div_add_mod N 9
    have h36 := Nat.div_add_mod N 36
    have h4m := Nat.mod_lt N (show 0 < 4 by norm_num)
    have h9m := Nat.mod_lt N (show 0 < 9 by norm_num)
    rw [hunion] at hsdiff
    omega
  have hnat' : (36 : ℝ) * squarefreeCountNat N ≤ 24 * N + 59 := by
    exact_mod_cast hnat
  linarith

/-- The sharper Mertens bound `|M(N)+1| ≤ N/9 + 59/36`, using the improved sieve
input on `Q(N/6)`. -/
theorem abs_mertens_add_one_le' (N : ℕ) (hN : 2 ≤ N) :
    |mertens N + 1| ≤ (N : ℝ) / 9 + 59 / 36 := by
  rw [mertens_eq_intCast]
  by_cases hlarge : 30 ≤ N
  · have hcount := abs_mertensInt_add_one_le_count N hlarge
    have hcount' : |(mertensInt N : ℝ) + 1| ≤ squarefreeCountNat (N / 6) := by
      exact_mod_cast hcount
    have hq := squarefreeCountNat_le_two_thirds (N / 6)
    have hdiv : (6 : ℝ) * (N / 6 : ℕ) ≤ N := by
      exact_mod_cast Nat.mul_div_le N 6
    nlinarith
  · have hsmall : (8 : ℤ) * |mertensInt N + 1| ≤ (N : ℤ) + 6 :=
      small_mertens_bound N hN (by omega)
    have hsmall' : (8 : ℝ) * |(mertensInt N : ℝ) + 1| ≤ (N : ℝ) + 6 := by
      exact_mod_cast hsmall
    have hNlt : (N : ℝ) < 30 := by exact_mod_cast (by omega : N < 30)
    nlinarith

/-- Generalized weighted telescoping bound with an affine weight `c₁·i + c₀`. -/
theorem weighted_diff_sq_le_gen (a b : ℕ) (ha : 1 ≤ a) (c1 c0 : ℝ)
    (hc1 : 0 ≤ c1) (hc0 : 0 ≤ c0) :
    (∑ i ∈ Ico a b,
      (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) * ((i : ℝ) * c1 + c0)) ≤
      2 * c1 / (a : ℝ) + c0 / (a : ℝ) ^ 2 := by
  have hrewrite :
      (∑ i ∈ Ico a b,
        (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) * ((i : ℝ) * c1 + c0)) =
        c1 * (∑ i ∈ Ico a b,
          (i : ℝ) * (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) +
        c0 * (∑ i ∈ Ico a b,
          (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2)) := by
    rw [mul_sum, mul_sum, ← sum_add_distrib]
    apply sum_congr rfl
    intro i hi
    ring
  rw [hrewrite]
  have h1 := sum_Ico_mul_diff_sq_le a b ha
  have h2 := sum_Ico_diff_sq_le a b ha
  have ha0 : (0 : ℝ) < a := by positivity
  calc
    _ ≤ c1 * (2 / (a : ℝ)) + c0 * (1 / (a : ℝ) ^ 2) := by
      gcongr
    _ = 2 * c1 / (a : ℝ) + c0 / (a : ℝ) ^ 2 := by ring

/-- Generalized finite Möbius-series tail bound.  For any affine Mertens bound
`|M(k)+1| ≤ k·c₁ + c₀` (with `c₁, c₀ ≥ 0`), the partial tail is controlled by
`c₁, c₀`. -/
theorem finite_tail_bound_gen (m n : ℕ) (hm : 2 ≤ m) (hmn : m + 1 < n)
    (c1 c0 : ℝ) (hc1 : 0 ≤ c1) (hc0 : 0 ≤ c0)
    (hmb : ∀ k, 2 ≤ k → |mertens k + 1| ≤ (k : ℝ) * c1 + c0) :
    |∑ i ∈ Ico (m + 1) n, muR i / (i : ℝ) ^ 2| ≤
      (((n - 1 : ℕ) : ℝ) * c1 + c0) / ((n - 1 : ℕ) : ℝ) ^ 2 +
        3 * c1 / ((m + 1 : ℕ) : ℝ) +
          2 * c0 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
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
  have hboundary := hmb (n - 1) hn1
  have hbase := hmb m hm
  have hsumabs :
      |∑ i ∈ Ico (m + 1) (n - 1),
        (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
          (mertens i + 1)| ≤
      ∑ i ∈ Ico (m + 1) (n - 1),
        (1 / (i : ℝ) ^ 2 - 1 / ((i + 1 : ℕ) : ℝ) ^ 2) *
          ((i : ℝ) * c1 + c0) := by
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
        exact mul_le_mul_of_nonneg_left (hmb i hi2) hdiff
  have hweighted := weighted_diff_sq_le_gen (m + 1) (n - 1) (by omega) c1 c0 hc1 hc0
  have hboundary' :
      |(1 / ((n - 1 : ℕ) : ℝ) ^ 2) * (mertens (n - 1) + 1)| ≤
        (((n - 1 : ℕ) : ℝ) * c1 + c0) / ((n - 1 : ℕ) : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / ((n - 1 : ℕ) : ℝ) ^ 2)]
    calc
      _ ≤ (1 / ((n - 1 : ℕ) : ℝ) ^ 2) *
          (((n - 1 : ℕ) : ℝ) * c1 + c0) := by
        exact mul_le_mul_of_nonneg_left hboundary (by positivity)
      _ = _ := by ring
  have hbase' :
      |(1 / ((m + 1 : ℕ) : ℝ) ^ 2) * (mertens m + 1)| ≤
        ((m : ℝ) * c1 + c0) / ((m + 1 : ℕ) : ℝ) ^ 2 := by
    rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / ((m + 1 : ℕ) : ℝ) ^ 2)]
    calc
      _ ≤ (1 / ((m + 1 : ℕ) : ℝ) ^ 2) * ((m : ℝ) * c1 + c0) := by
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
    _ ≤ (((n - 1 : ℕ) : ℝ) * c1 + c0) / ((n - 1 : ℕ) : ℝ) ^ 2 +
        (((m : ℝ) * c1 + c0) / ((m + 1 : ℕ) : ℝ) ^ 2) +
        (2 * c1 / ((m + 1 : ℕ) : ℝ) +
          c0 / ((m + 1 : ℕ) : ℝ) ^ 2) := by
      exact add_le_add (add_le_add hboundary' hbase') (hsumabs.trans hweighted)
    _ ≤ _ := by
      have hm0 : (0 : ℝ) < ((m + 1 : ℕ) : ℝ) := by positivity
      have hrem :
          (((m : ℝ) * c1 + c0) / ((m + 1 : ℕ) : ℝ) ^ 2) +
            (2 * c1 / ((m + 1 : ℕ) : ℝ) +
              c0 / ((m + 1 : ℕ) : ℝ) ^ 2) ≤
            3 * c1 / ((m + 1 : ℕ) : ℝ) +
              2 * c0 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
        have key :
            3 * c1 / ((m + 1 : ℕ) : ℝ) + 2 * c0 / ((m + 1 : ℕ) : ℝ) ^ 2 -
              ((((m : ℝ) * c1 + c0) / ((m + 1 : ℕ) : ℝ) ^ 2) +
                (2 * c1 / ((m + 1 : ℕ) : ℝ) + c0 / ((m + 1 : ℕ) : ℝ) ^ 2)) =
              c1 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
          have hcast : ((m + 1 : ℕ) : ℝ) = (m : ℝ) + 1 := by norm_num
          rw [hcast]; field_simp; ring
        have hnn : 0 ≤ c1 / ((m + 1 : ℕ) : ℝ) ^ 2 :=
          div_nonneg hc1 (by positivity)
        linarith [key, hnn]
      linarith

/-- Generalized Möbius-series tail bound: for an affine Mertens bound with
constants `c₁, c₀ ≥ 0`, the true Dirichlet-series tail beyond `m` is at most
`3c₁/(m+1) + 2c₀/(m+1)²`. -/
theorem abs_mu_tail_le_gen (m : ℕ) (hm : 2 ≤ m) (c1 c0 : ℝ)
    (hc1 : 0 ≤ c1) (hc0 : 0 ≤ c0)
    (hmb : ∀ k, 2 ≤ k → |mertens k + 1| ≤ (k : ℝ) * c1 + c0) :
    |density - ∑ i ∈ Icc 1 m, muR i / (i : ℝ) ^ 2| ≤
      3 * c1 / ((m + 1 : ℕ) : ℝ) + 2 * c0 / ((m + 1 : ℕ) : ℝ) ^ 2 := by
  let C : ℝ := 3 * c1 / ((m + 1 : ℕ) : ℝ) + 2 * c0 / ((m + 1 : ℕ) : ℝ) ^ 2
  let s : ℕ → ℝ := fun k ↦ muR (k + (m + 1)) / ((k + (m + 1) : ℕ) : ℝ) ^ 2
  have hs : HasSum s (density - ∑ i ∈ Icc 1 m, muR i / (i : ℝ) ^ 2) :=
    hasSum_mu_tail m
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
        (((n : ℝ) + m) * c1 + c0) / ((n : ℝ) + m) ^ 2) atTop (nhds 0) := by
    have hc1t : Tendsto (fun _ : ℕ ↦ c1) atTop (nhds c1) := tendsto_const_nhds
    have hc0t : Tendsto (fun _ : ℕ ↦ c0) atTop (nhds c0) := tendsto_const_nhds
    have hlim := (hc1t.mul hinv).add (hc0t.mul (hinv.pow 2))
    convert hlim using 1
    · funext n
      by_cases hn : (n : ℝ) + m = 0
      · simp [hn]
      · field_simp
    · norm_num
  have hright :
      Tendsto (fun n : ℕ ↦
        (((n : ℝ) + m) * c1 + c0) / ((n : ℝ) + m) ^ 2 + C)
        atTop (nhds C) := by
    convert hboundary.add tendsto_const_nhds using 1
    all_goals simp
  apply le_of_tendsto_of_tendsto hleft hright
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [hpartial]
  have hfin := finite_tail_bound_gen m (n + (m + 1)) hm (by omega) c1 c0 hc1 hc0 hmb
  have hcast : (n + (m + 1) - 1 : ℕ) = n + m := by omega
  rw [hcast] at hfin
  have hcast2 : ((n + m : ℕ) : ℝ) = (n : ℝ) + m := by push_cast; ring
  rw [hcast2] at hfin
  show |∑ i ∈ Ico (m + 1) (n + (m + 1)), muR i / (i : ℝ) ^ 2| ≤
    (((n : ℝ) + m) * c1 + c0) / ((n : ℝ) + m) ^ 2 + C
  simp only [C]
  linarith [hfin]

/-- The affine Mertens bound in the form required by the generalized tail lemmas,
with weight constants `c₁ = 1/9`, `c₀ = 59/36`. -/
theorem mertens_affine_bound (k : ℕ) (hk : 2 ≤ k) :
    |mertens k + 1| ≤ (k : ℝ) * (1 / 9) + 59 / 36 := by
  have h := abs_mertens_add_one_le' k hk
  have hrw : (k : ℝ) * (1 / 9) + 59 / 36 = (k : ℝ) / 9 + 59 / 36 := by ring
  rw [hrw]; exact h

/-- Sharpened coarse bound with leading constant `13/18`, valid for all `N ≥ 4`.
Compare `abs_R_nat_lt_coarse`, which has leading constant `13/16`. -/
theorem abs_R_nat_lt_coarse_sharp (N : ℕ) (hN : 4 ≤ N) :
    |R (N : ℝ)| < 13 / 18 * Real.sqrt N + 65 / 12 := by
  let m := N.sqrt
  have hm : 2 ≤ m := by
    dsimp [m]; exact Nat.le_sqrt.mpr (by omega)
  have hm1 : 1 ≤ m := by omega
  have hsqrt := nat_sqrt_real_bounds N
  have hms : (m : ℝ) ≤ Real.sqrt N := by simpa [m] using hsqrt.1
  have hsma : Real.sqrt N < (m : ℝ) + 1 := by simpa [m] using hsqrt.2
  have htheta : ∀ d ∈ Icc 1 m, 0 ≤ theta N d ∧ theta N d ≤ 1 := by
    intro d hd
    exact theta_bounds N d (mem_Icc.mp hd).1
  have hfrac0 := abs_sum_muR_mul_le m (theta N) htheta
  have hq := squarefreeCountNat_le_two_thirds m
  have hM : |mertens m| ≤ (m : ℝ) / 9 + 95 / 36 := by
    have h := abs_mertens_add_one_le' m hm
    have hsub : |mertens m| ≤ |mertens m + 1| + 1 := by
      calc
        |mertens m| = |(mertens m + 1) - 1| := by ring_nf
        _ ≤ |mertens m + 1| + |(1 : ℝ)| := abs_sub _ _
        _ = |mertens m + 1| + 1 := by norm_num
    linarith
  have hfrac :
      |∑ d ∈ Icc 1 m, muR d * theta N d| ≤
        7 / 18 * Real.sqrt N + 77 / 36 := by
    calc
      _ ≤ squarefreeCountNat m / 2 + |mertens m| / 2 := hfrac0
      _ ≤ 7 / 18 * (m : ℝ) + 77 / 36 := by linarith
      _ ≤ 7 / 18 * Real.sqrt N + 77 / 36 := by nlinarith
  let T : ℝ := density - ∑ d ∈ Icc 1 m, muR d / (d : ℝ) ^ 2
  let C : ℝ := 3 * (1 / 9) / ((m + 1 : ℕ) : ℝ) + 2 * (59 / 36) / ((m + 1 : ℕ) : ℝ) ^ 2
  have hT : |T| ≤ C :=
    abs_mu_tail_le_gen m hm (1 / 9) (59 / 36) (by norm_num) (by norm_num)
      mertens_affine_bound
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
  have hNC : (N : ℝ) * C < 1 / 3 * Real.sqrt N + 59 / 18 := by
    have hcast : (((m + 1 : ℕ) : ℝ)) = (m : ℝ) + 1 := by norm_num
    dsimp [C]
    rw [hcast]
    calc
      (N : ℝ) * (3 * (1 / 9) / ((m : ℝ) + 1) +
          2 * (59 / 36) / ((m : ℝ) + 1) ^ 2) =
        1 / 3 * ((N : ℝ) / ((m : ℝ) + 1)) +
          59 / 18 * ((N : ℝ) / ((m : ℝ) + 1) ^ 2) := by
        field_simp
        ring
      _ < 1 / 3 * Real.sqrt N + 59 / 18 := by nlinarith
  have hNT : |(N : ℝ) * T| < 1 / 3 * Real.sqrt N + 59 / 18 := by
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
    _ < (7 / 18 * Real.sqrt N + 77 / 36) +
        (1 / 3 * Real.sqrt N + 59 / 18) := by
      exact add_lt_add_of_le_of_lt (by simpa [m] using hfrac) (by simpa [T, m] using hNT)
    _ = _ := by ring

/-- **Sharpened Moser--MacLeod estimate.**  For every real `x ≥ 16`,
`|R x| < 13/18 · √x + 77/12`.  The leading constant `13/18 ≈ 0.722` improves on
the `13/16 ≈ 0.813` implicit in the headline `|R x| < √x`; it comes from the
sharper elementary sieve bound `Q(N) ≤ 2/3·N + O(1)` (excluding multiples of
both `4` and `9`). -/
theorem abs_R_lt_thirteen_eighteenths_sqrt (x : ℝ) (hx : 16 ≤ x) :
    |R x| < 13 / 18 * Real.sqrt x + 77 / 12 := by
  let N := ⌊x⌋₊
  have hx0 : 0 ≤ x := by linarith
  have hN : 4 ≤ N := by
    apply Nat.le_floor
    push_cast; linarith
  have hNx : (N : ℝ) ≤ x := Nat.floor_le hx0
  have hxN : x < (N : ℝ) + 1 := Nat.lt_floor_add_one x
  have hcount : squarefreeCount x = squarefreeCount (N : ℝ) := by
    simp [squarefreeCount, N]
  have hReq : R x = R (N : ℝ) - density * (x - N) := by
    rw [R, R, hcount]; ring
  have hcoarse := abs_R_nat_lt_coarse_sharp N hN
  have hsmono : Real.sqrt (N : ℝ) ≤ Real.sqrt x := Real.sqrt_le_sqrt hNx
  have hcpos : 0 < density := density_bounds.1.trans' (by norm_num [densityLower])
  have hclt : density < 1 := density_bounds.2.trans (by norm_num [densityUpper])
  have ht0 : 0 ≤ x - (N : ℝ) := sub_nonneg.mpr hNx
  have ht1 : x - (N : ℝ) < 1 := by linarith
  have hdt : density * (x - (N : ℝ)) < 1 := by
    have hnonneg : 0 ≤ (1 - density) * (x - (N : ℝ)) :=
      mul_nonneg (sub_nonneg.mpr hclt.le) ht0
    nlinarith
  rw [hReq]
  calc
    _ ≤ |R (N : ℝ)| + |density * (x - (N : ℝ))| := abs_sub _ _
    _ = |R (N : ℝ)| + density * (x - (N : ℝ)) := by
      rw [abs_mul, abs_of_pos hcpos, abs_of_nonneg ht0]
    _ < (13 / 18 * Real.sqrt N + 65 / 12) + density * (x - (N : ℝ)) := by linarith
    _ ≤ 13 / 18 * Real.sqrt x + 65 / 12 + density * (x - (N : ℝ)) := by nlinarith
    _ < 13 / 18 * Real.sqrt x + 77 / 12 := by linarith

/-- **Crossover.**  For `x ≥ 534` the sharpened right-hand side is *strictly below*
`√x`.  The threshold is optimal for this constant pair: the two sides meet at
`√x = 231/10`, i.e. `x = 533.61`, so `534` is the least integer past the
crossover. -/
theorem sharp_bound_lt_sqrt (x : ℝ) (hx : 534 ≤ x) :
    13 / 18 * Real.sqrt x + 77 / 12 < Real.sqrt x := by
  have hx0 : 0 ≤ x := by linarith
  have hs0 : 0 ≤ Real.sqrt x := Real.sqrt_nonneg _
  have hs2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0
  nlinarith [hs2, hs0, hx]

/-- The genuine improvement, made explicit: for every `x ≥ 534`,
`|R x|` is below `√x` by the strictly positive, unbounded margin
`5/18·√x − 77/12`.  This is what the sharpened `13/18` leading constant buys
beyond the headline `|R x| < √x`. -/
theorem abs_R_add_margin_lt_sqrt (x : ℝ) (hx : 534 ≤ x) :
    |R x| + (5 / 18 * Real.sqrt x - 77 / 12) < Real.sqrt x := by
  have h := abs_R_lt_thirteen_eighteenths_sqrt x (by linarith)
  linarith

/-- Consequently the headline bound `|R x| < √x` is re-derived for `x ≥ 534`
through the sharp estimate, with room to spare rather than the borderline
`13/16` argument used near the `x = 401` crossover. -/
theorem abs_R_lt_sqrt_sharp (x : ℝ) (hx : 534 ≤ x) :
    |R x| < Real.sqrt x :=
  lt_trans (abs_R_lt_thirteen_eighteenths_sqrt x (by linarith))
    (sharp_bound_lt_sqrt x hx)

#print axioms abs_R_lt_thirteen_eighteenths_sqrt
#print axioms abs_R_lt_sqrt_sharp

end
end MoserMacLeod
