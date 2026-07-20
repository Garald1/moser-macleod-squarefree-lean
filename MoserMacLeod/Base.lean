import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.NumberTheory.LSeries.HurwitzZetaValues
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Analysis.PSeries
import Mathlib.Data.Nat.Squarefree
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Infrastructure for the Moser--MacLeod square-root estimate

This file formalizes the theorem that the error in the elementary squarefree
count satisfies `|R x| < √x` for every real `x ≥ 1`.

The companion document `MOSER_MACLEOD_LEAN_COMPANION.md` gives the complete
human proof and maps each result below to the corresponding step in the 1966
paper. In particular, it records where this development uses different
numerical constants from Moser--MacLeod.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction ArithmeticFunction.Moebius BigOperators LSeries.notation
open Finset

/-- The density of the squarefree positive integers. -/
noncomputable def density : ℝ := 6 / Real.pi ^ 2

/-- The number of squarefree positive integers at most `N`. -/
def squarefreeCountNat (N : ℕ) : ℕ :=
  ∑ n ∈ Icc 1 N, if ArithmeticFunction.moebius n = 0 then 0 else 1

/-- Updating the squarefree count by one integer. -/
theorem squarefreeCountNat_succ (N : ℕ) :
    squarefreeCountNat (N + 1) = squarefreeCountNat N +
      (if ArithmeticFunction.moebius (N + 1) = 0 then 0 else 1) := by
  simp only [squarefreeCountNat]
  rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- The usual expression of the squarefree indicator as `μ(n)²`. -/
theorem sum_moebius_sq_eq_squarefreeCountNat (N : ℕ) :
    (∑ n ∈ Icc 1 N, (ArithmeticFunction.moebius n) ^ 2 : ℤ) =
      squarefreeCountNat N := by
  simp only [squarefreeCountNat, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero,
    Nat.cast_one]
  apply sum_congr rfl
  intro n hn
  rw [ArithmeticFunction.moebius_sq]
  by_cases hs : Squarefree n
  · simp [hs]
  · simp [hs]

noncomputable section

/-- The squarefree counting function on the reals. -/
def squarefreeCount (x : ℝ) : ℕ := squarefreeCountNat ⌊x⌋₊

/-- The error term in the squarefree counting problem. -/
def R (x : ℝ) : ℝ := squarefreeCount x - density * x

/-- The real-valued Möbius function. -/
def muR (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ)

/-- The summatory Möbius function. -/
def mertens (N : ℕ) : ℝ := ∑ n ∈ Icc 1 N, muR n

/-- Integer-valued version of `mertens`, used for exact certificates. -/
def mertensInt (N : ℕ) : ℤ :=
  ∑ n ∈ Icc 1 N, ArithmeticFunction.moebius n

/-- Updating the integer Mertens sum by one integer. -/
theorem mertensInt_succ (N : ℕ) :
    mertensInt (N + 1) = mertensInt N + ArithmeticFunction.moebius (N + 1) := by
  simp only [mertensInt]
  rw [sum_Icc_succ_top (by omega : 1 ≤ N + 1)]

/-- Moser--MacLeod's bounded periodic auxiliary function. -/
def auxF (n : ℕ) : ℤ :=
  (n : ℤ) - (n / 2 : ℕ) - (n / 3 : ℕ) - (n / 5 : ℕ) + (n / 30 : ℕ)

/-- The classical floor-Möbius sum. -/
def floorMobius (N : ℕ) : ℤ :=
  ∑ d ∈ Icc 1 N, ArithmeticFunction.moebius d * (N / d : ℕ)

/-- Rational bounds used by the finite certificate. -/
def densityLower : ℚ := 607 / 1000
def densityUpper : ℚ := 609 / 1000

theorem density_bounds :
    ((densityLower : ℚ) : ℝ) < density ∧ density < ((densityUpper : ℚ) : ℝ) := by
  have hp : 0 < Real.pi ^ 2 := sq_pos_of_pos Real.pi_pos
  constructor
  · apply (lt_div_iff₀ hp).2
    dsimp [densityLower]
    nlinarith [Real.pi_lt_d4, Real.pi_pos]
  · apply (div_lt_iff₀ hp).2
    dsimp [densityUpper]
    nlinarith [Real.pi_gt_d4, Real.pi_pos]

/-- A rational endpoint check, with the true density allowed to vary throughout
the certified interval `[607/1000, 609/1000]`. -/
def endpointOK (q n : ℕ) : Prop :=
  (((q : ℚ) - densityLower * n) ^ 2 < n) ∧
  (((q : ℚ) - densityUpper * n) ^ 2 < n)

/-- Executable counterpart of `endpointOK`. -/
def endpointOKb (q n : ℕ) : Bool :=
  decide ((((q : ℚ) - densityLower * n) ^ 2 < n) ∧
    (((q : ℚ) - densityUpper * n) ^ 2 < n))

theorem endpointOK_sound {q n : ℕ} (hn : 0 < n) (h : endpointOK q n) :
    |(q : ℝ) - density * n| < Real.sqrt n := by
  rcases density_bounds with ⟨hcL, hcU⟩
  rcases h with ⟨hL, hU⟩
  have hL' :
      (((q : ℝ) - ((densityLower : ℚ) : ℝ) * n) ^ 2 : ℝ) < n := by
    exact_mod_cast hL
  have hU' :
      (((q : ℝ) - ((densityUpper : ℚ) : ℝ) * n) ^ 2 : ℝ) < n := by
    exact_mod_cast hU
  have hs0 : 0 ≤ Real.sqrt (n : ℝ) := Real.sqrt_nonneg _
  have hs2 : Real.sqrt (n : ℝ) ^ 2 = n := Real.sq_sqrt (by positivity)
  have hLn :
      -Real.sqrt (n : ℝ) < (q : ℝ) - ((densityLower : ℚ) : ℝ) * n ∧
        (q : ℝ) - ((densityLower : ℚ) : ℝ) * n < Real.sqrt n := by
    constructor <;> nlinarith
  have hUn :
      -Real.sqrt (n : ℝ) < (q : ℝ) - ((densityUpper : ℚ) : ℝ) * n ∧
        (q : ℝ) - ((densityUpper : ℚ) : ℝ) * n < Real.sqrt n := by
    constructor <;> nlinarith
  rw [abs_lt]
  have hn0 : (0 : ℝ) ≤ n := by positivity
  constructor <;> nlinarith

/-- The Dirichlet series of the Möbius function at `2` is `6 / π²`. -/
theorem hasSum_mu_div_sq :
    HasSum (fun n : ℕ ↦ if n = 0 then 0 else muR n / (n : ℝ) ^ 2) density := by
  apply Complex.hasSum_ofReal.mp
  have hs : (1 : ℝ) < ((2 : ℂ).re) := by norm_num
  have hsum :=
    (ArithmeticFunction.LSeriesSummable_moebius_iff.mpr hs).LSeriesHasSum
  have hz : L (1 : ℕ → ℂ) (2 : ℂ) =
      (Real.pi : ℂ) ^ 2 / 6 := by
    rw [LSeries_one_eq_riemannZeta hs, riemannZeta_two]
  have hprod := LSeries_one_mul_Lseries_moebius hs
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hmu : L ↗ArithmeticFunction.moebius (2 : ℂ) = (6 : ℂ) / (Real.pi : ℂ) ^ 2 := by
    rw [hz] at hprod
    field_simp [hpi] at hprod ⊢
    linear_combination hprod
  rw [hmu] at hsum
  change HasSum (LSeries.term (fun n ↦ (ArithmeticFunction.moebius n : ℂ)) 2)
    (6 / (Real.pi : ℂ) ^ 2) at hsum
  have hterm :
      (fun n : ℕ ↦ ((if n = 0 then 0 else muR n / (n : ℝ) ^ 2 : ℝ) : ℂ)) =
        LSeries.term (fun n ↦ (ArithmeticFunction.moebius n : ℂ)) 2 := by
    funext n
    by_cases hn : n = 0
    · simp [hn]
    · simp [hn, muR, LSeries.term_of_ne_zero]
  rw [hterm]
  convert hsum using 1
  all_goals simp [density]

/-- A deliberately simple squarefree-count bound: a squarefree integer is
not divisible by `4`. -/
theorem squarefreeCountNat_le_three_quarters (N : ℕ) :
    (squarefreeCountNat N : ℝ) ≤ (3 / 4 : ℝ) * N + 3 / 4 := by
  classical
  let S := (Ioc 0 N).filter fun n ↦ ArithmeticFunction.moebius n ≠ 0
  let T := (Ioc 0 N).filter fun n ↦ ¬4 ∣ n
  have hq : squarefreeCountNat N = #S := by
    simp only [squarefreeCountNat, S]
    rw [← Icc_add_one_left_eq_Ioc]
    simpa [ite_not] using
      (sum_boole (R := ℕ) (fun n ↦ ArithmeticFunction.moebius n ≠ 0) (Icc 1 N))
  have hST : S ⊆ T := by
    intro n hn
    simp only [S, T, mem_filter, mem_Ioc] at hn ⊢
    refine ⟨hn.1, ?_⟩
    intro h4
    have hsq : Squarefree n :=
      ArithmeticFunction.moebius_ne_zero_iff_squarefree.mp hn.2
    have hu := hsq 2 (by simpa [pow_two] using h4)
    norm_num at hu
  have hdiv : #((Ioc 0 N).filter fun n ↦ 4 ∣ n) = N / 4 := by
    exact Nat.Ioc_filter_dvd_card_eq_div N 4
  have hnot : #T = N - N / 4 := by
    have hsplit := filter_card_add_filter_neg_card_eq_card
      (s := Ioc 0 N) (fun n ↦ 4 ∣ n)
    simp only [Nat.card_Ioc, Nat.sub_zero, hdiv, T] at hsplit ⊢
    omega
  have hnat : squarefreeCountNat N ≤ N - N / 4 := by
    rw [hq, ← hnot]
    exact card_le_card hST
  have hround : 4 * (N - N / 4) ≤ 3 * N + 3 := by omega
  norm_num at ⊢
  have hnat' : (squarefreeCountNat N : ℝ) ≤ (N - N / 4 : ℕ) := by
    exact_mod_cast hnat
  have hround' : (4 : ℝ) * (N - N / 4 : ℕ) ≤ 3 * N + 3 := by
    exact_mod_cast hround
  nlinarith

/-- The elementary identity `∑_{d≤N} μ(d) ⌊N/d⌋ = 1`. -/
theorem floorMobius_eq_one (N : ℕ) (hN : 1 ≤ N) : floorMobius N = 1 := by
  classical
  have hrow (d : ℕ) :
      ArithmeticFunction.moebius d * (N / d : ℕ) =
        ∑ k ∈ Ioc 0 N, if d ∣ k then ArithmeticFunction.moebius d else 0 := by
    rw [← Nat.Ioc_filter_dvd_card_eq_div N d]
    simp only [sum_ite, sum_const_zero, add_zero, sum_const, nsmul_eq_mul]
    ring
  have hinner (k : ℕ) (hk : k ∈ Ioc 0 N) :
      (∑ d ∈ Ioc 0 N, if d ∣ k then ArithmeticFunction.moebius d else 0) =
        ∑ d ∈ k.divisors, ArithmeticFunction.moebius d := by
    rcases Finset.mem_Ioc.mp hk with ⟨hkpos, hkle⟩
    have hk0 : k ≠ 0 := hkpos.ne'
    have hfilter : (Ioc 0 N).filter (fun d ↦ d ∣ k) = k.divisors := by
      ext d
      simp only [mem_filter, mem_Ioc, Nat.mem_divisors]
      constructor
      · rintro ⟨hdI, hdk⟩
        exact ⟨hdk, hk0⟩
      · rintro ⟨hdk, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdk hkpos, (Nat.le_of_dvd hkpos hdk).trans hkle⟩, hdk⟩
    rw [← hfilter]
    simp [sum_filter]
  have hdiv (k : ℕ) :
      (∑ d ∈ k.divisors, ArithmeticFunction.moebius d) =
        if k = 1 then 1 else 0 := by
    calc
      _ = (ArithmeticFunction.moebius *
          (ArithmeticFunction.zeta : ArithmeticFunction ℤ)) k :=
        ArithmeticFunction.coe_mul_zeta_apply.symm
      _ = (1 : ArithmeticFunction ℤ) k := by
        rw [ArithmeticFunction.moebius_mul_coe_zeta]
      _ = _ := ArithmeticFunction.one_apply
  rw [floorMobius, show Icc 1 N = Ioc 0 N by
    simpa using (Icc_add_one_left_eq_Ioc (0 : ℕ) N)]
  calc
    ∑ d ∈ Ioc 0 N, ArithmeticFunction.moebius d * (N / d : ℕ) =
        ∑ d ∈ Ioc 0 N, ∑ k ∈ Ioc 0 N,
          if d ∣ k then ArithmeticFunction.moebius d else 0 := by
      exact sum_congr rfl fun d _ ↦ hrow d
    _ = ∑ k ∈ Ioc 0 N, ∑ d ∈ Ioc 0 N,
          if d ∣ k then ArithmeticFunction.moebius d else 0 := by
      rw [sum_comm]
    _ = ∑ k ∈ Ioc 0 N, ∑ d ∈ k.divisors, ArithmeticFunction.moebius d := by
      exact sum_congr rfl hinner
    _ = ∑ k ∈ Ioc 0 N, if k = 1 then 1 else 0 := by
      exact sum_congr rfl fun k _ ↦ hdiv k
    _ = 1 := by simp [hN]

theorem auxF_periodic (n : ℕ) : auxF (n + 30) = auxF n := by
  have h2 : (n + 30) / 2 = n / 2 + 15 := by
    rw [Nat.add_div_of_dvd_left (a := n) (by norm_num : 2 ∣ 30)]
    norm_num
  have h3 : (n + 30) / 3 = n / 3 + 10 := by
    rw [Nat.add_div_of_dvd_left (a := n) (by norm_num : 3 ∣ 30)]
    norm_num
  have h5 : (n + 30) / 5 = n / 5 + 6 := by
    rw [Nat.add_div_of_dvd_left (a := n) (by norm_num : 5 ∣ 30)]
    norm_num
  have h30 : (n + 30) / 30 = n / 30 + 1 := by
    rw [Nat.add_div_of_dvd_left (a := n) (by norm_num : 30 ∣ 30)]
    norm_num
  rw [auxF, auxF, h2, h3, h5, h30]
  push_cast
  ring

theorem auxF_eq_zero_or_one (n : ℕ) : auxF n = 0 ∨ auxF n = 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n < 30
      · interval_cases n <;> norm_num [auxF]
      · have hdecomp : n = (n - 30) + 30 := by omega
        rw [hdecomp, auxF_periodic]
        exact ih (n - 30) (by omega)

theorem auxF_eq_one_of_pos_of_lt_six {n : ℕ} (hn : 0 < n) (hn6 : n < 6) :
    auxF n = 1 := by
  interval_cases n <;> norm_num [auxF]

theorem sum_mu_div_div_eq_one (N m : ℕ) (hm : 0 < m) (hmN : m ≤ N) :
    (∑ d ∈ Icc 1 N,
      ArithmeticFunction.moebius d * ((N / d) / m : ℕ)) = 1 := by
  classical
  have hpoint (d : ℕ) : (N / d) / m = (N / m) / d := by
    rw [Nat.div_div_eq_div_mul, Nat.div_div_eq_div_mul, mul_comm d m]
  simp_rw [hpoint]
  have hsub : Icc 1 (N / m) ⊆ Icc 1 N := by
    intro d hd
    exact mem_Icc.mpr ⟨(mem_Icc.mp hd).1, (mem_Icc.mp hd).2.trans (Nat.div_le_self N m)⟩
  rw [← sum_subset hsub]
  · exact floorMobius_eq_one (N / m) ((Nat.le_div_iff_mul_le hm).2 (by simpa using hmN))
  · intro d hdN hd
    have hlt : N / m < d := by
      have := (mem_Icc.mp hdN).1
      simpa [mem_Icc, this] using hd
    rw [Nat.div_eq_of_lt hlt]
    simp

theorem sum_mu_auxF_eq_neg_one (N : ℕ) (hN : 30 ≤ N) :
    (∑ d ∈ Icc 1 N, ArithmeticFunction.moebius d * auxF (N / d)) = -1 := by
  have h1 := floorMobius_eq_one N (by omega)
  simp only [floorMobius] at h1
  have h2 := sum_mu_div_div_eq_one N 2 (by norm_num) (by omega)
  have h3 := sum_mu_div_div_eq_one N 3 (by norm_num) (by omega)
  have h5 := sum_mu_div_div_eq_one N 5 (by norm_num) (by omega)
  have h30 := sum_mu_div_div_eq_one N 30 (by norm_num) hN
  simp only [auxF]
  simp_rw [mul_add, mul_sub]
  simp only [sum_add_distrib, sum_sub_distrib]
  linear_combination h1 - h2 - h3 - h5 + h30

theorem abs_mertensInt_add_one_le_count (N : ℕ) (hN : 30 ≤ N) :
    |mertensInt N + 1| ≤ (squarefreeCountNat (N / 6) : ℤ) := by
  classical
  have haux := sum_mu_auxF_eq_neg_one N hN
  have hrepr :
      mertensInt N + 1 =
        ∑ d ∈ Icc 1 N,
          ArithmeticFunction.moebius d * (1 - auxF (N / d)) := by
    simp only [mertensInt]
    simp_rw [mul_sub, mul_one]
    simp only [sum_sub_distrib]
    rw [haux]
    ring
  rw [hrepr]
  calc
    _ ≤ ∑ d ∈ Icc 1 N,
        |ArithmeticFunction.moebius d * (1 - auxF (N / d))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ Icc 1 N,
        if d ≤ N / 6 then |ArithmeticFunction.moebius d| else 0 := by
      apply sum_le_sum
      intro d hd
      rcases auxF_eq_zero_or_one (N / d) with hF | hF
      · simp only [hF, sub_zero, mul_one]
        by_cases hdsmall : d ≤ N / 6
        · simp [hdsmall]
        · have hdI := mem_Icc.mp hd
          have hqpos : 0 < N / d := Nat.div_pos hdI.2 hdI.1
          have hqlt : N / d < 6 := by
            by_contra h
            push_neg at h
            have hmul : 6 * d ≤ N := (Nat.le_div_iff_mul_le hdI.1).mp h
            have : d ≤ N / 6 := (Nat.le_div_iff_mul_le (by norm_num)).2 (by
              simpa [mul_comm] using hmul)
            exact hdsmall this
          have hone := auxF_eq_one_of_pos_of_lt_six hqpos hqlt
          omega
      · simp only [hF, sub_self, mul_zero, abs_zero]
        split <;> simp
    _ = ∑ d ∈ Icc 1 (N / 6), |ArithmeticFunction.moebius d| := by
      rw [sum_ite]
      simp only [sum_const_zero, add_zero]
      apply sum_congr
      · ext d
        simp only [mem_filter, mem_Icc]
        omega
      · intro d hd
        rfl
    _ = (squarefreeCountNat (N / 6) : ℤ) := by
      simp only [squarefreeCountNat, Nat.cast_sum, Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
      apply sum_congr rfl
      intro d hd
      rw [ArithmeticFunction.abs_moebius]
      by_cases hs : Squarefree d
      · simp [hs]
      · simp [hs]

theorem mertens_eq_intCast (N : ℕ) : mertens N = (mertensInt N : ℝ) := by
  simp [mertens, mertensInt, muR]

end
end MoserMacLeod
