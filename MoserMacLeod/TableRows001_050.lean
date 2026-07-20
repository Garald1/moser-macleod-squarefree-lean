import MoserMacLeod.Base

/-!
# Proof-producing finite rows 1--50

This generated shard proves the required Möbius values, updates the squarefree
prefix count one integer at a time, and checks the two exact rational endpoint
inequalities in each real cell.  It uses no native evaluator.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction.Moebius BigOperators
open Finset

private theorem mu_001 : μ 1 = 1 :=
  ArithmeticFunction.moebius_apply_one

private theorem count_001 : squarefreeCountNat 1 = 1 := by
  rw [show 1 = 0 + 1 by norm_num, squarefreeCountNat_succ]
  norm_num [squarefreeCountNat, mu_001]

private theorem cell_001 :
    endpointOK (squarefreeCountNat 1) 1 ∧
      endpointOK (squarefreeCountNat 1) (1 + 1) := by
  rw [count_001]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_002 : μ 2 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_002 : squarefreeCountNat 2 = 2 := by
  rw [show 2 = 1 + 1 by norm_num, squarefreeCountNat_succ, count_001]
  norm_num [mu_002]

private theorem cell_002 :
    endpointOK (squarefreeCountNat 2) 2 ∧
      endpointOK (squarefreeCountNat 2) (2 + 1) := by
  rw [count_002]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_003 : μ 3 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_003 : squarefreeCountNat 3 = 3 := by
  rw [show 3 = 2 + 1 by norm_num, squarefreeCountNat_succ, count_002]
  norm_num [mu_003]

private theorem cell_003 :
    endpointOK (squarefreeCountNat 3) 3 ∧
      endpointOK (squarefreeCountNat 3) (3 + 1) := by
  rw [count_003]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_004 : μ 4 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_004 : squarefreeCountNat 4 = 3 := by
  rw [show 4 = 3 + 1 by norm_num, squarefreeCountNat_succ, count_003]
  norm_num [mu_004]

private theorem cell_004 :
    endpointOK (squarefreeCountNat 4) 4 ∧
      endpointOK (squarefreeCountNat 4) (4 + 1) := by
  rw [count_004]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_005 : μ 5 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_005 : squarefreeCountNat 5 = 4 := by
  rw [show 5 = 4 + 1 by norm_num, squarefreeCountNat_succ, count_004]
  norm_num [mu_005]

private theorem cell_005 :
    endpointOK (squarefreeCountNat 5) 5 ∧
      endpointOK (squarefreeCountNat 5) (5 + 1) := by
  rw [count_005]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_006 : μ 6 = 1 := by
  rw [show 6 = 2 * 3 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3)]
  norm_num

private theorem count_006 : squarefreeCountNat 6 = 5 := by
  rw [show 6 = 5 + 1 by norm_num, squarefreeCountNat_succ, count_005]
  norm_num [mu_006]

private theorem cell_006 :
    endpointOK (squarefreeCountNat 6) 6 ∧
      endpointOK (squarefreeCountNat 6) (6 + 1) := by
  rw [count_006]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_007 : μ 7 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_007 : squarefreeCountNat 7 = 6 := by
  rw [show 7 = 6 + 1 by norm_num, squarefreeCountNat_succ, count_006]
  norm_num [mu_007]

private theorem cell_007 :
    endpointOK (squarefreeCountNat 7) 7 ∧
      endpointOK (squarefreeCountNat 7) (7 + 1) := by
  rw [count_007]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_008 : μ 8 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_008 : squarefreeCountNat 8 = 6 := by
  rw [show 8 = 7 + 1 by norm_num, squarefreeCountNat_succ, count_007]
  norm_num [mu_008]

private theorem cell_008 :
    endpointOK (squarefreeCountNat 8) 8 ∧
      endpointOK (squarefreeCountNat 8) (8 + 1) := by
  rw [count_008]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_009 : μ 9 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_009 : squarefreeCountNat 9 = 6 := by
  rw [show 9 = 8 + 1 by norm_num, squarefreeCountNat_succ, count_008]
  norm_num [mu_009]

private theorem cell_009 :
    endpointOK (squarefreeCountNat 9) 9 ∧
      endpointOK (squarefreeCountNat 9) (9 + 1) := by
  rw [count_009]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_010 : μ 10 = 1 := by
  rw [show 10 = 2 * 5 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)]
  norm_num

private theorem count_010 : squarefreeCountNat 10 = 7 := by
  rw [show 10 = 9 + 1 by norm_num, squarefreeCountNat_succ, count_009]
  norm_num [mu_010]

private theorem cell_010 :
    endpointOK (squarefreeCountNat 10) 10 ∧
      endpointOK (squarefreeCountNat 10) (10 + 1) := by
  rw [count_010]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_011 : μ 11 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_011 : squarefreeCountNat 11 = 8 := by
  rw [show 11 = 10 + 1 by norm_num, squarefreeCountNat_succ, count_010]
  norm_num [mu_011]

private theorem cell_011 :
    endpointOK (squarefreeCountNat 11) 11 ∧
      endpointOK (squarefreeCountNat 11) (11 + 1) := by
  rw [count_011]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_012 : μ 12 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_012 : squarefreeCountNat 12 = 8 := by
  rw [show 12 = 11 + 1 by norm_num, squarefreeCountNat_succ, count_011]
  norm_num [mu_012]

private theorem cell_012 :
    endpointOK (squarefreeCountNat 12) 12 ∧
      endpointOK (squarefreeCountNat 12) (12 + 1) := by
  rw [count_012]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_013 : μ 13 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_013 : squarefreeCountNat 13 = 9 := by
  rw [show 13 = 12 + 1 by norm_num, squarefreeCountNat_succ, count_012]
  norm_num [mu_013]

private theorem cell_013 :
    endpointOK (squarefreeCountNat 13) 13 ∧
      endpointOK (squarefreeCountNat 13) (13 + 1) := by
  rw [count_013]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_014 : μ 14 = 1 := by
  rw [show 14 = 2 * 7 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

private theorem count_014 : squarefreeCountNat 14 = 10 := by
  rw [show 14 = 13 + 1 by norm_num, squarefreeCountNat_succ, count_013]
  norm_num [mu_014]

private theorem cell_014 :
    endpointOK (squarefreeCountNat 14) 14 ∧
      endpointOK (squarefreeCountNat 14) (14 + 1) := by
  rw [count_014]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_015 : μ 15 = 1 := by
  rw [show 15 = 3 * 5 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)]
  norm_num

private theorem count_015 : squarefreeCountNat 15 = 11 := by
  rw [show 15 = 14 + 1 by norm_num, squarefreeCountNat_succ, count_014]
  norm_num [mu_015]

private theorem cell_015 :
    endpointOK (squarefreeCountNat 15) 15 ∧
      endpointOK (squarefreeCountNat 15) (15 + 1) := by
  rw [count_015]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_016 : μ 16 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_016 : squarefreeCountNat 16 = 11 := by
  rw [show 16 = 15 + 1 by norm_num, squarefreeCountNat_succ, count_015]
  norm_num [mu_016]

private theorem cell_016 :
    endpointOK (squarefreeCountNat 16) 16 ∧
      endpointOK (squarefreeCountNat 16) (16 + 1) := by
  rw [count_016]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_017 : μ 17 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_017 : squarefreeCountNat 17 = 12 := by
  rw [show 17 = 16 + 1 by norm_num, squarefreeCountNat_succ, count_016]
  norm_num [mu_017]

private theorem cell_017 :
    endpointOK (squarefreeCountNat 17) 17 ∧
      endpointOK (squarefreeCountNat 17) (17 + 1) := by
  rw [count_017]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_018 : μ 18 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_018 : squarefreeCountNat 18 = 12 := by
  rw [show 18 = 17 + 1 by norm_num, squarefreeCountNat_succ, count_017]
  norm_num [mu_018]

private theorem cell_018 :
    endpointOK (squarefreeCountNat 18) 18 ∧
      endpointOK (squarefreeCountNat 18) (18 + 1) := by
  rw [count_018]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_019 : μ 19 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_019 : squarefreeCountNat 19 = 13 := by
  rw [show 19 = 18 + 1 by norm_num, squarefreeCountNat_succ, count_018]
  norm_num [mu_019]

private theorem cell_019 :
    endpointOK (squarefreeCountNat 19) 19 ∧
      endpointOK (squarefreeCountNat 19) (19 + 1) := by
  rw [count_019]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_020 : μ 20 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_020 : squarefreeCountNat 20 = 13 := by
  rw [show 20 = 19 + 1 by norm_num, squarefreeCountNat_succ, count_019]
  norm_num [mu_020]

private theorem cell_020 :
    endpointOK (squarefreeCountNat 20) 20 ∧
      endpointOK (squarefreeCountNat 20) (20 + 1) := by
  rw [count_020]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_021 : μ 21 = 1 := by
  rw [show 21 = 3 * 7 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

private theorem count_021 : squarefreeCountNat 21 = 14 := by
  rw [show 21 = 20 + 1 by norm_num, squarefreeCountNat_succ, count_020]
  norm_num [mu_021]

private theorem cell_021 :
    endpointOK (squarefreeCountNat 21) 21 ∧
      endpointOK (squarefreeCountNat 21) (21 + 1) := by
  rw [count_021]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_022 : μ 22 = 1 := by
  rw [show 22 = 2 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_022 : squarefreeCountNat 22 = 15 := by
  rw [show 22 = 21 + 1 by norm_num, squarefreeCountNat_succ, count_021]
  norm_num [mu_022]

private theorem cell_022 :
    endpointOK (squarefreeCountNat 22) 22 ∧
      endpointOK (squarefreeCountNat 22) (22 + 1) := by
  rw [count_022]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_023 : μ 23 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_023 : squarefreeCountNat 23 = 16 := by
  rw [show 23 = 22 + 1 by norm_num, squarefreeCountNat_succ, count_022]
  norm_num [mu_023]

private theorem cell_023 :
    endpointOK (squarefreeCountNat 23) 23 ∧
      endpointOK (squarefreeCountNat 23) (23 + 1) := by
  rw [count_023]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_024 : μ 24 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_024 : squarefreeCountNat 24 = 16 := by
  rw [show 24 = 23 + 1 by norm_num, squarefreeCountNat_succ, count_023]
  norm_num [mu_024]

private theorem cell_024 :
    endpointOK (squarefreeCountNat 24) 24 ∧
      endpointOK (squarefreeCountNat 24) (24 + 1) := by
  rw [count_024]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_025 : μ 25 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

private theorem count_025 : squarefreeCountNat 25 = 16 := by
  rw [show 25 = 24 + 1 by norm_num, squarefreeCountNat_succ, count_024]
  norm_num [mu_025]

private theorem cell_025 :
    endpointOK (squarefreeCountNat 25) 25 ∧
      endpointOK (squarefreeCountNat 25) (25 + 1) := by
  rw [count_025]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_026 : μ 26 = 1 := by
  rw [show 26 = 2 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_026 : squarefreeCountNat 26 = 17 := by
  rw [show 26 = 25 + 1 by norm_num, squarefreeCountNat_succ, count_025]
  norm_num [mu_026]

private theorem cell_026 :
    endpointOK (squarefreeCountNat 26) 26 ∧
      endpointOK (squarefreeCountNat 26) (26 + 1) := by
  rw [count_026]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_027 : μ 27 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_027 : squarefreeCountNat 27 = 17 := by
  rw [show 27 = 26 + 1 by norm_num, squarefreeCountNat_succ, count_026]
  norm_num [mu_027]

private theorem cell_027 :
    endpointOK (squarefreeCountNat 27) 27 ∧
      endpointOK (squarefreeCountNat 27) (27 + 1) := by
  rw [count_027]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_028 : μ 28 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_028 : squarefreeCountNat 28 = 17 := by
  rw [show 28 = 27 + 1 by norm_num, squarefreeCountNat_succ, count_027]
  norm_num [mu_028]

private theorem cell_028 :
    endpointOK (squarefreeCountNat 28) 28 ∧
      endpointOK (squarefreeCountNat 28) (28 + 1) := by
  rw [count_028]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_029 : μ 29 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_029 : squarefreeCountNat 29 = 18 := by
  rw [show 29 = 28 + 1 by norm_num, squarefreeCountNat_succ, count_028]
  norm_num [mu_029]

private theorem cell_029 :
    endpointOK (squarefreeCountNat 29) 29 ∧
      endpointOK (squarefreeCountNat 29) (29 + 1) := by
  rw [count_029]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_030 : μ 30 = -1 := by
  rw [show 30 = 2 * 15 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 15 = 3 * 5 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5)]
  norm_num

private theorem count_030 : squarefreeCountNat 30 = 19 := by
  rw [show 30 = 29 + 1 by norm_num, squarefreeCountNat_succ, count_029]
  norm_num [mu_030]

private theorem cell_030 :
    endpointOK (squarefreeCountNat 30) 30 ∧
      endpointOK (squarefreeCountNat 30) (30 + 1) := by
  rw [count_030]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_031 : μ 31 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_031 : squarefreeCountNat 31 = 20 := by
  rw [show 31 = 30 + 1 by norm_num, squarefreeCountNat_succ, count_030]
  norm_num [mu_031]

private theorem cell_031 :
    endpointOK (squarefreeCountNat 31) 31 ∧
      endpointOK (squarefreeCountNat 31) (31 + 1) := by
  rw [count_031]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_032 : μ 32 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_032 : squarefreeCountNat 32 = 20 := by
  rw [show 32 = 31 + 1 by norm_num, squarefreeCountNat_succ, count_031]
  norm_num [mu_032]

private theorem cell_032 :
    endpointOK (squarefreeCountNat 32) 32 ∧
      endpointOK (squarefreeCountNat 32) (32 + 1) := by
  rw [count_032]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_033 : μ 33 = 1 := by
  rw [show 33 = 3 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_033 : squarefreeCountNat 33 = 21 := by
  rw [show 33 = 32 + 1 by norm_num, squarefreeCountNat_succ, count_032]
  norm_num [mu_033]

private theorem cell_033 :
    endpointOK (squarefreeCountNat 33) 33 ∧
      endpointOK (squarefreeCountNat 33) (33 + 1) := by
  rw [count_033]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_034 : μ 34 = 1 := by
  rw [show 34 = 2 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_034 : squarefreeCountNat 34 = 22 := by
  rw [show 34 = 33 + 1 by norm_num, squarefreeCountNat_succ, count_033]
  norm_num [mu_034]

private theorem cell_034 :
    endpointOK (squarefreeCountNat 34) 34 ∧
      endpointOK (squarefreeCountNat 34) (34 + 1) := by
  rw [count_034]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_035 : μ 35 = 1 := by
  rw [show 35 = 5 * 7 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

private theorem count_035 : squarefreeCountNat 35 = 23 := by
  rw [show 35 = 34 + 1 by norm_num, squarefreeCountNat_succ, count_034]
  norm_num [mu_035]

private theorem cell_035 :
    endpointOK (squarefreeCountNat 35) 35 ∧
      endpointOK (squarefreeCountNat 35) (35 + 1) := by
  rw [count_035]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_036 : μ 36 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_036 : squarefreeCountNat 36 = 23 := by
  rw [show 36 = 35 + 1 by norm_num, squarefreeCountNat_succ, count_035]
  norm_num [mu_036]

private theorem cell_036 :
    endpointOK (squarefreeCountNat 36) 36 ∧
      endpointOK (squarefreeCountNat 36) (36 + 1) := by
  rw [count_036]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_037 : μ 37 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_037 : squarefreeCountNat 37 = 24 := by
  rw [show 37 = 36 + 1 by norm_num, squarefreeCountNat_succ, count_036]
  norm_num [mu_037]

private theorem cell_037 :
    endpointOK (squarefreeCountNat 37) 37 ∧
      endpointOK (squarefreeCountNat 37) (37 + 1) := by
  rw [count_037]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_038 : μ 38 = 1 := by
  rw [show 38 = 2 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_038 : squarefreeCountNat 38 = 25 := by
  rw [show 38 = 37 + 1 by norm_num, squarefreeCountNat_succ, count_037]
  norm_num [mu_038]

private theorem cell_038 :
    endpointOK (squarefreeCountNat 38) 38 ∧
      endpointOK (squarefreeCountNat 38) (38 + 1) := by
  rw [count_038]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_039 : μ 39 = 1 := by
  rw [show 39 = 3 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_039 : squarefreeCountNat 39 = 26 := by
  rw [show 39 = 38 + 1 by norm_num, squarefreeCountNat_succ, count_038]
  norm_num [mu_039]

private theorem cell_039 :
    endpointOK (squarefreeCountNat 39) 39 ∧
      endpointOK (squarefreeCountNat 39) (39 + 1) := by
  rw [count_039]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_040 : μ 40 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_040 : squarefreeCountNat 40 = 26 := by
  rw [show 40 = 39 + 1 by norm_num, squarefreeCountNat_succ, count_039]
  norm_num [mu_040]

private theorem cell_040 :
    endpointOK (squarefreeCountNat 40) 40 ∧
      endpointOK (squarefreeCountNat 40) (40 + 1) := by
  rw [count_040]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_041 : μ 41 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_041 : squarefreeCountNat 41 = 27 := by
  rw [show 41 = 40 + 1 by norm_num, squarefreeCountNat_succ, count_040]
  norm_num [mu_041]

private theorem cell_041 :
    endpointOK (squarefreeCountNat 41) 41 ∧
      endpointOK (squarefreeCountNat 41) (41 + 1) := by
  rw [count_041]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_042 : μ 42 = -1 := by
  rw [show 42 = 2 * 21 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 21 = 3 * 7 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

private theorem count_042 : squarefreeCountNat 42 = 28 := by
  rw [show 42 = 41 + 1 by norm_num, squarefreeCountNat_succ, count_041]
  norm_num [mu_042]

private theorem cell_042 :
    endpointOK (squarefreeCountNat 42) 42 ∧
      endpointOK (squarefreeCountNat 42) (42 + 1) := by
  rw [count_042]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_043 : μ 43 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_043 : squarefreeCountNat 43 = 29 := by
  rw [show 43 = 42 + 1 by norm_num, squarefreeCountNat_succ, count_042]
  norm_num [mu_043]

private theorem cell_043 :
    endpointOK (squarefreeCountNat 43) 43 ∧
      endpointOK (squarefreeCountNat 43) (43 + 1) := by
  rw [count_043]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_044 : μ 44 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_044 : squarefreeCountNat 44 = 29 := by
  rw [show 44 = 43 + 1 by norm_num, squarefreeCountNat_succ, count_043]
  norm_num [mu_044]

private theorem cell_044 :
    endpointOK (squarefreeCountNat 44) 44 ∧
      endpointOK (squarefreeCountNat 44) (44 + 1) := by
  rw [count_044]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_045 : μ 45 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_045 : squarefreeCountNat 45 = 29 := by
  rw [show 45 = 44 + 1 by norm_num, squarefreeCountNat_succ, count_044]
  norm_num [mu_045]

private theorem cell_045 :
    endpointOK (squarefreeCountNat 45) 45 ∧
      endpointOK (squarefreeCountNat 45) (45 + 1) := by
  rw [count_045]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_046 : μ 46 = 1 := by
  rw [show 46 = 2 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_046 : squarefreeCountNat 46 = 30 := by
  rw [show 46 = 45 + 1 by norm_num, squarefreeCountNat_succ, count_045]
  norm_num [mu_046]

private theorem cell_046 :
    endpointOK (squarefreeCountNat 46) 46 ∧
      endpointOK (squarefreeCountNat 46) (46 + 1) := by
  rw [count_046]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_047 : μ 47 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_047 : squarefreeCountNat 47 = 31 := by
  rw [show 47 = 46 + 1 by norm_num, squarefreeCountNat_succ, count_046]
  norm_num [mu_047]

private theorem cell_047 :
    endpointOK (squarefreeCountNat 47) 47 ∧
      endpointOK (squarefreeCountNat 47) (47 + 1) := by
  rw [count_047]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_048 : μ 48 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_048 : squarefreeCountNat 48 = 31 := by
  rw [show 48 = 47 + 1 by norm_num, squarefreeCountNat_succ, count_047]
  norm_num [mu_048]

private theorem cell_048 :
    endpointOK (squarefreeCountNat 48) 48 ∧
      endpointOK (squarefreeCountNat 48) (48 + 1) := by
  rw [count_048]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_049 : μ 49 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 7 (by norm_num) (by norm_num)

private theorem count_049 : squarefreeCountNat 49 = 31 := by
  rw [show 49 = 48 + 1 by norm_num, squarefreeCountNat_succ, count_048]
  norm_num [mu_049]

private theorem cell_049 :
    endpointOK (squarefreeCountNat 49) 49 ∧
      endpointOK (squarefreeCountNat 49) (49 + 1) := by
  rw [count_049]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_050 : μ 50 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

theorem count_050 : squarefreeCountNat 50 = 31 := by
  rw [show 50 = 49 + 1 by norm_num, squarefreeCountNat_succ, count_049]
  norm_num [mu_050]

private theorem cell_050 :
    endpointOK (squarefreeCountNat 50) 50 ∧
      endpointOK (squarefreeCountNat 50) (50 + 1) := by
  rw [count_050]
  norm_num [endpointOK, densityLower, densityUpper]

theorem finite_endpoint_certificate_001_050 (N : ℕ)
    (hlo : 1 ≤ N) (hhi : N ≤ 50) :
    endpointOK (squarefreeCountNat N) N ∧
      endpointOK (squarefreeCountNat N) (N + 1) := by
  interval_cases N
  · exact cell_001
  · exact cell_002
  · exact cell_003
  · exact cell_004
  · exact cell_005
  · exact cell_006
  · exact cell_007
  · exact cell_008
  · exact cell_009
  · exact cell_010
  · exact cell_011
  · exact cell_012
  · exact cell_013
  · exact cell_014
  · exact cell_015
  · exact cell_016
  · exact cell_017
  · exact cell_018
  · exact cell_019
  · exact cell_020
  · exact cell_021
  · exact cell_022
  · exact cell_023
  · exact cell_024
  · exact cell_025
  · exact cell_026
  · exact cell_027
  · exact cell_028
  · exact cell_029
  · exact cell_030
  · exact cell_031
  · exact cell_032
  · exact cell_033
  · exact cell_034
  · exact cell_035
  · exact cell_036
  · exact cell_037
  · exact cell_038
  · exact cell_039
  · exact cell_040
  · exact cell_041
  · exact cell_042
  · exact cell_043
  · exact cell_044
  · exact cell_045
  · exact cell_046
  · exact cell_047
  · exact cell_048
  · exact cell_049
  · exact cell_050

/-- The small cases needed before the paper's periodic argument applies. -/
private theorem mertens_000 : mertensInt 0 = 0 := by
  norm_num [mertensInt]

private theorem mertens_001 : mertensInt 1 = 1 := by
  rw [show 1 = 0 + 1 by norm_num, mertensInt_succ, mertens_000, mu_001]
  norm_num

private theorem mertens_002 : mertensInt 2 = 0 := by
  rw [show 2 = 1 + 1 by norm_num, mertensInt_succ, mertens_001, mu_002]
  norm_num

private theorem mertens_003 : mertensInt 3 = -1 := by
  rw [show 3 = 2 + 1 by norm_num, mertensInt_succ, mertens_002, mu_003]
  norm_num

private theorem mertens_004 : mertensInt 4 = -1 := by
  rw [show 4 = 3 + 1 by norm_num, mertensInt_succ, mertens_003, mu_004]
  norm_num

private theorem mertens_005 : mertensInt 5 = -2 := by
  rw [show 5 = 4 + 1 by norm_num, mertensInt_succ, mertens_004, mu_005]
  norm_num

private theorem mertens_006 : mertensInt 6 = -1 := by
  rw [show 6 = 5 + 1 by norm_num, mertensInt_succ, mertens_005, mu_006]
  norm_num

private theorem mertens_007 : mertensInt 7 = -2 := by
  rw [show 7 = 6 + 1 by norm_num, mertensInt_succ, mertens_006, mu_007]
  norm_num

private theorem mertens_008 : mertensInt 8 = -2 := by
  rw [show 8 = 7 + 1 by norm_num, mertensInt_succ, mertens_007, mu_008]
  norm_num

private theorem mertens_009 : mertensInt 9 = -2 := by
  rw [show 9 = 8 + 1 by norm_num, mertensInt_succ, mertens_008, mu_009]
  norm_num

private theorem mertens_010 : mertensInt 10 = -1 := by
  rw [show 10 = 9 + 1 by norm_num, mertensInt_succ, mertens_009, mu_010]
  norm_num

private theorem mertens_011 : mertensInt 11 = -2 := by
  rw [show 11 = 10 + 1 by norm_num, mertensInt_succ, mertens_010, mu_011]
  norm_num

private theorem mertens_012 : mertensInt 12 = -2 := by
  rw [show 12 = 11 + 1 by norm_num, mertensInt_succ, mertens_011, mu_012]
  norm_num

private theorem mertens_013 : mertensInt 13 = -3 := by
  rw [show 13 = 12 + 1 by norm_num, mertensInt_succ, mertens_012, mu_013]
  norm_num

private theorem mertens_014 : mertensInt 14 = -2 := by
  rw [show 14 = 13 + 1 by norm_num, mertensInt_succ, mertens_013, mu_014]
  norm_num

private theorem mertens_015 : mertensInt 15 = -1 := by
  rw [show 15 = 14 + 1 by norm_num, mertensInt_succ, mertens_014, mu_015]
  norm_num

private theorem mertens_016 : mertensInt 16 = -1 := by
  rw [show 16 = 15 + 1 by norm_num, mertensInt_succ, mertens_015, mu_016]
  norm_num

private theorem mertens_017 : mertensInt 17 = -2 := by
  rw [show 17 = 16 + 1 by norm_num, mertensInt_succ, mertens_016, mu_017]
  norm_num

private theorem mertens_018 : mertensInt 18 = -2 := by
  rw [show 18 = 17 + 1 by norm_num, mertensInt_succ, mertens_017, mu_018]
  norm_num

private theorem mertens_019 : mertensInt 19 = -3 := by
  rw [show 19 = 18 + 1 by norm_num, mertensInt_succ, mertens_018, mu_019]
  norm_num

private theorem mertens_020 : mertensInt 20 = -3 := by
  rw [show 20 = 19 + 1 by norm_num, mertensInt_succ, mertens_019, mu_020]
  norm_num

private theorem mertens_021 : mertensInt 21 = -2 := by
  rw [show 21 = 20 + 1 by norm_num, mertensInt_succ, mertens_020, mu_021]
  norm_num

private theorem mertens_022 : mertensInt 22 = -1 := by
  rw [show 22 = 21 + 1 by norm_num, mertensInt_succ, mertens_021, mu_022]
  norm_num

private theorem mertens_023 : mertensInt 23 = -2 := by
  rw [show 23 = 22 + 1 by norm_num, mertensInt_succ, mertens_022, mu_023]
  norm_num

private theorem mertens_024 : mertensInt 24 = -2 := by
  rw [show 24 = 23 + 1 by norm_num, mertensInt_succ, mertens_023, mu_024]
  norm_num

private theorem mertens_025 : mertensInt 25 = -2 := by
  rw [show 25 = 24 + 1 by norm_num, mertensInt_succ, mertens_024, mu_025]
  norm_num

private theorem mertens_026 : mertensInt 26 = -1 := by
  rw [show 26 = 25 + 1 by norm_num, mertensInt_succ, mertens_025, mu_026]
  norm_num

private theorem mertens_027 : mertensInt 27 = -1 := by
  rw [show 27 = 26 + 1 by norm_num, mertensInt_succ, mertens_026, mu_027]
  norm_num

private theorem mertens_028 : mertensInt 28 = -1 := by
  rw [show 28 = 27 + 1 by norm_num, mertensInt_succ, mertens_027, mu_028]
  norm_num

private theorem mertens_029 : mertensInt 29 = -2 := by
  rw [show 29 = 28 + 1 by norm_num, mertensInt_succ, mertens_028, mu_029]
  norm_num

theorem small_mertens_bound (N : ℕ) (hlo : 2 ≤ N) (hhi : N < 30) :
    (8 : ℤ) * |mertensInt N + 1| ≤ (N : ℤ) + 6 := by
  interval_cases N
  · rw [mertens_002]
    norm_num
  · rw [mertens_003]
    norm_num
  · rw [mertens_004]
    norm_num
  · rw [mertens_005]
    norm_num
  · rw [mertens_006]
    norm_num
  · rw [mertens_007]
    norm_num
  · rw [mertens_008]
    norm_num
  · rw [mertens_009]
    norm_num
  · rw [mertens_010]
    norm_num
  · rw [mertens_011]
    norm_num
  · rw [mertens_012]
    norm_num
  · rw [mertens_013]
    norm_num
  · rw [mertens_014]
    norm_num
  · rw [mertens_015]
    norm_num
  · rw [mertens_016]
    norm_num
  · rw [mertens_017]
    norm_num
  · rw [mertens_018]
    norm_num
  · rw [mertens_019]
    norm_num
  · rw [mertens_020]
    norm_num
  · rw [mertens_021]
    norm_num
  · rw [mertens_022]
    norm_num
  · rw [mertens_023]
    norm_num
  · rw [mertens_024]
    norm_num
  · rw [mertens_025]
    norm_num
  · rw [mertens_026]
    norm_num
  · rw [mertens_027]
    norm_num
  · rw [mertens_028]
    norm_num
  · rw [mertens_029]
    norm_num

end MoserMacLeod
