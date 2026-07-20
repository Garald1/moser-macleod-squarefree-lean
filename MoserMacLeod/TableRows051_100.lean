import MoserMacLeod.TableRows001_050

/-!
# Proof-producing finite rows 51--100

This generated shard proves the required Möbius values, updates the squarefree
prefix count one integer at a time, and checks the two exact rational endpoint
inequalities in each real cell.  It uses no native evaluator.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction.Moebius BigOperators
open Finset

private theorem mu_051 : μ 51 = 1 := by
  rw [show 51 = 3 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_051 : squarefreeCountNat 51 = 32 := by
  rw [show 51 = 50 + 1 by norm_num, squarefreeCountNat_succ, count_050]
  norm_num [mu_051]

private theorem cell_051 :
    endpointOK (squarefreeCountNat 51) 51 ∧
      endpointOK (squarefreeCountNat 51) (51 + 1) := by
  rw [count_051]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_052 : μ 52 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_052 : squarefreeCountNat 52 = 32 := by
  rw [show 52 = 51 + 1 by norm_num, squarefreeCountNat_succ, count_051]
  norm_num [mu_052]

private theorem cell_052 :
    endpointOK (squarefreeCountNat 52) 52 ∧
      endpointOK (squarefreeCountNat 52) (52 + 1) := by
  rw [count_052]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_053 : μ 53 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_053 : squarefreeCountNat 53 = 33 := by
  rw [show 53 = 52 + 1 by norm_num, squarefreeCountNat_succ, count_052]
  norm_num [mu_053]

private theorem cell_053 :
    endpointOK (squarefreeCountNat 53) 53 ∧
      endpointOK (squarefreeCountNat 53) (53 + 1) := by
  rw [count_053]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_054 : μ 54 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_054 : squarefreeCountNat 54 = 33 := by
  rw [show 54 = 53 + 1 by norm_num, squarefreeCountNat_succ, count_053]
  norm_num [mu_054]

private theorem cell_054 :
    endpointOK (squarefreeCountNat 54) 54 ∧
      endpointOK (squarefreeCountNat 54) (54 + 1) := by
  rw [count_054]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_055 : μ 55 = 1 := by
  rw [show 55 = 5 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_055 : squarefreeCountNat 55 = 34 := by
  rw [show 55 = 54 + 1 by norm_num, squarefreeCountNat_succ, count_054]
  norm_num [mu_055]

private theorem cell_055 :
    endpointOK (squarefreeCountNat 55) 55 ∧
      endpointOK (squarefreeCountNat 55) (55 + 1) := by
  rw [count_055]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_056 : μ 56 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_056 : squarefreeCountNat 56 = 34 := by
  rw [show 56 = 55 + 1 by norm_num, squarefreeCountNat_succ, count_055]
  norm_num [mu_056]

private theorem cell_056 :
    endpointOK (squarefreeCountNat 56) 56 ∧
      endpointOK (squarefreeCountNat 56) (56 + 1) := by
  rw [count_056]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_057 : μ 57 = 1 := by
  rw [show 57 = 3 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_057 : squarefreeCountNat 57 = 35 := by
  rw [show 57 = 56 + 1 by norm_num, squarefreeCountNat_succ, count_056]
  norm_num [mu_057]

private theorem cell_057 :
    endpointOK (squarefreeCountNat 57) 57 ∧
      endpointOK (squarefreeCountNat 57) (57 + 1) := by
  rw [count_057]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_058 : μ 58 = 1 := by
  rw [show 58 = 2 * 29 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 29)]
  norm_num

private theorem count_058 : squarefreeCountNat 58 = 36 := by
  rw [show 58 = 57 + 1 by norm_num, squarefreeCountNat_succ, count_057]
  norm_num [mu_058]

private theorem cell_058 :
    endpointOK (squarefreeCountNat 58) 58 ∧
      endpointOK (squarefreeCountNat 58) (58 + 1) := by
  rw [count_058]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_059 : μ 59 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_059 : squarefreeCountNat 59 = 37 := by
  rw [show 59 = 58 + 1 by norm_num, squarefreeCountNat_succ, count_058]
  norm_num [mu_059]

private theorem cell_059 :
    endpointOK (squarefreeCountNat 59) 59 ∧
      endpointOK (squarefreeCountNat 59) (59 + 1) := by
  rw [count_059]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_060 : μ 60 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_060 : squarefreeCountNat 60 = 37 := by
  rw [show 60 = 59 + 1 by norm_num, squarefreeCountNat_succ, count_059]
  norm_num [mu_060]

private theorem cell_060 :
    endpointOK (squarefreeCountNat 60) 60 ∧
      endpointOK (squarefreeCountNat 60) (60 + 1) := by
  rw [count_060]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_061 : μ 61 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_061 : squarefreeCountNat 61 = 38 := by
  rw [show 61 = 60 + 1 by norm_num, squarefreeCountNat_succ, count_060]
  norm_num [mu_061]

private theorem cell_061 :
    endpointOK (squarefreeCountNat 61) 61 ∧
      endpointOK (squarefreeCountNat 61) (61 + 1) := by
  rw [count_061]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_062 : μ 62 = 1 := by
  rw [show 62 = 2 * 31 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 31)]
  norm_num

private theorem count_062 : squarefreeCountNat 62 = 39 := by
  rw [show 62 = 61 + 1 by norm_num, squarefreeCountNat_succ, count_061]
  norm_num [mu_062]

private theorem cell_062 :
    endpointOK (squarefreeCountNat 62) 62 ∧
      endpointOK (squarefreeCountNat 62) (62 + 1) := by
  rw [count_062]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_063 : μ 63 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_063 : squarefreeCountNat 63 = 39 := by
  rw [show 63 = 62 + 1 by norm_num, squarefreeCountNat_succ, count_062]
  norm_num [mu_063]

private theorem cell_063 :
    endpointOK (squarefreeCountNat 63) 63 ∧
      endpointOK (squarefreeCountNat 63) (63 + 1) := by
  rw [count_063]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_064 : μ 64 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_064 : squarefreeCountNat 64 = 39 := by
  rw [show 64 = 63 + 1 by norm_num, squarefreeCountNat_succ, count_063]
  norm_num [mu_064]

private theorem cell_064 :
    endpointOK (squarefreeCountNat 64) 64 ∧
      endpointOK (squarefreeCountNat 64) (64 + 1) := by
  rw [count_064]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_065 : μ 65 = 1 := by
  rw [show 65 = 5 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_065 : squarefreeCountNat 65 = 40 := by
  rw [show 65 = 64 + 1 by norm_num, squarefreeCountNat_succ, count_064]
  norm_num [mu_065]

private theorem cell_065 :
    endpointOK (squarefreeCountNat 65) 65 ∧
      endpointOK (squarefreeCountNat 65) (65 + 1) := by
  rw [count_065]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_066 : μ 66 = -1 := by
  rw [show 66 = 2 * 33 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 33 = 3 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_066 : squarefreeCountNat 66 = 41 := by
  rw [show 66 = 65 + 1 by norm_num, squarefreeCountNat_succ, count_065]
  norm_num [mu_066]

private theorem cell_066 :
    endpointOK (squarefreeCountNat 66) 66 ∧
      endpointOK (squarefreeCountNat 66) (66 + 1) := by
  rw [count_066]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_067 : μ 67 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_067 : squarefreeCountNat 67 = 42 := by
  rw [show 67 = 66 + 1 by norm_num, squarefreeCountNat_succ, count_066]
  norm_num [mu_067]

private theorem cell_067 :
    endpointOK (squarefreeCountNat 67) 67 ∧
      endpointOK (squarefreeCountNat 67) (67 + 1) := by
  rw [count_067]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_068 : μ 68 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_068 : squarefreeCountNat 68 = 42 := by
  rw [show 68 = 67 + 1 by norm_num, squarefreeCountNat_succ, count_067]
  norm_num [mu_068]

private theorem cell_068 :
    endpointOK (squarefreeCountNat 68) 68 ∧
      endpointOK (squarefreeCountNat 68) (68 + 1) := by
  rw [count_068]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_069 : μ 69 = 1 := by
  rw [show 69 = 3 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_069 : squarefreeCountNat 69 = 43 := by
  rw [show 69 = 68 + 1 by norm_num, squarefreeCountNat_succ, count_068]
  norm_num [mu_069]

private theorem cell_069 :
    endpointOK (squarefreeCountNat 69) 69 ∧
      endpointOK (squarefreeCountNat 69) (69 + 1) := by
  rw [count_069]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_070 : μ 70 = -1 := by
  rw [show 70 = 2 * 35 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 35 = 5 * 7 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

private theorem count_070 : squarefreeCountNat 70 = 44 := by
  rw [show 70 = 69 + 1 by norm_num, squarefreeCountNat_succ, count_069]
  norm_num [mu_070]

private theorem cell_070 :
    endpointOK (squarefreeCountNat 70) 70 ∧
      endpointOK (squarefreeCountNat 70) (70 + 1) := by
  rw [count_070]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_071 : μ 71 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_071 : squarefreeCountNat 71 = 45 := by
  rw [show 71 = 70 + 1 by norm_num, squarefreeCountNat_succ, count_070]
  norm_num [mu_071]

private theorem cell_071 :
    endpointOK (squarefreeCountNat 71) 71 ∧
      endpointOK (squarefreeCountNat 71) (71 + 1) := by
  rw [count_071]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_072 : μ 72 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_072 : squarefreeCountNat 72 = 45 := by
  rw [show 72 = 71 + 1 by norm_num, squarefreeCountNat_succ, count_071]
  norm_num [mu_072]

private theorem cell_072 :
    endpointOK (squarefreeCountNat 72) 72 ∧
      endpointOK (squarefreeCountNat 72) (72 + 1) := by
  rw [count_072]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_073 : μ 73 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_073 : squarefreeCountNat 73 = 46 := by
  rw [show 73 = 72 + 1 by norm_num, squarefreeCountNat_succ, count_072]
  norm_num [mu_073]

private theorem cell_073 :
    endpointOK (squarefreeCountNat 73) 73 ∧
      endpointOK (squarefreeCountNat 73) (73 + 1) := by
  rw [count_073]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_074 : μ 74 = 1 := by
  rw [show 74 = 2 * 37 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 37)]
  norm_num

private theorem count_074 : squarefreeCountNat 74 = 47 := by
  rw [show 74 = 73 + 1 by norm_num, squarefreeCountNat_succ, count_073]
  norm_num [mu_074]

private theorem cell_074 :
    endpointOK (squarefreeCountNat 74) 74 ∧
      endpointOK (squarefreeCountNat 74) (74 + 1) := by
  rw [count_074]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_075 : μ 75 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

private theorem count_075 : squarefreeCountNat 75 = 47 := by
  rw [show 75 = 74 + 1 by norm_num, squarefreeCountNat_succ, count_074]
  norm_num [mu_075]

private theorem cell_075 :
    endpointOK (squarefreeCountNat 75) 75 ∧
      endpointOK (squarefreeCountNat 75) (75 + 1) := by
  rw [count_075]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_076 : μ 76 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_076 : squarefreeCountNat 76 = 47 := by
  rw [show 76 = 75 + 1 by norm_num, squarefreeCountNat_succ, count_075]
  norm_num [mu_076]

private theorem cell_076 :
    endpointOK (squarefreeCountNat 76) 76 ∧
      endpointOK (squarefreeCountNat 76) (76 + 1) := by
  rw [count_076]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_077 : μ 77 = 1 := by
  rw [show 77 = 7 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_077 : squarefreeCountNat 77 = 48 := by
  rw [show 77 = 76 + 1 by norm_num, squarefreeCountNat_succ, count_076]
  norm_num [mu_077]

private theorem cell_077 :
    endpointOK (squarefreeCountNat 77) 77 ∧
      endpointOK (squarefreeCountNat 77) (77 + 1) := by
  rw [count_077]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_078 : μ 78 = -1 := by
  rw [show 78 = 2 * 39 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 39 = 3 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_078 : squarefreeCountNat 78 = 49 := by
  rw [show 78 = 77 + 1 by norm_num, squarefreeCountNat_succ, count_077]
  norm_num [mu_078]

private theorem cell_078 :
    endpointOK (squarefreeCountNat 78) 78 ∧
      endpointOK (squarefreeCountNat 78) (78 + 1) := by
  rw [count_078]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_079 : μ 79 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_079 : squarefreeCountNat 79 = 50 := by
  rw [show 79 = 78 + 1 by norm_num, squarefreeCountNat_succ, count_078]
  norm_num [mu_079]

private theorem cell_079 :
    endpointOK (squarefreeCountNat 79) 79 ∧
      endpointOK (squarefreeCountNat 79) (79 + 1) := by
  rw [count_079]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_080 : μ 80 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_080 : squarefreeCountNat 80 = 50 := by
  rw [show 80 = 79 + 1 by norm_num, squarefreeCountNat_succ, count_079]
  norm_num [mu_080]

private theorem cell_080 :
    endpointOK (squarefreeCountNat 80) 80 ∧
      endpointOK (squarefreeCountNat 80) (80 + 1) := by
  rw [count_080]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_081 : μ 81 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_081 : squarefreeCountNat 81 = 50 := by
  rw [show 81 = 80 + 1 by norm_num, squarefreeCountNat_succ, count_080]
  norm_num [mu_081]

private theorem cell_081 :
    endpointOK (squarefreeCountNat 81) 81 ∧
      endpointOK (squarefreeCountNat 81) (81 + 1) := by
  rw [count_081]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_082 : μ 82 = 1 := by
  rw [show 82 = 2 * 41 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 41)]
  norm_num

private theorem count_082 : squarefreeCountNat 82 = 51 := by
  rw [show 82 = 81 + 1 by norm_num, squarefreeCountNat_succ, count_081]
  norm_num [mu_082]

private theorem cell_082 :
    endpointOK (squarefreeCountNat 82) 82 ∧
      endpointOK (squarefreeCountNat 82) (82 + 1) := by
  rw [count_082]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_083 : μ 83 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_083 : squarefreeCountNat 83 = 52 := by
  rw [show 83 = 82 + 1 by norm_num, squarefreeCountNat_succ, count_082]
  norm_num [mu_083]

private theorem cell_083 :
    endpointOK (squarefreeCountNat 83) 83 ∧
      endpointOK (squarefreeCountNat 83) (83 + 1) := by
  rw [count_083]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_084 : μ 84 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_084 : squarefreeCountNat 84 = 52 := by
  rw [show 84 = 83 + 1 by norm_num, squarefreeCountNat_succ, count_083]
  norm_num [mu_084]

private theorem cell_084 :
    endpointOK (squarefreeCountNat 84) 84 ∧
      endpointOK (squarefreeCountNat 84) (84 + 1) := by
  rw [count_084]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_085 : μ 85 = 1 := by
  rw [show 85 = 5 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_085 : squarefreeCountNat 85 = 53 := by
  rw [show 85 = 84 + 1 by norm_num, squarefreeCountNat_succ, count_084]
  norm_num [mu_085]

private theorem cell_085 :
    endpointOK (squarefreeCountNat 85) 85 ∧
      endpointOK (squarefreeCountNat 85) (85 + 1) := by
  rw [count_085]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_086 : μ 86 = 1 := by
  rw [show 86 = 2 * 43 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 43)]
  norm_num

private theorem count_086 : squarefreeCountNat 86 = 54 := by
  rw [show 86 = 85 + 1 by norm_num, squarefreeCountNat_succ, count_085]
  norm_num [mu_086]

private theorem cell_086 :
    endpointOK (squarefreeCountNat 86) 86 ∧
      endpointOK (squarefreeCountNat 86) (86 + 1) := by
  rw [count_086]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_087 : μ 87 = 1 := by
  rw [show 87 = 3 * 29 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 29)]
  norm_num

private theorem count_087 : squarefreeCountNat 87 = 55 := by
  rw [show 87 = 86 + 1 by norm_num, squarefreeCountNat_succ, count_086]
  norm_num [mu_087]

private theorem cell_087 :
    endpointOK (squarefreeCountNat 87) 87 ∧
      endpointOK (squarefreeCountNat 87) (87 + 1) := by
  rw [count_087]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_088 : μ 88 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_088 : squarefreeCountNat 88 = 55 := by
  rw [show 88 = 87 + 1 by norm_num, squarefreeCountNat_succ, count_087]
  norm_num [mu_088]

private theorem cell_088 :
    endpointOK (squarefreeCountNat 88) 88 ∧
      endpointOK (squarefreeCountNat 88) (88 + 1) := by
  rw [count_088]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_089 : μ 89 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_089 : squarefreeCountNat 89 = 56 := by
  rw [show 89 = 88 + 1 by norm_num, squarefreeCountNat_succ, count_088]
  norm_num [mu_089]

private theorem cell_089 :
    endpointOK (squarefreeCountNat 89) 89 ∧
      endpointOK (squarefreeCountNat 89) (89 + 1) := by
  rw [count_089]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_090 : μ 90 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_090 : squarefreeCountNat 90 = 56 := by
  rw [show 90 = 89 + 1 by norm_num, squarefreeCountNat_succ, count_089]
  norm_num [mu_090]

private theorem cell_090 :
    endpointOK (squarefreeCountNat 90) 90 ∧
      endpointOK (squarefreeCountNat 90) (90 + 1) := by
  rw [count_090]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_091 : μ 91 = 1 := by
  rw [show 91 = 7 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_091 : squarefreeCountNat 91 = 57 := by
  rw [show 91 = 90 + 1 by norm_num, squarefreeCountNat_succ, count_090]
  norm_num [mu_091]

private theorem cell_091 :
    endpointOK (squarefreeCountNat 91) 91 ∧
      endpointOK (squarefreeCountNat 91) (91 + 1) := by
  rw [count_091]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_092 : μ 92 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_092 : squarefreeCountNat 92 = 57 := by
  rw [show 92 = 91 + 1 by norm_num, squarefreeCountNat_succ, count_091]
  norm_num [mu_092]

private theorem cell_092 :
    endpointOK (squarefreeCountNat 92) 92 ∧
      endpointOK (squarefreeCountNat 92) (92 + 1) := by
  rw [count_092]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_093 : μ 93 = 1 := by
  rw [show 93 = 3 * 31 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 31)]
  norm_num

private theorem count_093 : squarefreeCountNat 93 = 58 := by
  rw [show 93 = 92 + 1 by norm_num, squarefreeCountNat_succ, count_092]
  norm_num [mu_093]

private theorem cell_093 :
    endpointOK (squarefreeCountNat 93) 93 ∧
      endpointOK (squarefreeCountNat 93) (93 + 1) := by
  rw [count_093]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_094 : μ 94 = 1 := by
  rw [show 94 = 2 * 47 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 47)]
  norm_num

private theorem count_094 : squarefreeCountNat 94 = 59 := by
  rw [show 94 = 93 + 1 by norm_num, squarefreeCountNat_succ, count_093]
  norm_num [mu_094]

private theorem cell_094 :
    endpointOK (squarefreeCountNat 94) 94 ∧
      endpointOK (squarefreeCountNat 94) (94 + 1) := by
  rw [count_094]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_095 : μ 95 = 1 := by
  rw [show 95 = 5 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_095 : squarefreeCountNat 95 = 60 := by
  rw [show 95 = 94 + 1 by norm_num, squarefreeCountNat_succ, count_094]
  norm_num [mu_095]

private theorem cell_095 :
    endpointOK (squarefreeCountNat 95) 95 ∧
      endpointOK (squarefreeCountNat 95) (95 + 1) := by
  rw [count_095]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_096 : μ 96 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_096 : squarefreeCountNat 96 = 60 := by
  rw [show 96 = 95 + 1 by norm_num, squarefreeCountNat_succ, count_095]
  norm_num [mu_096]

private theorem cell_096 :
    endpointOK (squarefreeCountNat 96) 96 ∧
      endpointOK (squarefreeCountNat 96) (96 + 1) := by
  rw [count_096]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_097 : μ 97 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_097 : squarefreeCountNat 97 = 61 := by
  rw [show 97 = 96 + 1 by norm_num, squarefreeCountNat_succ, count_096]
  norm_num [mu_097]

private theorem cell_097 :
    endpointOK (squarefreeCountNat 97) 97 ∧
      endpointOK (squarefreeCountNat 97) (97 + 1) := by
  rw [count_097]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_098 : μ 98 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 7 (by norm_num) (by norm_num)

private theorem count_098 : squarefreeCountNat 98 = 61 := by
  rw [show 98 = 97 + 1 by norm_num, squarefreeCountNat_succ, count_097]
  norm_num [mu_098]

private theorem cell_098 :
    endpointOK (squarefreeCountNat 98) 98 ∧
      endpointOK (squarefreeCountNat 98) (98 + 1) := by
  rw [count_098]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_099 : μ 99 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_099 : squarefreeCountNat 99 = 61 := by
  rw [show 99 = 98 + 1 by norm_num, squarefreeCountNat_succ, count_098]
  norm_num [mu_099]

private theorem cell_099 :
    endpointOK (squarefreeCountNat 99) 99 ∧
      endpointOK (squarefreeCountNat 99) (99 + 1) := by
  rw [count_099]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_100 : μ 100 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

theorem count_100 : squarefreeCountNat 100 = 61 := by
  rw [show 100 = 99 + 1 by norm_num, squarefreeCountNat_succ, count_099]
  norm_num [mu_100]

private theorem cell_100 :
    endpointOK (squarefreeCountNat 100) 100 ∧
      endpointOK (squarefreeCountNat 100) (100 + 1) := by
  rw [count_100]
  norm_num [endpointOK, densityLower, densityUpper]

theorem finite_endpoint_certificate_051_100 (N : ℕ)
    (hlo : 51 ≤ N) (hhi : N ≤ 100) :
    endpointOK (squarefreeCountNat N) N ∧
      endpointOK (squarefreeCountNat N) (N + 1) := by
  interval_cases N
  · exact cell_051
  · exact cell_052
  · exact cell_053
  · exact cell_054
  · exact cell_055
  · exact cell_056
  · exact cell_057
  · exact cell_058
  · exact cell_059
  · exact cell_060
  · exact cell_061
  · exact cell_062
  · exact cell_063
  · exact cell_064
  · exact cell_065
  · exact cell_066
  · exact cell_067
  · exact cell_068
  · exact cell_069
  · exact cell_070
  · exact cell_071
  · exact cell_072
  · exact cell_073
  · exact cell_074
  · exact cell_075
  · exact cell_076
  · exact cell_077
  · exact cell_078
  · exact cell_079
  · exact cell_080
  · exact cell_081
  · exact cell_082
  · exact cell_083
  · exact cell_084
  · exact cell_085
  · exact cell_086
  · exact cell_087
  · exact cell_088
  · exact cell_089
  · exact cell_090
  · exact cell_091
  · exact cell_092
  · exact cell_093
  · exact cell_094
  · exact cell_095
  · exact cell_096
  · exact cell_097
  · exact cell_098
  · exact cell_099
  · exact cell_100

end MoserMacLeod
