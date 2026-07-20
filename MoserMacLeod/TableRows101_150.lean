import MoserMacLeod.TableRows051_100

/-!
# Proof-producing finite rows 101--150

This generated shard proves the required Möbius values, updates the squarefree
prefix count one integer at a time, and checks the two exact rational endpoint
inequalities in each real cell.  It uses no native evaluator.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction.Moebius BigOperators
open Finset

private theorem mu_101 : μ 101 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_101 : squarefreeCountNat 101 = 62 := by
  rw [show 101 = 100 + 1 by norm_num, squarefreeCountNat_succ, count_100]
  norm_num [mu_101]

private theorem cell_101 :
    endpointOK (squarefreeCountNat 101) 101 ∧
      endpointOK (squarefreeCountNat 101) (101 + 1) := by
  rw [count_101]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_102 : μ 102 = -1 := by
  rw [show 102 = 2 * 51 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 51 = 3 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_102 : squarefreeCountNat 102 = 63 := by
  rw [show 102 = 101 + 1 by norm_num, squarefreeCountNat_succ, count_101]
  norm_num [mu_102]

private theorem cell_102 :
    endpointOK (squarefreeCountNat 102) 102 ∧
      endpointOK (squarefreeCountNat 102) (102 + 1) := by
  rw [count_102]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_103 : μ 103 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_103 : squarefreeCountNat 103 = 64 := by
  rw [show 103 = 102 + 1 by norm_num, squarefreeCountNat_succ, count_102]
  norm_num [mu_103]

private theorem cell_103 :
    endpointOK (squarefreeCountNat 103) 103 ∧
      endpointOK (squarefreeCountNat 103) (103 + 1) := by
  rw [count_103]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_104 : μ 104 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_104 : squarefreeCountNat 104 = 64 := by
  rw [show 104 = 103 + 1 by norm_num, squarefreeCountNat_succ, count_103]
  norm_num [mu_104]

private theorem cell_104 :
    endpointOK (squarefreeCountNat 104) 104 ∧
      endpointOK (squarefreeCountNat 104) (104 + 1) := by
  rw [count_104]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_105 : μ 105 = -1 := by
  rw [show 105 = 3 * 35 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 35 = 5 * 7 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

private theorem count_105 : squarefreeCountNat 105 = 65 := by
  rw [show 105 = 104 + 1 by norm_num, squarefreeCountNat_succ, count_104]
  norm_num [mu_105]

private theorem cell_105 :
    endpointOK (squarefreeCountNat 105) 105 ∧
      endpointOK (squarefreeCountNat 105) (105 + 1) := by
  rw [count_105]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_106 : μ 106 = 1 := by
  rw [show 106 = 2 * 53 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 53)]
  norm_num

private theorem count_106 : squarefreeCountNat 106 = 66 := by
  rw [show 106 = 105 + 1 by norm_num, squarefreeCountNat_succ, count_105]
  norm_num [mu_106]

private theorem cell_106 :
    endpointOK (squarefreeCountNat 106) 106 ∧
      endpointOK (squarefreeCountNat 106) (106 + 1) := by
  rw [count_106]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_107 : μ 107 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_107 : squarefreeCountNat 107 = 67 := by
  rw [show 107 = 106 + 1 by norm_num, squarefreeCountNat_succ, count_106]
  norm_num [mu_107]

private theorem cell_107 :
    endpointOK (squarefreeCountNat 107) 107 ∧
      endpointOK (squarefreeCountNat 107) (107 + 1) := by
  rw [count_107]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_108 : μ 108 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_108 : squarefreeCountNat 108 = 67 := by
  rw [show 108 = 107 + 1 by norm_num, squarefreeCountNat_succ, count_107]
  norm_num [mu_108]

private theorem cell_108 :
    endpointOK (squarefreeCountNat 108) 108 ∧
      endpointOK (squarefreeCountNat 108) (108 + 1) := by
  rw [count_108]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_109 : μ 109 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_109 : squarefreeCountNat 109 = 68 := by
  rw [show 109 = 108 + 1 by norm_num, squarefreeCountNat_succ, count_108]
  norm_num [mu_109]

private theorem cell_109 :
    endpointOK (squarefreeCountNat 109) 109 ∧
      endpointOK (squarefreeCountNat 109) (109 + 1) := by
  rw [count_109]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_110 : μ 110 = -1 := by
  rw [show 110 = 2 * 55 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 55 = 5 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_110 : squarefreeCountNat 110 = 69 := by
  rw [show 110 = 109 + 1 by norm_num, squarefreeCountNat_succ, count_109]
  norm_num [mu_110]

private theorem cell_110 :
    endpointOK (squarefreeCountNat 110) 110 ∧
      endpointOK (squarefreeCountNat 110) (110 + 1) := by
  rw [count_110]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_111 : μ 111 = 1 := by
  rw [show 111 = 3 * 37 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 37)]
  norm_num

private theorem count_111 : squarefreeCountNat 111 = 70 := by
  rw [show 111 = 110 + 1 by norm_num, squarefreeCountNat_succ, count_110]
  norm_num [mu_111]

private theorem cell_111 :
    endpointOK (squarefreeCountNat 111) 111 ∧
      endpointOK (squarefreeCountNat 111) (111 + 1) := by
  rw [count_111]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_112 : μ 112 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_112 : squarefreeCountNat 112 = 70 := by
  rw [show 112 = 111 + 1 by norm_num, squarefreeCountNat_succ, count_111]
  norm_num [mu_112]

private theorem cell_112 :
    endpointOK (squarefreeCountNat 112) 112 ∧
      endpointOK (squarefreeCountNat 112) (112 + 1) := by
  rw [count_112]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_113 : μ 113 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_113 : squarefreeCountNat 113 = 71 := by
  rw [show 113 = 112 + 1 by norm_num, squarefreeCountNat_succ, count_112]
  norm_num [mu_113]

private theorem cell_113 :
    endpointOK (squarefreeCountNat 113) 113 ∧
      endpointOK (squarefreeCountNat 113) (113 + 1) := by
  rw [count_113]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_114 : μ 114 = -1 := by
  rw [show 114 = 2 * 57 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 57 = 3 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_114 : squarefreeCountNat 114 = 72 := by
  rw [show 114 = 113 + 1 by norm_num, squarefreeCountNat_succ, count_113]
  norm_num [mu_114]

private theorem cell_114 :
    endpointOK (squarefreeCountNat 114) 114 ∧
      endpointOK (squarefreeCountNat 114) (114 + 1) := by
  rw [count_114]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_115 : μ 115 = 1 := by
  rw [show 115 = 5 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_115 : squarefreeCountNat 115 = 73 := by
  rw [show 115 = 114 + 1 by norm_num, squarefreeCountNat_succ, count_114]
  norm_num [mu_115]

private theorem cell_115 :
    endpointOK (squarefreeCountNat 115) 115 ∧
      endpointOK (squarefreeCountNat 115) (115 + 1) := by
  rw [count_115]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_116 : μ 116 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_116 : squarefreeCountNat 116 = 73 := by
  rw [show 116 = 115 + 1 by norm_num, squarefreeCountNat_succ, count_115]
  norm_num [mu_116]

private theorem cell_116 :
    endpointOK (squarefreeCountNat 116) 116 ∧
      endpointOK (squarefreeCountNat 116) (116 + 1) := by
  rw [count_116]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_117 : μ 117 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_117 : squarefreeCountNat 117 = 73 := by
  rw [show 117 = 116 + 1 by norm_num, squarefreeCountNat_succ, count_116]
  norm_num [mu_117]

private theorem cell_117 :
    endpointOK (squarefreeCountNat 117) 117 ∧
      endpointOK (squarefreeCountNat 117) (117 + 1) := by
  rw [count_117]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_118 : μ 118 = 1 := by
  rw [show 118 = 2 * 59 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 59)]
  norm_num

private theorem count_118 : squarefreeCountNat 118 = 74 := by
  rw [show 118 = 117 + 1 by norm_num, squarefreeCountNat_succ, count_117]
  norm_num [mu_118]

private theorem cell_118 :
    endpointOK (squarefreeCountNat 118) 118 ∧
      endpointOK (squarefreeCountNat 118) (118 + 1) := by
  rw [count_118]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_119 : μ 119 = 1 := by
  rw [show 119 = 7 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_119 : squarefreeCountNat 119 = 75 := by
  rw [show 119 = 118 + 1 by norm_num, squarefreeCountNat_succ, count_118]
  norm_num [mu_119]

private theorem cell_119 :
    endpointOK (squarefreeCountNat 119) 119 ∧
      endpointOK (squarefreeCountNat 119) (119 + 1) := by
  rw [count_119]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_120 : μ 120 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_120 : squarefreeCountNat 120 = 75 := by
  rw [show 120 = 119 + 1 by norm_num, squarefreeCountNat_succ, count_119]
  norm_num [mu_120]

private theorem cell_120 :
    endpointOK (squarefreeCountNat 120) 120 ∧
      endpointOK (squarefreeCountNat 120) (120 + 1) := by
  rw [count_120]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_121 : μ 121 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 11 (by norm_num) (by norm_num)

private theorem count_121 : squarefreeCountNat 121 = 75 := by
  rw [show 121 = 120 + 1 by norm_num, squarefreeCountNat_succ, count_120]
  norm_num [mu_121]

private theorem cell_121 :
    endpointOK (squarefreeCountNat 121) 121 ∧
      endpointOK (squarefreeCountNat 121) (121 + 1) := by
  rw [count_121]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_122 : μ 122 = 1 := by
  rw [show 122 = 2 * 61 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 61)]
  norm_num

private theorem count_122 : squarefreeCountNat 122 = 76 := by
  rw [show 122 = 121 + 1 by norm_num, squarefreeCountNat_succ, count_121]
  norm_num [mu_122]

private theorem cell_122 :
    endpointOK (squarefreeCountNat 122) 122 ∧
      endpointOK (squarefreeCountNat 122) (122 + 1) := by
  rw [count_122]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_123 : μ 123 = 1 := by
  rw [show 123 = 3 * 41 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 41)]
  norm_num

private theorem count_123 : squarefreeCountNat 123 = 77 := by
  rw [show 123 = 122 + 1 by norm_num, squarefreeCountNat_succ, count_122]
  norm_num [mu_123]

private theorem cell_123 :
    endpointOK (squarefreeCountNat 123) 123 ∧
      endpointOK (squarefreeCountNat 123) (123 + 1) := by
  rw [count_123]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_124 : μ 124 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_124 : squarefreeCountNat 124 = 77 := by
  rw [show 124 = 123 + 1 by norm_num, squarefreeCountNat_succ, count_123]
  norm_num [mu_124]

private theorem cell_124 :
    endpointOK (squarefreeCountNat 124) 124 ∧
      endpointOK (squarefreeCountNat 124) (124 + 1) := by
  rw [count_124]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_125 : μ 125 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

private theorem count_125 : squarefreeCountNat 125 = 77 := by
  rw [show 125 = 124 + 1 by norm_num, squarefreeCountNat_succ, count_124]
  norm_num [mu_125]

private theorem cell_125 :
    endpointOK (squarefreeCountNat 125) 125 ∧
      endpointOK (squarefreeCountNat 125) (125 + 1) := by
  rw [count_125]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_126 : μ 126 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_126 : squarefreeCountNat 126 = 77 := by
  rw [show 126 = 125 + 1 by norm_num, squarefreeCountNat_succ, count_125]
  norm_num [mu_126]

private theorem cell_126 :
    endpointOK (squarefreeCountNat 126) 126 ∧
      endpointOK (squarefreeCountNat 126) (126 + 1) := by
  rw [count_126]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_127 : μ 127 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_127 : squarefreeCountNat 127 = 78 := by
  rw [show 127 = 126 + 1 by norm_num, squarefreeCountNat_succ, count_126]
  norm_num [mu_127]

private theorem cell_127 :
    endpointOK (squarefreeCountNat 127) 127 ∧
      endpointOK (squarefreeCountNat 127) (127 + 1) := by
  rw [count_127]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_128 : μ 128 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_128 : squarefreeCountNat 128 = 78 := by
  rw [show 128 = 127 + 1 by norm_num, squarefreeCountNat_succ, count_127]
  norm_num [mu_128]

private theorem cell_128 :
    endpointOK (squarefreeCountNat 128) 128 ∧
      endpointOK (squarefreeCountNat 128) (128 + 1) := by
  rw [count_128]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_129 : μ 129 = 1 := by
  rw [show 129 = 3 * 43 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 43)]
  norm_num

private theorem count_129 : squarefreeCountNat 129 = 79 := by
  rw [show 129 = 128 + 1 by norm_num, squarefreeCountNat_succ, count_128]
  norm_num [mu_129]

private theorem cell_129 :
    endpointOK (squarefreeCountNat 129) 129 ∧
      endpointOK (squarefreeCountNat 129) (129 + 1) := by
  rw [count_129]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_130 : μ 130 = -1 := by
  rw [show 130 = 2 * 65 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 65 = 5 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_130 : squarefreeCountNat 130 = 80 := by
  rw [show 130 = 129 + 1 by norm_num, squarefreeCountNat_succ, count_129]
  norm_num [mu_130]

private theorem cell_130 :
    endpointOK (squarefreeCountNat 130) 130 ∧
      endpointOK (squarefreeCountNat 130) (130 + 1) := by
  rw [count_130]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_131 : μ 131 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_131 : squarefreeCountNat 131 = 81 := by
  rw [show 131 = 130 + 1 by norm_num, squarefreeCountNat_succ, count_130]
  norm_num [mu_131]

private theorem cell_131 :
    endpointOK (squarefreeCountNat 131) 131 ∧
      endpointOK (squarefreeCountNat 131) (131 + 1) := by
  rw [count_131]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_132 : μ 132 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_132 : squarefreeCountNat 132 = 81 := by
  rw [show 132 = 131 + 1 by norm_num, squarefreeCountNat_succ, count_131]
  norm_num [mu_132]

private theorem cell_132 :
    endpointOK (squarefreeCountNat 132) 132 ∧
      endpointOK (squarefreeCountNat 132) (132 + 1) := by
  rw [count_132]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_133 : μ 133 = 1 := by
  rw [show 133 = 7 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_133 : squarefreeCountNat 133 = 82 := by
  rw [show 133 = 132 + 1 by norm_num, squarefreeCountNat_succ, count_132]
  norm_num [mu_133]

private theorem cell_133 :
    endpointOK (squarefreeCountNat 133) 133 ∧
      endpointOK (squarefreeCountNat 133) (133 + 1) := by
  rw [count_133]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_134 : μ 134 = 1 := by
  rw [show 134 = 2 * 67 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 67)]
  norm_num

private theorem count_134 : squarefreeCountNat 134 = 83 := by
  rw [show 134 = 133 + 1 by norm_num, squarefreeCountNat_succ, count_133]
  norm_num [mu_134]

private theorem cell_134 :
    endpointOK (squarefreeCountNat 134) 134 ∧
      endpointOK (squarefreeCountNat 134) (134 + 1) := by
  rw [count_134]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_135 : μ 135 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_135 : squarefreeCountNat 135 = 83 := by
  rw [show 135 = 134 + 1 by norm_num, squarefreeCountNat_succ, count_134]
  norm_num [mu_135]

private theorem cell_135 :
    endpointOK (squarefreeCountNat 135) 135 ∧
      endpointOK (squarefreeCountNat 135) (135 + 1) := by
  rw [count_135]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_136 : μ 136 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_136 : squarefreeCountNat 136 = 83 := by
  rw [show 136 = 135 + 1 by norm_num, squarefreeCountNat_succ, count_135]
  norm_num [mu_136]

private theorem cell_136 :
    endpointOK (squarefreeCountNat 136) 136 ∧
      endpointOK (squarefreeCountNat 136) (136 + 1) := by
  rw [count_136]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_137 : μ 137 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_137 : squarefreeCountNat 137 = 84 := by
  rw [show 137 = 136 + 1 by norm_num, squarefreeCountNat_succ, count_136]
  norm_num [mu_137]

private theorem cell_137 :
    endpointOK (squarefreeCountNat 137) 137 ∧
      endpointOK (squarefreeCountNat 137) (137 + 1) := by
  rw [count_137]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_138 : μ 138 = -1 := by
  rw [show 138 = 2 * 69 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 69 = 3 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_138 : squarefreeCountNat 138 = 85 := by
  rw [show 138 = 137 + 1 by norm_num, squarefreeCountNat_succ, count_137]
  norm_num [mu_138]

private theorem cell_138 :
    endpointOK (squarefreeCountNat 138) 138 ∧
      endpointOK (squarefreeCountNat 138) (138 + 1) := by
  rw [count_138]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_139 : μ 139 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_139 : squarefreeCountNat 139 = 86 := by
  rw [show 139 = 138 + 1 by norm_num, squarefreeCountNat_succ, count_138]
  norm_num [mu_139]

private theorem cell_139 :
    endpointOK (squarefreeCountNat 139) 139 ∧
      endpointOK (squarefreeCountNat 139) (139 + 1) := by
  rw [count_139]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_140 : μ 140 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_140 : squarefreeCountNat 140 = 86 := by
  rw [show 140 = 139 + 1 by norm_num, squarefreeCountNat_succ, count_139]
  norm_num [mu_140]

private theorem cell_140 :
    endpointOK (squarefreeCountNat 140) 140 ∧
      endpointOK (squarefreeCountNat 140) (140 + 1) := by
  rw [count_140]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_141 : μ 141 = 1 := by
  rw [show 141 = 3 * 47 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 47)]
  norm_num

private theorem count_141 : squarefreeCountNat 141 = 87 := by
  rw [show 141 = 140 + 1 by norm_num, squarefreeCountNat_succ, count_140]
  norm_num [mu_141]

private theorem cell_141 :
    endpointOK (squarefreeCountNat 141) 141 ∧
      endpointOK (squarefreeCountNat 141) (141 + 1) := by
  rw [count_141]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_142 : μ 142 = 1 := by
  rw [show 142 = 2 * 71 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 71)]
  norm_num

private theorem count_142 : squarefreeCountNat 142 = 88 := by
  rw [show 142 = 141 + 1 by norm_num, squarefreeCountNat_succ, count_141]
  norm_num [mu_142]

private theorem cell_142 :
    endpointOK (squarefreeCountNat 142) 142 ∧
      endpointOK (squarefreeCountNat 142) (142 + 1) := by
  rw [count_142]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_143 : μ 143 = 1 := by
  rw [show 143 = 11 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_143 : squarefreeCountNat 143 = 89 := by
  rw [show 143 = 142 + 1 by norm_num, squarefreeCountNat_succ, count_142]
  norm_num [mu_143]

private theorem cell_143 :
    endpointOK (squarefreeCountNat 143) 143 ∧
      endpointOK (squarefreeCountNat 143) (143 + 1) := by
  rw [count_143]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_144 : μ 144 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_144 : squarefreeCountNat 144 = 89 := by
  rw [show 144 = 143 + 1 by norm_num, squarefreeCountNat_succ, count_143]
  norm_num [mu_144]

private theorem cell_144 :
    endpointOK (squarefreeCountNat 144) 144 ∧
      endpointOK (squarefreeCountNat 144) (144 + 1) := by
  rw [count_144]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_145 : μ 145 = 1 := by
  rw [show 145 = 5 * 29 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 29)]
  norm_num

private theorem count_145 : squarefreeCountNat 145 = 90 := by
  rw [show 145 = 144 + 1 by norm_num, squarefreeCountNat_succ, count_144]
  norm_num [mu_145]

private theorem cell_145 :
    endpointOK (squarefreeCountNat 145) 145 ∧
      endpointOK (squarefreeCountNat 145) (145 + 1) := by
  rw [count_145]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_146 : μ 146 = 1 := by
  rw [show 146 = 2 * 73 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 73)]
  norm_num

private theorem count_146 : squarefreeCountNat 146 = 91 := by
  rw [show 146 = 145 + 1 by norm_num, squarefreeCountNat_succ, count_145]
  norm_num [mu_146]

private theorem cell_146 :
    endpointOK (squarefreeCountNat 146) 146 ∧
      endpointOK (squarefreeCountNat 146) (146 + 1) := by
  rw [count_146]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_147 : μ 147 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 7 (by norm_num) (by norm_num)

private theorem count_147 : squarefreeCountNat 147 = 91 := by
  rw [show 147 = 146 + 1 by norm_num, squarefreeCountNat_succ, count_146]
  norm_num [mu_147]

private theorem cell_147 :
    endpointOK (squarefreeCountNat 147) 147 ∧
      endpointOK (squarefreeCountNat 147) (147 + 1) := by
  rw [count_147]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_148 : μ 148 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_148 : squarefreeCountNat 148 = 91 := by
  rw [show 148 = 147 + 1 by norm_num, squarefreeCountNat_succ, count_147]
  norm_num [mu_148]

private theorem cell_148 :
    endpointOK (squarefreeCountNat 148) 148 ∧
      endpointOK (squarefreeCountNat 148) (148 + 1) := by
  rw [count_148]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_149 : μ 149 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_149 : squarefreeCountNat 149 = 92 := by
  rw [show 149 = 148 + 1 by norm_num, squarefreeCountNat_succ, count_148]
  norm_num [mu_149]

private theorem cell_149 :
    endpointOK (squarefreeCountNat 149) 149 ∧
      endpointOK (squarefreeCountNat 149) (149 + 1) := by
  rw [count_149]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_150 : μ 150 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

theorem count_150 : squarefreeCountNat 150 = 92 := by
  rw [show 150 = 149 + 1 by norm_num, squarefreeCountNat_succ, count_149]
  norm_num [mu_150]

private theorem cell_150 :
    endpointOK (squarefreeCountNat 150) 150 ∧
      endpointOK (squarefreeCountNat 150) (150 + 1) := by
  rw [count_150]
  norm_num [endpointOK, densityLower, densityUpper]

theorem finite_endpoint_certificate_101_150 (N : ℕ)
    (hlo : 101 ≤ N) (hhi : N ≤ 150) :
    endpointOK (squarefreeCountNat N) N ∧
      endpointOK (squarefreeCountNat N) (N + 1) := by
  interval_cases N
  · exact cell_101
  · exact cell_102
  · exact cell_103
  · exact cell_104
  · exact cell_105
  · exact cell_106
  · exact cell_107
  · exact cell_108
  · exact cell_109
  · exact cell_110
  · exact cell_111
  · exact cell_112
  · exact cell_113
  · exact cell_114
  · exact cell_115
  · exact cell_116
  · exact cell_117
  · exact cell_118
  · exact cell_119
  · exact cell_120
  · exact cell_121
  · exact cell_122
  · exact cell_123
  · exact cell_124
  · exact cell_125
  · exact cell_126
  · exact cell_127
  · exact cell_128
  · exact cell_129
  · exact cell_130
  · exact cell_131
  · exact cell_132
  · exact cell_133
  · exact cell_134
  · exact cell_135
  · exact cell_136
  · exact cell_137
  · exact cell_138
  · exact cell_139
  · exact cell_140
  · exact cell_141
  · exact cell_142
  · exact cell_143
  · exact cell_144
  · exact cell_145
  · exact cell_146
  · exact cell_147
  · exact cell_148
  · exact cell_149
  · exact cell_150

end MoserMacLeod
