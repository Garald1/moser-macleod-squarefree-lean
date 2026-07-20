import MoserMacLeod.TableRows101_150

/-!
# Proof-producing finite rows 151--200

This generated shard proves the required Möbius values, updates the squarefree
prefix count one integer at a time, and checks the two exact rational endpoint
inequalities in each real cell.  It uses no native evaluator.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction.Moebius BigOperators
open Finset

private theorem mu_151 : μ 151 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_151 : squarefreeCountNat 151 = 93 := by
  rw [show 151 = 150 + 1 by norm_num, squarefreeCountNat_succ, count_150]
  norm_num [mu_151]

private theorem cell_151 :
    endpointOK (squarefreeCountNat 151) 151 ∧
      endpointOK (squarefreeCountNat 151) (151 + 1) := by
  rw [count_151]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_152 : μ 152 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_152 : squarefreeCountNat 152 = 93 := by
  rw [show 152 = 151 + 1 by norm_num, squarefreeCountNat_succ, count_151]
  norm_num [mu_152]

private theorem cell_152 :
    endpointOK (squarefreeCountNat 152) 152 ∧
      endpointOK (squarefreeCountNat 152) (152 + 1) := by
  rw [count_152]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_153 : μ 153 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_153 : squarefreeCountNat 153 = 93 := by
  rw [show 153 = 152 + 1 by norm_num, squarefreeCountNat_succ, count_152]
  norm_num [mu_153]

private theorem cell_153 :
    endpointOK (squarefreeCountNat 153) 153 ∧
      endpointOK (squarefreeCountNat 153) (153 + 1) := by
  rw [count_153]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_154 : μ 154 = -1 := by
  rw [show 154 = 2 * 77 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 77 = 7 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_154 : squarefreeCountNat 154 = 94 := by
  rw [show 154 = 153 + 1 by norm_num, squarefreeCountNat_succ, count_153]
  norm_num [mu_154]

private theorem cell_154 :
    endpointOK (squarefreeCountNat 154) 154 ∧
      endpointOK (squarefreeCountNat 154) (154 + 1) := by
  rw [count_154]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_155 : μ 155 = 1 := by
  rw [show 155 = 5 * 31 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 31)]
  norm_num

private theorem count_155 : squarefreeCountNat 155 = 95 := by
  rw [show 155 = 154 + 1 by norm_num, squarefreeCountNat_succ, count_154]
  norm_num [mu_155]

private theorem cell_155 :
    endpointOK (squarefreeCountNat 155) 155 ∧
      endpointOK (squarefreeCountNat 155) (155 + 1) := by
  rw [count_155]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_156 : μ 156 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_156 : squarefreeCountNat 156 = 95 := by
  rw [show 156 = 155 + 1 by norm_num, squarefreeCountNat_succ, count_155]
  norm_num [mu_156]

private theorem cell_156 :
    endpointOK (squarefreeCountNat 156) 156 ∧
      endpointOK (squarefreeCountNat 156) (156 + 1) := by
  rw [count_156]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_157 : μ 157 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_157 : squarefreeCountNat 157 = 96 := by
  rw [show 157 = 156 + 1 by norm_num, squarefreeCountNat_succ, count_156]
  norm_num [mu_157]

private theorem cell_157 :
    endpointOK (squarefreeCountNat 157) 157 ∧
      endpointOK (squarefreeCountNat 157) (157 + 1) := by
  rw [count_157]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_158 : μ 158 = 1 := by
  rw [show 158 = 2 * 79 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 79)]
  norm_num

private theorem count_158 : squarefreeCountNat 158 = 97 := by
  rw [show 158 = 157 + 1 by norm_num, squarefreeCountNat_succ, count_157]
  norm_num [mu_158]

private theorem cell_158 :
    endpointOK (squarefreeCountNat 158) 158 ∧
      endpointOK (squarefreeCountNat 158) (158 + 1) := by
  rw [count_158]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_159 : μ 159 = 1 := by
  rw [show 159 = 3 * 53 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 53)]
  norm_num

private theorem count_159 : squarefreeCountNat 159 = 98 := by
  rw [show 159 = 158 + 1 by norm_num, squarefreeCountNat_succ, count_158]
  norm_num [mu_159]

private theorem cell_159 :
    endpointOK (squarefreeCountNat 159) 159 ∧
      endpointOK (squarefreeCountNat 159) (159 + 1) := by
  rw [count_159]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_160 : μ 160 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_160 : squarefreeCountNat 160 = 98 := by
  rw [show 160 = 159 + 1 by norm_num, squarefreeCountNat_succ, count_159]
  norm_num [mu_160]

private theorem cell_160 :
    endpointOK (squarefreeCountNat 160) 160 ∧
      endpointOK (squarefreeCountNat 160) (160 + 1) := by
  rw [count_160]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_161 : μ 161 = 1 := by
  rw [show 161 = 7 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_161 : squarefreeCountNat 161 = 99 := by
  rw [show 161 = 160 + 1 by norm_num, squarefreeCountNat_succ, count_160]
  norm_num [mu_161]

private theorem cell_161 :
    endpointOK (squarefreeCountNat 161) 161 ∧
      endpointOK (squarefreeCountNat 161) (161 + 1) := by
  rw [count_161]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_162 : μ 162 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_162 : squarefreeCountNat 162 = 99 := by
  rw [show 162 = 161 + 1 by norm_num, squarefreeCountNat_succ, count_161]
  norm_num [mu_162]

private theorem cell_162 :
    endpointOK (squarefreeCountNat 162) 162 ∧
      endpointOK (squarefreeCountNat 162) (162 + 1) := by
  rw [count_162]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_163 : μ 163 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_163 : squarefreeCountNat 163 = 100 := by
  rw [show 163 = 162 + 1 by norm_num, squarefreeCountNat_succ, count_162]
  norm_num [mu_163]

private theorem cell_163 :
    endpointOK (squarefreeCountNat 163) 163 ∧
      endpointOK (squarefreeCountNat 163) (163 + 1) := by
  rw [count_163]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_164 : μ 164 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_164 : squarefreeCountNat 164 = 100 := by
  rw [show 164 = 163 + 1 by norm_num, squarefreeCountNat_succ, count_163]
  norm_num [mu_164]

private theorem cell_164 :
    endpointOK (squarefreeCountNat 164) 164 ∧
      endpointOK (squarefreeCountNat 164) (164 + 1) := by
  rw [count_164]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_165 : μ 165 = -1 := by
  rw [show 165 = 3 * 55 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 55 = 5 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_165 : squarefreeCountNat 165 = 101 := by
  rw [show 165 = 164 + 1 by norm_num, squarefreeCountNat_succ, count_164]
  norm_num [mu_165]

private theorem cell_165 :
    endpointOK (squarefreeCountNat 165) 165 ∧
      endpointOK (squarefreeCountNat 165) (165 + 1) := by
  rw [count_165]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_166 : μ 166 = 1 := by
  rw [show 166 = 2 * 83 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 83)]
  norm_num

private theorem count_166 : squarefreeCountNat 166 = 102 := by
  rw [show 166 = 165 + 1 by norm_num, squarefreeCountNat_succ, count_165]
  norm_num [mu_166]

private theorem cell_166 :
    endpointOK (squarefreeCountNat 166) 166 ∧
      endpointOK (squarefreeCountNat 166) (166 + 1) := by
  rw [count_166]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_167 : μ 167 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_167 : squarefreeCountNat 167 = 103 := by
  rw [show 167 = 166 + 1 by norm_num, squarefreeCountNat_succ, count_166]
  norm_num [mu_167]

private theorem cell_167 :
    endpointOK (squarefreeCountNat 167) 167 ∧
      endpointOK (squarefreeCountNat 167) (167 + 1) := by
  rw [count_167]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_168 : μ 168 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_168 : squarefreeCountNat 168 = 103 := by
  rw [show 168 = 167 + 1 by norm_num, squarefreeCountNat_succ, count_167]
  norm_num [mu_168]

private theorem cell_168 :
    endpointOK (squarefreeCountNat 168) 168 ∧
      endpointOK (squarefreeCountNat 168) (168 + 1) := by
  rw [count_168]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_169 : μ 169 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 13 (by norm_num) (by norm_num)

private theorem count_169 : squarefreeCountNat 169 = 103 := by
  rw [show 169 = 168 + 1 by norm_num, squarefreeCountNat_succ, count_168]
  norm_num [mu_169]

private theorem cell_169 :
    endpointOK (squarefreeCountNat 169) 169 ∧
      endpointOK (squarefreeCountNat 169) (169 + 1) := by
  rw [count_169]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_170 : μ 170 = -1 := by
  rw [show 170 = 2 * 85 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 85 = 5 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_170 : squarefreeCountNat 170 = 104 := by
  rw [show 170 = 169 + 1 by norm_num, squarefreeCountNat_succ, count_169]
  norm_num [mu_170]

private theorem cell_170 :
    endpointOK (squarefreeCountNat 170) 170 ∧
      endpointOK (squarefreeCountNat 170) (170 + 1) := by
  rw [count_170]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_171 : μ 171 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_171 : squarefreeCountNat 171 = 104 := by
  rw [show 171 = 170 + 1 by norm_num, squarefreeCountNat_succ, count_170]
  norm_num [mu_171]

private theorem cell_171 :
    endpointOK (squarefreeCountNat 171) 171 ∧
      endpointOK (squarefreeCountNat 171) (171 + 1) := by
  rw [count_171]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_172 : μ 172 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_172 : squarefreeCountNat 172 = 104 := by
  rw [show 172 = 171 + 1 by norm_num, squarefreeCountNat_succ, count_171]
  norm_num [mu_172]

private theorem cell_172 :
    endpointOK (squarefreeCountNat 172) 172 ∧
      endpointOK (squarefreeCountNat 172) (172 + 1) := by
  rw [count_172]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_173 : μ 173 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_173 : squarefreeCountNat 173 = 105 := by
  rw [show 173 = 172 + 1 by norm_num, squarefreeCountNat_succ, count_172]
  norm_num [mu_173]

private theorem cell_173 :
    endpointOK (squarefreeCountNat 173) 173 ∧
      endpointOK (squarefreeCountNat 173) (173 + 1) := by
  rw [count_173]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_174 : μ 174 = -1 := by
  rw [show 174 = 2 * 87 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 87 = 3 * 29 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 29)]
  norm_num

private theorem count_174 : squarefreeCountNat 174 = 106 := by
  rw [show 174 = 173 + 1 by norm_num, squarefreeCountNat_succ, count_173]
  norm_num [mu_174]

private theorem cell_174 :
    endpointOK (squarefreeCountNat 174) 174 ∧
      endpointOK (squarefreeCountNat 174) (174 + 1) := by
  rw [count_174]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_175 : μ 175 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

private theorem count_175 : squarefreeCountNat 175 = 106 := by
  rw [show 175 = 174 + 1 by norm_num, squarefreeCountNat_succ, count_174]
  norm_num [mu_175]

private theorem cell_175 :
    endpointOK (squarefreeCountNat 175) 175 ∧
      endpointOK (squarefreeCountNat 175) (175 + 1) := by
  rw [count_175]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_176 : μ 176 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_176 : squarefreeCountNat 176 = 106 := by
  rw [show 176 = 175 + 1 by norm_num, squarefreeCountNat_succ, count_175]
  norm_num [mu_176]

private theorem cell_176 :
    endpointOK (squarefreeCountNat 176) 176 ∧
      endpointOK (squarefreeCountNat 176) (176 + 1) := by
  rw [count_176]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_177 : μ 177 = 1 := by
  rw [show 177 = 3 * 59 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 59)]
  norm_num

private theorem count_177 : squarefreeCountNat 177 = 107 := by
  rw [show 177 = 176 + 1 by norm_num, squarefreeCountNat_succ, count_176]
  norm_num [mu_177]

private theorem cell_177 :
    endpointOK (squarefreeCountNat 177) 177 ∧
      endpointOK (squarefreeCountNat 177) (177 + 1) := by
  rw [count_177]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_178 : μ 178 = 1 := by
  rw [show 178 = 2 * 89 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 89)]
  norm_num

private theorem count_178 : squarefreeCountNat 178 = 108 := by
  rw [show 178 = 177 + 1 by norm_num, squarefreeCountNat_succ, count_177]
  norm_num [mu_178]

private theorem cell_178 :
    endpointOK (squarefreeCountNat 178) 178 ∧
      endpointOK (squarefreeCountNat 178) (178 + 1) := by
  rw [count_178]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_179 : μ 179 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_179 : squarefreeCountNat 179 = 109 := by
  rw [show 179 = 178 + 1 by norm_num, squarefreeCountNat_succ, count_178]
  norm_num [mu_179]

private theorem cell_179 :
    endpointOK (squarefreeCountNat 179) 179 ∧
      endpointOK (squarefreeCountNat 179) (179 + 1) := by
  rw [count_179]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_180 : μ 180 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_180 : squarefreeCountNat 180 = 109 := by
  rw [show 180 = 179 + 1 by norm_num, squarefreeCountNat_succ, count_179]
  norm_num [mu_180]

private theorem cell_180 :
    endpointOK (squarefreeCountNat 180) 180 ∧
      endpointOK (squarefreeCountNat 180) (180 + 1) := by
  rw [count_180]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_181 : μ 181 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_181 : squarefreeCountNat 181 = 110 := by
  rw [show 181 = 180 + 1 by norm_num, squarefreeCountNat_succ, count_180]
  norm_num [mu_181]

private theorem cell_181 :
    endpointOK (squarefreeCountNat 181) 181 ∧
      endpointOK (squarefreeCountNat 181) (181 + 1) := by
  rw [count_181]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_182 : μ 182 = -1 := by
  rw [show 182 = 2 * 91 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 91 = 7 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_182 : squarefreeCountNat 182 = 111 := by
  rw [show 182 = 181 + 1 by norm_num, squarefreeCountNat_succ, count_181]
  norm_num [mu_182]

private theorem cell_182 :
    endpointOK (squarefreeCountNat 182) 182 ∧
      endpointOK (squarefreeCountNat 182) (182 + 1) := by
  rw [count_182]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_183 : μ 183 = 1 := by
  rw [show 183 = 3 * 61 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 61)]
  norm_num

private theorem count_183 : squarefreeCountNat 183 = 112 := by
  rw [show 183 = 182 + 1 by norm_num, squarefreeCountNat_succ, count_182]
  norm_num [mu_183]

private theorem cell_183 :
    endpointOK (squarefreeCountNat 183) 183 ∧
      endpointOK (squarefreeCountNat 183) (183 + 1) := by
  rw [count_183]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_184 : μ 184 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_184 : squarefreeCountNat 184 = 112 := by
  rw [show 184 = 183 + 1 by norm_num, squarefreeCountNat_succ, count_183]
  norm_num [mu_184]

private theorem cell_184 :
    endpointOK (squarefreeCountNat 184) 184 ∧
      endpointOK (squarefreeCountNat 184) (184 + 1) := by
  rw [count_184]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_185 : μ 185 = 1 := by
  rw [show 185 = 5 * 37 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 37)]
  norm_num

private theorem count_185 : squarefreeCountNat 185 = 113 := by
  rw [show 185 = 184 + 1 by norm_num, squarefreeCountNat_succ, count_184]
  norm_num [mu_185]

private theorem cell_185 :
    endpointOK (squarefreeCountNat 185) 185 ∧
      endpointOK (squarefreeCountNat 185) (185 + 1) := by
  rw [count_185]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_186 : μ 186 = -1 := by
  rw [show 186 = 2 * 93 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 93 = 3 * 31 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 31)]
  norm_num

private theorem count_186 : squarefreeCountNat 186 = 114 := by
  rw [show 186 = 185 + 1 by norm_num, squarefreeCountNat_succ, count_185]
  norm_num [mu_186]

private theorem cell_186 :
    endpointOK (squarefreeCountNat 186) 186 ∧
      endpointOK (squarefreeCountNat 186) (186 + 1) := by
  rw [count_186]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_187 : μ 187 = 1 := by
  rw [show 187 = 11 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_187 : squarefreeCountNat 187 = 115 := by
  rw [show 187 = 186 + 1 by norm_num, squarefreeCountNat_succ, count_186]
  norm_num [mu_187]

private theorem cell_187 :
    endpointOK (squarefreeCountNat 187) 187 ∧
      endpointOK (squarefreeCountNat 187) (187 + 1) := by
  rw [count_187]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_188 : μ 188 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_188 : squarefreeCountNat 188 = 115 := by
  rw [show 188 = 187 + 1 by norm_num, squarefreeCountNat_succ, count_187]
  norm_num [mu_188]

private theorem cell_188 :
    endpointOK (squarefreeCountNat 188) 188 ∧
      endpointOK (squarefreeCountNat 188) (188 + 1) := by
  rw [count_188]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_189 : μ 189 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_189 : squarefreeCountNat 189 = 115 := by
  rw [show 189 = 188 + 1 by norm_num, squarefreeCountNat_succ, count_188]
  norm_num [mu_189]

private theorem cell_189 :
    endpointOK (squarefreeCountNat 189) 189 ∧
      endpointOK (squarefreeCountNat 189) (189 + 1) := by
  rw [count_189]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_190 : μ 190 = -1 := by
  rw [show 190 = 2 * 95 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 95 = 5 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_190 : squarefreeCountNat 190 = 116 := by
  rw [show 190 = 189 + 1 by norm_num, squarefreeCountNat_succ, count_189]
  norm_num [mu_190]

private theorem cell_190 :
    endpointOK (squarefreeCountNat 190) 190 ∧
      endpointOK (squarefreeCountNat 190) (190 + 1) := by
  rw [count_190]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_191 : μ 191 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_191 : squarefreeCountNat 191 = 117 := by
  rw [show 191 = 190 + 1 by norm_num, squarefreeCountNat_succ, count_190]
  norm_num [mu_191]

private theorem cell_191 :
    endpointOK (squarefreeCountNat 191) 191 ∧
      endpointOK (squarefreeCountNat 191) (191 + 1) := by
  rw [count_191]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_192 : μ 192 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_192 : squarefreeCountNat 192 = 117 := by
  rw [show 192 = 191 + 1 by norm_num, squarefreeCountNat_succ, count_191]
  norm_num [mu_192]

private theorem cell_192 :
    endpointOK (squarefreeCountNat 192) 192 ∧
      endpointOK (squarefreeCountNat 192) (192 + 1) := by
  rw [count_192]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_193 : μ 193 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_193 : squarefreeCountNat 193 = 118 := by
  rw [show 193 = 192 + 1 by norm_num, squarefreeCountNat_succ, count_192]
  norm_num [mu_193]

private theorem cell_193 :
    endpointOK (squarefreeCountNat 193) 193 ∧
      endpointOK (squarefreeCountNat 193) (193 + 1) := by
  rw [count_193]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_194 : μ 194 = 1 := by
  rw [show 194 = 2 * 97 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 97)]
  norm_num

private theorem count_194 : squarefreeCountNat 194 = 119 := by
  rw [show 194 = 193 + 1 by norm_num, squarefreeCountNat_succ, count_193]
  norm_num [mu_194]

private theorem cell_194 :
    endpointOK (squarefreeCountNat 194) 194 ∧
      endpointOK (squarefreeCountNat 194) (194 + 1) := by
  rw [count_194]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_195 : μ 195 = -1 := by
  rw [show 195 = 3 * 65 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 65 = 5 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_195 : squarefreeCountNat 195 = 120 := by
  rw [show 195 = 194 + 1 by norm_num, squarefreeCountNat_succ, count_194]
  norm_num [mu_195]

private theorem cell_195 :
    endpointOK (squarefreeCountNat 195) 195 ∧
      endpointOK (squarefreeCountNat 195) (195 + 1) := by
  rw [count_195]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_196 : μ 196 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_196 : squarefreeCountNat 196 = 120 := by
  rw [show 196 = 195 + 1 by norm_num, squarefreeCountNat_succ, count_195]
  norm_num [mu_196]

private theorem cell_196 :
    endpointOK (squarefreeCountNat 196) 196 ∧
      endpointOK (squarefreeCountNat 196) (196 + 1) := by
  rw [count_196]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_197 : μ 197 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_197 : squarefreeCountNat 197 = 121 := by
  rw [show 197 = 196 + 1 by norm_num, squarefreeCountNat_succ, count_196]
  norm_num [mu_197]

private theorem cell_197 :
    endpointOK (squarefreeCountNat 197) 197 ∧
      endpointOK (squarefreeCountNat 197) (197 + 1) := by
  rw [count_197]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_198 : μ 198 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_198 : squarefreeCountNat 198 = 121 := by
  rw [show 198 = 197 + 1 by norm_num, squarefreeCountNat_succ, count_197]
  norm_num [mu_198]

private theorem cell_198 :
    endpointOK (squarefreeCountNat 198) 198 ∧
      endpointOK (squarefreeCountNat 198) (198 + 1) := by
  rw [count_198]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_199 : μ 199 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_199 : squarefreeCountNat 199 = 122 := by
  rw [show 199 = 198 + 1 by norm_num, squarefreeCountNat_succ, count_198]
  norm_num [mu_199]

private theorem cell_199 :
    endpointOK (squarefreeCountNat 199) 199 ∧
      endpointOK (squarefreeCountNat 199) (199 + 1) := by
  rw [count_199]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_200 : μ 200 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

theorem count_200 : squarefreeCountNat 200 = 122 := by
  rw [show 200 = 199 + 1 by norm_num, squarefreeCountNat_succ, count_199]
  norm_num [mu_200]

private theorem cell_200 :
    endpointOK (squarefreeCountNat 200) 200 ∧
      endpointOK (squarefreeCountNat 200) (200 + 1) := by
  rw [count_200]
  norm_num [endpointOK, densityLower, densityUpper]

theorem finite_endpoint_certificate_151_200 (N : ℕ)
    (hlo : 151 ≤ N) (hhi : N ≤ 200) :
    endpointOK (squarefreeCountNat N) N ∧
      endpointOK (squarefreeCountNat N) (N + 1) := by
  interval_cases N
  · exact cell_151
  · exact cell_152
  · exact cell_153
  · exact cell_154
  · exact cell_155
  · exact cell_156
  · exact cell_157
  · exact cell_158
  · exact cell_159
  · exact cell_160
  · exact cell_161
  · exact cell_162
  · exact cell_163
  · exact cell_164
  · exact cell_165
  · exact cell_166
  · exact cell_167
  · exact cell_168
  · exact cell_169
  · exact cell_170
  · exact cell_171
  · exact cell_172
  · exact cell_173
  · exact cell_174
  · exact cell_175
  · exact cell_176
  · exact cell_177
  · exact cell_178
  · exact cell_179
  · exact cell_180
  · exact cell_181
  · exact cell_182
  · exact cell_183
  · exact cell_184
  · exact cell_185
  · exact cell_186
  · exact cell_187
  · exact cell_188
  · exact cell_189
  · exact cell_190
  · exact cell_191
  · exact cell_192
  · exact cell_193
  · exact cell_194
  · exact cell_195
  · exact cell_196
  · exact cell_197
  · exact cell_198
  · exact cell_199
  · exact cell_200

end MoserMacLeod
