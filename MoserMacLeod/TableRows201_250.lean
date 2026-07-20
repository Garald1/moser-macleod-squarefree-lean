import MoserMacLeod.TableRows151_200

/-!
# Proof-producing finite rows 201--250

This generated shard proves the required Möbius values, updates the squarefree
prefix count one integer at a time, and checks the two exact rational endpoint
inequalities in each real cell.  It uses no native evaluator.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction.Moebius BigOperators
open Finset

private theorem mu_201 : μ 201 = 1 := by
  rw [show 201 = 3 * 67 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 67)]
  norm_num

private theorem count_201 : squarefreeCountNat 201 = 123 := by
  rw [show 201 = 200 + 1 by norm_num, squarefreeCountNat_succ, count_200]
  norm_num [mu_201]

private theorem cell_201 :
    endpointOK (squarefreeCountNat 201) 201 ∧
      endpointOK (squarefreeCountNat 201) (201 + 1) := by
  rw [count_201]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_202 : μ 202 = 1 := by
  rw [show 202 = 2 * 101 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 101)]
  norm_num

private theorem count_202 : squarefreeCountNat 202 = 124 := by
  rw [show 202 = 201 + 1 by norm_num, squarefreeCountNat_succ, count_201]
  norm_num [mu_202]

private theorem cell_202 :
    endpointOK (squarefreeCountNat 202) 202 ∧
      endpointOK (squarefreeCountNat 202) (202 + 1) := by
  rw [count_202]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_203 : μ 203 = 1 := by
  rw [show 203 = 7 * 29 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 29)]
  norm_num

private theorem count_203 : squarefreeCountNat 203 = 125 := by
  rw [show 203 = 202 + 1 by norm_num, squarefreeCountNat_succ, count_202]
  norm_num [mu_203]

private theorem cell_203 :
    endpointOK (squarefreeCountNat 203) 203 ∧
      endpointOK (squarefreeCountNat 203) (203 + 1) := by
  rw [count_203]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_204 : μ 204 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_204 : squarefreeCountNat 204 = 125 := by
  rw [show 204 = 203 + 1 by norm_num, squarefreeCountNat_succ, count_203]
  norm_num [mu_204]

private theorem cell_204 :
    endpointOK (squarefreeCountNat 204) 204 ∧
      endpointOK (squarefreeCountNat 204) (204 + 1) := by
  rw [count_204]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_205 : μ 205 = 1 := by
  rw [show 205 = 5 * 41 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 41)]
  norm_num

private theorem count_205 : squarefreeCountNat 205 = 126 := by
  rw [show 205 = 204 + 1 by norm_num, squarefreeCountNat_succ, count_204]
  norm_num [mu_205]

private theorem cell_205 :
    endpointOK (squarefreeCountNat 205) 205 ∧
      endpointOK (squarefreeCountNat 205) (205 + 1) := by
  rw [count_205]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_206 : μ 206 = 1 := by
  rw [show 206 = 2 * 103 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 103)]
  norm_num

private theorem count_206 : squarefreeCountNat 206 = 127 := by
  rw [show 206 = 205 + 1 by norm_num, squarefreeCountNat_succ, count_205]
  norm_num [mu_206]

private theorem cell_206 :
    endpointOK (squarefreeCountNat 206) 206 ∧
      endpointOK (squarefreeCountNat 206) (206 + 1) := by
  rw [count_206]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_207 : μ 207 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_207 : squarefreeCountNat 207 = 127 := by
  rw [show 207 = 206 + 1 by norm_num, squarefreeCountNat_succ, count_206]
  norm_num [mu_207]

private theorem cell_207 :
    endpointOK (squarefreeCountNat 207) 207 ∧
      endpointOK (squarefreeCountNat 207) (207 + 1) := by
  rw [count_207]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_208 : μ 208 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_208 : squarefreeCountNat 208 = 127 := by
  rw [show 208 = 207 + 1 by norm_num, squarefreeCountNat_succ, count_207]
  norm_num [mu_208]

private theorem cell_208 :
    endpointOK (squarefreeCountNat 208) 208 ∧
      endpointOK (squarefreeCountNat 208) (208 + 1) := by
  rw [count_208]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_209 : μ 209 = 1 := by
  rw [show 209 = 11 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_209 : squarefreeCountNat 209 = 128 := by
  rw [show 209 = 208 + 1 by norm_num, squarefreeCountNat_succ, count_208]
  norm_num [mu_209]

private theorem cell_209 :
    endpointOK (squarefreeCountNat 209) 209 ∧
      endpointOK (squarefreeCountNat 209) (209 + 1) := by
  rw [count_209]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_210 : μ 210 = 1 := by
  rw [show 210 = 2 * 105 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 105 = 3 * 35 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 35 = 5 * 7 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7)]
  norm_num

private theorem count_210 : squarefreeCountNat 210 = 129 := by
  rw [show 210 = 209 + 1 by norm_num, squarefreeCountNat_succ, count_209]
  norm_num [mu_210]

private theorem cell_210 :
    endpointOK (squarefreeCountNat 210) 210 ∧
      endpointOK (squarefreeCountNat 210) (210 + 1) := by
  rw [count_210]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_211 : μ 211 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_211 : squarefreeCountNat 211 = 130 := by
  rw [show 211 = 210 + 1 by norm_num, squarefreeCountNat_succ, count_210]
  norm_num [mu_211]

private theorem cell_211 :
    endpointOK (squarefreeCountNat 211) 211 ∧
      endpointOK (squarefreeCountNat 211) (211 + 1) := by
  rw [count_211]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_212 : μ 212 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_212 : squarefreeCountNat 212 = 130 := by
  rw [show 212 = 211 + 1 by norm_num, squarefreeCountNat_succ, count_211]
  norm_num [mu_212]

private theorem cell_212 :
    endpointOK (squarefreeCountNat 212) 212 ∧
      endpointOK (squarefreeCountNat 212) (212 + 1) := by
  rw [count_212]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_213 : μ 213 = 1 := by
  rw [show 213 = 3 * 71 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 71)]
  norm_num

private theorem count_213 : squarefreeCountNat 213 = 131 := by
  rw [show 213 = 212 + 1 by norm_num, squarefreeCountNat_succ, count_212]
  norm_num [mu_213]

private theorem cell_213 :
    endpointOK (squarefreeCountNat 213) 213 ∧
      endpointOK (squarefreeCountNat 213) (213 + 1) := by
  rw [count_213]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_214 : μ 214 = 1 := by
  rw [show 214 = 2 * 107 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 107)]
  norm_num

private theorem count_214 : squarefreeCountNat 214 = 132 := by
  rw [show 214 = 213 + 1 by norm_num, squarefreeCountNat_succ, count_213]
  norm_num [mu_214]

private theorem cell_214 :
    endpointOK (squarefreeCountNat 214) 214 ∧
      endpointOK (squarefreeCountNat 214) (214 + 1) := by
  rw [count_214]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_215 : μ 215 = 1 := by
  rw [show 215 = 5 * 43 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 43)]
  norm_num

private theorem count_215 : squarefreeCountNat 215 = 133 := by
  rw [show 215 = 214 + 1 by norm_num, squarefreeCountNat_succ, count_214]
  norm_num [mu_215]

private theorem cell_215 :
    endpointOK (squarefreeCountNat 215) 215 ∧
      endpointOK (squarefreeCountNat 215) (215 + 1) := by
  rw [count_215]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_216 : μ 216 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_216 : squarefreeCountNat 216 = 133 := by
  rw [show 216 = 215 + 1 by norm_num, squarefreeCountNat_succ, count_215]
  norm_num [mu_216]

private theorem cell_216 :
    endpointOK (squarefreeCountNat 216) 216 ∧
      endpointOK (squarefreeCountNat 216) (216 + 1) := by
  rw [count_216]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_217 : μ 217 = 1 := by
  rw [show 217 = 7 * 31 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 31)]
  norm_num

private theorem count_217 : squarefreeCountNat 217 = 134 := by
  rw [show 217 = 216 + 1 by norm_num, squarefreeCountNat_succ, count_216]
  norm_num [mu_217]

private theorem cell_217 :
    endpointOK (squarefreeCountNat 217) 217 ∧
      endpointOK (squarefreeCountNat 217) (217 + 1) := by
  rw [count_217]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_218 : μ 218 = 1 := by
  rw [show 218 = 2 * 109 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 109)]
  norm_num

private theorem count_218 : squarefreeCountNat 218 = 135 := by
  rw [show 218 = 217 + 1 by norm_num, squarefreeCountNat_succ, count_217]
  norm_num [mu_218]

private theorem cell_218 :
    endpointOK (squarefreeCountNat 218) 218 ∧
      endpointOK (squarefreeCountNat 218) (218 + 1) := by
  rw [count_218]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_219 : μ 219 = 1 := by
  rw [show 219 = 3 * 73 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 73)]
  norm_num

private theorem count_219 : squarefreeCountNat 219 = 136 := by
  rw [show 219 = 218 + 1 by norm_num, squarefreeCountNat_succ, count_218]
  norm_num [mu_219]

private theorem cell_219 :
    endpointOK (squarefreeCountNat 219) 219 ∧
      endpointOK (squarefreeCountNat 219) (219 + 1) := by
  rw [count_219]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_220 : μ 220 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_220 : squarefreeCountNat 220 = 136 := by
  rw [show 220 = 219 + 1 by norm_num, squarefreeCountNat_succ, count_219]
  norm_num [mu_220]

private theorem cell_220 :
    endpointOK (squarefreeCountNat 220) 220 ∧
      endpointOK (squarefreeCountNat 220) (220 + 1) := by
  rw [count_220]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_221 : μ 221 = 1 := by
  rw [show 221 = 13 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_221 : squarefreeCountNat 221 = 137 := by
  rw [show 221 = 220 + 1 by norm_num, squarefreeCountNat_succ, count_220]
  norm_num [mu_221]

private theorem cell_221 :
    endpointOK (squarefreeCountNat 221) 221 ∧
      endpointOK (squarefreeCountNat 221) (221 + 1) := by
  rw [count_221]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_222 : μ 222 = -1 := by
  rw [show 222 = 2 * 111 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 111 = 3 * 37 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 37)]
  norm_num

private theorem count_222 : squarefreeCountNat 222 = 138 := by
  rw [show 222 = 221 + 1 by norm_num, squarefreeCountNat_succ, count_221]
  norm_num [mu_222]

private theorem cell_222 :
    endpointOK (squarefreeCountNat 222) 222 ∧
      endpointOK (squarefreeCountNat 222) (222 + 1) := by
  rw [count_222]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_223 : μ 223 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_223 : squarefreeCountNat 223 = 139 := by
  rw [show 223 = 222 + 1 by norm_num, squarefreeCountNat_succ, count_222]
  norm_num [mu_223]

private theorem cell_223 :
    endpointOK (squarefreeCountNat 223) 223 ∧
      endpointOK (squarefreeCountNat 223) (223 + 1) := by
  rw [count_223]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_224 : μ 224 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_224 : squarefreeCountNat 224 = 139 := by
  rw [show 224 = 223 + 1 by norm_num, squarefreeCountNat_succ, count_223]
  norm_num [mu_224]

private theorem cell_224 :
    endpointOK (squarefreeCountNat 224) 224 ∧
      endpointOK (squarefreeCountNat 224) (224 + 1) := by
  rw [count_224]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_225 : μ 225 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_225 : squarefreeCountNat 225 = 139 := by
  rw [show 225 = 224 + 1 by norm_num, squarefreeCountNat_succ, count_224]
  norm_num [mu_225]

private theorem cell_225 :
    endpointOK (squarefreeCountNat 225) 225 ∧
      endpointOK (squarefreeCountNat 225) (225 + 1) := by
  rw [count_225]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_226 : μ 226 = 1 := by
  rw [show 226 = 2 * 113 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 113)]
  norm_num

private theorem count_226 : squarefreeCountNat 226 = 140 := by
  rw [show 226 = 225 + 1 by norm_num, squarefreeCountNat_succ, count_225]
  norm_num [mu_226]

private theorem cell_226 :
    endpointOK (squarefreeCountNat 226) 226 ∧
      endpointOK (squarefreeCountNat 226) (226 + 1) := by
  rw [count_226]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_227 : μ 227 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_227 : squarefreeCountNat 227 = 141 := by
  rw [show 227 = 226 + 1 by norm_num, squarefreeCountNat_succ, count_226]
  norm_num [mu_227]

private theorem cell_227 :
    endpointOK (squarefreeCountNat 227) 227 ∧
      endpointOK (squarefreeCountNat 227) (227 + 1) := by
  rw [count_227]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_228 : μ 228 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_228 : squarefreeCountNat 228 = 141 := by
  rw [show 228 = 227 + 1 by norm_num, squarefreeCountNat_succ, count_227]
  norm_num [mu_228]

private theorem cell_228 :
    endpointOK (squarefreeCountNat 228) 228 ∧
      endpointOK (squarefreeCountNat 228) (228 + 1) := by
  rw [count_228]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_229 : μ 229 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_229 : squarefreeCountNat 229 = 142 := by
  rw [show 229 = 228 + 1 by norm_num, squarefreeCountNat_succ, count_228]
  norm_num [mu_229]

private theorem cell_229 :
    endpointOK (squarefreeCountNat 229) 229 ∧
      endpointOK (squarefreeCountNat 229) (229 + 1) := by
  rw [count_229]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_230 : μ 230 = -1 := by
  rw [show 230 = 2 * 115 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 115 = 5 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_230 : squarefreeCountNat 230 = 143 := by
  rw [show 230 = 229 + 1 by norm_num, squarefreeCountNat_succ, count_229]
  norm_num [mu_230]

private theorem cell_230 :
    endpointOK (squarefreeCountNat 230) 230 ∧
      endpointOK (squarefreeCountNat 230) (230 + 1) := by
  rw [count_230]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_231 : μ 231 = -1 := by
  rw [show 231 = 3 * 77 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 77 = 7 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_231 : squarefreeCountNat 231 = 144 := by
  rw [show 231 = 230 + 1 by norm_num, squarefreeCountNat_succ, count_230]
  norm_num [mu_231]

private theorem cell_231 :
    endpointOK (squarefreeCountNat 231) 231 ∧
      endpointOK (squarefreeCountNat 231) (231 + 1) := by
  rw [count_231]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_232 : μ 232 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_232 : squarefreeCountNat 232 = 144 := by
  rw [show 232 = 231 + 1 by norm_num, squarefreeCountNat_succ, count_231]
  norm_num [mu_232]

private theorem cell_232 :
    endpointOK (squarefreeCountNat 232) 232 ∧
      endpointOK (squarefreeCountNat 232) (232 + 1) := by
  rw [count_232]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_233 : μ 233 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_233 : squarefreeCountNat 233 = 145 := by
  rw [show 233 = 232 + 1 by norm_num, squarefreeCountNat_succ, count_232]
  norm_num [mu_233]

private theorem cell_233 :
    endpointOK (squarefreeCountNat 233) 233 ∧
      endpointOK (squarefreeCountNat 233) (233 + 1) := by
  rw [count_233]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_234 : μ 234 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_234 : squarefreeCountNat 234 = 145 := by
  rw [show 234 = 233 + 1 by norm_num, squarefreeCountNat_succ, count_233]
  norm_num [mu_234]

private theorem cell_234 :
    endpointOK (squarefreeCountNat 234) 234 ∧
      endpointOK (squarefreeCountNat 234) (234 + 1) := by
  rw [count_234]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_235 : μ 235 = 1 := by
  rw [show 235 = 5 * 47 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 47)]
  norm_num

private theorem count_235 : squarefreeCountNat 235 = 146 := by
  rw [show 235 = 234 + 1 by norm_num, squarefreeCountNat_succ, count_234]
  norm_num [mu_235]

private theorem cell_235 :
    endpointOK (squarefreeCountNat 235) 235 ∧
      endpointOK (squarefreeCountNat 235) (235 + 1) := by
  rw [count_235]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_236 : μ 236 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_236 : squarefreeCountNat 236 = 146 := by
  rw [show 236 = 235 + 1 by norm_num, squarefreeCountNat_succ, count_235]
  norm_num [mu_236]

private theorem cell_236 :
    endpointOK (squarefreeCountNat 236) 236 ∧
      endpointOK (squarefreeCountNat 236) (236 + 1) := by
  rw [count_236]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_237 : μ 237 = 1 := by
  rw [show 237 = 3 * 79 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 79)]
  norm_num

private theorem count_237 : squarefreeCountNat 237 = 147 := by
  rw [show 237 = 236 + 1 by norm_num, squarefreeCountNat_succ, count_236]
  norm_num [mu_237]

private theorem cell_237 :
    endpointOK (squarefreeCountNat 237) 237 ∧
      endpointOK (squarefreeCountNat 237) (237 + 1) := by
  rw [count_237]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_238 : μ 238 = -1 := by
  rw [show 238 = 2 * 119 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 119 = 7 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_238 : squarefreeCountNat 238 = 148 := by
  rw [show 238 = 237 + 1 by norm_num, squarefreeCountNat_succ, count_237]
  norm_num [mu_238]

private theorem cell_238 :
    endpointOK (squarefreeCountNat 238) 238 ∧
      endpointOK (squarefreeCountNat 238) (238 + 1) := by
  rw [count_238]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_239 : μ 239 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_239 : squarefreeCountNat 239 = 149 := by
  rw [show 239 = 238 + 1 by norm_num, squarefreeCountNat_succ, count_238]
  norm_num [mu_239]

private theorem cell_239 :
    endpointOK (squarefreeCountNat 239) 239 ∧
      endpointOK (squarefreeCountNat 239) (239 + 1) := by
  rw [count_239]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_240 : μ 240 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_240 : squarefreeCountNat 240 = 149 := by
  rw [show 240 = 239 + 1 by norm_num, squarefreeCountNat_succ, count_239]
  norm_num [mu_240]

private theorem cell_240 :
    endpointOK (squarefreeCountNat 240) 240 ∧
      endpointOK (squarefreeCountNat 240) (240 + 1) := by
  rw [count_240]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_241 : μ 241 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_241 : squarefreeCountNat 241 = 150 := by
  rw [show 241 = 240 + 1 by norm_num, squarefreeCountNat_succ, count_240]
  norm_num [mu_241]

private theorem cell_241 :
    endpointOK (squarefreeCountNat 241) 241 ∧
      endpointOK (squarefreeCountNat 241) (241 + 1) := by
  rw [count_241]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_242 : μ 242 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 11 (by norm_num) (by norm_num)

private theorem count_242 : squarefreeCountNat 242 = 150 := by
  rw [show 242 = 241 + 1 by norm_num, squarefreeCountNat_succ, count_241]
  norm_num [mu_242]

private theorem cell_242 :
    endpointOK (squarefreeCountNat 242) 242 ∧
      endpointOK (squarefreeCountNat 242) (242 + 1) := by
  rw [count_242]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_243 : μ 243 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_243 : squarefreeCountNat 243 = 150 := by
  rw [show 243 = 242 + 1 by norm_num, squarefreeCountNat_succ, count_242]
  norm_num [mu_243]

private theorem cell_243 :
    endpointOK (squarefreeCountNat 243) 243 ∧
      endpointOK (squarefreeCountNat 243) (243 + 1) := by
  rw [count_243]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_244 : μ 244 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_244 : squarefreeCountNat 244 = 150 := by
  rw [show 244 = 243 + 1 by norm_num, squarefreeCountNat_succ, count_243]
  norm_num [mu_244]

private theorem cell_244 :
    endpointOK (squarefreeCountNat 244) 244 ∧
      endpointOK (squarefreeCountNat 244) (244 + 1) := by
  rw [count_244]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_245 : μ 245 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 7 (by norm_num) (by norm_num)

private theorem count_245 : squarefreeCountNat 245 = 150 := by
  rw [show 245 = 244 + 1 by norm_num, squarefreeCountNat_succ, count_244]
  norm_num [mu_245]

private theorem cell_245 :
    endpointOK (squarefreeCountNat 245) 245 ∧
      endpointOK (squarefreeCountNat 245) (245 + 1) := by
  rw [count_245]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_246 : μ 246 = -1 := by
  rw [show 246 = 2 * 123 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 123 = 3 * 41 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 41)]
  norm_num

private theorem count_246 : squarefreeCountNat 246 = 151 := by
  rw [show 246 = 245 + 1 by norm_num, squarefreeCountNat_succ, count_245]
  norm_num [mu_246]

private theorem cell_246 :
    endpointOK (squarefreeCountNat 246) 246 ∧
      endpointOK (squarefreeCountNat 246) (246 + 1) := by
  rw [count_246]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_247 : μ 247 = 1 := by
  rw [show 247 = 13 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_247 : squarefreeCountNat 247 = 152 := by
  rw [show 247 = 246 + 1 by norm_num, squarefreeCountNat_succ, count_246]
  norm_num [mu_247]

private theorem cell_247 :
    endpointOK (squarefreeCountNat 247) 247 ∧
      endpointOK (squarefreeCountNat 247) (247 + 1) := by
  rw [count_247]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_248 : μ 248 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_248 : squarefreeCountNat 248 = 152 := by
  rw [show 248 = 247 + 1 by norm_num, squarefreeCountNat_succ, count_247]
  norm_num [mu_248]

private theorem cell_248 :
    endpointOK (squarefreeCountNat 248) 248 ∧
      endpointOK (squarefreeCountNat 248) (248 + 1) := by
  rw [count_248]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_249 : μ 249 = 1 := by
  rw [show 249 = 3 * 83 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 83)]
  norm_num

private theorem count_249 : squarefreeCountNat 249 = 153 := by
  rw [show 249 = 248 + 1 by norm_num, squarefreeCountNat_succ, count_248]
  norm_num [mu_249]

private theorem cell_249 :
    endpointOK (squarefreeCountNat 249) 249 ∧
      endpointOK (squarefreeCountNat 249) (249 + 1) := by
  rw [count_249]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_250 : μ 250 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

theorem count_250 : squarefreeCountNat 250 = 153 := by
  rw [show 250 = 249 + 1 by norm_num, squarefreeCountNat_succ, count_249]
  norm_num [mu_250]

private theorem cell_250 :
    endpointOK (squarefreeCountNat 250) 250 ∧
      endpointOK (squarefreeCountNat 250) (250 + 1) := by
  rw [count_250]
  norm_num [endpointOK, densityLower, densityUpper]

theorem finite_endpoint_certificate_201_250 (N : ℕ)
    (hlo : 201 ≤ N) (hhi : N ≤ 250) :
    endpointOK (squarefreeCountNat N) N ∧
      endpointOK (squarefreeCountNat N) (N + 1) := by
  interval_cases N
  · exact cell_201
  · exact cell_202
  · exact cell_203
  · exact cell_204
  · exact cell_205
  · exact cell_206
  · exact cell_207
  · exact cell_208
  · exact cell_209
  · exact cell_210
  · exact cell_211
  · exact cell_212
  · exact cell_213
  · exact cell_214
  · exact cell_215
  · exact cell_216
  · exact cell_217
  · exact cell_218
  · exact cell_219
  · exact cell_220
  · exact cell_221
  · exact cell_222
  · exact cell_223
  · exact cell_224
  · exact cell_225
  · exact cell_226
  · exact cell_227
  · exact cell_228
  · exact cell_229
  · exact cell_230
  · exact cell_231
  · exact cell_232
  · exact cell_233
  · exact cell_234
  · exact cell_235
  · exact cell_236
  · exact cell_237
  · exact cell_238
  · exact cell_239
  · exact cell_240
  · exact cell_241
  · exact cell_242
  · exact cell_243
  · exact cell_244
  · exact cell_245
  · exact cell_246
  · exact cell_247
  · exact cell_248
  · exact cell_249
  · exact cell_250

end MoserMacLeod
