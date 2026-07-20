import MoserMacLeod.TableRows201_250

/-!
# Proof-producing finite rows 251--300

This generated shard proves the required Möbius values, updates the squarefree
prefix count one integer at a time, and checks the two exact rational endpoint
inequalities in each real cell.  It uses no native evaluator.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction.Moebius BigOperators
open Finset

private theorem mu_251 : μ 251 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_251 : squarefreeCountNat 251 = 154 := by
  rw [show 251 = 250 + 1 by norm_num, squarefreeCountNat_succ, count_250]
  norm_num [mu_251]

private theorem cell_251 :
    endpointOK (squarefreeCountNat 251) 251 ∧
      endpointOK (squarefreeCountNat 251) (251 + 1) := by
  rw [count_251]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_252 : μ 252 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_252 : squarefreeCountNat 252 = 154 := by
  rw [show 252 = 251 + 1 by norm_num, squarefreeCountNat_succ, count_251]
  norm_num [mu_252]

private theorem cell_252 :
    endpointOK (squarefreeCountNat 252) 252 ∧
      endpointOK (squarefreeCountNat 252) (252 + 1) := by
  rw [count_252]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_253 : μ 253 = 1 := by
  rw [show 253 = 11 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_253 : squarefreeCountNat 253 = 155 := by
  rw [show 253 = 252 + 1 by norm_num, squarefreeCountNat_succ, count_252]
  norm_num [mu_253]

private theorem cell_253 :
    endpointOK (squarefreeCountNat 253) 253 ∧
      endpointOK (squarefreeCountNat 253) (253 + 1) := by
  rw [count_253]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_254 : μ 254 = 1 := by
  rw [show 254 = 2 * 127 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 127)]
  norm_num

private theorem count_254 : squarefreeCountNat 254 = 156 := by
  rw [show 254 = 253 + 1 by norm_num, squarefreeCountNat_succ, count_253]
  norm_num [mu_254]

private theorem cell_254 :
    endpointOK (squarefreeCountNat 254) 254 ∧
      endpointOK (squarefreeCountNat 254) (254 + 1) := by
  rw [count_254]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_255 : μ 255 = -1 := by
  rw [show 255 = 3 * 85 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 85 = 5 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_255 : squarefreeCountNat 255 = 157 := by
  rw [show 255 = 254 + 1 by norm_num, squarefreeCountNat_succ, count_254]
  norm_num [mu_255]

private theorem cell_255 :
    endpointOK (squarefreeCountNat 255) 255 ∧
      endpointOK (squarefreeCountNat 255) (255 + 1) := by
  rw [count_255]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_256 : μ 256 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_256 : squarefreeCountNat 256 = 157 := by
  rw [show 256 = 255 + 1 by norm_num, squarefreeCountNat_succ, count_255]
  norm_num [mu_256]

private theorem cell_256 :
    endpointOK (squarefreeCountNat 256) 256 ∧
      endpointOK (squarefreeCountNat 256) (256 + 1) := by
  rw [count_256]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_257 : μ 257 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_257 : squarefreeCountNat 257 = 158 := by
  rw [show 257 = 256 + 1 by norm_num, squarefreeCountNat_succ, count_256]
  norm_num [mu_257]

private theorem cell_257 :
    endpointOK (squarefreeCountNat 257) 257 ∧
      endpointOK (squarefreeCountNat 257) (257 + 1) := by
  rw [count_257]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_258 : μ 258 = -1 := by
  rw [show 258 = 2 * 129 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 129 = 3 * 43 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 43)]
  norm_num

private theorem count_258 : squarefreeCountNat 258 = 159 := by
  rw [show 258 = 257 + 1 by norm_num, squarefreeCountNat_succ, count_257]
  norm_num [mu_258]

private theorem cell_258 :
    endpointOK (squarefreeCountNat 258) 258 ∧
      endpointOK (squarefreeCountNat 258) (258 + 1) := by
  rw [count_258]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_259 : μ 259 = 1 := by
  rw [show 259 = 7 * 37 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 37)]
  norm_num

private theorem count_259 : squarefreeCountNat 259 = 160 := by
  rw [show 259 = 258 + 1 by norm_num, squarefreeCountNat_succ, count_258]
  norm_num [mu_259]

private theorem cell_259 :
    endpointOK (squarefreeCountNat 259) 259 ∧
      endpointOK (squarefreeCountNat 259) (259 + 1) := by
  rw [count_259]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_260 : μ 260 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_260 : squarefreeCountNat 260 = 160 := by
  rw [show 260 = 259 + 1 by norm_num, squarefreeCountNat_succ, count_259]
  norm_num [mu_260]

private theorem cell_260 :
    endpointOK (squarefreeCountNat 260) 260 ∧
      endpointOK (squarefreeCountNat 260) (260 + 1) := by
  rw [count_260]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_261 : μ 261 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_261 : squarefreeCountNat 261 = 160 := by
  rw [show 261 = 260 + 1 by norm_num, squarefreeCountNat_succ, count_260]
  norm_num [mu_261]

private theorem cell_261 :
    endpointOK (squarefreeCountNat 261) 261 ∧
      endpointOK (squarefreeCountNat 261) (261 + 1) := by
  rw [count_261]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_262 : μ 262 = 1 := by
  rw [show 262 = 2 * 131 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 131)]
  norm_num

private theorem count_262 : squarefreeCountNat 262 = 161 := by
  rw [show 262 = 261 + 1 by norm_num, squarefreeCountNat_succ, count_261]
  norm_num [mu_262]

private theorem cell_262 :
    endpointOK (squarefreeCountNat 262) 262 ∧
      endpointOK (squarefreeCountNat 262) (262 + 1) := by
  rw [count_262]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_263 : μ 263 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_263 : squarefreeCountNat 263 = 162 := by
  rw [show 263 = 262 + 1 by norm_num, squarefreeCountNat_succ, count_262]
  norm_num [mu_263]

private theorem cell_263 :
    endpointOK (squarefreeCountNat 263) 263 ∧
      endpointOK (squarefreeCountNat 263) (263 + 1) := by
  rw [count_263]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_264 : μ 264 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_264 : squarefreeCountNat 264 = 162 := by
  rw [show 264 = 263 + 1 by norm_num, squarefreeCountNat_succ, count_263]
  norm_num [mu_264]

private theorem cell_264 :
    endpointOK (squarefreeCountNat 264) 264 ∧
      endpointOK (squarefreeCountNat 264) (264 + 1) := by
  rw [count_264]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_265 : μ 265 = 1 := by
  rw [show 265 = 5 * 53 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 53)]
  norm_num

private theorem count_265 : squarefreeCountNat 265 = 163 := by
  rw [show 265 = 264 + 1 by norm_num, squarefreeCountNat_succ, count_264]
  norm_num [mu_265]

private theorem cell_265 :
    endpointOK (squarefreeCountNat 265) 265 ∧
      endpointOK (squarefreeCountNat 265) (265 + 1) := by
  rw [count_265]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_266 : μ 266 = -1 := by
  rw [show 266 = 2 * 133 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 133 = 7 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_266 : squarefreeCountNat 266 = 164 := by
  rw [show 266 = 265 + 1 by norm_num, squarefreeCountNat_succ, count_265]
  norm_num [mu_266]

private theorem cell_266 :
    endpointOK (squarefreeCountNat 266) 266 ∧
      endpointOK (squarefreeCountNat 266) (266 + 1) := by
  rw [count_266]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_267 : μ 267 = 1 := by
  rw [show 267 = 3 * 89 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 89)]
  norm_num

private theorem count_267 : squarefreeCountNat 267 = 165 := by
  rw [show 267 = 266 + 1 by norm_num, squarefreeCountNat_succ, count_266]
  norm_num [mu_267]

private theorem cell_267 :
    endpointOK (squarefreeCountNat 267) 267 ∧
      endpointOK (squarefreeCountNat 267) (267 + 1) := by
  rw [count_267]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_268 : μ 268 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_268 : squarefreeCountNat 268 = 165 := by
  rw [show 268 = 267 + 1 by norm_num, squarefreeCountNat_succ, count_267]
  norm_num [mu_268]

private theorem cell_268 :
    endpointOK (squarefreeCountNat 268) 268 ∧
      endpointOK (squarefreeCountNat 268) (268 + 1) := by
  rw [count_268]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_269 : μ 269 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_269 : squarefreeCountNat 269 = 166 := by
  rw [show 269 = 268 + 1 by norm_num, squarefreeCountNat_succ, count_268]
  norm_num [mu_269]

private theorem cell_269 :
    endpointOK (squarefreeCountNat 269) 269 ∧
      endpointOK (squarefreeCountNat 269) (269 + 1) := by
  rw [count_269]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_270 : μ 270 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_270 : squarefreeCountNat 270 = 166 := by
  rw [show 270 = 269 + 1 by norm_num, squarefreeCountNat_succ, count_269]
  norm_num [mu_270]

private theorem cell_270 :
    endpointOK (squarefreeCountNat 270) 270 ∧
      endpointOK (squarefreeCountNat 270) (270 + 1) := by
  rw [count_270]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_271 : μ 271 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_271 : squarefreeCountNat 271 = 167 := by
  rw [show 271 = 270 + 1 by norm_num, squarefreeCountNat_succ, count_270]
  norm_num [mu_271]

private theorem cell_271 :
    endpointOK (squarefreeCountNat 271) 271 ∧
      endpointOK (squarefreeCountNat 271) (271 + 1) := by
  rw [count_271]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_272 : μ 272 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_272 : squarefreeCountNat 272 = 167 := by
  rw [show 272 = 271 + 1 by norm_num, squarefreeCountNat_succ, count_271]
  norm_num [mu_272]

private theorem cell_272 :
    endpointOK (squarefreeCountNat 272) 272 ∧
      endpointOK (squarefreeCountNat 272) (272 + 1) := by
  rw [count_272]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_273 : μ 273 = -1 := by
  rw [show 273 = 3 * 91 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 91 = 7 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_273 : squarefreeCountNat 273 = 168 := by
  rw [show 273 = 272 + 1 by norm_num, squarefreeCountNat_succ, count_272]
  norm_num [mu_273]

private theorem cell_273 :
    endpointOK (squarefreeCountNat 273) 273 ∧
      endpointOK (squarefreeCountNat 273) (273 + 1) := by
  rw [count_273]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_274 : μ 274 = 1 := by
  rw [show 274 = 2 * 137 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 137)]
  norm_num

private theorem count_274 : squarefreeCountNat 274 = 169 := by
  rw [show 274 = 273 + 1 by norm_num, squarefreeCountNat_succ, count_273]
  norm_num [mu_274]

private theorem cell_274 :
    endpointOK (squarefreeCountNat 274) 274 ∧
      endpointOK (squarefreeCountNat 274) (274 + 1) := by
  rw [count_274]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_275 : μ 275 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

private theorem count_275 : squarefreeCountNat 275 = 169 := by
  rw [show 275 = 274 + 1 by norm_num, squarefreeCountNat_succ, count_274]
  norm_num [mu_275]

private theorem cell_275 :
    endpointOK (squarefreeCountNat 275) 275 ∧
      endpointOK (squarefreeCountNat 275) (275 + 1) := by
  rw [count_275]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_276 : μ 276 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_276 : squarefreeCountNat 276 = 169 := by
  rw [show 276 = 275 + 1 by norm_num, squarefreeCountNat_succ, count_275]
  norm_num [mu_276]

private theorem cell_276 :
    endpointOK (squarefreeCountNat 276) 276 ∧
      endpointOK (squarefreeCountNat 276) (276 + 1) := by
  rw [count_276]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_277 : μ 277 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_277 : squarefreeCountNat 277 = 170 := by
  rw [show 277 = 276 + 1 by norm_num, squarefreeCountNat_succ, count_276]
  norm_num [mu_277]

private theorem cell_277 :
    endpointOK (squarefreeCountNat 277) 277 ∧
      endpointOK (squarefreeCountNat 277) (277 + 1) := by
  rw [count_277]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_278 : μ 278 = 1 := by
  rw [show 278 = 2 * 139 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 139)]
  norm_num

private theorem count_278 : squarefreeCountNat 278 = 171 := by
  rw [show 278 = 277 + 1 by norm_num, squarefreeCountNat_succ, count_277]
  norm_num [mu_278]

private theorem cell_278 :
    endpointOK (squarefreeCountNat 278) 278 ∧
      endpointOK (squarefreeCountNat 278) (278 + 1) := by
  rw [count_278]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_279 : μ 279 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_279 : squarefreeCountNat 279 = 171 := by
  rw [show 279 = 278 + 1 by norm_num, squarefreeCountNat_succ, count_278]
  norm_num [mu_279]

private theorem cell_279 :
    endpointOK (squarefreeCountNat 279) 279 ∧
      endpointOK (squarefreeCountNat 279) (279 + 1) := by
  rw [count_279]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_280 : μ 280 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_280 : squarefreeCountNat 280 = 171 := by
  rw [show 280 = 279 + 1 by norm_num, squarefreeCountNat_succ, count_279]
  norm_num [mu_280]

private theorem cell_280 :
    endpointOK (squarefreeCountNat 280) 280 ∧
      endpointOK (squarefreeCountNat 280) (280 + 1) := by
  rw [count_280]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_281 : μ 281 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_281 : squarefreeCountNat 281 = 172 := by
  rw [show 281 = 280 + 1 by norm_num, squarefreeCountNat_succ, count_280]
  norm_num [mu_281]

private theorem cell_281 :
    endpointOK (squarefreeCountNat 281) 281 ∧
      endpointOK (squarefreeCountNat 281) (281 + 1) := by
  rw [count_281]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_282 : μ 282 = -1 := by
  rw [show 282 = 2 * 141 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 141 = 3 * 47 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 47)]
  norm_num

private theorem count_282 : squarefreeCountNat 282 = 173 := by
  rw [show 282 = 281 + 1 by norm_num, squarefreeCountNat_succ, count_281]
  norm_num [mu_282]

private theorem cell_282 :
    endpointOK (squarefreeCountNat 282) 282 ∧
      endpointOK (squarefreeCountNat 282) (282 + 1) := by
  rw [count_282]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_283 : μ 283 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_283 : squarefreeCountNat 283 = 174 := by
  rw [show 283 = 282 + 1 by norm_num, squarefreeCountNat_succ, count_282]
  norm_num [mu_283]

private theorem cell_283 :
    endpointOK (squarefreeCountNat 283) 283 ∧
      endpointOK (squarefreeCountNat 283) (283 + 1) := by
  rw [count_283]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_284 : μ 284 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_284 : squarefreeCountNat 284 = 174 := by
  rw [show 284 = 283 + 1 by norm_num, squarefreeCountNat_succ, count_283]
  norm_num [mu_284]

private theorem cell_284 :
    endpointOK (squarefreeCountNat 284) 284 ∧
      endpointOK (squarefreeCountNat 284) (284 + 1) := by
  rw [count_284]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_285 : μ 285 = -1 := by
  rw [show 285 = 3 * 95 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 95 = 5 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_285 : squarefreeCountNat 285 = 175 := by
  rw [show 285 = 284 + 1 by norm_num, squarefreeCountNat_succ, count_284]
  norm_num [mu_285]

private theorem cell_285 :
    endpointOK (squarefreeCountNat 285) 285 ∧
      endpointOK (squarefreeCountNat 285) (285 + 1) := by
  rw [count_285]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_286 : μ 286 = -1 := by
  rw [show 286 = 2 * 143 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 143 = 11 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_286 : squarefreeCountNat 286 = 176 := by
  rw [show 286 = 285 + 1 by norm_num, squarefreeCountNat_succ, count_285]
  norm_num [mu_286]

private theorem cell_286 :
    endpointOK (squarefreeCountNat 286) 286 ∧
      endpointOK (squarefreeCountNat 286) (286 + 1) := by
  rw [count_286]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_287 : μ 287 = 1 := by
  rw [show 287 = 7 * 41 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 41)]
  norm_num

private theorem count_287 : squarefreeCountNat 287 = 177 := by
  rw [show 287 = 286 + 1 by norm_num, squarefreeCountNat_succ, count_286]
  norm_num [mu_287]

private theorem cell_287 :
    endpointOK (squarefreeCountNat 287) 287 ∧
      endpointOK (squarefreeCountNat 287) (287 + 1) := by
  rw [count_287]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_288 : μ 288 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_288 : squarefreeCountNat 288 = 177 := by
  rw [show 288 = 287 + 1 by norm_num, squarefreeCountNat_succ, count_287]
  norm_num [mu_288]

private theorem cell_288 :
    endpointOK (squarefreeCountNat 288) 288 ∧
      endpointOK (squarefreeCountNat 288) (288 + 1) := by
  rw [count_288]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_289 : μ 289 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 17 (by norm_num) (by norm_num)

private theorem count_289 : squarefreeCountNat 289 = 177 := by
  rw [show 289 = 288 + 1 by norm_num, squarefreeCountNat_succ, count_288]
  norm_num [mu_289]

private theorem cell_289 :
    endpointOK (squarefreeCountNat 289) 289 ∧
      endpointOK (squarefreeCountNat 289) (289 + 1) := by
  rw [count_289]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_290 : μ 290 = -1 := by
  rw [show 290 = 2 * 145 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 145 = 5 * 29 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 29)]
  norm_num

private theorem count_290 : squarefreeCountNat 290 = 178 := by
  rw [show 290 = 289 + 1 by norm_num, squarefreeCountNat_succ, count_289]
  norm_num [mu_290]

private theorem cell_290 :
    endpointOK (squarefreeCountNat 290) 290 ∧
      endpointOK (squarefreeCountNat 290) (290 + 1) := by
  rw [count_290]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_291 : μ 291 = 1 := by
  rw [show 291 = 3 * 97 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 97)]
  norm_num

private theorem count_291 : squarefreeCountNat 291 = 179 := by
  rw [show 291 = 290 + 1 by norm_num, squarefreeCountNat_succ, count_290]
  norm_num [mu_291]

private theorem cell_291 :
    endpointOK (squarefreeCountNat 291) 291 ∧
      endpointOK (squarefreeCountNat 291) (291 + 1) := by
  rw [count_291]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_292 : μ 292 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_292 : squarefreeCountNat 292 = 179 := by
  rw [show 292 = 291 + 1 by norm_num, squarefreeCountNat_succ, count_291]
  norm_num [mu_292]

private theorem cell_292 :
    endpointOK (squarefreeCountNat 292) 292 ∧
      endpointOK (squarefreeCountNat 292) (292 + 1) := by
  rw [count_292]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_293 : μ 293 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_293 : squarefreeCountNat 293 = 180 := by
  rw [show 293 = 292 + 1 by norm_num, squarefreeCountNat_succ, count_292]
  norm_num [mu_293]

private theorem cell_293 :
    endpointOK (squarefreeCountNat 293) 293 ∧
      endpointOK (squarefreeCountNat 293) (293 + 1) := by
  rw [count_293]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_294 : μ 294 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 7 (by norm_num) (by norm_num)

private theorem count_294 : squarefreeCountNat 294 = 180 := by
  rw [show 294 = 293 + 1 by norm_num, squarefreeCountNat_succ, count_293]
  norm_num [mu_294]

private theorem cell_294 :
    endpointOK (squarefreeCountNat 294) 294 ∧
      endpointOK (squarefreeCountNat 294) (294 + 1) := by
  rw [count_294]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_295 : μ 295 = 1 := by
  rw [show 295 = 5 * 59 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 59)]
  norm_num

private theorem count_295 : squarefreeCountNat 295 = 181 := by
  rw [show 295 = 294 + 1 by norm_num, squarefreeCountNat_succ, count_294]
  norm_num [mu_295]

private theorem cell_295 :
    endpointOK (squarefreeCountNat 295) 295 ∧
      endpointOK (squarefreeCountNat 295) (295 + 1) := by
  rw [count_295]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_296 : μ 296 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_296 : squarefreeCountNat 296 = 181 := by
  rw [show 296 = 295 + 1 by norm_num, squarefreeCountNat_succ, count_295]
  norm_num [mu_296]

private theorem cell_296 :
    endpointOK (squarefreeCountNat 296) 296 ∧
      endpointOK (squarefreeCountNat 296) (296 + 1) := by
  rw [count_296]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_297 : μ 297 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_297 : squarefreeCountNat 297 = 181 := by
  rw [show 297 = 296 + 1 by norm_num, squarefreeCountNat_succ, count_296]
  norm_num [mu_297]

private theorem cell_297 :
    endpointOK (squarefreeCountNat 297) 297 ∧
      endpointOK (squarefreeCountNat 297) (297 + 1) := by
  rw [count_297]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_298 : μ 298 = 1 := by
  rw [show 298 = 2 * 149 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 149)]
  norm_num

private theorem count_298 : squarefreeCountNat 298 = 182 := by
  rw [show 298 = 297 + 1 by norm_num, squarefreeCountNat_succ, count_297]
  norm_num [mu_298]

private theorem cell_298 :
    endpointOK (squarefreeCountNat 298) 298 ∧
      endpointOK (squarefreeCountNat 298) (298 + 1) := by
  rw [count_298]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_299 : μ 299 = 1 := by
  rw [show 299 = 13 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_299 : squarefreeCountNat 299 = 183 := by
  rw [show 299 = 298 + 1 by norm_num, squarefreeCountNat_succ, count_298]
  norm_num [mu_299]

private theorem cell_299 :
    endpointOK (squarefreeCountNat 299) 299 ∧
      endpointOK (squarefreeCountNat 299) (299 + 1) := by
  rw [count_299]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_300 : μ 300 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

theorem count_300 : squarefreeCountNat 300 = 183 := by
  rw [show 300 = 299 + 1 by norm_num, squarefreeCountNat_succ, count_299]
  norm_num [mu_300]

private theorem cell_300 :
    endpointOK (squarefreeCountNat 300) 300 ∧
      endpointOK (squarefreeCountNat 300) (300 + 1) := by
  rw [count_300]
  norm_num [endpointOK, densityLower, densityUpper]

theorem finite_endpoint_certificate_251_300 (N : ℕ)
    (hlo : 251 ≤ N) (hhi : N ≤ 300) :
    endpointOK (squarefreeCountNat N) N ∧
      endpointOK (squarefreeCountNat N) (N + 1) := by
  interval_cases N
  · exact cell_251
  · exact cell_252
  · exact cell_253
  · exact cell_254
  · exact cell_255
  · exact cell_256
  · exact cell_257
  · exact cell_258
  · exact cell_259
  · exact cell_260
  · exact cell_261
  · exact cell_262
  · exact cell_263
  · exact cell_264
  · exact cell_265
  · exact cell_266
  · exact cell_267
  · exact cell_268
  · exact cell_269
  · exact cell_270
  · exact cell_271
  · exact cell_272
  · exact cell_273
  · exact cell_274
  · exact cell_275
  · exact cell_276
  · exact cell_277
  · exact cell_278
  · exact cell_279
  · exact cell_280
  · exact cell_281
  · exact cell_282
  · exact cell_283
  · exact cell_284
  · exact cell_285
  · exact cell_286
  · exact cell_287
  · exact cell_288
  · exact cell_289
  · exact cell_290
  · exact cell_291
  · exact cell_292
  · exact cell_293
  · exact cell_294
  · exact cell_295
  · exact cell_296
  · exact cell_297
  · exact cell_298
  · exact cell_299
  · exact cell_300

end MoserMacLeod
