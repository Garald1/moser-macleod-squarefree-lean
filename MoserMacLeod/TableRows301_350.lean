import MoserMacLeod.TableRows251_300

/-!
# Proof-producing finite rows 301--350

This generated shard proves the required Möbius values, updates the squarefree
prefix count one integer at a time, and checks the two exact rational endpoint
inequalities in each real cell.  It uses no native evaluator.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction.Moebius BigOperators
open Finset

private theorem mu_301 : μ 301 = 1 := by
  rw [show 301 = 7 * 43 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 43)]
  norm_num

private theorem count_301 : squarefreeCountNat 301 = 184 := by
  rw [show 301 = 300 + 1 by norm_num, squarefreeCountNat_succ, count_300]
  norm_num [mu_301]

private theorem cell_301 :
    endpointOK (squarefreeCountNat 301) 301 ∧
      endpointOK (squarefreeCountNat 301) (301 + 1) := by
  rw [count_301]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_302 : μ 302 = 1 := by
  rw [show 302 = 2 * 151 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 151)]
  norm_num

private theorem count_302 : squarefreeCountNat 302 = 185 := by
  rw [show 302 = 301 + 1 by norm_num, squarefreeCountNat_succ, count_301]
  norm_num [mu_302]

private theorem cell_302 :
    endpointOK (squarefreeCountNat 302) 302 ∧
      endpointOK (squarefreeCountNat 302) (302 + 1) := by
  rw [count_302]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_303 : μ 303 = 1 := by
  rw [show 303 = 3 * 101 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 101)]
  norm_num

private theorem count_303 : squarefreeCountNat 303 = 186 := by
  rw [show 303 = 302 + 1 by norm_num, squarefreeCountNat_succ, count_302]
  norm_num [mu_303]

private theorem cell_303 :
    endpointOK (squarefreeCountNat 303) 303 ∧
      endpointOK (squarefreeCountNat 303) (303 + 1) := by
  rw [count_303]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_304 : μ 304 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_304 : squarefreeCountNat 304 = 186 := by
  rw [show 304 = 303 + 1 by norm_num, squarefreeCountNat_succ, count_303]
  norm_num [mu_304]

private theorem cell_304 :
    endpointOK (squarefreeCountNat 304) 304 ∧
      endpointOK (squarefreeCountNat 304) (304 + 1) := by
  rw [count_304]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_305 : μ 305 = 1 := by
  rw [show 305 = 5 * 61 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 61)]
  norm_num

private theorem count_305 : squarefreeCountNat 305 = 187 := by
  rw [show 305 = 304 + 1 by norm_num, squarefreeCountNat_succ, count_304]
  norm_num [mu_305]

private theorem cell_305 :
    endpointOK (squarefreeCountNat 305) 305 ∧
      endpointOK (squarefreeCountNat 305) (305 + 1) := by
  rw [count_305]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_306 : μ 306 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_306 : squarefreeCountNat 306 = 187 := by
  rw [show 306 = 305 + 1 by norm_num, squarefreeCountNat_succ, count_305]
  norm_num [mu_306]

private theorem cell_306 :
    endpointOK (squarefreeCountNat 306) 306 ∧
      endpointOK (squarefreeCountNat 306) (306 + 1) := by
  rw [count_306]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_307 : μ 307 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_307 : squarefreeCountNat 307 = 188 := by
  rw [show 307 = 306 + 1 by norm_num, squarefreeCountNat_succ, count_306]
  norm_num [mu_307]

private theorem cell_307 :
    endpointOK (squarefreeCountNat 307) 307 ∧
      endpointOK (squarefreeCountNat 307) (307 + 1) := by
  rw [count_307]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_308 : μ 308 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_308 : squarefreeCountNat 308 = 188 := by
  rw [show 308 = 307 + 1 by norm_num, squarefreeCountNat_succ, count_307]
  norm_num [mu_308]

private theorem cell_308 :
    endpointOK (squarefreeCountNat 308) 308 ∧
      endpointOK (squarefreeCountNat 308) (308 + 1) := by
  rw [count_308]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_309 : μ 309 = 1 := by
  rw [show 309 = 3 * 103 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 103)]
  norm_num

private theorem count_309 : squarefreeCountNat 309 = 189 := by
  rw [show 309 = 308 + 1 by norm_num, squarefreeCountNat_succ, count_308]
  norm_num [mu_309]

private theorem cell_309 :
    endpointOK (squarefreeCountNat 309) 309 ∧
      endpointOK (squarefreeCountNat 309) (309 + 1) := by
  rw [count_309]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_310 : μ 310 = -1 := by
  rw [show 310 = 2 * 155 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 155 = 5 * 31 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 31)]
  norm_num

private theorem count_310 : squarefreeCountNat 310 = 190 := by
  rw [show 310 = 309 + 1 by norm_num, squarefreeCountNat_succ, count_309]
  norm_num [mu_310]

private theorem cell_310 :
    endpointOK (squarefreeCountNat 310) 310 ∧
      endpointOK (squarefreeCountNat 310) (310 + 1) := by
  rw [count_310]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_311 : μ 311 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_311 : squarefreeCountNat 311 = 191 := by
  rw [show 311 = 310 + 1 by norm_num, squarefreeCountNat_succ, count_310]
  norm_num [mu_311]

private theorem cell_311 :
    endpointOK (squarefreeCountNat 311) 311 ∧
      endpointOK (squarefreeCountNat 311) (311 + 1) := by
  rw [count_311]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_312 : μ 312 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_312 : squarefreeCountNat 312 = 191 := by
  rw [show 312 = 311 + 1 by norm_num, squarefreeCountNat_succ, count_311]
  norm_num [mu_312]

private theorem cell_312 :
    endpointOK (squarefreeCountNat 312) 312 ∧
      endpointOK (squarefreeCountNat 312) (312 + 1) := by
  rw [count_312]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_313 : μ 313 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_313 : squarefreeCountNat 313 = 192 := by
  rw [show 313 = 312 + 1 by norm_num, squarefreeCountNat_succ, count_312]
  norm_num [mu_313]

private theorem cell_313 :
    endpointOK (squarefreeCountNat 313) 313 ∧
      endpointOK (squarefreeCountNat 313) (313 + 1) := by
  rw [count_313]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_314 : μ 314 = 1 := by
  rw [show 314 = 2 * 157 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 157)]
  norm_num

private theorem count_314 : squarefreeCountNat 314 = 193 := by
  rw [show 314 = 313 + 1 by norm_num, squarefreeCountNat_succ, count_313]
  norm_num [mu_314]

private theorem cell_314 :
    endpointOK (squarefreeCountNat 314) 314 ∧
      endpointOK (squarefreeCountNat 314) (314 + 1) := by
  rw [count_314]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_315 : μ 315 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_315 : squarefreeCountNat 315 = 193 := by
  rw [show 315 = 314 + 1 by norm_num, squarefreeCountNat_succ, count_314]
  norm_num [mu_315]

private theorem cell_315 :
    endpointOK (squarefreeCountNat 315) 315 ∧
      endpointOK (squarefreeCountNat 315) (315 + 1) := by
  rw [count_315]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_316 : μ 316 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_316 : squarefreeCountNat 316 = 193 := by
  rw [show 316 = 315 + 1 by norm_num, squarefreeCountNat_succ, count_315]
  norm_num [mu_316]

private theorem cell_316 :
    endpointOK (squarefreeCountNat 316) 316 ∧
      endpointOK (squarefreeCountNat 316) (316 + 1) := by
  rw [count_316]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_317 : μ 317 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_317 : squarefreeCountNat 317 = 194 := by
  rw [show 317 = 316 + 1 by norm_num, squarefreeCountNat_succ, count_316]
  norm_num [mu_317]

private theorem cell_317 :
    endpointOK (squarefreeCountNat 317) 317 ∧
      endpointOK (squarefreeCountNat 317) (317 + 1) := by
  rw [count_317]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_318 : μ 318 = -1 := by
  rw [show 318 = 2 * 159 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 159 = 3 * 53 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 53)]
  norm_num

private theorem count_318 : squarefreeCountNat 318 = 195 := by
  rw [show 318 = 317 + 1 by norm_num, squarefreeCountNat_succ, count_317]
  norm_num [mu_318]

private theorem cell_318 :
    endpointOK (squarefreeCountNat 318) 318 ∧
      endpointOK (squarefreeCountNat 318) (318 + 1) := by
  rw [count_318]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_319 : μ 319 = 1 := by
  rw [show 319 = 11 * 29 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 29)]
  norm_num

private theorem count_319 : squarefreeCountNat 319 = 196 := by
  rw [show 319 = 318 + 1 by norm_num, squarefreeCountNat_succ, count_318]
  norm_num [mu_319]

private theorem cell_319 :
    endpointOK (squarefreeCountNat 319) 319 ∧
      endpointOK (squarefreeCountNat 319) (319 + 1) := by
  rw [count_319]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_320 : μ 320 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_320 : squarefreeCountNat 320 = 196 := by
  rw [show 320 = 319 + 1 by norm_num, squarefreeCountNat_succ, count_319]
  norm_num [mu_320]

private theorem cell_320 :
    endpointOK (squarefreeCountNat 320) 320 ∧
      endpointOK (squarefreeCountNat 320) (320 + 1) := by
  rw [count_320]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_321 : μ 321 = 1 := by
  rw [show 321 = 3 * 107 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 107)]
  norm_num

private theorem count_321 : squarefreeCountNat 321 = 197 := by
  rw [show 321 = 320 + 1 by norm_num, squarefreeCountNat_succ, count_320]
  norm_num [mu_321]

private theorem cell_321 :
    endpointOK (squarefreeCountNat 321) 321 ∧
      endpointOK (squarefreeCountNat 321) (321 + 1) := by
  rw [count_321]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_322 : μ 322 = -1 := by
  rw [show 322 = 2 * 161 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 161 = 7 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_322 : squarefreeCountNat 322 = 198 := by
  rw [show 322 = 321 + 1 by norm_num, squarefreeCountNat_succ, count_321]
  norm_num [mu_322]

private theorem cell_322 :
    endpointOK (squarefreeCountNat 322) 322 ∧
      endpointOK (squarefreeCountNat 322) (322 + 1) := by
  rw [count_322]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_323 : μ 323 = 1 := by
  rw [show 323 = 17 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_323 : squarefreeCountNat 323 = 199 := by
  rw [show 323 = 322 + 1 by norm_num, squarefreeCountNat_succ, count_322]
  norm_num [mu_323]

private theorem cell_323 :
    endpointOK (squarefreeCountNat 323) 323 ∧
      endpointOK (squarefreeCountNat 323) (323 + 1) := by
  rw [count_323]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_324 : μ 324 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_324 : squarefreeCountNat 324 = 199 := by
  rw [show 324 = 323 + 1 by norm_num, squarefreeCountNat_succ, count_323]
  norm_num [mu_324]

private theorem cell_324 :
    endpointOK (squarefreeCountNat 324) 324 ∧
      endpointOK (squarefreeCountNat 324) (324 + 1) := by
  rw [count_324]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_325 : μ 325 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

private theorem count_325 : squarefreeCountNat 325 = 199 := by
  rw [show 325 = 324 + 1 by norm_num, squarefreeCountNat_succ, count_324]
  norm_num [mu_325]

private theorem cell_325 :
    endpointOK (squarefreeCountNat 325) 325 ∧
      endpointOK (squarefreeCountNat 325) (325 + 1) := by
  rw [count_325]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_326 : μ 326 = 1 := by
  rw [show 326 = 2 * 163 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 163)]
  norm_num

private theorem count_326 : squarefreeCountNat 326 = 200 := by
  rw [show 326 = 325 + 1 by norm_num, squarefreeCountNat_succ, count_325]
  norm_num [mu_326]

private theorem cell_326 :
    endpointOK (squarefreeCountNat 326) 326 ∧
      endpointOK (squarefreeCountNat 326) (326 + 1) := by
  rw [count_326]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_327 : μ 327 = 1 := by
  rw [show 327 = 3 * 109 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 109)]
  norm_num

private theorem count_327 : squarefreeCountNat 327 = 201 := by
  rw [show 327 = 326 + 1 by norm_num, squarefreeCountNat_succ, count_326]
  norm_num [mu_327]

private theorem cell_327 :
    endpointOK (squarefreeCountNat 327) 327 ∧
      endpointOK (squarefreeCountNat 327) (327 + 1) := by
  rw [count_327]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_328 : μ 328 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_328 : squarefreeCountNat 328 = 201 := by
  rw [show 328 = 327 + 1 by norm_num, squarefreeCountNat_succ, count_327]
  norm_num [mu_328]

private theorem cell_328 :
    endpointOK (squarefreeCountNat 328) 328 ∧
      endpointOK (squarefreeCountNat 328) (328 + 1) := by
  rw [count_328]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_329 : μ 329 = 1 := by
  rw [show 329 = 7 * 47 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 47)]
  norm_num

private theorem count_329 : squarefreeCountNat 329 = 202 := by
  rw [show 329 = 328 + 1 by norm_num, squarefreeCountNat_succ, count_328]
  norm_num [mu_329]

private theorem cell_329 :
    endpointOK (squarefreeCountNat 329) 329 ∧
      endpointOK (squarefreeCountNat 329) (329 + 1) := by
  rw [count_329]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_330 : μ 330 = 1 := by
  rw [show 330 = 2 * 165 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 165 = 3 * 55 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 55 = 5 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_330 : squarefreeCountNat 330 = 203 := by
  rw [show 330 = 329 + 1 by norm_num, squarefreeCountNat_succ, count_329]
  norm_num [mu_330]

private theorem cell_330 :
    endpointOK (squarefreeCountNat 330) 330 ∧
      endpointOK (squarefreeCountNat 330) (330 + 1) := by
  rw [count_330]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_331 : μ 331 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_331 : squarefreeCountNat 331 = 204 := by
  rw [show 331 = 330 + 1 by norm_num, squarefreeCountNat_succ, count_330]
  norm_num [mu_331]

private theorem cell_331 :
    endpointOK (squarefreeCountNat 331) 331 ∧
      endpointOK (squarefreeCountNat 331) (331 + 1) := by
  rw [count_331]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_332 : μ 332 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_332 : squarefreeCountNat 332 = 204 := by
  rw [show 332 = 331 + 1 by norm_num, squarefreeCountNat_succ, count_331]
  norm_num [mu_332]

private theorem cell_332 :
    endpointOK (squarefreeCountNat 332) 332 ∧
      endpointOK (squarefreeCountNat 332) (332 + 1) := by
  rw [count_332]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_333 : μ 333 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_333 : squarefreeCountNat 333 = 204 := by
  rw [show 333 = 332 + 1 by norm_num, squarefreeCountNat_succ, count_332]
  norm_num [mu_333]

private theorem cell_333 :
    endpointOK (squarefreeCountNat 333) 333 ∧
      endpointOK (squarefreeCountNat 333) (333 + 1) := by
  rw [count_333]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_334 : μ 334 = 1 := by
  rw [show 334 = 2 * 167 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 167)]
  norm_num

private theorem count_334 : squarefreeCountNat 334 = 205 := by
  rw [show 334 = 333 + 1 by norm_num, squarefreeCountNat_succ, count_333]
  norm_num [mu_334]

private theorem cell_334 :
    endpointOK (squarefreeCountNat 334) 334 ∧
      endpointOK (squarefreeCountNat 334) (334 + 1) := by
  rw [count_334]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_335 : μ 335 = 1 := by
  rw [show 335 = 5 * 67 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 67)]
  norm_num

private theorem count_335 : squarefreeCountNat 335 = 206 := by
  rw [show 335 = 334 + 1 by norm_num, squarefreeCountNat_succ, count_334]
  norm_num [mu_335]

private theorem cell_335 :
    endpointOK (squarefreeCountNat 335) 335 ∧
      endpointOK (squarefreeCountNat 335) (335 + 1) := by
  rw [count_335]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_336 : μ 336 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_336 : squarefreeCountNat 336 = 206 := by
  rw [show 336 = 335 + 1 by norm_num, squarefreeCountNat_succ, count_335]
  norm_num [mu_336]

private theorem cell_336 :
    endpointOK (squarefreeCountNat 336) 336 ∧
      endpointOK (squarefreeCountNat 336) (336 + 1) := by
  rw [count_336]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_337 : μ 337 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_337 : squarefreeCountNat 337 = 207 := by
  rw [show 337 = 336 + 1 by norm_num, squarefreeCountNat_succ, count_336]
  norm_num [mu_337]

private theorem cell_337 :
    endpointOK (squarefreeCountNat 337) 337 ∧
      endpointOK (squarefreeCountNat 337) (337 + 1) := by
  rw [count_337]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_338 : μ 338 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 13 (by norm_num) (by norm_num)

private theorem count_338 : squarefreeCountNat 338 = 207 := by
  rw [show 338 = 337 + 1 by norm_num, squarefreeCountNat_succ, count_337]
  norm_num [mu_338]

private theorem cell_338 :
    endpointOK (squarefreeCountNat 338) 338 ∧
      endpointOK (squarefreeCountNat 338) (338 + 1) := by
  rw [count_338]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_339 : μ 339 = 1 := by
  rw [show 339 = 3 * 113 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 113)]
  norm_num

private theorem count_339 : squarefreeCountNat 339 = 208 := by
  rw [show 339 = 338 + 1 by norm_num, squarefreeCountNat_succ, count_338]
  norm_num [mu_339]

private theorem cell_339 :
    endpointOK (squarefreeCountNat 339) 339 ∧
      endpointOK (squarefreeCountNat 339) (339 + 1) := by
  rw [count_339]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_340 : μ 340 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_340 : squarefreeCountNat 340 = 208 := by
  rw [show 340 = 339 + 1 by norm_num, squarefreeCountNat_succ, count_339]
  norm_num [mu_340]

private theorem cell_340 :
    endpointOK (squarefreeCountNat 340) 340 ∧
      endpointOK (squarefreeCountNat 340) (340 + 1) := by
  rw [count_340]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_341 : μ 341 = 1 := by
  rw [show 341 = 11 * 31 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 31)]
  norm_num

private theorem count_341 : squarefreeCountNat 341 = 209 := by
  rw [show 341 = 340 + 1 by norm_num, squarefreeCountNat_succ, count_340]
  norm_num [mu_341]

private theorem cell_341 :
    endpointOK (squarefreeCountNat 341) 341 ∧
      endpointOK (squarefreeCountNat 341) (341 + 1) := by
  rw [count_341]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_342 : μ 342 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_342 : squarefreeCountNat 342 = 209 := by
  rw [show 342 = 341 + 1 by norm_num, squarefreeCountNat_succ, count_341]
  norm_num [mu_342]

private theorem cell_342 :
    endpointOK (squarefreeCountNat 342) 342 ∧
      endpointOK (squarefreeCountNat 342) (342 + 1) := by
  rw [count_342]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_343 : μ 343 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 7 (by norm_num) (by norm_num)

private theorem count_343 : squarefreeCountNat 343 = 209 := by
  rw [show 343 = 342 + 1 by norm_num, squarefreeCountNat_succ, count_342]
  norm_num [mu_343]

private theorem cell_343 :
    endpointOK (squarefreeCountNat 343) 343 ∧
      endpointOK (squarefreeCountNat 343) (343 + 1) := by
  rw [count_343]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_344 : μ 344 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_344 : squarefreeCountNat 344 = 209 := by
  rw [show 344 = 343 + 1 by norm_num, squarefreeCountNat_succ, count_343]
  norm_num [mu_344]

private theorem cell_344 :
    endpointOK (squarefreeCountNat 344) 344 ∧
      endpointOK (squarefreeCountNat 344) (344 + 1) := by
  rw [count_344]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_345 : μ 345 = -1 := by
  rw [show 345 = 3 * 115 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 115 = 5 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_345 : squarefreeCountNat 345 = 210 := by
  rw [show 345 = 344 + 1 by norm_num, squarefreeCountNat_succ, count_344]
  norm_num [mu_345]

private theorem cell_345 :
    endpointOK (squarefreeCountNat 345) 345 ∧
      endpointOK (squarefreeCountNat 345) (345 + 1) := by
  rw [count_345]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_346 : μ 346 = 1 := by
  rw [show 346 = 2 * 173 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 173)]
  norm_num

private theorem count_346 : squarefreeCountNat 346 = 211 := by
  rw [show 346 = 345 + 1 by norm_num, squarefreeCountNat_succ, count_345]
  norm_num [mu_346]

private theorem cell_346 :
    endpointOK (squarefreeCountNat 346) 346 ∧
      endpointOK (squarefreeCountNat 346) (346 + 1) := by
  rw [count_346]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_347 : μ 347 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_347 : squarefreeCountNat 347 = 212 := by
  rw [show 347 = 346 + 1 by norm_num, squarefreeCountNat_succ, count_346]
  norm_num [mu_347]

private theorem cell_347 :
    endpointOK (squarefreeCountNat 347) 347 ∧
      endpointOK (squarefreeCountNat 347) (347 + 1) := by
  rw [count_347]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_348 : μ 348 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_348 : squarefreeCountNat 348 = 212 := by
  rw [show 348 = 347 + 1 by norm_num, squarefreeCountNat_succ, count_347]
  norm_num [mu_348]

private theorem cell_348 :
    endpointOK (squarefreeCountNat 348) 348 ∧
      endpointOK (squarefreeCountNat 348) (348 + 1) := by
  rw [count_348]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_349 : μ 349 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_349 : squarefreeCountNat 349 = 213 := by
  rw [show 349 = 348 + 1 by norm_num, squarefreeCountNat_succ, count_348]
  norm_num [mu_349]

private theorem cell_349 :
    endpointOK (squarefreeCountNat 349) 349 ∧
      endpointOK (squarefreeCountNat 349) (349 + 1) := by
  rw [count_349]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_350 : μ 350 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

theorem count_350 : squarefreeCountNat 350 = 213 := by
  rw [show 350 = 349 + 1 by norm_num, squarefreeCountNat_succ, count_349]
  norm_num [mu_350]

private theorem cell_350 :
    endpointOK (squarefreeCountNat 350) 350 ∧
      endpointOK (squarefreeCountNat 350) (350 + 1) := by
  rw [count_350]
  norm_num [endpointOK, densityLower, densityUpper]

theorem finite_endpoint_certificate_301_350 (N : ℕ)
    (hlo : 301 ≤ N) (hhi : N ≤ 350) :
    endpointOK (squarefreeCountNat N) N ∧
      endpointOK (squarefreeCountNat N) (N + 1) := by
  interval_cases N
  · exact cell_301
  · exact cell_302
  · exact cell_303
  · exact cell_304
  · exact cell_305
  · exact cell_306
  · exact cell_307
  · exact cell_308
  · exact cell_309
  · exact cell_310
  · exact cell_311
  · exact cell_312
  · exact cell_313
  · exact cell_314
  · exact cell_315
  · exact cell_316
  · exact cell_317
  · exact cell_318
  · exact cell_319
  · exact cell_320
  · exact cell_321
  · exact cell_322
  · exact cell_323
  · exact cell_324
  · exact cell_325
  · exact cell_326
  · exact cell_327
  · exact cell_328
  · exact cell_329
  · exact cell_330
  · exact cell_331
  · exact cell_332
  · exact cell_333
  · exact cell_334
  · exact cell_335
  · exact cell_336
  · exact cell_337
  · exact cell_338
  · exact cell_339
  · exact cell_340
  · exact cell_341
  · exact cell_342
  · exact cell_343
  · exact cell_344
  · exact cell_345
  · exact cell_346
  · exact cell_347
  · exact cell_348
  · exact cell_349
  · exact cell_350

end MoserMacLeod
