import MoserMacLeod.TableRows301_350

/-!
# Proof-producing finite rows 351--400

This generated shard proves the required Möbius values, updates the squarefree
prefix count one integer at a time, and checks the two exact rational endpoint
inequalities in each real cell.  It uses no native evaluator.
-/

namespace MoserMacLeod

open scoped ArithmeticFunction.Moebius BigOperators
open Finset

private theorem mu_351 : μ 351 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_351 : squarefreeCountNat 351 = 213 := by
  rw [show 351 = 350 + 1 by norm_num, squarefreeCountNat_succ, count_350]
  norm_num [mu_351]

private theorem cell_351 :
    endpointOK (squarefreeCountNat 351) 351 ∧
      endpointOK (squarefreeCountNat 351) (351 + 1) := by
  rw [count_351]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_352 : μ 352 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_352 : squarefreeCountNat 352 = 213 := by
  rw [show 352 = 351 + 1 by norm_num, squarefreeCountNat_succ, count_351]
  norm_num [mu_352]

private theorem cell_352 :
    endpointOK (squarefreeCountNat 352) 352 ∧
      endpointOK (squarefreeCountNat 352) (352 + 1) := by
  rw [count_352]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_353 : μ 353 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_353 : squarefreeCountNat 353 = 214 := by
  rw [show 353 = 352 + 1 by norm_num, squarefreeCountNat_succ, count_352]
  norm_num [mu_353]

private theorem cell_353 :
    endpointOK (squarefreeCountNat 353) 353 ∧
      endpointOK (squarefreeCountNat 353) (353 + 1) := by
  rw [count_353]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_354 : μ 354 = -1 := by
  rw [show 354 = 2 * 177 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 177 = 3 * 59 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 59)]
  norm_num

private theorem count_354 : squarefreeCountNat 354 = 215 := by
  rw [show 354 = 353 + 1 by norm_num, squarefreeCountNat_succ, count_353]
  norm_num [mu_354]

private theorem cell_354 :
    endpointOK (squarefreeCountNat 354) 354 ∧
      endpointOK (squarefreeCountNat 354) (354 + 1) := by
  rw [count_354]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_355 : μ 355 = 1 := by
  rw [show 355 = 5 * 71 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 71)]
  norm_num

private theorem count_355 : squarefreeCountNat 355 = 216 := by
  rw [show 355 = 354 + 1 by norm_num, squarefreeCountNat_succ, count_354]
  norm_num [mu_355]

private theorem cell_355 :
    endpointOK (squarefreeCountNat 355) 355 ∧
      endpointOK (squarefreeCountNat 355) (355 + 1) := by
  rw [count_355]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_356 : μ 356 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_356 : squarefreeCountNat 356 = 216 := by
  rw [show 356 = 355 + 1 by norm_num, squarefreeCountNat_succ, count_355]
  norm_num [mu_356]

private theorem cell_356 :
    endpointOK (squarefreeCountNat 356) 356 ∧
      endpointOK (squarefreeCountNat 356) (356 + 1) := by
  rw [count_356]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_357 : μ 357 = -1 := by
  rw [show 357 = 3 * 119 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 119 = 7 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_357 : squarefreeCountNat 357 = 217 := by
  rw [show 357 = 356 + 1 by norm_num, squarefreeCountNat_succ, count_356]
  norm_num [mu_357]

private theorem cell_357 :
    endpointOK (squarefreeCountNat 357) 357 ∧
      endpointOK (squarefreeCountNat 357) (357 + 1) := by
  rw [count_357]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_358 : μ 358 = 1 := by
  rw [show 358 = 2 * 179 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 179)]
  norm_num

private theorem count_358 : squarefreeCountNat 358 = 218 := by
  rw [show 358 = 357 + 1 by norm_num, squarefreeCountNat_succ, count_357]
  norm_num [mu_358]

private theorem cell_358 :
    endpointOK (squarefreeCountNat 358) 358 ∧
      endpointOK (squarefreeCountNat 358) (358 + 1) := by
  rw [count_358]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_359 : μ 359 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_359 : squarefreeCountNat 359 = 219 := by
  rw [show 359 = 358 + 1 by norm_num, squarefreeCountNat_succ, count_358]
  norm_num [mu_359]

private theorem cell_359 :
    endpointOK (squarefreeCountNat 359) 359 ∧
      endpointOK (squarefreeCountNat 359) (359 + 1) := by
  rw [count_359]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_360 : μ 360 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_360 : squarefreeCountNat 360 = 219 := by
  rw [show 360 = 359 + 1 by norm_num, squarefreeCountNat_succ, count_359]
  norm_num [mu_360]

private theorem cell_360 :
    endpointOK (squarefreeCountNat 360) 360 ∧
      endpointOK (squarefreeCountNat 360) (360 + 1) := by
  rw [count_360]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_361 : μ 361 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 19 (by norm_num) (by norm_num)

private theorem count_361 : squarefreeCountNat 361 = 219 := by
  rw [show 361 = 360 + 1 by norm_num, squarefreeCountNat_succ, count_360]
  norm_num [mu_361]

private theorem cell_361 :
    endpointOK (squarefreeCountNat 361) 361 ∧
      endpointOK (squarefreeCountNat 361) (361 + 1) := by
  rw [count_361]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_362 : μ 362 = 1 := by
  rw [show 362 = 2 * 181 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 181)]
  norm_num

private theorem count_362 : squarefreeCountNat 362 = 220 := by
  rw [show 362 = 361 + 1 by norm_num, squarefreeCountNat_succ, count_361]
  norm_num [mu_362]

private theorem cell_362 :
    endpointOK (squarefreeCountNat 362) 362 ∧
      endpointOK (squarefreeCountNat 362) (362 + 1) := by
  rw [count_362]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_363 : μ 363 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 11 (by norm_num) (by norm_num)

private theorem count_363 : squarefreeCountNat 363 = 220 := by
  rw [show 363 = 362 + 1 by norm_num, squarefreeCountNat_succ, count_362]
  norm_num [mu_363]

private theorem cell_363 :
    endpointOK (squarefreeCountNat 363) 363 ∧
      endpointOK (squarefreeCountNat 363) (363 + 1) := by
  rw [count_363]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_364 : μ 364 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_364 : squarefreeCountNat 364 = 220 := by
  rw [show 364 = 363 + 1 by norm_num, squarefreeCountNat_succ, count_363]
  norm_num [mu_364]

private theorem cell_364 :
    endpointOK (squarefreeCountNat 364) 364 ∧
      endpointOK (squarefreeCountNat 364) (364 + 1) := by
  rw [count_364]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_365 : μ 365 = 1 := by
  rw [show 365 = 5 * 73 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 73)]
  norm_num

private theorem count_365 : squarefreeCountNat 365 = 221 := by
  rw [show 365 = 364 + 1 by norm_num, squarefreeCountNat_succ, count_364]
  norm_num [mu_365]

private theorem cell_365 :
    endpointOK (squarefreeCountNat 365) 365 ∧
      endpointOK (squarefreeCountNat 365) (365 + 1) := by
  rw [count_365]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_366 : μ 366 = -1 := by
  rw [show 366 = 2 * 183 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 183 = 3 * 61 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 61)]
  norm_num

private theorem count_366 : squarefreeCountNat 366 = 222 := by
  rw [show 366 = 365 + 1 by norm_num, squarefreeCountNat_succ, count_365]
  norm_num [mu_366]

private theorem cell_366 :
    endpointOK (squarefreeCountNat 366) 366 ∧
      endpointOK (squarefreeCountNat 366) (366 + 1) := by
  rw [count_366]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_367 : μ 367 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_367 : squarefreeCountNat 367 = 223 := by
  rw [show 367 = 366 + 1 by norm_num, squarefreeCountNat_succ, count_366]
  norm_num [mu_367]

private theorem cell_367 :
    endpointOK (squarefreeCountNat 367) 367 ∧
      endpointOK (squarefreeCountNat 367) (367 + 1) := by
  rw [count_367]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_368 : μ 368 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_368 : squarefreeCountNat 368 = 223 := by
  rw [show 368 = 367 + 1 by norm_num, squarefreeCountNat_succ, count_367]
  norm_num [mu_368]

private theorem cell_368 :
    endpointOK (squarefreeCountNat 368) 368 ∧
      endpointOK (squarefreeCountNat 368) (368 + 1) := by
  rw [count_368]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_369 : μ 369 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_369 : squarefreeCountNat 369 = 223 := by
  rw [show 369 = 368 + 1 by norm_num, squarefreeCountNat_succ, count_368]
  norm_num [mu_369]

private theorem cell_369 :
    endpointOK (squarefreeCountNat 369) 369 ∧
      endpointOK (squarefreeCountNat 369) (369 + 1) := by
  rw [count_369]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_370 : μ 370 = -1 := by
  rw [show 370 = 2 * 185 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 185 = 5 * 37 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 37)]
  norm_num

private theorem count_370 : squarefreeCountNat 370 = 224 := by
  rw [show 370 = 369 + 1 by norm_num, squarefreeCountNat_succ, count_369]
  norm_num [mu_370]

private theorem cell_370 :
    endpointOK (squarefreeCountNat 370) 370 ∧
      endpointOK (squarefreeCountNat 370) (370 + 1) := by
  rw [count_370]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_371 : μ 371 = 1 := by
  rw [show 371 = 7 * 53 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 53)]
  norm_num

private theorem count_371 : squarefreeCountNat 371 = 225 := by
  rw [show 371 = 370 + 1 by norm_num, squarefreeCountNat_succ, count_370]
  norm_num [mu_371]

private theorem cell_371 :
    endpointOK (squarefreeCountNat 371) 371 ∧
      endpointOK (squarefreeCountNat 371) (371 + 1) := by
  rw [count_371]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_372 : μ 372 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_372 : squarefreeCountNat 372 = 225 := by
  rw [show 372 = 371 + 1 by norm_num, squarefreeCountNat_succ, count_371]
  norm_num [mu_372]

private theorem cell_372 :
    endpointOK (squarefreeCountNat 372) 372 ∧
      endpointOK (squarefreeCountNat 372) (372 + 1) := by
  rw [count_372]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_373 : μ 373 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_373 : squarefreeCountNat 373 = 226 := by
  rw [show 373 = 372 + 1 by norm_num, squarefreeCountNat_succ, count_372]
  norm_num [mu_373]

private theorem cell_373 :
    endpointOK (squarefreeCountNat 373) 373 ∧
      endpointOK (squarefreeCountNat 373) (373 + 1) := by
  rw [count_373]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_374 : μ 374 = -1 := by
  rw [show 374 = 2 * 187 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 187 = 11 * 17 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17)]
  norm_num

private theorem count_374 : squarefreeCountNat 374 = 227 := by
  rw [show 374 = 373 + 1 by norm_num, squarefreeCountNat_succ, count_373]
  norm_num [mu_374]

private theorem cell_374 :
    endpointOK (squarefreeCountNat 374) 374 ∧
      endpointOK (squarefreeCountNat 374) (374 + 1) := by
  rw [count_374]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_375 : μ 375 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 5 (by norm_num) (by norm_num)

private theorem count_375 : squarefreeCountNat 375 = 227 := by
  rw [show 375 = 374 + 1 by norm_num, squarefreeCountNat_succ, count_374]
  norm_num [mu_375]

private theorem cell_375 :
    endpointOK (squarefreeCountNat 375) 375 ∧
      endpointOK (squarefreeCountNat 375) (375 + 1) := by
  rw [count_375]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_376 : μ 376 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_376 : squarefreeCountNat 376 = 227 := by
  rw [show 376 = 375 + 1 by norm_num, squarefreeCountNat_succ, count_375]
  norm_num [mu_376]

private theorem cell_376 :
    endpointOK (squarefreeCountNat 376) 376 ∧
      endpointOK (squarefreeCountNat 376) (376 + 1) := by
  rw [count_376]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_377 : μ 377 = 1 := by
  rw [show 377 = 13 * 29 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 29)]
  norm_num

private theorem count_377 : squarefreeCountNat 377 = 228 := by
  rw [show 377 = 376 + 1 by norm_num, squarefreeCountNat_succ, count_376]
  norm_num [mu_377]

private theorem cell_377 :
    endpointOK (squarefreeCountNat 377) 377 ∧
      endpointOK (squarefreeCountNat 377) (377 + 1) := by
  rw [count_377]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_378 : μ 378 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_378 : squarefreeCountNat 378 = 228 := by
  rw [show 378 = 377 + 1 by norm_num, squarefreeCountNat_succ, count_377]
  norm_num [mu_378]

private theorem cell_378 :
    endpointOK (squarefreeCountNat 378) 378 ∧
      endpointOK (squarefreeCountNat 378) (378 + 1) := by
  rw [count_378]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_379 : μ 379 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_379 : squarefreeCountNat 379 = 229 := by
  rw [show 379 = 378 + 1 by norm_num, squarefreeCountNat_succ, count_378]
  norm_num [mu_379]

private theorem cell_379 :
    endpointOK (squarefreeCountNat 379) 379 ∧
      endpointOK (squarefreeCountNat 379) (379 + 1) := by
  rw [count_379]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_380 : μ 380 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_380 : squarefreeCountNat 380 = 229 := by
  rw [show 380 = 379 + 1 by norm_num, squarefreeCountNat_succ, count_379]
  norm_num [mu_380]

private theorem cell_380 :
    endpointOK (squarefreeCountNat 380) 380 ∧
      endpointOK (squarefreeCountNat 380) (380 + 1) := by
  rw [count_380]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_381 : μ 381 = 1 := by
  rw [show 381 = 3 * 127 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 127)]
  norm_num

private theorem count_381 : squarefreeCountNat 381 = 230 := by
  rw [show 381 = 380 + 1 by norm_num, squarefreeCountNat_succ, count_380]
  norm_num [mu_381]

private theorem cell_381 :
    endpointOK (squarefreeCountNat 381) 381 ∧
      endpointOK (squarefreeCountNat 381) (381 + 1) := by
  rw [count_381]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_382 : μ 382 = 1 := by
  rw [show 382 = 2 * 191 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 191)]
  norm_num

private theorem count_382 : squarefreeCountNat 382 = 231 := by
  rw [show 382 = 381 + 1 by norm_num, squarefreeCountNat_succ, count_381]
  norm_num [mu_382]

private theorem cell_382 :
    endpointOK (squarefreeCountNat 382) 382 ∧
      endpointOK (squarefreeCountNat 382) (382 + 1) := by
  rw [count_382]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_383 : μ 383 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_383 : squarefreeCountNat 383 = 232 := by
  rw [show 383 = 382 + 1 by norm_num, squarefreeCountNat_succ, count_382]
  norm_num [mu_383]

private theorem cell_383 :
    endpointOK (squarefreeCountNat 383) 383 ∧
      endpointOK (squarefreeCountNat 383) (383 + 1) := by
  rw [count_383]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_384 : μ 384 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_384 : squarefreeCountNat 384 = 232 := by
  rw [show 384 = 383 + 1 by norm_num, squarefreeCountNat_succ, count_383]
  norm_num [mu_384]

private theorem cell_384 :
    endpointOK (squarefreeCountNat 384) 384 ∧
      endpointOK (squarefreeCountNat 384) (384 + 1) := by
  rw [count_384]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_385 : μ 385 = -1 := by
  rw [show 385 = 5 * 77 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    show 77 = 7 * 11 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 11)]
  norm_num

private theorem count_385 : squarefreeCountNat 385 = 233 := by
  rw [show 385 = 384 + 1 by norm_num, squarefreeCountNat_succ, count_384]
  norm_num [mu_385]

private theorem cell_385 :
    endpointOK (squarefreeCountNat 385) 385 ∧
      endpointOK (squarefreeCountNat 385) (385 + 1) := by
  rw [count_385]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_386 : μ 386 = 1 := by
  rw [show 386 = 2 * 193 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 193)]
  norm_num

private theorem count_386 : squarefreeCountNat 386 = 234 := by
  rw [show 386 = 385 + 1 by norm_num, squarefreeCountNat_succ, count_385]
  norm_num [mu_386]

private theorem cell_386 :
    endpointOK (squarefreeCountNat 386) 386 ∧
      endpointOK (squarefreeCountNat 386) (386 + 1) := by
  rw [count_386]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_387 : μ 387 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 3 (by norm_num) (by norm_num)

private theorem count_387 : squarefreeCountNat 387 = 234 := by
  rw [show 387 = 386 + 1 by norm_num, squarefreeCountNat_succ, count_386]
  norm_num [mu_387]

private theorem cell_387 :
    endpointOK (squarefreeCountNat 387) 387 ∧
      endpointOK (squarefreeCountNat 387) (387 + 1) := by
  rw [count_387]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_388 : μ 388 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_388 : squarefreeCountNat 388 = 234 := by
  rw [show 388 = 387 + 1 by norm_num, squarefreeCountNat_succ, count_387]
  norm_num [mu_388]

private theorem cell_388 :
    endpointOK (squarefreeCountNat 388) 388 ∧
      endpointOK (squarefreeCountNat 388) (388 + 1) := by
  rw [count_388]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_389 : μ 389 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_389 : squarefreeCountNat 389 = 235 := by
  rw [show 389 = 388 + 1 by norm_num, squarefreeCountNat_succ, count_388]
  norm_num [mu_389]

private theorem cell_389 :
    endpointOK (squarefreeCountNat 389) 389 ∧
      endpointOK (squarefreeCountNat 389) (389 + 1) := by
  rw [count_389]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_390 : μ 390 = 1 := by
  rw [show 390 = 2 * 195 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    show 195 = 3 * 65 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 65 = 5 * 13 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 13)]
  norm_num

private theorem count_390 : squarefreeCountNat 390 = 236 := by
  rw [show 390 = 389 + 1 by norm_num, squarefreeCountNat_succ, count_389]
  norm_num [mu_390]

private theorem cell_390 :
    endpointOK (squarefreeCountNat 390) 390 ∧
      endpointOK (squarefreeCountNat 390) (390 + 1) := by
  rw [count_390]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_391 : μ 391 = 1 := by
  rw [show 391 = 17 * 23 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 17),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 23)]
  norm_num

private theorem count_391 : squarefreeCountNat 391 = 237 := by
  rw [show 391 = 390 + 1 by norm_num, squarefreeCountNat_succ, count_390]
  norm_num [mu_391]

private theorem cell_391 :
    endpointOK (squarefreeCountNat 391) 391 ∧
      endpointOK (squarefreeCountNat 391) (391 + 1) := by
  rw [count_391]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_392 : μ 392 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_392 : squarefreeCountNat 392 = 237 := by
  rw [show 392 = 391 + 1 by norm_num, squarefreeCountNat_succ, count_391]
  norm_num [mu_392]

private theorem cell_392 :
    endpointOK (squarefreeCountNat 392) 392 ∧
      endpointOK (squarefreeCountNat 392) (392 + 1) := by
  rw [count_392]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_393 : μ 393 = 1 := by
  rw [show 393 = 3 * 131 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 131)]
  norm_num

private theorem count_393 : squarefreeCountNat 393 = 238 := by
  rw [show 393 = 392 + 1 by norm_num, squarefreeCountNat_succ, count_392]
  norm_num [mu_393]

private theorem cell_393 :
    endpointOK (squarefreeCountNat 393) 393 ∧
      endpointOK (squarefreeCountNat 393) (393 + 1) := by
  rw [count_393]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_394 : μ 394 = 1 := by
  rw [show 394 = 2 * 197 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 197)]
  norm_num

private theorem count_394 : squarefreeCountNat 394 = 239 := by
  rw [show 394 = 393 + 1 by norm_num, squarefreeCountNat_succ, count_393]
  norm_num [mu_394]

private theorem cell_394 :
    endpointOK (squarefreeCountNat 394) 394 ∧
      endpointOK (squarefreeCountNat 394) (394 + 1) := by
  rw [count_394]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_395 : μ 395 = 1 := by
  rw [show 395 = 5 * 79 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 5),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 79)]
  norm_num

private theorem count_395 : squarefreeCountNat 395 = 240 := by
  rw [show 395 = 394 + 1 by norm_num, squarefreeCountNat_succ, count_394]
  norm_num [mu_395]

private theorem cell_395 :
    endpointOK (squarefreeCountNat 395) 395 ∧
      endpointOK (squarefreeCountNat 395) (395 + 1) := by
  rw [count_395]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_396 : μ 396 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

private theorem count_396 : squarefreeCountNat 396 = 240 := by
  rw [show 396 = 395 + 1 by norm_num, squarefreeCountNat_succ, count_395]
  norm_num [mu_396]

private theorem cell_396 :
    endpointOK (squarefreeCountNat 396) 396 ∧
      endpointOK (squarefreeCountNat 396) (396 + 1) := by
  rw [count_396]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_397 : μ 397 = -1 :=
  ArithmeticFunction.moebius_apply_prime (by norm_num)

private theorem count_397 : squarefreeCountNat 397 = 241 := by
  rw [show 397 = 396 + 1 by norm_num, squarefreeCountNat_succ, count_396]
  norm_num [mu_397]

private theorem cell_397 :
    endpointOK (squarefreeCountNat 397) 397 ∧
      endpointOK (squarefreeCountNat 397) (397 + 1) := by
  rw [count_397]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_398 : μ 398 = 1 := by
  rw [show 398 = 2 * 199 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 2),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 199)]
  norm_num

private theorem count_398 : squarefreeCountNat 398 = 242 := by
  rw [show 398 = 397 + 1 by norm_num, squarefreeCountNat_succ, count_397]
  norm_num [mu_398]

private theorem cell_398 :
    endpointOK (squarefreeCountNat 398) 398 ∧
      endpointOK (squarefreeCountNat 398) (398 + 1) := by
  rw [count_398]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_399 : μ 399 = -1 := by
  rw [show 399 = 3 * 133 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 3),
    show 133 = 7 * 19 by norm_num,
    ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime (by norm_num),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 7),
    ArithmeticFunction.moebius_apply_prime (by norm_num : Nat.Prime 19)]
  norm_num

private theorem count_399 : squarefreeCountNat 399 = 243 := by
  rw [show 399 = 398 + 1 by norm_num, squarefreeCountNat_succ, count_398]
  norm_num [mu_399]

private theorem cell_399 :
    endpointOK (squarefreeCountNat 399) 399 ∧
      endpointOK (squarefreeCountNat 399) (399 + 1) := by
  rw [count_399]
  norm_num [endpointOK, densityLower, densityUpper]

private theorem mu_400 : μ 400 = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  rw [Nat.squarefree_iff_prime_squarefree]
  intro h
  exact h 2 (by norm_num) (by norm_num)

theorem count_400 : squarefreeCountNat 400 = 243 := by
  rw [show 400 = 399 + 1 by norm_num, squarefreeCountNat_succ, count_399]
  norm_num [mu_400]

private theorem cell_400 :
    endpointOK (squarefreeCountNat 400) 400 ∧
      endpointOK (squarefreeCountNat 400) (400 + 1) := by
  rw [count_400]
  norm_num [endpointOK, densityLower, densityUpper]

theorem finite_endpoint_certificate_351_400 (N : ℕ)
    (hlo : 351 ≤ N) (hhi : N ≤ 400) :
    endpointOK (squarefreeCountNat N) N ∧
      endpointOK (squarefreeCountNat N) (N + 1) := by
  interval_cases N
  · exact cell_351
  · exact cell_352
  · exact cell_353
  · exact cell_354
  · exact cell_355
  · exact cell_356
  · exact cell_357
  · exact cell_358
  · exact cell_359
  · exact cell_360
  · exact cell_361
  · exact cell_362
  · exact cell_363
  · exact cell_364
  · exact cell_365
  · exact cell_366
  · exact cell_367
  · exact cell_368
  · exact cell_369
  · exact cell_370
  · exact cell_371
  · exact cell_372
  · exact cell_373
  · exact cell_374
  · exact cell_375
  · exact cell_376
  · exact cell_377
  · exact cell_378
  · exact cell_379
  · exact cell_380
  · exact cell_381
  · exact cell_382
  · exact cell_383
  · exact cell_384
  · exact cell_385
  · exact cell_386
  · exact cell_387
  · exact cell_388
  · exact cell_389
  · exact cell_390
  · exact cell_391
  · exact cell_392
  · exact cell_393
  · exact cell_394
  · exact cell_395
  · exact cell_396
  · exact cell_397
  · exact cell_398
  · exact cell_399
  · exact cell_400

end MoserMacLeod
