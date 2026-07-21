# The Moser--MacLeod squarefree error estimate in Lean

This repository gives a complete mathlib proof of

```lean
theorem MoserMacLeod.abs_R_lt_sqrt (x : ℝ) (hx : 0 < x) :
    |MoserMacLeod.R x| < Real.sqrt x
```

where `R x = Q(x) - (6 / π²) x` and `Q(x)` counts the positive squarefree
integers at most `x`. The paper states the result for `x ≥ 1`; the formal
theorem has the optimal elementary domain `x > 0`. For `0 < x < 1`, `Q(x)=0`
and the extra case is immediate.

The development is pinned to Lean/mathlib `v4.24.0`. It contains no
`native_decide`, `admit`, or proof `sorry`. (`Challenge.lean` intentionally
contains one `sorry`: it is the statement-only comparator input and is not a
dependency of the solution.)

## Start here

- [`Challenge.lean`](Challenge.lean) is a one-theorem, mathlib-only MWE.
- [`Solution.lean`](Solution.lean) has exactly the same theorem statement and
  imports the proof.
- [`MOSER_MACLEOD_LEAN_COMPANION.pdf`](MOSER_MACLEOD_LEAN_COMPANION.pdf) is the
  typeset human proof, trust audit, and paper-to-Lean index. 
- [`MoserMacLeod/Proof.lean`](MoserMacLeod/Proof.lean) contains the analytic
  argument and the public theorem.

This `Challenge`/`Solution` layout follows the Lean MWE convention discussed
in the Zulip thread and is directly usable with
[`leanprover/comparator`](https://github.com/leanprover/comparator).

## Build and audit

Install `elan`, then run:

```sh
lake exe cache get
lake build
lake env lean Challenge.lean
lake env lean Solution.lean
rg 'native_decide|admit' --glob '*.lean'
```

The `Challenge.lean` command succeeds with the expected warning about its
intentional `sorry`. The default `lake build` target does not build Challenge.

At the end of `MoserMacLeod/Proof.lean`, Lean prints the axioms of the final
theorem. They are the standard mathlib logical axioms `propext`,
`Classical.choice`, and `Quot.sound`; there is no `sorryAx`,
`Lean.ofReduceBool`, or `Lean.trustCompiler`.

## Repository structure

| Path | Purpose |
| --- | --- |
| `MoserMacLeod/Base.lean` | Definitions, density bounds, Dirichlet series, and the auxiliary-function argument |
| `MoserMacLeod/TableRows*.lean` | Eight reviewable proof-producing shards for bounded arithmetic |
| `MoserMacLeod/FiniteTable.lean` | Small dispatcher hiding generated rows from the mathematical proof |
| `MoserMacLeod/Infrastructure.lean` | Real-cell certificate and Mertens/weighted-sum estimates |
| `MoserMacLeod/Proof.lean` | Abel summation, square-divisor identity, error bound, and final theorem |
| `MoserMacLeod/SharpBound.lean` | Sharpened leading constant `13/18` for the large-`x` estimate |
| `MoserMacLeod.lean` | Stable public import |
| `Challenge.lean`, `Solution.lean` | Comparator-facing MWE |

## Sharpened leading constant

Beyond the headline `|R(x)| < √x`, the proof of `abs_R_lt_sqrt` establishes the
coarse large-`x` estimate `|R(N)| < 13/16 · √N + 11/4`, whose leading constant
`13/16 ≈ 0.813` already beats `1` asymptotically. `MoserMacLeod/SharpBound.lean`
improves this to

```lean
theorem MoserMacLeod.abs_R_lt_thirteen_eighteenths_sqrt (x : ℝ) (hx : 16 ≤ x) :
    |MoserMacLeod.R x| < 13 / 18 * Real.sqrt x + 77 / 12
```

with leading constant `13/18 ≈ 0.722`. The gain comes from sharpening the
elementary sieve input: a squarefree integer is divisible by neither `4` **nor**
`9`, giving `Q(N) ≤ 2/3·N + O(1)` instead of the coarser `Q(N) ≤ 3/4·N`. The
entire tail argument is re-run generically in the two weight constants
(`finite_tail_bound_gen`, `abs_mu_tail_le_gen`), so the original `13/16` proof
and the finite endpoint certificate are left untouched. The sharpened theorem
carries the same three standard axioms as the headline result.

Because of the additive term, this right-hand side improves on `√x` only past an
explicit crossover. The two sides `13/18·√x + 77/12` and `√x` meet at
`√x = 231/10`, i.e. `x = 533.61`, and `sharp_bound_lt_sqrt` proves

```lean
theorem MoserMacLeod.sharp_bound_lt_sqrt (x : ℝ) (hx : 534 ≤ x) :
    13 / 18 * Real.sqrt x + 77 / 12 < Real.sqrt x
```

so for `x ≥ 534` the estimate is *genuinely* below `√x`. `abs_R_add_margin_lt_sqrt`
records the improvement quantitatively — `|R x|` sits below `√x` by the positive,
unbounded margin `5/18·√x − 77/12` — and `abs_R_lt_sqrt_sharp` re-derives the
headline `|R x| < √x` for `x ≥ 534` through the sharp route, with room to spare
rather than the borderline `13/16` argument used near the `x = 401` crossover.

## Scope

Only the weaker Moser--MacLeod theorem `|R(x)| < √x` is formalized here (with the
sharpened large-`x` constant `13/18` above). The later `R(x) < √x/2` result and
the Cohen--Dress/MacLeod refinements are outside this repository.

## Contributing

Please keep mathematical changes small, state which paper step they implement,
and include the commands used to test them. Generated certificate changes
should remain sharded. See [`CONTRIBUTING.md`](CONTRIBUTING.md).
