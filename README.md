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
| `MoserMacLeod.lean` | Stable public import |
| `Challenge.lean`, `Solution.lean` | Comparator-facing MWE |

## Scope

Only the weaker Moser--MacLeod theorem `|R(x)| < √x` is formalized here. The
later `R(x) < √x/2` result and the Cohen--Dress/MacLeod refinements are outside
this repository.

## Contributing

Please keep mathematical changes small, state which paper step they implement,
and include the commands used to test them. Generated certificate changes
should remain sharded. See [`CONTRIBUTING.md`](CONTRIBUTING.md).
