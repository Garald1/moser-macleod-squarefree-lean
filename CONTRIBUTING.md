# Contributing

This repository is optimized for mathematical review.

1. Keep each change focused on one lemma or one paper step.
2. In the pull-request description, give the mathematical motivation, scope,
   and exact test commands.
3. Preserve the `Challenge.lean` theorem statement unless the target theorem
   itself is intentionally changing.
4. Put reusable lemmas in the smallest sensible module. Keep certificate
   implementation details behind `FiniteTable.lean`.
5. Shard large proof-producing computations; do not replace them with
   `native_decide` without discussing the trust boundary.
6. Update the paper-to-Lean table when a named lemma or bound changes.
7. Disclose substantial AI assistance in the pull request, and say which parts
   were checked independently by a human.

Before opening a pull request, run:

```sh
lake exe cache get
lake build
lake env lean Solution.lean
rg 'native_decide|admit' --glob '*.lean'
```

Warnings from `Challenge.lean` about `sorry` are intentional. New warnings in
solution modules should be fixed or explained.
