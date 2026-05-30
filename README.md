# error

This repository contains a small Coq check for the modular-arithmetic issue in the submitted logic note.

## Files

- `LogicCheck.v` formalizes the key point: an element can be invertible modulo a number without being equal to its own inverse.

## Verified statements

The Coq file checks that:

1. `5` has inverse `3` modulo `7`.
2. `5^2` is not congruent to `1` modulo `7`.
3. Therefore, invertibility alone does not imply `a^2 ≡ 1`.
4. If the two square congruences `(A+B)^2 ≡ 1` and `(A-B)^2 ≡ 1` are explicitly assumed, then the algebraic conclusion `4*A*B ≡ 0` follows; the invalid step is deriving those square congruences from mere invertibility.

## Check

```sh
coqc LogicCheck.v
```
