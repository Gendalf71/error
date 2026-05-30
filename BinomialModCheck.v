(******************************************************************************
  A Coq check of the binomial-expansion modular-arithmetic point in the
  submitted note.

  The file verifies that a congruence such as
      (a + b)^n ≡ a^n + b^n (mod q)
  means only that the binomial remainder is divisible by q.  It does not turn
  a modular congruence into an integer equality, and it does not force a or b
  to be zero.
 ******************************************************************************)

From Coq Require Import ZArith Lia.
Require Import LogicCheck.

Open Scope Z_scope.

Definition cube_intermediate (a b : Z) : Z := 3 * a * a * b + 3 * a * b * b.

Theorem cong_means_integer_multiple :
  forall q lhs rhs,
    cong q lhs rhs -> exists t, lhs = rhs + q * t.
Proof.
  intros q lhs rhs [t Ht]. exists t. lia.
Qed.

Theorem cube_binomial_remainder :
  forall a b,
    (a + b) ^ 3 - (a ^ 3 + b ^ 3) = cube_intermediate a b.
Proof.
  intros a b. unfold cube_intermediate. ring.
Qed.

Theorem cube_congruence_iff_intermediate_sum_congruent_zero :
  forall q a b,
    cong q ((a + b) ^ 3) (a ^ 3 + b ^ 3) <->
    cong q (cube_intermediate a b) 0.
Proof.
  intros q a b. split.
  - intros [t Ht]. unfold cong. exists t.
    rewrite <- cube_binomial_remainder. lia.
  - intros [t Ht]. unfold cong. exists t.
    rewrite cube_binomial_remainder. lia.
Qed.

Example thirty_is_zero_mod_five_but_not_integer_zero :
  cong 5 30 0 /\ 30 <> 0.
Proof.
  split.
  - unfold cong. exists 6. lia.
  - lia.
Qed.

Example cube_congruence_can_hold_with_nonzero_inputs :
  cong 3 ((1 + 1) ^ 3) (1 ^ 3 + 1 ^ 3) /\
  ~ cong 3 1 0 /\
  ~ cong 3 1 0.
Proof.
  repeat split.
  - unfold cong. exists 2. lia.
  - unfold cong. intros [t Ht]. lia.
  - unfold cong. intros [t Ht]. lia.
Qed.

Example cube_congruence_does_not_imply_integer_equality :
  cong 3 ((1 + 1) ^ 3) (1 ^ 3 + 1 ^ 3) /\
  (1 + 1) ^ 3 <> 1 ^ 3 + 1 ^ 3.
Proof.
  split.
  - unfold cong. exists 2. lia.
  - lia.
Qed.

Example intermediate_sum_can_be_nonzero_integer_but_zero_modulo :
  cong 3 (cube_intermediate 1 1) 0 /\ cube_intermediate 1 1 <> 0.
Proof.
  split.
  - unfold cong, cube_intermediate. exists 2. lia.
  - unfold cube_intermediate. lia.
Qed.

Example congruence_t_can_be_nonzero :
  exists t,
    (1 + 1) ^ 3 = 1 ^ 3 + 1 ^ 3 + 3 * t /\ t <> 0.
Proof.
  exists 2. lia.
Qed.
