(******************************************************************************
  A small Coq check of the modular-arithmetic point in the submitted note.

  The file verifies two things:
  1. The concrete counterexample modulo 7: 5 is invertible, but 5^2 is not
     congruent to 1.
  2. The later conclusion 4*A*B ≡ 0 does follow if one explicitly assumes
     both (A+B)^2 ≡ 1 and (A-B)^2 ≡ 1.  Thus the problem is exactly the
     missing premise that an invertible element must be self-inverse.
 ******************************************************************************)

From Coq Require Import ZArith Lia.

Open Scope Z_scope.

Definition cong (q a b : Z) : Prop := exists k : Z, a - b = q * k.
Definition invertible_mod (q a : Z) : Prop := exists b : Z, cong q (a * b) 1.
Definition sq (a : Z) : Z := a * a.

Lemma cong_refl : forall q a, cong q a a.
Proof.
  intros q a. unfold cong. exists 0. lia.
Qed.

Lemma cong_sym : forall q a b, cong q a b -> cong q b a.
Proof.
  intros q a b [k Hk]. unfold cong. exists (-k). lia.
Qed.

Lemma cong_sub : forall q a b c d,
    cong q a b -> cong q c d -> cong q (a - c) (b - d).
Proof.
  intros q a b c d [k Hk] [l Hl]. unfold cong. exists (k - l). lia.
Qed.

Example five_has_inverse_mod_7 : invertible_mod 7 5.
Proof.
  unfold invertible_mod, cong. exists 3. exists 2. lia.
Qed.

Example five_square_not_one_mod_7 : ~ cong 7 (sq 5) 1.
Proof.
  unfold cong, sq. intros [k Hk]. lia.
Qed.

Example inverse_existence_does_not_imply_square_one :
  exists q a, invertible_mod q a /\ ~ cong q (sq a) 1.
Proof.
  exists 7, 5. split.
  - exact five_has_inverse_mod_7.
  - exact five_square_not_one_mod_7.
Qed.

Theorem two_square_assumptions_imply_four_product_zero :
  forall q A B,
    cong q (sq (A + B)) 1 ->
    cong q (sq (A - B)) 1 ->
    cong q (4 * A * B) 0.
Proof.
  intros q A B Hplus Hminus.
  pose proof (cong_sub q (sq (A + B)) 1 (sq (A - B)) 1 Hplus Hminus)
    as Hdiff.
  unfold cong, sq in *.
  destruct Hdiff as [k Hk].
  exists k.
  replace (4 * A * B - 0) with
      ((A + B) * (A + B) - (A - B) * (A - B) - (1 - 1)) by ring.
  exact Hk.
Qed.

Theorem self_inverse_equiv_square_one_for_invertible :
  forall q a b,
    cong q (a * b) 1 ->
    cong q a b ->
    cong q (sq a) 1.
Proof.
  intros q a b Hab Ha_b.
  unfold cong, sq in *.
  destruct Hab as [k Hk].
  destruct Ha_b as [l Hl].
  exists (k + a * l).
  lia.
Qed.
