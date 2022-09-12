Require Import Lia PeanoNat.

Lemma Nmod_div: forall a b, b > 0 -> (a mod b) / b = 0.
intros a b gt.
apply Nat.div_small.
apply Nat.mod_upper_bound.
lia.
Qed.

Lemma Ndiv_ge_mul: forall a b c, b > 0 -> a / b >= c <-> a >= c * b.
unfold ge.
split.
-intros cle.
pose (Nat.div_mod a b) as dv.
assert(c * b + (a mod b) <= b * (a / b) + (a mod b)).
apply (Nat.mul_le_mono_l c (a / b) b) in cle.
lia.
rewrite <- dv in H0.
lia.
lia.
-intros cble.
  apply (Nat.div_le_mono _ _ b) in cble.
  rewrite Nat.div_mul in cble.
  lia.
  lia.
  lia.
Qed.

Lemma Ndiv_mul_le: forall a b, b > 0 -> a / b * b <= a.
intros a b bz.
apply (Ndiv_ge_mul a b (a / b)).
lia.
lia.
Qed.

Lemma Ndiv_gt_mul: forall a b c, b > 0 -> a / b < c <-> a < c * b.
intros a b c bgt.
pose (not_iff_compat (Ndiv_ge_mul a b c bgt)).
lia.
Qed.