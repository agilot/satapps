Set Implicit Arguments.
Require Import Bool PeanoNat.
Require Export Fun.

Section Binop.

Definition binop {A B C: Type} := A -> B -> C.

Definition comp_f_bin {A B C D: Type} (f: C -> D) (bin: @binop A B C): @binop A B D := fun a => fun b => f (bin a b).

Definition comp_bin_f {A B C: Type} (bin: @binop B B C) (f: A -> B) : @binop A A C := fun a1 => fun a2 => bin (f a1) (f a2).

Definition homomorphism {A B: Type} (f: A -> B) (bin1: @binop A A A) (bin2: @binop B B B) := comp_f_bin f bin1 = comp_bin_f bin2 f.

Definition linear {A: Type} (f: A -> A) (bin: @binop A A A) := homomorphism f bin bin.

End Binop.

Section Associativity.

Definition assoc {A: Type} (f: @binop A A A) := forall (a1 a2 a3: A), f a1 (f a2 a3) =f (f a1 a2) a3.

Class Semigroup {A: Type} (law: @binop A A A) :=
{semigroup_assoc: assoc law}.

End Associativity.

Section Identity.

Definition neutr_l {A B: Type} (f: @binop A B B) (e: A) := forall (b: B), f e b = b.

Definition neutr_r {A B: Type} (f: @binop A B A) (e: B) := forall (a: A), f a e = a.

Definition neutr {A: Type} (f: @binop A A A) (e: A) := neutr_l f e /\ neutr_r f e.

Class UnitalMagma {A: Type} (law: @binop A A A) (e: A) :=
{unimagma_neutr: neutr law e}.

Class Monoid {A: Type} (law: @binop A A A) (e: A) :=
{monoid_assoc: assoc law;
monoid_neutr: neutr law e}.

Theorem monoid_is_unimagma {A: Type}: forall law (e: A), Monoid law e -> UnitalMagma law e.
intros.
destruct H.
split.
tauto.
Qed.

Theorem monoid_is_semigroup {A: Type}: forall law (e: A), Monoid law e -> Semigroup law.
intros.
destruct H.
split.
tauto.
Qed.

Theorem neutr_l_r_unique {A: Type}: forall (f: @binop A A A) (e1: A) (e2: A), neutr_l f e1 -> neutr_r f e2 -> e1 = e2.
unfold neutr_r, neutr_l.
intros f e1 e2 n1 n2.
rewrite <- (n1 e2), (n2 e1).
tauto.
Qed.

Theorem neutr_unique {A: Type}: forall (f: @binop A A A) (e1: A) (e2: A), neutr f e1 -> neutr f e2 -> e1 = e2.
intros f e1 e2 n1 n2.
destruct n1, n2.
apply (neutr_l_r_unique H H2).
Qed.

End Identity.

Section Inverse.

Definition inv_l {A B C: Type} (f: @binop A B C) (e: C) (i: B -> A) := forall (b: B), f (i b) b = e.

Definition inv_r {A B C: Type} (f: @binop A B C) (e: C) (i: A -> B) := forall (a: A), f a (i a) = e.

Definition inv {A C: Type} (f: @binop A A C) (e: C) (i: A -> A) := inv_l f e i /\ inv_r f e i.

Class Group {A: Type} (law: @binop A A A) (e: A) (i: A -> A) :=
{group_assoc: assoc law;
group_neutr: neutr law e;
group_inv: inv law e i}.

Theorem group_is_monoid {A: Type}: forall law (e: A) i, Group law e i -> Monoid law e.
intros.
destruct H.
split.
tauto.
tauto.
Qed.

End Inverse.

Section Commutativity.

Definition comm {A B: Type} (f: @binop A A B) := forall (a1 a2: A), f a1 a2 = f a2 a1.

Class CommSemigroup {A: Type} (law: @binop A A A) :=
{comm_sg_is_sg: Semigroup law;
comm_semigroup: comm law}.

Class CommMonoid {A: Type} (law: @binop A A A) (e: A) :=
{comm_monoid_is_monoid: Monoid law e;
comm_monoid: comm law}.

Class AbelianGroup {A: Type} (law: @binop A A A) (e: A) (i: A -> A) :=
{abel_group_is_group: Group law e i;
abel_group_comm: comm law}.

Theorem comm_monoid_is_comm_semigroup {A: Type}: forall (law: @binop A A A) e, CommMonoid law e -> CommSemigroup law.
intros.
destruct H.
split.
apply (monoid_is_semigroup comm_monoid_is_monoid0).
tauto.
Qed.

Theorem abel_group_is_comm_monoid {A: Type}: forall (law: @binop A A A) e i, AbelianGroup law e i -> CommMonoid law e.
intros.
destruct H.
split.
apply (group_is_monoid abel_group_is_group0).
tauto.
Qed.

Definition flip {A B: Type} (f: @binop A A B) := fun x => fun y => f y x.

Theorem comm_flip {A B: Type}: forall (f: @binop A A B), comm f <-> f = flip f.
intros f.
unfold comm, flip.
split.
intro C.
apply functional_extensionality.
intros x.
apply functional_extensionality.
intros x0.
apply (C x x0).
intros F a1 a2.
pose (equal_f F).
pose (equal_f (e a1)).
rewrite (e0 a2).
tauto.
Qed.

Theorem neutr_l_comm {A: Type}: forall (f: @binop A A A) (e: A), neutr_l f e -> comm f -> neutr f e.
intros f e nl co.
split.
tauto.
unfold neutr_r.
unfold neutr_l in nl; unfold comm in co.
intros a.
pose (nl a).
pose (co e a).
rewrite <- e1.
rewrite e0.
tauto.
Qed.

Theorem neutr_r_comm {A: Type}: forall (f: @binop A A A) (e: A), neutr_r f e -> comm f -> neutr f e.
intros f e nr co.
split.
unfold neutr_l.
unfold neutr_r in nr; unfold comm in co.
intros a.
pose (nr a).
pose (co e a).
rewrite e1.
rewrite e0.
tauto.
tauto.
Qed.

End Commutativity.

Section Idempotence.

Definition idempotent {A: Type} (f: @binop A A A) := forall (a: A), f a a = a.

Class Band {A: Type} (law: @binop A A A) :=
{band_is_semigroup: Semigroup law;
 band_idem: idempotent law}.
Class Semilattice {A: Type} (law: @binop A A A) :=
{semilattice_assoc: assoc law;
 semilattice_comm: comm law;
 semilattice_idem: idempotent law}.
Class BoundedSemilattice {A: Type} (law: @binop A A A) (e: A) :=
{bounded_is_semilattice: Semilattice law;
 bound_indentity: neutr law e}.

Theorem semilattice_is_band {A: Type}: forall (law: @binop A A A), Semilattice law -> Band law.
intros.
destruct H.
split.
split.
tauto.
tauto.
Qed.

Theorem bounded_semilattice_is_monoid {A: Type}: forall (law: @binop A A A) e, BoundedSemilattice law e -> Monoid law e.
intros.
destruct H.
split.
destruct bounded_is_semilattice0.
tauto.
tauto.
Qed.

End Idempotence.

Section Absorb.

Definition abs_l {A B: Type} (f: @binop A B A) (z: A) := forall (b: B), f z b = z.

Definition abs_r {A B: Type} (f: @binop A B B) (z: B) := forall (a: A), f a z = z.

Definition abs {A: Type} (f: @binop A A A) (z: A) := abs_l f z /\ abs_r f z.

End Absorb.

Section Examples.

Theorem comp_assoc {A: Type}: assoc (@comp A A A).
unfold assoc, comp; tauto. Qed.

Theorem comp_neutr_l {A B: Type} : neutr_l (@comp A B B) id_f.
unfold neutr_l, comp, id_f.
intros.
apply functional_extensionality.
tauto.
Qed.

Theorem comp_neutr_r {A B: Type} : neutr_r (@comp A A B) id_f.
unfold neutr_r, comp, id_f.
intros.
apply functional_extensionality.
tauto.
Qed.

Definition comp_neutr {A: Type}: neutr (@comp A A A) id_f := conj comp_neutr_l comp_neutr_r.

Theorem comp_abs_l {A B: Type} : forall b, abs_l (@comp A A B) (const_f b).
unfold abs_l, comp, const_f; tauto. Qed.

Instance FunMonoid {A: Type} : Monoid (@comp A A A) id_f.
split.
apply comp_assoc.
apply comp_neutr.
Qed.

Theorem id_f_linear {A: Type}: forall (bin: @binop A A A), linear id bin.
intros bin.
unfold linear, homomorphism, comp_f_bin, comp_bin_f, id.
tauto.
Qed.


Definition andb_comm: comm andb := andb_comm.
Definition andb_assoc: assoc andb := andb_assoc.
Definition andb_neutr: neutr andb true := conj andb_true_l andb_true_r.
Definition andb_abs: abs andb false := conj andb_false_l andb_false_r.
Theorem andb_idem: idempotent andb.
unfold idempotent.
destruct a.
apply andb_true_l.
apply andb_false_l.
Qed.

Instance BoolAndBoundedSemilattice : BoundedSemilattice andb true.
split.
split.
apply andb_assoc. 
apply andb_comm.
apply andb_idem.
apply andb_neutr.
Qed.

Definition orb_comm: comm orb := orb_comm.
Definition orb_assoc: assoc orb := orb_assoc.
Definition orb_neutr: neutr orb false := conj orb_false_l orb_false_r.
Definition orb_abs: abs orb true := conj orb_true_l orb_true_r.
Theorem orb_idem: idempotent orb.
unfold idempotent.
destruct a.
apply orb_true_l.
apply orb_false_l.
Qed.

Instance BoolOrBoundedSemilattice : BoundedSemilattice orb false.
split.
split.
apply orb_assoc. 
apply orb_comm.
apply orb_idem.
apply orb_neutr.
Qed.

Definition xorb_comm: comm xorb := xorb_comm.
Definition xorb_assoc: assoc xorb := fun a b c => eq_sym (xorb_assoc a b c).

Instance BoolXorCommSemigroup : CommSemigroup xorb.
split.
split.
apply xorb_assoc.
apply xorb_comm.
Qed.


Definition plus_comm: comm plus := Nat.add_comm.
Definition plus_assoc: assoc plus := Nat.add_assoc.
Definition plus_neutr: neutr plus 0 := conj Nat.add_0_l Nat.add_0_r.

Instance NatPlusCommMonoid: CommMonoid plus 0.
split.
split.
apply plus_assoc.
apply plus_neutr.
apply plus_comm.
Qed.

Definition mult_comm: comm mult := Nat.mul_comm.
Definition mult_assoc: assoc mult := Nat.mul_assoc.
Definition mult_neutr: neutr mult 1 := conj Nat.mul_1_l Nat.mul_1_r.
Definition mult_absorb: abs mult 0 := conj Nat.mul_0_l Nat.mul_0_r.

Instance NatMultCommMonoid: CommMonoid mult 1.
split.
split.
apply mult_assoc.
apply mult_neutr.
apply mult_comm.
Qed.

End Examples.