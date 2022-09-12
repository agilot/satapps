Require Import List Le Gt Minus Min Bool PeanoNat NDiv Lia.
Require Export Pair NArithSpec.

Set Implicit Arguments.

Section ListOpt.

Variable A: Type.
Variable B: Type.
Variable C: Type.

Fixpoint fold_some {T: Type} (l: list T) :=
match l with
 | nil => nil
 | x :: t => (Some x) :: (fold_some t)
end.

Lemma eq_some: forall (a1: A) (a2: A), Some a1 = Some a2 -> a1 = a2.
intros.
inversion H.
tauto.
Qed.

Lemma fold_some_In : forall (l: list A) (e: A), In e l <-> In (Some e) (fold_some l).
intros l e.
induction l.
- tauto.
- simpl.
  split.
  intro H.
  destruct H.
  * apply (f_equal (fun x => Some x)) in H.
    tauto.
  * tauto.
  * intro H.
    destruct H.
    inversion H.
    tauto.
    tauto.
Qed.


Lemma fold_some_app: forall (l1: list A) (l2: list A), fold_some (l1 ++ l2) = (fold_some l1) ++ (fold_some l2).
intros l1 l2.
induction l1.
- tauto.
- simpl.
  apply (f_equal (fun l => (Some a) :: l)) in IHl1.
  tauto.
Qed.

Lemma fold_some_length: forall (l1: list A), length (fold_some l1) = length l1.
induction l1.
auto.
simpl.
lia.
Qed.

Lemma fold_some_nth: forall (n: nat) (l: list A) (d: A), nth n (fold_some l) (Some d) = Some (nth n l d).
induction n as [| n hn].
destruct l.
auto.
auto.
destruct l.
auto.
intros d.
simpl.
auto.
Qed.

Lemma fold_some_map: forall (l: list A) (f: A -> B), fold_some (map f l) = map (fun a: A => Some (f a)) l.
induction l.
- tauto.
- intros.
  simpl.
  rewrite (IHl f).
  tauto.
 Qed.
 
Lemma fold_some_combine: forall (l1: list A) (l2: list B), fold_some (combine l1 l2) = map fact_opt_pair (combine (fold_some l1) (fold_some l2)).
induction l1.
- destruct l2.
  * tauto.
  * tauto.
- destruct l2.
  * tauto.
  * simpl.
    rewrite (IHl1 l2).
    tauto.
Qed.

Lemma nth_error_nth: forall (n: nat) (l: list A), nth_error l n = nth n (fold_some l) None.
induction n as [| n hn].
destruct l.
auto.
auto.
destruct l.
auto.
simpl.
auto.
Qed.

Lemma nth_error_nth_lt: forall (n: nat) (l: list A) (d: A), n < length l -> nth_error l n = Some (nth n l d).
intros.
rewrite <- fold_some_length in H.
pose (nth_indep (fold_some l) None (Some d) H).
rewrite fold_some_nth in e.
rewrite <- nth_error_nth in e.
tauto.
Qed.

Lemma nth_error_overflow: forall n (l: list A), length l <= n -> nth_error l n = None.
intros n l le_n.
rewrite <- fold_some_length in le_n.
pose (nth_overflow (fold_some l) None le_n).
rewrite <- nth_error_nth in e.
tauto.
Qed.

Lemma nth_error_In : forall (n:nat) (l:list A), n < length l -> In (nth_error l n) (fold_some l).
intros n l lt_n.
rewrite <- fold_some_length in lt_n.
pose (nth_In (fold_some l) None lt_n).
rewrite <- nth_error_nth in i.
tauto.
Qed.

Lemma app_nth_error_1 :
    forall n (l: list A) l', n < length l -> nth_error (l++l') n = nth_error l n.
intros n l l' lt_l.
rewrite <- fold_some_length in lt_l. 
pose (app_nth1 (fold_some l) (fold_some l') None lt_l).
rewrite <- fold_some_app in e.
rewrite <- nth_error_nth in e.
rewrite <- nth_error_nth in e.
tauto.
Qed.

Lemma app_nth_error_2 : forall n (l: list A) l', n >= length l -> nth_error (l++l') n = nth_error l' (n - length l).
intros n l l' le_l.
rewrite <- fold_some_length in le_l. 
pose (app_nth2 (fold_some l) (fold_some l') None le_l).
rewrite <- fold_some_app in e.
rewrite <- nth_error_nth in e.
rewrite <- nth_error_nth in e.
rewrite fold_some_length in e. 
tauto.
Qed.

Lemma nth_error_in_or_none :
    forall (n:nat) (l:list A), {In (nth_error l n ) (fold_some l)} + {nth_error l n = None}.
intros n l.
pose (nth_in_or_default n (fold_some l) None).
rewrite <- nth_error_nth in s.
tauto.
Qed.

Lemma nth_error_univ: forall (l1: list A) (l2: list A), (forall n, nth_error l1 n = nth_error l2 n) -> l1 = l2.
induction l1.
- destruct l2.
  * tauto.
  * intro univ.
    pose (univ 0).
    simpl in e.
    discriminate.
- destruct l2.
  * intro univ.
    pose (univ 0).
    simpl in e.
    discriminate.
  * intro univ.
    assert(forall n : nat, nth_error l1 n = nth_error l2 n).
    -- intros n.
       apply (univ (S n)).
    -- pose (univ 0).
       inversion e.
       pose (IHl1 l2 H).
       rewrite e0.
       tauto.
Qed.

Lemma nth_error_map: forall (n: nat) (l: list A) (f: A -> B), nth_error (map f l) n = (opt_f f) (nth_error l n).
induction n.
- destruct l.
  * tauto.
  * tauto.
- destruct l.
  * tauto.
  * intro f.
    simpl.
    pose (IHn l f).
    tauto.
Qed.

End ListOpt.

Section In.

Variable A: Type.

Lemma In_tail: forall (l: list A) e, In e (tail l) -> In e l.
induction l.
- tauto.
- simpl.
  tauto.
Qed.

End In.

Section Update.

Variable A: Type.   
Variable B: Type.

Fixpoint update {T: Type} (l: list T) (n: nat) (v: T) :=
match n, l with
| 0, nil => nil
| 0, x :: t => v :: t
| S m, nil => nil
| S m, x :: t => x :: update t m v
end.

Lemma nth_error_update: forall n (l: list A) v, n < length l -> nth_error (update l n v) n = Some v.
induction n.
- destruct l.
  * intros.
    simpl in H.
    lia.
  * intros.
    tauto.
- destruct l.
  * intros.
    simpl in H.
    lia.
  * intros.
    simpl in H.
    apply Lt.lt_S_n in H.
    pose (IHn l v H).
    tauto.
Qed.

Lemma nth_update: forall n (l: list A) v def, n < length l -> nth n (update l n v) def = v.
induction n.
- destruct l.
  * intros.
    simpl in H.
    lia.
  * intros.
    tauto.
- destruct l.
  * intros.
    simpl in H.
    lia.
  * intros.
    simpl in H.
    apply Lt.lt_S_n in H.
    pose (IHn l v def H).
    tauto.
Qed.

Lemma update_overflow: forall n (l: list A) v, length l <= n -> update l n v = l.
induction n.
- intros.
  destruct l.
    * tauto.
    * simpl in H.
      lia.
- intros.
  destruct l.
  * tauto.
  * simpl.
    simpl in H.
    apply le_S_n in H.
    rewrite (IHn l v H).
    tauto.
Qed.

Lemma update_indep: forall n (l: list A) v v', length l <= n -> update l n v = update l n v'.
intros.
rewrite update_overflow.
rewrite update_overflow.
tauto.
tauto.
tauto.
Qed.

Lemma update_length: forall (l: list A) n v, length (update l n v) = length l.
induction l.
- destruct n.
  * tauto.
  * tauto.
- destruct n.
  * tauto.
  * intros.
    simpl.
    apply eq_S.
    apply (IHl n v).
Qed.

Lemma update_length_indep: forall (l: list A) n1 n2 v v', length (update l n1 v) = length (update l n2 v').
intros.
rewrite update_length.
rewrite update_length.
tauto.
Qed.

Lemma update_map: forall (l: list A) n (v: A) (f: A -> B), map f (update l n v) = update (map f l) n (f v).
induction l.
- destruct n.
  * tauto.
  * tauto.
- destruct n.
  * tauto.
  * intros v f.
    simpl.
    rewrite (IHl n v f).
    tauto.
Qed.

Lemma combine_update: forall (l1: list A) (l2: list B) n (v1: A) (v2: B), update (combine l1 l2) n (v1, v2) = combine (update l1 n v1) (update l2 n v2).
induction l1.
- destruct l2.
  * destruct n.
    -- tauto.
    -- tauto.
  * destruct n.
    -- tauto.
    -- tauto.
- destruct l2.
  * destruct n.
    -- tauto.
    -- tauto.
  * destruct n.
    -- tauto.
    -- intros.
       simpl.
       rewrite (IHl1 l2 n v1 v2).
       tauto.
Qed.

End Update.

Section Map.

Variable A: Type.
Variable B: Type.

Lemma map_repeat: forall (f: A -> B) n (v: A), map f (repeat v n) = repeat (f v) n.
intros.
induction n.
- tauto.
- simpl.
  rewrite IHn.
  tauto.
Qed.

Lemma map_binop_comb: forall (l1: list A) (l2: list A) (f: A -> A -> B), length l1 = length l2 -> 
map (bin_to_pair f) (combine l1 l2) =
map (bin_to_pair (flip f)) (combine l2 l1).
induction l1.
- intros.
  apply eq_sym in H.
  simpl in H.
  apply length_zero_iff_nil in H.
  rewrite H.
  tauto.
- destruct l2.
  * tauto.
  * intros.
    simpl.
    simpl in H.
    apply (Nat.succ_inj (length l1) (length l2)) in H.
    rewrite (IHl1 l2 f H).
    tauto.
Qed.  

End Map.

Section Combine.

Variable A: Type.
Variable B: Type.

Theorem combine_nth_error : forall (l1: list A) (l2: list B) n, length l1 = length l2 -> nth_error (combine l1 l2) n = fact_opt_pair ((nth_error l1 n), (nth_error l2 n)).
intros l1 l2 n leq.
rewrite nth_error_nth, nth_error_nth, nth_error_nth, fold_some_combine.
pose (map_nth (@fact_opt_pair A B) (combine (fold_some l1) (fold_some l2)) (None, None) n).
simpl in e.
rewrite e.
rewrite combine_nth.
tauto.
rewrite fold_some_length.
rewrite fold_some_length.
tauto.
Qed.

Theorem combine_app: forall (l1: list A) (l2: list B) l3 l4,
length l1 = length l2 -> combine (l1 ++ l3) (l2 ++ l4) = (combine l1 l2) ++ (combine l3 l4).
induction l1.
- destruct l2.
  * tauto.
  * simpl.
    lia.
- destruct l2.
  * simpl.
    lia.
  * simpl.
    intros l3 l4 e1.
    rewrite IHl1.
    tauto.
    lia.
Qed.

Theorem combine_In: forall (l1: list A) (l2: list B) v1 v2, In (v1, v2) (combine l1 l2) -> (In v1 l1 /\ In v2 l2).
induction l1.
- simpl.
  tauto.
- destruct l2.
  * simpl.
    tauto.
  * simpl.
    intros v1 v2 H.
    destruct H.
    apply pair_equal_spec in H.
    tauto.
    pose (IHl1 l2 v1 v2 H).
    tauto.
Qed.

Theorem combine_skipn: forall (l1: list A) (l2: list B) n, length l1 = length l2 -> skipn n (combine l1 l2) = combine (skipn n l1) (skipn n l2).
induction l1.
- simpl.
  intros l2 n H.
  rewrite skipn_nil, skipn_nil.
  tauto.
- induction l2.
  + intros n H.
    simpl in H.
    lia.
  + induction n.
    * tauto.
    * simpl.
      intros H.
      rewrite IHl1.
      tauto.
      lia.
Qed.

Theorem combine_app_distrib: forall (l1 l2: list A) (l3 l4: list B), length l1 = length l3 -> length l2 = length l4 -> combine (app l1 l2) (app l3 l4) = app (combine l1 l3) (combine l2 l4).
induction l1.
- destruct l2.
  + tauto.
  + destruct l3.
    * tauto.
    * intros.
      simpl in H.
      lia.
- destruct l2.
  + rewrite app_nil_r.
    destruct l3.
    * simpl. lia.
    * destruct l4.
      ++ simpl.
         rewrite app_nil_r, app_nil_r.
         tauto.
      ++ simpl. lia.
  + destruct l3.
    * destruct l4.
      ++ tauto.
      ++ simpl. lia.
    * destruct l4.
      ++ simpl. lia.
      ++ simpl.
         intros.
         rewrite IHl1.
         simpl.
         tauto.
         lia.
         simpl.
         lia.
Qed.
  
End Combine.

Section Binop.

Definition list_binop {A B C: Type} (l1: list A) (l2: list B) (bin: @binop A B C) := map (bin_to_pair bin) (combine l1 l2).

Theorem list_binop_nil_l {A B C: Type}: forall l (bin: @binop A B C), @list_binop A B C nil l bin = nil.
unfold list_binop.
intros l bin.
simpl.
tauto.
Qed.

Theorem list_binop_nil_r {A B C: Type}: forall l (bin: @binop A B C), @list_binop A B C l nil bin = nil.
unfold list_binop.
intros l bin.
rewrite combine_nil.
simpl.
tauto.
Qed.

Theorem list_binop_length {A B C: Type}: forall (l1: list A) (l2: list B) (bin: @binop A B C), length l1 = length l2 -> length (list_binop l1 l2 bin) = length l1.
intros l1 l2 bin leneq.
unfold list_binop, combine.
rewrite map_length.
rewrite combine_length.
rewrite leneq.
rewrite Nat.min_id.
tauto.
Qed.

Theorem list_binop_cons {A B C: Type}: forall (l1: list A) (l2: list B) (bin: @binop A B C)  x1 x2,  list_binop (x1 :: l1) (x2 :: l2) bin = (bin x1 x2) :: (list_binop l1 l2 bin).
tauto. Qed.


Theorem list_binop_nth_error {A B C: Type}: forall (l1: list A) (l2: list B) (bin: @binop A B C) n, length l1 = length l2 -> nth_error (list_binop l1 l2 bin) n = (opt_f (bin_to_pair bin)) (fact_opt_pair ((nth_error l1 n), (nth_error l2 n))).
intros M1 M2 bin n leneq.
unfold list_binop.
rewrite nth_error_map.
rewrite combine_nth_error.
tauto.
tauto.
Qed.

Theorem list_binop_nth {A B C: Type}: forall (l1: list A) (l2: list B) (bin: @binop A B C) n d1 d2, length l1 = length l2 -> nth n (list_binop l1 l2 bin) (bin d1 d2) = bin (nth n l1 d1) (nth n l2 d2).
intros l1 l2 bin n d1 d2 leneq.
unfold list_binop.
pose (map_nth (bin_to_pair bin) (combine l1 l2) (d1, d2) n).
unfold bin_to_pair in e.
simpl in e.
unfold bin_to_pair.
rewrite e.
rewrite combine_nth.
simpl.
tauto.
tauto.
Qed.

Theorem list_binop_update {A B C: Type}: forall (l1: list A) (l2: list B) (bin: @binop A B C) n d1 d2, length l1 = length l2 -> update (list_binop l1 l2 bin) n (bin d1 d2) = list_binop (update l1 n d1) (update l2 n d2) bin.
intros l1 l2 bin n d1 d2 leneq.
unfold list_binop.
pose (update_map (combine l1 l2) n (d1, d2) (bin_to_pair bin) ).
unfold bin_to_pair in e.
simpl in e.
unfold bin_to_pair.
rewrite <- e.
rewrite combine_update.
tauto.
Qed.

Theorem list_binop_map {A B C D: Type}: forall (l1: list A) (l2: list B) (bin: @binop A B C) (f: C -> D), length l1 = length l2 -> map f (list_binop l1 l2 bin) = list_binop l1 l2(comp_f_bin f bin).
intros l1 l2 bin f leneq.
unfold list_binop.
rewrite map_map.
rewrite bin_to_pair_comp_f_bin.
tauto.
Qed.

Lemma app_linear {A B: Type}: forall (f: A -> B), homomorphism (map f) (@app A) (@app B).
intros f.
unfold homomorphism, comp_f_bin, comp_bin_f.
apply functional_extensionality.
intros a.
apply functional_extensionality.
intros b.
apply map_app.
Qed.

Lemma list_binop_map_linear {A B: Type}: forall (l1 l2: list A)  (bin1: @binop A A A) (bin2: @binop B B B) (f: A -> B), homomorphism f bin1 bin2 -> map f (list_binop l1 l2 bin1) = list_binop (map f l1) (map  f l2) bin2.
induction l1.
- tauto.
- destruct l2.
  + tauto.
  + intros bin1 bin2 f hom.
    pose (IHl1 l2 bin1 bin2 f hom).
    simpl.
    unfold list_binop in e.
    rewrite e.
    rewrite list_binop_cons.
    unfold list_binop.
    unfold homomorphism in hom.
    unfold comp_f_bin, comp_bin_f in hom.
    unfold bin_to_pair.
    simpl.
    rewrite (equal_f (equal_f hom a) a0).
    tauto.
Qed.

Definition list_binop_comm {A B: Type}: forall (f: @binop A A B) l1 l2, length l1 = length l2 -> comm f -> list_binop l1 l2 f = list_binop l2 l1 f.
intros f l1 l2 leneq H.
unfold list_binop.
rewrite map_binop_comb.
apply comm_flip in H.
rewrite <- H.
tauto.
tauto.
Qed.

End Binop.

Section Concat.

Variable A: Type.

Lemma concat_length: forall (l: list (list A)), length (concat l) = list_sum (map (@length A) l).
induction l.
- tauto.
- simpl.
  rewrite app_length.
  lia.
Qed.

Lemma same_length_repeat: forall (l: list (list A)) L, Forall (fun x => length x = L) l -> map (@length A) l = repeat L (length l).
induction l.
- tauto.
- simpl.
  intros L fa.
  apply Forall_cons_iff in fa.
  destruct fa.
  rewrite H.
  rewrite (IHl L).
  tauto.
  tauto.
Qed.

Lemma list_sum_repeat: forall n v, list_sum (repeat v n) = n * v.
induction n.
- tauto.
- simpl.
  intros.
  rewrite (IHn v).
  tauto.
Qed.

Lemma concat_same_length: forall (l: list (list A)) L, Forall (fun x => length x = L) l -> length (concat l) = (length l) * L.
intros l L fa.
rewrite <- list_sum_repeat.
rewrite <- same_length_repeat.
apply concat_length.
tauto.
Qed.

Lemma app_inv_same_length: forall (a1: list A) a2 l1 l2, length a1 = length a2 -> a1 ++ l1 = a2 ++ l2 -> a1 = a2 /\ l1 = l2.
induction a1.
- simpl.
  intros.
  apply eq_sym, length_zero_iff_nil in H.
  rewrite H.
  rewrite H in H0.
  tauto.
- simpl.
  destruct a2.
  + simpl.
    lia.
  + simpl.
    intros.
    assert(length a1 = length a2).
    lia.
    assert(a = a0 /\ a1 ++ l1 = a2 ++ l2).
    split.
    apply (f_equal (@head A)) in H0.
    simpl in H0.
    apply eq_some in H0.
    tauto.
    apply (f_equal (@tail A)) in H0.
    simpl in H0.
    tauto.
    destruct H2.
    pose (IHa1 a2 l1 l2 H1 H3).
    destruct a3.
    rewrite H2, H4, H5.
    tauto.
Qed.

Lemma concat_same_length_eq: forall (l1 l2: list (list A)) L, L > 0 -> Forall (fun x => length x = L) l1 -> Forall (fun x => length x = L) l2 -> concat l1 = concat l2 -> l1 = l2.
induction l1, l2.
- tauto.
- simpl.
  intros.
  apply eq_sym, app_eq_nil in H2.
  destruct H2.
  apply Forall_cons_iff in H1.
  destruct H1.
  apply length_zero_iff_nil in H2.
  lia.
- simpl.
  intros.
  apply app_eq_nil in H2.
  destruct H2.
  apply Forall_cons_iff in H0.
  destruct H0.
  apply length_zero_iff_nil in H2.
  lia.
- simpl.
  intros L Lz f1 f2 conc.
  apply Forall_cons_iff in f1, f2.
  destruct f1, f2.
  apply app_inv_same_length in conc.
  destruct conc.
  rewrite (IHl1 l2 L Lz H0 H2 H4), H3.
  tauto.
  lia.
Qed.

End Concat.

Section FlatMap.
Variable A: Type.
Variable B: Type.
Lemma flat_map_length: forall (f: A -> list B) (l: list A) (L: nat), (forall a, length (f a) = L) -> length (flat_map f l) = length l * L.
intros f l L H.
rewrite flat_map_concat_map.
assert (Forall (fun x : list B => length x = L) (map f l)).
rewrite Forall_map.
apply Forall_forall.
intros.
apply (H x).
rewrite (concat_same_length H0).
rewrite map_length.
tauto.
Qed.

Lemma flat_map_nth: forall (f: A -> list B) (l: list A) (L: nat) n def1 def2, (forall a, length (f a) = L) -> n < L * (length l) -> nth n (flat_map f l) def2 = nth (Nat.modulo n L) (f (nth (Nat.div n L) l def1)) def2.
intros f.
induction l.
- intros.
  simpl in H0.
  lia.
- intros.
  simpl flat_map.
  pose (Nat.lt_decidable n L).
  destruct d.
  rewrite app_nth1.
  rewrite Nat.div_small.
  rewrite Nat.mod_small.
  tauto.
  tauto.
  tauto.
  rewrite H.
  tauto.
  apply Nat.nlt_ge in H1.
  rewrite app_nth2.
  rewrite H.
  simpl in H0.
  assert (n - L < L * length l).
  lia.  
  rewrite (IHl L (n - L) def1 def2 H H2).
  pose (n' := n - L).
  fold n'.
  assert(n = n' + L).
  lia.
  rewrite H3.
  rewrite <- (Nat.mul_1_l L) at 3.
  rewrite Nat.mod_add.
  rewrite <- (Nat.mul_1_l L) at 4.
  rewrite Nat.div_add.
  rewrite Nat.add_1_r.
  simpl.
  tauto.
  lia.
  lia.
  rewrite H.
  lia.
  Qed.

End FlatMap.

Section For.

Variable A: Type.
Variable B: Type.
Variable C: Type.

Definition for1 (l1: list A) (f: A -> B) := map f l1.

Definition for2 (l1: list A) (l2: list B)(f: @binop A B C) := flat_map (fun a => map (fun b => f a b) l2) l1.




Theorem for2_length: forall l1 l2 f, length (for2 l1 l2 f) = (length l1) * (length l2).
unfold for2.
intros l1 l2 f.
assert((forall a : A,
    length ((fun a0 : A => map (fun b : B => f a0 b) l2) a) =
    (length l2))).
intros.
apply map_length.
rewrite (flat_map_length (fun a : A => map (fun b : B => f a b) l2) l1 H).
tauto.
Qed.

Lemma for2_nth: forall l1 l2 f n def1 def2, n < (length l1) * (length l2) -> nth n (for2 l1 l2 f) def2 = nth (Nat.modulo n (length l2)) (map (fun b : B => f (nth (n / length l2) l1 def1) b) l2) def2.
intros.
unfold for2.
assert (forall a : A,
    length ((fun a0 : A => map (fun b : B => f a0 b) l2) a) =
    (length l2)).
    intros.
apply map_length.
rewrite Nat.mul_comm in H.
rewrite (flat_map_nth (fun a => map (fun b => f a b) l2) l1 def1 def2 H0 H).
tauto.
Qed.

End For.

Section FirstSkip.

Variable A: Type.

Lemma firstn_change_idx: forall (l: list A) n1 n2, length l <= n1 -> length l <= n2 -> firstn n1 l = firstn n2 l.
intros l n1 n2 l1 l2.
rewrite firstn_all2.
rewrite firstn_all2.
tauto.
tauto.
tauto.
Qed.

End FirstSkip.

Section Grouped.

Variable A: Type.

Fixpoint to_grid (l: list A) (r: nat) (c: nat) :=
 match r with 
  | 0 => nil
  | S r' => firstn c l :: to_grid (skipn c l) r' c 
end.



Lemma to_grid_tail: forall (l: list A) r c, tail (to_grid l (S r) c) = to_grid (skipn c l) r c.
tauto.
Qed.

Lemma to_grid_small: forall r c l, r > 0 -> length l <= c -> concat (to_grid l r c) = firstn c l.
induction r.
- lia.
- intros c l useless lc.
  simpl.
  assert (r = 0 \/ r > 0) as choice.
  lia.
  destruct choice.
  rewrite H.
  simpl.
  apply app_nil_r.
  assert (concat (to_grid (skipn c l) r c) = nil).
  rewrite IHr.
  rewrite skipn_all2.
  rewrite firstn_nil.
  tauto.
  tauto.
  tauto.
  rewrite skipn_length.
  lia.
  rewrite H0.
  rewrite app_nil_r.
  tauto.
Qed.

Lemma to_grid_all: forall (l: list A) c, c >= length l -> to_grid l 1 c = l :: nil.
intros l c ge.
unfold to_grid.
rewrite firstn_all2.
tauto.
tauto.
Qed.

Lemma concat_to_grid: forall (r: nat) (c: nat) (l: list A), concat (to_grid l r c) = firstn (r * c) l.
induction r.
- simpl.
  tauto.
- intros c l.
  assert(r = 0 \/ r > 0).
  lia.
  destruct H.
  * rewrite H.
    simpl.
    rewrite app_nil_r.
    rewrite Nat.add_0_r.
    tauto.
  * assert(length l < c \/ length l >= c) as choice.
    lia.
    simpl.
    destruct choice as [c1 | c2].
      + assert (length l <= c).
        lia.
        rewrite (to_grid_small (skipn c l)) .
        rewrite skipn_all2, firstn_nil, app_nil_r.
        apply firstn_change_idx.
        tauto.
        lia.
        tauto.
        tauto.
        rewrite skipn_length.
        lia.
      + rewrite IHr.
        assert(firstn c l = firstn (S r * c) (firstn c l)).
        rewrite firstn_firstn.
        assert(r * c >= c).
        unfold ge.
        rewrite <- (Nat.mul_1_l) at 1.
        apply Nat.mul_le_mono_r.
        lia.
        rewrite Nat.min_r.
        tauto.
        assert (r * c <= S r * c).
        lia.
        lia.
        rewrite H0.
        pose (@firstn_app A (S r * c) (firstn c l) (skipn c l)).
        assert (S r * c - length (firstn c l) = r * c).
        assert (length (firstn c l) = c).
        rewrite firstn_length.
        apply Nat.min_l.
        lia.
        lia.
        rewrite H1 in e.
        rewrite <- e.
        rewrite firstn_skipn.
        tauto.
Qed.

Lemma to_grid_nil: forall r c, concat (to_grid nil r c) = nil.
intros r c.
rewrite concat_to_grid.
apply firstn_nil.
Qed.
  

Lemma concat_to_grid_le: forall (r: nat) (c: nat) (l: list A), length l <= r * c -> concat (to_grid l r c) = l.
intros r c l lrc.
rewrite concat_to_grid.
rewrite firstn_all2.
tauto.
tauto.
Qed.

Lemma to_grid_idempotent: forall r c l, to_grid (concat (to_grid l r c)) r c = to_grid l r c.
induction r.
- simpl.
  tauto.
- intros c l.
  assert(S r > 0).
  lia.
  assert (length l <= c \/ length l > c).
  lia.
  destruct H0 as [c1 | c2].
  pose (to_grid_small l H c1).
  rewrite e.
  simpl.
  rewrite firstn_firstn.
  rewrite Nat.min_l.
  rewrite skipn_firstn_comm.
  assert(c - c = 0).
  lia.
  rewrite H0.
  rewrite firstn_O.
  rewrite skipn_all2.
  tauto.
  tauto.
  lia.
  simpl.
  rewrite <- IHr at 3.
  rewrite skipn_app.
  rewrite skipn_firstn_comm.
  assert (c - c = 0).
  lia.
  rewrite H0.
  rewrite firstn_O.
  rewrite app_nil_l.
  rewrite firstn_length.
  rewrite Nat.min_l.
  rewrite H0.
  rewrite skipn_O.
  rewrite firstn_app.
  rewrite firstn_firstn.
  rewrite Nat.min_l.
  rewrite firstn_length.
  rewrite Nat.min_l.
  rewrite H0.
  rewrite firstn_O.
  rewrite app_nil_r.
  tauto.
  lia.
  lia.
  lia.
Qed.


Lemma to_grid_truncated: forall l r c, to_grid l r c = to_grid (firstn (r * c) l) r c.
intros l r c.
pose (concat_to_grid r c l).
rewrite <- e.
rewrite to_grid_idempotent.
tauto.
Qed.


Lemma to_grid_length: forall (r: nat) (c: nat) (l: list A), length (to_grid l r c) = r.
induction r.
- tauto.
- simpl.
  intros c l.
  rewrite IHr.
  tauto.
Qed.

Lemma to_grid_element_length: forall r c l e, length l = r * c -> In e (to_grid l r c) -> length e = c.
induction r.
- simpl.
  tauto.
- intros c l e di H.
  simpl in H.
  destruct H.
  * rewrite <- H.
    rewrite firstn_length.
    apply Nat.min_l.
    lia.
  * apply (IHr c (skipn c l) e).
    rewrite skipn_length.
    lia.
    tauto.
Qed. 






Definition grouped (l: list A) (n: nat) := to_grid l ((length l) /  n) n.

Lemma grouped_0 : forall l, grouped l 0 = nil.
intros.
unfold grouped.
simpl.
tauto.
Qed.

Lemma grouped_to_grid: forall (l: list A) r c, c > 0 -> length l = r * c -> grouped l c = to_grid l r c.
intros l r c gt lrc.
unfold grouped.
rewrite lrc.
rewrite Nat.div_mul.
tauto.
lia.
Qed.


Lemma grouped_small: forall l n, 
length l < n -> grouped l n = nil.
intros l n len.
apply Nat.div_small in len.
unfold grouped.
rewrite len.
tauto.
Qed.

Lemma grouped_nil : forall n, grouped nil n = nil.
intros n.
assert(n = 0 \/ n > 0).
lia.
destruct H.
rewrite H.
unfold grouped.
tauto.
apply grouped_small.
simpl.
lia.
Qed.

Lemma concat_grouped: forall l n, concat (grouped l n) = firstn (length l / n * n) l .
intros l n.
unfold grouped.
apply concat_to_grid.
Qed.

Lemma grouped_all: forall (l: list A), l <> nil -> grouped l (length l) = l :: nil.
intros l nl.
unfold grouped.
rewrite Nat.div_same.
rewrite to_grid_all.
tauto.
lia.
apply (not_iff_compat (length_zero_iff_nil l)).
tauto.
Qed.

Lemma grouped_length: forall (n: nat) (l: list A) , length (grouped l n) = length l / n.
unfold grouped.
intros.
apply to_grid_length.
Qed.

Lemma grouped_truncated: forall l n, grouped l n = grouped (firstn (length l / n * n) l) n.
intros l n.
assert (n = 0 \/ n > 0).
lia.
destruct H.
rewrite H.
rewrite grouped_0, grouped_0.
tauto.
unfold grouped.
rewrite firstn_length.
rewrite Nat.min_l.
rewrite Nat.div_mul.
apply (to_grid_truncated l (length l / n) n).
lia.
apply Ndiv_mul_le.
lia.
Qed.



Lemma grouped_element_length:  forall l n e, In e (grouped l n) -> length e = n.
intros.
assert(n = 0 \/ n > 0).
lia.
destruct H0 as [c1 | c2].
rewrite c1 in H.
rewrite grouped_0 in H.
simpl in H.
tauto.
rewrite grouped_truncated in H.
unfold grouped in H.
apply to_grid_element_length in H.
tauto.
rewrite firstn_length, Nat.min_l.
rewrite Nat.div_mul.
tauto.
lia.
apply Ndiv_mul_le.
lia.
Qed.

End Grouped.

Section GroupedMap.

Variable A B: Type.

Lemma to_grid_map: forall r c l (f: A -> B), map (map f) (to_grid l r c) = to_grid (map f l) r c.
induction r.
- tauto.
- intros c l f.
  simpl.
  rewrite firstn_map.
  rewrite IHr.
  rewrite skipn_map.
  tauto.
Qed.
  
Lemma to_grid_concat_map: forall r c l (f: A -> B), map f (concat (to_grid l r c)) = concat (to_grid (map f l) r c).
intros r c l f.
rewrite concat_map.
rewrite to_grid_map.
tauto.
Qed.

Lemma grouped_map: forall n l (f: A -> B), map (map f) (grouped l n) = grouped (map f l) n.
intros n l f.
unfold grouped.
rewrite map_length.
apply to_grid_map.
Qed.
  
Lemma grouped_concat_map: forall n l (f: A -> B), map f (concat (grouped l n)) = concat (grouped (map f l) n).
intros n l f.
unfold grouped.
rewrite map_length.
apply to_grid_concat_map.
Qed.

Lemma to_grid_combine: forall r c (l1: list A) (l2: list B), length l1 = length l2 -> to_grid (combine l1 l2) r c = list_binop (to_grid l1 r c) (to_grid l2 r c) (@combine A B).
induction r.
- tauto.
- intros c l1 l2 H.
  simpl.
  rewrite list_binop_cons.
  rewrite combine_firstn.
  rewrite combine_skipn.
  rewrite (IHr c (skipn c l1) (skipn c l2)).
  tauto.
  rewrite skipn_length.
  rewrite skipn_length.
  lia.
  lia.
Qed.

Lemma grouped_combine: forall n (l1: list A) (l2: list B), length l1 = length l2 -> grouped (combine l1 l2) n = list_binop (grouped l1 n) (grouped l2 n) (@combine A B).
intros n l1 l2 leq.
unfold grouped.
rewrite to_grid_combine.
rewrite combine_length.
rewrite min_l.
rewrite leq.
tauto.
lia.
tauto.
Qed.

End GroupedMap.






 