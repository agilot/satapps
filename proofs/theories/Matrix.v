
From Coq Require Import PeanoNat List Decidable Bool FunctionalExtensionality Min Lia.
Require Import ListSpec2.

Section Matrices.

Definition Matrix {T: Type} : Type := nat * nat * list T.

Definition r {T: Type} (M: @Matrix T) := fst (fst M).
Definition c {T: Type} (M: @Matrix T) := snd (fst M).
Definition arr {T: Type} (M: @Matrix T) := snd M.
Definition shape {T: Type} (M: @Matrix T) := (r M, c M).
Definition is_valid {T: Type} (M: @Matrix T) := length (arr M) = (r M) * (c M).

Theorem matrix_eq {T: Type}: forall (M: @Matrix T), M = (r M, c M, arr M).
intros.
unfold r, c, arr.
destruct M.
destruct p.
simpl.
tauto.
Qed.

Theorem shape_eq {A B: Type}: forall (M1: @Matrix A) (M2: @Matrix B), shape M1 = shape M2 <-> (r M1 = r M2 /\ c M1 = c M2).
unfold shape.
intros M1 M2.
split.
- intro eq_sh.
pose (f_equal fst eq_sh).
simpl in e.
pose (f_equal snd eq_sh).
simpl in e0.
tauto.
- intro eq_sh.
destruct eq_sh.
rewrite H.
rewrite H0.
tauto.
Qed.

Definition is_empty {T: Type} (M: @Matrix T) := r M = 0 \/ c M = 0.

Lemma is_empty_is_valid_1 {T: Type} : forall (M: @Matrix T), is_empty M -> (is_valid M <-> arr M = nil).
intros M emp.
unfold is_valid.
destruct emp.
rewrite H.
rewrite Nat.mul_0_l.
apply length_zero_iff_nil.
rewrite H.
rewrite Nat.mul_0_r.
apply length_zero_iff_nil.
Qed.

Lemma is_empty_is_valid_2 {T: Type} : forall (M: @Matrix T), is_valid M -> (is_empty M <-> arr M = nil).
unfold is_valid, is_empty.
intros M isv.
split.
- intros emp.
  destruct emp.
  rewrite H in isv.
  rewrite Nat.mul_0_l in isv.
  apply length_zero_iff_nil.
  tauto.
  rewrite H in isv.
  rewrite Nat.mul_0_r in isv.
  apply length_zero_iff_nil.
  tauto.
- intros arrnil.
  apply length_zero_iff_nil in arrnil.
  rewrite arrnil in isv.
  apply eq_sym in isv.
  apply (Mult.mult_is_O (r M) (c M)).
  tauto.
Qed.

End Matrices.

Section MatrixOps.

Definition in_bounds {T: Type} (M: @Matrix T) (i: nat) (j: nat) := i < (r M) /\ j < (c M).

Lemma in_bounds_is_valid_access {T: Type} : forall (M: @Matrix T) (i: nat) (j: nat), is_valid M -> in_bounds M i j -> (i * (c M) + j < length (arr M)).
intros M i j is_v p.
rewrite is_v.
destruct p as [p0 p1].
apply (Nat.add_lt_mono_l j (c M) (i * (c M))) in p1.
rewrite <- (Nat.mul_1_l (c M) ) in p1 at 3.
rewrite <- Nat.mul_add_distr_r in p1.
rewrite Nat.add_1_r in p1.
pose (Lt.lt_le_S i (r M) p0) as l.
apply (Nat.mul_le_mono_r _ _ (c M)) in l.
lia.
Qed.

Lemma out_of_bounds_is_not_valid_access {T: Type} : forall (M: @Matrix T) (i: nat) (j: nat), is_valid M -> i >= (r M) -> (i * (c M) + j >= length (arr M)).
unfold ge.
intros M i j is_v p.
rewrite is_v.
apply (Nat.mul_le_mono_r _ _ (c M)) in p.
lia.
Qed.

Lemma is_empty_not_in_bounds {T: Type} : forall (M: @Matrix T), is_empty M  -> (forall i j, ~in_bounds M i j).
intros M emp.
unfold in_bounds.
unfold is_empty in emp.
lia.
Qed.

Lemma not_in_bounds_ge {T: Type} : forall (M: @Matrix T) i j, ~in_bounds M i j -> (forall i' j', i' >= i -> j' >= j -> ~in_bounds M i' j').
unfold in_bounds.
lia.
Qed.

Lemma not_in_bounds_0 {T: Type} : forall (M: @Matrix T), ~in_bounds M 0 0 -> (forall i j, ~in_bounds M i j).
unfold in_bounds.
lia.
Qed.

Lemma not_in_bounds_is_empty {T: Type} : forall (M: @Matrix T), ~in_bounds M 0 0 -> is_empty M.
unfold in_bounds, is_empty.
intros ninb M.
lia.
Qed.

Definition Apply_opt {T: Type} (M: Matrix)(i: nat)(j: nat): option T := nth_error (arr M) (i * (c M) + j).
Definition Apply_def {T: Type} (M: Matrix)(i: nat)(j: nat)(def: T): T := nth (i * (c M) + j) (arr M) def.

Theorem apply_opt_apply_def {T: Type}: forall (M: Matrix) i j (def: T), is_valid M -> in_bounds M i j -> Apply_opt M i j = Some(Apply_def M i j def).
intros M i j def is_v in_b.
unfold Apply_opt.
unfold Apply_def.
apply nth_error_nth_lt.
apply in_bounds_is_valid_access.
tauto.
tauto.
Qed.

Theorem apply_def_indep {T: Type}: forall (M: Matrix) i j (def1: T) (def2: T), is_valid M -> in_bounds M i j -> Apply_def M i j def1 = Apply_def M i j def2.
intros M i j def1 def2 is_v in_b.
unfold Apply_def.
apply nth_indep.
apply in_bounds_is_valid_access.
tauto.
tauto.
Qed.

Theorem apply_def_out_of_bounds {T: Type}: forall (M: @Matrix T) i j def, is_valid M -> i >= r M -> Apply_def M i j def = def.
intros M i j def isv ir.
unfold Apply_def.
apply nth_overflow. 
apply out_of_bounds_is_not_valid_access.
tauto.
tauto.
Qed.

Theorem apply_def_is_empty {T: Type}: forall (M: @Matrix T), is_empty M -> is_valid M -> forall i j def, Apply_def M i j def = def.
intros M emp isv i j def.
unfold Apply_def.
apply (is_empty_is_valid_1 M emp) in isv.
rewrite isv.
induction (i * (c M) + j).
tauto.
tauto.
Qed.

Theorem apply_opt_none_ge {T: Type}: forall (M: @Matrix T) i j, Apply_opt M i j = None -> forall i' j', i' >= i -> j' >= j -> Apply_opt M i' j' = None.
unfold Apply_opt, ge.
intros M i j appnone i' j' gei gej.
apply nth_error_None.
apply nth_error_None in appnone.
assert(i * c M + j <= i * c M + j').
lia.
assert(i * c M + j' <= i' * c M + j').
rewrite <- Nat.add_le_mono_r.
apply (Nat.mul_le_mono_r i i' (c M)).
tauto.
lia.
Qed. 

Theorem apply_opt_none {T: Type}: forall (M: @Matrix T), Apply_opt M 0 0 = None -> forall i j, Apply_opt M i j = None.
intros M apply0 i j.
pose (apply_opt_none_ge M 0 0 apply0 i j).
apply e.
lia.
lia.
Qed.

Theorem apply_opt_out_of_bounds {T: Type}: forall (M: @Matrix T) i j, is_valid M -> i >= r M -> Apply_opt M i j = None.
intros M i j isv ir.
unfold Apply_opt.
apply nth_error_None.
apply out_of_bounds_is_not_valid_access.
tauto.
tauto.
Qed.


Theorem apply_opt_is_empty_1 {T: Type}: forall (M: @Matrix T), is_empty M -> is_valid M -> forall i j, Apply_opt M i j = None.
intros M emp isv i j.
unfold Apply_opt.
apply (is_empty_is_valid_1 M emp) in isv.
rewrite isv.
rewrite nth_error_None.
simpl.
lia.
Qed.

Theorem apply_opt_is_empty_2 {T: Type}: forall (M: @Matrix T), is_valid M -> Apply_opt M 0 0 = None -> is_empty M.
unfold Apply_opt, is_empty, is_valid.
intros M isv app0.
rewrite Nat.mul_0_l in app0.
rewrite Nat.add_0_l in app0.
apply nth_error_None in app0.
assert (length (arr M) = 0).
lia.
rewrite H in isv.
lia.
Qed.

Theorem apply_opt_is_empty_3 {T: Type}: forall (M: @Matrix T), is_empty M -> Apply_opt M 0 0 = None -> is_valid M.
unfold Apply_opt, is_empty, is_valid.
intros M isv app0.
rewrite Nat.mul_0_l in app0.
rewrite Nat.add_0_l in app0.
apply nth_error_None in app0.
assert (length (arr M) = 0).
lia.
rewrite H.
lia.
Qed.

Definition Update {T: Type} (M: Matrix)(i: nat)(j: nat)(v: T): Matrix := (r M, c M, update (arr M) (i * (c M) + j) v).

Theorem update_is_valid {T: Type}: forall (M: @Matrix T) i j v, is_valid M -> is_valid (Update M i j v).
intros M i j v is_valid_M.
unfold is_valid.
unfold Update.
unfold r.
unfold c.
simpl.
unfold is_valid in is_valid_M.
rewrite update_length.
tauto.
Qed.

Theorem update_in_bounds {T: Type}: forall (M: @Matrix T) i j v i' j', in_bounds M i' j' -> in_bounds (Update M i j v) i' j'.
tauto. Qed.

Theorem update_out_of_bounds {T: Type}: forall (M: @Matrix T) i j v, is_valid M -> i >= r M -> Update M i j v = M.
intros M i j v isv ir.
unfold Update.
rewrite update_overflow.
apply eq_sym.
apply matrix_eq.
apply out_of_bounds_is_not_valid_access.
tauto.
tauto.
Qed.

Theorem update_empty {T: Type}: forall (M: @Matrix T) v, is_valid M -> is_empty M -> (forall i j, Update M i j v = M).
intros M v isv ise i j.
unfold Update.
rewrite update_overflow.
apply eq_sym.
apply matrix_eq.
pose ((proj1 (is_empty_is_valid_1 M ise)) isv).
apply length_zero_iff_nil in e.
rewrite e.
lia.
Qed.

Theorem apply_opt_update {T: Type}: forall (M : Matrix) i j (v: T), is_valid M -> in_bounds M i j -> Apply_opt (Update M i j v) i j  = Some v.
intros M i j v is_valid_M in_bounds_M.
pose (in_bounds_is_valid_access _ _ _ is_valid_M in_bounds_M).
apply nth_error_update.
tauto.
Qed.

Theorem apply_def_update {T: Type}: forall (M : Matrix) i j (v: T) (def: T), (is_valid M) -> in_bounds M i j -> Apply_def (Update M i j v) i j def  = v.
intros M i j v def is_valid_M in_bounds.
pose (in_bounds_is_valid_access _ _ _ is_valid_M in_bounds).
apply nth_update.
tauto.
Qed.

Definition Map {A B: Type} (M: @Matrix A) (f: A -> B): @Matrix B := (r M, c M, map f (arr M)).

Theorem map_is_valid{A B: Type}: forall (M: Matrix) (f: A -> B), is_valid M -> is_valid (Map M f).
intros M is_valid_M.
unfold is_valid.
unfold Map.
unfold r.
unfold c.
simpl.
unfold is_valid in is_valid_M.
rewrite map_length.
tauto.
Qed.

Theorem map_in_bounds {A B: Type}: forall (M: Matrix) (f: A -> B) i j, in_bounds M i j -> in_bounds (Map M f) i j.
intros M f i j; tauto. Qed.

Theorem map_empty {A B: Type}: forall (M: Matrix) (f: A -> B), is_empty M -> is_empty (Map M f).
tauto. Qed. 

Theorem apply_opt_map {A B: Type}: forall (M: Matrix) (f: A -> B) i j, Apply_opt (Map M f) i j = (opt_f f) (Apply_opt M i j).
intros M f i j; apply nth_error_map. Qed.

Theorem apply_def_map {A B: Type}: forall (M: @Matrix A) (f: A -> B) i j (def: A), Apply_def (Map M f) i j (f def) = f (Apply_def M i j def).
intros M f i j def; apply map_nth. Qed.

Theorem map_update {A B: Type}: forall (M: @Matrix A) (f: A -> B) i j v, Map (Update M i j v) f = Update (Map M f) i j (f v).
intros M f i j v.
unfold Map, Update, r, c.
simpl.
rewrite update_map.
tauto.
Qed.

Theorem mat_map_map {A B C: Type}: forall M (f: A -> B) (g: B -> C), Map (Map M f) g = Map M (comp g f).
intros M f g.
unfold Map, r, c, arr, comp.
simpl.
rewrite (map_map f g (snd M)).
tauto.
Qed.

Definition Zip {A B: Type} (M1: @Matrix A) (M2: @Matrix B) := (r M1, c M1, combine (arr M1) (arr M2)).

Theorem zip_is_valid {A B : Type}: forall (M1: @Matrix A) (M2: @Matrix B),  is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> is_valid (Zip M1 M2).
unfold Zip, is_valid, r, c.
simpl.
intros M1 M2 isv1 isv2 sheq.
rewrite combine_length.
apply (proj1 (shape_eq M1 M2)) in sheq.
unfold r, c in sheq.
destruct sheq.
rewrite isv1.
rewrite isv2.
rewrite H.
rewrite H0.
rewrite Nat.min_id.
tauto.
Qed.

Theorem zip_in_bounds {A B: Type}: forall (M1: @Matrix A) (M2: @Matrix B) i j, in_bounds M1 i j -> in_bounds M2 i j -> in_bounds (Zip M1 M2) i j.
intros M f i j; tauto. Qed.

Theorem apply_opt_zip {A B: Type}: forall (M1: @Matrix A) (M2: @Matrix B) i j, is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> Apply_opt (Zip M1 M2) i j = fact_opt_pair ((Apply_opt M1 i j), (Apply_opt M2 i j)).
unfold is_valid.
intros M1 M2 i j isv1 isv2 sheq.
apply shape_eq in sheq.
destruct sheq.
unfold Apply_opt, Zip.
rewrite H0.
simpl.
rewrite combine_nth_error.
unfold c.
simpl.
tauto.
rewrite isv1, isv2, H, H0.
tauto.
Qed.

Theorem apply_def_zip {A B: Type}: forall (M1: @Matrix A) (M2: @Matrix B) i j d1 d2, is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> Apply_def (Zip M1 M2) i j (d1, d2) = ((Apply_def M1 i j d1), (Apply_def M2 i j d2)).
unfold Apply_def, Zip, is_valid.
intros M1 M2 i j d1 d2 isv1 isv2 sheq.
apply shape_eq in sheq.
destruct sheq.
simpl.
rewrite combine_nth.
rewrite H0.
tauto.
rewrite isv1, isv2, H, H0.
tauto.
Qed.

Theorem zip_update {A B: Type}: forall (M1: @Matrix A) (M2: @Matrix B) i j d1 d2, shape M1 = shape M2 -> Update (Zip M1 M2) i j (d1, d2) = Zip (Update M1 i j d1) (Update M2 i j d2).
unfold is_valid, Update, Zip, r, c, arr.
intros M1 M2 i j d1 d2 sheq.
simpl.
apply shape_eq in sheq.
unfold r, c in sheq.
destruct sheq.
rewrite combine_update.
rewrite H0.
tauto.
Qed.


Definition MatBinop {A B C: Type} (bin: @binop A B C): binop := fun M1 => fun M2 =>
Map (Zip M1 M2) (bin_to_pair bin).

Theorem mat_binop_is_valid {A B C: Type}: forall M1 M2 (bin: @binop A B C), is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> is_valid (MatBinop bin M1 M2).
intros M1 M2 bin isv1 isv2 sheq.
apply map_is_valid.
apply zip_is_valid.
tauto.
tauto.
tauto.
Qed.

Theorem mat_binop_in_bounds {A B C: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (bin: @binop A B C)  i j, in_bounds M1 i j -> in_bounds M2 i j -> in_bounds (MatBinop bin M1 M2) i j.
intros M f i j; tauto. Qed.

Theorem mat_binop_list_binop {A B C: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (bin: @binop A B C), arr (MatBinop bin M1 M2) = list_binop (arr M1) (arr M2) bin.
intros M1 M2 bin.
tauto.
Qed.

Theorem apply_opt_mat_binop {A B C: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (bin: @binop A B C) i j , is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> Apply_opt (MatBinop bin M1 M2) i j = (opt_f (bin_to_pair bin)) (fact_opt_pair ((Apply_opt M1 i j), (Apply_opt M2 i j))).
intros M1 M2 bin i j isv1 isv2 sheq.
unfold MatBinop.
rewrite apply_opt_map.
rewrite apply_opt_zip.
tauto.
tauto.
tauto.
tauto.
Qed.

Theorem apply_def_mat_binop {A B C: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (bin: @binop A B C) i j d1 d2, is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> Apply_def (MatBinop bin M1 M2) i j (bin d1 d2) = bin (Apply_def M1 i j d1) (Apply_def M2 i j d2).
intros M1 M2 bin i j d1 d2 isv1 isv2 sheq.
unfold MatBinop.
pose (apply_def_map (Zip M1 M2) (bin_to_pair bin) i j (d1, d2)).
unfold bin_to_pair in e.
simpl in e.
unfold bin_to_pair.
rewrite e.
rewrite apply_def_zip.
simpl.
tauto.
tauto.
tauto.
tauto.
Qed.

Theorem mat_binop_update {A B C: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (bin: @binop A B C) i j d1 d2, shape M1 = shape M2 -> Update (MatBinop bin M1 M2) i j (bin d1 d2) = MatBinop bin (Update M1 i j d1) (Update M2 i j d2).
intros M1 M2 bi i j d1 d2 sheq.
unfold MatBinop.
pose (map_update (Zip M1 M2) (bin_to_pair bi) i j (d1, d2)).
unfold bin_to_pair in e.
simpl in e.
unfold bin_to_pair.
rewrite <- e.
rewrite zip_update.
tauto.
tauto.
Qed.

Theorem mat_binop_map {A B C D: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (bin: @binop A B C) (f: C -> D), shape M1 = shape M2 -> Map (MatBinop bin M1 M2) f = MatBinop (comp_f_bin f bin) M1 M2.
intros M1 M2 bin f sheq.
unfold MatBinop.
rewrite mat_map_map.
rewrite bin_to_pair_comp_f_bin.
tauto.
Qed.

Definition mat_binop_comm {A B: Type}: forall (f: @binop A A B) M1 M2, is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> comm f -> MatBinop f M1 M2 = MatBinop f M2 M1.
intros f M1 M2 isv1 isv2 shap_eq H.
rewrite matrix_eq.
rewrite mat_binop_list_binop.
unfold MatBinop.
unfold Map, Zip, r, c.
simpl.
rewrite list_binop_comm.
apply shape_eq in shap_eq.
unfold r, c in shap_eq.
destruct shap_eq.
rewrite H0, H1.
tauto.
unfold is_valid in isv1.
unfold is_valid in isv2.
rewrite isv1.
rewrite isv2.
apply shape_eq in shap_eq.
lia.
tauto.
Qed.

Definition VConcat {A: Type} (M1: @Matrix A) (M2: @Matrix A) := ((r M1) + (r M2), c M1, (arr M1) ++ (arr M2)).

Theorem vconcat_is_valid {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A),
is_valid M1 -> is_valid M2 -> c M1 = c M2 -> is_valid (VConcat M1 M2).
unfold is_valid, VConcat, r, c, arr.
simpl.
intros M1 M2 isv1 isv2 req.
rewrite app_length.
lia.
Qed.

Theorem vconcat_empty_l {A: Type}: forall (M1: @Matrix A) M2, is_valid M1 -> is_valid M2 -> c M1 = c M2-> is_empty M1 -> c M2 > 0 -> VConcat M1 M2 = M2.
intros M1 M2 isv1 isv2 ceq ise cm2.
assert (arr (VConcat M1 M2) = arr M2).
apply (is_empty_is_valid_1 M1 ise) in isv1.
unfold VConcat.
rewrite isv1, app_nil_l.
unfold arr.
tauto.
assert(c
      (VConcat M1 M2) =
    c M2).
    unfold VConcat, c.
    tauto.
assert (r (VConcat M1 M2) = r M2).
pose (vconcat_is_valid M1 M2 isv1 isv2 ceq).
unfold is_valid in i.
apply (f_equal (@length A)) in H.
unfold is_valid in isv2.
rewrite isv2, i in H.
rewrite H0 in H.
apply (Nat.mul_cancel_r) in H.
tauto.
lia.
rewrite matrix_eq.
rewrite (matrix_eq (VConcat M1 M2)).
apply pair_equal_spec.
split.
apply pair_equal_spec.
tauto.
tauto.
Qed.

Theorem vconcat_empty_r {A: Type}: forall (M1: @Matrix A) M2, is_valid M1 -> is_valid M2 -> c M1 = c M2-> is_empty M2 -> c M1 > 0 -> VConcat M1 M2 = M1.
intros M1 M2 isv1 isv2 ceq ise cm1.
assert (arr (VConcat M1 M2) = arr M1).
apply (is_empty_is_valid_1 M2 ise) in isv2.
unfold VConcat.
rewrite isv2, app_nil_r.
unfold arr.
tauto.
assert(c
      (VConcat M1 M2) =
    c M1).
    unfold VConcat, c.
    tauto.
assert (r (VConcat M1 M2) = r M1).
pose (vconcat_is_valid M1 M2 isv1 isv2 ceq).
unfold is_valid in i.
apply (f_equal (@length A)) in H.
unfold is_valid in isv1.
rewrite isv1, i in H.
rewrite H0 in H.
apply (Nat.mul_cancel_r) in H.
tauto.
lia.
rewrite matrix_eq.
rewrite (matrix_eq (VConcat M1 M2)).
apply pair_equal_spec.
split.
apply pair_equal_spec.
tauto.
tauto.
Qed.

Theorem vconcat_map {A B: Type}: forall (M1: @Matrix A) (M2: @Matrix A) (f: A -> B), Map (VConcat M1 M2) f = VConcat (Map M1 f) (Map M2 f).
intros.
unfold Map, VConcat, r, c.
simpl.
rewrite map_app.
tauto.
Qed.

Theorem vconcat_zip {A B: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (M3: @Matrix A) (M4: @Matrix B), is_valid M1 -> is_valid M2 -> shape M1 = shape M2 ->
VConcat (Zip M1 M2) (Zip M3 M4) = Zip (VConcat M1 M3) (VConcat M2 M4).
unfold VConcat, Zip, r, c, is_valid.
simpl.
intros.
rewrite combine_app.
tauto.
apply shape_eq in H1.
destruct H1.
lia.
Qed.

Theorem vconcat_binop {A B C: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (M3: @Matrix A) (M4: @Matrix B) (bin: @binop A B C), is_valid M1 -> is_valid M2 -> shape M1 = shape M2 ->
VConcat (MatBinop bin M1 M2) (MatBinop bin M3 M4) = MatBinop bin (VConcat M1 M3) (VConcat M2 M4).
intros M1 M2 M3 M4 bin isv1 isv2 sheq.
unfold MatBinop.
rewrite <- vconcat_map.
rewrite <- vconcat_zip.
tauto.
tauto.
tauto.
tauto.
Qed.


Theorem vconcat_apply_def_1 {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A) i j def, is_valid M1 -> in_bounds M1 i j -> Apply_def (VConcat M1 M2) i j def = Apply_def M1 i j def.

intros M1 M2 i j def isv1 b.
apply in_bounds_is_valid_access in b.
unfold Apply_def, VConcat, r, c, arr.
simpl.
apply app_nth1.
unfold c, arr in b.
tauto.
tauto.
Qed.

Theorem vconcat_apply_def_2 {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A) i j def, is_valid M1 -> c M1 = c M2 -> r M1 <= i -> Apply_def (VConcat M1 M2) i j def = Apply_def M2 (i - (r M1)) j def.

intros M1 M2 i j def isv1 ceq b.
unfold Apply_def, VConcat.
unfold c at 1.
unfold arr at 3.
simpl.
rewrite ceq.
assert ((i - r M1) * c M2 + j = i * c M2 + j - r M1 * c M1).
rewrite Nat.mul_sub_distr_r.
rewrite <- Nat.add_sub_swap.
rewrite ceq.
tauto.
apply Nat.mul_le_mono_r.
tauto.
rewrite H.
rewrite <- isv1.
apply app_nth2.
rewrite <- ceq.
apply out_of_bounds_is_not_valid_access.
tauto.
tauto.
Qed.

Theorem vconcat_apply_opt_1 {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A) i j, is_valid M1 -> in_bounds M1 i j -> Apply_opt (VConcat M1 M2) i j = Apply_opt M1 i j.
intros M1 M2 i j isv1 b.
apply in_bounds_is_valid_access in b.
unfold Apply_opt, VConcat, r, c, arr.
simpl.
apply app_nth_error_1.
unfold c, arr in b.
tauto.
tauto.
Qed.

Theorem vconcat_apply_opt_2 {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A) i j, is_valid M1 -> c M1 = c M2 -> r M1 <= i -> Apply_opt (VConcat M1 M2) i j = Apply_opt M2 (i - (r M1)) j.

intros M1 M2 i j isv1 ceq b.
unfold Apply_opt, VConcat.
unfold c at 1.
unfold arr at 3.
simpl.
rewrite ceq.
assert ((i - r M1) * c M2 + j = i * c M2 + j - r M1 * c M1).
rewrite Nat.mul_sub_distr_r.
rewrite <- Nat.add_sub_swap.
rewrite ceq.
tauto.
apply Nat.mul_le_mono_r.
tauto.
rewrite H.
rewrite <- isv1.
apply app_nth_error_2.
rewrite <- ceq.
apply out_of_bounds_is_not_valid_access.
tauto.
tauto.
Qed.

Definition HConcat {A: Type} (M1: @Matrix A) (M2: @Matrix A) := (r M1, c M1 + c M2, 
match c M1, c M2 with
| 0, _ => arr M2
| _, 0 => arr M1
| S m, S m' => concat (list_binop (grouped (arr M1) (c M1)) (grouped (arr M2) (c M2)) (@app A))
end).


Theorem hconcat_is_valid {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A),
is_valid M1 -> is_valid M2 -> r M1 = r M2 -> is_valid (HConcat M1 M2).
unfold is_valid, HConcat, r, c, arr.
intros M1 M2.
destruct (snd (fst M1)), (snd (fst M2)).
- simpl.
  lia.
- simpl.
  lia.
- simpl.
  lia.
- simpl.
  intros isv1 isv2 req.
  rewrite (@concat_same_length A _ (S n + S n0)).
  rewrite list_binop_length.
  rewrite grouped_length.
  rewrite isv1.
  rewrite Nat.div_mul.
  tauto.
  lia.
  rewrite grouped_length, grouped_length, isv1, isv2, Nat.div_mul, Nat.div_mul.
  tauto.
  lia.
  lia.
  unfold list_binop.
  apply Forall_map.
  apply Forall_forall.
  intros x inx.
  unfold bin_to_pair.
  rewrite app_length.
  rewrite (surjective_pairing x) in inx.
  apply combine_In in inx.
  destruct inx.
  apply grouped_element_length in H.
  apply grouped_element_length in H0.
  lia.
  Qed.
  
Theorem hconcat_0_l {A: Type} : forall (M1: @Matrix A) M2, is_valid M1 -> is_valid M2 -> r M1 = r M2-> is_empty M1 -> r M2 > 0 -> HConcat M1 M2 = M2.
intros M1 M2 isv1 isv2 ceq ise cm2.
assert(arr M1 = nil).
apply ((proj1 (is_empty_is_valid_1 M1 ise))isv1).
assert(is_valid (HConcat M1 M2)).
apply (hconcat_is_valid M1 M2 isv1 isv2 ceq).
assert(c M1 = 0) as c1.
unfold is_empty in ise.
rewrite <- ceq in cm2.
lia.
assert (arr (HConcat M1 M2) = arr M2).
unfold HConcat.
rewrite c1, ceq.
rewrite Nat.add_0_l.
unfold arr.
simpl.
tauto.
assert(r (HConcat M1 M2) = r M2).
unfold HConcat.
rewrite ceq.
unfold r, c.
simpl.
tauto.
assert(c (HConcat M1 M2) = c M2).
unfold HConcat, r, c.
simpl.
unfold c in c1.
rewrite c1.
lia.
rewrite matrix_eq.
rewrite <- H1, <- H2, <- H3.
apply matrix_eq.
Qed.

Theorem hconcat_0_r {A: Type} : forall (M1: @Matrix A) M2, is_valid M1 -> is_valid M2 -> r M1 = r M2-> is_empty M2 -> r M1 > 0 -> HConcat M1 M2 = M1.
intros M1 M2 isv1 isv2 ceq ise cm1.
assert(arr M2 = nil).
apply ((proj1 (is_empty_is_valid_1 M2 ise))isv2).
assert(is_valid (HConcat M1 M2)).
apply (hconcat_is_valid M1 M2 isv1 isv2 ceq).
assert(c M2 = 0) as c1.
unfold is_empty in ise.
rewrite ceq in cm1.
lia.
assert (arr (HConcat M1 M2) = arr M1).
unfold HConcat.
rewrite c1, ceq.
rewrite Nat.add_0_r.
unfold arr.
simpl.
assert(c M1 = 0 -> snd M1 = nil).
intros.
assert(is_empty M1).
unfold is_empty.
tauto.
apply is_empty_is_valid_1 in H2.
apply H2 in isv1.
unfold arr in isv1.
tauto.
unfold arr in H.
destruct (c M1).
rewrite H1.
tauto.
tauto.
tauto.
assert(r (HConcat M1 M2) = r M1).
unfold HConcat.
rewrite ceq.
unfold r, c.
simpl.
tauto.
assert(c (HConcat M1 M2) = c M1).
unfold HConcat, r, c.
simpl.
unfold c in c1.
rewrite c1.
lia.
rewrite matrix_eq.
rewrite <- H1, <- H2, <- H3.
apply matrix_eq.
Qed.


Theorem hconcat_map {A B: Type}: forall (M1: @Matrix A) (M2: @Matrix A) (f: A -> B), Map (HConcat M1 M2) f = HConcat (Map M1 f) (Map M2 f).
intros M1 M2 f.
unfold Map, HConcat, r, c.
simpl.
destruct (snd (fst M1)).
tauto.
destruct (snd (fst M2)).
tauto. 
rewrite <- grouped_map, <- grouped_map.
rewrite concat_map.
rewrite (list_binop_map_linear _ _ (app_linear f)).
tauto.
Qed.

Theorem hconcat_zip {A B: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (M3: @Matrix A) (M4: @Matrix B), is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> shape M3 = shape M4 ->
HConcat (Zip M1 M2) (Zip M3 M4) = Zip (HConcat M1 M3) (HConcat M2 M4).
unfold HConcat, Zip, is_valid, shape, r, c.
simpl.
intros M1 M2 M3 M4 l1 l2 sheq1 sheq2.
apply pair_equal_spec in sheq1, sheq2.
destruct sheq1 as [req1 ceq1], sheq2 as [req2 ceq2]. 
destruct (snd (fst M1)).
- rewrite <- ceq1.
  tauto.
- destruct (snd (fst M3)).
  + rewrite <- ceq1, <- ceq2. 
    tauto.
  + rewrite <- ceq1, <- ceq2.
    rewrite grouped_combine, grouped_combine.
    

rewrite combine_app.
tauto.
apply shape_eq in H1.
destruct H1.
lia.
Qed.

Theorem hconcat_binop {A B C: Type}: forall (M1: @Matrix A) (M2: @Matrix B) (M3: @Matrix A) (M4: @Matrix B) (bin: @binop A B C), is_valid M1 -> is_valid M2 -> shape M1 = shape M2 ->
VConcat (MatBinop bin M1 M2) (MatBinop bin M3 M4) = MatBinop bin (VConcat M1 M3) (VConcat M2 M4).
intros M1 M2 M3 M4 bin isv1 isv2 sheq.
unfold MatBinop.
rewrite <- vconcat_map.
rewrite <- vconcat_zip.
tauto.
tauto.
tauto.
tauto.
Qed.


Theorem hconcat_apply_def_1 {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A) i j def, is_valid M1 -> in_bounds M1 i j -> Apply_def (VConcat M1 M2) i j def = Apply_def M1 i j def.

intros M1 M2 i j def isv1 b.
apply in_bounds_is_valid_access in b.
unfold Apply_def, VConcat, r, c, arr.
simpl.
apply app_nth1.
unfold c, arr in b.
tauto.
tauto.
Qed.

Theorem hconcat_apply_def_2 {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A) i j def, is_valid M1 -> c M1 = c M2 -> r M1 <= i -> Apply_def (VConcat M1 M2) i j def = Apply_def M2 (i - (r M1)) j def.

intros M1 M2 i j def isv1 ceq b.
unfold Apply_def, VConcat.
unfold c at 1.
unfold arr at 3.
simpl.
rewrite ceq.
assert ((i - r M1) * c M2 + j = i * c M2 + j - r M1 * c M1).
rewrite Nat.mul_sub_distr_r.
rewrite <- Nat.add_sub_swap.
rewrite ceq.
tauto.
apply Nat.mul_le_mono_r.
tauto.
rewrite H.
rewrite <- isv1.
apply app_nth2.
rewrite <- ceq.
apply out_of_bounds_is_not_valid_access.
tauto.
tauto.
Qed.

Theorem hconcat_apply_opt_1 {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A) i j, is_valid M1 -> in_bounds M1 i j -> Apply_opt (VConcat M1 M2) i j = Apply_opt M1 i j.
intros M1 M2 i j isv1 b.
apply in_bounds_is_valid_access in b.
unfold Apply_opt, VConcat, r, c, arr.
simpl.
apply app_nth_error_1.
unfold c, arr in b.
tauto.
tauto.
Qed.

Theorem hconcat_apply_opt_2 {A: Type}: forall (M1: @Matrix A) (M2: @Matrix A) i j, is_valid M1 -> c M1 = c M2 -> r M1 <= i -> Apply_opt (VConcat M1 M2) i j = Apply_opt M2 (i - (r M1)) j.

intros M1 M2 i j isv1 ceq b.
unfold Apply_opt, VConcat.
unfold c at 1.
unfold arr at 3.
simpl.
rewrite ceq.
assert ((i - r M1) * c M2 + j = i * c M2 + j - r M1 * c M1).
rewrite Nat.mul_sub_distr_r.
rewrite <- Nat.add_sub_swap.
rewrite ceq.
tauto.
apply Nat.mul_le_mono_r.
tauto.
rewrite H.
rewrite <- isv1.
apply app_nth_error_2.
rewrite <- ceq.
apply out_of_bounds_is_not_valid_access.
tauto.
tauto.
Qed.

Definition Fill {T: Type}(r: nat)(c: nat)(v: T) := (r, c, repeat v (r * c)).

Theorem fill_is_valid {T: Type}: forall r c (v: T), is_valid (Fill r c v).
intros; apply repeat_length. Qed.

Theorem fill_in_bounds {T: Type}: forall r c (v: T) i j, i < r /\ j < c <-> in_bounds (Fill r c v) i j.
intros.
unfold in_bounds, Fill, r, c.
simpl.
tauto.
Qed.

Theorem fill_apply_def {T: Type}: forall r c (v: T) i j def, i < r /\ j < c -> Apply_def (Fill r c v) i j def = v.
intros.
unfold Apply_def, Fill, r, c, arr.
simpl.
pose (nth_repeat v (r0 * c0) (i * c0 + j)).
rewrite (nth_indep _ _ def) in e.
tauto.
pose  ((proj1 (fill_in_bounds r0 c0 v i j )) H).
apply in_bounds_is_valid_access in i0.
tauto.
apply fill_is_valid.
Qed.

Theorem fill_apply_opt {T: Type}: forall r c (v: T) i j, i < r /\ j < c -> Apply_opt (Fill r c v) i j = Some v.
intros.
unfold Apply_def, Fill, r, c, arr.
simpl.
pose  ((proj1 (fill_in_bounds r0 c0 v i j )) H).
apply in_bounds_is_valid_access in i0.
pose (nth_error_repeat v i0).
rewrite fill_is_valid in e.
tauto.
apply fill_is_valid.
Qed.

Theorem map_fill {A B: Type}: forall (f: A -> B) r c (v: A), Map (Fill r c v) f = Fill r c (f v).
intros f r0 c0 v.
unfold Fill.
unfold Map.
simpl.
rewrite map_repeat.
tauto.
Qed.

Theorem vconcat_fill {A: Type}: forall r r' c (v: A), VConcat (Fill r c v) (Fill r' c v) = Fill (r + r') c v.
intros r0 r' c0 v.
unfold Fill, VConcat, r, c, arr.
simpl.
rewrite <- repeat_app.
assert (r0 * c0 + r' * c0 = (r0 + r') * c0).
lia.
rewrite H.
tauto.
Qed.

Definition IdMat {A: Type} (d: A) (o: A) (n: nat) := (n, n, for2 (seq 0 n) (seq 0 n) (fun i => fun j => if i =? j then d else o)).

Theorem id_mat_is_valid {A: Type}: forall (d: A) o n, is_valid (IdMat d o n).
intros d o n.
unfold is_valid, IdMat, r, c, arr.
simpl.
rewrite for2_length.
rewrite seq_length.
tauto.
Qed. 

Theorem id_mat_in_bounds {A: Type} :forall (d: A) o n i j, i < n /\ j < n <-> in_bounds (@IdMat A d o n) i j.
intros d o n i j.
unfold in_bounds, IdMat, r, c.
simpl.
tauto.
Qed.

Theorem id_mat_apply_def_1 {A: Type}: forall (d: A) o n i j, i < n /\ j < n -> i = j -> Apply_def (IdMat d o n) i j d = d.
intros d o n i j H e.
unfold Apply_def.
simpl.
rewrite (for2_nth _ _ _  0 d).
rewrite seq_length.
rewrite Nat.add_comm.
rewrite Nat.mod_add.
rewrite Nat.div_add.
rewrite Nat.div_small.
rewrite Nat.add_0_l.
rewrite e.
rewrite seq_nth.
rewrite Nat.add_0_l.
rewrite Nat.mod_small.
pose (map_nth (fun b : nat => if j =? b then d else o) (seq 0 n) j j).
simpl in e0.
rewrite seq_nth in e0.
rewrite Nat.add_0_l in e0.
rewrite Nat.eqb_refl in e0.
tauto.
lia.
lia.
lia.
lia.
lia.
lia.
rewrite seq_length.
pose ((proj1 (@id_mat_in_bounds A d o n i j)) H).
apply in_bounds_is_valid_access in i0.
unfold IdMat, arr in i0.
simpl in i0.
rewrite for2_length in i0.
rewrite seq_length in i0.
tauto.
apply id_mat_is_valid.
Qed.

Theorem id_mat_apply_def_2 {A: Type}: forall (d: A) o n i j, i < n /\ j < n -> i <> j -> Apply_def (IdMat d o n) i j o = o.
intros d o n i j H ne.
unfold Apply_def.
simpl.
rewrite (for2_nth _ _ _  0 o).
rewrite seq_length.
rewrite Nat.add_comm.
rewrite Nat.mod_add.
rewrite Nat.div_add.
rewrite Nat.div_small.
rewrite Nat.add_0_l.
rewrite seq_nth.
rewrite Nat.add_0_l.
rewrite Nat.mod_small.
pose (map_nth (fun b : nat => if i =? b then d else o) (seq 0 n) 0 j).
simpl in e.
rewrite seq_nth in e.
rewrite Nat.add_0_l in e.
rewrite <- Nat.eqb_neq in ne.
rewrite ne in e.
rewrite (nth_indep _ _ o) in e.
tauto.
rewrite map_length.
rewrite seq_length.
lia.
lia.
lia.
lia.
lia.
lia.
lia.
rewrite seq_length.
pose ((proj1 (@id_mat_in_bounds A d o n i j)) H).
apply in_bounds_is_valid_access in i0.
unfold IdMat, arr in i0.
simpl in i0.
rewrite for2_length in i0.
rewrite seq_length in i0.
tauto.
apply id_mat_is_valid.
Qed.

Theorem id_mat_apply_opt_1 {A: Type}: forall (d: A) o n i j, i < n /\ j < n -> i = j -> Apply_opt (IdMat d o n) i j = Some d.
intros d o n i j b e.
rewrite (apply_opt_apply_def _ _ _ d).
rewrite id_mat_apply_def_1.
tauto.
tauto.
tauto.
apply id_mat_is_valid.
apply id_mat_in_bounds.
tauto.
Qed.

Theorem id_mat_apply_opt_2 {A: Type}: forall (d: A) o n i j, i < n /\ j < n -> i <> j -> Apply_opt (IdMat d o n) i j = Some o.
intros d o n i j b ne.
rewrite (apply_opt_apply_def _ _ _ o).
rewrite id_mat_apply_def_2.
tauto.
tauto.
tauto.
apply id_mat_is_valid.
apply id_mat_in_bounds.
tauto.
Qed.

End MatrixOps.

Section BoolMatrix.

Definition Complement (M: @Matrix bool): @Matrix bool := Map M negb.

Corollary complement_is_valid: forall (M: Matrix), is_valid M -> is_valid (Complement M).
intros M; apply map_is_valid. Qed.

Corollary complement_in_bound: forall (M: Matrix) i j, in_bounds M i j -> in_bounds (Complement M) i j.
tauto. Qed.

Corollary complement_apply_opt: forall (M: Matrix) i j, Apply_opt (Complement M) i j = (opt_f negb) (Apply_opt M i j).
intros; apply apply_opt_map. Qed.

Corollary complement_apply_def: forall (M: @Matrix bool) i j def, Apply_def (Complement M) i j (negb def) = negb (Apply_def M i j def).
intros M i j def; apply apply_def_map. Qed.

Corollary complement_update: forall (M: Matrix) i j v, Complement (Update M i j v) = Update (Complement M ) i j (negb v).
intros M i j v; apply map_update. Qed.

Theorem complement_complement: forall (M: Matrix), Complement (Complement M) = M.
intro M.
unfold Complement, Map, r, c, arr.
simpl.
pose (map_map negb negb (snd M)).
rewrite e.
assert((fun x : bool =>
      negb (negb x)) = (fun x: bool => x)).
apply functional_extensionality.
intros.
apply negb_involutive.
rewrite H.
rewrite map_id.
rewrite matrix_eq.
tauto.
Qed.

Definition FalseMat (r: nat)(c: nat) : Matrix := Fill r c false.
Definition TrueMat (r: nat)(c: nat) : Matrix := Fill r c true.

Corollary falsemat_is_valid: forall r c , is_valid (FalseMat r c).
intros; apply fill_is_valid. Qed.

Corollary truemat_is_valid: forall r c , is_valid (TrueMat r c).
intros; apply fill_is_valid. Qed.

Corollary falsemat_in_bounds: forall r c i j, i < r /\ j < c <-> in_bounds (FalseMat r c) i j.
intros; apply fill_in_bounds. Qed.

Corollary truemat_in_bounds: forall r c i j, i < r /\ j < c <-> in_bounds (TrueMat r c) i j.
intros; apply fill_in_bounds. Qed.

Corollary falsemat_apply_def: forall r c i j def, i < r /\ j < c -> Apply_def (FalseMat r c) i j def = false.
intros r0 c0 i j; apply fill_apply_def. Qed.

Corollary truemat_apply_def: forall r c i j def, i < r /\ j < c -> Apply_def (TrueMat r c) i j def = true.
intros r0 c0 i j; apply fill_apply_def. Qed.

Corollary falsemat_apply_opt {T: Type}: forall r c i j, i < r /\ j < c -> Apply_opt (FalseMat r c) i j = Some false.
intros r0 c0 i j; apply fill_apply_opt. Qed.

Corollary truemat_apply_opt {T: Type}: forall r c i j, i < r /\ j < c -> Apply_opt (TrueMat r c) i j = Some true.
intros r0 c0 i j; apply fill_apply_opt. Qed.

Corollary complement_false: forall r c, Complement (FalseMat r c) = (TrueMat r c).
intros r0 c0; apply map_fill. Qed.

Corollary complement_true: forall r c, Complement (TrueMat r c) = (FalseMat r c).
intros r0 c0; apply map_fill. Qed.

Definition And (M1: @Matrix bool) (M2: @Matrix bool) := MatBinop andb M1 M2.
Definition Or (M1: @Matrix bool) (M2: @Matrix bool) := MatBinop orb M1 M2.
Definition Xor (M1: @Matrix bool) (M2: @Matrix bool) := MatBinop xorb M1 M2.

Corollary mat_and_is_valid : forall M1 M2 , is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> is_valid (And M1 M2).
intros M1 M2; apply mat_binop_is_valid. Qed.

Theorem mat_and_in_bounds : forall M1 M2 i j, in_bounds M1 i j -> in_bounds M2 i j -> in_bounds (And M1 M2) i j.
intros M f i j; tauto. Qed.

Theorem mat_and_comm: forall M1 M2, is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> And M1 M2 = And M2 M1.
intros.
apply mat_binop_comm.
tauto.
tauto.
tauto.
apply andb_comm.
Qed.

Corollary mat_or_is_valid : forall M1 M2 , is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> is_valid (Or M1 M2).
intros M1 M2; apply mat_binop_is_valid. Qed.

Theorem mat_or_in_bounds : forall M1 M2 i j, in_bounds M1 i j -> in_bounds M2 i j -> in_bounds (Or M1 M2) i j.
intros M f i j; tauto. Qed.

Theorem mat_or_comm: forall M1 M2, is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> Or M1 M2 = Or M2 M1.
intros.
apply mat_binop_comm.
tauto.
tauto.
tauto.
apply orb_comm.
Qed.

Corollary mat_xor_is_valid : forall M1 M2 , is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> is_valid (Xor M1 M2).
intros M1 M2; apply mat_binop_is_valid. Qed.

Theorem mat_xor_in_bounds : forall M1 M2 i j, in_bounds M1 i j -> in_bounds M2 i j -> in_bounds (Xor M1 M2) i j.

intros M f i j; tauto. Qed.

Theorem mat_xor_comm: forall M1 M2, is_valid M1 -> is_valid M2 -> shape M1 = shape M2 -> Xor M1 M2 = Xor M2 M1.
intros.
apply mat_binop_comm.
tauto.
tauto.
tauto.
apply xorb_comm.
Qed.

End BoolMatrix.