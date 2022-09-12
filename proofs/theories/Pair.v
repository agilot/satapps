Require Export Algebra.


Section PairOp.

Definition pairop {A B C: Type} := A * B -> C.

Definition bin_to_pair {A B C: Type} (f: @binop A B C) : pairop := (fun x: A * B => f (fst x) (snd x)).

Definition pair_to_bin {A B C: Type} (f: @pairop A B C) : @binop A B C := (fun a => fun b => f (a, b)).

Theorem bin_to_pair_to_bin {A B C: Type}: forall (f: @pairop A B C), bin_to_pair (pair_to_bin f) = f.
unfold bin_to_pair, pair_to_bin.
intros f.
apply functional_extensionality.
tauto.
Qed.

Theorem pair_to_bin_to_pair {A B C: Type}: forall (bin: @binop A B C), pair_to_bin (bin_to_pair bin) = bin.
unfold bin_to_pair, pair_to_bin.
intros f.
apply functional_extensionality.
tauto.
Qed.

Theorem bin_to_pair_comp_f_bin {A B C D: Type}: forall (f: C -> D) (bin: @binop A B C), bin_to_pair (comp_f_bin f bin) = comp f (bin_to_pair bin).
intros f bin.
unfold bin_to_pair, comp_f_bin, comp.
tauto.
Qed.

End PairOp.

Section Option.

Definition push_opt_pair {A B: Type} (op: option (A * B)): (option A) * (option B) :=
match op with
| Some (a, b) => (Some a, Some b)
| None => (None, None)
end.

Definition fact_opt_pair {A B: Type} (op: (option A) * (option B)): option (A * B) :=
match op with
| (Some a, Some b) => Some (a, b)
| _ => None
end.

Theorem fact_push_opt_pair {A B: Type}: forall op: (option (A * B)), fact_opt_pair (push_opt_pair op) = op.
destruct op.
tauto.
tauto.
Qed.

End Option.