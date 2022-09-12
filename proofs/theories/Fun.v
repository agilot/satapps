Require Export FunctionalExtensionality.

Definition id_f {A: Type}: A -> A := fun a => a.

Definition const_f {A B: Type} (b: B): A -> B := fun a => b.

Definition comp{A B C: Type} (f: B -> C) (g: A -> B) := fun a => f (g a).

Definition inv_f_l {A B: Type} (f: A -> B) (i: B -> A) := comp i f = id_f.
Definition inv_f_r {A B: Type} (f: A -> B) (i: B -> A) := comp f i = id_f.
Definition inv_f {A B: Type} (f: A -> B) (i: B -> A) := inv_f_l f i /\ inv_f_r f i.

Definition opt_f {A B: Type} (f: A -> B) := 
(fun o: option A => match o with
| Some a => Some (f a)
| None => None
end).





