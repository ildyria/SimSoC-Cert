(*
Inductive le (n : nat) : nat -> Prop :=
  | le_n : n <= n
  | le_S : forall m : nat, n <= m -> n <= S m
*)

Definition pr_le0 {n} {m} (l: n <= m) :=
  let diag n m :=
    match m with
      | O => forall X: nat -> Prop, X n -> X m
      | _ => True
    end in
  match l in (_ <= m) return (diag n m) with
    | le_n =>
      match n return (diag n n) with
        | 0 => fun X k => k
        | S _ => I
      end
    | le_S _ _ => I
  end.

(* For a successor, there are 2 possible continuations k1 and k2 *)
Definition pr_leS {n} {m} (l: n <= m) :=
  let diag n m' :=
    match m' with
      | S m => forall X: nat -> Prop, X n -> (n <= m -> X (S m)) -> X m'
      | _ => True
    end in
  match l in (_ <= m') return (diag n m') with
    | le_n =>
      match n return (diag n n) with
        | 0 => I
        | S n0 => fun X k1 _ => k1
      end
    | le_S m l' => fun X _ k2 => k2 l'
  end.

(* Applications *)

Lemma invle0 : forall n, n <= 0 -> n = 0.
Proof.
intros n l. apply (pr_le0 l). reflexivity.
Qed.

Lemma invle3 : forall n, n <= 3 -> n = 3 \/ n <= 2.
intros n l. apply (pr_leS l). 
  left; trivial.
  right; trivial.
Qed.

(* For record: Some inspiration for diag relations *)

Definition impred n m :=
  forall X: nat -> Prop, 
  X n -> (forall m', n <= m' -> X (S m')) -> X m.

Lemma l1: forall n m, n <= m -> impred n m.
intros n m l. case l; clear l m. 
  intros X xn H. apply xn. 
  intros m l X xn H. apply H. exact l. 
Defined.
 

Lemma l2: forall n m, impred n m -> n <= m.
intros n m i. apply i; clear i m. 
  constructor 1. 
  exact (le_S n).
Qed.
