Require Import Arith.

Inductive id : Type :=
  Id : nat -> id.

Inductive tm : Type :=
  | C : nat -> tm
  | V : id -> tm
  | P : tm -> tm -> tm
  | A : tm -> tm -> tm.

Definition beq_id X1 X2 :=
  match (X1, X2) with
    (Id n1, Id n2) => beq_nat n1 n2
  end.

Definition state := id -> option nat.
(*Definition st :=  id -> (id * nat).*)
Definition empty_state : state :=
  fun _ => None.
(*Definition empty_st : st :=
  fun X => (X, 0).*)

Definition update (st : state) (X: id) (n : option nat) : state :=
  fun X' => if beq_id X X' then n else st X'.

(*Definition update_st (s: st) (X: id) (t: nat) : st :=
  fun X' => if beq_id X X' then (X, t) else s X'.*)

Definition get (s: state) (X: id) :=
  fun X' => if beq_id X X' then s X' else None.

Eval compute in get ((update empty_state (Id 1) (Some 2))) (Id 1) (Id 1).

Inductive eval : state -> tm -> state -> option nat -> Prop :=
  | E_Const : forall s n,
      eval s (C n) s (Some n)
  | E_Var : forall s i,
      eval s (V i) s (s i)
  | E_Plus : forall s t1 n1 s' t2 n2 s'',
      eval s t1 s' (Some n1) ->
      eval s' t2 s'' (Some n2) ->
      eval s (P t1 t2) s'' (Some (n1 + n2))
  | E_Assign : forall s t1 s' i t2 n2,
      eval s t1 s (s i) ->
      eval s t2 s' n2 ->
      eval s (A t1 t2) (update s' i n2) n2.

Example eval1 :
  eval empty_state (A (V (Id 1)) (C 3)) (update empty_state (Id 1) (Some 3)) (Some 3).
  apply E_Assign.
  apply E_Var.
  apply E_Const.
Qed.

(*Example eval2 :
  eval empty_state (A (C 0) (C 3)) (update empty_state (Id 1) (Some 3)) (Some 3).
  apply E_Assign.*)

(* JF I was wrong, value is just C; but updating still needed *)
Inductive red : tm -> state -> tm -> state -> Prop :=
  | R_PlusConstConst : forall n1 n2 st,
      red (P (C n1) (C n2)) st (C (n1 + n2)) st
  | R_Plus1 : forall t1 st t1' st' t2,
      red t1 st t1' st' ->
      red (P t1 t2) st (P t1' t2) st'
  | R_Plus2 : forall t2 st t2' st' n1,
      red t2 st t2' st' ->
      red (P (C n1) t2) st (P (C n1) t2') st'
  | R_AssignConst : forall i n st,
      red (A (V i) (C n)) st (C n) (update st i (Some n))
  | R_Assign1 : forall t2 st t2' st' i,
      red t2 st t2' st' ->
      red (A (V i) t2) st (A (V i) t2') st'
  | R_Assign2 : forall t1 t2 st t1' st',
      red t1 st t1' st' ->
      red (A t1 t2) st (A t1' t2) st'.

