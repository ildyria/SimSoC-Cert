Inductive even_i : nat -> Prop :=
  | E0: even_i 0
  | E2: forall n, even_i n -> even_i (S (S n)).

(* ------------------------------------------------------------ *)
(* Section 2: "old" small inversions *)

(* How to get rid of the basic absurd case *)
Lemma ev1_eq47 : even_i 1 -> 4 = 7.
Proof. 
intros e1. 
pose (diag x := match x with 1 => 4 = 7  | _ => True end).
change (diag 1); case e1; intros; exact I.
Undo.
revert e1; intro H. apply (
      match H in even_i n return diag n with E0 => I | E2 _ _ => I end
). 
Qed.

Lemma ev3_eq47 : even_i 3 -> 4 = 7.
Proof. 
intros e3. 
pose (diag x := match x with 3 => 4 = 7  | _ => True end).
change (diag 3). 
case e3; try (exact I).
intros n0 en0. case en0. try exact I.
intros n1 en1. exact I. 
Qed.

(* Not in the paper: definitional (non-interactive) style *)
Definition ev3_eq47_def : even_i 3 -> 4 = 7 :=
  fun e3 : even_i 3 =>
  let diag x := match x with 3 => 4 = 7  | _ => True end in
  match e3 in (even_i n) return (diag n) with
    | E0 => I
    | E2 n0 en0 =>
      match en0 in (even_i n) return (diag (S (S n))) with
        | E0 => I
        | E2 n1 en1 => I
      end
  end.

(* Not in the paper: inverting even_i 5 *)
Lemma ev5_eq47 : even_i 5 -> 4 = 7.
Proof. 
intros e5. 
pose (diag x := match x with 5 => 4 = 7  | _ => True end).
change (diag 5). 
case e5; try (exact I).
intros n0 en0. case en0; try exact I.
intros n1 en1. case en1; try exact I.
intros n2 en2. exact I. 
Qed.
Print ev5_eq47.

(* Not in the paper: inverting even_i 5, definitional (non-interactive) style *)
Definition ev5_eq47_def : even_i 5 -> 4 = 7 :=
  fun e5 : even_i 5 =>
  let diag x := match x with 5 => 4 = 7  | _ => True end in
  match e5 in (even_i n) return (diag n) with
    | E0 => I
    | E2 n0 en0 =>
      match en0 in (even_i n) return (diag (S (S n))) with
        | E0 => I
        | E2 n1 en1 =>
          match en1 in (even_i n) return (diag (S (S (S (S n))))) with
            | E0 => I
            | E2 _ _ => I
          end
      end
  end.


(* ------------------------------------------------------------ *)
(* Section 3 *)

Lemma ev1_eq74_gendiag : even_i 1 -> 7 = 4.
Proof. 
intros e1. 
pose (diag x := match x with 1 => forall (X: Prop), X  | _ => True end).
apply (match e1 in even_i n return diag n with E0 => I | _ => I end).
Qed.

Definition pr_1 {n} (en: even_i n) :=
    let diag x := match x with 1 => forall (X: Prop), X | _ => True end in
    match en in even_i n return diag n with  E0 => I | _ => I end.


(* Not in the paper: using pr_1 *)
Lemma ev1_eq74 : even_i 1 -> 7 = 4.
Proof. 
intros e1. 
pose (diag x := match x with 1 => 7 = 4  | _ => True end). 
change (diag 1); destruct e1; exact I. 
Undo.
apply (pr_1 e1).
Qed.

(* Not in the paper: direct style (OK for only 1 premise) *)
(* The type of the result is either (even_i p) if n = 2 + p, True otherwise *)
Definition dpremises_E2 {n} (en: even_i n) :=
    let diag x :=
      match x with 
        | S (S y) => even_i y
        | _ => True 
      end in
    match en in even_i n return diag n with
       | E2 p e => e
       | _ => I
    end.

(* Using dpremises_E2 *)
Lemma ev_i_plus_def : forall n m, even_i n -> even_i (n+m) -> even_i m.
Proof. 
intros n m e. induction e as [ | n e IHe]; simpl. 
  trivial.

  intros e2.
  generalize (dpremises_E2 e2). intro enm. Undo. 
  refine ((fun enm => _) (dpremises_E2 e2)). 
  apply IHe. 
Qed.

(** CPS style *)
Definition premises_E2 {n} (en: even_i n) :=
    let diag x :=
      match x with 
        | S (S y) => forall (X: Prop), (even_i y -> X) -> X
        | _ => True 
      end in
    match en in even_i n return diag n with
       | E2 p e => fun X k => k e
       | _ => I
    end.


(* Using premises_E2 *) 
Lemma ev_i_plus_cont :
   forall n m, even_i n -> even_i (n+m) -> even_i m.
Proof. 
intros n m e. induction e as [ | n e IHe]; simpl. 
  trivial.

  intros e2.
  apply (premises_E2 e2). intro enm. 
(* Old version, slightly more complicated;
   still used in SimSoC-cert
   generalize (premises_E2 e2); intro pr. apply pr; intro enm; clear pr.
*)
  apply IHe. exact enm. 
Qed.


(* Not in the paper: using refine instead of apply *)
Lemma ev_i_plus_cont_refine : forall n m, even_i n -> even_i (n+m) -> even_i m.
Proof. 
intros n m e. induction e as [ | n e IHe]; simpl. 
  trivial.

  intros e2.
  refine ((premises_E2 e2) _ (fun enm => _)). 
  apply IHe. exact enm. 
Qed.
  

         (* ---------------------- *)


(* Toy language of expressions *)
Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm.

Inductive val : Type :=
  | nval  : nat -> val
  | bval  : bool -> val.

(* Evaluation *)
Inductive eval : tm -> val -> Prop :=
  | E_Const : forall n,
      eval (tm_const n) (nval n)
  | E_Plus : forall t1 t2 n1 n2,
      eval t1 (nval n1) ->
      eval t2 (nval n2) ->
      eval (tm_plus t1 t2) (nval (plus n1 n2)).

(* Not in the paper, but could be (used in tests, and room available) *)
Definition pr_const_1_2 {t} {v} (e:eval t v) :=
  let diag t v :=
  match t, v with
    | tm_const tc, nval n => forall (X:nat -> Prop), X tc -> X n
    | _ ,_ => True
  end
  in 
  match e in (eval t v) return diag t v with
       | E_Const n => (fun X k => k)
       | _ => I
  end.

(* Not in the paper, but could be (used in tests, and room available) *)
Definition pr_const_1 {t} {v} (e:eval t v) :=
  let diag t v :=
  match t with
    | tm_const n => forall (X: val -> Prop),  X (nval n) -> X v
    | _  => True
  end
  in match e in (eval t v) return diag t v with
       | E_Const n => (fun X k => k)
       | _ => I
  end.

(* Not in the paper *)
Definition pr_const_2 t v :=
  match v with
    | nval n => forall (X: tm -> Prop),  X (tm_const n) -> X t
    | _  => True
  end.

(* Not in the paper: the technique also works for Type instead of Prop *)
Definition TRUE : Type := forall T: Type, T -> T. 
Definition II : TRUE := fun T t => t. 


(* For inverting plus *)
Definition pr_plus {t} {v} (e: eval t v) :=
  let diag t v :=
  match t with
    | tm_plus t1 t2 => forall (X:val -> Prop),
      (forall n1 n2, eval t1 (nval n1) ->
                     eval t2 (nval n2) ->
                     X (nval (plus n1 n2))) -> X v
    | _ => True
  end
  in match e in (eval t v) return diag t v with
       | E_Plus _ _ n1 n2 H1 H2 => (fun X k => k n1 n2 H1 H2)
       | _ => I
     end.

Section varP.

(* Illustrates the need for reverting some hypotheses *)
(* Not discussed in the paper, standard Coq technique *)
Variable P : val -> Prop.

Lemma test_evc1': 
  forall v ,P v -> 
  eval (tm_const 1) v -> v = nval 1.
Proof.
  intros v p e.
  revert p.
  apply (pr_const_1 e).
  intro p.
  reflexivity.
Qed.


(* Explanations could be added here about pr_const_1_2 *)
Lemma test_ev1: 
  forall v , P v -> eval (tm_plus (tm_const 1) (tm_const 0)) v -> v = nval 1.
Proof.
  intros v p e.
  revert p.
  apply (pr_plus e). intros n1 n2 e1 e2.
  apply (pr_const_1_2 e1).
  apply (pr_const_1_2 e2).
  intro p.
  reflexivity.
Qed.

End varP.

(* ------------------------------------------------------------ *)

(* Non-deterministic evaluation, in order to illustrate 
   - several cases matching an "input" (see pp. 6-7 of the paper)
   - more than 1 argument, as for tm

(Not in the paper)
*)

Section varQ.

Variable Q : tm -> Prop.

Inductive eval': tm -> val -> Prop :=
  | E_Const' : forall n,
      eval' (tm_const n) (nval n)
  | E_Plus1 : forall t1 t2 n1 n2,
      eval' t1 (nval n1) ->
      eval' t2 (nval n2) ->
      eval' (tm_plus t1 t2) (nval (plus n1 n2))
  | E_Plus2 : forall t1 t2 n2,
      Q t1 ->
      eval' t2 (nval n2) ->
      eval' (tm_plus t1 t2) (nval n2).

(* Similar to pr_const_1_2 *)
Definition pr_const_1_2' {t} {v} (e:eval' t v) :=
  let diag t v :=
  match t, v with
    | tm_const tc, nval n => forall (X:nat -> Prop), X tc -> X n
    | _ ,_ => True
  end
  in 
  match e in (eval' t v) return diag t v with
       | E_Const' n => (fun X k => k)
       | _ => I
  end.

(* Similar to pr_const_1_2 *)
Definition pr_const_1' {t} {v} (e:eval' t v) :=
  let diag t v :=
  match t with
    | tm_const n => forall (X: val -> Prop),  X (nval n) -> X v
    | _  => True
  end
  in match e in (eval' t v) return diag t v with
       | E_Const' n => (fun X k => k)
       | _ => I
  end.

(* However, non-determinism for plus has to be taken into account *)
Definition pr_plus' {t} {v} (e: eval' t v) :=
  let diag t v :=
  match t with
    | tm_plus t1 t2 => forall (X:val -> Prop),
      (forall n1 n2, eval' t1 (nval n1) ->
                     eval' t2 (nval n2) ->
                     X (nval (plus n1 n2)))
      ->
      (forall n2, Q t1 ->
                  eval' t2 (nval n2) ->
                  X (nval n2))-> X v
    | _ => True
  end
  in match e in (eval' t v) return diag t v with
       | E_Plus1 _ _ n1 n2 H1 H2 => (fun X k1 k2 => k1 n1 n2 H1 H2)
       | E_Plus2 _ _ n2 H1 H2 => (fun X k1 k2 => k2 n2 H1 H2)
       | _ => I
     end.

Lemma test_ev'2:
  forall t, eval' (tm_plus (tm_const 0) (tm_const 1)) t-> t=nval 1.
Proof.
intros t e.
apply (pr_plus' e). 
   intros n1 n2 e1 e2. apply (pr_const_1_2' e1). apply (pr_const_1_2' e2). reflexivity.
   intros n2 q e2. apply (pr_const_1_2' e2). reflexivity. 
Qed.


End varQ.
