Inductive even_i : nat -> Prop :=
  | E0: even_i 0
  | E2: forall n, even_i n -> even_i (S (S n)).

(* ------------------------------------------------------------ *)
(* Section 3.2: "old" small inversions *)

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
(* Section 3.3 *)

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
  
(* From reviewer 3 itp13 *)
Definition pr {n} (en: even_i n) :=
  let diag x := match x with
                  | O => forall (X: Prop), X -> X
                  | S (S n) => forall (X: Prop), (even_i n -> X) -> X 
                  | _ => forall (X: Prop), X
                end in
  match en in even_i n return diag n with
    | E0 => fun X h => h
    | E2 n hn => fun X h => h hn
  end.

Lemma ev1_eq74' : even_i 1 -> 7 = 4.
Proof. 
intros e1. 
apply (pr e1).
Qed.

Lemma ev_i_plus_cont' :
   forall n m, even_i n -> even_i (n+m) -> even_i m.
Proof. 
intros n m e. induction e as [ | n e IHe]; simpl. 
  trivial.

  intros e2.
  apply (pr e2). intro enm. 
  apply IHe. exact enm. 
Qed.

(* ------------------------------------------------------------ *)
(* Section 3.4 *)


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

(* Not in the paper *)
Definition pr_const_2 t v :=
  match v with
    | nval n => forall (X: tm -> Prop),  X (tm_const n) -> X t
    | _  => True
  end.

(* Not in the paper: the technique also works for Type instead of Prop *)
Definition TRUE : Type := forall T: Type, T -> T. 
Definition II : TRUE := fun T t => t. 


(* Combination suggested by reviewer 3 itp13 *)

Definition pr_eval_1 {t} {v} (e:eval t v) :=
  let diag t v :=
  match t with
    | tm_const n => forall (X: val -> Prop),  X (nval n) -> X v
    | tm_plus t1 t2 => forall (X:val -> Prop),
      (forall n1 n2, eval t1 (nval n1) ->
                     eval t2 (nval n2) ->
                     X (nval (plus n1 n2))) -> X v
  end
  in match e in (eval t v) return diag t v with
       | E_Const n => (fun X k => k)
       | E_Plus _ _ n1 n2 H1 H2 => (fun X k => k n1 n2 H1 H2)
  end.

Definition pr_eval_1_2 {t} {v} (e:eval t v) :=
  let diag t v :=
  match t, v with
    | tm_const c, nval n => forall (X:nat -> Prop), X c -> X n
    | tm_plus t1 t2, nval n => forall (X:nat -> Prop),
      (forall n1 n2, eval t1 (nval n1) -> eval t2 (nval n2) -> X (plus n1 n2)) -> X n
    | _ ,_ => forall X:Prop, X
  end
  in 
  match e in (eval t v) return diag t v with
       | E_Const n => (fun X k => k)
       | E_Plus _ _ n1 n2 H1 H2 => (fun X k => k n1 n2 H1 H2)
  end.

(* This one can be used in all examples but test_ev2 *)
Definition pr_eval_1_2_other {t} {v} (e:eval t v) :=
  let diag t v :=
  match t, v with
    | tm_const c, nval n => forall (X:nat -> Prop), X c -> X n
    | tm_plus t1 t2, nval n => forall (X:nat -> Prop),
      (forall n1 n2, eval t1 (nval n1) -> eval t2 (nval n2) -> X (plus n1 n2)) -> X n
    | _ ,_ => True
  end
  in 
  match e in (eval t v) return diag t v with
       | E_Const n => (fun X k => k)
       | E_Plus _ _ n1 n2 H1 H2 => (fun X k => k n1 n2 H1 H2)
  end.

Section varP.

(* Illustrates the need for reverting some hypotheses *)
(* Not discussed in the paper, standard Coq technique *)
Variable P : val -> Prop.

Lemma test_evc1' : 
  forall v ,P v -> 
  eval (tm_const 1) v -> v = nval 1.
Proof.
  intros v p e.
  revert p.
  apply (pr_eval_1 e).
  intro p.
  reflexivity.
Qed.


(* Explanations could be added here about pr_eval_1_2 *)
Lemma test_ev1: 
  forall v , P v -> eval (tm_plus (tm_const 1) (tm_const 0)) v -> v = nval 1.
Proof.
  intros v p e.
  revert p.
  apply (pr_eval_1 e). intros n1 n2 e1 e2.
  apply (pr_eval_1_2 e1).
  apply (pr_eval_1_2 e2).
  intro p.
  reflexivity.
Qed.

(* For this one pr_eval_1_2_other cannot be used *)
Lemma test_ev2: 
  eval (tm_plus (tm_const 1) (tm_const 0)) (bval true) -> False.
Proof.
intro e. apply (pr_eval_1_2 e).
Qed.

Lemma test_ev2': 
  eval (tm_plus (tm_const 1) (tm_const 0)) (nval 0) -> False.
Proof.
  intro e. 
  cut (0=1). discriminate.
  pattern 0 at 1. apply (pr_eval_1_2 e). intros n1 n2 e1 e2. 
  apply (pr_eval_1_2 e1).
  apply (pr_eval_1_2 e2).
  reflexivity.
Qed.

Lemma test_ev3: 
  forall n, n < 5 -> eval (tm_plus (tm_const 1) (tm_const 0)) (nval n) -> n = 1.
Proof.
  intros n l e. revert l.
  apply (pr_eval_1_2 e). intros n1 n2 e1 e2.
  apply (pr_eval_1_2 e1).
  apply (pr_eval_1_2 e2).
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

(* Similar to pr_eval_1 *)

Definition pr_eval_1' {t} {v} (e:eval' t v) :=
  let diag t v :=
  match t with
    | tm_const n => forall (X: val -> Prop),  X (nval n) -> X v
    | tm_plus t1 t2 => forall (X:val -> Prop),
      (forall n1 n2, 
       eval' t1 (nval n1) -> eval' t2 (nval n2) -> X (nval (plus n1 n2))) ->
      (forall n2, Q t1 -> eval' t2 (nval n2) -> X (nval n2))-> X v
  end
  in match e in (eval' t v) return diag t v with
       | E_Const' n => (fun X k => k)
       | E_Plus1 _ _ n1 n2 H1 H2 => (fun X k1 k2 => k1 n1 n2 H1 H2)
       | E_Plus2 _ _ n2 H1 H2 => (fun X k1 k2 => k2 n2 H1 H2)
  end.

(* Similar to pr_eval_1_2 *)
Definition pr_eval_1_2' {t} {v} (e:eval' t v) :=
  let diag t v :=
  match t, v with
    | tm_const c, nval n => forall (X:nat -> Prop), X c -> X n
    | tm_plus t1 t2, nval n => forall (X:nat -> Prop),
      (forall n1 n2, 
       eval' t1 (nval n1) -> eval' t2 (nval n2) -> X (plus n1 n2)) ->
      (forall n2, Q t1 -> eval' t2 (nval n2) -> X n2)-> X n
    | _ ,_ => forall X:Prop, X
  end
  in 
  match e in (eval' t v) return diag t v with
       | E_Const' n => (fun X k => k)
       | E_Plus1 _ _ n1 n2 H1 H2 => (fun X k1 k2 => k1 n1 n2 H1 H2)
       | E_Plus2 _ _ n2 H1 H2 => (fun X k1 k2 => k2 n2 H1 H2)
  end.


Lemma test_ev'2:
  forall t, eval' (tm_plus (tm_const 0) (tm_const 1)) t-> t=nval 1.
Proof.
intros t e.
apply (pr_eval_1' e). 
   intros n1 n2 e1 e2. apply (pr_eval_1_2' e1). apply (pr_eval_1_2' e2). reflexivity.
   intros n2 q e2. apply (pr_eval_1_2' e2). reflexivity. 
Qed.



Lemma test_ev'3:
  forall n, eval' (tm_plus (tm_const 0) (tm_const 1)) (nval n) -> n = 1.
Proof.
intros n e.
apply (pr_eval_1_2' e). 
   intros n1 n2 e1 e2. apply (pr_eval_1_2' e1). apply (pr_eval_1_2' e2). reflexivity.
   intros n2 q e2. apply (pr_eval_1_2' e2). reflexivity. 
Qed.

End varQ.


(* ------------------------------------------------------------ *)
(* Section 3.5 *)

Inductive t : nat -> Set :=
    | F1 : forall {n}, t (S n)
    | FS : forall {n}, t n -> t (S n).

Inductive odd : forall n : nat, t n -> Prop :=
   | odd_1 : forall n, odd (S n) F1
   | odd_SS : forall n i, odd n i -> odd _ (FS (FS i)).


Definition premises_odd {n} {i: t n} (of: odd n i) :=
  let diag n i :=
    match i with
      | F1 _ => forall (X: Prop), X -> X
      | FS _ (FS _ y)  => forall (X: Prop), (odd _ y -> X) -> X
      | _ => forall (X: Prop), X
    end in
  match of in odd n i return diag n i with
      | odd_1 n => fun X k => k
      | odd_SS n i o => fun X k => k o
  end.

Definition premises_odd_SS {n} {i: t n} (of: odd n i) :=
  let diag n i :=
    match i with
      | FS _ (FS _ y)  => forall (X: Prop), (odd _ y -> X) -> X
      | _ => True 
    end in
  match of in odd n i return diag n i with
      | odd_SS n i o => fun X k => k o
      | _ => I
  end.


(* A failure for standard inversion *)
Lemma odd_SS_inv: forall n i, odd _ (FS (FS i)) -> odd n i.
Proof.
  intros n i o. apply (premises_odd o). trivial.
Qed.

Lemma odd_SS_inv_with_simpl_pr: forall n i, odd _ (FS (FS i)) -> odd n i.
Proof.
  intros n i o. apply (premises_odd_SS o). trivial.
Qed.
