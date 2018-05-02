(** begin chunk60 *)
Inductive t : nat -> Set :=
    | F1 : forall {n}, t (S n)
    | FS : forall {n}, t n -> t (S n).

Inductive odd : forall n : nat, t n -> Prop :=
   | odd_1 : forall n, odd (S n) F1
   | odd_SS : forall n i, odd n i -> odd _ (FS (FS i)).
(** end chunk60 *)


(** begin chunk61 *)
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
(** end chunk61 *)


(* Coq inversion fails on this one *)
(** begin chunk62 *)
Lemma odd_SS_inv: forall n i, odd _ (FS (FS i)) -> odd n i.
Proof. intros n i o. apply (premises_odd_SS o). trivial. Qed.
(** end chunk62 *)


(** begin chunk21 *)
Inductive even_i : nat -> Prop :=
  | E0: even_i 0
  | E2: forall n, even_i n -> even_i (S (S n)).
(** end chunk21 *)

Lemma l1: forall x, even_i (S (S (S x))) -> S x <> 1. 
Proof.
intros x H.
pose (diag n := match n with S (S p) => p <> 1 | _ => True end).  
(* change (diag (S (S (S x)))); case H. *)
refine (match H in (even_i n) return (diag n) with
          | E2 x0 ex0 => _ 
          | _ => I
        end). red. clear x H diag. 
case ex0; discriminate.
Qed.

Lemma l2: forall x, even_i (S x) -> exists y, even_i y /\ x = (S y). 

intros x H.
pose (diag n := match n with S p => exists y : nat, even_i y /\ p = S y | _ => True end). 
change (diag (S x)).  
case H; simpl. 
  exact I.
  clear x H. intros n e; exists n. auto. 
Qed.

(* ------------------------------------------------------------ *)
(* From here: to be used in sec:absurd *)

(* How to get rid of the basic absurd case *)
Lemma ev1_eq47 : even_i 1 -> 4 = 7.
Proof. 
intros e1. 
pose (
(** begin chunk24 *)
      diag x := match x with 1 => 4 = 7  | _ => True end
(** end chunk24 *)
).
change (diag 1); case e1; intros; exact I.
Undo.
revert e1; intro H; apply (
(** begin chunk25 *)
      match H in even_i n return diag n with E0 => I | E2 _ _ => I end
(** end chunk25 *)
). 
Qed.

Lemma ev3_eq47 : even_i 3 -> 4 = 7.
Proof. 
intros e3. 
pose (
(** begin chunk26 *)
      diag x := match x with 3 => 4 = 7  | _ => True end
(** end chunk26 *)
).
change (diag 3). 
case e3; try (exact I).
intros n0 en0. case en0. try exact I.
intros n1 en1. exact I. 
Qed.

Definition ev3_eq47_direct : even_i 3 -> 4 = 7 :=
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

(** begin chunk23 *)
Definition ev5_eq47_direct : even_i 5 -> 4 = 7 :=
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
(** end chunk23 *)


(* ------------------------------------------------------------ *)
(* From here: transition between sec:absurd and sec:improvement *)

(* Fails
Lemma ev3_eq74_gendiag : even_i 3 -> 7 = 4.
Proof. 
intros e3. 
pose (diag x := match x with 3 => forall (X: Prop), X  | _ => True end). 
refine (match e3 in even_i n return diag n with E0 => I | _ => _ end).
case e1; simpl. 
change (diag 1 _); destruct e1; exact I. 
Undo.
apply (pr_1 e1).
(* refine ((fun kpr => kpr ) (pr_1P e1)).*)
Qed.
*)

Lemma ev1_eq74_gendiag : even_i 1 -> 7 = 4.
Proof. 
intros e1. 
pose (
(** begin chunk27 *)
      diag x := match x with 1 => forall (X: Prop), X  | _ => True end
(** end chunk27 *)
).
(*
generalize (match e1 in even_i n return diag n with E0 => I | _ => I end);
intro k; red in k. apply k. 
Undo 2.
*)
apply (match e1 in even_i n return diag n with E0 => I | _ => I end).
Qed.

(** begin chunk29 *)
Definition pr_1 {n} (en: even_i n) :=
    let diag x := match x with 1 => forall (X: Prop), X | _ => True end in
    match en in even_i n return diag n with  E0 => I | _ => I end.
(** end chunk29 *)

Definition pr_1P {n} (en: even_i n) {X: Prop} :=
    let diag x :=
      match x with 
        | 1 => X
        | _ => True 
      end in
    match en in even_i n return diag n with
       | E0 => I
       | _ => I
    end.

Lemma ev1_eq74 : even_i 1 -> 7 = 4.
Proof. 
intros e1. 
pose (diag x := match x with 1 => 7 = 4  | _ => True end). 
change (diag 1); destruct e1; exact I. 
Undo.
apply (pr_1 e1).
(* refine ((fun kpr => kpr ) (pr_1P e1)).*)
Qed.

(* ------------------------------------------------------------ *)
(* From here: to be used in sec:improvement *)

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

(* Here we really need to get the right premise *)
Lemma ev_i_plus_direct : forall n m, even_i n -> even_i (n+m) -> even_i m.
Proof. 
intros n m e. induction e as [ | n e IHe]; simpl. 
  trivial.

  intros e2.
  generalize (dpremises_E2 e2). intro enm. Undo. 
  refine ((fun enm => _) (dpremises_E2 e2)). 
  apply IHe. 
Qed.

(** begin chunk30 *)
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
(** end chunk30 *)

(** begin chunk19 *)
Definition premises_Ap {u} (a: A u) :=
    let diag x :=
      match x with 
        | (** $\cal P$ *) => forall (X: Prop), (** $(\forall \mathbf{p_1}, X) \rightarrow  \ldots(\forall \mathbf{p_n}, X) \rightarrow X$ %\coqdoceol% *)
        | _ => True 
      end in
    match a in A p return diag p with
       | (** $C_1\; \mathbf{e_1}$ *)  => fun X k1... kn  => k1(** $\mathbf{e_1}$ %\coqdoceol%  *)
       (** $\vdots$ %\coqdoceol%  *)
       | (** $C_n\; \mathbf{e_n}$ *)  => fun X k1... kn  => kn(** $\mathbf{e_n}$ %\coqdoceol%  *)
       | _ => I
    end.
(** end chunk19 *)


Lemma ev_i_plus_cont :
(** begin chunk28 *)
   forall n m, even_i n -> even_i (n+m) -> even_i m.
(** end chunk28 *)
Proof. 
intros n m e. induction e as [ | n e IHe]; simpl. 
  trivial.

  intros e2.
  apply (premises_E2 e2). intro enm. 
(* Old complicated version
  generalize (premises_E2 e2); intro pr. apply pr; intro enm; clear pr.
*)
  apply IHe. exact enm. 
Qed.

Lemma ev_i_plus_cont_refine : forall n m, even_i n -> even_i (n+m) -> even_i m.
Proof. 
intros n m e. induction e as [ | n e IHe]; simpl. 
  trivial.

  intros e2.
  refine ((premises_E2 e2) _ (fun enm => _)). 
(*  Old complicated version
  refine ((fun pr => pr _ (fun enm => _)) (premises_E2 e2)). clear pr. 
*)
  apply IHe. exact enm. 
Qed.
  
(* BEGIN forget what follows *) 
Lemma ev_i_plus_cont_fix : forall n m, even_i n -> even_i (n+m) -> even_i m.
Proof. 
intros n m. revert n. fix 2. intros n e. 
destruct e as [ | n e]; simpl. 
  trivial.

  intros e2.
  refine ((fun pr => pr _ (fun enm => _)) (premises_E2 e2)); clear pr. 
  apply (ev_i_plus_cont_fix n e). exact enm. 
Qed.
(* trying to invert even_i n for n = 0 or n = S (S p);  *)

Definition premises_E2E0 {n} (en: even_i n) :=
    let diag :=
      forall (X: nat -> Prop), 
        X 0 -> (forall y, even_i y -> X (S (S y))) -> X n in
    fun (X: nat -> Prop) k1 k2 => 
      match en in (even_i n) return X n with
       | E0 => k1
       | E2 p e => k2 p e
    end.

(* TODO : renaming e_ -> e2, e2 --> ?? **)
Lemma ev_i_plus_cont_fix_20 : forall n m, even_i n -> even_i (n+m) -> even_i m.
Proof. 
intros n m. revert n. fix 2. intros n e. 
generalize (premises_E2E0 e). intro pr. apply pr; simpl; clear pr.
  trivial.

  intros p e2 e_.
  apply (ev_i_plus_cont_fix_20 p e2). 
  refine ((fun pr => pr _ (fun enm => _)) (premises_E2 e_)); clear pr. exact enm. 
Qed.
(* END forget what follows *) 
  

(** begin chunk11 *)
Fixpoint even_f (n: nat) : Prop :=
  match n with
  | O => True
  | 1 => False
  | S (S n) => even_f n
  end.
(** end chunk11 *)

(* BEGIN forget what follows *) 
(* Easier than expected for even_f *)
Lemma ev_f_plus_cont : forall n m, even_f n -> even_f (n+m) -> even_f m.
Proof.
fix 1. 
intros n m. destruct n as [| [ | n]]; simpl.
   trivial.
   intro fa; case fa. 
   apply ev_f_plus_cont. 
Qed.

Fixpoint mul4 (n: nat) : Prop :=
  match n with
  | O => True
  | 1 | 2 | 3 => False
  | S (S (S (S n))) => mul4 n
  end.

Theorem mul4_even_f : forall n, mul4 n -> even_f n.
Proof.
fix 1. intro n. 
refine (
  match n with
  | O => _
  | 1 | 2 | 3 => _
  | S (S (S (S n))) => _
  end); simpl; trivial.
apply mul4_even_f. 
Qed.
(* END forget what follows *) 

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)



(* small examples from devel/xiaomu*)

(*
Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm.

Inductive eval : tm -> tm -> Prop :=
  | E_Const : forall n,
      eval (tm_const n) (tm_const n)
  | E_Plus : forall t1 t2 n1 n2,
      eval t1 (tm_const n1) ->
      eval t2 (tm_const n2) ->
      eval (tm_plus t1 t2) (tm_const (plus n1 n2)).

Variable C:Prop.
Lemma test_step:eval (tm_plus (tm_const 0) (tm_const 3))
                (tm_const (plus 1 3))->C.
(*intro. inversion H. inv H3. inv H4. inversion H2.*)
*)

(* Try : Different type of input output *)

(** begin chunk31 *)
Inductive tm : Type :=
  | tm_const : nat -> tm
  | tm_plus : tm -> tm -> tm.

Inductive val : Type :=
  | nval  : nat -> val
  | bval  : bool -> val.

Inductive eval : tm -> val -> Prop :=
  | E_Const : forall n,
      eval (tm_const n) (nval n)
  | E_Plus : forall t1 t2 n1 n2,
      eval t1 (nval n1) -> eval t2 (nval n2) ->
      eval (tm_plus t1 t2) (nval (plus n1 n2)).
(** end chunk31 *)

(** begin chunk33 *)
  match t, v with
    | tm_const c, nval n => forall (X:nat -> Prop), X c -> X n
    | tm_plus t1 t2, nval n => forall (X:nat -> Prop),
      (forall n1 n2, eval t1 (nval n1) -> eval t2 (nval n2) -> X (plus n1 n2)) -> X n
    | _, _ => forall X:Prop, X
  end.
(** end chunk33 *)

(* begin chunk33 *)
Definition pr_const_1_2 {t} {v} (e:eval t v) :=
  let diag t v :=
  match t, v with
    | tm_const c, nval n => forall (X:nat -> Prop), X c -> X n
    | _ ,_ => True
  end
  in 
  match e in (eval t v) return diag t v with
       | E_Const n => (fun X k => k)
       | _ => I
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
(* end chunk33 *)

(** begin chunk32 *)
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
(** end chunk32 *)

Definition pr_const_2 t v :=
  match v with
    | nval n => forall (X: tm -> Prop),  X (tm_const n) -> X t
    | _  => True
  end.

Definition TRUE : Type := forall T: Type, T -> T. 
Definition II : TRUE := fun T t => t. 


(** begin chunk34 *)
Definition pr_plus_1 {t} {v} (e: eval t v) :=
  let diag t v :=
  match t with
    | tm_plus t1 t2 => forall (X:val -> Prop),
      (forall n1 n2, eval t1 (nval n1) -> eval t2 (nval n2) -> X (nval (plus n1 n2)))
      -> X v
    | _ => True
  end in match e in (eval t v) return diag t v with
       | E_Plus _ _ n1 n2 H1 H2 => (fun X k => k n1 n2 H1 H2)
       | _ => I
     end.
(** end chunk34 *)

(** begin chunk39 *)
  match t, v with
    | tm_plus t1 t2, nval n => forall (X:nat -> Prop),
      (forall n1 n2, eval t1 (nval n1) -> eval t2 (nval n2) -> X (plus n1 n2)) -> X n
    | _, _ => True
  end.
(** end chunk39 *)

(* begin chunk39 *)
Definition pr_plus_1_2 {t} {v} (e: eval t v) :=
  let diag t v :=
  match t, v with
    | tm_plus t1 t2, nval n => forall (X:nat -> Prop),
      (forall n1 n2, eval t1 (nval n1) -> eval t2 (nval n2) -> X (plus n1 n2))
      -> X n
    | _, _ => True
  end
  in 
  match e in (eval t v) return diag t v with
       | E_Plus _ _ n1 n2 H1 H2 => (fun X k => k n1 n2 H1 H2)
       | _ => I
  end.
(* end chunk39 *)

Section varP.

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

Lemma test_ev1_no_revert: 
(** begin chunk38 *)
Lemma ex1: forall v, eval (tm_plus (tm_const 1) (tm_const 0)) v -> v = nval 1.
Lemma ex2: forall n, eval (tm_plus (tm_const 1) (tm_const 0)) (nval n) -> n = 1.
(** end chunk38 *)
Proof.
  intros v p e.
  apply (pr_plus_1 e). intros n1 n2 e1 e2.
  apply (pr_const_1_2 e1).
  apply (pr_const_1_2 e2).
  intro p.
  reflexivity.
Qed.

Lemma test_ev3_no_revert: 
  forall n, eval (tm_plus (tm_const 1) (tm_const 0)) (nval n) -> n = 1.
Proof.
  intros n e.
  apply (pr_plus_1_2 e). intros n1 n2 e1 e2.
  apply (pr_const_1_2 e1).
  apply (pr_const_1_2 e2).
  intro p.
  reflexivity.
Qed.



(* Important: chunk nmbr 37 = good example to explain ! *)
Lemma test_ev1: 
(** begin chunk35 *)
  forall v , P v -> eval (tm_plus (tm_const 1) (tm_const 0)) v -> v = nval 1.
(** end chunk35 *)
Proof.
  intros v p e.
  revert p.
(** begin chunk36 *)
(** end chunk36 *)
  apply (pr_plus_1 e). intros n1 n2 e1 e2.
(** begin chunk37 *)
  e1 : eval (tm_const 1) (nval n1)
  e2 : eval (tm_const 0) (nval n2)
  ============================
   P (nval (n1 + n2)) -> nval (n1 + n2) = nval 1
(** end chunk37 *)
  apply (pr_const_1_2 e1).
  apply (pr_const_1_2 e2).
  intro p.
  reflexivity.
Qed.

End varP.

(* Old examples *)
(*
Lemma test_ev2: eval (tm_plus (tm_const 1) (tm_const 0)) (nval 0)->False.
intro. 
pose (diag x:= match x with tm_plus (tm_const 1) (tm_const 0) => False |_=> True end).
change (diag (tm_plus (tm_const 1) (tm_const 0))).
case H; clear H; simpl.
  trivial.
*)

(*
Section varP.

Variable P : val -> Prop.

Lemma test_evc1': 
  forall v ,P v -> 
  eval (tm_const 1) v -> v = nval 1.
intros v p e.
generalize
  (match e in (eval t v) return diag_const_1 t v with
     | E_Const n => (fun X k => k)
     | _ => I
   end);
clear e. intro k; red in k. apply k. reflexivity.
Qed.

Lemma test_ev1': 
  forall v ,P v -> 
  eval (tm_plus (tm_const 1) (tm_const 0)) v -> v = nval 1.

(*intros. inversion H. subst. inversion H2. subst. inversion H4. subst. simpl. reflexivity.
Qed.*)
intros v p e.
generalize
  (match e in (eval t v) return diag_plus_1 t v with
     | E_Plus _ _ n1 n2 H1 H2 => (fun X k => k n1 n2 H1 H2)
     | _ => I
   end);
clear e.
intro k; red in k. revert p. apply k; clear k. intros n1 n2 e1 e2 p.



generalize
  (match e1 in (eval t v) return diag_const_1_2 t v with
     | E_Const n => (fun X k => k )
     | _ => I
   end);
clear e1. 
intro k; red in k. apply k. clear k. 
generalize
  (match e2 in (eval t v)
     return diag_const_1_2 t v with
     |E_Const n => (fun X k => k)
     |_=>I
   end).
clear e2.
intro k. red in k. apply k. clear k.
simpl. reflexivity.
Qed.

End varP.
*)

(* End of try *) (* Sucseed *)

(* Old example : Same type of input output *)

(*
Inductive ex0 : tm -> Prop :=
  | t0 : ex0 (tm_const 0)
  | tx : forall t1 t2, ex0 t1 -> ex0 t2 ->
         ex0 (tm_plus t1 t2).

Lemma test_ex0 : ex0 (tm_const 1) -> False.
intro. inversion H.
Qed.
Lemma test_ex0': ex0 (tm_const 1) -> False.
intro.
pose (diag x:= match x with tm_const 1 => False |_ => True end).
change (diag (tm_const 1)). case H. clear H.
simpl. trivial.
simpl. trivial.
Qed.

Inductive eval : tm -> tm -> Prop :=
  | E_Const : forall n,
      eval (tm_const n) (tm_const n)
  | E_Plus : forall t1 t2 n1 n2,
      eval t1 (tm_const n1) ->
      eval t2 (tm_const n2) ->
      eval (tm_plus t1 t2) (tm_const (plus n1 n2)).


Variable Q : tm -> Prop.

Inductive eval': tm -> tm -> Prop :=
  | E_C : forall n,
      eval' (tm_const n) (tm_const n)
  | E_Plus1 : forall t1 t2 n1 n2,
      eval' t1 (tm_const n1) ->
      eval' t2 (tm_const n2) ->
      eval' (tm_plus t1 t2) (tm_const (plus n1 n2))
  | E_Plus2 : forall t1 t2 n2,
      Q t1 ->
      eval' t2 (tm_const n2) ->
      eval' (tm_plus t1 t2) (tm_const n2).

Lemma test_ev'1:forall t,eval' (tm_plus (tm_const 0) (tm_const 1)) t->t=tm_const 1.
Proof.
intros. inversion H. subst.
  inversion H2. subst. inversion H4. subst.
  simpl. reflexivity.
  inversion H4. subst.
  reflexivity.
Qed.

Definition diag_plus' t t' :=
  match t with
    |tm_plus t1 t2 =>
      forall (X:tm -> Prop),
        (forall n1 n2, 
          eval' t1 (tm_const n1) ->
          eval' t2 (tm_const n2) ->
          X (tm_const (plus n1 n2)))
          ->
          (forall n2,
            Q t1 ->
            eval' t2 (tm_const n2) ->
            X (tm_const n2))-> X t'
    |_=>True
  end.

Lemma test_ev'2:forall t,eval' (tm_plus (tm_const 0) (tm_const 1)) t->t=tm_const 1.
Proof.
intros.
generalize
  (match H in (eval' t t')
     return diag_plus' t t' with
     |E_Plus1 _ _ n1 n2 H1 H2 => (fun X k1 k2=> k1 n1 n2 H1 H2)
     |E_Plus2 _ _ n2 H1 H2 => (fun X k1 k2=> k2 n2 H1 H2)
     |_=> I
   end).
clear H. intro k. red in k.
apply k. clear k.
Admitted.

(*
Lemma test_ev1: eval (tm_plus (tm_const 1) (tm_const 0)) (tm_const (plus 1 1)) -> False.
intro. inversion H. subst. inversion H3. subst. inversion H4. subst.
info discriminate.
Qed.
*)

Definition diag_const t t' :=
  match t, t' with
    |tm_const tc, tm_const tc' => forall (X:nat -> Prop), X tc -> X tc'
    |_ ,_=> True
  end.
Definition diag_plus t t' :=
  match t with
    |tm_plus t1 t2 => forall (X:tm -> Prop),
      (forall n1 n2, eval t1 (tm_const n1) ->
                     eval t2 (tm_const n2) ->
                     X (tm_const (plus n1 n2))) -> X t'
    |_ => True
  end.

(*
Lemma test_ev2: eval (tm_plus (tm_const 1) (tm_const 0)) (tm_const 0)->False.
intro. 
pose (diag x:= match x with tm_plus (tm_const 1) (tm_const 0) => False |_=> True end).
change (diag (tm_plus (tm_const 1) (tm_const 0))).
case H. clear H.
simpl.*)

Variable P : tm -> Prop.

Lemma test_ev1': forall t,P t -> eval (tm_plus (tm_const 1) (tm_const 0)) t -> t=tm_const 1%nat.
(*intros. inversion H. subst. inversion H2. subst. inversion H4. subst. simpl. reflexivity.
Qed.*)
intros t H0 H.
generalize
  (match H in (eval t t')
  return diag_plus t t' with
  |E_Plus _ _ n1 n2 H1 H2 => (fun X k => k n1 n2 H1 H2)
  |_=>I
   end).
clear H.
intro k. red in k. revert H0. apply k. clear k. intros.
generalize
  (match H in (eval t t')
     return diag_const t t' with
     |E_Const n => (fun X k => k)
     |_=>I
   end).
clear H.
intro k. red in k. apply k. clear k.
generalize
  (match H0 in (eval t t')
     return diag_const t t' with
     |E_Const n => (fun X k => k)
     |_=>I
   end).
clear H0.
intro k. red in k. apply k. clear k.
simpl. reflexivity.
Qed.

*)

(* The file should compile until this point *)

(*
   match PE in even_i n return P n with E0 => (** $t_\EZ$ *) | E2 e ex => (** $t_\ET$ *) end
*)
(** begin chunk22 *)
        match PE in even_i n return P n with
          | E0 => (** $t_\EZ$ %\coqdoceol% *)
          | E2 e ex => (** $t_\ET$ %\coqdoceol% *)
        end
(** end chunk22 *)

(* ------------------------------------------------------------------------- *)
(* ------------------------------------------------------------------------- *)

(* Include coq code from SimSoC-cert from here *)

(* Constructor eval_valof *)
(** begin chunk40 *)
Definition inv_valof {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m RV ex t m' ex') :=
  let diag e ex ex' m m' :=
    match ex with
      | Evalof a c =>
        forall (X:expr->Prop),
          (forall t a',
            type_is_volatile (typeof a) = false ->
            eval_expr g e m LV a t m' a'->
            X (Evalof a' c)) ->
          (forall t1 a' b ofs t2 v,
            type_is_volatile (typeof a) = true ->
            eval_expr g e m LV a t1 m' a' ->
            eval_simple_lvalue g e m' a' b ofs ->
            deref_loc g (typeof a) m' b ofs t2 v ->
            c = typeof a ->
            X (Eval v c))
          -> X ex'
      | _ =>True
    end in
    match ee in (eval_expr _ e m _ ex _ m' ex')
      return diag e ex ex' m m' with
      |eval_valof _ _ _ t _ a' _ H1 H2 => (fun X k1 k2 => k1 t a' H1 H2)
      |eval_valof_volatile _ _ _ t1 _ a' _ b ofs t2 v H1 H2 H3 H4 H5 =>
        (fun X k1 k2 => k2 t1 a' b ofs t2 v H1 H2 H3 H4 H5)
      | _ => I
    end.
(** end chunk40 *)

(* Proof script using old inversion*)
Lemma same_copy_SR :
  forall e m l b s t m' v em,
    proc_state_related m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m expr_cp_SR t m' v ->
    (forall l b, proc_state_related m' e
      (Ok tt (mk_semstate l b (Arm6_State.set_cpsr s (Arm6_State.spsr s em))))).
Proof.
  intros until em. intros psrel cpsr l b.
  inv cpsr.
  
  (* paste the current goal here *)

(** begin chunk41 *)
  l' : local
  b' : bool
  a' : expr
  H : eval_expr (Genv.globalenv prog_adc) e m RV
         (Ecall (Evalof (Evar copy_StatusRegister T14) T14)
            (Econs
               (Eaddrof
                  (Efield (Ederef (Evalof (Evar proc T3) T3) T6)
                     adc_compcert.cpsr T7) T8)
               (Econs
                  (Ecall (Evalof (Evar spsr T15) T15)
                     (Econs (Evalof (Evar proc T3) T3) Enil) T8) Enil))
            T12) t m' a'
  ============================
   proc_state_related m' e st'
(** end chunk41 *)

(** begin chunk42 *)
  inv H. inv H4. inv H9. inv H5. inv H4. inv H5. 
  inv H15. inv H4. inv H5. inv H14. inv H4. inv H3. 
  inv H15. inv H5. inv H4. inv H5. inv H21. inv H13.
(** end chunk42 *)
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m4 vargs0 t5 m2 vres0 l b s) 
    in psrel; [idtac|exact H18|exact H23].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m2 vargs t3 m' vres l' b'
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em)))
    in psrel; [idtac|exact H11|exact H16].
  exact psrel.
Qed.

(** begin chunk43 *)
Lemma same_cp_SR :
  forall e m l b s t m' v em,
    proc_state_related proc m e (Ok tt (mk_semstate l b s)) ->
    eval_expression (Genv.globalenv prog_adc) e m cp_SR t m' v ->
    proc_state_related proc m' e
      (Ok tt (mk_semstate l b
      (Arm6_State.set_cpsr s (Arm6_State.spsr s em)))).
(** end chunk43 *)

(* Proof script using ad-hoc inversion*)
Proof.
  intros until em. intros psrel cpsr.
  inv cpsr. rename H into ee,H0 into esrv. unfold cp_SR in ee.
  inv_eval_expr m m'.
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m vargs0 t9 m3 vres0 l b s)
    in psrel; [idtac|exact Heqff0|exact ev_funcall].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m3 vargs t2 m' vres l b
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em))) in psrel;
  [idtac|exact Heqff|exact ev_funcall0].
  exact psrel.
Qed.

(* Proof script using inv *)
Proof.
  intros until em. intros psrel cpsr.
  inv cpsr.
  unfold cp_SR in H.  
  inv H. inv H4. inv H9.
  inv H5.
  inv H4. inv H5. inv H15. inv H4. inv H5.
  inv H14.
  inv H4. inv H3. inv H15.
  inv H5.
  inv H4. inv H5.
  inv H21.
  inv H13.
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m4 vargs0 t5 m2 vres0 l b s)
    in psrel; [idtac|exact H18|exact H23].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m2 vargs t3 m' vres l b
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em))) in psrel;
  [idtac|exact H11|exact H16].
  exact psrel.
Qed.

(* Proof script using BasicElim *)
Proof.
  intros until em. intros psrel cpsr.
  inversion cpsr. subst. rename H into ee,H0 into esrv. unfold cp_SR in ee.
  try (repeat (generalize_eqs_vars ee; destruct ee; simplify_dep_elim)).
  try (repeat (generalize_eqs_vars H; destruct H; simplify_dep_elim)).
  try (repeat (generalize_eqs_vars H6; destruct H6; simplify_dep_elim)).
  try (repeat (generalize_eqs_vars H; destruct H; simplify_dep_elim)).
  try (repeat (generalize_eqs_vars H6; destruct H6; simplify_dep_elim)).
  try (repeat (generalize_eqs_vars H; destruct H; simplify_dep_elim)).  
  unfold block in H2, H3, H4, H9, H10, H11.
  (* Time inv_eval_expr m m'. *)
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m vargs0 t0 m0 vres0 l b s)
    in psrel; [idtac|exact H10|exact H12].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m0 vargs t3 m3 vres l b
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em))) in psrel;
  [idtac|exact H3|exact H5].
  exact psrel.
Qed.

(* Proof script using derive inversion *)
Proof.
  intros until em. intros psrel cpsr.
  inv cpsr.
  unfold cp_SR in 
  inversion H using leminveval; try discriminate;
  intros; subst; clear H;
  injection H11; intros; subst; clear H11 H1 H10.
  inversion H2 using leminveval; try discriminate;
  intros; subst; clear H2;
  injection H10; intros; subst; clear H10 H H9.
  inversion H14 using leminveval; try discriminate;
  intros; subst; clear H14;
  injection H9; intros; subst; clear H H9 H8.
  inversion H3 using leminveval_list; try discriminate;
  intros; subst; clear H3;
  injection H8; intros; subst; clear H H8.
  inversion H12 using leminveval; try discriminate;
  intros; subst; clear H12;
  injection H8; intros; subst; clear H H8 H3.
  inversion H14 using leminveval; try discriminate;
  intros; subst; clear H14;
  injection H8; intros; subst; clear H H8 H3.
  inversion H12 using leminveval; try discriminate;
  intros; subst; clear H12;
  injection H8; intros; subst; clear H H8 H3.
  inversion H14 using leminveval; try discriminate;
  intros; subst; clear H14;
  injection H8; intros; subst; clear H H8 H3.
  inversion H12 using leminveval; try discriminate;
  intros; subst; clear H12;
  injection H8; intros; subst; clear H H8 H3.
  inversion H13 using leminveval_list; try discriminate;
  intros; subst; clear H13;
  injection H1; intros; subst; clear H1 H.
  inversion H11 using leminveval; try discriminate;
  intros; subst; clear H11;
  injection H1; intros; subst; clear H1 H H10.
  inversion H3 using leminveval; try discriminate;
  intros; subst; clear H3;
  injection H9; intros; subst; clear H H8 H9.
  inversion H14 using leminveval; try discriminate;
  intros; subst; clear H14;
  injection H8; intros; subst; clear H H8 H3.
  inversion H17 using leminveval_list; try discriminate;
  intros; subst; clear H17;
  injection H1; intros; subst; clear H1 H.
  inversion H11 using leminveval; try discriminate;
  intros; subst; clear H11;
  injection H8; intros; subst; clear H H8 H3.
  inversion H17 using leminveval; try discriminate;
  intros; subst; clear H17;
  injection H8; intros; subst; clear H H8 H3.
  inversion H13 using leminveval_list; try discriminate;
  intros; subst; clear H13; clear H3 H.
  inversion H12 using leminveval_list; try discriminate;
  intros; subst; clear H12; clear H3 H.  
  (* Function spsr, get spsr from the current state *)
  apply (functions_behavior_ok e l b s vf0 fd0 m5 vargs0 t5 m2 vres0 l b s)
    in psrel; [idtac|exact H21|exact H23].
  (* Function copy_StatusRegister, copy the current spsr to cpsr*)
  apply (functions_behavior_ok e l b s vf fd m2 vargs t3 m' vres l b
    (Arm6_State.set_cpsr s (Arm6_State.spsr s em))) in psrel;
  [idtac|exact H7|exact H16].
  exact psrel.
Qed.

Definition cp_SR' :=
(** begin chunk45 *)
  Ecall
  (Evalof (Evar copy_StatusRegister T14) T14)
  (Econs
    (Eaddrof
      (Efield
        (Ederef (Evalof (Evar adc_compcert.proc T3) T3) T6)
        cpsr T7) T8)
    (Econs
      (Ecall (Evalof (Evar spsr T15) T15)
        (Econs (Evalof (Evar adc_compcert.proc T3) T3)
          Enil) T8) Enil)) T12.
(** end chunk45 *)

(* Excerpt from Cstrategy.v *)
(** begin chunk50 *)
Inductive eval_expr :
  env -> mem -> kind -> expr -> trace -> mem -> expr -> Prop :=
  ...
  | eval_field: forall e m a t m' a' f ty,
      eval_expr e m RV a t m' a' ->
      eval_expr e m LV (Efield a f ty) t m' (Efield a' f ty)
(** end chunk50 *)

(* Excerpt from general inversion tactic on eval_expr from m to m' *)
(** begin chunk51 *)
Ltac inv_eval_expr m m' :=
  ...
  let t1_:=fresh "t" in
  let v1_:=fresh "v" in
  let ev_ex1 := fresh "ev_ex" in
  ...
  match goal with
  ...
    | [ee: eval_expr ?ge ?e m LV (Efield ?a ?f ?ty) ?t m' ?a' |- ?cl] =>
      apply (inv_field ee); clear ee; intros t1_ a1_ ev_ex1; intros;
      inv_eval_expr m m'
(** end chunk51 *)

(** begin chunk52 *)
Definition inv_field {g} {e} {m} {ex} {t} {m'} {ex'}
  (ee:eval_expr g e m LV ex t m' ex') :=
  let diag e ex ex' m m' :=
    match ex with
      | Efield a b c => 
        forall(X:expr->Prop),
          (forall t a', eval_expr g e m RV a t m' a' -> X (Efield a' b c)) -> X ex'
      | _ => True
    end in
    match ee in (eval_expr _ e m _ ex _ m' ex') return diag e ex ex' m m' with
      | eval_field _ _ _ t _ a' _ _ H1 =>   fun X k => k t a' H1
      | _ => I
    end.
(** end chunk52 *)


(* General inversion tactic on eval_expr from m to m' *)
Ltac inv_eval_expr m m' :=
  let f:=fresh "f" in
  let nexp:=fresh "nexp" in
  let a_:=fresh "a" in
  let a'_:=fresh "a'" in
  (*ev_funcall*)
  let rf_:=fresh "rf" in
  let t1_:=fresh "t" in
  let t2_:=fresh "t" in
  let t3_:=fresh "t" in
  let m1_:=fresh "m" in
  let m2_:=fresh "m" in
  let rf'_:= fresh "rf'" in
  let rargs'_:=fresh "rargs'" in
  let vf_:=fresh "vf" in
  let vargs_:=fresh "vargs" in
  let targs_:=fresh "targs" in
  let tres_:=fresh "tres" in
  let fd_:=fresh "fd" in
  let vres_:=fresh "vres" in
  let ty_:=fresh "ty" in
  let ev_ex:=fresh "ev_ex" in
  let ev_elst:=fresh "ev_eslst" in
  let esr1:=fresh "esr" in
  let esr2:=fresh "esr" in
  let Heqcf:=fresh "Heqcf" in
  let eslst:=fresh "eslst" in
  let Heqff:=fresh "Heqff" in
  let Heqtf:=fresh "Heqtf" in
  let ev_funcall:=fresh "ev_funcall" in
  (* ev_condition *)
  let a1_:=fresh "a" in
  let a2_:=fresh "a" in
  let v1_:=fresh "v" in
  let v2_:=fresh "v" in
  let v3_:=fresh "v" in
  let b_:=fresh "b" in
  let ev_ex1 := fresh "ev_ex" in
  let ev_ex2 := fresh "ev_ex" in
  let bv := fresh "bv" in
  let semcast:=fresh "semcast" in
  let smpl := fresh "smpl" in
  (* assignment *)
  let ofs_ := fresh "ofs" in
  let esl := fresh "esl" in
  let svot := fresh "svot" in
  (* exprlist *)
  let alst := fresh "alst" in
  match goal with
    |[ee:eval_expr ?ge ?e m ?k ?ex ?et ?m' ?ex'|-?cl]=>
      pose(next_m := m'); pose(next_e := ex');
      change m' with next_m in ee; change ex' with next_e in ee;
      repeat(match goal with [h: context c [m']|-?cl]=>revert h end||idtac);
      repeat(match goal with [h: context c [ex']|-?cl]=> revert h end||idtac);
      unfold next_m,next_e in ee;clear next_m next_e
  end;
  match goal with
    |[ee:eval_expr ?ge ?e m RV (Eval ?v ?ty) ?et m' ?a'|-?cl]=>
      apply (inv_val ee); clear ee; try intros
    |[ee:eval_expr ?ge ?e m LV (Evar ?x ?ty) ?et m' ?a'|-?cl]=>
      apply (inv_var ee); clear ee; try intros
    |[ee:eval_expr ?ge ?e m LV (Efield ?a ?f ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_field ee); clear ee; intros t1_ a1_ ev_ex1; try intros;
      inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Evalof ?a ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_valof ee); clear ee;
      (*intros t1_ a_ ev_ex;*) try intros;
      inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m LV (Ederef ?a ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_deref ee); clear ee; intros t2_ a2_ ev_ex1; try intros;
      inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Eaddrof ?a ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_addrof ee); clear ee; intros t1_ a1_; intros ev_ex1; try intros;
      inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Eunop ?op ?a ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_unop ee); clear ee; intros;inv_eval_expr m m'
    |[ee:eval_expr ?ge ?e m RV (Ebinop ?op ?a1 ?a2 ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_binop ee); clear ee; intros t1_ m1_ a1_ t2_ a2_ ev_ex1 ev_ex2;
      try intros;
      try
      (match goal with
        |[ee1:eval_expr ?ge ?e m ?k a1 ?t1 ?mbo ?a1'|-?cl1]=>
          (*if the inversion before may give a equality saying that
             m = m?, and m will be replaced by m?. So the order will
             be, invert the hypothesis related to the lase memory 
             state first, then step backward *)          
          inv_eval_expr mbo m';
          inv_eval_expr m mbo
      end)
    (*|[ee:eval_expr ?ge ?e m RV (Ecast ?a ?ty) ?t m' ?a'|-?cl]=>
      inv ee;inv_eval_expr m m'*)
    |[ee:eval_expr ?ge ?e m RV (Econdition ?a1 ?a2 ?a3 ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_condition ee); clear ee;
      intros t1_ m1_ a1_ v1_ t2_ a2_ v2_ b_ v3_;
      intros smpl ev_ex1 esr1 bv ev_ex2 esr2 semcast;
      try intros;
      try
      (match goal with
        |[ee1: eval_expr ge e m RV a1 ?t1 ?mcond ?a1'|-?cl1]=>
          inv_eval_expr m mcond
      end)
    (*|[ee:eval_expr ?ge ?e m RV (Esizeof ?ty' ?ty) ?t m ?a'|-?cl]=>
      inv ee*)
    |[ee:eval_expr ?ge ?e m RV (Eassign ?l ?r ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_assign ee); clear ee;
      intros t1_ m1_ a1_ t2_ m2_ a2_ b_ ofs_ v1_ v2_ ;
      intros ev_ex1 ev_ex2 esl esr1 semcast svot Heqtf;
      try intros;
      try
      (match goal with
        |[ee1:eval_expr ge e m LV l ?t1 ?masgn1 ?l'|-?cl]=>
          try
          (match goal with
            |[ee2:eval_expr ge e masgn1 RV r ?t2 ?masgn2 ?r'|-?cl]=>
              inv_eval_expr masgn1 masgn2;
              inv_eval_expr m masgn1
          end)
      end)
    (*|[ee:eval_expr ?ge ?e m RV (Eassignop ?op ?l ?r ?tyres ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      try
      (match goal with
        |[ee1:eval_expr ge e m LV l ?t1 ?masgnop1 ?l'|-?cl]=>
          try
          (match goal with
            |[ee2:eval_expr ge e masgnop1 RV r ?t2 ?masgnop2 ?r'|-?cl]=>
              inv_eval_expr masgnop1 masgnop2;
              inv_eval_expr m masgnop1
          end)
      end)
    |[ee:eval_expr ?ge ?e m RV (Epostincr ?id ?l ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      try
      (match goal with
        |[ee1:eval_expr ge e m LV l t ?mpi ?l'|-?cl]=>
          inv_eval_expr m mpi
      end)
    |[ee:eval_expr ?ge ?e m RV (Ecomma ?r1 ?r2 ?ty) ?t m' ?a'|-?cl]=>
      inv ee;
      match goal with
        |[ee1:eval_expr ge e m RV r1 ?t1 ?mcom ?r1'|-?cl]=>
          inv_eval_expr m mcom; inv_eval_expr mcom m'
      end*)
    |[ee:eval_expr ?ge ?e m RV (Ecall ?rf ?rargs ?ty) ?t m' ?a'|-?cl]=>
      apply (inv_call ee); clear ee;
        intros t1_ m1_ rf'_ t2_ m2_ rargs'_ vf_ vargs_ targs_ tres_ fd_ t3_ 
          vres_;
        intros ev_ex ev_elst esr1 eslst Heqcf Heqff Heqtf 
          ev_funcall esr2;
      try
      (match goal with
        |[ee1:eval_expr ge e m RV rf ?t1 ?mc1 ?rf'|-?cl]=>
          try
          (match goal with
            |[eel:eval_exprlist ge e mc1 ?rargs ?t2 ?mc2 ?rargs'|-?cl]=>
              inv_eval_expr mc1 mc2;
              inv_eval_expr m mc1
          end)
      end)
    |[eel:eval_exprlist ?ge ?e m (Econs ?a1 ?al) ?t m' ?rargs'|-?cl]=>
      apply (inv_cons eel); clear eel;
      intros t1_ m1_ a1_ t2_ alst ev_ex1 ev_elst;
      try intros;
      try
      (match goal with
        |[eel1:eval_expr ge e m RV a1 ?t1 ?ml1 ?a1'|-?cl]=>
          inv_eval_expr ml1 m';
          inv_eval_expr m ml1
      end)
    |[eel:eval_exprlist ?ge ?e m Enil ?t m' ?al'|-?cl]=>
      apply (inv_nil eel); clear eel
    |_=> pose(f:=0)
  end.

(* It may be useless to try make it compilable *)
(* However let us hope that coqdoc will still be happy *)
