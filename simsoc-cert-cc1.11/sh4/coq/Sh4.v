(**
SimSoC-Cert, a toolkit for generating certified processor simulators.

See the COPYRIGHTS and LICENSE files.

Formalization of the SH4 architecture following the:

SH-4, Software Manual, Renesas 32-Bit RISC, Rev.6.00 2006.09

Page numbers refer to Renesas_SH4_2006.pdf.

Basic types and functions for describing the SH4 state.
*)

Set Implicit Arguments.

Require Import Integers Bitvec ZArith Coqlib Util.

(****************************************************************************)
(** Processor modes *)
(****************************************************************************)

Inductive proc_mode : Type := usr.

(****************************************************************************)
(**  Registers *)
(****************************************************************************)

Definition SR := mk_regnum 16. (* Control Register *)
Definition SSR := mk_regnum 17. (* Control Register *)
Definition GBR := mk_regnum 18. (* Control Register *)
Definition MACH := mk_regnum 19. (* System Register *)
Definition MACL := mk_regnum 20. (* System Register *)
Definition PR := mk_regnum 21. (* System Register *)
Definition VBR := mk_regnum 22. (* Control Register *)
Definition PC := mk_regnum 23. (* System Register *)
Definition SPC := mk_regnum 24. (* Control Register *)
Definition SGR := mk_regnum 25. (* Control Register *)
Definition DBR := mk_regnum 26. (* Control Register *)

(* *)

Definition FPSCR := mk_regnum 100. (* System Register (* Floating Point Unit *) *)
Definition FPUL := mk_regnum 101. (* System Register (* Floating Point Unit *) *)

Definition PTEH := mk_regnum 102. (* MMU Related Register *)
Definition PTEL := mk_regnum 103. (* MMU Related Register *)
Definition PTEA := mk_regnum 104. (* MMU Related Register *)
                              
Definition EXPEVT := mk_regnum 105. (* Exception Related Register *)
Definition TRA := mk_regnum 106. (* Exception Related Register *)

(* *)

Inductive register : Type :=
| R (k : regnum).

Lemma register_eqdec : forall x y : register, {x=y}+{~x=y}.
Proof.
destruct x; destruct y; intros; try (right; discriminate).
destruct (Regnum.eq_dec k k0). subst. auto.
right. intro h. inversion h. contradiction.
Qed.

Definition reg_mode (m : proc_mode) (k : regnum) : register := R k.

(****************************************************************************)
(**  Memory *)
(****************************************************************************)

Inductive memory : Type :=
| M : Int.int -> memory.

(****************************************************************************)
(** Program status registers *)
(****************************************************************************)

Definition proc_mode_of_word (w : word) : option proc_mode := Some usr.

Inductive instruction_set : Set := SH4 (* COQBUG #843 : If the declaration has type [Prop], the OCaml extracted code is not well-typed *).

Definition inst_set (w : word) : option instruction_set := Some SH4.

(* 2.2.4 page 35 *)
Definition Tbit := 0%nat.
Definition Sbit := 1%nat.
Definition Qbit := 8%nat.
Definition Mbit := 9%nat.
Definition BLbit := 28%nat.
Definition RBbit := 29%nat.
Definition MDbit := 30%nat.

(****************************************************************************)
(** Exceptions *)
(****************************************************************************)

Inductive exception : Set :=
  UndIns (* COQBUG #843 : If the declaration has type [Prop], the OCaml extracted code is not well-typed *).

(****************************************************************************)
(* Exception priorities *)
(****************************************************************************)

Definition priority (e : exception) : BinInt.Z :=
  match e with
    | UndIns => 7 (* lowest *)
  end.

(*WARNING: by using this function, exceptions are always sorted from
the highest priority to the lowest, so that the exception with highest
priority is the first one *)

Fixpoint insert (e : exception) (l : list exception) : list exception :=
  match l with
    | nil => e :: nil
    | e' :: l' => if zlt (priority e) (priority e') then e :: l
      else e' :: insert e l'
  end.

(****************************************************************************)
(* The condition field *)
(****************************************************************************)

(****************************************************************************)
(** Condition codes *)
(****************************************************************************)
