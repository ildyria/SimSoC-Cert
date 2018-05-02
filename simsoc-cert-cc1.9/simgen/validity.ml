(**
SimSoC-Cert, a toolkit for generating certified processor simulators
See the COPYRIGHTS and LICENSE files.

List of the additional validity constraints that an instruction must
satisfy in order to be predictable.
*)

(* NB: some constraints given below are used to distinguish between
 *     cases which are likely to be equivalent:
 *
 * example: cpy r0, r1 <=> mov r0, r1 <=> mov r0, r1 LSL #0
 *
 * Theses cases are not considered as unpredictable not undefined in
 * the specification *)

open Ast;;

type vconstraint =
  | NotPC of string    (* the string must contains the name of the parameter *)
  | NotLR of string    (* the string must contains the name of the parameter *)
  | IsEven of string   (* a parameter that should contain an even value *)
  | NotZero of string  (* a parameter that should not be zero *)
  | NotZero2 of string * string  (* two parameters that should not be zero together *)
  | NoWritebackDest    (* no write-back with Rd==Rn *)
  | NotSame of string * string (* R<a> <> R<b> *)
  | NotLSL0            (* to distinguished between (equivalent?) mode cases *)
  | Not2lowRegs        (* not (H1 == 0 && H2 == 0), for thumb isntructions *)
  | BLXbit0            (* special constraint for the thumb BLX (1) instruction *)
  | Or of vconstraint list * vconstraint list
  | NotV of string * int
  | OtherVC of exp     (* Other validy constraints described by a boolean
                        * expression *)

let constraints =
  let cs = Hashtbl.create 150 in
    Hashtbl.add cs "BLX2" [NotPC "m"];
    Hashtbl.add cs "BXJ" [NotPC "m"];
    Hashtbl.add cs "CLZ" [NotPC "m"; NotPC "d"];
    Hashtbl.add cs "LDM1" [NotPC "n"; NotZero "register_list"];
    Hashtbl.add cs "LDM2" [NotPC "n"; NotZero "register_list"];
    Hashtbl.add cs "LDM3" [NotPC "n"];
    Hashtbl.add cs "LDR" [NoWritebackDest];
    Hashtbl.add cs "LDRB" [NotPC "d"; NoWritebackDest];
    Hashtbl.add cs "LDRBT" [NotPC "d"; NotSame ("d", "n")];
    Hashtbl.add cs "LDRD" [NotPC "d"; NotLR "d"; IsEven "d"]; (* FIXME: UNDEFINED if "d" is odd *)
    Hashtbl.add cs "LDREX" [NotPC "d"; NotPC "n"];
    Hashtbl.add cs "LDRH" [NotPC "d"; NoWritebackDest];
    Hashtbl.add cs "LDRSB" [NotPC "d"; NoWritebackDest];
    Hashtbl.add cs "LDRSH" [NotPC "d"; NoWritebackDest];
    Hashtbl.add cs "LDRT" [NotPC "d"; NotSame ("d", "n")];
    Hashtbl.add cs "MCR" [NotPC "d"];
    Hashtbl.add cs "MCRR" [NotPC "d"; NotPC "n"; NotSame ("d", "n")];
    Hashtbl.add cs "MLA" [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "MOV" [OtherVC (Fun ("not_cpy_instr", [Var "bincode"]))];
    Hashtbl.add cs "MRRC" [NotPC "d"; NotPC "n"; NotSame ("d", "n")];
    Hashtbl.add cs "MRS" [NotPC "d"];
    Hashtbl.add cs "MUL" [NotPC "d"; NotPC "m"; NotPC "s"];
    Hashtbl.add cs "PKHBT" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "PKHTB" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QADD" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QADD16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QADD8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QADDSUBX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QDADD" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QDSUB" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QSUB" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QSUB16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QSUB8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "QSUBADDX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "REV" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "REV16" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "REVSH" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "RFE" [NotPC "n"];
    Hashtbl.add cs "SADD16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SADD8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SADDSUBX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SEL" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SHADD16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SHADD8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SHADDSUBX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SHSUB16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SHSUB8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SHSUBADDX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SMLAxy" [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "SMLAD" [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "SMLAL" [NotPC "dHi"; NotPC "dLo"; NotPC "m";
                            NotPC "s"; NotSame ("dHi", "dLo")];
    Hashtbl.add cs "SMLALxy" [NotPC "dHi"; NotPC "dLo"; NotPC "m";
                              NotPC "s"; NotSame ("dHi", "dLo")];
    Hashtbl.add cs "SMLALD" [NotPC "dHi"; NotPC "dLo"; NotPC "m";
                             NotPC "s"; NotSame ("dHi", "dLo")];
    Hashtbl.add cs "SMLAWy" [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "SMLSD" [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "SMLSLD" [NotPC "dHi"; NotPC "dLo"; NotPC "m"; NotPC "s";
                             NotSame ("dHi", "dLo")];
    Hashtbl.add cs "SMMLA" [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "SMMLS" [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "SMMUL" [NotPC "d"; NotPC "m"; NotPC "s"];
    Hashtbl.add cs "SMUAD" [NotPC "d"; NotPC "m"; NotPC "s"];
    Hashtbl.add cs "SMULxy" [NotPC "d"; NotPC "m"; NotPC "s"];
    Hashtbl.add cs "SMULL" [NotPC "dHi"; NotPC "dLo"; NotPC "m"; NotPC "s";
                            NotSame ("dHi", "dLo")];
    Hashtbl.add cs "SMULWy" [NotPC "d"; NotPC "m"; NotPC "s"];
    Hashtbl.add cs "SMUSD" [NotPC "d"; NotPC "m"; NotPC "s"];
    Hashtbl.add cs "SSAT" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "SSAT16" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "SSUB16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SSUB8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SSUBADDX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "STM1" [NotPC "n"; NotZero "register_list"];
    Hashtbl.add cs "STM2" [NotPC "n"; NotZero "register_list"];
    Hashtbl.add cs "STR" [NoWritebackDest];
    Hashtbl.add cs "STRB" [NoWritebackDest; NotPC "d"];
    Hashtbl.add cs "STRBT" [NotPC "d"; NotSame ("d", "n")];
    Hashtbl.add cs "STRD" [NotLR "d"; IsEven "d"]; (* FIXME: UNDEFINED if "d" is odd *)
    Hashtbl.add cs "STREX" [NotPC "d"; NotPC "n"; NotPC "m";
                            NotSame ("d", "n"); NotSame ("d", "m")];
    Hashtbl.add cs "STRH" [NoWritebackDest; NotPC "d"];
    Hashtbl.add cs "STRT" [NotSame ("d", "n")];
    Hashtbl.add cs "SWP" [NotPC "d"; NotPC "n"; NotPC "m";
                          NotSame ("n", "m"); NotSame ("n", "d")];
    Hashtbl.add cs "SWPB" [NotPC "d"; NotPC "n"; NotPC "m";
                           NotSame ("n", "m"); NotSame ("n", "d")];
    Hashtbl.add cs "SXTAB" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SXTAB16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SXTAH" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "SXTB" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "SXTB16" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "SXTH" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "UADD16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UADD8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UADDSUBX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UHADD16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UHADD8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UHADDSUBX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UHSUB16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UHSUB8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UHSUBADDX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UMAAL" [NotPC "dHi"; NotPC "dLo"; NotPC "m";
                            NotPC "s"; NotSame ("dHi", "dLo")];
    Hashtbl.add cs "UMLAL" [NotPC "dHi"; NotPC "dLo"; NotPC "m";
                            NotPC "s"; NotSame ("dHi", "dLo")];
    Hashtbl.add cs "UMULL" [NotPC "dHi"; NotPC "dLo"; NotPC "m";
                            NotPC "s"; NotSame ("dHi", "dLo")];
    Hashtbl.add cs "UQADD16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UQADD8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UQADDSUBX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UQSUB16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UQSUB8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UQSUBADDX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "USAD8" [NotPC "d"; NotPC "m"; NotPC "s"];
    Hashtbl.add cs "USADA8" [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "USAT" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "USAT16" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "USUB16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "USUB8" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "USUBADDX" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UXTAB" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UXTAB16" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UXTAH" [NotPC "d"; NotPC "m"; NotPC "n"];
    Hashtbl.add cs "UXTB" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "UXTB16" [NotPC "d"; NotPC "m"];
    Hashtbl.add cs "UXTH" [NotPC "d"; NotPC "m"];
    (* 117 instructions in this table / 148 *)
    Hashtbl.add cs "M1_LSLImm"
      [NotZero "shift_imm"]; (* to distinguish from (equivalent?) M1_Register *)
    Hashtbl.add cs "M1_LSLReg"
      [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "M1_LSRReg"
      [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "M1_ASRReg"
      [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    Hashtbl.add cs "M1_RRImm"
      [NotZero "shift_imm"];
    Hashtbl.add cs "M1_RRReg"
      [NotPC "d"; NotPC "m"; NotPC "s"; NotPC "n"];
    (* 6 mode 1 cases in this table / 11 *)
    Hashtbl.add cs "M2_RegOff" [NotPC "m"];
    Hashtbl.add cs "M2_ScRegOff" [NotPC "m"; NotLSL0];
    Hashtbl.add cs "M2_Imm_preInd" [NotPC "n"];
    Hashtbl.add cs "M2_Reg_preInd" [NotPC "n"; NotPC "m"];
    Hashtbl.add cs "M2_ScReg_preInd"
      [NotPC "n"; NotPC "m"; NotLSL0];
    Hashtbl.add cs "M2_Imm_postInd" [NotPC "n"];
    Hashtbl.add cs "M2_Reg_postInd" [NotPC "n"; NotPC "m"];
    Hashtbl.add cs "M2_ScReg_postInd"
      [NotPC "n"; NotPC "m"; NotLSL0];
    (* 8 mode 2 cases in this table / 9 *)
    Hashtbl.add cs "M3_RegOff" [NotPC "m"];
    Hashtbl.add cs "M3_Imm_preInd" [NotPC "n"];
    Hashtbl.add cs "M3_Reg_preInd" [NotPC "n"; NotPC "m"];
    Hashtbl.add cs "M3_Imm_preInd" [NotPC "n"];
    Hashtbl.add cs "M3_Reg_preInd" [NotPC "n"; NotPC "m"];
    (* 5 mode 3 cases in this table / 6 *)
    (* no constraints for mode 4 *)
    Hashtbl.add cs "M5_Imm_preInd" [NotPC "n"];
    Hashtbl.add cs "M5_Imm_postInd" [NotPC "n"];
    Hashtbl.add cs "M5_U" [NotZero "U"];
    (* 3 mode 5 cases in this table / 4 *)
    Hashtbl.add cs "Tb_ADD1" [NotZero "immed_3"]; (* MOV (2) otherwise *)
    Hashtbl.add cs "Tb_ADD4" [Not2lowRegs];
    Hashtbl.add cs "Tb_B1" [OtherVC (Fun ("not_AL_cond", [Var "cond"]))];
                                                (* undefined otherwise *)
    Hashtbl.add cs "Tb_BL" [NotZero "H"; BLXbit0];
    Hashtbl.add cs "Tb_BLX2" [NotPC "m"];
    Hashtbl.add cs "Tb_CMP3" [NotPC "n"; Not2lowRegs];
    Hashtbl.add cs "Tb_LDMIA" [NotZero "register_list"];
    Hashtbl.add cs "Tb_MOV3" [Not2lowRegs];
    Hashtbl.add cs "Tb_POP" [NotZero2 ("R", "register_list")];
    Hashtbl.add cs "Tb_PUSH" [NotZero2 ("R", "register_list")];
    (* 9 Thumb instructions in this table / 73 *)
    cs;;

(* REMARK: constraints that cannot be checked statically are not managed in this file *)

(* FIXME: other constraints not taken into account yet:
 * CPS:  not ( (imod == 0b00 && mmod == 0) ||
               (imod == 0b01 && mmod == 0) ||
               (imod == 0b01 && mmod == 1) )
 * LDM1, LDM3: not (W && n in register_list)
 * LDRD, STRD: NoWritebackDest(Rd and Rd+1), Rm!=Rd, Rm!=Rd+1
 * STM1, STMIA: not (Rn in register_list && W && not (lowest-numbered Rn))
 *
 * BKPT: cond must be AL (already 0b1110 in the coding table)
 * LDM2, STM2: not bit[21] (already 0 in their coding tables)
 * PLD: bit[24] && not bit[21] (already fixed to the right values in the coding table)
 *)

(* check whether the instruction i has some constraints *)
let has_constraints i = Hashtbl.mem constraints i;;

(* get the constraints associated to i *)
let get_constraints i =
  try Hashtbl.find constraints i
  with Not_found -> [];;

(* generate an expression that check the constraints *)
exception Empty_list;;
let rec vcs_to_exp vcs :Ast.exp option=
  let aux vc = match vc with
    | NotPC s -> BinOp (Var s, "!=", Num "15")
    | NotLR s -> BinOp (Var s, "!=", Num "14")
    | IsEven s -> Fun ("is_even", [Var s])
    | NotZero s -> BinOp (Var s, "!=", Num "0")
    | NotZero2 (s1, s2) ->
        let a = BinOp (Var s1, "!=", Num "0")
        and b = BinOp (Var s2, "!=", Num "0")
        in BinOp (a, "or", b)
    | NoWritebackDest ->
        let w = BinOp (Var "W", "==", Num "0") in
        let r = BinOp (Var "n", "!=", Var "d") in
          BinOp (w, "or", r)
    | NotSame (s1, s2) -> BinOp (Var s1, "!=", Var s2)
    | NotLSL0 ->
        let a = BinOp (Var "shift", "!=", Num "0") in
        let b = BinOp (Var "shift_imm", "!=", Num "0") in
          BinOp (a, "or", b)
    | Not2lowRegs -> 
        let e1 = BinOp (Var "H1", "!=", Num "0") in
        let e2 = BinOp (Var "H2", "!=", Num "0") in
          BinOp (e1, "or", e2)
    | BLXbit0 ->
        let h = BinOp (Var "H", "!=", Bin "0b01") in
        let o1 = BinOp (Var "offset_11", "AND", Num "1") in
          BinOp (h, "or", BinOp (o1, "==", Num "0"))
    | Or (l1, l2) -> 
	let a = vcs_to_exp l1 in let b = vcs_to_exp l2 in
	  begin match a,b with
	    | None, None -> raise Empty_list
	    | Some a, Some b -> BinOp (a, "or", b)
	    | None, Some b -> b
	    | Some a, None -> a
	  end
    | NotV (s, i) -> 
	BinOp (Var s, "!=", Num (Char.escaped (char_of_int i)))
    | OtherVC e -> e
  in
  let rec auxl vcs = match vcs with
    | [] -> raise Empty_list
    | [vc] -> aux vc
    | vc :: vcs -> BinOp (aux vc, "and", auxl vcs)
  in
    try Some (auxl vcs)
    with Empty_list -> None;;

let to_exp i = vcs_to_exp (get_constraints i);;
