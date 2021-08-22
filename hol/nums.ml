(* ========================================================================= *)
(* The axiom of infinity; construction of the natural numbers.               *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Parser
open Equal
open Boolean
open Tactics
open Simp
open Theorems
open Ind_defs
open Class
open Meson
open Pair
;;

(* ------------------------------------------------------------------------- *)
(* Declare a new type "ind" of individuals.                                  *)
(* ------------------------------------------------------------------------- *)

new_type ("ind",0);;

(* ------------------------------------------------------------------------- *)
(* We assert the axiom of infinity as in HOL88, but then we can forget it!   *)
(* ------------------------------------------------------------------------- *)

let vONE_ONE = new_definition
  (parse_term "ONE_ONE(f:A->B) = !x1 x2. (f x1 = f x2) ==> (x1 = x2)");;

let vONTO = new_definition
  (parse_term "ONTO(f:A->B) = !y. ?x. y = f x");;

let vINFINITY_AX = new_axiom
  (parse_term "?f:ind->ind. ONE_ONE f /\\ ~(ONTO f)");;

(* ------------------------------------------------------------------------- *)
(* Actually introduce constants.                                             *)
(* ------------------------------------------------------------------------- *)

let vIND_SUC_0_EXISTS = prove
 ((parse_term "?(f:ind->ind) z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\\ (!x. ~(f x = z))"),
  vX_CHOOSE_TAC (parse_term "f:ind->ind") vINFINITY_AX ----> vEXISTS_TAC (parse_term "f:ind->ind") ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vONE_ONE; vONTO] ----> vMESON_TAC[]);;

let vIND_SUC_SPEC =
  let th1 = new_definition
   (parse_term "IND_SUC = @f:ind->ind. ?z. (!x1 x2. (f x1 = f x2) = (x1 = x2)) /\\\n                                (!x. ~(f x = z))") in
  let th2 = vREWRITE_RULE[vGSYM th1] (vSELECT_RULE vIND_SUC_0_EXISTS) in
  let th3 = new_definition
   (parse_term "IND_0 = @z:ind. (!x1 x2. IND_SUC x1 = IND_SUC x2 <=> x1 = x2) /\\\n                    (!x. ~(IND_SUC x = z))") in
  vREWRITE_RULE[vGSYM th3] (vSELECT_RULE th2);;

let vIND_SUC_INJ,vIND_SUC_0 = vCONJ_PAIR vIND_SUC_SPEC;;

(* ------------------------------------------------------------------------- *)
(* Carve out the natural numbers inductively.                                *)
(* ------------------------------------------------------------------------- *)

let vNUM_REP_RULES,vNUM_REP_INDUCT,vNUM_REP_CASES =
  new_inductive_definition
   (parse_term "NUM_REP IND_0 /\\\n    (!i. NUM_REP i ==> NUM_REP (IND_SUC i))");;

let num_tydef = new_basic_type_definition
  "num" ("mk_num","dest_num")
    (vCONJUNCT1 vNUM_REP_RULES);;

let vZERO_DEF = new_definition
 (parse_term "_0 = mk_num IND_0");;

let vSUC_DEF = new_definition
 (parse_term "SUC n = mk_num(IND_SUC(dest_num n))");;

(* ------------------------------------------------------------------------- *)
(* Distinctness and injectivity of constructors.                             *)
(* ------------------------------------------------------------------------- *)

let vNOT_SUC = prove
 ((parse_term "!n. ~(SUC n = _0)"),
  vREWRITE_TAC[vSUC_DEF; vZERO_DEF] ---->
  vMESON_TAC[vNUM_REP_RULES; fst num_tydef; snd num_tydef; vIND_SUC_0]);;

let vSUC_INJ = prove
 ((parse_term "!m n. SUC m = SUC n <=> m = n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vSUC_DEF] ---->
  vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM(vMP_TAC -| vAP_TERM (parse_term "dest_num")) ---->
  vSUBGOAL_THEN (parse_term "!p. NUM_REP (IND_SUC (dest_num p))") vMP_TAC ++-->
   [vGEN_TAC ----> vMATCH_MP_TAC (vCONJUNCT2 vNUM_REP_RULES); vALL_TAC] ---->
  vREWRITE_TAC[fst num_tydef; snd num_tydef] ---->
  vDISCH_TAC ----> vASM_REWRITE_TAC[vIND_SUC_INJ] ---->
  vDISCH_THEN(vMP_TAC -| vAP_TERM (parse_term "mk_num")) ---->
  vREWRITE_TAC[fst num_tydef]);;

(* ------------------------------------------------------------------------- *)
(* Induction.                                                                *)
(* ------------------------------------------------------------------------- *)

let num_INDUCTION = prove
 ((parse_term "!P. P(_0) /\\ (!n. P(n) ==> P(SUC n)) ==> !n. P n"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC (parse_term "\\i. NUM_REP i /\\ P(mk_num i):bool") vNUM_REP_INDUCT) ---->
  vASM_REWRITE_TAC[vGSYM vZERO_DEF; vNUM_REP_RULES] ---->
  vW(vC vSUBGOAL_THEN (fun t -> vREWRITE_TAC[t]) -| funpow 2 lhand -| snd) ++-->
   [vREPEAT vSTRIP_TAC ++-->
     [vMATCH_MP_TAC(vCONJUNCT2 vNUM_REP_RULES) ----> vASM_REWRITE_TAC[];
      vSUBGOAL_THEN (parse_term "mk_num(IND_SUC i) = SUC(mk_num i)") vSUBST1_TAC ++-->
       [vREWRITE_TAC[vSUC_DEF] ----> vREPEAT vAP_TERM_TAC ---->
        vCONV_TAC vSYM_CONV ----> vREWRITE_TAC[vGSYM(snd num_tydef)] ---->
        vFIRST_ASSUM vMATCH_ACCEPT_TAC;
        vFIRST_ASSUM vMATCH_MP_TAC ----> vFIRST_ASSUM vMATCH_ACCEPT_TAC]];
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "dest_num n")) ---->
    vREWRITE_TAC[fst num_tydef; snd num_tydef]]);;

(* ------------------------------------------------------------------------- *)
(* Recursion.                                                                *)
(* ------------------------------------------------------------------------- *)

let num_Axiom = prove
 ((parse_term "!(e:A) f. ?!fn. (fn _0 = e) /\\\n                   (!n. fn (SUC n) = f (fn n) n)"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vEXISTS_UNIQUE_THM] ----> vCONJ_TAC ++-->
   [(vMP_TAC -| prove_inductive_relations_exist)
      (parse_term "PRG _0 e /\\ (!b:A n:num. PRG n b ==> PRG (SUC n) (f b n))") ---->
    vDISCH_THEN(vCHOOSE_THEN (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vASSUME_TAC -| vGSYM)) ---->
    vSUBGOAL_THEN (parse_term "!n:num. ?!y:A. PRG n y") vMP_TAC ++-->
     [vMATCH_MP_TAC num_INDUCTION ----> vREPEAT vSTRIP_TAC ---->
      vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vBINDER_CONV [vGSYM th]) ---->
      vREWRITE_TAC[vGSYM vNOT_SUC; vNOT_SUC; vSUC_INJ; vEXISTS_UNIQUE_REFL] ---->
      vREWRITE_TAC[vUNWIND_THM1] ---->
      vUNDISCH_TAC (parse_term "?!y. PRG (n:num) (y:A)") ---->
      vREWRITE_TAC[vEXISTS_UNIQUE_THM] ---->
      vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "y:A")) vASSUME_TAC) ---->
      vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[] ++-->
       [vMAP_EVERY vEXISTS_TAC [(parse_term "(f:A->num->A) y n"); (parse_term "y:A")];
        vAP_THM_TAC ----> vAP_TERM_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC] ---->
      vASM_REWRITE_TAC[];
      vREWRITE_TAC[vUNIQUE_SKOLEM_ALT] ---->
      vDISCH_THEN(vX_CHOOSE_THEN (parse_term "fn:num->A") (vASSUME_TAC -| vGSYM)) ---->
      vEXISTS_TAC (parse_term "fn:num->A") ----> vASM_REWRITE_TAC[] ---->
      vGEN_TAC ----> vFIRST_ASSUM(vMATCH_MP_TAC -| vCONJUNCT2) ---->
      vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vI [vGSYM th]) ----> vREFL_TAC];
    vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vFUN_EQ_THM] ---->
    vMATCH_MP_TAC num_INDUCTION ----> vASM_REWRITE_TAC[] ---->
    vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* The basic numeral tag; rewrite existing instances of "_0".                *)
(* ------------------------------------------------------------------------- *)

let vNUMERAL =
  let num_ty = type_of(lhand(concl vZERO_DEF)) in
  let funn_ty = mk_fun_ty num_ty num_ty in
  let numeral_tm = mk_var("NUMERAL",funn_ty) in
  let n_tm = mk_var("n",num_ty) in
  new_definition(mk_eq(mk_comb(numeral_tm,n_tm),n_tm));;

let vNOT_SUC, num_INDUCTION, num_Axiom =
  let th = prove((parse_term "_0 = 0"),vREWRITE_TAC[vNUMERAL]) in
  match
  map (vGEN_REWRITE_RULE vDEPTH_CONV [th])
    [vNOT_SUC; num_INDUCTION; num_Axiom]
  with [a;b;c] -> a,b,c | _ -> assert false;;

(* ------------------------------------------------------------------------- *)
(* Induction tactic.                                                         *)
(* ------------------------------------------------------------------------- *)

let (vINDUCT_TAC:tactic) =
  vMATCH_MP_TAC num_INDUCTION ---->
  vCONJ_TAC ++--> [vALL_TAC; vGEN_TAC ----> vDISCH_TAC];;

let num_RECURSION =
  let avs = fst(strip_forall(concl num_Axiom)) in
  vGENL avs (vEXISTENCE (vSPECL avs num_Axiom));;

(* ------------------------------------------------------------------------- *)
(* Cases theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let num_CASES = prove
 ((parse_term "!m. (m = 0) \\/ (?n. m = SUC n)"),
  vINDUCT_TAC ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Augmenting inductive type store.                                          *)
(* ------------------------------------------------------------------------- *)

inductive_type_store :=
 ("num",(2,num_INDUCTION,num_RECURSION))::(!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* "Bitwise" binary representation of numerals.                              *)
(* ------------------------------------------------------------------------- *)

let vBIT0_DEF =
  let funn_ty = type_of(rator(lhand(snd(dest_forall(concl vNUMERAL))))) in
  let bit0_tm = mk_var("BIT0",funn_ty) in
  let def = new_definition
   (mk_eq(bit0_tm,(parse_term "@fn. fn 0 = 0 /\\ (!n. fn (SUC n) = SUC (SUC(fn n)))")))
  and th = vBETA_RULE(vISPECL [(parse_term "0"); (parse_term "\\m n:num. SUC(SUC m)")] num_RECURSION) in
  vREWRITE_RULE[vGSYM def] (vSELECT_RULE th);;

let vBIT1_DEF =
  let funn_ty = type_of(rator(lhand(lhand(concl vBIT0_DEF)))) in
  let num_ty = snd(dest_fun_ty funn_ty) in
  let n_tm = mk_var("n",num_ty) in
  let bit1_tm = mk_var("BIT1",funn_ty) in
  new_definition(mk_eq(mk_comb(bit1_tm,n_tm),(parse_term "SUC (BIT0 n)")));;

(* ------------------------------------------------------------------------- *)
(* Syntax operations on numerals.                                            *)
(* ------------------------------------------------------------------------- *)

let mk_numeral =
  let open Num in
  let pow24 = pow2 24 and num_0 = Int 0
  and zero_tm = mk_const("_0",[])
  and vBIT0_tm = mk_const("BIT0",[])
  and vBIT1_tm = mk_const("BIT1",[])
  and vNUMERAL_tm = mk_const("NUMERAL",[]) in
  let rec stripzeros l = match l with false::t -> stripzeros t | _ -> l in
  let rec raw_list_of_num l n =
    if n =/ num_0 then stripzeros l else
    let h = Num.int_of_num(mod_num n pow24) in
    raw_list_of_num
     ((h land 8388608 <> 0)::(h land 4194304 <> 0)::(h land 2097152 <> 0)::
      (h land 1048576 <> 0)::(h land 524288 <> 0)::(h land 262144 <> 0)::
      (h land 131072 <> 0)::(h land 65536 <> 0)::(h land 32768 <> 0)::
      (h land 16384 <> 0)::(h land 8192 <> 0)::(h land 4096 <> 0)::
      (h land 2048 <> 0)::(h land 1024 <> 0)::(h land 512 <> 0)::
      (h land 256 <> 0)::(h land 128 <> 0)::(h land 64 <> 0)::
      (h land 32 <> 0)::(h land 16 <> 0)::(h land 8 <> 0)::(h land 4 <> 0)::
      (h land 2 <> 0)::(h land 1 <> 0)::l) (quo_num n pow24) in
  let rec numeral_of_list t l =
    match l with
      [] -> t
    | b::r -> numeral_of_list(mk_comb((if b then vBIT1_tm else vBIT0_tm),t)) r in
  let mk_raw_numeral n = numeral_of_list zero_tm (raw_list_of_num [] n) in
  fun n -> if n </ num_0 then failwith "mk_numeral: negative argument" else
           mk_comb(vNUMERAL_tm,mk_raw_numeral n);;

let mk_small_numeral n = mk_numeral(Int n);;

let dest_small_numeral t = Num.int_of_num(dest_numeral t);;

let is_numeral = can dest_numeral;;

(* ------------------------------------------------------------------------- *)
(* Derived principles of definition based on existence.                      *)
(*                                                                           *)
(* This is put here because we use numerals as tags to force different       *)
(* constants specified with equivalent theorems to have different underlying *)
(* definitions, ensuring that there are no provable equalities between them  *)
(* and so in some sense the constants are "underspecified" as the user might *)
(* want for some applications.                                               *)
(* ------------------------------------------------------------------------- *)

let the_specifications = ref [];;

let new_specification =
  let code c = mk_small_numeral (Char.code (c.[0])) in
  let mk_code name =
      end_itlist (curry mk_pair) (map code (explode name)) in
  let check_distinct l =
    try let _ = itlist (fun t res -> if mem t res then fail() else t::res) l [] in true
    with Failure _ -> false in
  let specify name th =
    let ntm = mk_code name in
    let gv = genvar(type_of ntm) in
    let th0 = vCONV_RULE(vREWR_CONV vSKOLEM_THM) (vGEN gv th) in
    let th1 = vCONV_RULE(vRATOR_CONV (vREWR_CONV vEXISTS_THM) +--->
                        vBETA_CONV) th0 in
    let _l,r = dest_comb(concl th1) in
    let rn = mk_comb(r,ntm) in
    let ty = type_of rn in
    let th2 = new_definition(mk_eq(mk_var(name,ty),rn)) in
    vGEN_REWRITE_RULE vONCE_DEPTH_CONV [vGSYM th2]
     (vSPEC ntm (vCONV_RULE vBETA_CONV th1)) in
  let rec specifies names th =
    match names with
      [] -> th
    | name::onames -> let th' = specify name th in
                      specifies onames th' in
  fun names th ->
    let asl,c = dest_thm th in
    if not (asl = []) then
      failwith "new_specification: Assumptions not allowed in theorem" else
    if not (frees c = []) then
      failwith "new_specification: Free variables in predicate" else
    let avs = fst(strip_exists c) in
    if length names = 0 || length names > length avs then
      failwith "new_specification: Unsuitable number of constant names" else
    if not (check_distinct names) then
      failwith "new_specification: Constant names not distinct"
    else
      try let sth = snd(find (fun ((names',th'),_sth') ->
                               names' = names && aconv (concl th') (concl th))
                             (!the_specifications)) in
          warn true ("Benign respecification"); sth
      with Failure _ ->
          let sth = specifies names th in
          the_specifications := ((names,th),sth)::(!the_specifications);
          sth;;
