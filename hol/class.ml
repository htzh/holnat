(* ========================================================================= *)
(* Extensional, classical reasoning with AC starts now!                      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Printer
open Parser
open Equal
open Boolean
open Drule
open Tactics
open Itab
open Simp
open Theorems
open Ind_defs

(* ------------------------------------------------------------------------- *)
(* Eta-axiom, corresponding conversion, and extensionality.                  *)
(* ------------------------------------------------------------------------- *)

let vETA_AX = new_axiom
  (parse_term "!t:A->B. (\\x. t x) = t");;

let vETA_CONV =
  let t = (parse_term "t:A->B") in
  let pth = prove((parse_term "(\\x. (t:A->B) x) = t"),vMATCH_ACCEPT_TAC vETA_AX) in
  fun tm ->
    try let bv,bod = dest_abs tm in
        let l,r = dest_comb bod in
        if r = bv && not (vfree_in bv l) then
          vTRANS (vREFL tm) (vPINST [type_of bv,aty; type_of bod,bty] [l,t] pth)
        else fail()
    with Failure _ -> failwith "ETA_CONV";;

let vEQ_EXT = try Cache.lookup_thm "EQ_EXT" with _ ->  prove
 ((parse_term "!(f:A->B) g. (!x. f x = g x) ==> f = g"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vABS (parse_term "x:A") -| vSPEC (parse_term "x:A")) ---->
  vREWRITE_TAC[vETA_AX]);;

let vFUN_EQ_THM = try Cache.lookup_thm "FUN_EQ_THM" with _ ->  prove
 ((parse_term "!(f:A->B) g. f = g <=> (!x. f x = g x)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN vSUBST1_TAC ----> vGEN_TAC ----> vREFL_TAC;
    vMATCH_ACCEPT_TAC vEQ_EXT]);;

(* ------------------------------------------------------------------------- *)
(* Indefinite descriptor (giving AC).                                        *)
(* ------------------------------------------------------------------------- *)

new_constant("@",(parse_type "(A->bool)->A"));;

parse_as_binder "@";;

let is_select = is_binder "@";;
let dest_select = dest_binder "@";;
let mk_select = mk_binder "@";;

let vSELECT_AX = new_axiom
 (parse_term "!P (x:A). P x ==> P((@) P)");;

(* ------------------------------------------------------------------------- *)
(* Useful for compatibility. (The old EXISTS_DEF.)                           *)
(* ------------------------------------------------------------------------- *)

let vEXISTS_THM = try Cache.lookup_thm "EXISTS_THM" with _ ->  prove
 ((parse_term "(?) = \\P:A->bool. P ((@) P)"),
  vMATCH_MP_TAC vEQ_EXT ----> vBETA_TAC ----> vX_GEN_TAC (parse_term "P:A->bool") ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vETA_AX] ---->
  vEQ_TAC ++-->
   [vDISCH_THEN(vCHOOSE_THEN vMP_TAC) ----> vMATCH_ACCEPT_TAC vSELECT_AX;
    vDISCH_TAC ----> vEXISTS_TAC (parse_term "((@) P):A") ----> vPOP_ASSUM vACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Rules and so on for the select operator.                                  *)
(* ------------------------------------------------------------------------- *)

let vSELECT_RULE =
  let vP = (parse_term "P:A->bool") in
  let pth = prove
   ((parse_term "(?) (P:A->bool) ==> P((@) P)"),
    vSIMP_TAC[vSELECT_AX; vETA_AX]) in
  fun th ->
    try let abs = rand(concl th) in
        let ty = type_of(bndvar abs) in
        vCONV_RULE vBETA_CONV (vMP (vPINST [ty,aty] [abs,vP] pth) th)
    with Failure _ -> failwith "SELECT_RULE";;

let vSELECT_CONV =
  let vP = (parse_term "P:A->bool") in
  let pth = prove
   ((parse_term "(P:A->bool)((@) P) = (?) P"),
    vREWRITE_TAC[vEXISTS_THM] ----> vBETA_TAC ----> vREFL_TAC) in
   fun tm ->
     try let is_epsok t = is_select t &&
                          let bv,bod = dest_select t in
                          aconv tm (vsubst [t,bv] bod) in
         let pickeps = find_term is_epsok tm in
         let abs = rand pickeps in
         let ty = type_of (bndvar abs) in
         vCONV_RULE (vLAND_CONV vBETA_CONV) (vPINST [ty,aty] [abs,vP] pth)
     with Failure _ -> failwith "SELECT_CONV";;

(* ------------------------------------------------------------------------- *)
(* Some basic theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let vSELECT_REFL = try Cache.lookup_thm "SELECT_REFL" with _ ->  prove
 ((parse_term "!x:A. (@y. y = x) = x"),
  vGEN_TAC ----> vCONV_TAC vSELECT_CONV ---->
  vEXISTS_TAC (parse_term "x:A") ----> vREFL_TAC);;

let vSELECT_UNIQUE = try Cache.lookup_thm "SELECT_UNIQUE" with _ ->  prove
 ((parse_term "!P x. (!y:A. P y = (y = x)) ==> ((@) P = x)"),
  vREPEAT vSTRIP_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vETA_AX] ---->
  vASM_REWRITE_TAC[vSELECT_REFL]);;

extend_basic_rewrites [vSELECT_REFL];;

(* ------------------------------------------------------------------------- *)
(* Now we can derive type definitions from existence; check benignity.       *)
(* ------------------------------------------------------------------------- *)

let the_type_definitions = ref ([]:((string*string*string)*(thm*thm))list);;

let new_type_definition tyname (absname,repname) th =
  try let th',tth' = assoc (tyname,absname,repname) (!the_type_definitions) in
      if concl th' <> concl th then failwith "" else
      (warn true "Benign redefinition of type"; tth')
  with Failure _ ->
    let th0 =
     vCONV_RULE (vRATOR_CONV (vREWR_CONV vEXISTS_THM) +---> vBETA_CONV) th in
    let th1,th2 = new_basic_type_definition tyname (absname,repname) th0 in
    let tth = vCONJ (vGEN_ALL th1)
                   (vGEN_ALL (vCONV_RULE(vLAND_CONV (vTRY_CONV vBETA_CONV)) th2)) in
    the_type_definitions := ((tyname,absname,repname),(th,tth))::
                            (!the_type_definitions);
    tth;;

(* ------------------------------------------------------------------------- *)
(* Derive excluded middle. The proof is an optimization due to Mark Adams of *)
(* the original Diaconescu proof as presented in Beeson's book.              *)
(* ------------------------------------------------------------------------- *)

let vEXCLUDED_MIDDLE = try Cache.lookup_thm "EXCLUDED_MIDDLE" with _ ->  prove
 ((parse_term "!t. t \\/ ~t"),
  vGEN_TAC ----> vSUBGOAL_THEN
   (parse_term "(((@x. (x <=> F) \\/ t) <=> F) \\/ t) /\\ (((@x. (x <=> T) \\/ t) <=> T) \\/ t)")
  vMP_TAC ++-->
   [vCONJ_TAC ----> vCONV_TAC vSELECT_CONV ++-->
     [vEXISTS_TAC (parse_term "F"); vEXISTS_TAC (parse_term "T")] ---->
    vDISJ1_TAC ----> vREFL_TAC;
    vDISCH_THEN(vSTRIP_ASSUME_TAC -| vGSYM) ---->
    vTRY(vDISJ1_TAC ----> vFIRST_ASSUM vACCEPT_TAC) ---->
    vDISJ2_TAC ----> vDISCH_TAC ----> vMP_TAC(vITAUT (parse_term "~(T <=> F)")) ---->
    vPURE_ONCE_ASM_REWRITE_TAC[] ---->
    vASM_REWRITE_TAC[vITAUT (parse_term "p \\/ T <=> T")]]);;

let vBOOL_CASES_AX = try Cache.lookup_thm "BOOL_CASES_AX" with _ ->  prove
 ((parse_term "!t. (t <=> T) \\/ (t <=> F)"),
  vGEN_TAC ----> vDISJ_CASES_TAC(vSPEC (parse_term "t:bool") vEXCLUDED_MIDDLE) ---->
  vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Classically based tactics. (See also COND_CASES_TAC later on.)            *)
(* ------------------------------------------------------------------------- *)

let vBOOL_CASES_TAC p = vSTRUCT_CASES_TAC (vSPEC p vBOOL_CASES_AX);;

let vASM_CASES_TAC t = vDISJ_CASES_TAC(vSPEC t vEXCLUDED_MIDDLE);;

(* ------------------------------------------------------------------------- *)
(* Set up a reasonable tautology checker for classical logic.                *)
(* ------------------------------------------------------------------------- *)

let vTAUT =
  let vPROP_REWRITE_TAC = vREWRITE_TAC[] in
  let vRTAUT_TAC (asl,w) =
    let ok t = type_of t = bool_ty && can (find_term is_var) t && free_in t w in
    (vPROP_REWRITE_TAC ---->
     vW((fun t1 t2 -> t1 ----> t2) (vREWRITE_TAC[]) -| vBOOL_CASES_TAC -|
       hd -| sort free_in -| find_terms ok -| snd)) (asl,w) in
  let vTAUT_TAC = vREPEAT(vGEN_TAC |---> vCONJ_TAC) ----> vREPEAT vRTAUT_TAC in
  fun tm -> prove(tm,vTAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* A few useful classical tautologies.                                       *)
(* ------------------------------------------------------------------------- *)

let vDE_MORGAN_THM = vTAUT
  (parse_term "!t1 t2. (~(t1 /\\ t2) <=> ~t1 \\/ ~t2) /\\ (~(t1 \\/ t2) <=> ~t1 /\\ ~t2)");;

let vNOT_CLAUSES =
  vTAUT (parse_term "(!t. ~ ~t <=> t) /\\ (~T <=> F) /\\ (~F <=> T)");;

let vNOT_IMP = vTAUT (parse_term "!t1 t2. ~(t1 ==> t2) <=> t1 /\\ ~t2");;

let vCONTRAPOS_THM = vTAUT (parse_term "!t1 t2. (~t1 ==> ~t2) <=> (t2 ==> t1)");;

extend_basic_rewrites [vCONJUNCT1 vNOT_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Some classically based rules.                                             *)
(* ------------------------------------------------------------------------- *)

let vCCONTR =
  let vP = (parse_term "P:bool") in
  let pth = vTAUT (parse_term "(~P ==> F) ==> P") in
  fun tm th ->
    try let tm' = mk_neg tm in
        vMP (vINST [tm,vP] pth) (vDISCH tm' th)
    with Failure _ -> failwith "CCONTR";;

let vCONTRAPOS_CONV =
  let a = (parse_term "a:bool") and b = (parse_term "b:bool") in
  let pth = vTAUT (parse_term "(a ==> b) <=> (~b ==> ~a)") in
  fun tm ->
    try let vP,vQ = dest_imp tm in
        vINST [vP,a; vQ,b] pth
    with Failure _ -> failwith "CONTRAPOS_CONV";;

(* ------------------------------------------------------------------------- *)
(* A classicalal "refutation" tactic.                                        *)
(* ------------------------------------------------------------------------- *)

let vREFUTE_THEN =
  let f_tm = (parse_term "F")
  and conv = vREWR_CONV(vTAUT (parse_term "p <=> ~p ==> F")) in
  fun ttac (_asl,w as gl) ->
    if w = f_tm then vALL_TAC gl
    else if is_neg w then vDISCH_THEN ttac gl
    else (vCONV_TAC conv ----> vDISCH_THEN ttac) gl;;

(* ------------------------------------------------------------------------- *)
(* Infinite de Morgan laws.                                                  *)
(* ------------------------------------------------------------------------- *)

let vNOT_EXISTS_THM = try Cache.lookup_thm "NOT_EXISTS_THM" with _ ->  prove
 ((parse_term "!P. ~(?x:A. P x) <=> (!x. ~(P x))"),
  vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ----> vUNDISCH_TAC (parse_term "~(?x:A. P x)") ---->
    vREWRITE_TAC[] ----> vEXISTS_TAC (parse_term "x:A") ----> vPOP_ASSUM vACCEPT_TAC;
    vDISCH_THEN(vCHOOSE_THEN vMP_TAC) ----> vASM_REWRITE_TAC[]]);;

let vEXISTS_NOT_THM = try Cache.lookup_thm "EXISTS_NOT_THM" with _ ->  prove
 ((parse_term "!P. (?x:A. ~(P x)) <=> ~(!x. P x)"),
  vONCE_REWRITE_TAC[vTAUT (parse_term "(a <=> ~b) <=> (~a <=> b)")] ---->
  vREWRITE_TAC[vNOT_EXISTS_THM]);;

let vNOT_FORALL_THM = try Cache.lookup_thm "NOT_FORALL_THM" with _ ->  prove
 ((parse_term "!P. ~(!x. P x) <=> (?x:A. ~(P x))"),
  vMATCH_ACCEPT_TAC(vGSYM vEXISTS_NOT_THM));;

let vFORALL_NOT_THM = try Cache.lookup_thm "FORALL_NOT_THM" with _ ->  prove
 ((parse_term "!P. (!x. ~(P x)) <=> ~(?x:A. P x)"),
  vMATCH_ACCEPT_TAC(vGSYM vNOT_EXISTS_THM));;

(* ------------------------------------------------------------------------- *)
(* Expand quantification over Booleans.                                      *)
(* ------------------------------------------------------------------------- *)

let vFORALL_BOOL_THM = try Cache.lookup_thm "FORALL_BOOL_THM" with _ ->  prove
  ((parse_term "(!b. P b) <=> P T /\\ P F"),
   vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
   vGEN_TAC ----> vBOOL_CASES_TAC (parse_term "b:bool") ----> vASM_REWRITE_TAC[]);;

let vEXISTS_BOOL_THM = try Cache.lookup_thm "EXISTS_BOOL_THM" with _ ->  prove
 ((parse_term "(?b. P b) <=> P T \\/ P F"),
  vMATCH_MP_TAC(vTAUT (parse_term "(~p <=> ~q) ==> (p <=> q)")) ---->
  vREWRITE_TAC[vDE_MORGAN_THM; vNOT_EXISTS_THM; vFORALL_BOOL_THM]);;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and disjunction                                      *)
(* ------------------------------------------------------------------------- *)

let vLEFT_FORALL_OR_THM = try Cache.lookup_thm "LEFT_FORALL_OR_THM" with _ ->  prove
 ((parse_term "!P Q. (!x:A. P x \\/ Q) <=> (!x. P x) \\/ Q"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vTAUT (parse_term "(a <=> b) <=> (~a <=> ~b)")] ---->
  vREWRITE_TAC[vNOT_FORALL_THM; vDE_MORGAN_THM; vLEFT_EXISTS_AND_THM]);;

let vRIGHT_FORALL_OR_THM = try Cache.lookup_thm "RIGHT_FORALL_OR_THM" with _ ->  prove
 ((parse_term "!P Q. (!x:A. P \\/ Q x) <=> P \\/ (!x. Q x)"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vTAUT (parse_term "(a <=> b) <=> (~a <=> ~b)")] ---->
  vREWRITE_TAC[vNOT_FORALL_THM; vDE_MORGAN_THM; vRIGHT_EXISTS_AND_THM]);;

let vLEFT_OR_FORALL_THM = try Cache.lookup_thm "LEFT_OR_FORALL_THM" with _ ->  prove
 ((parse_term "!P Q. (!x:A. P x) \\/ Q <=> (!x. P x \\/ Q)"),
  vMATCH_ACCEPT_TAC(vGSYM vLEFT_FORALL_OR_THM));;

let vRIGHT_OR_FORALL_THM = try Cache.lookup_thm "RIGHT_OR_FORALL_THM" with _ ->  prove
 ((parse_term "!P Q. P \\/ (!x:A. Q x) <=> (!x. P \\/ Q x)"),
  vMATCH_ACCEPT_TAC(vGSYM vRIGHT_FORALL_OR_THM));;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

let vLEFT_IMP_FORALL_THM = try Cache.lookup_thm "LEFT_IMP_FORALL_THM" with _ ->  prove
 ((parse_term "!P Q. ((!x:A. P x) ==> Q) <=> (?x. P x ==> Q)"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vTAUT (parse_term "(a <=> b) <=> (~a <=> ~b)")] ---->
  vREWRITE_TAC[vNOT_EXISTS_THM; vNOT_IMP; vLEFT_AND_FORALL_THM]);;

let vLEFT_EXISTS_IMP_THM = try Cache.lookup_thm "LEFT_EXISTS_IMP_THM" with _ ->  prove
 ((parse_term "!P Q. (?x. P x ==> Q) <=> ((!x:A. P x) ==> Q)"),
  vMATCH_ACCEPT_TAC(vGSYM vLEFT_IMP_FORALL_THM));;

let vRIGHT_IMP_EXISTS_THM = try Cache.lookup_thm "RIGHT_IMP_EXISTS_THM" with _ ->  prove
 ((parse_term "!P Q. (P ==> ?x:A. Q x) <=> (?x:A. P ==> Q x)"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vTAUT (parse_term "(a <=> b) <=> (~a <=> ~b)")] ---->
  vREWRITE_TAC[vNOT_EXISTS_THM; vNOT_IMP; vRIGHT_AND_FORALL_THM]);;

let vRIGHT_EXISTS_IMP_THM = try Cache.lookup_thm "RIGHT_EXISTS_IMP_THM" with _ ->  prove
 ((parse_term "!P Q. (?x:A. P ==> Q x) <=> (P ==> ?x:A. Q x)"),
  vMATCH_ACCEPT_TAC(vGSYM vRIGHT_IMP_EXISTS_THM));;

(* ------------------------------------------------------------------------- *)
(* The conditional.                                                          *)
(* ------------------------------------------------------------------------- *)

let vCOND_DEF = new_definition
  (parse_term "COND = \\t t1 t2. @x:A. ((t <=> T) ==> (x = t1)) /\\\n                          ((t <=> F) ==> (x = t2))");;

let vCOND_CLAUSES = try Cache.lookup_thm "COND_CLAUSES" with _ ->  prove
 ((parse_term "!(t1:A) t2. ((if T then t1 else t2) = t1) /\\\n               ((if F then t1 else t2) = t2)"),
  vREWRITE_TAC[vCOND_DEF]);;

let is_cond tm =
  try fst(dest_const(rator(rator (rator tm)))) = "COND"
  with Failure _ -> false;;

let mk_cond (b,x,y) =
  try let c = mk_const("COND",[type_of x,aty]) in
      mk_comb(mk_comb(mk_comb(c,b),x),y)
  with Failure _ -> failwith "mk_cond";;

let dest_cond tm =
  try let tm1,y = dest_comb tm in
      let tm2,x = dest_comb tm1 in
      let c,b = dest_comb tm2 in
      if fst(dest_const c) = "COND" then (b,(x,y)) else fail()
  with Failure _ -> failwith "dest_cond";;

extend_basic_rewrites [vCOND_CLAUSES];;

let vCOND_EXPAND = try Cache.lookup_thm "COND_EXPAND" with _ ->  prove
 ((parse_term "!b t1 t2. (if b then t1 else t2) <=> (~b \\/ t1) /\\ (b \\/ t2)"),
  vREPEAT vGEN_TAC ----> vBOOL_CASES_TAC (parse_term "b:bool") ---->
  vREWRITE_TAC[]);;

let vCOND_ID = try Cache.lookup_thm "COND_ID" with _ ->  prove
 ((parse_term "!b (t:A). (if b then t else t) = t"),
  vREPEAT vGEN_TAC ----> vBOOL_CASES_TAC (parse_term "b:bool") ----> vREWRITE_TAC[]);;

let vCOND_RAND = try Cache.lookup_thm "COND_RAND" with _ ->  prove
 ((parse_term "!b (f:A->B) x y. f (if b then x else y) = (if b then f x else f y)"),
  vREPEAT vGEN_TAC ----> vBOOL_CASES_TAC (parse_term "b:bool") ----> vREWRITE_TAC[]);;

let vCOND_RATOR = try Cache.lookup_thm "COND_RATOR" with _ ->  prove
 ((parse_term "!b (f:A->B) g x. (if b then f else g)(x) = (if b then f x else g x)"),
  vREPEAT vGEN_TAC ----> vBOOL_CASES_TAC (parse_term "b:bool") ----> vREWRITE_TAC[]);;

let vCOND_ABS = try Cache.lookup_thm "COND_ABS" with _ ->  prove
 ((parse_term "!b (f:A->B) g. (\\x. if b then f x else g x) = (if b then f else g)"),
  vREPEAT vGEN_TAC ----> vBOOL_CASES_TAC (parse_term "b:bool") ----> vREWRITE_TAC[vETA_AX]);;

let vCOND_SWAP = try Cache.lookup_thm "COND_SWAP" with _ ->  prove
 ((parse_term "!p x y:A. (if ~p then x else y) = (if p then y else x)"),
  vREPEAT vGEN_TAC ----> vBOOL_CASES_TAC (parse_term "p:bool") ----> vREWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Redefine TAUT to freeze in the rewrites including COND.                   *)
(* ------------------------------------------------------------------------- *)

let vTAUT =
  let vPROP_REWRITE_TAC = vREWRITE_TAC[] in
  let vRTAUT_TAC (asl,w) =
    let ok t = type_of t = bool_ty && can (find_term is_var) t && free_in t w in
    (vPROP_REWRITE_TAC ---->
     vW((fun t1 t2 -> t1 ----> t2) (vREWRITE_TAC[]) -| vBOOL_CASES_TAC -|
       hd -| sort free_in -| find_terms ok -| snd)) (asl,w) in
  let vTAUT_TAC = vREPEAT(vGEN_TAC |---> vCONJ_TAC) ----> vREPEAT vRTAUT_TAC in
  fun tm -> prove(tm,vTAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Throw monotonicity in.                                                    *)
(* ------------------------------------------------------------------------- *)

let vMONO_COND = try Cache.lookup_thm "MONO_COND" with _ ->  prove
 ((parse_term "(A ==> B) /\\ (C ==> D) ==> (if b then A else C) ==> (if b then B else D)"),
  vSTRIP_TAC ----> vBOOL_CASES_TAC (parse_term "b:bool") ---->
  vASM_REWRITE_TAC[]);;

monotonicity_theorems := vMONO_COND::(!monotonicity_theorems);;

(* ------------------------------------------------------------------------- *)
(* Tactic for splitting over an arbitrarily chosen conditional.              *)
(* ------------------------------------------------------------------------- *)

let vCOND_ELIM_THM = try Cache.lookup_thm "COND_ELIM_THM" with _ ->  prove
 ((parse_term "(P:A->bool) (if c then x else y) <=> (c ==> P x) /\\ (~c ==> P y)"),
  vBOOL_CASES_TAC (parse_term "c:bool") ----> vREWRITE_TAC[]);;

let vCOND_ELIM_CONV = vHIGHER_REWRITE_CONV[vCOND_ELIM_THM] true;;

let (vCOND_CASES_TAC :tactic) =
  let vDENEG_RULE = vGEN_REWRITE_RULE vI [vTAUT (parse_term "~ ~ p <=> p")] in
  vCONV_TAC vCOND_ELIM_CONV ----> vCONJ_TAC ++-->
    [vDISCH_THEN(fun th -> vASSUME_TAC th ----> vSUBST1_TAC(vEQT_INTRO th));
     vDISCH_THEN(fun th -> try let th' = vDENEG_RULE th in
                              vASSUME_TAC th' ----> vSUBST1_TAC(vEQT_INTRO th')
                          with Failure _ ->
                              vASSUME_TAC th ----> vSUBST1_TAC(vEQF_INTRO th))];;

(* ------------------------------------------------------------------------- *)
(* Skolemization.                                                            *)
(* ------------------------------------------------------------------------- *)

let vSKOLEM_THM = try Cache.lookup_thm "SKOLEM_THM" with _ ->  prove
 ((parse_term "!P. (!x:A. ?y:B. P x y) <=> (?y. !x. P x (y x))"),
  vREPEAT(vSTRIP_TAC |---> vEQ_TAC) ++-->
   [vEXISTS_TAC (parse_term "\\x:A. @y:B. P x y") ----> vGEN_TAC ---->
    vBETA_TAC ----> vCONV_TAC vSELECT_CONV;
    vEXISTS_TAC (parse_term "(y:A->B) x")] ---->
  vPOP_ASSUM vMATCH_ACCEPT_TAC);;

let vSKOLEM_THM_GEN = try Cache.lookup_thm "SKOLEM_THM_GEN" with _ ->  prove
 ((parse_term "!P R. (!x. P x ==> ?y. R x y) <=> (?f. !x. P x ==> R x (f x))"),
  vREWRITE_TAC[vRIGHT_IMP_EXISTS_THM; vSKOLEM_THM]);;

(* ------------------------------------------------------------------------- *)
(* NB: this one is true intutionistically and intensionally.                 *)
(* ------------------------------------------------------------------------- *)

let vUNIQUE_SKOLEM_ALT = try Cache.lookup_thm "UNIQUE_SKOLEM_ALT" with _ ->  prove
 ((parse_term "!P:A->B->bool. (!x. ?!y. P x y) <=> ?f. !x y. P x y <=> (f x = y)"),
  vGEN_TAC ----> vREWRITE_TAC[vEXISTS_UNIQUE_ALT; vSKOLEM_THM]);;

(* ------------------------------------------------------------------------- *)
(* and this one intuitionistically and extensionally.                        *)
(* ------------------------------------------------------------------------- *)

let vUNIQUE_SKOLEM_THM = try Cache.lookup_thm "UNIQUE_SKOLEM_THM" with _ ->  prove
 ((parse_term "!P. (!x:A. ?!y:B. P x y) <=> (?!f. !x. P x (f x))"),
  vGEN_TAC ----> vREWRITE_TAC[vEXISTS_UNIQUE_THM; vSKOLEM_THM; vFORALL_AND_THM] ---->
  vEQ_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN vASSUME_TAC) ---->
  vASM_REWRITE_TAC[] ++-->
   [vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vFUN_EQ_THM] ---->
    vX_GEN_TAC (parse_term "x:A") ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vEXISTS_TAC (parse_term "x:A") ----> vASM_REWRITE_TAC[];
    vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "y1:B"); (parse_term "y2:B")] ----> vSTRIP_TAC ---->
    vFIRST_ASSUM(vX_CHOOSE_TAC (parse_term "f:A->B")) ---->
    vSUBGOAL_THEN (parse_term "(\\z. if z = x then y1 else (f:A->B) z) =\n                  (\\z. if z = x then y2 else (f:A->B) z)") vMP_TAC ++-->
     [vFIRST_ASSUM vMATCH_MP_TAC ---->
      vREPEAT vSTRIP_TAC ----> vBETA_TAC ----> vCOND_CASES_TAC ---->
      vASM_REWRITE_TAC[];
      vDISCH_THEN(vMP_TAC -| vC vAP_THM (parse_term "x:A")) ----> vREWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Extend default congruences for contextual rewriting.                      *)
(* ------------------------------------------------------------------------- *)

let vCOND_CONG =
  vTAUT (parse_term "(g = g') ==>\n        (g' ==> (t = t')) ==>\n        (~g' ==> (e = e')) ==>\n        ((if g then t else e) = (if g' then t' else e'))") in
  extend_basic_congs [vCOND_CONG];;

let vCOND_EQ_CLAUSE = prove
 ((parse_term "(if x = x then y else z) = y"),
  vREWRITE_TAC[]) in
 extend_basic_rewrites [vCOND_EQ_CLAUSE];;

(* ------------------------------------------------------------------------- *)
(* We can now treat "bool" as an enumerated type for some purposes.          *)
(* ------------------------------------------------------------------------- *)

let bool_INDUCT = try Cache.lookup_thm "bool_INDUCT" with _ ->  prove
 ((parse_term "!P. P F /\\ P T ==> !x. P x"),
  vREPEAT vSTRIP_TAC ----> vDISJ_CASES_TAC(vSPEC (parse_term "x:bool") vBOOL_CASES_AX) ---->
  vASM_REWRITE_TAC[]);;

let bool_RECURSION = try Cache.lookup_thm "bool_RECURSION" with _ ->  prove
 ((parse_term "!a b:A. ?f. f F = a /\\ f T = b"),
  vREPEAT vGEN_TAC ----> vEXISTS_TAC (parse_term "\\x. if x then b:A else a") ---->
  vREWRITE_TAC[]);;

let inductive_type_store = ref
 ["bool",(2,bool_INDUCT,bool_RECURSION)];;
