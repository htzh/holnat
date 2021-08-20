(* ========================================================================= *)
(* Additional theorems, mainly about quantifiers, and additional tactics.    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2012                         *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Printer
open Parser
open Equal
open Bool
open Tactics
open Itab
open Simp

(* ------------------------------------------------------------------------- *)
(* More stuff about equality.                                                *)
(* ------------------------------------------------------------------------- *)

let vEQ_REFL = prove
 ((parse_term "!x:A. x = x"),
  vGEN_TAC ----> vREFL_TAC);;

let vREFL_CLAUSE = prove
 ((parse_term "!x:A. (x = x) <=> T"),
  vGEN_TAC ----> vMATCH_ACCEPT_TAC(vEQT_INTRO(vSPEC_ALL vEQ_REFL)));;

let vEQ_SYM = prove
 ((parse_term "!(x:A) y. (x = y) ==> (y = x)"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vACCEPT_TAC -| vSYM));;

let vEQ_SYM_EQ = prove
 ((parse_term "!(x:A) y. (x = y) <=> (y = x)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vMATCH_ACCEPT_TAC vEQ_SYM);;

let vEQ_TRANS = prove
 ((parse_term "!(x:A) y z. (x = y) /\\ (y = z) ==> (x = z)"),
  vREPEAT vSTRIP_TAC ----> vPURE_ASM_REWRITE_TAC[] ----> vREFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* The following is a common special case of ordered rewriting.              *)
(* ------------------------------------------------------------------------- *)

let vAC acsuite = vEQT_ELIM -| vPURE_REWRITE_CONV[acsuite; vREFL_CLAUSE];;

(* ------------------------------------------------------------------------- *)
(* A couple of theorems about beta reduction.                                *)
(* ------------------------------------------------------------------------- *)

let vBETA_THM = prove
 ((parse_term "!(f:A->B) y. (\\x. (f:A->B) x) y = f y"),
  vREPEAT vGEN_TAC ----> vBETA_TAC ----> vREFL_TAC);;

let vABS_SIMP = prove
 ((parse_term "!(t1:A) (t2:B). (\\x. t1) t2 = t1"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vBETA_THM; vREFL_CLAUSE]);;

(* ------------------------------------------------------------------------- *)
(* A few "big name" intuitionistic tautologies.                              *)
(* ------------------------------------------------------------------------- *)

let vCONJ_ASSOC = prove
 ((parse_term "!t1 t2 t3. t1 /\\ t2 /\\ t3 <=> (t1 /\\ t2) /\\ t3"),
  vITAUT_TAC);;

let vCONJ_SYM = prove
 ((parse_term "!t1 t2. t1 /\\ t2 <=> t2 /\\ t1"),
  vITAUT_TAC);;

let vCONJ_ACI = prove
 ((parse_term "(p /\\ q <=> q /\\ p) /\\\n   ((p /\\ q) /\\ r <=> p /\\ (q /\\ r)) /\\\n   (p /\\ (q /\\ r) <=> q /\\ (p /\\ r)) /\\\n   (p /\\ p <=> p) /\\\n   (p /\\ (p /\\ q) <=> p /\\ q)"),
  vITAUT_TAC);;

let vDISJ_ASSOC = prove
 ((parse_term "!t1 t2 t3. t1 \\/ t2 \\/ t3 <=> (t1 \\/ t2) \\/ t3"),
  vITAUT_TAC);;

let vDISJ_SYM = prove
 ((parse_term "!t1 t2. t1 \\/ t2 <=> t2 \\/ t1"),
  vITAUT_TAC);;

let vDISJ_ACI = prove
 ((parse_term "(p \\/ q <=> q \\/ p) /\\\n   ((p \\/ q) \\/ r <=> p \\/ (q \\/ r)) /\\\n   (p \\/ (q \\/ r) <=> q \\/ (p \\/ r)) /\\\n   (p \\/ p <=> p) /\\\n   (p \\/ (p \\/ q) <=> p \\/ q)"),
  vITAUT_TAC);;

let vIMP_CONJ = prove
 ((parse_term "p /\\ q ==> r <=> p ==> q ==> r"),
  vITAUT_TAC);;

let vIMP_IMP = vGSYM vIMP_CONJ;;

let vIMP_CONJ_ALT = prove
 ((parse_term "p /\\ q ==> r <=> q ==> p ==> r"),
  vITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* A couple of "distribution" tautologies are useful.                        *)
(* ------------------------------------------------------------------------- *)

let vLEFT_OR_DISTRIB = prove
 ((parse_term "!p q r. p /\\ (q \\/ r) <=> p /\\ q \\/ p /\\ r"),
  vITAUT_TAC);;

let vRIGHT_OR_DISTRIB = prove
 ((parse_term "!p q r. (p \\/ q) /\\ r <=> p /\\ r \\/ q /\\ r"),
  vITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Degenerate cases of quantifiers.                                          *)
(* ------------------------------------------------------------------------- *)

let vFORALL_SIMP = prove
 ((parse_term "!t. (!x:A. t) = t"),
  vITAUT_TAC);;

let vEXISTS_SIMP = prove
 ((parse_term "!t. (?x:A. t) = t"),
  vITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* I also use this a lot (as a prelude to congruence reasoning).             *)
(* ------------------------------------------------------------------------- *)

let vEQ_IMP = vITAUT (parse_term "(a <=> b) ==> a ==> b");;

(* ------------------------------------------------------------------------- *)
(* Start building up the basic rewrites; we add a few more later.            *)
(* ------------------------------------------------------------------------- *)

let vEQ_CLAUSES = prove
 ((parse_term "!t. ((T <=> t) <=> t) /\\ ((t <=> T) <=> t) /\\\n       ((F <=> t) <=> ~t) /\\ ((t <=> F) <=> ~t)"),
  vITAUT_TAC);;

let vNOT_CLAUSES_WEAK = prove
 ((parse_term "(~T <=> F) /\\ (~F <=> T)"),
  vITAUT_TAC);;

let vAND_CLAUSES = prove
 ((parse_term "!t. (T /\\ t <=> t) /\\ (t /\\ T <=> t) /\\ (F /\\ t <=> F) /\\\n       (t /\\ F <=> F) /\\ (t /\\ t <=> t)"),
  vITAUT_TAC);;

let vOR_CLAUSES = prove
 ((parse_term "!t. (T \\/ t <=> T) /\\ (t \\/ T <=> T) /\\ (F \\/ t <=> t) /\\\n       (t \\/ F <=> t) /\\ (t \\/ t <=> t)"),
  vITAUT_TAC);;

let vIMP_CLAUSES = prove
 ((parse_term "!t. (T ==> t <=> t) /\\ (t ==> T <=> T) /\\ (F ==> t <=> T) /\\\n       (t ==> t <=> T) /\\ (t ==> F <=> ~t)"),
  vITAUT_TAC);;

extend_basic_rewrites
  [vREFL_CLAUSE;
   vEQ_CLAUSES;
   vNOT_CLAUSES_WEAK;
   vAND_CLAUSES;
   vOR_CLAUSES;
   vIMP_CLAUSES;
   vFORALL_SIMP;
   vEXISTS_SIMP;
   vBETA_THM;
   let vIMP_EQ_CLAUSE = prove
    ((parse_term "((x = x) ==> p) <=> p"),
     vREWRITE_TAC[vEQT_INTRO(vSPEC_ALL vEQ_REFL); vIMP_CLAUSES]) in
   vIMP_EQ_CLAUSE];;

extend_basic_congs
  [vITAUT (parse_term "(p <=> p') ==> (p' ==> (q <=> q')) ==> (p ==> q <=> p' ==> q')")];;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for unique existence.                                        *)
(* ------------------------------------------------------------------------- *)

let vEXISTS_UNIQUE_THM = prove
 ((parse_term "!P. (?!x:A. P x) <=> (?x. P x) /\\ (!x x'. P x /\\ P x' ==> (x = x'))"),
  vGEN_TAC ----> vREWRITE_TAC[vEXISTS_UNIQUE_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Trivial instances of existence.                                           *)
(* ------------------------------------------------------------------------- *)

let vEXISTS_REFL = prove
 ((parse_term "!a:A. ?x. x = a"),
  vGEN_TAC ----> vEXISTS_TAC (parse_term "a:A") ----> vREFL_TAC);;

let vEXISTS_UNIQUE_REFL = prove
 ((parse_term "!a:A. ?!x. x = a"),
  vGEN_TAC ----> vREWRITE_TAC[vEXISTS_UNIQUE_THM] ---->
  vREPEAT(vEQ_TAC |---> vSTRIP_TAC) +---->
   [vEXISTS_TAC (parse_term "a:A"); vASM_REWRITE_TAC[]] ---->
  vREFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Unwinding.                                                                *)
(* ------------------------------------------------------------------------- *)

let vUNWIND_THM1 = prove
 ((parse_term "!P (a:A). (?x. a = x /\\ P x) <=> P a"),
  vREPEAT vGEN_TAC ----> vEQ_TAC +---->
   [vDISCH_THEN(vCHOOSE_THEN (vCONJUNCTS_THEN2 vSUBST1_TAC vACCEPT_TAC));
    vDISCH_TAC ----> vEXISTS_TAC (parse_term "a:A") ---->
    vCONJ_TAC ----> vTRY(vFIRST_ASSUM vMATCH_ACCEPT_TAC) ---->
    vREFL_TAC]);;

let vUNWIND_THM2 = prove
 ((parse_term "!P (a:A). (?x. x = a /\\ P x) <=> P a"),
  vREPEAT vGEN_TAC ----> vCONV_TAC(vLAND_CONV(vONCE_DEPTH_CONV vSYM_CONV)) ---->
  vMATCH_ACCEPT_TAC vUNWIND_THM1);;

let vFORALL_UNWIND_THM2 = prove
 ((parse_term "!P (a:A). (!x. x = a ==> P x) <=> P a"),
  vREPEAT vGEN_TAC ----> vEQ_TAC +---->
   [vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "a:A")) ----> vREWRITE_TAC[];
    vDISCH_TAC ----> vGEN_TAC ----> vDISCH_THEN vSUBST1_TAC ---->
    vASM_REWRITE_TAC[]]);;

let vFORALL_UNWIND_THM1 = prove
 ((parse_term "!P a. (!x. a = x ==> P x) <=> P a"),
  vREPEAT vGEN_TAC ----> vCONV_TAC(vLAND_CONV(vONCE_DEPTH_CONV vSYM_CONV)) ---->
  vMATCH_ACCEPT_TAC vFORALL_UNWIND_THM2);;

(* ------------------------------------------------------------------------- *)
(* Permuting quantifiers.                                                    *)
(* ------------------------------------------------------------------------- *)

let vSWAP_FORALL_THM = prove
 ((parse_term "!P:A->B->bool. (!x y. P x y) <=> (!y x. P x y)"),
  vITAUT_TAC);;

let vSWAP_EXISTS_THM = prove
 ((parse_term "!P:A->B->bool. (?x y. P x y) <=> (?y x. P x y)"),
  vITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Universal quantifier and conjunction.                                     *)
(* ------------------------------------------------------------------------- *)

let vFORALL_AND_THM = prove
 ((parse_term "!P Q. (!x:A. P x /\\ Q x) <=> (!x. P x) /\\ (!x. Q x)"),
  vITAUT_TAC);;

let vAND_FORALL_THM = prove
 ((parse_term "!P Q. (!x. P x) /\\ (!x. Q x) <=> (!x:A. P x /\\ Q x)"),
  vITAUT_TAC);;

let vLEFT_AND_FORALL_THM = prove
 ((parse_term "!P Q. (!x:A. P x) /\\ Q <=> (!x:A. P x /\\ Q)"),
  vITAUT_TAC);;

let vRIGHT_AND_FORALL_THM = prove
 ((parse_term "!P Q. P /\\ (!x:A. Q x) <=> (!x. P /\\ Q x)"),
  vITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and disjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let vEXISTS_OR_THM = prove
 ((parse_term "!P Q. (?x:A. P x \\/ Q x) <=> (?x. P x) \\/ (?x. Q x)"),
  vITAUT_TAC);;

let vOR_EXISTS_THM = prove
 ((parse_term "!P Q. (?x. P x) \\/ (?x. Q x) <=> (?x:A. P x \\/ Q x)"),
  vITAUT_TAC);;

let vLEFT_OR_EXISTS_THM = prove
 ((parse_term "!P Q. (?x. P x) \\/ Q <=> (?x:A. P x \\/ Q)"),
  vITAUT_TAC);;

let vRIGHT_OR_EXISTS_THM = prove
 ((parse_term "!P Q. P \\/ (?x. Q x) <=> (?x:A. P \\/ Q x)"),
  vITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Existential quantifier and conjunction.                                   *)
(* ------------------------------------------------------------------------- *)

let vLEFT_EXISTS_AND_THM = prove
 ((parse_term "!P Q. (?x:A. P x /\\ Q) <=> (?x:A. P x) /\\ Q"),
  vITAUT_TAC);;

let vRIGHT_EXISTS_AND_THM = prove
 ((parse_term "!P Q. (?x:A. P /\\ Q x) <=> P /\\ (?x:A. Q x)"),
  vITAUT_TAC);;

let vTRIV_EXISTS_AND_THM = prove
 ((parse_term "!P Q. (?x:A. P /\\ Q) <=> (?x:A. P) /\\ (?x:A. Q)"),
  vITAUT_TAC);;

let vLEFT_AND_EXISTS_THM = prove
 ((parse_term "!P Q. (?x:A. P x) /\\ Q <=> (?x:A. P x /\\ Q)"),
  vITAUT_TAC);;

let vRIGHT_AND_EXISTS_THM = prove
 ((parse_term "!P Q. P /\\ (?x:A. Q x) <=> (?x:A. P /\\ Q x)"),
  vITAUT_TAC);;

let vTRIV_AND_EXISTS_THM = prove
 ((parse_term "!P Q. (?x:A. P) /\\ (?x:A. Q) <=> (?x:A. P /\\ Q)"),
  vITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Only trivial instances of universal quantifier and disjunction.           *)
(* ------------------------------------------------------------------------- *)

let vTRIV_FORALL_OR_THM = prove
 ((parse_term "!P Q. (!x:A. P \\/ Q) <=> (!x:A. P) \\/ (!x:A. Q)"),
  vITAUT_TAC);;

let vTRIV_OR_FORALL_THM = prove
 ((parse_term "!P Q. (!x:A. P) \\/ (!x:A. Q) <=> (!x:A. P \\/ Q)"),
  vITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Implication and quantifiers.                                              *)
(* ------------------------------------------------------------------------- *)

let vRIGHT_IMP_FORALL_THM = prove
 ((parse_term "!P Q. (P ==> !x:A. Q x) <=> (!x. P ==> Q x)"),
  vITAUT_TAC);;

let vRIGHT_FORALL_IMP_THM = prove
 ((parse_term "!P Q. (!x. P ==> Q x) <=> (P ==> !x:A. Q x)"),
  vITAUT_TAC);;

let vLEFT_IMP_EXISTS_THM = prove
 ((parse_term "!P Q. ((?x:A. P x) ==> Q) <=> (!x. P x ==> Q)"),
  vITAUT_TAC);;

let vLEFT_FORALL_IMP_THM = prove
 ((parse_term "!P Q. (!x. P x ==> Q) <=> ((?x:A. P x) ==> Q)"),
  vITAUT_TAC);;

let vTRIV_FORALL_IMP_THM = prove
 ((parse_term "!P Q. (!x:A. P ==> Q) <=> ((?x:A. P) ==> (!x:A. Q))"),
  vITAUT_TAC);;

let vTRIV_EXISTS_IMP_THM = prove
 ((parse_term "!P Q. (?x:A. P ==> Q) <=> ((!x:A. P) ==> (?x:A. Q))"),
  vITAUT_TAC);;

(* ------------------------------------------------------------------------- *)
(* Monotonicity theorems for logical operations w.r.t. implication.          *)
(* ------------------------------------------------------------------------- *)

let vMONO_AND = vITAUT (parse_term "(A ==> B) /\\ (C ==> D) ==> (A /\\ C ==> B /\\ D)");;

let vMONO_OR = vITAUT (parse_term "(A ==> B) /\\ (C ==> D) ==> (A \\/ C ==> B \\/ D)");;

let vMONO_IMP = vITAUT (parse_term "(B ==> A) /\\ (C ==> D) ==> ((A ==> C) ==> (B ==> D))");;

let vMONO_NOT = vITAUT (parse_term "(B ==> A) ==> (~A ==> ~B)");;

let vMONO_FORALL = prove
 ((parse_term "(!x:A. P x ==> Q x) ==> ((!x. P x) ==> (!x. Q x))"),
  vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vASM_REWRITE_TAC[]);;

let vMONO_EXISTS = prove
 ((parse_term "(!x:A. P x ==> Q x) ==> ((?x. P x) ==> (?x. Q x))"),
  vDISCH_TAC ----> vDISCH_THEN(vX_CHOOSE_TAC (parse_term "x:A")) ---->
  vEXISTS_TAC (parse_term "x:A") ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A generic "without loss of generality" lemma for symmetry.                *)
(* ------------------------------------------------------------------------- *)

let vWLOG_RELATION = prove
 ((parse_term "!R P. (!x y. P x y ==> P y x) /\\\n         (!x y. R x y \\/ R y x) /\\\n         (!x y. R x y ==> P x y)\n         ==> !x y. P x y"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN
   (vCONJUNCTS_THEN2 vASSUME_TAC (vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC)) ---->
  vREPEAT(vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC) ---->
  vSTRIP_TAC ----> vASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Alternative versions of unique existence.                                 *)
(* ------------------------------------------------------------------------- *)

let vEXISTS_UNIQUE_ALT = prove
 ((parse_term "!P:A->bool. (?!x. P x) <=> (?x. !y. P y <=> (x = y))"),
  vGEN_TAC ----> vREWRITE_TAC[vEXISTS_UNIQUE_THM] ----> vEQ_TAC +---->
   [vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "x:A")) vASSUME_TAC) ---->
    vEXISTS_TAC (parse_term "x:A") ----> vGEN_TAC ----> vEQ_TAC +---->
     [vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vFIRST_ASSUM vMATCH_ACCEPT_TAC];
    vDISCH_THEN(vX_CHOOSE_TAC (parse_term "x:A")) ---->
    vASM_REWRITE_TAC[vGSYM vEXISTS_REFL] ----> vREPEAT vGEN_TAC ---->
    vDISCH_THEN(vCONJUNCTS_THEN (vSUBST1_TAC -| vSYM)) ----> vREFL_TAC]);;

let vEXISTS_UNIQUE = prove
 ((parse_term "!P:A->bool. (?!x. P x) <=> (?x. P x /\\ !y. P y ==> (y = x))"),
  vGEN_TAC ----> vREWRITE_TAC[vEXISTS_UNIQUE_ALT] ---->
  vAP_TERM_TAC ----> vABS_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vBINDER_CONV)
   [vITAUT (parse_term "(a <=> b) <=> (a ==> b) /\\ (b ==> a)")] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vEQ_SYM_EQ] ---->
  vREWRITE_TAC[vFORALL_AND_THM] ----> vSIMP_TAC[] ---->
  vREWRITE_TAC[vLEFT_FORALL_IMP_THM; vEXISTS_REFL] ---->
  vREWRITE_TAC[vCONJ_ACI]);;

(* ------------------------------------------------------------------------- *)
(* DESTRUCT_TAC, FIX_TAC, INTRO_TAC and HYP_TAC, giving more brief and       *)
(* elegant ways of naming introduced variables and assumptions (from Marco   *)
(* Maggesi).                                                                 *)
(* ------------------------------------------------------------------------- *)

let vDESTRUCT_TAC,vFIX_TAC,vINTRO_TAC,vHYP_TAC =
  (* ---------------------------------------------------------------------- *)
  (* Like GEN_TAC but fails instead of generating a primed variant when the *)
  (* variable occurs free in the context.                                   *)
  (* ---------------------------------------------------------------------- *)
  let (vPURE_GEN_TAC: tactic) =
    fun (asl,w) ->
      try let x = fst(dest_forall w) in
          let avoids = itlist (union -| thm_frees -| snd) asl (frees w) in
          if mem x avoids then fail() else vX_GEN_TAC x (asl,w)
      with Failure _ -> failwith "PURE_GEN_TAC"
  (* ---------------------------------------------------------------------- *)
  (* Like X_GEN_TAC but needs only the name of the variable, not the type.  *)
  (* ---------------------------------------------------------------------- *)
  and (vNAME_GEN_TAC: string -> tactic) =
    fun s gl ->
      let ty = (snd -| dest_var -| fst -| dest_forall -| snd) gl  in
      vX_GEN_TAC (mk_var(s,ty)) gl
  and vOBTAIN_THEN v ttac th =
    let ty = (snd -| dest_var -| fst -| dest_exists -| concl) th in
    vX_CHOOSE_THEN (mk_var(v,ty)) ttac th
  and vCONJ_LIST_TAC = end_itlist (fun t1 t2 -> vCONJ_TAC +----> [t1; t2])
  and vNUM_DISJ_TAC n =
    if n <= 0 then failwith "NUM_DISJ_TAC" else
    vREPLICATE_TAC (n-1) vDISJ2_TAC ----> vREPEAT vDISJ1_TAC
  and vNAME_PULL_FORALL_CONV =
    let vSWAP_FORALL_CONV = vREWR_CONV vSWAP_FORALL_THM
    and vAND_FORALL_CONV = vGEN_REWRITE_CONV vI [vAND_FORALL_THM]
    and vRIGHT_IMP_FORALL_CONV = vGEN_REWRITE_CONV vI [vRIGHT_IMP_FORALL_THM] in
    fun s ->
      let rec vPULL_FORALL tm =
          if is_forall tm then
            if name_of(fst(dest_forall tm)) = s then vREFL tm else
              (vBINDER_CONV vPULL_FORALL +---> vSWAP_FORALL_CONV) tm
          else if is_imp tm then
            (vRAND_CONV vPULL_FORALL +---> vRIGHT_IMP_FORALL_CONV) tm
          else if is_conj tm then
            (vBINOP_CONV vPULL_FORALL +---> vAND_FORALL_CONV) tm
          else
            fail () in
      vPULL_FORALL in
  let pa_ident p = function
      Ident s::rest when p s -> s,rest
    | _ -> raise Noparse in
  let pa_label = pa_ident isalnum
  and pa_var = pa_ident isalpha in
  let fix_tac =
    let fix_var v = vCONV_TAC (vNAME_PULL_FORALL_CONV v) ----> vPURE_GEN_TAC
    and fix_rename =
      function u,[v] -> vCONV_TAC (vNAME_PULL_FORALL_CONV v) ----> vNAME_GEN_TAC u
             | u,_   -> vNAME_GEN_TAC u in
    let vars =
      let pa_rename =
        let oname = possibly (a(Ident "/") ++ pa_var >> snd) in
        (a(Resword "[") ++ pa_var >> snd) ++ oname ++ a(Resword "]") >> fst in
      many ((pa_rename >> fix_rename) ||| (pa_var >> fix_var)) >> vEVERY
    and star = possibly (a (Ident "*") >> vK ()) in
    vars ++ star >> function tac,[] -> tac | tac,_ -> tac ----> vREPEAT vGEN_TAC
  and destruct_tac =
    let vOBTAINL_THEN : string list -> thm_tactical =
      vEVERY_TCL -| map vOBTAIN_THEN in
    let rec destruct inp = disj inp
    and disj inp =
      let vDISJ_CASES_LIST = end_itlist vDISJ_CASES_THEN2 in
      (listof conj (a(Resword "|")) "Disjunction" >> vDISJ_CASES_LIST) inp
    and conj inp = (atleast 1 atom >> end_itlist vCONJUNCTS_THEN2) inp
    and obtain inp =
      let obtain_prfx =
        let var_list = atleast 1 pa_var in
        (a(Ident "@") ++ var_list >> snd) ++ a(Resword ".") >> fst in
      (obtain_prfx ++ destruct >> uncurry vOBTAINL_THEN) inp
    and atom inp =
      let label =
        function Ident "_"::res -> vK vALL_TAC,res
               | Ident "+"::res -> vMP_TAC,res
               | Ident s::res when isalnum s -> vLABEL_TAC s,res
               | _ -> raise Noparse
      and paren =
        (a(Resword "(") ++ destruct >> snd) ++ a(Resword ")") >> fst in
      (obtain ||| label ||| paren) inp in
    destruct in
  let intro_tac =
    let number = function
        Ident s::rest ->
          (try check ((<=) 1) (int_of_string s), rest
           with Failure _ -> raise Noparse)
      | _ -> raise Noparse
    and pa_fix = a(Ident "!") ++ fix_tac >> snd
    and pa_dest = destruct_tac >> vDISCH_THEN in
    let pa_prefix =
      elistof (pa_fix ||| pa_dest) (a(Resword ";")) "Prefix intro pattern" in
    let rec pa_intro toks =
      (pa_prefix ++ possibly pa_postfix >> uncurry (@) >> vEVERY) toks
    and pa_postfix toks = (pa_conj ||| pa_disj) toks
    and pa_conj toks =
      let conjs =
        listof pa_intro (a(Ident "&")) "Intro pattern" >> vCONJ_LIST_TAC in
      ((a(Resword "{") ++ conjs >> snd) ++ a(Resword "}") >> fst) toks
    and pa_disj toks =
      let disj = number >> vNUM_DISJ_TAC in
      ((a(Ident "#") ++ disj >> snd) ++ pa_intro >> uncurry (---->)) toks in
    pa_intro in
  let hyp_tac rule =
    let pa_action = function
        Resword ":" :: rest -> vREMOVE_THEN,rest
      | Resword "->" :: rest -> vUSE_THEN,rest
      | _ -> raise Noparse in
    pa_label ++ possibly (pa_action ++ destruct_tac) >>
    (function
       | lbl,[action,tac] -> action lbl (tac -| rule)
       | lbl,_ -> vREMOVE_THEN lbl (vLABEL_TAC lbl -| rule)) in
  let vDESTRUCT_TAC s =
    let tac,rest =
      (fix "Destruct pattern" destruct_tac -| lex -| explode) s in
    if rest=[] then tac else failwith "Garbage after destruct pattern"
  and vINTRO_TAC s =
    let tac,rest =
      (fix "Introduction pattern" intro_tac -| lex -| explode) s in
    if rest=[] then tac else failwith "Garbage after intro pattern"
  and vFIX_TAC s =
    let tac,rest = (fix_tac -| lex -| explode) s in
    if rest=[] then tac else failwith "FIX_TAC: invalid pattern"
  and vHYP_TAC s rule =
    let tac,rest = (hyp_tac rule -| lex -| explode) s in
    if rest=[] then tac else failwith "HYP_TAC: invalid pattern" in
  vDESTRUCT_TAC,vFIX_TAC,vINTRO_TAC,vHYP_TAC;;

let vCLAIM_TAC s tm = vSUBGOAL_THEN tm (vDESTRUCT_TAC s);;
