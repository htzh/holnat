(* ========================================================================= *)
(* Very basic set theory (using predicates as sets).                         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2016                       *)
(*              (c) Copyright, Marco Maggesi 2012-2017                       *)
(*             (c) Copyright, Andrea Gabrielli 2012-2017                     *)
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
open Simp
open Theorems
open Ind_defs
open Class
open Trivia
open Meson
open Metis
open Pair
open Nums
open Recursion
open Arith
open Wf
open Calc_num
open Int
;;

(* ------------------------------------------------------------------------- *)
(* Infix symbols for set operations.                                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("IN",(11,"right"));;
parse_as_infix("SUBSET",(12,"right"));;
parse_as_infix("PSUBSET",(12,"right"));;
parse_as_infix("INTER",(20,"right"));;
parse_as_infix("UNION",(16,"right"));;
parse_as_infix("DIFF",(18,"left"));;
parse_as_infix("INSERT",(21,"right"));;
parse_as_infix("DELETE",(21,"left"));;

parse_as_infix("HAS_SIZE",(12,"right"));;
parse_as_infix("<=_c",(12,"right"));;
parse_as_infix("<_c",(12,"right"));;
parse_as_infix(">=_c",(12,"right"));;
parse_as_infix(">_c",(12,"right"));;
parse_as_infix("=_c",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Set membership.                                                           *)
(* ------------------------------------------------------------------------- *)

let vIN = new_definition
  (parse_term "!P:A->bool. !x. x IN P <=> P x");;

(* ------------------------------------------------------------------------- *)
(* Axiom of extensionality in this framework.                                *)
(* ------------------------------------------------------------------------- *)

let vEXTENSION = prove
 ((parse_term "!s t. (s = t) <=> !x:A. x IN s <=> x IN t"),
  vREWRITE_TAC[vIN; vFUN_EQ_THM]);;

(* ------------------------------------------------------------------------- *)
(* General specification.                                                    *)
(* ------------------------------------------------------------------------- *)

let vGSPEC = new_definition
  (parse_term "GSPEC (p:A->bool) = p");;

let vSETSPEC = new_definition
  (parse_term "SETSPEC v P t <=> P /\\ (v = t)");;

(* ------------------------------------------------------------------------- *)
(* Rewrite rule for eliminating set-comprehension membership assertions.     *)
(* ------------------------------------------------------------------------- *)

let vIN_ELIM_THM = prove
 ((parse_term "(!P x. x IN GSPEC (\\v. P (SETSPEC v)) <=> P (\\p t. p /\\ (x = t))) /\\\n   (!p x. x IN GSPEC (\\v. ?y. SETSPEC v (p y) y) <=> p x) /\\\n   (!P x. GSPEC (\\v. P (SETSPEC v)) x <=> P (\\p t. p /\\ (x = t))) /\\\n   (!p x. GSPEC (\\v. ?y. SETSPEC v (p y) y) x <=> p x) /\\\n   (!p x. x IN (\\y. p y) <=> p x)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vIN; vGSPEC] ---->
  vTRY(vAP_TERM_TAC ----> vREWRITE_TAC[vFUN_EQ_THM]) ---->
  vREWRITE_TAC[vSETSPEC] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* These two definitions are needed first, for the parsing of enumerations.  *)
(* ------------------------------------------------------------------------- *)

let vEMPTY = new_definition
  (parse_term "EMPTY = (\\x:A. F)");;

let vINSERT_DEF = new_definition
  (parse_term "x INSERT s = \\y:A. y IN s \\/ (y = x)");;

(* ------------------------------------------------------------------------- *)
(* The other basic operations.                                               *)
(* ------------------------------------------------------------------------- *)

let vUNIV = new_definition
  (parse_term "UNIV = (\\x:A. T)");;

let vUNION = new_definition
  (parse_term "s UNION t = {x:A | x IN s \\/ x IN t}");;

let vUNIONS = new_definition
  (parse_term "UNIONS s = {x:A | ?u. u IN s /\\ x IN u}");;

let vINTER = new_definition
  (parse_term "s INTER t = {x:A | x IN s /\\ x IN t}");;

let vINTERS = new_definition
  (parse_term "INTERS s = {x:A | !u. u IN s ==> x IN u}");;

let vDIFF = new_definition
  (parse_term "s DIFF t =  {x:A | x IN s /\\ ~(x IN t)}");;

let vINSERT = prove
 ((parse_term "x INSERT s = {y:A | y IN s \\/ (y = x)}"),
  vREWRITE_TAC[vEXTENSION; vINSERT_DEF; vIN_ELIM_THM]);;

let vDELETE = new_definition
  (parse_term "s DELETE x = {y:A | y IN s /\\ ~(y = x)}");;

(* ------------------------------------------------------------------------- *)
(* Other basic predicates.                                                   *)
(* ------------------------------------------------------------------------- *)

let vSUBSET = new_definition
  (parse_term "s SUBSET t <=> !x:A. x IN s ==> x IN t");;

let vPSUBSET = new_definition
  (parse_term "(s:A->bool) PSUBSET t <=> s SUBSET t /\\ ~(s = t)");;

let vDISJOINT = new_definition
  (parse_term "DISJOINT (s:A->bool) t <=> (s INTER t = EMPTY)");;

let vSING = new_definition
  (parse_term "SING s = ?x:A. s = {x}");;

(* ------------------------------------------------------------------------- *)
(* Finiteness.                                                               *)
(* ------------------------------------------------------------------------- *)

let vFINITE_RULES,vFINITE_INDUCT,vFINITE_CASES =
  new_inductive_definition
    (parse_term "FINITE (EMPTY:A->bool) /\\\n     !(x:A) s. FINITE s ==> FINITE (x INSERT s)");;

let vINFINITE = new_definition
  (parse_term "INFINITE (s:A->bool) <=> ~(FINITE s)");;

(* ------------------------------------------------------------------------- *)
(* Stuff concerned with functions.                                           *)
(* ------------------------------------------------------------------------- *)

let vIMAGE = new_definition
  (parse_term "IMAGE (f:A->B) s = { y | ?x. x IN s /\\ (y = f x)}");;

let vINJ = new_definition
  (parse_term "INJ (f:A->B) s t <=>\n     (!x. x IN s ==> (f x) IN t) /\\\n     (!x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y))");;

let vSURJ = new_definition
  (parse_term "SURJ (f:A->B) s t <=>\n     (!x. x IN s ==> (f x) IN t) /\\\n     (!x. (x IN t) ==> ?y. y IN s /\\ (f y = x))");;

let vBIJ = new_definition
  (parse_term "BIJ (f:A->B) s t <=> INJ f s t /\\ SURJ f s t");;

(* ------------------------------------------------------------------------- *)
(* Another funny thing.                                                      *)
(* ------------------------------------------------------------------------- *)

let vCHOICE = new_definition
  (parse_term "CHOICE s = @x:A. x IN s");;

let vREST = new_definition
  (parse_term "REST (s:A->bool) = s DELETE (CHOICE s)");;

(* ------------------------------------------------------------------------- *)
(* Basic membership properties.                                              *)
(* ------------------------------------------------------------------------- *)

let vNOT_IN_EMPTY = prove
 ((parse_term "!x:A. ~(x IN EMPTY)"),
  vREWRITE_TAC[vIN; vEMPTY]);;

let vIN_UNIV = prove
 ((parse_term "!x:A. x IN UNIV"),
  vREWRITE_TAC[vUNIV; vIN]);;

let vIN_UNION = prove
 ((parse_term "!s t (x:A). x IN (s UNION t) <=> x IN s \\/ x IN t"),
  vREWRITE_TAC[vIN_ELIM_THM; vUNION]);;

let vIN_UNIONS = prove
 ((parse_term "!s (x:A). x IN (UNIONS s) <=> ?t. t IN s /\\ x IN t"),
  vREWRITE_TAC[vIN_ELIM_THM; vUNIONS]);;

let vIN_INTER = prove
 ((parse_term "!s t (x:A). x IN (s INTER t) <=> x IN s /\\ x IN t"),
  vREWRITE_TAC[vIN_ELIM_THM; vINTER]);;

let vIN_INTERS = prove
 ((parse_term "!s (x:A). x IN (INTERS s) <=> !t. t IN s ==> x IN t"),
  vREWRITE_TAC[vIN_ELIM_THM; vINTERS]);;

let vIN_DIFF = prove
 ((parse_term "!(s:A->bool) t x. x IN (s DIFF t) <=> x IN s /\\ ~(x IN t)"),
  vREWRITE_TAC[vIN_ELIM_THM; vDIFF]);;

let vIN_INSERT = prove
 ((parse_term "!x:A. !y s. x IN (y INSERT s) <=> (x = y) \\/ x IN s"),
  vONCE_REWRITE_TAC[vDISJ_SYM] ----> vREWRITE_TAC[vIN_ELIM_THM; vINSERT]);;

let vIN_DELETE = prove
 ((parse_term "!s. !x:A. !y. x IN (s DELETE y) <=> x IN s /\\ ~(x = y)"),
  vREWRITE_TAC[vIN_ELIM_THM; vDELETE]);;

let vIN_SING = prove
 ((parse_term "!x y. x IN {y:A} <=> (x = y)"),
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY]);;

let vIN_IMAGE = prove
 ((parse_term "!y:B. !s f. (y IN (IMAGE f s)) <=> ?x:A. (y = f x) /\\ x IN s"),
  vONCE_REWRITE_TAC[vCONJ_SYM] ----> vREWRITE_TAC[vIN_ELIM_THM; vIMAGE]);;

let vIN_REST = prove
 ((parse_term "!x:A. !s. x IN (REST s) <=> x IN s /\\ ~(x = CHOICE s)"),
  vREWRITE_TAC[vREST; vIN_DELETE]);;

let vFORALL_IN_INSERT = prove
 ((parse_term "!P a s. (!x. x IN (a INSERT s) ==> P x) <=> P a /\\ (!x. x IN s ==> P x)"),
  vREWRITE_TAC[vIN_INSERT] ----> vMESON_TAC[]);;

let vEXISTS_IN_INSERT = prove
 ((parse_term "!P a s. (?x. x IN (a INSERT s) /\\ P x) <=> P a \\/ ?x. x IN s /\\ P x"),
  vREWRITE_TAC[vIN_INSERT] ----> vMESON_TAC[]);;

let vFORALL_IN_UNION = prove
 ((parse_term "!P s t:A->bool.\n        (!x. x IN s UNION t ==> P x) <=>\n        (!x. x IN s ==> P x) /\\ (!x. x IN t ==> P x)"),
  vREWRITE_TAC[vIN_UNION] ----> vMESON_TAC[]);;

let vEXISTS_IN_UNION = prove
 ((parse_term "!P s t:A->bool.\n        (?x. x IN s UNION t /\\ P x) <=>\n        (?x. x IN s /\\ P x) \\/ (?x. x IN t /\\ P x)"),
  vREWRITE_TAC[vIN_UNION] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic property of the choice function.                                    *)
(* ------------------------------------------------------------------------- *)

let vCHOICE_DEF = prove
 ((parse_term "!s:A->bool. ~(s = EMPTY) ==> (CHOICE s) IN s"),
  vREWRITE_TAC[vCHOICE; vEXTENSION; vNOT_IN_EMPTY; vNOT_FORALL_THM; vEXISTS_THM]);;

(* ------------------------------------------------------------------------- *)
(* Tactic to automate some routine set theory by reduction to FOL.           *)
(* ------------------------------------------------------------------------- *)

let vSET_TAC =
  let vPRESET_TAC =
    vPOP_ASSUM_LIST(vK vALL_TAC) ----> vREPEAT vCOND_CASES_TAC ---->
    vREWRITE_TAC[vEXTENSION; vSUBSET; vPSUBSET; vDISJOINT; vSING] ---->
    vREWRITE_TAC[vNOT_IN_EMPTY; vIN_UNIV; vIN_UNION; vIN_INTER; vIN_DIFF; vIN_INSERT;
                vIN_DELETE; vIN_REST; vIN_INTERS; vIN_UNIONS; vIN_IMAGE;
                vIN_ELIM_THM; vIN] in
  fun ths ->
    (if ths = [] then vALL_TAC else vMP_TAC(end_itlist vCONJ ths)) ---->
    vPRESET_TAC ---->
    vMESON_TAC[];;

let vSET_RULE tm = prove(tm,vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Misc. theorems.                                                           *)
(* ------------------------------------------------------------------------- *)

let vNOT_EQUAL_SETS = prove
 ((parse_term "!s:A->bool. !t. ~(s = t) <=> ?x. x IN t <=> ~(x IN s)"),
  vSET_TAC[]);;

let vINSERT_RESTRICT = prove
 ((parse_term "!P s a:A.\n        {x | x IN a INSERT s /\\ P x} =\n        if P a then a INSERT {x | x IN s /\\ P x} else {x | x IN s /\\ P x}"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ----> vASM vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The empty set.                                                            *)
(* ------------------------------------------------------------------------- *)

let vMEMBER_NOT_EMPTY = prove
 ((parse_term "!s:A->bool. (?x. x IN s) <=> ~(s = EMPTY)"),
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* The universal set.                                                        *)
(* ------------------------------------------------------------------------- *)

let vUNIV_NOT_EMPTY = prove
 ((parse_term "~(UNIV:A->bool = EMPTY)"),
  vSET_TAC[]);;

let vEMPTY_NOT_UNIV = prove
 ((parse_term "~(EMPTY:A->bool = UNIV)"),
  vSET_TAC[]);;

let vEQ_UNIV = prove
 ((parse_term "(!x:A. x IN s) <=> (s = UNIV)"),
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set inclusion.                                                            *)
(* ------------------------------------------------------------------------- *)

let vSUBSET_TRANS = prove
 ((parse_term "!(s:A->bool) t u. s SUBSET t /\\ t SUBSET u ==> s SUBSET u"),
  vSET_TAC[]);;

let vSUBSET_REFL = prove
 ((parse_term "!s:A->bool. s SUBSET s"),
  vSET_TAC[]);;

let vSUBSET_ANTISYM = prove
 ((parse_term "!(s:A->bool) t. s SUBSET t /\\ t SUBSET s ==> s = t"),
  vSET_TAC[]);;

let vSUBSET_ANTISYM_EQ = prove
 ((parse_term "!(s:A->bool) t. s SUBSET t /\\ t SUBSET s <=> s = t"),
  vSET_TAC[]);;

let vEMPTY_SUBSET = prove
 ((parse_term "!s:A->bool. EMPTY SUBSET s"),
  vSET_TAC[]);;

let vSUBSET_EMPTY = prove
 ((parse_term "!s:A->bool. s SUBSET EMPTY <=> (s = EMPTY)"),
  vSET_TAC[]);;

let vSUBSET_UNIV = prove
 ((parse_term "!s:A->bool. s SUBSET UNIV"),
  vSET_TAC[]);;

let vUNIV_SUBSET = prove
 ((parse_term "!s:A->bool. UNIV SUBSET s <=> (s = UNIV)"),
  vSET_TAC[]);;

let vSING_SUBSET = prove
 ((parse_term "!s x. {x} SUBSET s <=> x IN s"),
  vSET_TAC[]);;

let vSUBSET_RESTRICT = prove
 ((parse_term "!s P. {x | x IN s /\\ P x} SUBSET s"),
  vSIMP_TAC[vSUBSET; vIN_ELIM_THM]);;

(* ------------------------------------------------------------------------- *)
(* Proper subset.                                                            *)
(* ------------------------------------------------------------------------- *)

let vPSUBSET_TRANS = prove
 ((parse_term "!(s:A->bool) t u. s PSUBSET t /\\ t PSUBSET u ==> s PSUBSET u"),
  vSET_TAC[]);;

let vPSUBSET_SUBSET_TRANS = prove
 ((parse_term "!(s:A->bool) t u. s PSUBSET t /\\ t SUBSET u ==> s PSUBSET u"),
  vSET_TAC[]);;

let vSUBSET_PSUBSET_TRANS = prove
 ((parse_term "!(s:A->bool) t u. s SUBSET t /\\ t PSUBSET u ==> s PSUBSET u"),
  vSET_TAC[]);;

let vPSUBSET_IRREFL = prove
 ((parse_term "!s:A->bool. ~(s PSUBSET s)"),
  vSET_TAC[]);;

let vNOT_PSUBSET_EMPTY = prove
 ((parse_term "!s:A->bool. ~(s PSUBSET EMPTY)"),
  vSET_TAC[]);;

let vNOT_UNIV_PSUBSET = prove
 ((parse_term "!s:A->bool. ~(UNIV PSUBSET s)"),
  vSET_TAC[]);;

let vPSUBSET_UNIV = prove
 ((parse_term "!s:A->bool. s PSUBSET UNIV <=> ?x. ~(x IN s)"),
  vSET_TAC[]);;

let vPSUBSET_ALT = prove
 ((parse_term "!s t:A->bool. s PSUBSET t <=> s SUBSET t /\\ (?a. a IN t /\\ ~(a IN s))"),
  vREWRITE_TAC[vPSUBSET] ----> vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Union.                                                                    *)
(* ------------------------------------------------------------------------- *)

let vUNION_ASSOC = prove
 ((parse_term "!(s:A->bool) t u. (s UNION t) UNION u = s UNION (t UNION u)"),
  vSET_TAC[]);;

let vUNION_IDEMPOT = prove
 ((parse_term "!s:A->bool. s UNION s = s"),
  vSET_TAC[]);;

let vUNION_COMM = prove
 ((parse_term "!(s:A->bool) t. s UNION t = t UNION s"),
  vSET_TAC[]);;

let vSUBSET_UNION = prove
 ((parse_term "(!s:A->bool. !t. s SUBSET (s UNION t)) /\\\n   (!s:A->bool. !t. s SUBSET (t UNION s))"),
  vSET_TAC[]);;

let vSUBSET_UNION_ABSORPTION = prove
 ((parse_term "!s:A->bool. !t. s SUBSET t <=> (s UNION t = t)"),
  vSET_TAC[]);;

let vUNION_EMPTY = prove
 ((parse_term "(!s:A->bool. EMPTY UNION s = s) /\\\n   (!s:A->bool. s UNION EMPTY = s)"),
  vSET_TAC[]);;

let vUNION_UNIV = prove
 ((parse_term "(!s:A->bool. UNIV UNION s = UNIV) /\\\n   (!s:A->bool. s UNION UNIV = UNIV)"),
  vSET_TAC[]);;

let vEMPTY_UNION = prove
 ((parse_term "!s:A->bool. !t. (s UNION t = EMPTY) <=> (s = EMPTY) /\\ (t = EMPTY)"),
  vSET_TAC[]);;

let vUNION_SUBSET = prove
 ((parse_term "!s t u. (s UNION t) SUBSET u <=> s SUBSET u /\\ t SUBSET u"),
  vSET_TAC[]);;

let vUNION_RESTRICT = prove
 ((parse_term "!P s t.\n        {x | x IN (s UNION t) /\\ P x} =\n        {x | x IN s /\\ P x} UNION {x | x IN t /\\ P x}"),
  vSET_TAC[]);;

let vFORALL_SUBSET_UNION = prove
 ((parse_term "!t u:A->bool.\n        (!s. s SUBSET t UNION u ==> P s) <=>\n        (!t' u'. t' SUBSET t /\\ u' SUBSET u ==> P(t' UNION u'))"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vREPEAT vSTRIP_TAC ----> vFIRST_X_ASSUM vMATCH_MP_TAC ----> vASM vSET_TAC[];
    vDISCH_TAC ----> vX_GEN_TAC (parse_term "s:A->bool") ----> vDISCH_TAC ---->
    vFIRST_ASSUM(vMP_TAC -| vSPECL [(parse_term "s INTER t:A->bool"); (parse_term "s INTER u:A->bool")]) ---->
    vANTS_TAC ++--> [vALL_TAC; vMATCH_MP_TAC vEQ_IMP ----> vAP_TERM_TAC] ---->
    vASM vSET_TAC[]]);;

let vEXISTS_SUBSET_UNION = prove
 ((parse_term "!t u:A->bool.\n        (?s. s SUBSET t UNION u /\\ P s) <=>\n        (?t' u'. t' SUBSET t /\\ u' SUBSET u /\\ P(t' UNION u'))"),
  vREWRITE_TAC[vMESON[] (parse_term "(?x. P x /\\ Q x) <=> ~(!x. P x ==> ~Q x)")] ---->
  vREWRITE_TAC[vFORALL_SUBSET_UNION] ----> vMESON_TAC[]);;

let vFORALL_SUBSET_INSERT = prove
 ((parse_term "!a:A t. (!s. s SUBSET a INSERT t ==> P s) <=>\n           (!s. s SUBSET t ==> P s /\\ P (a INSERT s))"),
  vREPEAT vGEN_TAC ---->
  vONCE_REWRITE_TAC[vSET_RULE (parse_term "a INSERT s = {a} UNION s")] ---->
  vREWRITE_TAC[vFORALL_SUBSET_UNION; vSET_RULE
   (parse_term "s SUBSET {a} <=> s = {} \\/ s = {a}")] ---->
  vMESON_TAC[vUNION_EMPTY]);;

let vEXISTS_SUBSET_INSERT = prove
 ((parse_term "!a:A t. (?s. s SUBSET a INSERT t /\\ P s) <=>\n           (?s. s SUBSET t /\\ (P s \\/ P (a INSERT s)))"),
  vREWRITE_TAC[vMESON[] (parse_term "(?x. P x /\\ Q x) <=> ~(!x. P x ==> ~Q x)")] ---->
  vREWRITE_TAC[vFORALL_SUBSET_INSERT] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Intersection.                                                             *)
(* ------------------------------------------------------------------------- *)

let vINTER_ASSOC = prove
 ((parse_term "!(s:A->bool) t u. (s INTER t) INTER u = s INTER (t INTER u)"),
  vSET_TAC[]);;

let vINTER_IDEMPOT = prove
 ((parse_term "!s:A->bool. s INTER s = s"),
  vSET_TAC[]);;

let vINTER_COMM = prove
 ((parse_term "!(s:A->bool) t. s INTER t = t INTER s"),
  vSET_TAC[]);;

let vINTER_SUBSET = prove
 ((parse_term "(!s:A->bool. !t. (s INTER t) SUBSET s) /\\\n   (!s:A->bool. !t. (t INTER s) SUBSET s)"),
  vSET_TAC[]);;

let vSUBSET_INTER_ABSORPTION = prove
 ((parse_term "!s:A->bool. !t. s SUBSET t <=> (s INTER t = s)"),
  vSET_TAC[]);;

let vINTER_EMPTY = prove
 ((parse_term "(!s:A->bool. EMPTY INTER s = EMPTY) /\\\n   (!s:A->bool. s INTER EMPTY = EMPTY)"),
  vSET_TAC[]);;

let vINTER_UNIV = prove
 ((parse_term "(!s:A->bool. UNIV INTER s = s) /\\\n   (!s:A->bool. s INTER UNIV = s)"),
  vSET_TAC[]);;

let vSUBSET_INTER = prove
 ((parse_term "!s t u. s SUBSET (t INTER u) <=> s SUBSET t /\\ s SUBSET u"),
  vSET_TAC[]);;

let vINTER_RESTRICT = prove
 ((parse_term "!P s t.\n        {x | x IN (s INTER t) /\\ P x} =\n        {x | x IN s /\\ P x} INTER {x | x IN t /\\ P x}"),
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Distributivity.                                                           *)
(* ------------------------------------------------------------------------- *)

let vUNION_OVER_INTER = prove
 ((parse_term "!s:A->bool. !t u. s INTER (t UNION u) = (s INTER t) UNION (s INTER u)"),
  vSET_TAC[]);;

let vINTER_OVER_UNION = prove
 ((parse_term "!s:A->bool. !t u. s UNION (t INTER u) = (s UNION t) INTER (s UNION u)"),
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Disjoint sets.                                                            *)
(* ------------------------------------------------------------------------- *)

let vIN_DISJOINT = prove
 ((parse_term "!s:A->bool. !t. DISJOINT s t <=> ~(?x. x IN s /\\ x IN t)"),
  vSET_TAC[]);;

let vDISJOINT_SYM = prove
 ((parse_term "!s:A->bool. !t. DISJOINT s t <=> DISJOINT t s"),
  vSET_TAC[]);;

let vDISJOINT_EMPTY = prove
 ((parse_term "!s:A->bool. DISJOINT EMPTY s /\\ DISJOINT s EMPTY"),
  vSET_TAC[]);;

let vDISJOINT_EMPTY_REFL = prove
 ((parse_term "!s:A->bool. (s = EMPTY) <=> (DISJOINT s s)"),
  vSET_TAC[]);;

let vDISJOINT_UNION = prove
 ((parse_term "!s:A->bool. !t u. DISJOINT (s UNION t) u <=> DISJOINT s u /\\ DISJOINT t u"),
  vSET_TAC[]);;

let vDISJOINT_SING = prove
 ((parse_term "(!s a:A. DISJOINT s {a} <=> ~(a IN s)) /\\\n   (!s a:A. DISJOINT {a} s <=> ~(a IN s))"),
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set difference.                                                           *)
(* ------------------------------------------------------------------------- *)

let vDIFF_EMPTY = prove
 ((parse_term "!s:A->bool. s DIFF EMPTY = s"),
  vSET_TAC[]);;

let vEMPTY_DIFF = prove
 ((parse_term "!s:A->bool. EMPTY DIFF s = EMPTY"),
  vSET_TAC[]);;

let vDIFF_UNIV = prove
 ((parse_term "!s:A->bool. s DIFF UNIV = EMPTY"),
  vSET_TAC[]);;

let vDIFF_DIFF = prove
 ((parse_term "!s:A->bool. !t. (s DIFF t) DIFF t = s DIFF t"),
  vSET_TAC[]);;

let vDIFF_EQ_EMPTY = prove
 ((parse_term "!s:A->bool. s DIFF s = EMPTY"),
  vSET_TAC[]);;

let vSUBSET_DIFF = prove
 ((parse_term "!s t. (s DIFF t) SUBSET s"),
  vSET_TAC[]);;

let vCOMPL_COMPL = prove
 ((parse_term "!s. (:A) DIFF ((:A) DIFF s) = s"),
  vSET_TAC[]);;

let vDIFF_RESTRICT = prove
 ((parse_term "!P s t.\n        {x | x IN (s DIFF t) /\\ P x} =\n        {x | x IN s /\\ P x} DIFF {x | x IN t /\\ P x}"),
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Insertion and deletion.                                                   *)
(* ------------------------------------------------------------------------- *)

let vCOMPONENT = prove
 ((parse_term "!x:A. !s. x IN (x INSERT s)"),
  vSET_TAC[]);;

let vDECOMPOSITION = prove
 ((parse_term "!s:A->bool. !x. x IN s <=> ?t. (s = x INSERT t) /\\ ~(x IN t)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vSTRIP_TAC ---->
  vASM_REWRITE_TAC[vIN_INSERT] ----> vEXISTS_TAC (parse_term "s DELETE x:A") ---->
  vPOP_ASSUM vMP_TAC ----> vSET_TAC[]);;

let vSET_CASES = prove
 ((parse_term "!s:A->bool. (s = EMPTY) \\/ ?x:A. ?t. (s = x INSERT t) /\\ ~(x IN t)"),
  vMESON_TAC[vMEMBER_NOT_EMPTY; vDECOMPOSITION]);;

let vABSORPTION = prove
 ((parse_term "!x:A. !s. x IN s <=> (x INSERT s = s)"),
  vSET_TAC[]);;

let vINSERT_INSERT = prove
 ((parse_term "!x:A. !s. x INSERT (x INSERT s) = x INSERT s"),
  vSET_TAC[]);;

let vINSERT_COMM = prove
 ((parse_term "!x:A. !y s. x INSERT (y INSERT s) = y INSERT (x INSERT s)"),
  vSET_TAC[]);;

let vINSERT_UNIV = prove
 ((parse_term "!x:A. x INSERT UNIV = UNIV"),
  vSET_TAC[]);;

let vNOT_INSERT_EMPTY = prove
 ((parse_term "!x:A. !s. ~(x INSERT s = EMPTY)"),
  vSET_TAC[]);;

let vNOT_EMPTY_INSERT = prove
 ((parse_term "!x:A. !s. ~(EMPTY = x INSERT s)"),
  vSET_TAC[]);;

let vINSERT_UNION = prove
 ((parse_term "!x:A. !s t. (x INSERT s) UNION t =\n               if x IN t then s UNION t else x INSERT (s UNION t)"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vPOP_ASSUM vMP_TAC ----> vSET_TAC[]);;

let vINSERT_UNION_EQ = prove
 ((parse_term "!x:A. !s t. (x INSERT s) UNION t = x INSERT (s UNION t)"),
  vSET_TAC[]);;

let vINSERT_INTER = prove
 ((parse_term "!x:A. !s t. (x INSERT s) INTER t =\n               if x IN t then x INSERT (s INTER t) else s INTER t"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vPOP_ASSUM vMP_TAC ----> vSET_TAC[]);;

let vDISJOINT_INSERT = prove
 ((parse_term "!(x:A) s t. DISJOINT (x INSERT s) t <=> (DISJOINT s t) /\\ ~(x IN t)"),
  vSET_TAC[]);;

let vINSERT_SUBSET = prove
 ((parse_term "!x:A. !s t. (x INSERT s) SUBSET t <=> (x IN t /\\ s SUBSET t)"),
  vSET_TAC[]);;

let vSUBSET_INSERT = prove
 ((parse_term "!x:A. !s. ~(x IN s) ==> !t. s SUBSET (x INSERT t) <=> s SUBSET t"),
  vSET_TAC[]);;

let vINSERT_DIFF = prove
 ((parse_term "!s t. !x:A. (x INSERT s) DIFF t =\n               if x IN t then s DIFF t else x INSERT (s DIFF t)"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vPOP_ASSUM vMP_TAC ----> vSET_TAC[]);;

let vINSERT_AC = prove
 ((parse_term "(x INSERT (y INSERT s) = y INSERT (x INSERT s)) /\\\n   (x INSERT (x INSERT s) = x INSERT s)"),
  vREWRITE_TAC[vINSERT_COMM; vINSERT_INSERT]);;

let vINTER_ACI = prove
 ((parse_term "(p INTER q = q INTER p) /\\\n   ((p INTER q) INTER r = p INTER q INTER r) /\\\n   (p INTER q INTER r = q INTER p INTER r) /\\\n   (p INTER p = p) /\\\n   (p INTER p INTER q = p INTER q)"),
  vSET_TAC[]);;

let vUNION_ACI = prove
 ((parse_term "(p UNION q = q UNION p) /\\\n   ((p UNION q) UNION r = p UNION q UNION r) /\\\n   (p UNION q UNION r = q UNION p UNION r) /\\\n   (p UNION p = p) /\\\n   (p UNION p UNION q = p UNION q)"),
  vSET_TAC[]);;

let vDELETE_NON_ELEMENT = prove
 ((parse_term "!x:A. !s. ~(x IN s) <=> (s DELETE x = s)"),
  vSET_TAC[]);;

let vIN_DELETE_EQ = prove
 ((parse_term "!s x. !x':A.\n     (x IN s <=> x' IN s) <=> (x IN (s DELETE x') <=> x' IN (s DELETE x))"),
  vSET_TAC[]);;

let vEMPTY_DELETE = prove
 ((parse_term "!x:A. EMPTY DELETE x = EMPTY"),
  vSET_TAC[]);;

let vDELETE_DELETE = prove
 ((parse_term "!x:A. !s. (s DELETE x) DELETE x = s DELETE x"),
  vSET_TAC[]);;

let vDELETE_COMM = prove
 ((parse_term "!x:A. !y. !s. (s DELETE x) DELETE y = (s DELETE y) DELETE x"),
  vSET_TAC[]);;

let vDELETE_SUBSET = prove
 ((parse_term "!x:A. !s. (s DELETE x) SUBSET s"),
  vSET_TAC[]);;

let vSUBSET_DELETE = prove
 ((parse_term "!x:A. !s t. s SUBSET (t DELETE x) <=> ~(x IN s) /\\ (s SUBSET t)"),
  vSET_TAC[]);;

let vSUBSET_INSERT_DELETE = prove
 ((parse_term "!x:A. !s t. s SUBSET (x INSERT t) <=> ((s DELETE x) SUBSET t)"),
  vSET_TAC[]);;

let vDIFF_INSERT = prove
 ((parse_term "!s t. !x:A. s DIFF (x INSERT t) = (s DELETE x) DIFF t"),
  vSET_TAC[]);;

let vPSUBSET_INSERT_SUBSET = prove
 ((parse_term "!s t. s PSUBSET t <=> ?x:A. ~(x IN s) /\\ (x INSERT s) SUBSET t"),
  vSET_TAC[]);;

let vDELETE_INSERT = prove
 ((parse_term "!x:A. !y s.\n      (x INSERT s) DELETE y =\n        if x = y then s DELETE y else x INSERT (s DELETE y)"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vPOP_ASSUM vMP_TAC ----> vSET_TAC[]);;

let vINSERT_DELETE = prove
 ((parse_term "!x:A. !s. x IN s ==> (x INSERT (s DELETE x) = s)"),
  vSET_TAC[]);;

let vDELETE_INTER = prove
 ((parse_term "!s t. !x:A. (s DELETE x) INTER t = (s INTER t) DELETE x"),
  vSET_TAC[]);;

let vDISJOINT_DELETE_SYM = prove
 ((parse_term "!s t. !x:A. DISJOINT (s DELETE x) t = DISJOINT (t DELETE x) s"),
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Multiple union.                                                           *)
(* ------------------------------------------------------------------------- *)

let vUNIONS_0 = prove
 ((parse_term "UNIONS {} = {}"),
  vSET_TAC[]);;

let vUNIONS_1 = prove
 ((parse_term "UNIONS {s} = s"),
  vSET_TAC[]);;

let vUNIONS_2 = prove
 ((parse_term "UNIONS {s,t} = s UNION t"),
  vSET_TAC[]);;

let vUNIONS_INSERT = prove
 ((parse_term "UNIONS (s INSERT u) = s UNION (UNIONS u)"),
  vSET_TAC[]);;

let vFORALL_IN_UNIONS = prove
 ((parse_term "!P s. (!x. x IN UNIONS s ==> P x) <=> !t x. t IN s /\\ x IN t ==> P x"),
  vSET_TAC[]);;

let vEXISTS_IN_UNIONS = prove
 ((parse_term "!P s. (?x. x IN UNIONS s /\\ P x) <=> (?t x. t IN s /\\ x IN t /\\ P x)"),
  vSET_TAC[]);;

let vEMPTY_UNIONS = prove
 ((parse_term "!s. (UNIONS s = {}) <=> !t. t IN s ==> t = {}"),
  vSET_TAC[]);;

let vINTER_UNIONS = prove
 ((parse_term "(!s t. UNIONS s INTER t = UNIONS {x INTER t | x IN s}) /\\\n   (!s t. t INTER UNIONS s = UNIONS {t INTER x | x IN s})"),
  vONCE_REWRITE_TAC[vEXTENSION] ---->
  vREWRITE_TAC[vIN_UNIONS; vIN_ELIM_THM; vIN_INTER] ---->
  vMESON_TAC[vIN_INTER]);;

let vUNIONS_SUBSET = prove
 ((parse_term "!f t. UNIONS f SUBSET t <=> !s. s IN f ==> s SUBSET t"),
  vSET_TAC[]);;

let vSUBSET_UNIONS = prove
 ((parse_term "!f g. f SUBSET g ==> UNIONS f SUBSET UNIONS g"),
  vSET_TAC[]);;

let vUNIONS_UNION = prove
 ((parse_term "!s t. UNIONS(s UNION t) = (UNIONS s) UNION (UNIONS t)"),
  vSET_TAC[]);;

let vINTERS_UNION = prove
 ((parse_term "!s t. INTERS (s UNION t) = INTERS s INTER INTERS t"),
  vSET_TAC[]);;

let vUNIONS_MONO = prove
 ((parse_term "(!x. x IN s ==> ?y. y IN t /\\ x SUBSET y) ==> UNIONS s SUBSET UNIONS t"),
  vSET_TAC[]);;

let vUNIONS_MONO_IMAGE = prove
 ((parse_term "(!x. x IN s ==> f x SUBSET g x)\n   ==> UNIONS(IMAGE f s) SUBSET UNIONS(IMAGE g s)"),
  vSET_TAC[]);;

let vUNIONS_UNIV = prove
 ((parse_term "UNIONS (:A->bool) = (:A)"),
  vREWRITE_TAC[vEXTENSION; vIN_UNIONS; vIN_UNIV] ---->
  vMESON_TAC[vIN_SING]);;

let vUNIONS_INSERT_EMPTY = prove
 ((parse_term "!s. UNIONS({} INSERT s) = UNIONS s"),
  vONCE_REWRITE_TAC[vEXTENSION] ---->
  vREWRITE_TAC[vIN_UNIONS; vIN_INSERT] ----> vMESON_TAC[vNOT_IN_EMPTY]);;

let vUNIONS_DELETE_EMPTY = prove
 ((parse_term "!s. UNIONS(s DELETE {}) = UNIONS s"),
  vONCE_REWRITE_TAC[vEXTENSION] ---->
  vREWRITE_TAC[vIN_UNIONS; vIN_DELETE] ----> vMESON_TAC[vNOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Multiple intersection.                                                    *)
(* ------------------------------------------------------------------------- *)

let vINTERS_0 = prove
 ((parse_term "INTERS {} = (:A)"),
  vSET_TAC[]);;

let vINTERS_1 = prove
 ((parse_term "INTERS {s} = s"),
  vSET_TAC[]);;

let vINTERS_2 = prove
 ((parse_term "INTERS {s,t} = s INTER t"),
  vSET_TAC[]);;

let vINTERS_INSERT = prove
 ((parse_term "INTERS (s INSERT u) = s INTER (INTERS u)"),
  vSET_TAC[]);;

let vSUBSET_INTERS = prove
 ((parse_term "!s f. s SUBSET INTERS f <=> (!t. t IN f ==> s SUBSET t)"),
  vSET_TAC[]);;

let vINTERS_SUBSET = prove
 ((parse_term "!u s:A->bool.\n    ~(u = {}) /\\ (!t. t IN u ==> t SUBSET s) ==> INTERS u SUBSET s"),
  vSET_TAC[]);;

let vINTERS_SUBSET_STRONG = prove
 ((parse_term "!u s:A->bool. (?t. t IN u /\\ t SUBSET s) ==> INTERS u SUBSET s"),
  vSET_TAC[]);;

let vINTERS_ANTIMONO = prove
 ((parse_term "!f g. g SUBSET f ==> INTERS f SUBSET INTERS g"),
  vSET_TAC[]);;

let vINTERS_EQ_UNIV = prove
 ((parse_term "!f. INTERS f = (:A) <=> !s. s IN f ==> s = (:A)"),
  vSET_TAC[]);;

let vINTERS_ANTIMONO_GEN = prove
 ((parse_term "!s t. (!y. y IN t ==> ?x. x IN s /\\ x SUBSET y)\n         ==> INTERS s SUBSET INTERS t"),
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Image.                                                                    *)
(* ------------------------------------------------------------------------- *)

let vIMAGE_CLAUSES = prove
 ((parse_term "(IMAGE f {} = {}) /\\\n   (IMAGE f (x INSERT s) = (f x) INSERT (IMAGE f s))"),
  vREWRITE_TAC[vIMAGE; vIN_ELIM_THM; vNOT_IN_EMPTY; vIN_INSERT; vEXTENSION] ---->
  vMESON_TAC[]);;

let vIMAGE_UNION = prove
 ((parse_term "!f s t. IMAGE f (s UNION t) = (IMAGE f s) UNION (IMAGE f t)"),
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vIN_UNION] ----> vMESON_TAC[]);;

let vIMAGE_ID = prove
 ((parse_term "!s. IMAGE (\\x. x) s = s"),
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vUNWIND_THM1]);;

let vIMAGE_I = prove
 ((parse_term "!s. IMAGE I s = s"),
  vREWRITE_TAC[vI_DEF; vIMAGE_ID]);;

let vIMAGE_o = prove
 ((parse_term "!f g s. IMAGE (f o g) s = IMAGE f (IMAGE g s)"),
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; o_THM] ----> vMESON_TAC[]);;

let vIMAGE_SUBSET = prove
 ((parse_term "!f s t. s SUBSET t ==> (IMAGE f s) SUBSET (IMAGE f t)"),
  vREWRITE_TAC[vSUBSET; vIN_IMAGE] ----> vMESON_TAC[]);;

let vIMAGE_INTER_INJ = prove
 ((parse_term "!f s t. (!x y. (f(x) = f(y)) ==> (x = y))\n           ==> (IMAGE f (s INTER t) = (IMAGE f s) INTER (IMAGE f t))"),
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vIN_INTER] ----> vMESON_TAC[]);;

let vIMAGE_DIFF_INJ = prove
 ((parse_term "!f:A->B s t.\n        (!x y. x IN s /\\ y IN t /\\ f x = f y ==> x = y)\n        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t"),
  vSET_TAC[]);;

let vIMAGE_DIFF_INJ_ALT = prove
 ((parse_term "!f:A->B s t.\n        (!x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y) /\\ t SUBSET s\n        ==> IMAGE f (s DIFF t) = IMAGE f s DIFF IMAGE f t"),
  vSET_TAC[]);;

let vIMAGE_DELETE_INJ = prove
 ((parse_term "!f:A->B s a.\n        (!x. x IN s /\\ f x = f a ==> x = a)\n        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a"),
  vSET_TAC[]);;

let vIMAGE_DELETE_INJ_ALT = prove
 ((parse_term "!f:A->B s a.\n        (!x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y) /\\ a IN s\n        ==> IMAGE f (s DELETE a) = IMAGE f s DELETE f a"),
  vSET_TAC[]);;

let vIMAGE_EQ_EMPTY = prove
 ((parse_term "!f s. (IMAGE f s = {}) <=> (s = {})"),
  vREWRITE_TAC[vEXTENSION; vNOT_IN_EMPTY; vIN_IMAGE] ----> vMESON_TAC[]);;

let vFORALL_IN_IMAGE = prove
 ((parse_term "!f s. (!y. y IN IMAGE f s ==> P y) <=> (!x. x IN s ==> P(f x))"),
  vREWRITE_TAC[vIN_IMAGE] ----> vMESON_TAC[]);;

let vEXISTS_IN_IMAGE = prove
 ((parse_term "!f s. (?y. y IN IMAGE f s /\\ P y) <=> ?x. x IN s /\\ P(f x)"),
  vREWRITE_TAC[vIN_IMAGE] ----> vMESON_TAC[]);;

let vFORALL_IN_IMAGE_2 = prove
 ((parse_term "!f P s. (!x y. x IN IMAGE f s /\\ y IN IMAGE f s ==> P x y) <=>\n           (!x y. x IN s /\\ y IN s ==> P (f x) (f y))"),
  vSET_TAC[]);;

let vIMAGE_CONST = prove
 ((parse_term "!s c. IMAGE (\\x. c) s = if s = {} then {} else {c}"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vIMAGE_CLAUSES] ---->
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vIN_SING] ---->
  vASM_MESON_TAC[vMEMBER_NOT_EMPTY]);;

let vSIMPLE_IMAGE = prove
 ((parse_term "!f s. {f x | x IN s} = IMAGE f s"),
  vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vIN_IMAGE] ----> vMESON_TAC[]);;

let vSIMPLE_IMAGE_GEN = prove
 ((parse_term "!f P. {f x | P x} = IMAGE f {x | P x}"),
  vSET_TAC[]);;

let vIMAGE_UNIONS = prove
 ((parse_term "!f s. IMAGE f (UNIONS s) = UNIONS (IMAGE (IMAGE f) s)"),
  vONCE_REWRITE_TAC[vEXTENSION] ----> vREWRITE_TAC[vIN_UNIONS; vIN_IMAGE] ---->
  vREWRITE_TAC[vLEFT_AND_EXISTS_THM] ---->
  vONCE_REWRITE_TAC[vSWAP_EXISTS_THM] ---->
  vREWRITE_TAC[vGSYM vCONJ_ASSOC; vUNWIND_THM2; vIN_IMAGE] ---->
  vMESON_TAC[]);;

let vFUN_IN_IMAGE = prove
 ((parse_term "!f s x. x IN s ==> f(x) IN IMAGE f s"),
  vSET_TAC[]);;

let vSURJECTIVE_IMAGE_EQ = prove
 ((parse_term "!s t. (!y. y IN t ==> ?x. f x = y) /\\ (!x. (f x) IN t <=> x IN s)\n         ==> IMAGE f s = t"),
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Misc lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let vEMPTY_GSPEC = prove
 ((parse_term "{x | F} = {}"),
  vSET_TAC[]);;

let vUNIV_GSPEC = prove
 ((parse_term "{x | T} = UNIV"),
  vSET_TAC[]);;

let vSING_GSPEC = prove
 ((parse_term "(!a. {x | x = a} = {a}) /\\\n   (!a. {x | a = x} = {a})"),
  vSET_TAC[]);;

let vIN_GSPEC = prove
 ((parse_term "!s:A->bool. {x | x IN s} = s"),
  vSET_TAC[]);;

let vIN_ELIM_PAIR_THM = prove
 ((parse_term "!P a b. (a,b) IN {(x,y) | P x y} <=> P a b"),
  vREWRITE_TAC[vIN_ELIM_THM] ----> vMESON_TAC[vPAIR_EQ]);;

let vIN_ELIM_TRIPLE_THM = prove
 ((parse_term "(!P a b c. (a,b,c) IN {(x,y,z) | P x y z} <=> P a b c) /\\\n   (!P a b c. ((a,b),c) IN {((x,y),z) | P x y z} <=> P a b c)"),
  vREWRITE_TAC[vIN_ELIM_THM; vPAIR_EQ] ----> vMESON_TAC[]);;

let vIN_ELIM_QUAD_THM = prove
 ((parse_term "(!P a b c d. (a,b,c,d) IN {w,x,y,z | P w x y z} <=> P a b c d) /\\\n   (!P a b c d. ((a,b),(c,d)) IN {(w,x),(y,z) | P w x y z} <=> P a b c d) /\\\n   (!P a b c d. (((a,b),c),d) IN {(((w,x),y),z) | P w x y z} <=> P a b c d)"),
  vREWRITE_TAC[vIN_ELIM_THM; vPAIR_EQ] ----> vMESON_TAC[]);;

let vSET_PAIR_THM = prove
 ((parse_term "!P. {p | P p} = {(a,b) | P(a,b)}"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_ELIM_THM; vIN_ELIM_PAIR_THM]);;

let vFORALL_IN_GSPEC = prove
 ((parse_term "(!P f. (!z. z IN {f x | P x} ==> Q z) <=> (!x. P x ==> Q(f x))) /\\\n   (!P f. (!z. z IN {f x y | P x y} ==> Q z) <=>\n          (!x y. P x y ==> Q(f x y))) /\\\n   (!P f. (!z. z IN {f w x y | P w x y} ==> Q z) <=>\n          (!w x y. P w x y ==> Q(f w x y))) /\\\n   (!P f. (!z. z IN {f v w x y | P v w x y} ==> Q z) <=>\n          (!v w x y. P v w x y ==> Q(f v w x y)))"),
  vSET_TAC[]);;

let vEXISTS_IN_GSPEC = prove
 ((parse_term "(!P f. (?z. z IN {f x | P x} /\\ Q z) <=> (?x. P x /\\ Q(f x))) /\\\n   (!P f. (?z. z IN {f x y | P x y} /\\ Q z) <=>\n          (?x y. P x y /\\ Q(f x y))) /\\\n   (!P f. (?z. z IN {f w x y | P w x y} /\\ Q z) <=>\n          (?w x y. P w x y /\\ Q(f w x y))) /\\\n   (!P f. (?z. z IN {f v w x y | P v w x y} /\\ Q z) <=>\n          (?v w x y. P v w x y /\\ Q(f v w x y)))"),
  vSET_TAC[]);;

let vSET_PROVE_CASES = prove
 ((parse_term "!P:(A->bool)->bool.\n       P {} /\\ (!a s. ~(a IN s) ==> P(a INSERT s))\n       ==> !s. P s"),
  vMESON_TAC[vSET_CASES]);;

let vUNIONS_IMAGE = prove
 ((parse_term "!f s. UNIONS (IMAGE f s) = {y | ?x. x IN s /\\ y IN f x}"),
  vREPEAT vGEN_TAC ---->  vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[vIN_UNIONS; vIN_IMAGE; vIN_ELIM_THM] ----> vMESON_TAC[]);;

let vINTERS_IMAGE = prove
 ((parse_term "!f s. INTERS (IMAGE f s) = {y | !x. x IN s ==> y IN f x}"),
  vREPEAT vGEN_TAC ---->  vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[vIN_INTERS; vIN_IMAGE; vIN_ELIM_THM] ----> vMESON_TAC[]);;

let vUNIONS_GSPEC = prove
 ((parse_term "(!P f. UNIONS {f x | P x} = {a | ?x. P x /\\ a IN (f x)}) /\\\n   (!P f. UNIONS {f x y | P x y} = {a | ?x y. P x y /\\ a IN (f x y)}) /\\\n   (!P f. UNIONS {f x y z | P x y z} =\n            {a | ?x y z. P x y z /\\ a IN (f x y z)})"),
  vREPEAT vSTRIP_TAC ----> vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[vIN_UNIONS; vIN_ELIM_THM] ----> vMESON_TAC[]);;

let vINTERS_GSPEC = prove
 ((parse_term "(!P f. INTERS {f x | P x} = {a | !x. P x ==> a IN (f x)}) /\\\n   (!P f. INTERS {f x y | P x y} = {a | !x y. P x y ==> a IN (f x y)}) /\\\n   (!P f. INTERS {f x y z | P x y z} =\n                {a | !x y z. P x y z ==> a IN (f x y z)})"),
  vREPEAT vSTRIP_TAC ----> vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[vIN_INTERS; vIN_ELIM_THM] ----> vMESON_TAC[]);;

let vUNIONS_SINGS_GEN = prove
 ((parse_term "!P:A->bool. UNIONS {{x} | P x} = {x | P x}"),
  vREWRITE_TAC[vUNIONS_GSPEC] ----> vSET_TAC[]);;

let vUNIONS_SINGS = prove
 ((parse_term "!s:A->bool. UNIONS {{x} | x IN s} = s"),
  vREWRITE_TAC[vUNIONS_GSPEC] ----> vSET_TAC[]);;

let vIMAGE_INTERS = prove
 ((parse_term "!f s. ~(s = {}) /\\\n         (!x y. x IN UNIONS s /\\ y IN UNIONS s /\\ f x = f y ==> x = y)\n         ==> IMAGE f (INTERS s) = INTERS(IMAGE (IMAGE f) s)"),
  vREWRITE_TAC[vINTERS_IMAGE] ----> vSET_TAC[]);;

let vDIFF_INTERS = prove
 ((parse_term "!u s. u DIFF INTERS s = UNIONS {u DIFF t | t IN s}"),
  vREWRITE_TAC[vUNIONS_GSPEC] ----> vSET_TAC[]);;

let vINTERS_UNIONS = prove
 ((parse_term "!s. INTERS s = UNIV DIFF (UNIONS {UNIV DIFF t | t IN s})"),
  vREWRITE_TAC[vGSYM vDIFF_INTERS] ----> vSET_TAC[]);;

let vUNIONS_INTERS = prove
 ((parse_term "!s. UNIONS s = UNIV DIFF (INTERS {UNIV DIFF t | t IN s})"),
  vGEN_TAC ----> vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[vIN_UNIONS; vIN_UNIV; vIN_DIFF; vINTERS_GSPEC; vIN_ELIM_THM] ---->
  vMESON_TAC[]);;

let vUNIONS_DIFF = prove
 ((parse_term "!s t. UNIONS s DIFF t = UNIONS {x DIFF t | x IN s}"),
  vREWRITE_TAC[vUNIONS_GSPEC] ----> vSET_TAC[]);;

let vDIFF_UNIONS = prove
 ((parse_term "!u s. u DIFF UNIONS s = u INTER INTERS {u DIFF t | t IN s}"),
  vREWRITE_TAC[vINTERS_GSPEC] ----> vSET_TAC[]);;

let vDIFF_UNIONS_NONEMPTY = prove
 ((parse_term "!u s. ~(s = {}) ==> u DIFF UNIONS s = INTERS {u DIFF t | t IN s}"),
  vREWRITE_TAC[vINTERS_GSPEC] ----> vSET_TAC[]);;

let vINTERS_OVER_UNIONS = prove
 ((parse_term "!f:A->(B->bool)->bool s.\n        INTERS { UNIONS(f x) | x IN s} =\n        UNIONS { INTERS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[vSIMPLE_IMAGE; vINTERS_IMAGE; vUNIONS_IMAGE; vUNIONS_GSPEC] ---->
  vREWRITE_TAC[vIN_UNIONS; vIN_ELIM_THM] ---->
  vX_GEN_TAC (parse_term "b:B") ----> vREWRITE_TAC[vRIGHT_IMP_EXISTS_THM; vSKOLEM_THM] ---->
  vMESON_TAC[]);;

let vINTER_INTERS = prove
 ((parse_term "(!f s:A->bool. s INTER INTERS f =\n           if f = {} then s else INTERS {s INTER t | t IN f}) /\\\n   (!f s:A->bool. INTERS f INTER s =\n           if f = {} then s else INTERS {t INTER s | t IN f})"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vINTERS_0; vINTER_UNIV; vINTERS_GSPEC] ---->
  vASM vSET_TAC[]);;

let vUNIONS_OVER_INTERS = prove
 ((parse_term "!f:A->(B->bool)->bool s.\n        UNIONS { INTERS(f x) | x IN s} =\n        INTERS { UNIONS {g x | x IN s} |g| !x. x IN s ==> g x IN f x}"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[vSIMPLE_IMAGE; vINTERS_IMAGE; vUNIONS_IMAGE; vINTERS_GSPEC] ---->
  vREWRITE_TAC[vIN_INTERS; vIN_ELIM_THM] ---->
  vGEN_TAC ----> vONCE_REWRITE_TAC[vTAUT (parse_term "(p <=> q) <=> (~p <=> ~q)")] ---->
  vREWRITE_TAC[vNOT_FORALL_THM; vNOT_IMP; vNOT_EXISTS_THM] ---->
  vREWRITE_TAC[vAND_FORALL_THM; vGSYM vSKOLEM_THM] ----> vMESON_TAC[]);;

let vIMAGE_INTERS_SUBSET = prove
 ((parse_term "!(f:A->B) g. IMAGE f (INTERS g) SUBSET INTERS (IMAGE (IMAGE f) g)"),
  vREWRITE_TAC[vINTERS_IMAGE] ----> vSET_TAC[]);;

let vIMAGE_INTER_SUBSET = prove
 ((parse_term "!f s t. IMAGE f (s INTER t) SUBSET IMAGE f s INTER IMAGE f t"),
  vSET_TAC[]);;

let vIMAGE_INTER_SATURATED_GEN = prove
 ((parse_term "!f:A->B s t u.\n        {x | x IN u /\\ f(x) IN IMAGE f s} SUBSET s /\\ t SUBSET u \\/\n        {x | x IN u /\\ f(x) IN IMAGE f t} SUBSET t /\\ s SUBSET u\n        ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t"),
  vSET_TAC[]);;

let vIMAGE_INTERS_SATURATED_GEN = prove
 ((parse_term "!f:A->B g s u.\n        ~(g = {}) /\\\n        (!t. t IN g ==> t SUBSET u) /\\\n        (!t. t IN g DELETE s ==> {x | x IN u /\\ f(x) IN IMAGE f t} SUBSET t)\n        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)"),
  let lemma = prove
   ((parse_term "~(g = {}) /\\\n     (!t. t IN g ==> t SUBSET u /\\ {x | x IN u /\\ f(x) IN IMAGE f t} SUBSET t)\n     ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)"),
    vONCE_REWRITE_TAC[vEXTENSION] ---->
    vREWRITE_TAC[vINTERS_IMAGE; vIN_INTERS; vIN_IMAGE] ---->
    vREWRITE_TAC[vLEFT_IMP_EXISTS_THM; vIN_ELIM_THM; vNOT_IN_EMPTY] ---->
    vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
    vREWRITE_TAC[vIMP_CONJ; vFORALL_UNWIND_THM2] ----> vSET_TAC[]) in
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "(s:A->bool) IN g") ---->
  vASM_SIMP_TAC[vSET_RULE (parse_term "~(s IN g) ==> g DELETE s = g")] ++-->
   [vALL_TAC; vMESON_TAC[lemma]] ---->
  vREWRITE_TAC[vCONJ_ASSOC] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vFIRST_X_ASSUM(vSUBST1_TAC -| vMATCH_MP (vSET_RULE
   (parse_term "x IN s ==> s = x INSERT (s DELETE x)"))) ---->
  vREWRITE_TAC[vFORALL_IN_INSERT; vNOT_INSERT_EMPTY] ---->
  vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "g DELETE (s:A->bool) = {}") ---->
  vASM_REWRITE_TAC[vIMAGE_CLAUSES; vINTERS_0; vINTERS_1] ---->
  vREWRITE_TAC[vIMAGE_CLAUSES; vINTERS_INSERT] ---->
  vMATCH_MP_TAC(vSET_RULE
   (parse_term "IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t /\\\n    IMAGE f t = u ==> IMAGE f (s INTER t) = IMAGE f s INTER u")) ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vIMAGE_INTER_SATURATED_GEN ---->
    vEXISTS_TAC (parse_term "u:A->bool") ----> vASM vSET_TAC[];
    vMATCH_MP_TAC lemma ----> vASM vSET_TAC[]]);;

let vIMAGE_INTER_SATURATED = prove
 ((parse_term "!f:A->B s t.\n        {x | f(x) IN IMAGE f s} SUBSET s \\/ {x | f(x) IN IMAGE f t} SUBSET t\n         ==> IMAGE f (s INTER t) = IMAGE f s INTER IMAGE f t"),
  vSET_TAC[]);;

let vIMAGE_INTERS_SATURATED = prove
 ((parse_term "!f:A->B g s.\n        ~(g = {}) /\\ (!t. t IN g DELETE s ==> {x | f(x) IN IMAGE f t} SUBSET t)\n        ==> IMAGE f (INTERS g) = INTERS (IMAGE (IMAGE f) g)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vIMAGE_INTERS_SATURATED_GEN ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "s:A->bool"); (parse_term "(:A)")] ---->
  vASM_REWRITE_TAC[vIN_UNIV; vSUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Stronger form of induction is sometimes handy.                            *)
(* ------------------------------------------------------------------------- *)

let vFINITE_INDUCT_STRONG = prove
 ((parse_term "!P:(A->bool)->bool.\n        P {} /\\ (!x s. P s /\\ ~(x IN s) /\\ FINITE s ==> P(x INSERT s))\n        ==> !s. FINITE s ==> P s"),
  vGEN_TAC ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "!s:A->bool. FINITE s ==> FINITE s /\\ P s") vMP_TAC ++-->
   [vALL_TAC; vMESON_TAC[]] ---->
  vMATCH_MP_TAC vFINITE_INDUCT ----> vASM_SIMP_TAC[vFINITE_RULES] ---->
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[] ----> vASM_CASES_TAC (parse_term "x:A IN s") ++-->
   [vSUBGOAL_THEN (parse_term "x:A INSERT s = s") (fun th -> vASM_REWRITE_TAC[th]) ---->
    vUNDISCH_TAC (parse_term "x:A IN s") ----> vSET_TAC[];
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Useful general properties of functions.                                   *)
(* ------------------------------------------------------------------------- *)

let vINJECTIVE_ON_ALT = prove
 ((parse_term "!P f. (!x y. P x /\\ P y /\\ f x = f y ==> x = y) <=>\n         (!x y. P x /\\ P y ==> (f x = f y <=> x = y))"),
  vMESON_TAC[]);;

let vINJECTIVE_ALT = prove
 ((parse_term "!f. (!x y. f x = f y ==> x = y) <=> (!x y. f x = f y <=> x = y)"),
  vMESON_TAC[]);;

let vSURJECTIVE_ON_RIGHT_INVERSE = prove
 ((parse_term "!f t. (!y. y IN t ==> ?x. x IN s /\\ (f(x) = y)) <=>\n         (?g. !y. y IN t ==> g(y) IN s /\\ (f(g(y)) = y))"),
  vREWRITE_TAC[vRIGHT_IMP_EXISTS_THM; vSKOLEM_THM]);;

let vINJECTIVE_ON_LEFT_INVERSE = prove
 ((parse_term "!f s. (!x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)) <=>\n         (?g. !x. x IN s ==> (g(f(x)) = x))"),
  let lemma = vMESON[]
   (parse_term "(!x. x IN s ==> (g(f(x)) = x)) <=>\n    (!y x. x IN s /\\ (y = f x) ==> (g y = x))") in
  vREWRITE_TAC[lemma; vGSYM vSKOLEM_THM] ----> vMESON_TAC[]);;

let vBIJECTIVE_ON_LEFT_RIGHT_INVERSE = prove
 ((parse_term "!f s t.\n        (!x. x IN s ==> f(x) IN t)\n        ==> ((!x y. x IN s /\\ y IN s /\\ f(x) = f(y) ==> x = y) /\\\n             (!y. y IN t ==> ?x. x IN s /\\ f x = y) <=>\n            ?g. (!y. y IN t ==> g(y) IN s) /\\\n                (!y. y IN t ==> (f(g(y)) = y)) /\\\n                (!x. x IN s ==> (g(f(x)) = x)))"),
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[vINJECTIVE_ON_LEFT_INVERSE; vSURJECTIVE_ON_RIGHT_INVERSE] ---->
  vREWRITE_TAC[vRIGHT_AND_EXISTS_THM] ----> vAP_TERM_TAC ----> vABS_TAC ---->
  vEQ_TAC ----> vASM_MESON_TAC[]);;

let vSURJECTIVE_RIGHT_INVERSE = prove
 ((parse_term "(!y. ?x. f(x) = y) <=> (?g. !y. f(g(y)) = y)"),
  vMESON_TAC[vSURJECTIVE_ON_RIGHT_INVERSE; vIN_UNIV]);;

let vINJECTIVE_LEFT_INVERSE = prove
 ((parse_term "(!x y. (f x = f y) ==> (x = y)) <=> (?g. !x. g(f(x)) = x)"),
  let th = vREWRITE_RULE[vIN_UNIV]
   (vISPECL [(parse_term "f:A->B"); (parse_term "UNIV:A->bool")] vINJECTIVE_ON_LEFT_INVERSE) in
  vREWRITE_TAC[th]);;

let vBIJECTIVE_LEFT_RIGHT_INVERSE = prove
 ((parse_term "!f:A->B.\n       (!x y. f(x) = f(y) ==> x = y) /\\ (!y. ?x. f x = y) <=>\n       ?g. (!y. f(g(y)) = y) /\\ (!x. g(f(x)) = x)"),
  vGEN_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "(:A)"); (parse_term "(:B)")] vBIJECTIVE_ON_LEFT_RIGHT_INVERSE) ---->
  vREWRITE_TAC[vIN_UNIV]);;

let vFUNCTION_FACTORS_LEFT_GEN = prove
 ((parse_term "!P f g. (!x y. P x /\\ P y /\\ g x = g y ==> f x = f y) <=>\n           (?h. !x. P x ==> f(x) = h(g x))"),
  vONCE_REWRITE_TAC[vMESON[]
   (parse_term "(!x. P x ==> f(x) = g(k x)) <=> (!y x. P x /\\ y = k x ==> f x = g y)")] ---->
  vREWRITE_TAC[vGSYM vSKOLEM_THM] ----> vMESON_TAC[]);;

let vFUNCTION_FACTORS_LEFT = prove
 ((parse_term "!f g. (!x y. (g x = g y) ==> (f x = f y)) <=> ?h. f = h o g"),
  vREWRITE_TAC[vFUN_EQ_THM; o_THM;
   vGSYM(vREWRITE_RULE[] (vISPEC (parse_term "\\x. T") vFUNCTION_FACTORS_LEFT_GEN))]);;

let vFUNCTION_FACTORS_RIGHT_GEN = prove
 ((parse_term "!P f g. (!x. P x ==> ?y. g(y) = f(x)) <=>\n           (?h. !x. P x ==> f(x) = g(h x))"),
  vREWRITE_TAC[vGSYM vSKOLEM_THM] ----> vMESON_TAC[]);;

let vFUNCTION_FACTORS_RIGHT = prove
 ((parse_term "!f g. (!x. ?y. g(y) = f(x)) <=> ?h. f = g o h"),
  vREWRITE_TAC[vFUN_EQ_THM; o_THM; vGSYM vSKOLEM_THM] ----> vMESON_TAC[]);;

let vSURJECTIVE_FORALL_THM = prove
 ((parse_term "!f:A->B. (!y. ?x. f x = y) <=> (!P. (!x. P(f x)) <=> (!y. P y))"),
  vGEN_TAC ----> vEQ_TAC ++--> [vMESON_TAC[]; vALL_TAC] ---->
  vDISCH_THEN(fun th -> vONCE_REWRITE_TAC[vGSYM th]) ----> vMESON_TAC[]);;

let vSURJECTIVE_EXISTS_THM = prove
 ((parse_term "!f:A->B. (!y. ?x. f x = y) <=> (!P. (?x. P(f x)) <=> (?y. P y))"),
  vGEN_TAC ----> vEQ_TAC ++--> [vMESON_TAC[]; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "\\y:B. !x:A. ~(f x = y)")) ----> vMESON_TAC[]);;

let vSURJECTIVE_IMAGE_THM = prove
 ((parse_term "!f:A->B. (!y. ?x. f x = y) <=> (!P. IMAGE f {x | P(f x)} = {x | P x})"),
  vGEN_TAC ----> vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vIN_ELIM_THM] ---->
  vEQ_TAC ++--> [vALL_TAC; vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "\\y:B. T"))] ---->
  vMESON_TAC[]);;

let vIMAGE_INJECTIVE_IMAGE_OF_SUBSET = prove
 ((parse_term "!f:A->B s.\n     ?t. t SUBSET s /\\\n         IMAGE f s = IMAGE f t /\\\n         (!x y. x IN t /\\ y IN t /\\ f x = f y ==> x = y)"),
  vREPEAT vGEN_TAC ---->
  vSUBGOAL_THEN
   (parse_term "?g. !y. y IN IMAGE (f:A->B) s ==> g(y) IN s /\\ f(g(y)) = y")
  vSTRIP_ASSUME_TAC ++-->
   [vREWRITE_TAC[vGSYM vSURJECTIVE_ON_RIGHT_INVERSE] ----> vSET_TAC[];
    vEXISTS_TAC (parse_term "IMAGE (g:B->A) (IMAGE (f:A->B) s)") ----> vASM vSET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Basic combining theorems for finite sets.                                 *)
(* ------------------------------------------------------------------------- *)

let vFINITE_EMPTY = prove
 ((parse_term "FINITE {}"),
  vREWRITE_TAC[vFINITE_RULES]);;

let vFINITE_SUBSET = prove
 ((parse_term "!(s:A->bool) t. FINITE t /\\ s SUBSET t ==> FINITE s"),
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vREWRITE_TAC[vIMP_CONJ] ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT ----> vCONJ_TAC ++-->
   [vMESON_TAC[vSUBSET_EMPTY; vFINITE_RULES]; vALL_TAC] ---->
  vX_GEN_TAC (parse_term "x:A") ----> vX_GEN_TAC (parse_term "u:A->bool") ----> vDISCH_TAC ---->
  vX_GEN_TAC (parse_term "t:A->bool") ----> vDISCH_TAC ---->
  vSUBGOAL_THEN (parse_term "FINITE((x:A) INSERT (t DELETE x))") vASSUME_TAC ++-->
   [vMATCH_MP_TAC(vCONJUNCT2 vFINITE_RULES) ---->
    vFIRST_ASSUM vMATCH_MP_TAC ---->
    vUNDISCH_TAC (parse_term "t SUBSET (x:A INSERT u)") ----> vSET_TAC[];
    vASM_CASES_TAC (parse_term "x:A IN t") ++-->
     [vSUBGOAL_THEN (parse_term "x:A INSERT (t DELETE x) = t") vSUBST_ALL_TAC ++-->
       [vUNDISCH_TAC (parse_term "x:A IN t") ----> vSET_TAC[]; vASM_REWRITE_TAC[]];
      vFIRST_ASSUM vMATCH_MP_TAC ---->
      vUNDISCH_TAC (parse_term "t SUBSET x:A INSERT u") ---->
      vUNDISCH_TAC (parse_term "~(x:A IN t)") ----> vSET_TAC[]]]);;

let vFINITE_RESTRICT = prove
 ((parse_term "!s:A->bool P. FINITE s ==> FINITE {x | x IN s /\\ P x}"),
  vMESON_TAC[vSUBSET_RESTRICT; vFINITE_SUBSET]);;

let vFINITE_UNION_IMP = prove
 ((parse_term "!(s:A->bool) t. FINITE s /\\ FINITE t ==> FINITE (s UNION t)"),
  vREWRITE_TAC[vIMP_CONJ] ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT ----> vREWRITE_TAC[vUNION_EMPTY] ---->
  vSUBGOAL_THEN (parse_term "!x s t. (x:A INSERT s) UNION t = x INSERT (s UNION t)")
  (fun th -> vREWRITE_TAC[th]) ++-->
   [vSET_TAC[];
    vMESON_TAC[vFINITE_RULES]]);;

let vFINITE_UNION = prove
 ((parse_term "!(s:A->bool) t. FINITE(s UNION t) <=> FINITE(s) /\\ FINITE(t)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vFINITE_SUBSET ---->
    vEXISTS_TAC (parse_term "(s:A->bool) UNION t") ----> vASM_REWRITE_TAC[] ----> vSET_TAC[];
    vMATCH_ACCEPT_TAC vFINITE_UNION_IMP]);;

let vFINITE_INTER = prove
 ((parse_term "!(s:A->bool) t. FINITE s \\/ FINITE t ==> FINITE (s INTER t)"),
  vMESON_TAC[vINTER_SUBSET; vFINITE_SUBSET]);;

let vFINITE_INSERT = prove
 ((parse_term "!(s:A->bool) x. FINITE (x INSERT s) <=> FINITE s"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vMATCH_MP_TAC vFINITE_SUBSET ---->
    vEXISTS_TAC (parse_term "x:A INSERT s") ----> vASM_REWRITE_TAC[] ----> vSET_TAC[];
    vMATCH_MP_TAC(vCONJUNCT2 vFINITE_RULES) ---->
    vASM_REWRITE_TAC[]]);;

let vFINITE_SING = prove
 ((parse_term "!a. FINITE {a}"),
  vREWRITE_TAC[vFINITE_INSERT; vFINITE_RULES]);;

let vFINITE_DELETE_IMP = prove
 ((parse_term "!(s:A->bool) x. FINITE s ==> FINITE (s DELETE x)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vFINITE_SUBSET ---->
  vASM_REWRITE_TAC[] ----> vASM vSET_TAC[]);;

let vFINITE_DELETE = prove
 ((parse_term "!(s:A->bool) x. FINITE (s DELETE x) <=> FINITE s"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vFINITE_DELETE_IMP] ---->
  vASM_CASES_TAC (parse_term "x:A IN s") ++-->
   [vSUBGOAL_THEN (parse_term "s = x INSERT (s DELETE x:A)")
    (fun th -> vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [th]) ---->
    vREWRITE_TAC[vFINITE_INSERT] ----> vPOP_ASSUM vMP_TAC ----> vSET_TAC[];
    vSUBGOAL_THEN (parse_term "s DELETE x:A = s") (fun th -> vREWRITE_TAC[th]) ---->
    vPOP_ASSUM vMP_TAC ----> vSET_TAC[]]);;

let vFINITE_FINITE_UNIONS = prove
 ((parse_term "!s. FINITE(s) ==> (FINITE(UNIONS s) <=> (!t. t IN s ==> FINITE(t)))"),
  vMATCH_MP_TAC vFINITE_INDUCT ---->
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY; vUNIONS_0; vUNIONS_INSERT] ---->
  vREWRITE_TAC[vFINITE_UNION; vFINITE_RULES] ----> vMESON_TAC[]);;

let vFINITE_IMAGE_EXPAND = prove
 ((parse_term "!(f:A->B) s. FINITE s ==> FINITE {y | ?x. x IN s /\\ (y = f x)}"),
  vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT ---->
  vREWRITE_TAC[vNOT_IN_EMPTY; vREWRITE_RULE[] vEMPTY_GSPEC; vFINITE_RULES] ---->
  vREPEAT vGEN_TAC ---->
  vSUBGOAL_THEN (parse_term "{y | ?z. z IN (x INSERT s) /\\ (y = (f:A->B) z)} =\n                {y | ?z. z IN s /\\ (y = f z)} UNION {(f x)}")
  (fun th -> vREWRITE_TAC[th]) ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vIN_INSERT; vIN_UNION; vNOT_IN_EMPTY] ---->
    vMESON_TAC[];
    vREWRITE_TAC[vFINITE_UNION; vFINITE_INSERT; vFINITE_RULES]]);;

let vFINITE_IMAGE = prove
 ((parse_term "!(f:A->B) s. FINITE s ==> FINITE (IMAGE f s)"),
  vREWRITE_TAC[vIMAGE; vFINITE_IMAGE_EXPAND]);;

let vFINITE_IMAGE_INJ_GENERAL = prove
 ((parse_term "!(f:A->B) A s.\n        (!x y. x IN s /\\ y IN s /\\ f(x) = f(y) ==> x = y) /\\\n        FINITE A\n        ==> FINITE {x | x IN s /\\ f(x) IN A}"),
  vREPEAT vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vINJECTIVE_ON_LEFT_INVERSE]) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "g:B->A")) ---->
  vMATCH_MP_TAC vFINITE_SUBSET ----> vEXISTS_TAC (parse_term "IMAGE (g:B->A) A") ---->
  vASM_SIMP_TAC[vFINITE_IMAGE] ----> vASM vSET_TAC[]);;

let vFINITE_FINITE_PREIMAGE_GENERAL = prove
 ((parse_term "!f:A->B s t.\n        FINITE t /\\\n        (!y. y IN t ==> FINITE {x | x IN s /\\ f(x) = y})\n        ==> FINITE {x | x IN s /\\ f(x) IN t}"),
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN
   (parse_term "{x | x IN s /\\ (f:A->B)(x) IN t} =\n    UNIONS (IMAGE (\\a. {x | x IN s /\\ f x = a}) t)")
  vSUBST1_TAC ++-->
   [vGEN_REWRITE_TAC vI [vEXTENSION] ----> vREWRITE_TAC[vIN_ELIM_THM; vIN_UNIONS] ---->
    vREWRITE_TAC[vEXISTS_IN_IMAGE] ----> vSET_TAC[];
    vASM_SIMP_TAC[vFINITE_FINITE_UNIONS; vFINITE_IMAGE; vFORALL_IN_IMAGE]]);;

let vFINITE_FINITE_PREIMAGE = prove
 ((parse_term "!f:A->B t.\n        FINITE t /\\\n        (!y. y IN t ==> FINITE {x | f(x) = y})\n        ==> FINITE {x | f(x) IN t}"),
  vREPEAT vGEN_TAC ----> vMP_TAC
   (vISPECL [(parse_term "f:A->B"); (parse_term "(:A)"); (parse_term "t:B->bool")] vFINITE_FINITE_PREIMAGE_GENERAL) ---->
  vREWRITE_TAC[vIN_UNIV]);;

let vFINITE_IMAGE_INJ_EQ = prove
 ((parse_term "!(f:A->B) s.\n        (!x y. x IN s /\\ y IN s /\\ f(x) = f(y) ==> x = y)\n        ==> (FINITE(IMAGE f s) <=> FINITE s)"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vASM_SIMP_TAC[vFINITE_IMAGE] ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vIMP_IMP] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vFINITE_IMAGE_INJ_GENERAL) ---->
  vMATCH_MP_TAC vEQ_IMP ----> vAP_TERM_TAC ----> vSET_TAC[]);;

let vFINITE_IMAGE_INJ = prove
 ((parse_term "!(f:A->B) A.\n        (!x y. f(x) = f(y) ==> x = y) /\\ FINITE A\n        ==> FINITE {x | f(x) IN A}"),
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vSPECL [(parse_term "f:A->B"); (parse_term "A:B->bool"); (parse_term "UNIV:A->bool")]
    vFINITE_IMAGE_INJ_GENERAL) ----> vREWRITE_TAC[vIN_UNIV]);;

let vFINITE_IMAGE_GEN = prove
 ((parse_term "!(f:A->B) (g:A->C) s t.\n        IMAGE f s SUBSET t /\\ FINITE t /\\\n        (!x y. x IN s /\\ y IN s /\\ f x = f y ==> g x = g y)\n        ==> FINITE(IMAGE g s)"),
  vREPEAT vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vFUNCTION_FACTORS_LEFT_GEN]) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "h:B->C")) ---->
  vSUBGOAL_THEN (parse_term "IMAGE g s = IMAGE (h:B->C) (IMAGE (f:A->B) s)") vSUBST1_TAC ++-->
   [vASM vSET_TAC[]; vASM_MESON_TAC[vFINITE_IMAGE; vFINITE_SUBSET]]);;

let vINFINITE_IMAGE = prove
 ((parse_term "!f:A->B s.\n        INFINITE s /\\ (!x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y)\n        ==> INFINITE (IMAGE f s)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ_ALT; vINJECTIVE_ON_LEFT_INVERSE] ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "g:B->A")) ---->
  vREWRITE_TAC[vINFINITE; vCONTRAPOS_THM] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN (parse_term "s = IMAGE (g:B->A) (IMAGE f s)") vSUBST1_TAC ++-->
   [vASM vSET_TAC[]; vMATCH_MP_TAC vFINITE_IMAGE ----> vASM_REWRITE_TAC[]]);;

let vINFINITE_IMAGE_INJ = prove
 ((parse_term "!f:A->B. (!x y. (f x = f y) ==> (x = y))\n            ==> !s. INFINITE s ==> INFINITE(IMAGE f s)"),
  vMESON_TAC[vINFINITE_IMAGE]);;

let vINFINITE_NONEMPTY = prove
 ((parse_term "!s. INFINITE(s) ==> ~(s = EMPTY)"),
  vMESON_TAC[vINFINITE; vFINITE_RULES]);;

let vINFINITE_DIFF_FINITE = prove
 ((parse_term "!s:A->bool t. INFINITE(s) /\\ FINITE(t) ==> INFINITE(s DIFF t)"),
  vREPEAT vGEN_TAC ---->
  vMATCH_MP_TAC(vTAUT (parse_term "(b /\\ ~c ==> ~a) ==> a /\\ b ==> c")) ---->
  vREWRITE_TAC[vINFINITE] ----> vSTRIP_TAC ---->
  vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC (parse_term "(t:A->bool) UNION (s DIFF t)") ---->
  vASM_REWRITE_TAC[vFINITE_UNION] ----> vSET_TAC[]);;

let vSUBSET_IMAGE_INJ = prove
 ((parse_term "!f:A->B s t.\n        s SUBSET (IMAGE f t) <=>\n        ?u. u SUBSET t /\\\n            (!x y. x IN u /\\ y IN u ==> (f x = f y <=> x = y)) /\\\n            s = IMAGE f u"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++--> [vALL_TAC; vMESON_TAC[vIMAGE_SUBSET]] ---->
  vDISCH_TAC ----> vFIRST_ASSUM(vMP_TAC -| vMATCH_MP (vSET_RULE
   (parse_term "s SUBSET IMAGE f t ==> !x. x IN s ==> ?y. y IN t /\\ f y = x"))) ---->
  vREWRITE_TAC[vSURJECTIVE_ON_RIGHT_INVERSE] ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "g:B->A")) ---->
  vEXISTS_TAC (parse_term "IMAGE (g:B->A) s") ----> vASM vSET_TAC[]);;

let vSUBSET_IMAGE = prove
 ((parse_term "!f:A->B s t. s SUBSET (IMAGE f t) <=> ?u. u SUBSET t /\\ (s = IMAGE f u)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++--> [vALL_TAC; vMESON_TAC[vIMAGE_SUBSET]] ---->
  vREWRITE_TAC[vSUBSET_IMAGE_INJ] ----> vMATCH_MP_TAC vMONO_EXISTS ----> vSET_TAC[]);;

let vEXISTS_SUBSET_IMAGE = prove
 ((parse_term "!P f s.\n    (?t. t SUBSET IMAGE f s /\\ P t) <=> (?t. t SUBSET s /\\ P (IMAGE f t))"),
  vREWRITE_TAC[vSUBSET_IMAGE] ----> vMESON_TAC[]);;

let vFORALL_SUBSET_IMAGE = prove
 ((parse_term "!P f s. (!t. t SUBSET IMAGE f s ==> P t) <=>\n           (!t. t SUBSET s ==> P(IMAGE f t))"),
  vREWRITE_TAC[vSUBSET_IMAGE] ----> vMESON_TAC[]);;

let vEXISTS_SUBSET_IMAGE_INJ = prove
 ((parse_term "!P f s.\n    (?t. t SUBSET IMAGE f s /\\ P t) <=>\n    (?t. t SUBSET s /\\\n         (!x y. x IN t /\\ y IN t ==> (f x = f y <=> x = y)) /\\\n         P (IMAGE f t))"),
  vREWRITE_TAC[vSUBSET_IMAGE_INJ] ----> vMESON_TAC[]);;

let vFORALL_SUBSET_IMAGE_INJ = prove
 ((parse_term "!P f s. (!t. t SUBSET IMAGE f s ==> P t) <=>\n           (!t. t SUBSET s /\\\n                (!x y. x IN t /\\ y IN t ==> (f x = f y <=> x = y))\n                 ==> P(IMAGE f t))"),
  vREPEAT vGEN_TAC ---->
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(!t. p t) <=> ~(?t. ~p t)")] ---->
  vREWRITE_TAC[vNOT_IMP; vEXISTS_SUBSET_IMAGE_INJ; vGSYM vCONJ_ASSOC]);;

let vEXISTS_FINITE_SUBSET_IMAGE_INJ = prove
 ((parse_term "!P f s.\n    (?t. FINITE t /\\ t SUBSET IMAGE f s /\\ P t) <=>\n    (?t. FINITE t /\\ t SUBSET s /\\\n         (!x y. x IN t /\\ y IN t ==> (f x = f y <=> x = y)) /\\\n         P (IMAGE f t))"),
  vONCE_REWRITE_TAC[vTAUT (parse_term "p /\\ q /\\ r <=> q /\\ p /\\ r")] ---->
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vEXISTS_SUBSET_IMAGE_INJ] ---->
  vAP_TERM_TAC ----> vABS_TAC ----> vMESON_TAC[vFINITE_IMAGE_INJ_EQ]);;

let vFORALL_FINITE_SUBSET_IMAGE_INJ = prove
 ((parse_term "!P f s. (!t. FINITE t /\\ t SUBSET IMAGE f s ==> P t) <=>\n           (!t. FINITE t /\\ t SUBSET s /\\\n                (!x y. x IN t /\\ y IN t ==> (f x = f y <=> x = y))\n                 ==> P(IMAGE f t))"),
  vREPEAT vGEN_TAC ---->
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(!t. p t) <=> ~(?t. ~p t)")] ---->
  vREWRITE_TAC[vNOT_IMP; vEXISTS_FINITE_SUBSET_IMAGE_INJ; vGSYM vCONJ_ASSOC]);;

let vEXISTS_FINITE_SUBSET_IMAGE = prove
 ((parse_term "!P f s.\n    (?t. FINITE t /\\ t SUBSET IMAGE f s /\\ P t) <=>\n    (?t. FINITE t /\\ t SUBSET s /\\ P (IMAGE f t))"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vREWRITE_TAC[vEXISTS_FINITE_SUBSET_IMAGE_INJ] ----> vMESON_TAC[];
    vMESON_TAC[vFINITE_IMAGE; vIMAGE_SUBSET]]);;

let vFORALL_FINITE_SUBSET_IMAGE = prove
 ((parse_term "!P f s. (!t. FINITE t /\\ t SUBSET IMAGE f s ==> P t) <=>\n           (!t. FINITE t /\\ t SUBSET s ==> P(IMAGE f t))"),
  vREPEAT vGEN_TAC ---->
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(!x. P x) <=> ~(?x. ~P x)")] ---->
  vREWRITE_TAC[vNOT_IMP; vGSYM vCONJ_ASSOC; vEXISTS_FINITE_SUBSET_IMAGE]);;

let vFINITE_SUBSET_IMAGE = prove
 ((parse_term "!f:A->B s t.\n        FINITE(t) /\\ t SUBSET (IMAGE f s) <=>\n        ?s'. FINITE s' /\\ s' SUBSET s /\\ (t = IMAGE f s')"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vALL_TAC; vASM_MESON_TAC[vFINITE_IMAGE; vIMAGE_SUBSET]] ---->
  vSPEC_TAC((parse_term "t:B->bool"),(parse_term "t:B->bool")) ---->
  vREWRITE_TAC[vFORALL_FINITE_SUBSET_IMAGE] ----> vMESON_TAC[]);;

let vFINITE_SUBSET_IMAGE_IMP = prove
 ((parse_term "!f:A->B s t.\n        FINITE(t) /\\ t SUBSET (IMAGE f s)\n        ==> ?s'. FINITE s' /\\ s' SUBSET s /\\ t SUBSET (IMAGE f s')"),
  vMESON_TAC[vSUBSET_REFL; vFINITE_SUBSET_IMAGE]);;

let vFINITE_IMAGE_EQ = prove
 ((parse_term "!(f:A->B) s. FINITE(IMAGE f s) <=>\n                ?t. FINITE t /\\ t SUBSET s /\\ IMAGE f s = IMAGE f t"),
  vMESON_TAC[vFINITE_SUBSET_IMAGE; vFINITE_IMAGE; vSUBSET_REFL]);;

let vFINITE_IMAGE_EQ_INJ = prove
 ((parse_term "!(f:A->B) s. FINITE(IMAGE f s) <=>\n                ?t. FINITE t /\\ t SUBSET s /\\ IMAGE f s = IMAGE f t /\\\n                    (!x y. x IN t /\\ y IN t ==> (f x = f y <=> x = y))"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++--> [vALL_TAC; vMESON_TAC[vFINITE_IMAGE]] ---->
  vDISCH_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "IMAGE (f:A->B) s"); (parse_term "s:A->bool")]
        vSUBSET_IMAGE_INJ) ---->
  vREWRITE_TAC[vSUBSET_REFL] ----> vMATCH_MP_TAC vMONO_EXISTS ---->
  vASM_METIS_TAC[vFINITE_IMAGE_INJ_EQ]);;

let vFINITE_DIFF = prove
 ((parse_term "!s t. FINITE s ==> FINITE(s DIFF t)"),
  vMESON_TAC[vFINITE_SUBSET; vSUBSET_DIFF]);;

let vINFINITE_SUPERSET = prove
 ((parse_term "!s t. INFINITE s /\\ s SUBSET t ==> INFINITE t"),
  vREWRITE_TAC[vINFINITE] ----> vMESON_TAC[vFINITE_SUBSET]);;

let vFINITE_TRANSITIVITY_CHAIN = prove
 ((parse_term "!R s:A->bool.\n        FINITE s /\\\n        (!x. ~(R x x)) /\\\n        (!x y z. R x y /\\ R y z ==> R x z) /\\\n        (!x. x IN s ==> ?y. y IN s /\\ R x y)\n        ==> s = {}"),
  vGEN_TAC ----> vONCE_REWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ----> vREWRITE_TAC[vNOT_IN_EMPTY] ---->
  vSET_TAC[]);;

let vUNIONS_MAXIMAL_SETS = prove
 ((parse_term "!f. FINITE f\n       ==> UNIONS {t:A->bool | t IN f /\\ !u. u IN f ==> ~(t PSUBSET u)} =\n           UNIONS f"),
  vSIMP_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET_UNIONS; vSUBSET_RESTRICT] ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vUNIONS_MONO ---->
  vX_GEN_TAC (parse_term "s:A->bool") ----> vDISCH_TAC ----> vREWRITE_TAC[vEXISTS_IN_GSPEC] ---->
  vGEN_REWRITE_TAC vI [vTAUT (parse_term "p <=> ~ ~ p")] ----> vDISCH_TAC ---->
  vMP_TAC(vISPECL [(parse_term "\\t u:A->bool. s SUBSET t /\\ t PSUBSET u");
    (parse_term "{t:A->bool | t IN f /\\ s SUBSET t}")]vFINITE_TRANSITIVITY_CHAIN) ---->
  vASM_SIMP_TAC[vNOT_IMP; vFINITE_RESTRICT; vFORALL_IN_GSPEC; vEXISTS_IN_GSPEC] ---->
  vREPEAT vCONJ_TAC ++--> [vSET_TAC[]; vSET_TAC[]; vALL_TAC; vASM vSET_TAC[]] ---->
  vASM_MESON_TAC[vPSUBSET_TRANS; vSUBSET_PSUBSET_TRANS; vPSUBSET]);;

let vFINITE_SUBSET_UNIONS = prove
 ((parse_term "!f s:A->bool.\n        FINITE s /\\ s SUBSET UNIONS f\n        ==> ?f'. FINITE f' /\\ f' SUBSET f /\\ s SUBSET UNIONS f'"),
  vREPEAT vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vSUBSET]) ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vTOP_DEPTH_CONV)
   [vIN_UNIONS; vRIGHT_IMP_EXISTS_THM] ---->
  vREWRITE_TAC[vSKOLEM_THM; vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC (parse_term "u:A->A->bool") ----> vDISCH_TAC ---->
  vEXISTS_TAC (parse_term "IMAGE (u:A->A->bool) s") ---->
  vASM_SIMP_TAC[vFINITE_IMAGE; vUNIONS_IMAGE] ----> vASM vSET_TAC[]);;

let vUNIONS_IN_CHAIN = prove
 ((parse_term "!f:(A->bool)->bool.\n        FINITE f /\\ ~(f = {}) /\\\n        (!s t. s IN f /\\ t IN f ==> s SUBSET t \\/ t SUBSET s)\n        ==> UNIONS f IN f"),
  vREWRITE_TAC[vIMP_CONJ] ----> vMATCH_MP_TAC vFINITE_INDUCT ---->
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM; vFORALL_IN_INSERT; vUNIONS_INSERT] ---->
  vREWRITE_TAC[vFORALL_AND_THM; vTAUT (parse_term "p ==> q /\\ r <=> (p ==> q) /\\ (p ==> r)");
              vNOT_INSERT_EMPTY] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "s:A->bool"); (parse_term "f:(A->bool)->bool")] ---->
  vASM_CASES_TAC (parse_term "f:(A->bool)->bool = {}") ---->
  vASM_REWRITE_TAC[vUNIONS_0; vIN_INSERT; vUNION_EMPTY] ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC(vMESON[]
   (parse_term "s UNION t = s \\/ s UNION t = t\n    ==> t IN f ==> s UNION t = s \\/ s UNION t IN f")) ---->
  vASM vSET_TAC[]);;

let vINTERS_IN_CHAIN = prove
 ((parse_term "!f:(A->bool)->bool.\n        FINITE f /\\ ~(f = {}) /\\\n        (!s t. s IN f /\\ t IN f ==> s SUBSET t \\/ t SUBSET s)\n        ==> INTERS f IN f"),
  vREWRITE_TAC[vIMP_CONJ] ----> vMATCH_MP_TAC vFINITE_INDUCT ---->
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM; vFORALL_IN_INSERT; vINTERS_INSERT] ---->
  vREWRITE_TAC[vFORALL_AND_THM; vTAUT (parse_term "p ==> q /\\ r <=> (p ==> q) /\\ (p ==> r)");
              vNOT_INSERT_EMPTY] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "s:A->bool"); (parse_term "f:(A->bool)->bool")] ---->
  vASM_CASES_TAC (parse_term "f:(A->bool)->bool = {}") ---->
  vASM_REWRITE_TAC[vINTERS_0; vIN_INSERT; vINTER_UNIV] ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC(vMESON[]
   (parse_term "s INTER t = s \\/ s INTER t = t\n    ==> t IN f ==> s INTER t = s \\/ s INTER t IN f")) ---->
  vASM vSET_TAC[]);;

let vFINITE_SUBSET_UNIONS_CHAIN = prove
 ((parse_term "!f s:A->bool.\n        FINITE s /\\ s SUBSET UNIONS f /\\ ~(f = {}) /\\\n        (!t u. t IN f /\\ u IN f ==> t SUBSET u \\/ u SUBSET t)\n        ==> ?t. t IN f /\\ s SUBSET t"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:(A->bool)->bool"); (parse_term "s:A->bool")]
        vFINITE_SUBSET_UNIONS) ---->
  vASM_REWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC (parse_term "t:(A->bool)->bool") ---->
  vASM_CASES_TAC (parse_term "t:(A->bool)->bool = {}") ++-->
   [vASM_SIMP_TAC[vUNIONS_0] ----> vASM vSET_TAC[]; vSTRIP_TAC] ---->
  vEXISTS_TAC (parse_term "UNIONS t:A->bool") ---->
  vASM_REWRITE_TAC[] ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vREWRITE_RULE[vSUBSET]) ---->
  vMATCH_MP_TAC vUNIONS_IN_CHAIN ----> vASM vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Recursion over finite sets; based on Ching-Tsun's code (archive 713).     *)
(* ------------------------------------------------------------------------- *)

let vFINREC = new_recursive_definition num_RECURSION
  (parse_term "(FINREC (f:A->B->B) b s a 0 <=> (s = {}) /\\ (a = b)) /\\\n   (FINREC (f:A->B->B) b s a (SUC n) <=>\n                ?x c. x IN s /\\\n                      FINREC f b (s DELETE x) c n  /\\\n                      (a = f x c))");;

let vFINREC_1_LEMMA = prove
 ((parse_term "!f b s a. FINREC f b s a (SUC 0) <=> ?x. (s = {x}) /\\ (a = f x b)"),
  vREWRITE_TAC[vFINREC] ---->
  vREPEAT vGEN_TAC ----> vAP_TERM_TAC ----> vABS_TAC ----> vSET_TAC[]);;

let vFINREC_SUC_LEMMA = prove
 ((parse_term "!(f:A->B->B) b.\n         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))\n         ==> !n s z.\n                FINREC f b s z (SUC n)\n                ==> !x. x IN s ==> ?w. FINREC f b (s DELETE x) w n /\\\n                                       (z = f x w)"),
  let lem = prove((parse_term "s DELETE (x:A) DELETE y = s DELETE y DELETE x"),vSET_TAC[]) in
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vINDUCT_TAC ++-->
   [vREWRITE_TAC[vFINREC_1_LEMMA] ----> vREWRITE_TAC[vFINREC] ---->
    vREPEAT vGEN_TAC ----> vSTRIP_TAC ----> vSTRIP_TAC ---->
    vASM_REWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ---->
    vDISCH_THEN vSUBST1_TAC ----> vEXISTS_TAC (parse_term "b:B") ---->
    vASM_REWRITE_TAC[] ----> vSET_TAC[];
    vREPEAT vGEN_TAC ---->
    vGEN_REWRITE_TAC vLAND_CONV [vFINREC] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "y:A") vMP_TAC) ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "c:B") vSTRIP_ASSUME_TAC) ---->
    vX_GEN_TAC (parse_term "x:A") ----> vDISCH_TAC ---->
    vASM_CASES_TAC (parse_term "x:A = y") ----> vASM_REWRITE_TAC[] ++-->
     [vEXISTS_TAC (parse_term "c:B") ----> vASM_REWRITE_TAC[];
      vUNDISCH_TAC (parse_term "FINREC (f:A->B->B) b (s DELETE y) c (SUC n)") ---->
      vDISCH_THEN(vANTE_RES_THEN (vMP_TAC -| vSPEC (parse_term "x:A"))) ---->
      vASM_REWRITE_TAC[vIN_DELETE] ---->
      vDISCH_THEN(vX_CHOOSE_THEN (parse_term "v:B") vSTRIP_ASSUME_TAC) ---->
      vEXISTS_TAC (parse_term "(f:A->B->B) y v") ----> vASM_REWRITE_TAC[vFINREC] ---->
      vCONJ_TAC ++-->
       [vMAP_EVERY vEXISTS_TAC [(parse_term "y:A"); (parse_term "v:B")] ---->
        vONCE_REWRITE_TAC[lem] ----> vASM_REWRITE_TAC[vIN_DELETE];
        vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]]]);;

let vFINREC_UNIQUE_LEMMA = prove
 ((parse_term "!(f:A->B->B) b.\n         (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))\n         ==> !n1 n2 s a1 a2.\n                FINREC f b s a1 n1 /\\ FINREC f b s a2 n2\n                ==> (a1 = a2) /\\ (n1 = n2)"),
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vINDUCT_TAC ----> vINDUCT_TAC ++-->
   [vREWRITE_TAC[vFINREC] ----> vMESON_TAC[vNOT_IN_EMPTY];
    vREWRITE_TAC[vFINREC] ----> vMESON_TAC[vNOT_IN_EMPTY];
    vREWRITE_TAC[vFINREC] ----> vMESON_TAC[vNOT_IN_EMPTY];
    vIMP_RES_THEN vASSUME_TAC vFINREC_SUC_LEMMA ----> vREPEAT vGEN_TAC ---->
    vDISCH_THEN(fun th -> vMP_TAC(vCONJUNCT1 th) ----> vMP_TAC th) ---->
    vDISCH_THEN(vCONJUNCTS_THEN (vANTE_RES_THEN vASSUME_TAC)) ---->
    vREWRITE_TAC[vFINREC] ----> vSTRIP_TAC ----> vASM_MESON_TAC[]]);;

let vFINREC_EXISTS_LEMMA = prove
 ((parse_term "!(f:A->B->B) b s. FINITE s ==> ?a n. FINREC f b s a n"),
  let lem = prove((parse_term "~(x IN s ) ==> ((x:A INSERT s) DELETE x = s)"),vSET_TAC[]) in
  vGEN_TAC ----> vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREPEAT vSTRIP_TAC ++-->
   [vMAP_EVERY vEXISTS_TAC [(parse_term "b:B"); (parse_term "0")] ----> vREWRITE_TAC[vFINREC];
    vMAP_EVERY vEXISTS_TAC [(parse_term "(f:A->B->B) x a"); (parse_term "SUC n")] ---->
    vREWRITE_TAC[vFINREC] ----> vMAP_EVERY vEXISTS_TAC [(parse_term "x:A"); (parse_term "a:B")] ---->
    vFIRST_ASSUM(fun th -> vASM_REWRITE_TAC[vMATCH_MP lem th; vIN_INSERT])]);;

let vFINREC_FUN_LEMMA = prove
 ((parse_term "!P (R:A->B->C->bool).\n       (!s. P s ==> ?a n. R s a n) /\\\n       (!n1 n2 s a1 a2. R s a1 n1 /\\ R s a2 n2 ==> (a1 = a2) /\\ (n1 = n2))\n       ==> ?f. !s a. P s ==> ((?n. R s a n) <=> (f s = a))"),
  vREPEAT vSTRIP_TAC ----> vEXISTS_TAC (parse_term "\\s:A. @a:B. ?n:C. R s a n") ---->
  vREPEAT vSTRIP_TAC ----> vBETA_TAC ----> vEQ_TAC ++-->
   [vSTRIP_TAC ----> vMATCH_MP_TAC vSELECT_UNIQUE ----> vASM_MESON_TAC[];
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vCONV_TAC vSELECT_CONV ---->
    vASM_MESON_TAC[]]);;

let vFINREC_FUN = prove
 ((parse_term "!(f:A->B->B) b.\n        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))\n        ==> ?g. (g {} = b) /\\\n                !s x. FINITE s /\\ x IN s\n                      ==> (g s = f x (g (s DELETE x)))"),
  vREPEAT vSTRIP_TAC ----> vIMP_RES_THEN vMP_TAC vFINREC_UNIQUE_LEMMA ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "b:B")) ----> vDISCH_THEN
   (vMP_TAC -| vCONJ (vSPECL [(parse_term "f:A->B->B"); (parse_term "b:B")] vFINREC_EXISTS_LEMMA)) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vFINREC_FUN_LEMMA) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "g:(A->bool)->B")) ---->
  vEXISTS_TAC (parse_term "g:(A->bool)->B") ----> vCONJ_TAC ++-->
   [vSUBGOAL_THEN (parse_term "FINITE(EMPTY:A->bool)")
    (vANTE_RES_THEN (fun th -> vGEN_REWRITE_TAC vI [vGSYM th])) ++-->
     [vREWRITE_TAC[vFINITE_RULES];
      vEXISTS_TAC (parse_term "0") ----> vREWRITE_TAC[vFINREC]];
    vREPEAT vSTRIP_TAC ---->
    vANTE_RES_THEN vMP_TAC (vASSUME (parse_term "FINITE(s:A->bool)")) ---->
    vDISCH_THEN(vASSUME_TAC -| vGSYM) ----> vASM_REWRITE_TAC[] ---->
    vFIRST_ASSUM(vMP_TAC -| vSPEC (parse_term "(g:(A->bool)->B) s")) ---->
    vREWRITE_TAC[] ----> vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
    vINDUCT_TAC ++-->
     [vASM_REWRITE_TAC[vFINREC] ----> vDISCH_TAC ----> vUNDISCH_TAC (parse_term "x:A IN s") ---->
      vASM_REWRITE_TAC[vNOT_IN_EMPTY];
      vIMP_RES_THEN vASSUME_TAC vFINREC_SUC_LEMMA ---->
      vDISCH_THEN(vANTE_RES_THEN (vMP_TAC -| vSPEC (parse_term "x:A"))) ---->
      vASM_REWRITE_TAC[] ---->
      vDISCH_THEN(vX_CHOOSE_THEN (parse_term "w:B") (vCONJUNCTS_THEN vASSUME_TAC)) ---->
      vSUBGOAL_THEN (parse_term "(g (s DELETE x:A) = w:B)") vSUBST1_TAC ++-->
       [vSUBGOAL_THEN (parse_term "FINITE(s DELETE x:A)") vMP_TAC ++-->
         [vMATCH_MP_TAC vFINITE_SUBSET ----> vEXISTS_TAC (parse_term "s:A->bool") ---->
          vASM_REWRITE_TAC[] ----> vSET_TAC[];
          vDISCH_THEN(vANTE_RES_THEN (vMP_TAC -| vGSYM)) ---->
          vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
          vEXISTS_TAC (parse_term "n:num") ----> vASM_REWRITE_TAC[]];
        vASM_REWRITE_TAC[]]]]);;

let vSET_RECURSION_LEMMA = prove
 ((parse_term "!(f:A->B->B) b.\n        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))\n        ==> ?g. (g {} = b) /\\\n                !x s. FINITE s\n                      ==> (g (x INSERT s) =\n                                if x IN s then g s else f x (g s))"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "b:B") -| vMATCH_MP vFINREC_FUN) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "g:(A->bool)->B") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "g:(A->bool)->B") ----> vASM_REWRITE_TAC[] ---->
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
  vDISCH_TAC ++-->
   [vAP_TERM_TAC ----> vREWRITE_TAC[vGSYM vABSORPTION] ----> vASM_REWRITE_TAC[];
    vSUBGOAL_THEN (parse_term "FINITE(x:A INSERT s) /\\ x IN (x INSERT s)") vMP_TAC ++-->
     [vREWRITE_TAC[vIN_INSERT] ----> vASM_MESON_TAC[vFINITE_RULES];
      vDISCH_THEN(vANTE_RES_THEN vSUBST1_TAC) ---->
      vREPEAT vAP_TERM_TAC ----> vUNDISCH_TAC (parse_term "~(x:A IN s)") ----> vSET_TAC[]]]);;

let vITSET = new_definition
  (parse_term "ITSET f s b =\n        (@g. (g {} = b) /\\\n             !x s. FINITE s\n                   ==> (g (x INSERT s) = if x IN s then g s else f x (g s)))\n        s");;

let vFINITE_RECURSION = prove
 ((parse_term "!(f:A->B->B) b.\n        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))\n        ==> (ITSET f {} b = b) /\\\n            !x s. FINITE s\n                  ==> (ITSET f (x INSERT s) b =\n                       if x IN s then ITSET f s b\n                                 else f x (ITSET f s b))"),
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vITSET] ---->
  vCONV_TAC vSELECT_CONV ----> vMATCH_MP_TAC vSET_RECURSION_LEMMA ---->
  vASM_REWRITE_TAC[]);;

let vFINITE_RECURSION_DELETE = prove
 ((parse_term "!(f:A->B->B) b.\n        (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s)))\n        ==> (ITSET f {} b = b) /\\\n            !x s. FINITE s\n                  ==> (ITSET f s b =\n                       if x IN s then f x (ITSET f (s DELETE x) b)\n                                 else ITSET f (s DELETE x) b)"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vFINITE_RECURSION) ---->
  vDISCH_THEN(vSTRIP_ASSUME_TAC -| vSPEC (parse_term "b:B")) ----> vASM_REWRITE_TAC[] ---->
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "x:A IN s") ----> vASM_REWRITE_TAC[] ++-->
   [vDISCH_THEN(vMP_TAC -| vMATCH_MP vFINITE_DELETE_IMP) ---->
    vDISCH_THEN(vANTE_RES_THEN vMP_TAC -| vSPEC (parse_term "x:A")) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "x:A")) ---->
    vREWRITE_TAC[vIN_DELETE] ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ----> vUNDISCH_TAC (parse_term "x:A IN s") ----> vSET_TAC[];
    vDISCH_TAC ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vUNDISCH_TAC (parse_term "~(x:A IN s)") ----> vSET_TAC[]]);;

let vITSET_EQ = prove
 ((parse_term "!s f g b. FINITE(s) /\\ (!x. x IN s ==> (f x = g x)) /\\\n             (!x y s. ~(x = y) ==> (f x (f y s) = f y (f x s))) /\\\n             (!x y s. ~(x = y) ==> (g x (g y s) = g y (g x s)))\n             ==> (ITSET f s b = ITSET g s b)"),
  vONCE_REWRITE_TAC[vIMP_CONJ] ---->
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vFINITE_RECURSION; vNOT_IN_EMPTY; vIN_INSERT] ---->
  vREPEAT vSTRIP_TAC ----> vAP_TERM_TAC ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vREWRITE_RULE[vRIGHT_IMP_FORALL_THM]) ---->
  vASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality.                                                              *)
(* ------------------------------------------------------------------------- *)

let vCARD = new_definition
 (parse_term "CARD s = ITSET (\\x n. SUC n) s 0");;

let vCARD_CLAUSES = prove
 ((parse_term "(CARD ({}:A->bool) = 0) /\\\n   (!(x:A) s. FINITE s ==>\n                 (CARD (x INSERT s) =\n                      if x IN s then CARD s else SUC(CARD s)))"),
  vMP_TAC(vISPECL [(parse_term "\\(x:A) n. SUC n"); (parse_term "0")] vFINITE_RECURSION) ---->
  vREWRITE_TAC[vCARD]);;

let vCARD_UNION = prove
 ((parse_term "!(s:A->bool) t. FINITE(s) /\\ FINITE(t) /\\ (s INTER t = EMPTY)\n         ==> (CARD (s UNION t) = CARD s + CARD t)"),
  vREWRITE_TAC[vTAUT (parse_term "a /\\ b /\\ c ==> d <=> a ==> b /\\ c ==> d")] ---->
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vUNION_EMPTY; vCARD_CLAUSES; vINTER_EMPTY; vADD_CLAUSES] ---->
  vX_GEN_TAC (parse_term "x:A") ----> vX_GEN_TAC (parse_term "s:A->bool") ----> vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "(x:A INSERT s) UNION t = x INSERT (s UNION t)")
  vSUBST1_TAC ++--> [vSET_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN (parse_term "FINITE ((s:A->bool) UNION t) /\\ FINITE s")
  vSTRIP_ASSUME_TAC ++-->
   [vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vFINITE_UNION_IMP ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vMP_TAC(vISPECL [(parse_term "x:A"); (parse_term "s:A->bool")] (vCONJUNCT2 vCARD_CLAUSES)) ---->
  vMP_TAC(vISPECL [(parse_term "x:A"); (parse_term "s:A->bool UNION t")] (vCONJUNCT2 vCARD_CLAUSES)) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vSUBGOAL_THEN (parse_term "~(x:A IN (s UNION t))") vASSUME_TAC ++-->
   [vASM_REWRITE_TAC[vIN_UNION] ---->
    vUNDISCH_TAC (parse_term "(x:A INSERT s) INTER t = EMPTY") ---->
    vREWRITE_TAC[vEXTENSION; vIN_INSERT; vIN_INTER; vNOT_IN_EMPTY] ---->
    vMESON_TAC[];
    vASM_REWRITE_TAC[vSUC_INJ; vADD_CLAUSES] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
    vUNDISCH_TAC (parse_term "x:A INSERT s INTER t = EMPTY") ----> vSET_TAC[]]);;

let vCARD_DELETE = prove
 ((parse_term "!x:A s. FINITE(s)\n           ==> (CARD(s DELETE x) = if x IN s then CARD(s) - 1 else CARD(s))"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ++-->
   [vSUBGOAL_THEN (parse_term "s = x:A INSERT (s DELETE x)")
     (fun th -> vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [th])
    ++--> [vUNDISCH_TAC (parse_term "x:A IN s") ----> vSET_TAC[]; vALL_TAC] ---->
    vASM_SIMP_TAC[vCARD_CLAUSES; vFINITE_DELETE; vIN_DELETE; vSUC_SUB1];
    vAP_TERM_TAC ----> vUNDISCH_TAC (parse_term "~(x:A IN s)") ----> vSET_TAC[]]);;

let vCARD_UNION_EQ = prove
 ((parse_term "!s t u. FINITE u /\\ (s INTER t = {}) /\\ (s UNION t = u)\n           ==> (CARD s + CARD t = CARD u)"),
  vMESON_TAC[vCARD_UNION; vFINITE_SUBSET; vSUBSET_UNION]);;

let vCARD_DIFF = prove
 ((parse_term "!s t. FINITE s /\\ t SUBSET s ==> CARD(s DIFF t) = CARD s - CARD t"),
  vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC(vARITH_RULE (parse_term "a + b:num = c ==> a = c - b")) ---->
  vMATCH_MP_TAC vCARD_UNION_EQ ----> vASM_SIMP_TAC[] ----> vASM vSET_TAC[]);;

let vCARD_EQ_0 = prove
 ((parse_term "!s. FINITE s ==> ((CARD s = 0) <=> (s = {}))"),
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vCARD_CLAUSES; vNOT_INSERT_EMPTY; vNOT_SUC]);;

let vCARD_SING = prove
 ((parse_term "!a:A. CARD {a} = 1"),
  vSIMP_TAC[vCARD_CLAUSES; vFINITE_INSERT; vFINITE_EMPTY; vNOT_IN_EMPTY; vARITH]);;

(* ------------------------------------------------------------------------- *)
(* A stronger still form of induction where we get to choose the element.    *)
(* ------------------------------------------------------------------------- *)

let vFINITE_INDUCT_DELETE = prove
 ((parse_term "!P. P {} /\\\n       (!s. FINITE s /\\ ~(s = {}) ==> ?x. x IN s /\\ (P(s DELETE x) ==> P s))\n       ==> !s:A->bool. FINITE s ==> P s"),
  vGEN_TAC ----> vSTRIP_TAC ----> vGEN_TAC ----> vWF_INDUCT_TAC (parse_term "CARD(s:A->bool)") ---->
  vASM_CASES_TAC (parse_term "s:A->bool = {}") ----> vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vUNDISCH_TAC
   (parse_term "!s. FINITE s /\\ ~(s = {}) ==> ?x:A. x IN s /\\ (P(s DELETE x) ==> P s)") ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "s:A->bool")) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "x:A") (vCONJUNCTS_THEN2 vASSUME_TAC vMATCH_MP_TAC)) ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "s DELETE (x:A)")) ---->
  vASM_SIMP_TAC[vFINITE_DELETE; vCARD_DELETE; vCARD_EQ_0;
               vARITH_RULE (parse_term "n - 1 < n <=> ~(n = 0)")]);;

(* ------------------------------------------------------------------------- *)
(* Relational form is often more useful.                                     *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE = new_definition
  (parse_term "s HAS_SIZE n <=> FINITE s /\\ (CARD s = n)");;

let vHAS_SIZE_CARD = prove
 ((parse_term "!s n. s HAS_SIZE n ==> (CARD s = n)"),
  vSIMP_TAC[vHAS_SIZE]);;

let vHAS_SIZE_0 = prove
 ((parse_term "!(s:A->bool). s HAS_SIZE 0 <=> (s = {})"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vHAS_SIZE] ---->
  vEQ_TAC ----> vDISCH_TAC ---->
  vASM_REWRITE_TAC[vFINITE_RULES; vCARD_CLAUSES] ---->
  vFIRST_ASSUM(vMP_TAC -| vCONJUNCT2) ---->
  vFIRST_ASSUM(vMP_TAC -| vCONJUNCT1) ---->
  vSPEC_TAC((parse_term "s:A->bool"),(parse_term "s:A->bool")) ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vNOT_INSERT_EMPTY] ---->
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP (vCONJUNCT2 vCARD_CLAUSES) th]) ---->
  vASM_REWRITE_TAC[vNOT_SUC]);;

let vHAS_SIZE_SUC = prove
 ((parse_term "!(s:A->bool) n. s HAS_SIZE (SUC n) <=>\n                   ~(s = {}) /\\ !a. a IN s ==> (s DELETE a) HAS_SIZE n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vHAS_SIZE] ---->
  vASM_CASES_TAC (parse_term "s:A->bool = {}") ---->
  vASM_REWRITE_TAC[vCARD_CLAUSES; vFINITE_RULES; vNOT_IN_EMPTY; vNOT_SUC] ---->
  vREWRITE_TAC[vFINITE_DELETE] ---->
  vASM_CASES_TAC (parse_term "FINITE(s:A->bool)") ---->
  vASM_REWRITE_TAC[vNOT_FORALL_THM; vMEMBER_NOT_EMPTY] ---->
  vEQ_TAC ----> vREPEAT vSTRIP_TAC ++-->
   [vMP_TAC(vISPECL [(parse_term "a:A"); (parse_term "s DELETE a:A")] (vCONJUNCT2 vCARD_CLAUSES)) ---->
    vASM_REWRITE_TAC[vFINITE_DELETE; vIN_DELETE] ---->
    vSUBGOAL_THEN (parse_term "a INSERT (s DELETE a:A) = s") vSUBST1_TAC ++-->
     [vUNDISCH_TAC (parse_term "a:A IN s") ----> vSET_TAC[];
      vASM_REWRITE_TAC[vSUC_INJ] ----> vMESON_TAC[]];
    vFIRST_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vGSYM vMEMBER_NOT_EMPTY]) ---->
    vDISCH_THEN(vX_CHOOSE_TAC (parse_term "a:A")) ---->
    vMP_TAC(vISPECL [(parse_term "a:A"); (parse_term "s DELETE a:A")] (vCONJUNCT2 vCARD_CLAUSES)) ---->
    vASM_REWRITE_TAC[vFINITE_DELETE; vIN_DELETE] ---->
    vSUBGOAL_THEN (parse_term "a INSERT (s DELETE a:A) = s") vSUBST1_TAC ++-->
     [vUNDISCH_TAC (parse_term "a:A IN s") ----> vSET_TAC[];
      vASM_MESON_TAC[]]]);;

let vHAS_SIZE_UNION = prove
 ((parse_term "!s t m n. s HAS_SIZE m /\\ t HAS_SIZE n /\\ DISJOINT s t\n             ==> (s UNION t) HAS_SIZE (m + n)"),
  vSIMP_TAC[vHAS_SIZE; vFINITE_UNION; vDISJOINT; vCARD_UNION]);;

let vHAS_SIZE_DIFF = prove
 ((parse_term "!s t m n. s HAS_SIZE m /\\ t HAS_SIZE n /\\ t SUBSET s\n             ==> (s DIFF t) HAS_SIZE (m - n)"),
  vSIMP_TAC[vHAS_SIZE; vFINITE_DIFF; vCARD_DIFF]);;

let vHAS_SIZE_UNIONS = prove
 ((parse_term "!s t:A->B->bool m n.\n        s HAS_SIZE m /\\\n        (!x. x IN s ==> t(x) HAS_SIZE n) /\\\n        (!x y. x IN s /\\ y IN s /\\ ~(x = y) ==> DISJOINT (t x) (t y))\n        ==> UNIONS {t(x) | x IN s} HAS_SIZE (m * n)"),
  vGEN_REWRITE_TAC (funpow 4 vBINDER_CONV -| funpow 2 vLAND_CONV) [vHAS_SIZE] ---->
  vREWRITE_TAC[vGSYM vCONJ_ASSOC] ---->
  vONCE_REWRITE_TAC[vIMP_CONJ] ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ----> vCONJ_TAC ++-->
   [vREPEAT vGEN_TAC ----> vREWRITE_TAC[vCARD_CLAUSES] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 (vSUBST1_TAC -| vSYM) (vK vALL_TAC)) ---->
    vREWRITE_TAC[vMULT_CLAUSES; vHAS_SIZE_0; vEMPTY_UNIONS] ---->
    vREWRITE_TAC[vIN_ELIM_THM; vNOT_IN_EMPTY];
    vALL_TAC] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "s:A->bool")] ----> vSTRIP_TAC ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "t:A->B->bool"); (parse_term "m:num"); (parse_term "n:num")] ---->
  vASM_SIMP_TAC[vCARD_CLAUSES] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vSUBST1_TAC -| vSYM) vSTRIP_ASSUME_TAC) ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "UNIONS {t y | y IN x INSERT s} = t x UNION UNIONS {t y | y IN s}")] ---->
  vREWRITE_TAC[vARITH_RULE (parse_term "SUC a * b = b + a * b")] ---->
  vMATCH_MP_TAC vHAS_SIZE_UNION ----> vASM_SIMP_TAC[vIN_INSERT] ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "DISJOINT a (UNIONS s) <=> !x. x IN s ==> DISJOINT a x")] ---->
  vASM_SIMP_TAC[vIN_ELIM_THM; vLEFT_IMP_EXISTS_THM] ---->
  vASM_MESON_TAC[vIN_INSERT]);;

let vFINITE_HAS_SIZE = prove
 ((parse_term "!s. FINITE s <=> s HAS_SIZE CARD s"),
  vREWRITE_TAC[vHAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* This is often more useful as a rewrite.                                   *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_CLAUSES = prove
 ((parse_term "(s HAS_SIZE 0 <=> (s = {})) /\\\n   (s HAS_SIZE (SUC n) <=>\n        ?a t. t HAS_SIZE n /\\ ~(a IN t) /\\ (s = a INSERT t))"),
  let lemma = vSET_RULE (parse_term "a IN s ==> (s = a INSERT (s DELETE a))") in
  vREWRITE_TAC[vHAS_SIZE_0] ----> vREPEAT vSTRIP_TAC ----> vEQ_TAC ++-->
   [vREWRITE_TAC[vHAS_SIZE_SUC; vGSYM vMEMBER_NOT_EMPTY] ---->
    vMESON_TAC[lemma; vIN_DELETE];
    vSIMP_TAC[vLEFT_IMP_EXISTS_THM; vHAS_SIZE; vCARD_CLAUSES; vFINITE_INSERT]]);;

(* ------------------------------------------------------------------------- *)
(* Produce an explicit expansion for "s HAS_SIZE n" for numeral n.           *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_CONV =
  let pth = prove
   ((parse_term "(~(a IN {}) /\\ P <=> P) /\\\n     (~(a IN {b}) /\\ P <=> ~(a = b) /\\ P) /\\\n     (~(a IN (b INSERT cs)) /\\ P <=> ~(a = b) /\\ ~(a IN cs) /\\ P)"),
    vSET_TAC[])
  and qth = prove
   ((parse_term "((?s. s HAS_SIZE 0 /\\ P s) <=> P {}) /\\\n     ((?s. s HAS_SIZE (SUC n) /\\ P s) <=>\n      (?a s. s HAS_SIZE n /\\ ~(a IN s) /\\ P(a INSERT s)))"),
    vREWRITE_TAC[vHAS_SIZE_CLAUSES] ----> vMESON_TAC[]) in
  let qconv_0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 qth]
  and qconv_1 = vGEN_REWRITE_CONV vI [vCONJUNCT2 qth]
  and rconv_0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 pth]
  and rconv_1 = vGEN_REWRITE_CONV vI [vCONJUNCT2 pth] in
  let rec vEXISTS_HAS_SIZE_AND_CONV tm =
   (qconv_0 ||-->
    (vBINDER_CONV(vLAND_CONV(vRAND_CONV num_CONV)) +--->
     qconv_1 +--->
     vBINDER_CONV vEXISTS_HAS_SIZE_AND_CONV)) tm in
  let rec vNOT_IN_INSERT_CONV tm =
   ((rconv_0 +---> vNOT_IN_INSERT_CONV) ||-->
    (rconv_1 +---> vRAND_CONV vNOT_IN_INSERT_CONV) ||-->
    vALL_CONV) tm in
  let vHAS_SIZE_CONV =
    vGEN_REWRITE_CONV vI [vCONJUNCT1 vHAS_SIZE_CLAUSES] ||-->
    (vRAND_CONV num_CONV +--->
     vGEN_REWRITE_CONV vI [vCONJUNCT2 vHAS_SIZE_CLAUSES] +--->
     vBINDER_CONV vEXISTS_HAS_SIZE_AND_CONV) in
  fun tm ->
    let th = vHAS_SIZE_CONV tm in
    let tm' = rand(concl th) in
    let evs,_bod = strip_exists tm' in
    if evs = [] then th else
    let th' = funpow (length evs) vBINDER_CONV vNOT_IN_INSERT_CONV tm' in
    vTRANS th th';;

(* ------------------------------------------------------------------------- *)
(* Various useful lemmas about cardinalities of unions etc.                  *)
(* ------------------------------------------------------------------------- *)

let vCARD_SUBSET_EQ = prove
 ((parse_term "!(a:A->bool) b. FINITE b /\\ a SUBSET b /\\ (CARD a = CARD b) ==> (a = b)"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [(parse_term "a:A->bool"); (parse_term "b DIFF (a:A->bool)")] vCARD_UNION) ---->
  vSUBGOAL_THEN (parse_term "FINITE(a:A->bool)") vASSUME_TAC ++-->
   [vASM_MESON_TAC[vFINITE_SUBSET]; vALL_TAC] ---->
  vSUBGOAL_THEN (parse_term "FINITE(b:A->bool DIFF a)") vASSUME_TAC ++-->
   [vMATCH_MP_TAC vFINITE_SUBSET ----> vEXISTS_TAC (parse_term "b:A->bool") ---->
    vASM_REWRITE_TAC[] ----> vSET_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN (parse_term "a:A->bool INTER (b DIFF a) = EMPTY") vASSUME_TAC ++-->
   [vSET_TAC[]; vALL_TAC] ---->
  vASM_REWRITE_TAC[] ---->
  vSUBGOAL_THEN (parse_term "a UNION (b:A->bool DIFF a) = b") vASSUME_TAC ++-->
   [vUNDISCH_TAC (parse_term "a:A->bool SUBSET b") ----> vSET_TAC[]; vALL_TAC] ---->
  vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vARITH_RULE (parse_term "(a = a + b) <=> (b = 0)")] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN (parse_term "b:A->bool DIFF a = EMPTY") vMP_TAC ++-->
   [vREWRITE_TAC[vGSYM vHAS_SIZE_0] ---->
    vASM_REWRITE_TAC[vHAS_SIZE];
    vUNDISCH_TAC (parse_term "a:A->bool SUBSET b") ----> vSET_TAC[]]);;

let vCARD_SUBSET = prove
 ((parse_term "!(a:A->bool) b. a SUBSET b /\\ FINITE(b) ==> CARD(a) <= CARD(b)"),
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "b:A->bool = a UNION (b DIFF a)") vSUBST1_TAC ++-->
   [vUNDISCH_TAC (parse_term "a:A->bool SUBSET b") ----> vSET_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN
   (parse_term "CARD (a UNION b DIFF a) = CARD(a:A->bool) + CARD(b DIFF a)")
  vSUBST1_TAC ++-->
   [vMATCH_MP_TAC vCARD_UNION ----> vREPEAT vCONJ_TAC ++-->
     [vMATCH_MP_TAC vFINITE_SUBSET ----> vEXISTS_TAC (parse_term "b:A->bool") ---->
      vASM_REWRITE_TAC[];
      vMATCH_MP_TAC vFINITE_SUBSET ----> vEXISTS_TAC (parse_term "b:A->bool") ---->
      vASM_REWRITE_TAC[] ----> vSET_TAC[];
      vSET_TAC[]];
    vARITH_TAC]);;

let vCARD_SUBSET_LE = prove
 ((parse_term "!(a:A->bool) b. FINITE b /\\ a SUBSET b /\\ (CARD b <= CARD a) ==> (a = b)"),
  vMESON_TAC[vCARD_SUBSET; vCARD_SUBSET_EQ; vLE_ANTISYM]);;

let vSUBSET_CARD_EQ = prove
 ((parse_term "!s t. FINITE t /\\ s SUBSET t ==> (CARD s = CARD t <=> s = t)"),
  vMESON_TAC[vCARD_SUBSET_EQ; vLE_ANTISYM; vCARD_SUBSET]);;

let vFINITE_CARD_LE_SUBSET = prove
 ((parse_term "!s (t:A->bool) n.\n        s SUBSET t /\\ FINITE t /\\ CARD t <= n\n        ==> FINITE s /\\ CARD s <= n"),
  vMESON_TAC[vFINITE_SUBSET; vCARD_SUBSET; vLE_TRANS]);;

let vCARD_PSUBSET = prove
 ((parse_term "!(a:A->bool) b. a PSUBSET b /\\ FINITE(b) ==> CARD(a) < CARD(b)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vSET_RULE
   (parse_term "a PSUBSET b <=> ?x. x IN b /\\ ~(x IN a) /\\ a SUBSET (b DELETE x)") ] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "x:A") vSTRIP_ASSUME_TAC) ---->
  vMATCH_MP_TAC vLET_TRANS ----> vEXISTS_TAC (parse_term "CARD(b DELETE (x:A))") ---->
  vASM_SIMP_TAC[vCARD_SUBSET; vFINITE_DELETE] ---->
  vASM_SIMP_TAC[vCARD_DELETE; vARITH_RULE (parse_term "n - 1 < n <=> ~(n = 0)")] ---->
  vASM_MESON_TAC[vCARD_EQ_0; vMEMBER_NOT_EMPTY]);;

let vCARD_PSUBSET_IMP = prove
 ((parse_term "!a b. a SUBSET b /\\ ~(CARD a = CARD b) ==> a PSUBSET b"),
  vREWRITE_TAC[vPSUBSET] ----> vMESON_TAC[]);;

let vCARD_PSUBSET_EQ = prove
 ((parse_term "!a b. FINITE b /\\ a SUBSET b ==> (a PSUBSET b <=> CARD a < CARD b)"),
  vMESON_TAC[vCARD_PSUBSET_IMP; vCARD_PSUBSET; vLT_REFL]);;

let vCARD_UNION_LE = prove
 ((parse_term "!s t:A->bool.\n        FINITE s /\\ FINITE t ==> CARD(s UNION t) <= CARD(s) + CARD(t)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
  vEXISTS_TAC (parse_term "CARD(s:A->bool) + CARD(t DIFF s)") ---->
  vASM_SIMP_TAC[vLE_ADD_LCANCEL; vCARD_SUBSET; vSUBSET_DIFF; vFINITE_DIFF] ---->
  vMATCH_MP_TAC vEQ_IMP_LE ---->
  vONCE_REWRITE_TAC[vSET_RULE (parse_term "s UNION t = s UNION (t DIFF s)")] ---->
  vMATCH_MP_TAC vCARD_UNION ----> vASM_SIMP_TAC[vFINITE_DIFF] ----> vSET_TAC[]);;

let vFINITE_CARD_LE_UNION = prove
 ((parse_term "!s (t:A->bool) m n.\n        (FINITE s /\\ CARD s <= m) /\\\n        (FINITE t /\\ CARD t <= n)\n        ==> FINITE(s UNION t) /\\ CARD(s UNION t) <= m + n"),
  vMESON_TAC[vFINITE_UNION; vCARD_UNION_LE; vLE_ADD2; vLE_TRANS]);;

let vCARD_UNIONS_LE = prove
 ((parse_term "!s t:A->B->bool m n.\n        s HAS_SIZE m /\\ (!x. x IN s ==> FINITE(t x) /\\ CARD(t x) <= n)\n        ==> CARD(UNIONS {t(x) | x IN s}) <= m * n"),
  vGEN_REWRITE_TAC (funpow 4 vBINDER_CONV -| funpow 2 vLAND_CONV) [vHAS_SIZE] ---->
  vREWRITE_TAC[vGSYM vCONJ_ASSOC] ---->
  vONCE_REWRITE_TAC[vIMP_CONJ] ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ----> vCONJ_TAC ---->
  vREWRITE_TAC[vSET_RULE (parse_term "UNIONS {t x | x IN {}} = {}"); vCARD_CLAUSES; vLE_0] ---->
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ----> vREPEAT vGEN_TAC ---->
  vASM_SIMP_TAC[vCARD_CLAUSES; vFINITE_RULES] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vSUBST_ALL_TAC -| vSYM) vASSUME_TAC) ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "UNIONS {t x | x IN a INSERT s} = t(a) UNION UNIONS {t x | x IN s}")] ---->
  vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC
   (parse_term "CARD((t:A->B->bool) x) + CARD(UNIONS {(t:A->B->bool) y | y IN s})") ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vCARD_UNION_LE ----> vASM_SIMP_TAC[vIN_INSERT] ---->
    vREWRITE_TAC[vSET_RULE (parse_term "{t x | x IN s} = IMAGE t s")] ---->
    vASM_SIMP_TAC[vFINITE_FINITE_UNIONS; vFINITE_IMAGE; vFORALL_IN_IMAGE;
                 vIN_INSERT];
    vMATCH_MP_TAC(vARITH_RULE (parse_term "a <= n /\\ b <= x * n ==> a + b <= SUC x * n")) ---->
    vASM_SIMP_TAC[vIN_INSERT]]);;

let vCARD_UNION_GEN = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t\n         ==> CARD(s UNION t) = (CARD(s) + CARD(t)) - CARD(s INTER t)"),
  vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vSET_RULE (parse_term "s UNION t = s UNION (t DIFF s)")] ---->
  vASM_SIMP_TAC[vARITH_RULE (parse_term "x:num <= y ==> (a + y) - x = a + (y - x)");
               vCARD_SUBSET; vINTER_SUBSET; vGSYM vCARD_DIFF] ---->
  vREWRITE_TAC[vSET_RULE (parse_term "t DIFF (s INTER t) = t DIFF s")] ---->
  vMATCH_MP_TAC vCARD_UNION ----> vASM_SIMP_TAC[vFINITE_DIFF] ----> vSET_TAC[]);;

let vCARD_UNION_OVERLAP_EQ = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t\n         ==> (CARD(s UNION t) = CARD s + CARD t <=> s INTER t = {})"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vASM_SIMP_TAC[vCARD_UNION_GEN] ---->
  vREWRITE_TAC[vARITH_RULE (parse_term "a - b = a <=> b = 0 \\/ a = 0")] ---->
  vASM_SIMP_TAC[vADD_EQ_0; vCARD_EQ_0; vFINITE_INTER] ----> vSET_TAC[]);;

let vCARD_UNION_OVERLAP = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t /\\ CARD(s UNION t) < CARD(s) + CARD(t)\n         ==> ~(s INTER t = {})"),
  vSIMP_TAC[vGSYM vCARD_UNION_OVERLAP_EQ] ----> vARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of image under maps, injective or general.                    *)
(* ------------------------------------------------------------------------- *)

let vCARD_IMAGE_INJ = prove
 ((parse_term "!(f:A->B) s. (!x y. x IN s /\\ y IN s /\\ (f(x) = f(y)) ==> (x = y)) /\\\n                FINITE s ==> (CARD (IMAGE f s) = CARD s)"),
  vGEN_TAC ---->
  vREWRITE_TAC[vTAUT (parse_term "a /\\ b ==> c <=> b ==> a ==> c")] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vNOT_IN_EMPTY; vIMAGE_CLAUSES] ---->
  vREPEAT vSTRIP_TAC ---->
  vASM_SIMP_TAC[vCARD_CLAUSES; vFINITE_IMAGE; vIN_IMAGE] ---->
  vCOND_CASES_TAC ----> vASM_MESON_TAC[vIN_INSERT]);;

let vHAS_SIZE_IMAGE_INJ = prove
 ((parse_term "!(f:A->B) s n.\n        (!x y. x IN s /\\ y IN s /\\ (f(x) = f(y)) ==> (x = y)) /\\ s HAS_SIZE n\n        ==> (IMAGE f s) HAS_SIZE n"),
  vSIMP_TAC[vHAS_SIZE; vFINITE_IMAGE] ----> vMESON_TAC[vCARD_IMAGE_INJ]);;

let vCARD_IMAGE_LE = prove
 ((parse_term "!(f:A->B) s. FINITE s ==> CARD(IMAGE f s) <= CARD s"),
  vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vIMAGE_CLAUSES; vCARD_CLAUSES; vFINITE_IMAGE; vLE_REFL] ---->
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vDISCH_THEN(vMP_TAC -| vCONJUNCT1) ----> vARITH_TAC);;

let vFINITE_CARD_LE_IMAGE = prove
 ((parse_term "!(f:A->B) s n.\n        FINITE s /\\ CARD s <= n ==> FINITE(IMAGE f s) /\\ CARD(IMAGE f s) <= n"),
  vMESON_TAC[vCARD_IMAGE_LE; vLE_TRANS; vFINITE_IMAGE]);;

let vCARD_IMAGE_INJ_EQ = prove
 ((parse_term "!f:A->B s t.\n        FINITE s /\\\n        (!x. x IN s ==> f(x) IN t) /\\\n        (!y. y IN t ==> ?!x. x IN s /\\ f(x) = y)\n        ==> CARD t = CARD s"),
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "t = IMAGE (f:A->B) s") vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_IMAGE] ----> vASM_MESON_TAC[];
    vMATCH_MP_TAC vCARD_IMAGE_INJ ----> vASM_MESON_TAC[]]);;

let vCARD_SUBSET_IMAGE = prove
 ((parse_term "!f s t. FINITE t /\\ s SUBSET IMAGE f t ==> CARD s <= CARD t"),
  vMESON_TAC[vLE_TRANS; vFINITE_IMAGE; vCARD_IMAGE_LE; vCARD_SUBSET]);;

let vHAS_SIZE_IMAGE_INJ_EQ = prove
 ((parse_term "!f s n.\n        (!x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y)\n        ==> ((IMAGE f s) HAS_SIZE n <=> s HAS_SIZE n)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vHAS_SIZE] ---->
  vMATCH_MP_TAC(vTAUT
   (parse_term "(a' <=> a) /\\ (a ==> (b' <=> b)) ==> (a' /\\ b' <=> a /\\ b)")) ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vFINITE_IMAGE_INJ_EQ;
    vDISCH_TAC ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vMATCH_MP_TAC vCARD_IMAGE_INJ] ---->
  vASM_REWRITE_TAC[]);;

let vCARD_IMAGE_EQ_INJ = prove
 ((parse_term "!f:A->B s.\n        FINITE s\n        ==> (CARD(IMAGE f s) = CARD s <=>\n             !x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y)"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC; vASM_MESON_TAC[vCARD_IMAGE_INJ]] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "y:A")] ----> vSTRIP_TAC ---->
  vASM_CASES_TAC (parse_term "x:A = y") ----> vASM_REWRITE_TAC[] ---->
  vUNDISCH_TAC (parse_term "CARD(IMAGE (f:A->B) s) = CARD s") ---->
  vSUBGOAL_THEN (parse_term "IMAGE  (f:A->B) s = IMAGE f (s DELETE y)") vSUBST1_TAC ++-->
   [vASM vSET_TAC[]; vREWRITE_TAC[]] ---->
  vMATCH_MP_TAC(vARITH_RULE (parse_term "!n. m <= n /\\ n < p ==> ~(m:num = p)")) ---->
  vEXISTS_TAC (parse_term "CARD(s DELETE (y:A))") ---->
  vASM_SIMP_TAC[vCARD_IMAGE_LE; vFINITE_DELETE] ---->
  vASM_SIMP_TAC[vCARD_DELETE; vCARD_EQ_0;
               vARITH_RULE (parse_term "n - 1 < n <=> ~(n = 0)")] ---->
  vASM vSET_TAC[]);;

let vEXISTS_SMALL_SUBSET_IMAGE_INJ = prove
 ((parse_term "!P f s n.\n    (?t. FINITE t /\\ CARD t < n /\\ t SUBSET IMAGE f s /\\ P t) <=>\n    (?t. FINITE t /\\ CARD t < n /\\ t SUBSET s /\\\n         (!x y. x IN t /\\ y IN t ==> (f x = f y <=> x = y)) /\\\n         P (IMAGE f t))"),
  vONCE_REWRITE_TAC[vTAUT (parse_term "p /\\ q /\\ r /\\ s <=> r /\\ s /\\ p /\\ q")] ---->
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vEXISTS_SUBSET_IMAGE_INJ] ---->
  vREWRITE_TAC[vCONJ_ASSOC] ----> vAP_TERM_TAC ----> vABS_TAC ---->
  vMATCH_MP_TAC(vTAUT
   (parse_term "(p ==> (q <=> s)) /\\ (p /\\ s ==> (r <=> t))\n    ==> ((p /\\ q) /\\ r <=> (p /\\ s) /\\ t)")) ---->
  vMESON_TAC[vCARD_IMAGE_INJ; vFINITE_IMAGE_INJ_EQ]);;

let vFORALL_SMALL_SUBSET_IMAGE_INJ = prove
 ((parse_term "!P f s n.\n    (!t. FINITE t /\\ CARD t < n /\\ t SUBSET IMAGE f s ==> P t) <=>\n    (!t. FINITE t /\\ CARD t < n /\\ t SUBSET s /\\\n         (!x y. x IN t /\\ y IN t ==> (f x = f y <=> x = y))\n         ==> P (IMAGE f t))"),
  vREPEAT vGEN_TAC ---->
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(!t. p t) <=> ~(?t. ~p t)")] ---->
  vREWRITE_TAC[vNOT_IMP; vEXISTS_SMALL_SUBSET_IMAGE_INJ; vGSYM vCONJ_ASSOC]);;

let vEXISTS_SMALL_SUBSET_IMAGE = prove
 ((parse_term "!P f s n.\n    (?t. FINITE t /\\ CARD t < n /\\ t SUBSET IMAGE f s /\\ P t) <=>\n    (?t. FINITE t /\\ CARD t < n /\\ t SUBSET s /\\\n         P (IMAGE f t))"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vREWRITE_TAC[vEXISTS_SMALL_SUBSET_IMAGE_INJ] ----> vMESON_TAC[];
    vMESON_TAC[vFINITE_IMAGE; vCARD_IMAGE_LE; vLET_TRANS; vIMAGE_SUBSET]]);;

let vFORALL_SMALL_SUBSET_IMAGE = prove
 ((parse_term "!P f s n.\n    (!t. FINITE t /\\ CARD t < n /\\ t SUBSET IMAGE f s ==> P t) <=>\n    (!t. FINITE t /\\ CARD t < n /\\ t SUBSET s ==> P (IMAGE f t))"),
  vREPEAT vGEN_TAC ---->
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(!t. p t) <=> ~(?t. ~p t)")] ---->
  vREWRITE_TAC[vNOT_IMP; vEXISTS_SMALL_SUBSET_IMAGE; vGSYM vCONJ_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Choosing a smaller subset of a given size.                                *)
(* ------------------------------------------------------------------------- *)

let vCHOOSE_SUBSET_STRONG = prove
 ((parse_term "!n s:A->bool.\n        (FINITE s ==> n <= CARD s) ==> ?t. t SUBSET s /\\ t HAS_SIZE n"),
  vINDUCT_TAC ----> vREWRITE_TAC[vHAS_SIZE_0; vHAS_SIZE_SUC] ++-->
   [vMESON_TAC[vEMPTY_SUBSET]; vALL_TAC] ---->
  vMATCH_MP_TAC vSET_PROVE_CASES ---->
  vREWRITE_TAC[vFINITE_EMPTY; vCARD_CLAUSES; vARITH_RULE (parse_term "~(SUC n <= 0)")] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "a:A"); (parse_term "s:A->bool")] ----> vDISCH_TAC ---->
  vASM_SIMP_TAC[vCARD_CLAUSES; vFINITE_INSERT; vLE_SUC] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "s:A->bool")) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "t:A->bool") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "(a:A) INSERT t") ---->
  vREPEAT(vCONJ_TAC ++--> [vASM vSET_TAC[]; vALL_TAC]) ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vHAS_SIZE]) ---->
  vASM_SIMP_TAC[vHAS_SIZE; vCARD_DELETE; vFINITE_INSERT; vFINITE_DELETE;
               vCARD_CLAUSES] ---->
  vGEN_TAC ----> vCOND_CASES_TAC ----> vREWRITE_TAC[vSUC_SUB1] ---->
  vASM vSET_TAC[]);;

let vCHOOSE_SUBSET_EQ = prove
 ((parse_term "!n s:A->bool.\n     (FINITE s ==> n <= CARD s) <=> (?t. t SUBSET s /\\ t HAS_SIZE n)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vCHOOSE_SUBSET_STRONG] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "t:A->bool") vSTRIP_ASSUME_TAC) ----> vDISCH_TAC ---->
  vTRANS_TAC vLE_TRANS (parse_term "CARD(t:A->bool)") ---->
  vASM_MESON_TAC[vCARD_SUBSET; vHAS_SIZE; vLE_REFL]);;

let vCHOOSE_SUBSET = prove
 ((parse_term "!s:A->bool. FINITE s ==> !n. n <= CARD s ==> ?t. t SUBSET s /\\ t HAS_SIZE n"),
  vMESON_TAC[vCHOOSE_SUBSET_STRONG]);;

let vCHOOSE_SUBSET_BETWEEN = prove
 ((parse_term "!n s u:A->bool.\n        s SUBSET u /\\ FINITE s /\\ CARD s <= n /\\ (FINITE u ==> n <= CARD u)\n        ==> ?t. s SUBSET t /\\ t SUBSET u /\\ t HAS_SIZE n"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "n - CARD(s:A->bool)"); (parse_term "u DIFF s:A->bool")]
        vCHOOSE_SUBSET_STRONG) ---->
  vANTS_TAC ++-->
   [vASM_CASES_TAC (parse_term "FINITE(u:A->bool)") ---->
    vASM_SIMP_TAC[vCARD_DIFF; vARITH_RULE (parse_term "n:num <= m ==> n - x <= m - x")] ---->
    vMATCH_MP_TAC(vTAUT (parse_term "~p ==> p ==> q")) ---->
    vASM_MESON_TAC[vFINITE_UNION; vFINITE_SUBSET; vSET_RULE
     (parse_term "u SUBSET (u DIFF s) UNION s")];
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "t:A->bool") vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC (parse_term "s UNION t:A->bool") ---->
    vREPEAT(vCONJ_TAC ++--> [vASM vSET_TAC[]; vALL_TAC]) ---->
    vSUBGOAL_THEN (parse_term "n:num = CARD(s) + (n - CARD(s:A->bool))") vSUBST1_TAC ++-->
     [vASM_ARITH_TAC;
      vMATCH_MP_TAC vHAS_SIZE_UNION] ---->
      vASM_REWRITE_TAC[] ----> vASM_REWRITE_TAC[vHAS_SIZE] ----> vASM vSET_TAC[]]);;

let vCARD_LE_UNIONS_CHAIN = prove
 ((parse_term "!(f:(A->bool)->bool) n.\n        (!t u. t IN f /\\ u IN f ==> t SUBSET u \\/ u SUBSET t) /\\\n        (!t. t IN f ==> FINITE t /\\ CARD t <= n)\n        ==> FINITE(UNIONS f) /\\ CARD(UNIONS f) <= n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "f:(A->bool)->bool = {}") ---->
  vASM_REWRITE_TAC[vUNIONS_0; vFINITE_EMPTY; vCARD_CLAUSES; vLE_0] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vGEN_REWRITE_TAC vI [vGSYM vCONTRAPOS_THM] ---->
  vREWRITE_TAC[vNOT_FORALL_THM; vNOT_IMP; vTAUT (parse_term "~(p /\\ q) <=> p ==> ~q")] ---->
  vREWRITE_TAC[vARITH_RULE (parse_term "~(x <= n) <=> SUC n <= x")] ---->
  vREWRITE_TAC[vCHOOSE_SUBSET_EQ] ----> vREWRITE_TAC[vRIGHT_AND_EXISTS_THM] ---->
  vONCE_REWRITE_TAC[vSWAP_EXISTS_THM] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC (parse_term "s:A->bool") ---->
  vREWRITE_TAC[vHAS_SIZE] ----> vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vFINITE_SUBSET_UNIONS_CHAIN ---->
  vASM_REWRITE_TAC[]);;

let vCARD_LE_1 = prove
 ((parse_term "!s:A->bool. FINITE s /\\ CARD s <= 1 <=> ?a. s SUBSET {a}"),
  vGEN_TAC ----> vREWRITE_TAC[vARITH_RULE (parse_term "c <= 1 <=> c = 0 \\/ c = 1")] ---->
  vREWRITE_TAC[vLEFT_OR_DISTRIB; vGSYM vHAS_SIZE] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vHAS_SIZE_CONV) ----> vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Lemmas about the parity of the set of fixed points of an involution.      *)
(* ------------------------------------------------------------------------- *)

let vINVOLUTION_EVEN_NOFIXPOINTS = prove
 ((parse_term "!f (s:A->bool).\n        FINITE s /\\ (!x. x IN s ==> f x IN s /\\ ~(f x = x) /\\ f(f x) = x)\n        ==> EVEN(CARD s)"),
  vREPEAT vGEN_TAC ----> vABBREV_TAC (parse_term "n = CARD(s:A->bool)") ---->
  vPOP_ASSUM vMP_TAC ---->
  vREWRITE_TAC[vTAUT (parse_term "p ==> q /\\ r ==> s <=> (q /\\ p) /\\ r ==> s")] ---->
  vMAP_EVERY (fun t -> vSPEC_TAC(t,t)) [(parse_term "s:A->bool"); (parse_term "n:num")] ---->
  vMATCH_MP_TAC num_WF ----> vX_GEN_TAC (parse_term "n:num") ----> vDISCH_TAC ---->
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vARITH] ---->
  vMATCH_MP_TAC vSET_PROVE_CASES ----> vASM_REWRITE_TAC[vCARD_CLAUSES] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "a:A"); (parse_term "s:A->bool")] ---->
  vSIMP_TAC[vFINITE_INSERT; vIMP_CONJ; vCARD_CLAUSES; vFORALL_IN_INSERT] ---->
  vREWRITE_TAC[vIN_INSERT] ----> vASM_CASES_TAC (parse_term "f(a:A) = a") ---->
  vASM_REWRITE_TAC[] ----> vASM_CASES_TAC (parse_term "n = 1") ---->
  vASM_SIMP_TAC[vARITH_RULE (parse_term "SUC n = 1 <=> n = 0"); vCARD_EQ_0; vNOT_IN_EMPTY] ---->
  vREPEAT vSTRIP_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "n - 2")) ---->
  vANTS_TAC ++--> [vASM_ARITH_TAC; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "s DELETE (f:A->A) a")) ---->
  vASM_SIMP_TAC[vFINITE_DELETE; vCARD_DELETE; vEVEN_SUB; vARITH] ---->
  vASM_REWRITE_TAC[vARITH_RULE (parse_term "n <= 2 <=> n = 0 \\/ n = 1 \\/ n = 2")] ---->
  vASM_CASES_TAC (parse_term "n = 2") ----> vASM_REWRITE_TAC[vARITH] ---->
  vDISCH_THEN vMATCH_MP_TAC ----> vCONJ_TAC ++-->
   [vASM_ARITH_TAC; vASM vSET_TAC[]]);;

let vINVOLUTION_EVEN_FIXPOINTS = prove
 ((parse_term "!f (s:A->bool).\n        FINITE s /\\ (!x. x IN s ==> f x IN s /\\ f(f x) = x)\n        ==> (EVEN(CARD {x | x IN s /\\ f x = x}) <=> EVEN(CARD s))"),
  vREPEAT vSTRIP_TAC ----> vTRANS_TAC vEQ_TRANS
  (parse_term "EVEN(CARD({x:A | x IN s /\\ f x = x} UNION {x | x IN s /\\ ~(f x = x)}))") ---->
  vCONJ_TAC ++--> [vALL_TAC; vAP_TERM_TAC ----> vAP_TERM_TAC ----> vSET_TAC[]] ---->
  vASM_SIMP_TAC[vEVEN_ADD; vCARD_UNION; vFINITE_RESTRICT; vSET_RULE
   (parse_term "{x | x IN s /\\ P x} INTER {x | x IN s /\\ ~P x} = {}")] ---->
  vREWRITE_TAC[vTAUT (parse_term "(p <=> (p <=> q)) <=> q")] ---->
  vMATCH_MP_TAC vINVOLUTION_EVEN_NOFIXPOINTS ---->
  vEXISTS_TAC (parse_term "f:A->A") ----> vASM_SIMP_TAC[vFINITE_RESTRICT] ---->
  vASM vSET_TAC[]);;
