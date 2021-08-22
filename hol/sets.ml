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
open Ind_types
open Lists
open Realax
open Calc_int
open Realarith
open Real
open Calc_rat
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

(* ------------------------------------------------------------------------- *)
(* Cardinality of product.                                                   *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_PRODUCT_DEPENDENT = prove
 ((parse_term "!s m t n.\n         s HAS_SIZE m /\\ (!x. x IN s ==> t(x) HAS_SIZE n)\n         ==> {(x:A,y:B) | x IN s /\\ y IN t(x)} HAS_SIZE (m * n)"),
  vGEN_REWRITE_TAC (funpow 4 vBINDER_CONV -| funpow 2 vLAND_CONV) [vHAS_SIZE] ---->
  vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vCARD_CLAUSES; vNOT_IN_EMPTY; vIN_INSERT] ----> vCONJ_TAC ++-->
   [vGEN_TAC ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
    vREWRITE_TAC[vMULT_CLAUSES; vHAS_SIZE_0] ----> vSET_TAC[];
    vALL_TAC] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "s:A->bool")] ----> vSTRIP_TAC ---->
  vX_GEN_TAC (parse_term "m:num") ----> vDISCH_THEN(vASSUME_TAC -| vSYM) ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "t:A->B->bool"); (parse_term "n:num")] ---->
  vREWRITE_TAC[vTAUT (parse_term "a \\/ b ==> c <=> (a ==> c) /\\ (b ==> c)")] ---->
  vSIMP_TAC[vFORALL_AND_THM; vLEFT_FORALL_IMP_THM; vEXISTS_REFL] ---->
  vSTRIP_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "CARD(s:A->bool)")) ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES] ----> vDISCH_TAC ---->
  vREWRITE_TAC[vSET_RULE
    (parse_term "{(x,y) | (x = a \\/ x IN s) /\\ y IN t(x)} =\n     {(x,y) | x IN s /\\ y IN t(x)} UNION\n     IMAGE (\\y. (a,y)) (t a)")] ---->
  vMATCH_MP_TAC vHAS_SIZE_UNION ---->
  vASM_SIMP_TAC[vHAS_SIZE_IMAGE_INJ; vPAIR_EQ] ---->
  vREWRITE_TAC[vDISJOINT; vIN_IMAGE; vIN_ELIM_THM; vIN_INTER; vEXTENSION;
              vNOT_IN_EMPTY; vEXISTS_PAIR_THM; vPAIR_EQ] ---->
  vREPEAT vSTRIP_TAC ----> vASM_MESON_TAC[vPAIR_EQ]);;

let vFINITE_PRODUCT_DEPENDENT = prove
 ((parse_term "!f:A->B->C s t.\n        FINITE s /\\ (!x. x IN s ==> FINITE(t x))\n        ==> FINITE {f x y | x IN s /\\ y IN (t x)}"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC (parse_term "IMAGE (\\(x,y). (f:A->B->C) x y) {x,y | x IN s /\\ y IN t x}") ---->
  vREWRITE_TAC[vSUBSET; vIN_IMAGE; vEXISTS_PAIR_THM; vIN_ELIM_PAIR_THM] ---->
  vREWRITE_TAC[vFORALL_IN_GSPEC] ---->
  vCONJ_TAC ++--> [vMATCH_MP_TAC vFINITE_IMAGE; vMESON_TAC[]] ---->
  vMAP_EVERY vUNDISCH_TAC
   [(parse_term "!x:A. x IN s ==> FINITE(t x :B->bool)"); (parse_term "FINITE(s:A->bool)")] ---->
  vMAP_EVERY (fun t -> vSPEC_TAC(t,t)) [(parse_term "t:A->B->bool"); (parse_term "s:A->bool")] ---->
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ----> vCONJ_TAC ++-->
   [vGEN_TAC ----> vSUBGOAL_THEN (parse_term "{(x:A,y:B) | x IN {} /\\ y IN (t x)} = {}")
     (fun th -> vREWRITE_TAC[th; vFINITE_RULES]) ---->
    vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vNOT_IN_EMPTY];
    vALL_TAC] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "a:A"); (parse_term "s:A->bool")] ----> vSTRIP_TAC ---->
  vX_GEN_TAC (parse_term "t:A->B->bool") ---->
  vSUBGOAL_THEN
   (parse_term "{(x:A,y:B) | x IN (a INSERT s) /\\ y IN (t x)} =\n    IMAGE (\\y. a,y) (t a) UNION {(x,y) | x IN s /\\ y IN (t x)}")
   (fun th -> vASM_SIMP_TAC[vIN_INSERT; vFINITE_IMAGE; vFINITE_UNION; th]) ---->
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vIN_ELIM_THM; vIN_INSERT; vIN_UNION] ---->
  vMESON_TAC[]);;

let vFINITE_PRODUCT = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t ==> FINITE {(x:A,y:B) | x IN s /\\ y IN t}"),
  vSIMP_TAC[vFINITE_PRODUCT_DEPENDENT]);;

let vCARD_PRODUCT = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t\n         ==> (CARD {(x:A,y:B) | x IN s /\\ y IN t} = CARD s * CARD t)"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [(parse_term "s:A->bool"); (parse_term "CARD(s:A->bool)"); (parse_term "\\x:A. t:B->bool");
                  (parse_term "CARD(t:B->bool)")] vHAS_SIZE_PRODUCT_DEPENDENT) ---->
  vASM_SIMP_TAC[vHAS_SIZE]);;

let vHAS_SIZE_PRODUCT = prove
 ((parse_term "!s m t n. s HAS_SIZE m /\\ t HAS_SIZE n\n             ==> {(x:A,y:B) | x IN s /\\ y IN t} HAS_SIZE (m * n)"),
  vSIMP_TAC[vHAS_SIZE; vCARD_PRODUCT; vFINITE_PRODUCT]);;

(* ------------------------------------------------------------------------- *)
(* Actually introduce a Cartesian product operation.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("CROSS",(22,"right"));;

let vCROSS = new_definition
 (parse_term "s CROSS t = {x,y | x IN s /\\ y IN t}");;

let vIN_CROSS = prove
 ((parse_term "!x y s t. (x,y) IN (s CROSS t) <=> x IN s /\\ y IN t"),
  vREWRITE_TAC[vCROSS; vIN_ELIM_PAIR_THM]);;

let vHAS_SIZE_CROSS = prove
 ((parse_term "!s t m n. s HAS_SIZE m /\\ t HAS_SIZE n ==> (s CROSS t) HAS_SIZE (m * n)"),
  vREWRITE_TAC[vCROSS; vHAS_SIZE_PRODUCT]);;

let vFINITE_CROSS = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t ==> FINITE(s CROSS t)"),
  vSIMP_TAC[vCROSS; vFINITE_PRODUCT]);;

let vCARD_CROSS = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t ==> CARD(s CROSS t) = CARD s * CARD t"),
  vSIMP_TAC[vCROSS; vCARD_PRODUCT]);;

let vCROSS_EQ_EMPTY = prove
 ((parse_term "!s t. s CROSS t = {} <=> s = {} \\/ t = {}"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_CROSS; vNOT_IN_EMPTY] ---->
  vMESON_TAC[]);;

let vCROSS_EMPTY = prove
 ((parse_term "(!s:A->bool. s CROSS {} = {}) /\\ (!t:B->bool. {} CROSS t = {})"),
  vREWRITE_TAC[vCROSS_EQ_EMPTY]);;

let vCROSS_SING = prove
 ((parse_term "!x:A y:B. {x} CROSS {y} = {(x,y)}"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_SING; vIN_CROSS; vPAIR_EQ]);;

let vCROSS_UNIV = prove
 ((parse_term "(:A) CROSS (:B) = (:A#B)"),
  vREWRITE_TAC[vCROSS; vEXTENSION; vIN_ELIM_PAIR_THM; vFORALL_PAIR_THM; vIN_UNIV]);;

let vFINITE_CROSS_EQ = prove
 ((parse_term "!s:A->bool t:B->bool.\n        FINITE(s CROSS t) <=> s = {} \\/ t = {} \\/ FINITE s /\\ FINITE t"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "s:A->bool = {}") ---->
  vASM_REWRITE_TAC[vCROSS_EMPTY; vFINITE_EMPTY] ---->
  vASM_CASES_TAC (parse_term "t:B->bool = {}") ---->
  vASM_REWRITE_TAC[vCROSS_EMPTY; vFINITE_EMPTY] ---->
  vEQ_TAC ----> vREWRITE_TAC[vFINITE_CROSS] ----> vREPEAT vSTRIP_TAC ++-->
   [vFIRST_ASSUM(vMP_TAC -| vMATCH_MP(vISPEC (parse_term "FST:A#B->A") vFINITE_IMAGE));
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP(vISPEC (parse_term "SND:A#B->B") vFINITE_IMAGE))] ---->
  vMATCH_MP_TAC(vREWRITE_RULE[vIMP_CONJ_ALT] vFINITE_SUBSET) ---->
  vREWRITE_TAC[vSUBSET; vIN_IMAGE; vEXISTS_PAIR_THM; vIN_CROSS] ---->
  vASM vSET_TAC[]);;

let vINFINITE_CROSS_EQ = prove
 ((parse_term "!(s:A->bool) (t:B->bool).\n        INFINITE(s CROSS t) <=>\n        ~(s = {}) /\\ INFINITE t \\/ INFINITE s /\\ ~(t = {})"),
  vREWRITE_TAC[vINFINITE; vFINITE_CROSS_EQ] ----> vMESON_TAC[vFINITE_EMPTY]);;

let vFINITE_CROSS_UNIV = prove
 ((parse_term "FINITE(:A#B) <=> FINITE(:A) /\\ FINITE(:B)"),
  vREWRITE_TAC[vGSYM vCROSS_UNIV; vFINITE_CROSS_EQ; vUNIV_NOT_EMPTY]);;

let vINFINITE_CROSS_UNIV = prove
 ((parse_term "INFINITE(:A#B) <=> INFINITE(:A) \\/ INFINITE(:B)"),
  vREWRITE_TAC[vGSYM vCROSS_UNIV; vINFINITE_CROSS_EQ; vUNIV_NOT_EMPTY] ---->
  vMESON_TAC[]);;

let vFINITE_UNIV_PAIR = prove
 ((parse_term "FINITE(:A#A) <=> FINITE(:A)"),
  vREWRITE_TAC[vFINITE_CROSS_UNIV]);;

let vINFINITE_UNIV_PAIR = prove
 ((parse_term "INFINITE(:A#A) <=> INFINITE(:A)"),
  vREWRITE_TAC[vINFINITE_CROSS_UNIV]);;

let vFORALL_IN_CROSS = prove
 ((parse_term "!P s t. (!z. z IN s CROSS t ==> P z) <=>\n           (!x y. x IN s /\\ y IN t ==> P(x,y))"),
  vREWRITE_TAC[vFORALL_PAIR_THM; vIN_CROSS]);;

let vEXISTS_IN_CROSS = prove
 ((parse_term "!P s t. (?z. z IN s CROSS t /\\ P z) <=>\n           (?x y. x IN s /\\ y IN t /\\ P(x,y))"),
  vREWRITE_TAC[vEXISTS_PAIR_THM; vGSYM vCONJ_ASSOC; vIN_CROSS]);;

let vSUBSET_CROSS = prove
 ((parse_term "!s t s' t'. s CROSS t SUBSET s' CROSS t' <=>\n                s = {} \\/ t = {} \\/ s SUBSET s' /\\ t SUBSET t'"),
  vSIMP_TAC[vCROSS; vEXTENSION; vIN_ELIM_PAIR_THM; vSUBSET;
   vFORALL_PAIR_THM; vIN_CROSS; vNOT_IN_EMPTY] ----> vMESON_TAC[]);;

let vCROSS_MONO = prove
 ((parse_term "!s t s' t'. s SUBSET s' /\\ t SUBSET t' ==> s CROSS t SUBSET s' CROSS t'"),
  vSIMP_TAC[vSUBSET_CROSS]);;

let vCROSS_EQ = prove
 ((parse_term "!s s':A->bool t t':B->bool.\n        s CROSS t = s' CROSS t' <=>\n        (s = {} \\/ t = {}) /\\ (s' = {} \\/ t' = {}) \\/ s = s' /\\ t = t'"),
  vREWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET_CROSS] ----> vSET_TAC[]);;

let vIMAGE_FST_CROSS = prove
 ((parse_term "!s:A->bool t:B->bool.\n        IMAGE FST (s CROSS t) = if t = {} then {} else s"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vCROSS_EMPTY; vIMAGE_CLAUSES] ---->
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE] ----> vONCE_REWRITE_TAC[vCONJ_SYM] ---->
  vREWRITE_TAC[vEXISTS_IN_CROSS; vFST] ----> vASM vSET_TAC[]);;

let vIMAGE_SND_CROSS = prove
 ((parse_term "!s:A->bool t:B->bool.\n        IMAGE SND (s CROSS t) = if s = {} then {} else t"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vCROSS_EMPTY; vIMAGE_CLAUSES] ---->
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE] ----> vONCE_REWRITE_TAC[vCONJ_SYM] ---->
  vREWRITE_TAC[vEXISTS_IN_CROSS; vSND] ----> vASM vSET_TAC[]);;

let vIMAGE_PAIRED_CROSS = prove
 ((parse_term "!(f:A->B) (g:C->D) s t.\n         IMAGE (\\(x,y). f x,g y) (s CROSS t) = (IMAGE f s) CROSS (IMAGE g t)"),
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vEXISTS_PAIR_THM; vIN_CROSS; vFORALL_PAIR_THM;
              vPAIR_EQ] ---->
  vMESON_TAC[]);;

let vCROSS_INTER = prove
 ((parse_term "(!s t u. s CROSS (t INTER u) = (s CROSS t) INTER (s CROSS u)) /\\\n   (!s t u. (s INTER t) CROSS u = (s CROSS u) INTER (t CROSS u))"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_INTER; vIN_CROSS] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vTAUT);;

let vCROSS_UNION = prove
 ((parse_term "(!s t u. s CROSS (t UNION u) = (s CROSS t) UNION (s CROSS u)) /\\\n   (!s t u. (s UNION t) CROSS u = (s CROSS u) UNION (t CROSS u))"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_UNION; vIN_CROSS] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vTAUT);;

let vCROSS_DIFF = prove
 ((parse_term "(!s t u. s CROSS (t DIFF u) = (s CROSS t) DIFF (s CROSS u)) /\\\n   (!s t u. (s DIFF t) CROSS u = (s CROSS u) DIFF (t CROSS u))"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_DIFF; vIN_CROSS] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vTAUT);;

let vINTER_CROSS = prove
 ((parse_term "!s s' t t'.\n      (s CROSS t) INTER (s' CROSS t') = (s INTER s') CROSS (t INTER t')"),
  vREWRITE_TAC[vEXTENSION; vIN_INTER; vFORALL_PAIR_THM; vIN_CROSS] ---->
  vCONV_TAC vTAUT);;

let vCROSS_UNIONS_UNIONS,vCROSS_UNIONS = (vCONJ_PAIR -| prove)
 ((parse_term "(!f g. (UNIONS f) CROSS (UNIONS g) =\n          UNIONS {s CROSS t | s IN f /\\ t IN g}) /\\\n   (!s f. s CROSS (UNIONS f) = UNIONS {s CROSS t | t IN f}) /\\\n   (!f t. (UNIONS f) CROSS t = UNIONS {s CROSS t | s IN f})"),
  vREWRITE_TAC[vUNIONS_GSPEC; vEXTENSION; vFORALL_PAIR_THM; vIN_ELIM_THM;
              vIN_CROSS] ---->
  vSET_TAC[]);;

let vCROSS_INTERS_INTERS,vCROSS_INTERS = (vCONJ_PAIR -| prove)
 ((parse_term "(!f g. (INTERS f) CROSS (INTERS g) =\n          if f = {} then INTERS {UNIV CROSS t | t IN g}\n          else if g = {} then INTERS {s CROSS UNIV | s IN f}\n          else INTERS {s CROSS t | s IN f /\\ t IN g}) /\\\n   (!s f. s CROSS (INTERS f) =\n          if f = {} then s CROSS UNIV else INTERS {s CROSS t | t IN f}) /\\\n   (!f t. (INTERS f) CROSS t =\n          if f = {} then UNIV CROSS t else INTERS {s CROSS t | s IN f})"),
  vREPEAT vSTRIP_TAC ----> vREPEAT (vCOND_CASES_TAC ----> vREWRITE_TAC[]) ---->
  vASM_REWRITE_TAC[vINTERS_GSPEC; vEXTENSION; vFORALL_PAIR_THM; vIN_ELIM_THM;
                  vIN_CROSS; vNOT_IN_EMPTY] ---->
  vASM vSET_TAC[]);;

let vDISJOINT_CROSS = prove
 ((parse_term "!s:A->bool t:B->bool s' t'.\n        DISJOINT (s CROSS t) (s' CROSS t') <=>\n        DISJOINT s s' \\/ DISJOINT t t'"),
  vREWRITE_TAC[vDISJOINT; vINTER_CROSS; vCROSS_EQ_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* "Extensional" functions, mapping to a fixed value ARB outside the domain. *)
(* Even though these are still total, they're a conveniently better model    *)
(* of the partial function space (e.g. the space has the right cardinality). *)
(* ------------------------------------------------------------------------- *)

let vARB = new_definition
  (parse_term "ARB = (@x:A. F)");;

let vEXTENSIONAL = new_definition
  (parse_term "EXTENSIONAL s = {f:A->B | !x. ~(x IN s) ==> f x = ARB}");;

let vIN_EXTENSIONAL = prove
 ((parse_term "!s f:A->B. f IN EXTENSIONAL s <=> (!x. ~(x IN s) ==> f x = ARB)"),
  vREWRITE_TAC[vEXTENSIONAL; vIN_ELIM_THM]);;

let vIN_EXTENSIONAL_UNDEFINED = prove
 ((parse_term "!s f:A->B x. f IN EXTENSIONAL s /\\ ~(x IN s) ==> f x = ARB"),
  vSIMP_TAC[vIN_EXTENSIONAL]);;

let vEXTENSIONAL_EMPTY = prove
 ((parse_term "EXTENSIONAL {} = {\\x:A. ARB:B}"),
  vREWRITE_TAC[vEXTENSION; vIN_EXTENSIONAL; vIN_SING; vNOT_IN_EMPTY] ---->
  vREWRITE_TAC[vFUN_EQ_THM]);;

let vEXTENSIONAL_UNIV = prove
 ((parse_term "!f. EXTENSIONAL (:A) f"),
  vREWRITE_TAC[vEXTENSIONAL; vIN_UNIV; vIN_ELIM_THM]);;

let vEXTENSIONAL_EQ = prove
 ((parse_term "!s f g:A->B.\n     f IN EXTENSIONAL s /\\ g IN EXTENSIONAL s /\\ (!x. x IN s ==> f x = g x)\n     ==> f = g"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vFUN_EQ_THM] ----> vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "x:A IN s") ++-->
  [vASM_SIMP_TAC[]; vASM_MESON_TAC[vIN_EXTENSIONAL_UNDEFINED]]);;

(* ------------------------------------------------------------------------- *)
(* Restriction of a function to an EXTENSIONAL one on a subset.              *)
(* ------------------------------------------------------------------------- *)

let vRESTRICTION = new_definition
  (parse_term "RESTRICTION s (f:A->B) x = if x IN s then f x else ARB");;

let vRESTRICTION_THM = prove
 ((parse_term "!s (f:A->B). RESTRICTION s f = \\x. if x IN s then f x else ARB"),
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION]);;

let vRESTRICTION_DEFINED = prove
 ((parse_term "!s f:A->B x. x IN s ==> RESTRICTION s f x = f x"),
  vSIMP_TAC[vRESTRICTION]);;

let vRESTRICTION_UNDEFINED = prove
 ((parse_term "!s f:A->B x. ~(x IN s) ==> RESTRICTION s f x = ARB"),
  vSIMP_TAC[vRESTRICTION]);;

let vRESTRICTION_EQ = prove
 ((parse_term "!s f:A->B x y. x IN s /\\ f x = y ==> RESTRICTION s f x = y"),
  vSIMP_TAC[vRESTRICTION_DEFINED]);;

let vRESTRICTION_IN_EXTENSIONAL = prove
 ((parse_term "!s f:A->B. RESTRICTION s f IN EXTENSIONAL s"),
  vSIMP_TAC[vIN_EXTENSIONAL; vRESTRICTION]);;

let vRESTRICTION_EXTENSION = prove
 ((parse_term "!s f g:A->B. RESTRICTION s f = RESTRICTION s g <=>\n                (!x. x IN s ==> f x = g x)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vRESTRICTION; vFUN_EQ_THM] ----> vMESON_TAC[]);;

let vRESTRICTION_FIXPOINT = prove
 ((parse_term "!s f:A->B. RESTRICTION s f = f <=> f IN EXTENSIONAL s"),
  vREWRITE_TAC[vIN_EXTENSIONAL; vFUN_EQ_THM; vRESTRICTION] ----> vMESON_TAC[]);;

let vRESTRICTION_RESTRICTION = prove
 ((parse_term "!s t f:A->B.\n        s SUBSET t ==> RESTRICTION s (RESTRICTION t f) = RESTRICTION s f"),
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION] ----> vSET_TAC[]);;

let vRESTRICTION_IDEMP = prove
 ((parse_term "!s f:A->B. RESTRICTION s (RESTRICTION s f) = RESTRICTION s f"),
  vREWRITE_TAC[vRESTRICTION_FIXPOINT; vRESTRICTION_IN_EXTENSIONAL]);;

let vIMAGE_RESTRICTION = prove
 ((parse_term "!f:A->B s t. s SUBSET t ==> IMAGE (RESTRICTION t f) s = IMAGE f s"),
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vRESTRICTION] ----> vSET_TAC[]);;

let vRESTRICTION_COMPOSE_RIGHT = prove
 ((parse_term "!f:A->B g:B->C s.\n        RESTRICTION s (g o RESTRICTION s f) =\n        RESTRICTION s (g o f)"),
  vREWRITE_TAC[vFUN_EQ_THM; o_DEF; vRESTRICTION] ---->
  vSIMP_TAC[vSUBSET; vFORALL_IN_IMAGE] ----> vSET_TAC[]);;

let vRESTRICTION_COMPOSE_LEFT = prove
 ((parse_term "!f:A->B g:B->C s t.\n        IMAGE f s SUBSET t\n        ==> RESTRICTION s (RESTRICTION t g o f) =\n            RESTRICTION s (g o f)"),
  vREWRITE_TAC[vFUN_EQ_THM; o_DEF; vRESTRICTION] ---->
  vSIMP_TAC[vSUBSET; vFORALL_IN_IMAGE] ----> vSET_TAC[]);;

let vRESTRICTION_COMPOSE = prove
 ((parse_term "!f:A->B g:B->C s t.\n        IMAGE f s SUBSET t\n        ==> RESTRICTION s (RESTRICTION t g o RESTRICTION s f) =\n            RESTRICTION s (g o f)"),
  vSIMP_TAC[vRESTRICTION_COMPOSE_LEFT; vRESTRICTION_COMPOSE_RIGHT]);;

let vRESTRICTION_UNIQUE = prove
 ((parse_term "!s (f:A->B) g.\n        RESTRICTION s f = g <=> EXTENSIONAL s g /\\ !x. x IN s ==> f x = g x"),
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION; vEXTENSIONAL; vIN_ELIM_THM] ---->
  vMESON_TAC[]);;

let vRESTRICTION_UNIQUE_ALT = prove
 ((parse_term "!s (f:A->B) g.\n        f = RESTRICTION s g <=> EXTENSIONAL s f /\\ !x. x IN s ==> f x = g x"),
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION; vEXTENSIONAL; vIN_ELIM_THM] ---->
  vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* General Cartesian product / dependent function space.                     *)
(* ------------------------------------------------------------------------- *)

let cartesian_product = new_definition
 (parse_term "cartesian_product k s =\n        {f:K->A | EXTENSIONAL k f /\\ !i. i IN k ==> f i IN s i}");;

let vIN_CARTESIAN_PRODUCT = prove
 ((parse_term "!k s (x:K->A).\n        x IN cartesian_product k s <=>\n        EXTENSIONAL k x /\\ (!i. i IN k ==> x i IN s i)"),
  vREWRITE_TAC[cartesian_product; vIN_ELIM_THM]);;

let vCARTESIAN_PRODUCT = prove
 ((parse_term "!k s. cartesian_product k s =\n         {f:K->A | !i. f i IN (if i IN k then s i else {ARB})}"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[cartesian_product; vIN_ELIM_THM; vEXTENSIONAL] ---->
  vMESON_TAC[vIN_SING]);;

let vRESTRICTION_IN_CARTESIAN_PRODUCT = prove
 ((parse_term "!k s (f:K->A).\n        RESTRICTION k f IN cartesian_product k s <=>\n        !i. i IN k ==> (f i) IN (s i)"),
  vREWRITE_TAC[vRESTRICTION; cartesian_product; vEXTENSIONAL; vIN_ELIM_THM] ---->
  vSET_TAC[]);;

let vCARTESIAN_PRODUCT_AS_RESTRICTIONS = prove
 ((parse_term "!k (s:K->A->bool).\n      cartesian_product k s =\n      {RESTRICTION k f |f| !i. i IN k ==> f i IN s i}"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET; vFORALL_IN_GSPEC] ---->
  vREWRITE_TAC[vRESTRICTION_IN_CARTESIAN_PRODUCT] ---->
  vX_GEN_TAC (parse_term "x:K->A") ---->
  vREWRITE_TAC[cartesian_product; vIN_ELIM_THM; vEXTENSIONAL] ---->
  vSTRIP_TAC ----> vEXISTS_TAC (parse_term "x:K->A") ---->
  vASM_REWRITE_TAC[vFUN_EQ_THM; vRESTRICTION] ----> vASM_MESON_TAC[]);;

let vCARTESIAN_PRODUCT_EQ_EMPTY = prove
 ((parse_term "!k s:K->A->bool.\n        cartesian_product k s = {} <=> ?i. i IN k /\\ s i = {}"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vLAND_CONV [vEXTENSION] ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "(?i. i IN k /\\ s i = {}) <=> ~(!i. ?a. i IN k ==> a IN s i)")] ---->
  vREWRITE_TAC[vSKOLEM_THM; vNOT_EXISTS_THM; cartesian_product] ---->
  vREWRITE_TAC[vIN_ELIM_THM; vNOT_IN_EMPTY] ----> vEQ_TAC ---->
  vDISCH_TAC ----> vX_GEN_TAC (parse_term "f:K->A") ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "\\i. if i IN k then (f:K->A) i else ARB")) ---->
  vREWRITE_TAC[vEXTENSIONAL; vIN_ELIM_THM] ----> vSIMP_TAC[]);;

let vCARTESIAN_PRODUCT_EMPTY = prove
 ((parse_term "!s. cartesian_product {} s = {(\\i. ARB)}"),
  vREWRITE_TAC[vCARTESIAN_PRODUCT; vNOT_IN_EMPTY; vEXTENSION] ---->
  vREWRITE_TAC[vIN_ELIM_THM; vIN_SING] ----> vREWRITE_TAC[vFUN_EQ_THM]);;

let vCARTESIAN_PRODUCT_EQ_MEMBERS = prove
 ((parse_term "!k s x y:K->A.\n        x IN cartesian_product k s /\\ y IN cartesian_product k s /\\\n        (!i. i IN k ==> x i = y i)\n        ==> x = y"),
  vREWRITE_TAC[cartesian_product; vIN_ELIM_THM] ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vEXTENSIONAL_EQ ---->
  vEXISTS_TAC (parse_term "k:K->bool") ----> vASM_REWRITE_TAC[vIN]);;

let vCARTESIAN_PRODUCT_EQ_MEMBERS_EQ = prove
 ((parse_term "!k s x y.\n        x IN cartesian_product k s /\\\n        y IN cartesian_product k s\n        ==> (x = y <=> !i. i IN k ==> x i = y i)"),
  vMESON_TAC[vCARTESIAN_PRODUCT_EQ_MEMBERS]);;

let vSUBSET_CARTESIAN_PRODUCT = prove
 ((parse_term "!k s t:K->A->bool.\n        cartesian_product k s SUBSET cartesian_product k t <=>\n        cartesian_product k s = {} \\/ !i. i IN k ==> s i SUBSET t i"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "cartesian_product k (s:K->A->bool) = {}") ---->
  vASM_REWRITE_TAC[vEMPTY_SUBSET] ---->
  vREWRITE_TAC[vSUBSET; cartesian_product; vIN_ELIM_THM] ---->
  vEQ_TAC ++--> [vALL_TAC; vMESON_TAC[]] ----> vFIRST_X_ASSUM(vMP_TAC -|
    vGEN_REWRITE_RULE vRAND_CONV [vCARTESIAN_PRODUCT_EQ_EMPTY]) ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "~(?i. i IN k /\\ s i = {}) <=> (!i. ?a. i IN k ==> a IN s i)")] ---->
  vREWRITE_TAC[vSKOLEM_THM; vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC (parse_term "z:K->A") ----> vDISCH_TAC ----> vDISCH_TAC ---->
  vX_GEN_TAC (parse_term "i:K") ----> vDISCH_TAC ----> vX_GEN_TAC (parse_term "x:A") ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC
   (parse_term "(\\j. if j IN k then if j = i then x else z j else ARB):K->A")) ---->
  vREWRITE_TAC[vEXTENSIONAL; vIN_ELIM_THM] ----> vSIMP_TAC[] ---->
  vASM_MESON_TAC[]);;

let vCARTESIAN_PRODUCT_EQ = prove
 ((parse_term "!k s t:K->A->bool.\n        cartesian_product k s = cartesian_product k t <=>\n        cartesian_product k s = {} /\\ cartesian_product k t = {} \\/\n        !i. i IN k ==> s i = t i"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "!i. i IN k ==> (s:K->A->bool) i = t i") ---->
  vASM_REWRITE_TAC[] ++-->
   [vASM_SIMP_TAC[cartesian_product; vEXTENSION; vIN_ELIM_THM];
    vASM_CASES_TAC (parse_term "cartesian_product k (t:K->A->bool) = {}") ---->
    vASM_REWRITE_TAC[] ---->
    vASM_CASES_TAC (parse_term "cartesian_product k (s:K->A->bool) = {}") ---->
    vASM_REWRITE_TAC[] ---->
    vASM_REWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET_CARTESIAN_PRODUCT] ---->
    vASM vSET_TAC[]]);;

let vINTER_CARTESIAN_PRODUCT = prove
 ((parse_term "!k s t:K->A->bool.\n        (cartesian_product k s) INTER (cartesian_product k t) =\n        cartesian_product k (\\i. s i INTER t i)"),
  vREWRITE_TAC[vEXTENSION; cartesian_product; vIN_INTER; vIN_ELIM_THM] ---->
  vSET_TAC[]);;

let vCARTESIAN_PRODUCT_UNIV = prove
 ((parse_term "cartesian_product (:K) (\\i. (:A)) = (:K->A)"),
  vREWRITE_TAC[vEXTENSION; vIN_UNIV; cartesian_product; vIN_ELIM_THM] ---->
  vREWRITE_TAC[vEXTENSIONAL_UNIV]);;

let vCARTESIAN_PRODUCT_SINGS = prove
 ((parse_term "!k x:K->A. EXTENSIONAL k x ==> cartesian_product k (\\i. {x i}) = {x}"),
  vREWRITE_TAC[cartesian_product; vIN_SING] ---->
  vREWRITE_TAC[vEXTENSION; vEXTENSIONAL; vIN_ELIM_THM; vIN_SING] ---->
  vREWRITE_TAC[vFUN_EQ_THM] ----> vMESON_TAC[]);;

let vCARTESIAN_PRODUCT_SINGS_GEN = prove
 ((parse_term "!k x. cartesian_product k (\\i. {x i}) = {RESTRICTION k x}"),
  vREWRITE_TAC[cartesian_product; vIN_SING] ---->
  vREWRITE_TAC[vEXTENSION; vEXTENSIONAL; vIN_ELIM_THM; vIN_SING] ---->
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION] ----> vMESON_TAC[]);;

let vIMAGE_PROJECTION_CARTESIAN_PRODUCT = prove
 ((parse_term "!k s:K->A->bool i.\n        IMAGE (\\x. x i) (cartesian_product k s) =\n        if cartesian_product k s = {} then {}\n        else if i IN k then s i else {ARB}"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "cartesian_product k (s:K->A->bool) = {}") ---->
  vASM_REWRITE_TAC[vIMAGE_CLAUSES] ---->
  vREWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET; vFORALL_IN_IMAGE] ---->
  vSIMP_TAC[vCARTESIAN_PRODUCT; vIN_ELIM_THM] ---->
  vX_GEN_TAC (parse_term "x:A") ----> vDISCH_TAC ----> vFIRST_X_ASSUM(vMP_TAC -|
    vGEN_REWRITE_RULE vRAND_CONV [vCARTESIAN_PRODUCT_EQ_EMPTY]) ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "~(?i. i IN k /\\ s i = {}) <=> (!i. ?a. i IN k ==> a IN s i)")] ---->
  vREWRITE_TAC[vSKOLEM_THM; vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC (parse_term "z:K->A") ----> vDISCH_TAC ---->
  vREWRITE_TAC[vIN_IMAGE; vIN_ELIM_THM] ---->
  vEXISTS_TAC
   (parse_term "\\j. if j = i then x else if j IN k then (z:K->A) j else ARB") ---->
  vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[vIN_SING]);;

let vFORALL_CARTESIAN_PRODUCT_ELEMENTS = prove
 ((parse_term "!P k s:K->A->bool.\n        (!z i. z IN cartesian_product k s /\\ i IN k ==> P i (z i)) <=>\n        cartesian_product k s = {} \\/\n        (!i x. i IN k /\\ x IN s i ==> P i x)"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "cartesian_product k (s:K->A->bool) = {}") ---->
  vASM_REWRITE_TAC[vNOT_IN_EMPTY] ---->
  vREWRITE_TAC[cartesian_product; vIN_ELIM_THM] ----> vEQ_TAC ++-->
   [vDISCH_TAC; vMESON_TAC[]] ---->
  vFIRST_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vRAND_CONV
   [vCARTESIAN_PRODUCT_EQ_EMPTY]) ---->
  vREWRITE_TAC[vSKOLEM_THM; vLEFT_IMP_EXISTS_THM; vSET_RULE
     (parse_term "~(?i. i IN k /\\ s i = {}) <=> (!i. ?x. i IN k ==> x IN s i)")] ---->
  vX_GEN_TAC (parse_term "z:K->A") ----> vDISCH_TAC ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "i:K"); (parse_term "x:A")] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL
   [(parse_term "\\j. if j = i then x else if j IN k then (z:K->A) j else ARB"); (parse_term "i:K")]) ---->
  vASM_REWRITE_TAC[vEXTENSIONAL; vIN_ELIM_THM] ----> vASM_MESON_TAC[]);;

let vFORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ = prove
 ((parse_term "!P k s.\n        ~(cartesian_product k s = {})\n        ==> ((!i x. i IN k /\\ x IN s i ==> P i x) <=>\n             !z i. z IN cartesian_product k s /\\ i IN k ==> P i (z i))"),
  vSIMP_TAC[vFORALL_CARTESIAN_PRODUCT_ELEMENTS]);;

let vEXISTS_CARTESIAN_PRODUCT_ELEMENT = prove
 ((parse_term "!P k s:K->A->bool.\n        (?z. z IN cartesian_product k s /\\ (!i. i IN k ==> P i (z i))) <=>\n        (!i. i IN k ==> ?x. x IN (s i) /\\ P i x)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vCARTESIAN_PRODUCT_AS_RESTRICTIONS; vEXISTS_IN_GSPEC] ---->
  vSIMP_TAC[vRESTRICTION] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Product of a family of maps.                                              *)
(* ------------------------------------------------------------------------- *)

let product_map = new_definition
 (parse_term "product_map k (f:K->A->B) = \\x. RESTRICTION k (\\i. f i (x i))");;

let vPRODUCT_MAP_RESTRICTION = prove
 ((parse_term "!(f:K->A->B) k x.\n        product_map k f (RESTRICTION k x) = RESTRICTION k (\\i. f i (x i))"),
  vSIMP_TAC[product_map; vRESTRICTION; o_THM; vFUN_EQ_THM]);;

let vIMAGE_PRODUCT_MAP = prove
 ((parse_term "!(f:K->A->B) k s.\n        IMAGE (product_map k f) (cartesian_product k s) =\n        cartesian_product k (\\i. IMAGE (f i) (s i))"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vCARTESIAN_PRODUCT_AS_RESTRICTIONS] ---->
  vONCE_REWRITE_TAC[vSIMPLE_IMAGE_GEN] ---->
  vREWRITE_TAC[product_map; vGSYM vIMAGE_o; o_DEF] ---->
  vGEN_REWRITE_TAC vI [vEXTENSION] ----> vX_GEN_TAC (parse_term "g:K->B") ---->
  vREWRITE_TAC[vIN_IMAGE; vRESTRICTION; vIN_ELIM_THM] ---->
  vEQ_TAC ----> vSTRIP_TAC ---->
  vASM_REWRITE_TAC[vRESTRICTION_EXTENSION] ---->
  vASM vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Disjoint union construction for a family of sets.                         *)
(* ------------------------------------------------------------------------- *)

let disjoint_union = new_definition
 (parse_term "disjoint_union (k:K->bool) (s:K->A->bool) = { (i,x) | i IN k /\\ x IN s i}");;

let vSUBSET_DISJOINT_UNION = prove
 ((parse_term "!k (s:K->A->bool) t.\n        disjoint_union k s SUBSET disjoint_union k t <=>\n        !i. i IN k ==> s i SUBSET t i"),
  vREWRITE_TAC[vSUBSET; disjoint_union; vFORALL_IN_GSPEC] ---->
  vREWRITE_TAC[vIN_ELIM_PAIR_THM] ----> vSET_TAC[]);;

let vDISJOINT_UNION_EQ = prove
 ((parse_term "!k (s:K->A->bool) t.\n        disjoint_union k s = disjoint_union k t <=>\n        !i. i IN k ==> s i = t i"),
  vREWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET_DISJOINT_UNION] ---->
  vSET_TAC[]);;

let vSUBSET_DISJOINT_UNION_EXISTS = prove
 ((parse_term "!k (s:K->A->bool) u.\n        u SUBSET disjoint_union k s <=>\n        ?t. u = disjoint_union k t /\\ !i. i IN k ==> t i SUBSET s i"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC; vMESON_TAC[vSUBSET_DISJOINT_UNION]] ---->
  vEXISTS_TAC (parse_term "\\i. {x | (i,x) IN (u:K#A->bool)}") ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vSUBSET; vEXTENSION] ---->
  vREWRITE_TAC[disjoint_union; vFORALL_PAIR_THM; vIN_ELIM_PAIR_THM] ---->
  vSET_TAC[]);;

let vINTER_DISJOINT_UNION = prove
 ((parse_term "!k s t:K->A->bool.\n        (disjoint_union k s) INTER (disjoint_union k t) =\n        disjoint_union k (\\i. s i INTER t i)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vEXTENSION; disjoint_union; vIN_INTER; vIN_ELIM_THM] ---->
  vMESON_TAC[vPAIR_EQ]);;

let vUNION_DISJOINT_UNION = prove
 ((parse_term "!k s t:K->A->bool.\n        (disjoint_union k s) UNION (disjoint_union k t) =\n        disjoint_union k (\\i. s i UNION t i)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vEXTENSION; disjoint_union; vIN_UNION; vIN_ELIM_THM] ---->
  vMESON_TAC[vPAIR_EQ]);;

let vDISJOINT_UNION_EQ_EMPTY = prove
 ((parse_term "!k s:K->A->bool.\n        disjoint_union k s = {} <=> !i. i IN k ==> s i = {}"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; disjoint_union; vIN_ELIM_PAIR_THM;
              vNOT_IN_EMPTY] ---->
  vSET_TAC[]);;

let vDISJOINT_DISJOINT_UNION = prove
 ((parse_term "!k s t:K->A->bool.\n        DISJOINT (disjoint_union k s) (disjoint_union k t) =\n        !i. i IN k ==> DISJOINT (s i) (t i)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vDISJOINT; vINTER_DISJOINT_UNION; vDISJOINT_UNION_EQ_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of functions with bounded domain (support) and range.         *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_FUNSPACE = prove
 ((parse_term "!d n t:B->bool m s:A->bool.\n        s HAS_SIZE m /\\ t HAS_SIZE n\n        ==> {f | (!x. x IN s ==> f(x) IN t) /\\ (!x. ~(x IN s) ==> (f x = d))}\n            HAS_SIZE (n EXP m)"),
  vGEN_TAC ----> vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[vHAS_SIZE_CLAUSES] ++-->
   [vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[vNOT_IN_EMPTY; vEXP] ---->
    vCONV_TAC vHAS_SIZE_CONV ----> vEXISTS_TAC (parse_term "(\\x. d):A->B") ---->
    vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vIN_SING] ----> vREWRITE_TAC[vFUN_EQ_THM];
    vREWRITE_TAC[vLEFT_IMP_EXISTS_THM; vLEFT_AND_EXISTS_THM]] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "s0:A->bool"); (parse_term "a:A"); (parse_term "s:A->bool")] ---->
  vSTRIP_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "s:A->bool")) ---->
  vASM_REWRITE_TAC[] ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN
   (parse_term "{f:A->B | (!x. x IN a INSERT s ==> f x IN t) /\\\n              (!x. ~(x IN a INSERT s) ==> (f x = d))} =\n    IMAGE (\\(b,g) x. if x = a then b else g(x))\n          {b,g | b IN t /\\\n                 g IN {f | (!x. x IN s ==> f x IN t) /\\\n                           (!x. ~(x IN s) ==> (f x = d))}}")
  vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vFORALL_PAIR_THM; vIN_ELIM_THM;
                vEXISTS_PAIR_THM] ---->
    vREWRITE_TAC[vPAIR_EQ; vCONJ_ASSOC; vONCE_REWRITE_RULE[vCONJ_SYM]
     vUNWIND_THM1] ---->
    vX_GEN_TAC (parse_term "f:A->B") ----> vREWRITE_TAC[vIN_INSERT] ----> vEQ_TAC ++-->
     [vSTRIP_TAC ----> vMAP_EVERY vEXISTS_TAC
       [(parse_term "(f:A->B) a"); (parse_term "\\x. if x IN s then (f:A->B) x else d")] ---->
      vREWRITE_TAC[vFUN_EQ_THM] ----> vASM_MESON_TAC[];
      vDISCH_THEN(vX_CHOOSE_THEN (parse_term "b:B") (vX_CHOOSE_THEN (parse_term "g:A->B")
        vSTRIP_ASSUME_TAC)) ---->
      vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[]];
    vALL_TAC] ---->
  vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ----> vASM_SIMP_TAC[vEXP; vHAS_SIZE_PRODUCT] ---->
  vREWRITE_TAC[vFORALL_PAIR_THM; vIN_ELIM_THM; vPAIR_EQ; vCONJ_ASSOC] ---->
  vREWRITE_TAC[vONCE_REWRITE_RULE[vCONJ_SYM] vUNWIND_THM1] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ---->
  vREWRITE_TAC[vFUN_EQ_THM] ----> vREPEAT vGEN_TAC ---->
  vSTRIP_TAC ----> vCONJ_TAC ++-->
   [vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "a:A")) ----> vREWRITE_TAC[];
    vX_GEN_TAC (parse_term "x:A") ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "x:A")) ---->
    vASM_MESON_TAC[]]);;

let vCARD_FUNSPACE = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t\n         ==> (CARD {f | (!x. x IN s ==> f(x) IN t) /\\\n                        (!x. ~(x IN s) ==> (f x = d))} =\n              (CARD t) EXP (CARD s))"),
  vMESON_TAC[vHAS_SIZE_FUNSPACE; vHAS_SIZE]);;

let vFINITE_FUNSPACE = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t\n         ==> FINITE {f | (!x. x IN s ==> f(x) IN t) /\\\n                         (!x. ~(x IN s) ==> (f x = d))}"),
  vMESON_TAC[vHAS_SIZE_FUNSPACE; vHAS_SIZE]);;

let vHAS_SIZE_FUNSPACE_UNIV = prove
 ((parse_term "!m n. (:A) HAS_SIZE m /\\ (:B) HAS_SIZE n ==> (:A->B) HAS_SIZE (n EXP m)"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vHAS_SIZE_FUNSPACE) ---->
  vREWRITE_TAC[vIN_UNIV; vUNIV_GSPEC]);;

let vCARD_FUNSPACE_UNIV = prove
 ((parse_term "FINITE(:A) /\\ FINITE(:B) ==> CARD(:A->B) = CARD(:B) EXP CARD(:A)"),
  vMESON_TAC[vHAS_SIZE_FUNSPACE_UNIV; vHAS_SIZE]);;

let vFINITE_FUNSPACE_UNIV = prove
 ((parse_term "FINITE(:A) /\\ FINITE(:B) ==> FINITE(:A->B)"),
  vMESON_TAC[vHAS_SIZE_FUNSPACE_UNIV; vHAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of type bool.                                                 *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_BOOL = prove
 ((parse_term "(:bool) HAS_SIZE 2"),
  vSUBGOAL_THEN (parse_term "(:bool) = {F,T}") vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_INSERT] ----> vCONV_TAC vTAUT;
    vSIMP_TAC[vHAS_SIZE; vCARD_CLAUSES; vFINITE_INSERT; vFINITE_EMPTY; vARITH;
             vIN_SING; vNOT_IN_EMPTY]]);;

let vCARD_BOOL = prove
 ((parse_term "CARD(:bool) = 2"),
  vMESON_TAC[vHAS_SIZE_BOOL; vHAS_SIZE]);;

let vFINITE_BOOL = prove
 ((parse_term "FINITE(:bool)"),
  vMESON_TAC[vHAS_SIZE_BOOL; vHAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Hence cardinality of powerset.                                            *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_POWERSET = prove
 ((parse_term "!(s:A->bool) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 EXP n)"),
  vREPEAT vSTRIP_TAC ----> vSUBGOAL_THEN
   (parse_term "{t | t SUBSET s} =\n    {f | (!x:A. x IN s ==> f(x) IN UNIV) /\\ (!x. ~(x IN s) ==> (f x = F))}")
  vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vIN_UNIV; vSUBSET; vIN; vCONTRAPOS_THM];
    vMATCH_MP_TAC vHAS_SIZE_FUNSPACE ----> vASM_REWRITE_TAC[] ---->
    vCONV_TAC vHAS_SIZE_CONV ----> vMAP_EVERY vEXISTS_TAC [(parse_term "T"); (parse_term "F")] ---->
    vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_INSERT; vNOT_IN_EMPTY] ---->
    vCONV_TAC vTAUT]);;

let vCARD_POWERSET = prove
 ((parse_term "!s:A->bool. FINITE s ==> (CARD {t | t SUBSET s} = 2 EXP (CARD s))"),
  vMESON_TAC[vHAS_SIZE_POWERSET; vHAS_SIZE]);;

let vFINITE_POWERSET = prove
 ((parse_term "!s:A->bool. FINITE s ==> FINITE {t | t SUBSET s}"),
  vMESON_TAC[vHAS_SIZE_POWERSET; vHAS_SIZE]);;

let vFINITE_POWERSET_EQ = prove
 ((parse_term "!s:A->bool. FINITE {t | t SUBSET s} <=> FINITE s"),
  vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vFINITE_POWERSET] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN (parse_term "FINITE(IMAGE (\\x:A. {x}) s)") vMP_TAC ++-->
   [vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vREWRITE_RULE[vIMP_CONJ]
        vFINITE_SUBSET)) ---->
    vSIMP_TAC[vSUBSET; vFORALL_IN_IMAGE; vIN_ELIM_THM; vIN_SING];
    vMATCH_MP_TAC vEQ_IMP ----> vMATCH_MP_TAC vFINITE_IMAGE_INJ_EQ ---->
    vSET_TAC[]]);;

let vFINITE_RESTRICTED_SUBSETS = prove
 ((parse_term "!P s:A->bool. FINITE s ==> FINITE {t | t SUBSET s /\\ P t}"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC (parse_term "{t:A->bool | t SUBSET s}") ---->
  vASM_SIMP_TAC[vFINITE_POWERSET] ----> vSET_TAC[]);;

let vFINITE_UNIONS = prove
 ((parse_term "!s:(A->bool)->bool.\n        FINITE(UNIONS s) <=> FINITE s /\\ (!t. t IN s ==> FINITE t)"),
  vGEN_TAC ----> vASM_CASES_TAC (parse_term "FINITE(s:(A->bool)->bool)") ---->
  vASM_SIMP_TAC[vFINITE_FINITE_UNIONS] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vFINITE_POWERSET) ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vCONTRAPOS_THM] ---->
  vMATCH_MP_TAC(vREWRITE_RULE[vIMP_CONJ_ALT] vFINITE_SUBSET) ----> vSET_TAC[]);;

let vFINITE_CARD_LE_UNIONS = prove
 ((parse_term "!s (t:A->B->bool) m n.\n        (!x. x IN s ==> FINITE(t x) /\\ CARD(t x) <= n) /\\\n        FINITE s /\\ CARD s <= m\n        ==> FINITE(UNIONS {t x | x IN s}) /\\\n            CARD(UNIONS {t x | x IN s}) <= m * n"),
  vREPEAT vSTRIP_TAC ---->
  vASM_SIMP_TAC[vFINITE_UNIONS; vFORALL_IN_GSPEC; vFINITE_IMAGE; vSIMPLE_IMAGE] ---->
  vTRANS_TAC vLE_TRANS (parse_term "CARD(s:A->bool) * n") ---->
  vASM_REWRITE_TAC[vGSYM vSIMPLE_IMAGE; vLE_MULT_RCANCEL] ---->
  vMATCH_MP_TAC vCARD_UNIONS_LE ----> vASM_REWRITE_TAC[vHAS_SIZE]);;

let vPOWERSET_CLAUSES = prove
 ((parse_term "{s | s SUBSET {}} = {{}} /\\\n   (!a:A t. {s | s SUBSET (a INSERT t)} =\n            {s | s SUBSET t} UNION IMAGE (\\s. a INSERT s) {s | s SUBSET t})"),
  vREWRITE_TAC[vSUBSET_INSERT_DELETE; vSUBSET_EMPTY; vSING_GSPEC] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "a:A"); (parse_term "t:A->bool")] ---->
  vMATCH_MP_TAC vSUBSET_ANTISYM ----> vREWRITE_TAC[vUNION_SUBSET] ---->
  vONCE_REWRITE_TAC[vSUBSET] ---->
  vREWRITE_TAC[vFORALL_IN_IMAGE; vFORALL_IN_GSPEC] ---->
  vREWRITE_TAC[vIN_ELIM_THM; vIN_UNION; vIN_IMAGE] ---->
  vCONJ_TAC ++--> [vALL_TAC; vSET_TAC[]] ---->
  vX_GEN_TAC (parse_term "s:A->bool") ---->
  vASM_CASES_TAC (parse_term "(a:A) IN s") ++--> [vALL_TAC; vASM vSET_TAC[]] ---->
  vSTRIP_TAC ----> vDISJ2_TAC ----> vEXISTS_TAC (parse_term "s DELETE (a:A)") ---->
  vASM vSET_TAC[]);;

let vFINITE_IMAGE_INFINITE = prove
 ((parse_term "!f:A->B s.\n        INFINITE s /\\ FINITE(IMAGE f s)\n        ==> ?a. a IN s /\\ INFINITE {x | x IN s /\\ f x = f a}"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ_ALT] ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC vI [vGSYM vCONTRAPOS_THM] ---->
  vREWRITE_TAC[vNOT_EXISTS_THM; vINFINITE; vTAUT (parse_term "~(p /\\ q) <=> p ==> ~q")] ---->
  vDISCH_TAC ---->
  vSUBGOAL_THEN (parse_term "s = UNIONS {{x | x IN s /\\ (f:A->B) x = y} |y| y IN IMAGE f s}")
  vSUBST1_TAC ++--> [vREWRITE_TAC[vUNIONS_GSPEC] ----> vSET_TAC[]; vALL_TAC] ---->
  vASM_SIMP_TAC[vFINITE_UNIONS; vSIMPLE_IMAGE; vFINITE_IMAGE; vFORALL_IN_IMAGE]);;

let vFINITE_RESTRICTED_POWERSET = prove
 ((parse_term "!(s:A->bool) n.\n        FINITE {t | t SUBSET s /\\ t HAS_SIZE n} <=>\n        FINITE s \\/ n = 0"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[] ++-->
   [vREWRITE_TAC[vHAS_SIZE_0; vSET_RULE (parse_term "t SUBSET s /\\ t = {} <=> t = {}")] ---->
    vREWRITE_TAC[vSING_GSPEC; vFINITE_SING];
    vASM_CASES_TAC (parse_term "FINITE(s:A->bool)") ----> vASM_REWRITE_TAC[] ++-->
     [vONCE_REWRITE_TAC[vSET_RULE
       (parse_term "{x | P x /\\ Q x} = {x | x IN {y | P y} /\\ Q x}")] ---->
      vASM_SIMP_TAC[vFINITE_RESTRICT; vFINITE_POWERSET];
      vDISCH_TAC ----> vSUBGOAL_THEN (parse_term "FINITE(s:A->bool)")
      vMP_TAC ++--> [vALL_TAC; vASM_REWRITE_TAC[]] ---->
      vMATCH_MP_TAC vFINITE_SUBSET ---->
      vEXISTS_TAC (parse_term "UNIONS {t:A->bool | t SUBSET s /\\ t HAS_SIZE n}") ---->
      vCONJ_TAC ++-->
       [vASM_SIMP_TAC[vFINITE_UNIONS; vFORALL_IN_GSPEC] ----> vSIMP_TAC[vHAS_SIZE];
        vGEN_REWRITE_TAC vI [vSUBSET] ----> vX_GEN_TAC (parse_term "x:A") ----> vDISCH_TAC ---->
        vREWRITE_TAC[vUNIONS_GSPEC; vIN_ELIM_THM] ---->
        vONCE_REWRITE_TAC[vSET_RULE (parse_term "P /\\ x IN t <=> {x} SUBSET t /\\ P")] ---->
        vMATCH_MP_TAC vCHOOSE_SUBSET_BETWEEN ---->
        vASM_REWRITE_TAC[vSING_SUBSET; vFINITE_SING; vCARD_SING] ---->
        vASM_SIMP_TAC[vLE_1]]]]);;

let vFINITE_RESTRICTED_FUNSPACE = prove
 ((parse_term "!s:A->bool t:B->bool k.\n        FINITE s /\\ FINITE t\n        ==> FINITE {f | IMAGE f s SUBSET t /\\ {x | ~(f x = k x)} SUBSET s}"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC
   (parse_term "IMAGE (\\u:(A#B)->bool x. if ?y. (x,y) IN u then @y. (x,y) IN u else k x)\n          {u | u SUBSET (s CROSS t)}") ---->
  vASM_SIMP_TAC[vFINITE_POWERSET; vFINITE_CROSS; vFINITE_IMAGE] ---->
  vGEN_REWRITE_TAC vI [vSUBSET] ----> vREWRITE_TAC[vFORALL_IN_GSPEC] ---->
  vX_GEN_TAC (parse_term "f:A->B") ----> vSTRIP_TAC ---->
  vREWRITE_TAC[vIN_IMAGE; vIN_ELIM_THM] ---->
  vEXISTS_TAC (parse_term "IMAGE (\\x. x,(f:A->B) x) {x | ~(f x = k x)}") ---->
  vASM_SIMP_TAC[vFINITE_IMAGE] ----> vCONJ_TAC ++-->
   [vALL_TAC;
    vREWRITE_TAC[vSUBSET; vFORALL_IN_IMAGE; vIN_ELIM_THM; vIN_CROSS] ---->
    vASM vSET_TAC[]] ---->
  vREWRITE_TAC[vFUN_EQ_THM] ----> vX_GEN_TAC (parse_term "x:A") ---->
  vREWRITE_TAC[vIN_IMAGE; vIN_ELIM_THM; vPAIR_EQ] ---->
  vREWRITE_TAC[vGSYM vCONJ_ASSOC; vUNWIND_THM1; vUNWIND_THM2] ---->
  vASM_CASES_TAC (parse_term "(f:A->B) x = k x") ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Set of numbers is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let vNUMSEG_CLAUSES_LT = prove
 ((parse_term "{i | i < 0} = {} /\\\n   (!k. {i | i < SUC k} = k INSERT {i | i < k})"),
  vREWRITE_TAC[vLT] ----> vSET_TAC[]);;

let vHAS_SIZE_NUMSEG_LT = prove
 ((parse_term "!n. {m | m < n} HAS_SIZE n"),
  vREWRITE_TAC[vHAS_SIZE] ----> vINDUCT_TAC ---->
  vASM_SIMP_TAC[vNUMSEG_CLAUSES_LT; vFINITE_EMPTY; vCARD_CLAUSES; vFINITE_INSERT;
               vIN_ELIM_THM; vLT_REFL]);;

let vCARD_NUMSEG_LT = prove
 ((parse_term "!n. CARD {m | m < n} = n"),
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vHAS_SIZE_NUMSEG_LT]);;

let vFINITE_NUMSEG_LT = prove
 ((parse_term "!n:num. FINITE {m | m < n}"),
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vHAS_SIZE_NUMSEG_LT]);;

let vNUMSEG_CLAUSES_LE = prove
 ((parse_term "{i | i <= 0} = {0} /\\\n   (!k. {i | i <= SUC k} = SUC k INSERT {i | i <= k})"),
  vREWRITE_TAC[vLE] ----> vSET_TAC[]);;

let vHAS_SIZE_NUMSEG_LE = prove
 ((parse_term "!n. {m | m <= n} HAS_SIZE (n + 1)"),
  vREWRITE_TAC[vGSYM vLT_SUC_LE; vHAS_SIZE_NUMSEG_LT; vADD1]);;

let vFINITE_NUMSEG_LE = prove
 ((parse_term "!n. FINITE {m | m <= n}"),
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vHAS_SIZE_NUMSEG_LE]);;

let vCARD_NUMSEG_LE = prove
 ((parse_term "!n. CARD {m | m <= n} = n + 1"),
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vHAS_SIZE_NUMSEG_LE]);;

let num_FINITE = prove
 ((parse_term "!s:num->bool. FINITE s <=> ?a. !x. x IN s ==> x <= a"),
  vGEN_TAC ----> vEQ_TAC ++-->
   [vSPEC_TAC((parse_term "s:num->bool"),(parse_term "s:num->bool")) ---->
    vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
    vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ----> vMESON_TAC[vLE_CASES; vLE_TRANS];
    vDISCH_THEN(vX_CHOOSE_TAC (parse_term "n:num")) ----> vMATCH_MP_TAC vFINITE_SUBSET ---->
    vEXISTS_TAC (parse_term "{m:num | m <= n}") ----> vREWRITE_TAC[vFINITE_NUMSEG_LE] ---->
    vASM_SIMP_TAC[vSUBSET; vIN_ELIM_THM]]);;

let num_FINITE_AVOID = prove
 ((parse_term "!s:num->bool. FINITE(s) ==> ?a. ~(a IN s)"),
  vMESON_TAC[num_FINITE; vLT; vNOT_LT]);;

let num_INFINITE_EQ = prove
 ((parse_term "!s:num->bool. INFINITE s <=> !N. ?n. N <= n /\\ n IN s"),
  vGEN_TAC ----> vREWRITE_TAC[vINFINITE; num_FINITE] ---->
  vMESON_TAC[vNOT_LE; vLT_IMP_LE; vLE_SUC_LT]);;

let num_INFINITE = prove
 ((parse_term "INFINITE(:num)"),
  vREWRITE_TAC[vINFINITE] ----> vMESON_TAC[num_FINITE_AVOID; vIN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Set of strings is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let string_INFINITE = prove
 ((parse_term "INFINITE(:string)"),
  vMP_TAC num_INFINITE ----> vREWRITE_TAC[vINFINITE; vCONTRAPOS_THM] ---->
  vDISCH_THEN(vMP_TAC -| vISPEC (parse_term "LENGTH:string->num") -| vMATCH_MP vFINITE_IMAGE) ---->
  vMATCH_MP_TAC vEQ_IMP ----> vAP_TERM_TAC ---->
  vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_IMAGE] ----> vMESON_TAC[vLENGTH_REPLICATE]);;

(* ------------------------------------------------------------------------- *)
(* Non-trivial intervals of reals are infinite.                              *)
(* ------------------------------------------------------------------------- *)

let vFINITE_REAL_INTERVAL = prove
 ((parse_term "(!a. ~FINITE {x:real | a < x}) /\\\n   (!a. ~FINITE {x:real | a <= x}) /\\\n   (!b. ~FINITE {x:real | x < b}) /\\\n   (!b. ~FINITE {x:real | x <= b}) /\\\n   (!a b. FINITE {x:real | a < x /\\ x < b} <=> b <= a) /\\\n   (!a b. FINITE {x:real | a <= x /\\ x < b} <=> b <= a) /\\\n   (!a b. FINITE {x:real | a < x /\\ x <= b} <=> b <= a) /\\\n   (!a b. FINITE {x:real | a <= x /\\ x <= b} <=> b <= a)"),
  vSUBGOAL_THEN (parse_term "!a b. FINITE {x:real | a < x /\\ x < b} <=> b <= a")
  vASSUME_TAC ++-->
   [vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_NOT_LT] ---->
    vASM_CASES_TAC (parse_term "a:real < b") ---->
    vASM_SIMP_TAC[vREAL_ARITH (parse_term "~(a:real < b) ==> ~(a < x /\\ x < b)")] ---->
    vREWRITE_TAC[vEMPTY_GSPEC; vFINITE_EMPTY] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP (vREWRITE_RULE[vIMP_CONJ] vFINITE_SUBSET)) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "IMAGE (\\n. a + (b - a) / (&n + &2)) (:num)")) ---->
    vREWRITE_TAC[vSUBSET; vFORALL_IN_IMAGE; vIN_UNIV; vIN_ELIM_THM] ---->
    vSIMP_TAC[vREAL_LT_ADDR; vREAL_ARITH (parse_term "a + x / y < b <=> x / y < b - a")] ---->
    vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_SUB_LT; vREAL_LT_LDIV_EQ; vNOT_IMP;
                 vREAL_ARITH (parse_term "&0:real < &n + &2")] ---->
    vREWRITE_TAC[vREAL_ARITH (parse_term "x:real < x * (n + &2) <=> &0 < x * (n + &1)")] ---->
    vASM_SIMP_TAC[vREAL_SUB_LT; vREAL_LT_MUL; vREAL_ARITH (parse_term "&0:real < &n + &1")] ---->
    vMP_TAC num_INFINITE ----> vREWRITE_TAC[vINFINITE] ---->
    vMATCH_MP_TAC vEQ_IMP ----> vAP_TERM_TAC ----> vCONV_TAC vSYM_CONV ---->
    vMATCH_MP_TAC vFINITE_IMAGE_INJ_EQ ---->
    vASM_SIMP_TAC[vREAL_OF_NUM_EQ; vREAL_FIELD
     (parse_term "a < b ==> (a + (b - a) / (&n + &2) = a + (b - a) / (&m + &2) <=>\n                 &n:real = &m)")];
    vALL_TAC] ---->
  vASM_REWRITE_TAC[] ----> vREPEAT vCONJ_TAC ----> vREPEAT vGEN_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "{x:real | a < x /\\ x < a + &1}") -|
        vMATCH_MP(vREWRITE_RULE[vIMP_CONJ] vFINITE_SUBSET)) ---->
    vASM_REWRITE_TAC[vSUBSET; vIN_ELIM_THM] ----> vREAL_ARITH_TAC;
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "{x:real | a < x /\\ x < a + &1}") -|
        vMATCH_MP(vREWRITE_RULE[vIMP_CONJ] vFINITE_SUBSET)) ---->
    vASM_REWRITE_TAC[vSUBSET; vIN_ELIM_THM] ----> vREAL_ARITH_TAC;
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "{x:real | b - &1 < x /\\ x < b}") -|
        vMATCH_MP(vREWRITE_RULE[vIMP_CONJ] vFINITE_SUBSET)) ---->
    vASM_REWRITE_TAC[vSUBSET; vIN_ELIM_THM] ----> vREAL_ARITH_TAC;
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "{x:real | b - &1 < x /\\ x < b}") -|
        vMATCH_MP(vREWRITE_RULE[vIMP_CONJ] vFINITE_SUBSET)) ---->
    vASM_REWRITE_TAC[vSUBSET; vIN_ELIM_THM] ----> vREAL_ARITH_TAC;
    vREWRITE_TAC[vREAL_ARITH
     (parse_term "a:real <= x /\\ x < b <=> (a < x /\\ x < b) \\/ ~(b <= a) /\\ x = a")];
    vREWRITE_TAC[vREAL_ARITH
     (parse_term "a:real < x /\\ x <= b <=> (a < x /\\ x < b) \\/ ~(b <= a) /\\ x = b")];
    vASM_CASES_TAC (parse_term "b:real = a") ---->
    vASM_SIMP_TAC[vREAL_LE_ANTISYM; vREAL_LE_REFL; vSING_GSPEC; vFINITE_SING] ---->
    vASM_SIMP_TAC[vREAL_ARITH
     (parse_term "~(b:real = a) ==>\n        (a <= x /\\ x <= b <=> (a < x /\\ x < b) \\/ ~(b <= a) /\\ x = a \\/\n        ~(b <= a) /\\ x = b)")]] ---->
  vASM_REWRITE_TAC[vFINITE_UNION; vSET_RULE
   (parse_term "{x | p x \\/ q x} = {x | p x} UNION {x | q x}")] ---->
  vASM_CASES_TAC (parse_term "b:real <= a") ---->
  vASM_REWRITE_TAC[vEMPTY_GSPEC; vFINITE_EMPTY]);;

let real_INFINITE = prove
 ((parse_term "INFINITE(:real)"),
  vREWRITE_TAC[vINFINITE] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "{x:real | &0 <= x}") -|
        vMATCH_MP(vREWRITE_RULE[vIMP_CONJ] vFINITE_SUBSET)) ---->
  vREWRITE_TAC[vFINITE_REAL_INTERVAL; vSUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Indexing of finite sets and enumeration of subsets of N in order.         *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_INDEX = prove
 ((parse_term "!s n. s HAS_SIZE n\n         ==> ?f:num->A. (!m. m < n ==> f(m) IN s) /\\\n                        (!x. x IN s ==> ?!m. m < n /\\ (f m = x))"),
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ----> vINDUCT_TAC ---->
  vSIMP_TAC[vHAS_SIZE_0; vHAS_SIZE_SUC; vLT; vNOT_IN_EMPTY] ---->
  vX_GEN_TAC (parse_term "s:A->bool") ----> vREWRITE_TAC[vEXTENSION; vNOT_IN_EMPTY] ---->
  vREWRITE_TAC[vNOT_FORALL_THM] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "a:A")) (vMP_TAC -| vSPEC (parse_term "a:A"))) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "s DELETE (a:A)")) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "f:num->A") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "\\m:num. if m < n then f(m) else a:A") ----> vCONJ_TAC ++-->
   [vGEN_TAC ----> vREWRITE_TAC[] ----> vCOND_CASES_TAC ---->
    vASM_MESON_TAC[vIN_DELETE]; vALL_TAC] ---->
  vX_GEN_TAC (parse_term "x:A") ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "x:A")) ---->
  vASM_REWRITE_TAC[vIN_DELETE] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vCOND_ELIM_CONV) ---->
  vASM_CASES_TAC (parse_term "a:A = x") ----> vASM_SIMP_TAC[] ---->
  vASM_MESON_TAC[vLT_REFL; vIN_DELETE]);;

let vINFINITE_ENUMERATE = prove
 ((parse_term "!s:num->bool.\n       INFINITE s\n       ==> ?r:num->num. (!m n. m < n ==> r(m) < r(n)) /\\\n                        IMAGE r (:num) = s"),
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "!n:num. ?x. n <= x /\\ x IN s") vMP_TAC ++-->
   [vASM_MESON_TAC[vINFINITE; num_FINITE; vLT_IMP_LE; vNOT_LE];
    vGEN_REWRITE_TAC (vLAND_CONV -| vBINDER_CONV) [num_WOP]] ---->
  vREWRITE_TAC[vSKOLEM_THM; vLEFT_IMP_EXISTS_THM; vFORALL_AND_THM] ---->
  vREWRITE_TAC[vTAUT (parse_term "p ==> ~(q /\\ r) <=> q /\\ p ==> ~r")] ---->
  vX_GEN_TAC (parse_term "next:num->num") ----> vSTRIP_TAC ---->
  (vMP_TAC -| prove_recursive_functions_exist num_RECURSION)
   (parse_term "(f(0) = next 0) /\\ (!n. f(SUC n) = next(f n + 1))") ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC (parse_term "r:num->num") ----> vSTRIP_TAC ---->
  vMATCH_MP_TAC(vTAUT (parse_term "p /\\ (p ==> q) ==> p /\\ q")) ----> vCONJ_TAC ++-->
   [vGEN_TAC ----> vINDUCT_TAC ----> vASM_REWRITE_TAC[vLT] ---->
    vASM_MESON_TAC[vARITH_RULE (parse_term "m <= n /\\ n + 1 <= p ==> m < p"); vLE_LT];
    vDISCH_TAC] ---->
  vASM_REWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vFORALL_IN_IMAGE; vSUBSET] ---->
  vREWRITE_TAC[vIN_IMAGE; vIN_UNIV] ----> vCONJ_TAC ++-->
   [vINDUCT_TAC ----> vASM_MESON_TAC[]; vALL_TAC] ---->
  vMATCH_MP_TAC num_WF ----> vX_GEN_TAC (parse_term "n:num") ----> vREPEAT vSTRIP_TAC ---->
  vASM_CASES_TAC (parse_term "?m:num. m < n /\\ m IN s") ++-->
   [vMP_TAC(vSPEC (parse_term "\\m:num. m < n /\\ m IN s") num_MAX) ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC(vTAUT
     (parse_term "p /\\ (q ==> r) ==> (p <=> q) ==> r")) ---->
    vCONJ_TAC ++--> [vMESON_TAC[vLT_IMP_LE]; vALL_TAC] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "p:num") vSTRIP_ASSUME_TAC) ---->
    vSUBGOAL_THEN (parse_term "?q. p = (r:num->num) q") (vCHOOSE_THEN vSUBST_ALL_TAC) ++-->
     [vASM_MESON_TAC[]; vEXISTS_TAC (parse_term "SUC q")] ---->
    vASM_REWRITE_TAC[vGSYM vLE_ANTISYM; vGSYM vNOT_LT] ---->
    vASM_MESON_TAC[vNOT_LE; vARITH_RULE (parse_term "r < p <=> r + 1 <= p")];
    vEXISTS_TAC (parse_term "0") ----> vASM_REWRITE_TAC[vGSYM vLE_ANTISYM; vGSYM vNOT_LT] ---->
    vASM_MESON_TAC[vLE_0]]);;

let vINFINITE_ENUMERATE_EQ = prove
 ((parse_term "!s:num->bool.\n     INFINITE s <=> ?r. (!m n:num. m < n ==> r m < r n) /\\ IMAGE r (:num) = s"),
  vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vINFINITE_ENUMERATE] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "r:num->num") (vSTRIP_ASSUME_TAC -| vGSYM)) ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vINFINITE_IMAGE ---->
  vREWRITE_TAC[num_INFINITE; vIN_UNIV] ---->
  vMATCH_MP_TAC vWLOG_LT ----> vASM_MESON_TAC[vLT_REFL]);;

let vINFINITE_ENUMERATE_SUBSET = prove
 ((parse_term "!s. INFINITE s <=>\n       ?f:num->A. (!x. f x IN s) /\\ (!x y. f x = f y ==> x = y)"),
  vGEN_TAC ----> vEQ_TAC ----> vSTRIP_TAC ++-->
   [vSUBGOAL_THEN (parse_term "?f:num->A. !n. f n IN s /\\ !m. m < n ==> ~(f m = f n)")
    vMP_TAC ++-->
     [vMATCH_MP_TAC(vMATCH_MP vWF_REC_EXISTS vWF_num) ----> vSIMP_TAC[] ---->
      vMAP_EVERY vX_GEN_TAC [(parse_term "f:num->A"); (parse_term "n:num")] ----> vSTRIP_TAC ---->
      vFIRST_ASSUM(vMP_TAC -| vSPEC (parse_term "IMAGE (f:num->A) {m | m < n}") -|
        vMATCH_MP (vREWRITE_RULE[vIMP_CONJ] vINFINITE_DIFF_FINITE)) ---->
      vSIMP_TAC[vFINITE_IMAGE; vFINITE_NUMSEG_LT] ---->
      vDISCH_THEN(vMP_TAC -| vMATCH_MP vINFINITE_NONEMPTY) ----> vSET_TAC[];
      vMATCH_MP_TAC vMONO_EXISTS ----> vGEN_TAC ----> vSTRIP_TAC ---->
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vWLOG_LT ----> vASM vSET_TAC[]];
     vMATCH_MP_TAC vINFINITE_SUPERSET ---->
     vEXISTS_TAC (parse_term "IMAGE (f:num->A) (:num)") ---->
     vASM_REWRITE_TAC[vSUBSET; vFORALL_IN_IMAGE] ---->
     vASM_MESON_TAC[vINFINITE_IMAGE_INJ; num_INFINITE]]);;

(* ------------------------------------------------------------------------- *)
(* Mapping between finite sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

let set_of_list = new_recursive_definition list_RECURSION
  (parse_term "(set_of_list ([]:A list) = {}) /\\\n   (set_of_list (CONS (h:A) t) = h INSERT (set_of_list t))");;

let list_of_set = new_definition
  (parse_term "list_of_set s = @l. (set_of_list l = s) /\\ (LENGTH l = CARD s)");;

let vLIST_OF_SET_PROPERTIES = prove
 ((parse_term "!s:A->bool. FINITE(s)\n               ==> (set_of_list(list_of_set s) = s) /\\\n                   (LENGTH(list_of_set s) = CARD s)"),
  vREWRITE_TAC[list_of_set] ---->
  vCONV_TAC(vBINDER_CONV(vRAND_CONV vSELECT_CONV)) ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ----> vREPEAT vSTRIP_TAC ++-->
   [vEXISTS_TAC (parse_term "[]:A list") ----> vREWRITE_TAC[vCARD_CLAUSES; vLENGTH; set_of_list];
    vEXISTS_TAC (parse_term "CONS (x:A) l") ----> vASM_REWRITE_TAC[vLENGTH] ---->
    vASM_REWRITE_TAC[set_of_list] ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC
     [vMATCH_MP (vCONJUNCT2 vCARD_CLAUSES) th]) ---->
    vASM_REWRITE_TAC[]]);;

let vSET_OF_LIST_OF_SET = prove
 ((parse_term "!s. FINITE(s) ==> (set_of_list(list_of_set s) = s)"),
  vMESON_TAC[vLIST_OF_SET_PROPERTIES]);;

let vLENGTH_LIST_OF_SET = prove
 ((parse_term "!s. FINITE(s) ==> (LENGTH(list_of_set s) = CARD s)"),
  vMESON_TAC[vLIST_OF_SET_PROPERTIES]);;

let vMEM_LIST_OF_SET = prove
 ((parse_term "!s:A->bool. FINITE(s) ==> !x. MEM x (list_of_set s) <=> x IN s"),
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vSET_OF_LIST_OF_SET) ---->
  vDISCH_THEN(fun th -> vGEN_REWRITE_TAC (vBINDER_CONV -| funpow 2 vRAND_CONV)
    [vGSYM th]) ---->
  vSPEC_TAC((parse_term "list_of_set(s:A->bool)"),(parse_term "l:A list")) ---->
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vMEM; set_of_list; vNOT_IN_EMPTY] ---->
  vASM_REWRITE_TAC[vIN_INSERT]);;

let vFINITE_SET_OF_LIST = prove
 ((parse_term "!l. FINITE(set_of_list l)"),
  vLIST_INDUCT_TAC ----> vASM_SIMP_TAC[set_of_list; vFINITE_RULES]);;

let vIN_SET_OF_LIST = prove
 ((parse_term "!x l. x IN (set_of_list l) <=> MEM x l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY; vMEM; set_of_list] ---->
  vASM_MESON_TAC[]);;

let vSET_OF_LIST_APPEND = prove
 ((parse_term "!l1 l2. set_of_list(APPEND l1 l2) = set_of_list(l1) UNION set_of_list(l2)"),
  vREWRITE_TAC[vEXTENSION; vIN_SET_OF_LIST; vIN_UNION; vMEM_APPEND]);;

let vSET_OF_LIST_MAP = prove
 ((parse_term "!f l. set_of_list(MAP f l) = IMAGE f (set_of_list l)"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[set_of_list; vMAP; vIMAGE_CLAUSES]);;

let vSET_OF_LIST_EQ_EMPTY = prove
 ((parse_term "!l. set_of_list l = {} <=> l = []"),
  vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[set_of_list; vNOT_CONS_NIL; vNOT_INSERT_EMPTY]);;

let vLIST_OF_SET_EMPTY = prove
 ((parse_term "list_of_set {} = []"),
  vREWRITE_TAC[vGSYM vLENGTH_EQ_NIL] ---->
  vSIMP_TAC[vLENGTH_LIST_OF_SET; vFINITE_EMPTY; vCARD_CLAUSES]);;

let vLIST_OF_SET_SING = prove
 ((parse_term "!a:A. list_of_set {a} = [a]"),
  vGEN_TAC ----> vREWRITE_TAC[list_of_set] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vMATCH_MP_TAC list_INDUCT ----> vREWRITE_TAC[vNOT_CONS_NIL] ---->
  vSIMP_TAC[vLENGTH; vCARD_CLAUSES; vFINITE_EMPTY; vNOT_IN_EMPTY; vNOT_SUC] ---->
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vDISCH_THEN(vK vALL_TAC) ---->
  vSIMP_TAC[vLENGTH; set_of_list; vCONS_11; vSUC_INJ; vNOT_CONS_NIL; vNOT_SUC] ---->
  vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Mappings from finite set enumerations to lists (no "setification").       *)
(* ------------------------------------------------------------------------- *)

let dest_setenum =
  let fn = splitlist (dest_binary "INSERT") in
  fun tm -> let l,n = fn tm in
            if is_const n && fst(dest_const n) = "EMPTY" then l
            else failwith "dest_setenum: not a finite set enumeration";;

let is_setenum = can dest_setenum;;

let mk_setenum =
  let insert_atm = (parse_term "(INSERT):A->(A->bool)->(A->bool)")
  and nil_atm = (parse_term "(EMPTY):A->bool") in
  fun (l,ty) ->
    let insert_tm = inst [ty,aty] insert_atm
    and nil_tm = inst [ty,aty] nil_atm in
    itlist (mk_binop insert_tm) l nil_tm;;

let mk_fset l = mk_setenum(l,type_of(hd l));;

(* ------------------------------------------------------------------------- *)
(* Pairwise property over sets and lists.                                    *)
(* ------------------------------------------------------------------------- *)

let pairwise = new_definition
  (parse_term "pairwise r s <=> !x y. x IN s /\\ y IN s /\\ ~(x = y) ==> r x y");;

let vPAIRWISE_EMPTY = prove
 ((parse_term "!r. pairwise r {} <=> T"),
  vREWRITE_TAC[pairwise; vNOT_IN_EMPTY] ----> vMESON_TAC[]);;

let vPAIRWISE_SING = prove
 ((parse_term "!r x. pairwise r {x} <=> T"),
  vREWRITE_TAC[pairwise; vIN_SING] ----> vMESON_TAC[]);;

let vPAIRWISE_IMP = prove
 ((parse_term "!P Q s:A->bool.\n        pairwise P s /\\\n        (!x y. x IN s /\\ y IN s /\\ P x y /\\ ~(x = y) ==> Q x y)\n        ==> pairwise Q s"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vPAIRWISE_MONO = prove
 ((parse_term "!r s t. pairwise r s /\\ t SUBSET s ==> pairwise r t"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vPAIRWISE_AND = prove
 ((parse_term "!R R' s. pairwise R s /\\ pairwise R' s <=>\n            pairwise (\\x y. R x y /\\ R' x y) s"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vPAIRWISE_INSERT = prove
 ((parse_term "!r x s.\n        pairwise r (x INSERT s) <=>\n        (!y. y IN s /\\ ~(y = x) ==> r x y /\\ r y x) /\\\n        pairwise r s"),
  vREWRITE_TAC[pairwise; vIN_INSERT] ----> vMESON_TAC[]);;

let vPAIRWISE_INSERT_SYMMETRIC = prove
 ((parse_term "!r (x:A) s.\n        (!y. y IN s ==> (r x y <=> r y x))\n        ==> (pairwise r (x INSERT s) <=>\n             (!y. y IN s /\\ ~(y = x) ==> r x y) /\\ pairwise r s)"),
  vREWRITE_TAC[vPAIRWISE_INSERT] ----> vMESON_TAC[]);;

let vPAIRWISE_IMAGE = prove
 ((parse_term "!r f. pairwise r (IMAGE f s) <=>\n         pairwise (\\x y. ~(f x = f y) ==> r (f x) (f y)) s"),
  vREWRITE_TAC[pairwise; vIN_IMAGE] ----> vMESON_TAC[]);;

let vPAIRWISE_UNION = prove
 ((parse_term "!R s t. pairwise R (s UNION t) <=>\n           pairwise R s /\\ pairwise R t /\\\n           (!x y. x IN s DIFF t /\\ y IN t DIFF s ==> R x y /\\ R y x)"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vPAIRWISE_CHAIN_UNIONS = prove
 ((parse_term "!R:A->A->bool c.\n        (!s. s IN c ==> pairwise R s) /\\\n        (!s t. s IN c /\\ t IN c ==> s SUBSET t \\/ t SUBSET s)\n        ==> pairwise R (UNIONS c)"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vDIFF_UNIONS_PAIRWISE_DISJOINT = prove
 ((parse_term "!s t:(A->bool)->bool.\n        pairwise DISJOINT s /\\ t SUBSET s\n        ==> UNIONS s DIFF UNIONS t = UNIONS(s DIFF t)"),
  vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC(vSET_RULE (parse_term "t UNION u = s /\\ DISJOINT t u ==> s DIFF t = u")) ---->
  vCONJ_TAC ++-->
   [vREWRITE_TAC[vGSYM vUNIONS_UNION] ----> vAP_TERM_TAC ----> vASM vSET_TAC[];
    vREWRITE_TAC[vDISJOINT; vINTER_UNIONS; vEMPTY_UNIONS; vFORALL_IN_GSPEC] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [pairwise]) ---->
    vREWRITE_TAC[vDISJOINT; vIN_DIFF] ----> vREPEAT vSTRIP_TAC ---->
    vFIRST_X_ASSUM vMATCH_MP_TAC ---->
    vREPEAT(vCONJ_TAC ++--> [vASM vSET_TAC[]; vALL_TAC]) ----> vASM_MESON_TAC[]]);;

let vINTER_UNIONS_PAIRWISE_DISJOINT = prove
 ((parse_term "!s t:(A->bool)->bool.\n        pairwise DISJOINT (s UNION t)\n        ==> UNIONS s INTER UNIONS t = UNIONS(s INTER t)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vINTER_UNIONS; vSIMPLE_IMAGE; vUNIONS_IMAGE] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vEXTENSION] ---->
  vREWRITE_TAC[pairwise; vIN_UNIONS; vIN_INTER; vIN_ELIM_THM; vIN_UNION] ---->
  vDISCH_TAC ----> vX_GEN_TAC (parse_term "z:A") ----> vREWRITE_TAC[vRIGHT_AND_EXISTS_THM] ---->
  vEQ_TAC ++--> [vREWRITE_TAC[vLEFT_IMP_EXISTS_THM]; vMESON_TAC[]] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "u:A->bool"); (parse_term "v:A->bool")] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "u:A->bool"); (parse_term "v:A->bool")]) ---->
  vASM_CASES_TAC (parse_term "u:A->bool = v") ----> vASM_REWRITE_TAC[] ++-->
   [vASM_MESON_TAC[]; vASM vSET_TAC[]]);;

let vPSUBSET_UNIONS_PAIRWISE_DISJOINT = prove
 ((parse_term "!u v:(A->bool)->bool.\n        pairwise DISJOINT v /\\ u PSUBSET (v DELETE {})\n        ==> UNIONS u PSUBSET UNIONS v"),
  vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC(vSET_RULE (parse_term "u SUBSET v /\\ ~(v DIFF u = {}) ==> u PSUBSET v")) ---->
  vCONJ_TAC ++--> [vASM vSET_TAC[]; vALL_TAC] ---->
  vW(vMP_TAC -| vPART_MATCH (lhand -| rand)
      vDIFF_UNIONS_PAIRWISE_DISJOINT -| lhand -| rand -| snd) ---->
  vANTS_TAC ++--> [vASM vSET_TAC[]; vDISCH_THEN vSUBST1_TAC] ---->
  vREWRITE_TAC[vEMPTY_UNIONS] ---->
  vFIRST_ASSUM(vMP_TAC -| vCONJUNCT2 -| vGEN_REWRITE_RULE vI [vPSUBSET_ALT]) ---->
  vREWRITE_TAC[vIN_DELETE; vIN_DIFF] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Useful idioms for being a suitable union/intersection of somethings.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("UNION_OF",(20,"right"));;
parse_as_infix("INTERSECTION_OF",(20,"right"));;

let vUNION_OF = new_definition
 (parse_term "P UNION_OF Q =\n   \\s:A->bool. ?u. P u /\\ (!c. c IN u ==> Q c) /\\ UNIONS u = s");;

let vINTERSECTION_OF = new_definition
 (parse_term "P INTERSECTION_OF Q =\n   \\s:A->bool. ?u. P u /\\ (!c. c IN u ==> Q c) /\\ INTERS u = s");;

let vUNION_OF_INC = prove
 ((parse_term "!P Q s:A->bool. P {s} /\\ Q s ==> (P UNION_OF Q) s"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vUNION_OF] ---->
  vEXISTS_TAC (parse_term "{s:A->bool}") ----> vASM_SIMP_TAC[vUNIONS_1; vIN_SING]);;

let vINTERSECTION_OF_INC = prove
 ((parse_term "!P Q s:A->bool. P {s} /\\ Q s ==> (P INTERSECTION_OF Q) s"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vINTERSECTION_OF] ---->
  vEXISTS_TAC (parse_term "{s:A->bool}") ----> vASM_SIMP_TAC[vINTERS_1; vIN_SING]);;

let vUNION_OF_MONO = prove
 ((parse_term "!P Q Q' s:A->bool.\n        (P UNION_OF Q) s /\\ (!x. Q x ==> Q' x) ==> (P UNION_OF Q') s"),
  vREWRITE_TAC[vUNION_OF] ----> vMESON_TAC[]);;

let vINTERSECTION_OF_MONO = prove
 ((parse_term "!P Q Q' s:A->bool.\n        (P INTERSECTION_OF Q) s /\\ (!x. Q x ==> Q' x)\n        ==> (P INTERSECTION_OF Q') s"),
  vREWRITE_TAC[vINTERSECTION_OF] ----> vMESON_TAC[]);;

let vFORALL_UNION_OF = prove
 ((parse_term "(!s. (P UNION_OF Q) s ==> R s) <=>\n   (!t. P t /\\ (!c. c IN t ==> Q c) ==> R(UNIONS t))"),
  vREWRITE_TAC[vUNION_OF] ----> vMESON_TAC[]);;

let vFORALL_INTERSECTION_OF = prove
 ((parse_term "(!s. (P INTERSECTION_OF Q) s ==> R s) <=>\n   (!t. P t /\\ (!c. c IN t ==> Q c) ==> R(INTERS t))"),
  vREWRITE_TAC[vINTERSECTION_OF] ----> vMESON_TAC[]);;

let vUNION_OF_EMPTY = prove
 ((parse_term "!P Q:(A->bool)->bool. P {} ==> (P UNION_OF Q) {}"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vUNION_OF] ---->
  vEXISTS_TAC (parse_term "{}:(A->bool)->bool") ---->
  vASM_REWRITE_TAC[vUNIONS_0; vNOT_IN_EMPTY]);;

let vINTERSECTION_OF_EMPTY = prove
 ((parse_term "!P Q:(A->bool)->bool. P {} ==> (P INTERSECTION_OF Q) UNIV"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vINTERSECTION_OF] ---->
  vEXISTS_TAC (parse_term "{}:(A->bool)->bool") ---->
  vASM_REWRITE_TAC[vINTERS_0; vNOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* The ARBITRARY and FINITE cases of UNION_OF / INTERSECTION_OF              *)
(* ------------------------------------------------------------------------- *)

let vARBITRARY = new_definition
 (parse_term "ARBITRARY (s:(A->bool)->bool) <=> T");;

let vARBITRARY_UNION_OF_ALT = prove
 ((parse_term "!B s:A->bool.\n        (ARBITRARY UNION_OF B) s <=>\n        !x. x IN s ==>  ?u. u IN B /\\ x IN u /\\ u SUBSET s"),
  vGEN_TAC ----> vREWRITE_TAC[vFORALL_AND_THM; vTAUT
   (parse_term "(p <=> q) <=> (p ==> q) /\\ (q ==> p)")] ---->
  vREWRITE_TAC[vFORALL_UNION_OF; vARBITRARY] ---->
  vCONJ_TAC ++--> [vSET_TAC[]; vALL_TAC] ---->
  vX_GEN_TAC (parse_term "s:A->bool") ----> vDISCH_TAC ---->
  vREWRITE_TAC[vARBITRARY; vUNION_OF] ---->
  vEXISTS_TAC (parse_term "{u:A->bool | u IN B /\\ u SUBSET s}") ----> vASM vSET_TAC[]);;

let vARBITRARY_UNION_OF_EMPTY = prove
 ((parse_term "!P:(A->bool)->bool. (ARBITRARY UNION_OF P) {}"),
  vSIMP_TAC[vUNION_OF_EMPTY; vARBITRARY]);;

let vARBITRARY_INTERSECTION_OF_EMPTY = prove
 ((parse_term "!P:(A->bool)->bool. (ARBITRARY INTERSECTION_OF P) UNIV"),
  vSIMP_TAC[vINTERSECTION_OF_EMPTY; vARBITRARY]);;

let vARBITRARY_UNION_OF_INC = prove
 ((parse_term "!P s:A->bool. P s ==> (ARBITRARY UNION_OF P) s"),
  vSIMP_TAC[vUNION_OF_INC; vARBITRARY]);;

let vARBITRARY_INTERSECTION_OF_INC = prove
 ((parse_term "!P s:A->bool. P s ==> (ARBITRARY INTERSECTION_OF P) s"),
  vSIMP_TAC[vINTERSECTION_OF_INC; vARBITRARY]);;

let vARBITRARY_UNION_OF_COMPLEMENT = prove
 ((parse_term "!P s. (ARBITRARY UNION_OF P) s <=>\n         (ARBITRARY INTERSECTION_OF (\\s. P((:A) DIFF s))) ((:A) DIFF s)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vUNION_OF; vINTERSECTION_OF] ---->
  vEQ_TAC ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "u:(A->bool)->bool") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "IMAGE (\\c. (:A) DIFF c) u") ---->
  vASM_SIMP_TAC[vARBITRARY; vFORALL_IN_IMAGE; vCOMPL_COMPL] ---->
  vONCE_REWRITE_TAC[vUNIONS_INTERS; vINTERS_UNIONS] ---->
  vREWRITE_TAC[vSET_RULE (parse_term "{f y | y IN IMAGE g s} = IMAGE (\\x. f(g x)) s")] ---->
  vASM_REWRITE_TAC[vIMAGE_ID; vCOMPL_COMPL]);;

let vARBITRARY_INTERSECTION_OF_COMPLEMENT = prove
 ((parse_term "!P s. (ARBITRARY INTERSECTION_OF P) s <=>\n         (ARBITRARY UNION_OF (\\s. P((:A) DIFF s))) ((:A) DIFF s)"),
  vREWRITE_TAC[vARBITRARY_UNION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vETA_AX; vCOMPL_COMPL]);;

let vARBITRARY_UNION_OF_IDEMPOT = prove
 ((parse_term "!P:(A->bool)->bool.\n        ARBITRARY UNION_OF ARBITRARY UNION_OF P = ARBITRARY UNION_OF P"),
  vGEN_TAC ----> vREWRITE_TAC[vFUN_EQ_THM] ----> vX_GEN_TAC (parse_term "s:A->bool") ---->
  vEQ_TAC ----> vREWRITE_TAC[vARBITRARY_UNION_OF_INC] ---->
  vREWRITE_TAC[vUNION_OF; vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC (parse_term "u:(A->bool)->bool") ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC (vSUBST1_TAC -| vSYM)) ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vRIGHT_IMP_EXISTS_THM] ---->
  vREWRITE_TAC[vSKOLEM_THM; vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC (parse_term "f:(A->bool)->(A->bool)->bool") ----> vDISCH_TAC ---->
  vEXISTS_TAC
    (parse_term "IMAGE SND {s,t | s IN u /\\ t IN (f:(A->bool)->(A->bool)->bool) s}") ---->
  vASM_SIMP_TAC[vARBITRARY] ---->
  vREWRITE_TAC[vFORALL_IN_IMAGE; vFORALL_IN_GSPEC] ---->
  vCONJ_TAC ++--> [vASM vSET_TAC[]; vREWRITE_TAC[vUNIONS_IMAGE]] ---->
  vREWRITE_TAC[vEXISTS_IN_GSPEC] ----> vASM vSET_TAC[]);;

let vARBITRARY_INTERSECTION_OF_IDEMPOT = prove
 ((parse_term "!P:(A->bool)->bool.\n        ARBITRARY INTERSECTION_OF ARBITRARY INTERSECTION_OF P =\n        ARBITRARY INTERSECTION_OF P"),
  vREWRITE_TAC[vCOMPL_COMPL; vETA_AX; vREWRITE_RULE[vGSYM vFUN_EQ_THM; vETA_AX]
              vARBITRARY_INTERSECTION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vARBITRARY_UNION_OF_IDEMPOT]);;

let vARBITRARY_UNION_OF_UNIONS = prove
 ((parse_term "!P u:(A->bool)->bool.\n        (!s. s IN u ==> (ARBITRARY UNION_OF P) s)\n        ==> (ARBITRARY UNION_OF P) (UNIONS u)"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vARBITRARY_UNION_OF_IDEMPOT] ---->
  vONCE_REWRITE_TAC[vUNION_OF] ----> vREWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "u:(A->bool)->bool") ----> vASM_REWRITE_TAC[vARBITRARY]);;

let vARBITRARY_UNION_OF_UNION = prove
 ((parse_term "!P s t. (ARBITRARY UNION_OF P) s /\\ (ARBITRARY UNION_OF P) t\n           ==> (ARBITRARY UNION_OF P) (s UNION t)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vUNIONS_2] ---->
  vMATCH_MP_TAC vARBITRARY_UNION_OF_UNIONS ---->
  vASM_REWRITE_TAC[vARBITRARY; vFORALL_IN_INSERT] ---->
  vREWRITE_TAC[vARBITRARY; vNOT_IN_EMPTY]);;

let vARBITRARY_INTERSECTION_OF_INTERS = prove
 ((parse_term "!P u:(A->bool)->bool.\n        (!s. s IN u ==> (ARBITRARY INTERSECTION_OF P) s)\n        ==> (ARBITRARY INTERSECTION_OF P) (INTERS u)"),
  vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vARBITRARY_INTERSECTION_OF_IDEMPOT] ---->
  vONCE_REWRITE_TAC[vINTERSECTION_OF] ----> vREWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "u:(A->bool)->bool") ----> vASM_REWRITE_TAC[vARBITRARY]);;

let vARBITRARY_INTERSECTION_OF_INTER = prove
 ((parse_term "!P s t. (ARBITRARY INTERSECTION_OF P) s /\\ (ARBITRARY INTERSECTION_OF P) t\n           ==> (ARBITRARY INTERSECTION_OF P) (s INTER t)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vINTERS_2] ---->
  vMATCH_MP_TAC vARBITRARY_INTERSECTION_OF_INTERS ---->
  vASM_REWRITE_TAC[vARBITRARY; vFORALL_IN_INSERT] ---->
  vREWRITE_TAC[vARBITRARY; vNOT_IN_EMPTY]);;

let vARBITRARY_UNION_OF_INTER_EQ = prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. (ARBITRARY UNION_OF P) s /\\ (ARBITRARY UNION_OF P) t\n               ==> (ARBITRARY UNION_OF P) (s INTER t)) <=>\n        (!s t. P s /\\ P t ==> (ARBITRARY UNION_OF P) (s INTER t))"),
  vGEN_TAC ---->
  vEQ_TAC ++--> [vMESON_TAC[vARBITRARY_UNION_OF_INC]; vDISCH_TAC] ---->
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vUNION_OF] ---->
  vREWRITE_TAC[] ----> vDISCH_THEN(vSTRIP_ASSUME_TAC -| vGSYM) ---->
  vASM_REWRITE_TAC[vINTER_UNIONS] ---->
  vREPLICATE_TAC 2
   (vMATCH_MP_TAC vARBITRARY_UNION_OF_UNIONS ---->
    vASM_SIMP_TAC[vSIMPLE_IMAGE; vARBITRARY; vFORALL_IN_IMAGE] ---->
    vREPEAT vSTRIP_TAC));;

let vARBITRARY_UNION_OF_INTER = prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. P s /\\ P t ==> P(s INTER t))\n        ==> (!s t. (ARBITRARY UNION_OF P) s /\\ (ARBITRARY UNION_OF P) t\n                   ==> (ARBITRARY UNION_OF P) (s INTER t))"),
  vREWRITE_TAC[vARBITRARY_UNION_OF_INTER_EQ] ---->
  vMESON_TAC[vARBITRARY_UNION_OF_INC]);;

let vARBITRARY_INTERSECTION_OF_UNION_EQ = prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. (ARBITRARY INTERSECTION_OF P) s /\\\n               (ARBITRARY INTERSECTION_OF P) t\n               ==> (ARBITRARY INTERSECTION_OF P) (s UNION t)) <=>\n        (!s t. P s /\\ P t ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))"),
  vONCE_REWRITE_TAC[vARBITRARY_INTERSECTION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vSET_RULE
    (parse_term "UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)")] ---->
  vREWRITE_TAC[vMESON[vCOMPL_COMPL] (parse_term "(!s. P(UNIV DIFF s)) <=> (!s. P s)")] ---->
  vREWRITE_TAC[vARBITRARY_UNION_OF_INTER_EQ] ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))")] ---->
  vREWRITE_TAC[vMESON[vCOMPL_COMPL] (parse_term "(!s. P(UNIV DIFF s)) <=> (!s. P s)")] ---->
  vREWRITE_TAC[vCOMPL_COMPL]);;

let vARBITRARY_INTERSECTION_OF_UNION = prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. P s /\\ P t ==> P(s UNION t))\n        ==> (!s t. (ARBITRARY INTERSECTION_OF P) s /\\\n                   (ARBITRARY INTERSECTION_OF P) t\n                   ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))"),
  vREWRITE_TAC[vARBITRARY_INTERSECTION_OF_UNION_EQ] ---->
  vMESON_TAC[vARBITRARY_INTERSECTION_OF_INC]);;

let vFINITE_UNION_OF_EMPTY = prove
 ((parse_term "!P:(A->bool)->bool. (FINITE UNION_OF P) {}"),
  vSIMP_TAC[vUNION_OF_EMPTY; vFINITE_EMPTY]);;

let vFINITE_INTERSECTION_OF_EMPTY = prove
 ((parse_term "!P:(A->bool)->bool. (FINITE INTERSECTION_OF P) UNIV"),
  vSIMP_TAC[vINTERSECTION_OF_EMPTY; vFINITE_EMPTY]);;

let vFINITE_UNION_OF_INC = prove
 ((parse_term "!P s:A->bool. P s ==> (FINITE UNION_OF P) s"),
  vSIMP_TAC[vUNION_OF_INC; vFINITE_SING]);;

let vFINITE_INTERSECTION_OF_INC = prove
 ((parse_term "!P s:A->bool. P s ==> (FINITE INTERSECTION_OF P) s"),
  vSIMP_TAC[vINTERSECTION_OF_INC; vFINITE_SING]);;

let vFINITE_UNION_OF_COMPLEMENT = prove
 ((parse_term "!P s. (FINITE UNION_OF P) s <=>\n         (FINITE INTERSECTION_OF (\\s. P((:A) DIFF s))) ((:A) DIFF s)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vUNION_OF; vINTERSECTION_OF] ---->
  vEQ_TAC ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "u:(A->bool)->bool") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "IMAGE (\\c. (:A) DIFF c) u") ---->
  vASM_SIMP_TAC[vFINITE_IMAGE; vFORALL_IN_IMAGE; vCOMPL_COMPL] ---->
  vONCE_REWRITE_TAC[vUNIONS_INTERS; vINTERS_UNIONS] ---->
  vREWRITE_TAC[vSET_RULE (parse_term "{f y | y IN IMAGE g s} = IMAGE (\\x. f(g x)) s")] ---->
  vASM_REWRITE_TAC[vIMAGE_ID; vCOMPL_COMPL]);;

let vFINITE_INTERSECTION_OF_COMPLEMENT = prove
 ((parse_term "!P s. (FINITE INTERSECTION_OF P) s <=>\n         (FINITE UNION_OF (\\s. P((:A) DIFF s))) ((:A) DIFF s)"),
  vREWRITE_TAC[vFINITE_UNION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vETA_AX; vCOMPL_COMPL]);;

let vFINITE_UNION_OF_IDEMPOT = prove
 ((parse_term "!P:(A->bool)->bool.\n        FINITE UNION_OF FINITE UNION_OF P = FINITE UNION_OF P"),
  vGEN_TAC ----> vREWRITE_TAC[vFUN_EQ_THM] ----> vX_GEN_TAC (parse_term "s:A->bool") ---->
  vEQ_TAC ----> vREWRITE_TAC[vFINITE_UNION_OF_INC] ---->
  vREWRITE_TAC[vUNION_OF; vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC (parse_term "u:(A->bool)->bool") ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC (vSUBST1_TAC -| vSYM)) ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vRIGHT_IMP_EXISTS_THM] ---->
  vREWRITE_TAC[vSKOLEM_THM; vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC (parse_term "f:(A->bool)->(A->bool)->bool") ----> vDISCH_TAC ---->
  vEXISTS_TAC
    (parse_term "IMAGE SND {s,t | s IN u /\\ t IN (f:(A->bool)->(A->bool)->bool) s}") ---->
  vASM_SIMP_TAC[vFINITE_IMAGE; vFINITE_PRODUCT_DEPENDENT] ---->
  vREWRITE_TAC[vFORALL_IN_IMAGE; vFORALL_IN_GSPEC] ---->
  vCONJ_TAC ++--> [vASM vSET_TAC[]; vREWRITE_TAC[vUNIONS_IMAGE]] ---->
  vREWRITE_TAC[vEXISTS_IN_GSPEC] ----> vASM vSET_TAC[]);;

let vFINITE_INTERSECTION_OF_IDEMPOT = prove
 ((parse_term "!P:(A->bool)->bool.\n        FINITE INTERSECTION_OF FINITE INTERSECTION_OF P =\n        FINITE INTERSECTION_OF P"),
  vREWRITE_TAC[vCOMPL_COMPL; vETA_AX; vREWRITE_RULE[vGSYM vFUN_EQ_THM; vETA_AX]
              vFINITE_INTERSECTION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vFINITE_UNION_OF_IDEMPOT]);;

let vFINITE_UNION_OF_UNIONS = prove
 ((parse_term "!P u:(A->bool)->bool.\n        FINITE u /\\ (!s. s IN u ==> (FINITE UNION_OF P) s)\n        ==> (FINITE UNION_OF P) (UNIONS u)"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vFINITE_UNION_OF_IDEMPOT] ---->
  vONCE_REWRITE_TAC[vUNION_OF] ----> vREWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "u:(A->bool)->bool") ----> vASM_REWRITE_TAC[]);;

let vFINITE_UNION_OF_UNION = prove
 ((parse_term "!P s t. (FINITE UNION_OF P) s /\\ (FINITE UNION_OF P) t\n           ==> (FINITE UNION_OF P) (s UNION t)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vUNIONS_2] ---->
  vMATCH_MP_TAC vFINITE_UNION_OF_UNIONS ---->
  vASM_REWRITE_TAC[vFINITE_INSERT; vFORALL_IN_INSERT] ---->
  vREWRITE_TAC[vFINITE_EMPTY; vNOT_IN_EMPTY]);;

let vFINITE_INTERSECTION_OF_INTERS = prove
 ((parse_term "!P u:(A->bool)->bool.\n        FINITE u /\\ (!s. s IN u ==> (FINITE INTERSECTION_OF P) s)\n        ==> (FINITE INTERSECTION_OF P) (INTERS u)"),
  vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vFINITE_INTERSECTION_OF_IDEMPOT] ---->
  vONCE_REWRITE_TAC[vINTERSECTION_OF] ----> vREWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "u:(A->bool)->bool") ----> vASM_REWRITE_TAC[]);;

let vFINITE_INTERSECTION_OF_INTER = prove
 ((parse_term "!P s t. (FINITE INTERSECTION_OF P) s /\\ (FINITE INTERSECTION_OF P) t\n           ==> (FINITE INTERSECTION_OF P) (s INTER t)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vINTERS_2] ---->
  vMATCH_MP_TAC vFINITE_INTERSECTION_OF_INTERS ---->
  vASM_REWRITE_TAC[vFINITE_INSERT; vFORALL_IN_INSERT] ---->
  vREWRITE_TAC[vFINITE_EMPTY; vNOT_IN_EMPTY]);;

let vFINITE_UNION_OF_INTER_EQ = prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. (FINITE UNION_OF P) s /\\ (FINITE UNION_OF P) t\n                   ==> (FINITE UNION_OF P) (s INTER t)) <=>\n        (!s t. P s /\\ P t ==> (FINITE UNION_OF P) (s INTER t))"),
  vGEN_TAC ---->
  vEQ_TAC ++--> [vMESON_TAC[vFINITE_UNION_OF_INC]; vDISCH_TAC] ---->
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vUNION_OF] ---->
  vREWRITE_TAC[] ----> vDISCH_THEN(vSTRIP_ASSUME_TAC -| vGSYM) ---->
  vASM_REWRITE_TAC[vINTER_UNIONS] ---->
  vREPLICATE_TAC 2
   (vMATCH_MP_TAC vFINITE_UNION_OF_UNIONS ---->
    vASM_SIMP_TAC[vSIMPLE_IMAGE; vFINITE_IMAGE; vFORALL_IN_IMAGE] ---->
    vREPEAT vSTRIP_TAC));;

let vFINITE_UNION_OF_INTER = prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. P s /\\ P t ==> P(s INTER t))\n        ==> (!s t. (FINITE UNION_OF P) s /\\ (FINITE UNION_OF P) t\n                   ==> (FINITE UNION_OF P) (s INTER t))"),
  vREWRITE_TAC[vFINITE_UNION_OF_INTER_EQ] ---->
  vMESON_TAC[vFINITE_UNION_OF_INC]);;

let vFINITE_INTERSECTION_OF_UNION_EQ = prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. (FINITE INTERSECTION_OF P) s /\\\n               (FINITE INTERSECTION_OF P) t\n               ==> (FINITE INTERSECTION_OF P) (s UNION t)) <=>\n        (!s t. P s /\\ P t ==> (FINITE INTERSECTION_OF P) (s UNION t))"),
  vONCE_REWRITE_TAC[vFINITE_INTERSECTION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vSET_RULE
    (parse_term "UNIV DIFF (s UNION t) = (UNIV DIFF s) INTER (UNIV DIFF t)")] ---->
  vREWRITE_TAC[vMESON[vCOMPL_COMPL] (parse_term "(!s. P(UNIV DIFF s)) <=> (!s. P s)")] ---->
  vREWRITE_TAC[vFINITE_UNION_OF_INTER_EQ] ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "s INTER t = UNIV DIFF ((UNIV DIFF s) UNION (UNIV DIFF t))")] ---->
  vREWRITE_TAC[vMESON[vCOMPL_COMPL] (parse_term "(!s. P(UNIV DIFF s)) <=> (!s. P s)")] ---->
  vREWRITE_TAC[vCOMPL_COMPL]);;

let vFINITE_INTERSECTION_OF_UNION = prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. P s /\\ P t ==> P(s UNION t))\n        ==> (!s t. (FINITE INTERSECTION_OF P) s /\\\n                   (FINITE INTERSECTION_OF P) t\n                   ==> (FINITE INTERSECTION_OF P) (s UNION t))"),
  vREWRITE_TAC[vFINITE_INTERSECTION_OF_UNION_EQ] ---->
  vMESON_TAC[vFINITE_INTERSECTION_OF_INC]);;

(* ------------------------------------------------------------------------- *)
(* Some additional properties of "set_of_list".                              *)
(* ------------------------------------------------------------------------- *)

let vCARD_SET_OF_LIST_LE = prove
 ((parse_term "!l. CARD(set_of_list l) <= LENGTH l"),
  vLIST_INDUCT_TAC ---->
  vSIMP_TAC[vLENGTH; set_of_list; vCARD_CLAUSES; vFINITE_SET_OF_LIST] ---->
  vASM_ARITH_TAC);;

let vHAS_SIZE_SET_OF_LIST = prove
 ((parse_term "!l. (set_of_list l) HAS_SIZE (LENGTH l) <=> PAIRWISE (\\x y. ~(x = y)) l"),
  vREWRITE_TAC[vHAS_SIZE; vFINITE_SET_OF_LIST] ----> vLIST_INDUCT_TAC ---->
  vASM_SIMP_TAC[vCARD_CLAUSES; vLENGTH; set_of_list; vPAIRWISE; vALL;
               vFINITE_SET_OF_LIST; vGSYM vALL_MEM; vIN_SET_OF_LIST] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vSUC_INJ] ---->
  vASM_MESON_TAC[vCARD_SET_OF_LIST_LE; vARITH_RULE (parse_term "~(SUC n <= n)")]);;

(* ------------------------------------------------------------------------- *)
(* Classic result on function of finite set into itself.                     *)
(* ------------------------------------------------------------------------- *)

let vSURJECTIVE_IFF_INJECTIVE_GEN = prove
 ((parse_term "!s t f:A->B.\n        FINITE s /\\ FINITE t /\\ (CARD s = CARD t) /\\ (IMAGE f s) SUBSET t\n        ==> ((!y. y IN t ==> ?x. x IN s /\\ (f x = y)) <=>\n             (!x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)))"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vREPEAT vSTRIP_TAC ++-->
   [vASM_CASES_TAC (parse_term "x:A = y") ----> vASM_REWRITE_TAC[] ---->
    vSUBGOAL_THEN (parse_term "CARD s <= CARD (IMAGE (f:A->B) (s DELETE y))") vMP_TAC ++-->
     [vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vCARD_SUBSET ---->
      vASM_SIMP_TAC[vFINITE_IMAGE; vFINITE_DELETE] ---->
      vREWRITE_TAC[vSUBSET; vIN_IMAGE; vIN_DELETE] ----> vASM_MESON_TAC[];
      vREWRITE_TAC[vNOT_LE] ----> vMATCH_MP_TAC vLET_TRANS ---->
      vEXISTS_TAC (parse_term "CARD(s DELETE (y:A))") ---->
      vASM_SIMP_TAC[vCARD_IMAGE_LE; vFINITE_DELETE] ---->
      vASM_SIMP_TAC[vCARD_DELETE; vARITH_RULE (parse_term "x - 1 < x <=> ~(x = 0)")] ---->
      vASM_MESON_TAC[vCARD_EQ_0; vMEMBER_NOT_EMPTY]];
    vSUBGOAL_THEN (parse_term "IMAGE (f:A->B) s = t") vMP_TAC ++-->
     [vALL_TAC; vASM_MESON_TAC[vEXTENSION; vIN_IMAGE]] ---->
    vASM_MESON_TAC[vCARD_SUBSET_EQ; vCARD_IMAGE_INJ]]);;

let vSURJECTIVE_IFF_INJECTIVE = prove
 ((parse_term "!s f:A->A.\n        FINITE s /\\ (IMAGE f s) SUBSET s\n        ==> ((!y. y IN s ==> ?x. x IN s /\\ (f x = y)) <=>\n             (!x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)))"),
  vSIMP_TAC[vSURJECTIVE_IFF_INJECTIVE_GEN]);;

let vIMAGE_IMP_INJECTIVE_GEN = prove
 ((parse_term "!s t f:A->B.\n        FINITE s /\\ (CARD s = CARD t) /\\ (IMAGE f s = t)\n        ==> !x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vASSUME_TAC -| vGSYM) ---->
  vMP_TAC(vISPECL [(parse_term "s:A->bool"); (parse_term "t:B->bool"); (parse_term "f:A->B")]
                vSURJECTIVE_IFF_INJECTIVE_GEN) ---->
  vASM_SIMP_TAC[vSUBSET_REFL; vFINITE_IMAGE] ---->
  vASM_MESON_TAC[vEXTENSION; vIN_IMAGE]);;

let vIMAGE_IMP_INJECTIVE = prove
 ((parse_term "!s f. FINITE s /\\ (IMAGE f s = s)\n       ==> !x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)"),
  vMESON_TAC[vIMAGE_IMP_INJECTIVE_GEN]);;

let vHAS_SIZE_IMAGE_INJ_RESTRICT = prove
 ((parse_term "!(f:A->B) s t P n.\n      FINITE s /\\ FINITE t /\\ CARD s = CARD t /\\\n      IMAGE f s SUBSET t /\\\n      (!x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y) /\\\n      {x | x IN s /\\ P(f x)} HAS_SIZE n\n      ==> {x | x IN t /\\ P x} HAS_SIZE n"),
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN
   (parse_term "{x | x IN t /\\ P x} = IMAGE (f:A->B) {x | x IN s /\\ P(f x)}")
  vSUBST1_TAC ++-->
   [vMP_TAC(vISPECL [(parse_term "s:A->bool"); (parse_term "t:B->bool"); (parse_term "f:A->B")]
        vSURJECTIVE_IFF_INJECTIVE_GEN) ---->
    vASM_REWRITE_TAC[] ----> vASM vSET_TAC[];
    vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ---->
    vASM_REWRITE_TAC[] ----> vASM vSET_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Converse relation between cardinality and injection.                      *)
(* ------------------------------------------------------------------------- *)

let vCARD_LE_INJ = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t /\\ CARD s <= CARD t\n   ==> ?f:A->B. (IMAGE f s) SUBSET t /\\\n                !x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)"),
  vREWRITE_TAC[vIMP_CONJ] ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vIMAGE_CLAUSES; vEMPTY_SUBSET; vNOT_IN_EMPTY] ---->
  vSIMP_TAC[vCARD_CLAUSES] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "s:A->bool")] ----> vSTRIP_TAC ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vCARD_CLAUSES; vLE; vNOT_SUC] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "y:B"); (parse_term "t:B->bool")] ---->
  vSIMP_TAC[vCARD_CLAUSES] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vK vALL_TAC) vSTRIP_ASSUME_TAC) ---->
  vREWRITE_TAC[vLE_SUC] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "t:B->bool")) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "f:A->B") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "\\z:A. if z = x then (y:B) else f(z)") ---->
  vREWRITE_TAC[vIN_INSERT; vSUBSET; vIN_IMAGE] ---->
  vASM_MESON_TAC[vSUBSET; vIN_IMAGE]);;

(* ------------------------------------------------------------------------- *)
(* Occasionally handy rewrites.                                              *)
(* ------------------------------------------------------------------------- *)

let vFORALL_IN_CLAUSES = prove
 ((parse_term "(!P. (!x. x IN {} ==> P x) <=> T) /\\\n   (!P a s. (!x. x IN (a INSERT s) ==> P x) <=> P a /\\ (!x. x IN s ==> P x))"),
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ----> vMESON_TAC[]);;

let vEXISTS_IN_CLAUSES = prove
 ((parse_term "(!P. (?x. x IN {} /\\ P x) <=> F) /\\\n   (!P a s. (?x. x IN (a INSERT s) /\\ P x) <=> P a \\/ (?x. x IN s /\\ P x))"),
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Injectivity and surjectivity of image and preimage under a function.      *)
(* ------------------------------------------------------------------------- *)

let vINJECTIVE_ON_IMAGE = prove
 ((parse_term "!f:A->B u.\n    (!s t. s SUBSET u /\\ t SUBSET u /\\ IMAGE f s = IMAGE f t ==> s = t) <=>\n    (!x y. x IN u /\\ y IN u /\\ f x = f y ==> x = y)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++--> [vDISCH_TAC; vSET_TAC[]] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "y:A")] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "{x:A}"); (parse_term "{y:A}")]) ---->
  vASM_REWRITE_TAC[vSING_SUBSET; vIMAGE_CLAUSES] ----> vSET_TAC[]);;

let vINJECTIVE_IMAGE = prove
 ((parse_term "!f:A->B.\n    (!s t. IMAGE f s = IMAGE f t ==> s = t) <=> (!x y. f x = f y ==> x = y)"),
  vGEN_TAC ----> vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "(:A)")] vINJECTIVE_ON_IMAGE) ---->
  vREWRITE_TAC[vIN_UNIV; vSUBSET_UNIV]);;

let vSURJECTIVE_ON_IMAGE = prove
 ((parse_term "!f:A->B u v.\n        (!t. t SUBSET v ==> ?s. s SUBSET u /\\ IMAGE f s = t) <=>\n        (!y. y IN v ==> ?x. x IN u /\\ f x = y)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vX_GEN_TAC (parse_term "y:B") ----> vDISCH_TAC ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "{y:B}")) ----> vASM vSET_TAC[];
    vDISCH_TAC ----> vX_GEN_TAC (parse_term "t:B->bool") ----> vDISCH_TAC ---->
    vEXISTS_TAC (parse_term "{x | x IN u /\\ (f:A->B) x IN t}") ----> vASM vSET_TAC[]]);;

let vSURJECTIVE_IMAGE = prove
 ((parse_term "!f:A->B. (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)"),
  vGEN_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "(:A)"); (parse_term "(:B)")] vSURJECTIVE_ON_IMAGE) ---->
  vREWRITE_TAC[vIN_UNIV; vSUBSET_UNIV]);;

let vINJECTIVE_ON_PREIMAGE = prove
 ((parse_term "!f:A->B s u.\n        (!t t'. t SUBSET u /\\ t' SUBSET u /\\\n                {x | x IN s /\\ f x IN t} = {x | x IN s /\\ f x IN t'}\n                ==> t = t') <=>\n        u SUBSET IMAGE f s"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++--> [vALL_TAC; vASM vSET_TAC[]] ---->
  vREWRITE_TAC[vSUBSET] ----> vX_GEN_TAC (parse_term "y:B") ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "{y:B}"); (parse_term "{}:B->bool")]) ----> vASM vSET_TAC[]);;

let vSURJECTIVE_ON_PREIMAGE = prove
 ((parse_term "!f:A->B s u.\n        (!k. k SUBSET s\n             ==> ?t. t SUBSET u /\\ {x | x IN s /\\ f x IN t} = k) <=>\n        IMAGE f s SUBSET u /\\\n        (!x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y)"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vCONJ_TAC ++-->
     [vREWRITE_TAC[vSUBSET; vFORALL_IN_IMAGE] ----> vX_GEN_TAC (parse_term "x:A") ---->
      vDISCH_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "{x:A}")) ----> vASM vSET_TAC[];
      vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "y:A")] ----> vSTRIP_TAC ---->
      vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "{x:A}")) ----> vASM vSET_TAC[]];
    vX_GEN_TAC (parse_term "k:A->bool") ----> vSTRIP_TAC ---->
    vEXISTS_TAC (parse_term "IMAGE (f:A->B) k") ----> vASM vSET_TAC[]]);;

let vINJECTIVE_PREIMAGE = prove
 ((parse_term "!f:A->B.\n        (!t t'. {x | f x IN t} = {x | f x IN t'} ==> t = t') <=>\n        IMAGE f UNIV = UNIV"),
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "(:A)"); (parse_term "(:B)")]
        vINJECTIVE_ON_PREIMAGE) ---->
  vREWRITE_TAC[vIN_UNIV; vSUBSET_UNIV] ----> vSET_TAC[]);;

let vSURJECTIVE_PREIMAGE = prove
 ((parse_term "!f:A->B. (!k. ?t. {x | f x IN t} = k) <=> (!x y. f x = f y ==> x = y)"),
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "(:A)"); (parse_term "(:B)")]
        vSURJECTIVE_ON_PREIMAGE) ---->
  vREWRITE_TAC[vIN_UNIV; vSUBSET_UNIV] ----> vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Existence of bijections between two finite sets of same size.             *)
(* ------------------------------------------------------------------------- *)

let vCARD_EQ_BIJECTION = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t /\\ CARD s = CARD t\n   ==> ?f:A->B. (!x. x IN s ==> f(x) IN t) /\\\n                (!y. y IN t ==> ?x. x IN s /\\ f x = y) /\\\n                !x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)"),
  vMP_TAC vCARD_LE_INJ ----> vREPEAT(vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC) ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ---->
  vASM_REWRITE_TAC[vLE_REFL] ----> vMATCH_MP_TAC vMONO_EXISTS ---->
  vASM_SIMP_TAC[vSURJECTIVE_IFF_INJECTIVE_GEN] ---->
  vMESON_TAC[vSUBSET; vIN_IMAGE]);;

let vCARD_EQ_BIJECTIONS = prove
 ((parse_term "!s t. FINITE s /\\ FINITE t /\\ CARD s = CARD t\n   ==> ?f:A->B g. (!x. x IN s ==> f(x) IN t /\\ g(f x) = x) /\\\n                  (!y. y IN t ==> g(y) IN s /\\ f(g y) = y)"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vCARD_EQ_BIJECTION) ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vREWRITE_TAC[vSURJECTIVE_ON_RIGHT_INVERSE] ---->
  vGEN_TAC ----> vREWRITE_TAC[vLEFT_AND_EXISTS_THM; vRIGHT_AND_EXISTS_THM] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vMESON_TAC[]);;

let vCARD_EQ_BIJECTIONS_SPECIAL = prove
 ((parse_term "!s t (a:A) (b:B).\n         FINITE s /\\ FINITE t /\\ CARD s = CARD t /\\ a IN s /\\ b IN t\n         ==> ?f g. f a = b /\\ g b = a /\\\n                   (!x. x IN s ==> f x IN t /\\ g (f x) = x) /\\\n                   (!y. y IN t ==> g y IN s /\\ f (g y) = y)"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "s DELETE (a:A)"); (parse_term "t DELETE (b:B)")]
        vCARD_EQ_BIJECTIONS) ---->
  vASM_SIMP_TAC[vFINITE_DELETE; vCARD_DELETE; vIN_DELETE; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "f:A->B"); (parse_term "g:B->A")] ----> vSTRIP_TAC ---->
  vEXISTS_TAC (parse_term "\\x. if x = a then b else (f:A->B) x") ---->
  vEXISTS_TAC (parse_term "\\y. if y = b then a else (g:B->A) y") ---->
  vASM_MESON_TAC[]);;

let vBIJECTIONS_HAS_SIZE = prove
 ((parse_term "!s t f:A->B g.\n        (!x. x IN s ==> f(x) IN t /\\ g(f x) = x) /\\\n        (!y. y IN t ==> g(y) IN s /\\ f(g y) = y) /\\\n        s HAS_SIZE n\n        ==> t HAS_SIZE n"),
  vREPEAT vSTRIP_TAC ----> vSUBGOAL_THEN (parse_term "t = IMAGE (f:A->B) s") vSUBST_ALL_TAC ++-->
   [vASM vSET_TAC[];
    vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ----> vASM_MESON_TAC[]]);;

let vBIJECTIONS_HAS_SIZE_EQ = prove
 ((parse_term "!s t f:A->B g.\n        (!x. x IN s ==> f(x) IN t /\\ g(f x) = x) /\\\n        (!y. y IN t ==> g(y) IN s /\\ f(g y) = y)\n        ==> !n. s HAS_SIZE n <=> t HAS_SIZE n"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ---->
  vMATCH_MP_TAC(vONCE_REWRITE_RULE
  [vTAUT (parse_term "a /\\ b /\\ c ==> d <=> a /\\ b ==> c ==> d")] vBIJECTIONS_HAS_SIZE) ++-->
   [vMAP_EVERY vEXISTS_TAC [(parse_term "f:A->B"); (parse_term "g:B->A")];
    vMAP_EVERY vEXISTS_TAC [(parse_term "g:B->A"); (parse_term "f:A->B")]] ---->
  vASM_MESON_TAC[]);;

let vBIJECTIONS_CARD_EQ = prove
 ((parse_term "!s t f:A->B g.\n        (FINITE s \\/ FINITE t) /\\\n        (!x. x IN s ==> f(x) IN t /\\ g(f x) = x) /\\\n        (!y. y IN t ==> g(y) IN s /\\ f(g y) = y)\n        ==> CARD s = CARD t"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2
   vMP_TAC (vMP_TAC -| vMATCH_MP vBIJECTIONS_HAS_SIZE_EQ)) ---->
  vMESON_TAC[vHAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Transitive relation with finitely many predecessors is wellfounded.       *)
(* ------------------------------------------------------------------------- *)

let vWF_FINITE = prove
 ((parse_term "!(<<). (!x. ~(x << x)) /\\ (!x y z. x << y /\\ y << z ==> x << z) /\\\n          (!x:A. FINITE {y | y << x})\n          ==> WF(<<)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vWF_DCHAIN] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "s:num->A") vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN (parse_term "!m n. m < n ==> (s:num->A) n << s m") vASSUME_TAC ++-->
   [vMATCH_MP_TAC vTRANSITIVE_STEPWISE_LT ----> vASM_MESON_TAC[]; vALL_TAC] ---->
  vMP_TAC(vISPEC (parse_term "s:num->A") vINFINITE_IMAGE_INJ) ----> vANTS_TAC ++-->
   [vASM_MESON_TAC[vLT_CASES]; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "(:num)")) ---->
  vREWRITE_TAC[num_INFINITE] ----> vREWRITE_TAC[vINFINITE] ---->
  vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC (parse_term "s(0) INSERT {y:A | y << s(0)}") ---->
  vASM_REWRITE_TAC[vFINITE_INSERT] ---->
  vREWRITE_TAC[vSUBSET; vFORALL_IN_IMAGE; vIN_UNIV; vIN_INSERT] ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vIN_ELIM_THM] ----> vASM_MESON_TAC[vLT_0]);;

let vWF_PSUBSET = prove
 ((parse_term "!s:A->bool. FINITE s ==> WF (\\t1 t2. t1 PSUBSET t2 /\\ t2 SUBSET s)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vWF_FINITE ----> vSIMP_TAC[vCONJ_ASSOC] ---->
  vCONJ_TAC ++--> [vSET_TAC[]; vX_GEN_TAC (parse_term "t:A->bool")] ---->
  vMATCH_MP_TAC vFINITE_SUBSET ----> vEXISTS_TAC (parse_term "{t:A->bool | t SUBSET s}") ---->
  vASM_SIMP_TAC[vFINITE_POWERSET] ----> vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cardinal comparisons (more theory in Library/card.ml)                     *)
(* ------------------------------------------------------------------------- *)

let le_c = new_definition
  (parse_term "s <=_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\\\n                    (!x y. x IN s /\\ y IN s /\\ (f(x) = f(y)) ==> (x = y))");;

let lt_c = new_definition
  (parse_term "s <_c t <=> s <=_c t /\\ ~(t <=_c s)");;

let eq_c = new_definition
  (parse_term "s =_c t <=> ?f. (!x. x IN s ==> f(x) IN t) /\\\n                   !y. y IN t ==> ?!x. x IN s /\\ (f x = y)");;

let ge_c = new_definition
 (parse_term "s >=_c t <=> t <=_c s");;

let gt_c = new_definition
 (parse_term "s >_c t <=> t <_c s");;

let vLE_C = prove
 ((parse_term "!s t. s <=_c t <=> ?g. !x. x IN s ==> ?y. y IN t /\\ (g y = x)"),
  vREWRITE_TAC[le_c; vINJECTIVE_ON_LEFT_INVERSE; vSURJECTIVE_ON_RIGHT_INVERSE;
              vRIGHT_IMP_EXISTS_THM; vSKOLEM_THM; vRIGHT_AND_EXISTS_THM] ---->
  vMESON_TAC[]);;

let vGE_C = prove
 ((parse_term "!s t. s >=_c t <=> ?f. !y. y IN t ==> ?x. x IN s /\\ (y = f x)"),
  vREWRITE_TAC[ge_c; vLE_C] ----> vMESON_TAC[]);;

let vCOUNTABLE = new_definition
  (parse_term "COUNTABLE t <=> (:num) >=_c t");;

(* ------------------------------------------------------------------------- *)
(* Supremum and infimum.                                                     *)
(* ------------------------------------------------------------------------- *)

let sup = new_definition
  (parse_term "sup s = @a:real. (!x. x IN s ==> x <= a) /\\\n                    !b. (!x. x IN s ==> x <= b) ==> a <= b");;

let vSUP_EQ = prove
 ((parse_term "!s t. (!b. (!x. x IN s ==> x <= b) <=> (!x. x IN t ==> x <= b))\n         ==> sup s = sup t"),
  vSIMP_TAC[sup]);;

let vSUP = prove
 ((parse_term "!s. ~(s = {}) /\\ (?b. !x. x IN s ==> x <= b)\n       ==> (!x. x IN s ==> x <= sup s) /\\\n           !b. (!x. x IN s ==> x <= b) ==> sup s <= b"),
  vREWRITE_TAC[sup] ----> vCONV_TAC(vONCE_DEPTH_CONV vSELECT_CONV) ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_COMPLETE ---->
  vASM_MESON_TAC[vMEMBER_NOT_EMPTY]);;

let vSUP_FINITE_LEMMA = prove
 ((parse_term "!s. FINITE s /\\ ~(s = {}) ==> ?b:real. b IN s /\\ !x. x IN s ==> x <= b"),
  vREWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vNOT_INSERT_EMPTY; vIN_INSERT] ---->
  vREWRITE_TAC[vGSYM vMEMBER_NOT_EMPTY] ---->
  vMESON_TAC[vREAL_LE_TOTAL; vREAL_LE_TRANS]);;

let vSUP_FINITE = prove
 ((parse_term "!s. FINITE s /\\ ~(s = {}) ==> (sup s) IN s /\\ !x. x IN s ==> x <= sup s"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vSUP_FINITE_LEMMA) ---->
  vASM_MESON_TAC[vREAL_LE_ANTISYM; vREAL_LE_TOTAL; vSUP]);;

let vREAL_LE_SUP_FINITE = prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (a <= sup s <=> ?x. x IN s /\\ a <= x)"),
  vMESON_TAC[vSUP_FINITE; vREAL_LE_TRANS]);;

let vREAL_SUP_LE_FINITE = prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (sup s <= a <=> !x. x IN s ==> x <= a)"),
  vMESON_TAC[vSUP_FINITE; vREAL_LE_TRANS]);;

let vREAL_LT_SUP_FINITE = prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (a < sup s <=> ?x. x IN s /\\ a < x)"),
  vMESON_TAC[vSUP_FINITE; vREAL_LTE_TRANS]);;

let vREAL_SUP_LT_FINITE = prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (sup s < a <=> !x. x IN s ==> x < a)"),
  vMESON_TAC[vSUP_FINITE; vREAL_LET_TRANS]);;

let vREAL_SUP_UNIQUE = prove
 ((parse_term "!s b. (!x. x IN s ==> x <= b) /\\\n         (!b'. b' < b ==> ?x. x IN s /\\ b' < x)\n         ==> sup s = b"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[sup] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vASM_MESON_TAC[vREAL_NOT_LE; vREAL_LE_ANTISYM]);;

let vREAL_SUP_LE = prove
 ((parse_term "!b. ~(s = {}) /\\ (!x. x IN s ==> x <= b) ==> sup s <= b"),
  vMESON_TAC[vSUP]);;

let vREAL_SUP_LE_SUBSET = prove
 ((parse_term "!s t. ~(s = {}) /\\ s SUBSET t /\\ (?b. !x. x IN t ==> x <= b)\n         ==> sup s <= sup t"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_SUP_LE ---->
  vMP_TAC(vSPEC (parse_term "t:real->bool") vSUP) ----> vASM vSET_TAC[]);;

let vREAL_SUP_BOUNDS = prove
 ((parse_term "!s a b. ~(s = {}) /\\ (!x. x IN s ==> a <= x /\\ x <= b)\n           ==> a <= sup s /\\ sup s <= b"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPEC (parse_term "s:real->bool") vSUP) ----> vANTS_TAC ++-->
   [vASM_MESON_TAC[]; vALL_TAC] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vGSYM vMEMBER_NOT_EMPTY]) ---->
  vASM_MESON_TAC[vREAL_LE_TRANS]);;

let vREAL_ABS_SUP_LE = prove
 ((parse_term "!s a. ~(s = {}) /\\ (!x. x IN s ==> abs(x) <= a) ==> abs(sup s) <= a"),
  vREWRITE_TAC[vGSYM vREAL_BOUNDS_LE; vREAL_SUP_BOUNDS]);;

let vREAL_SUP_ASCLOSE = prove
 ((parse_term "!s l e. ~(s = {}) /\\ (!x. x IN s ==> abs(x - l) <= e)\n           ==> abs(sup s - l) <= e"),
  vSIMP_TAC[vREAL_ARITH (parse_term "abs(x - l):real <= e <=> l - e <= x /\\ x <= l + e")] ---->
  vREWRITE_TAC[vREAL_SUP_BOUNDS]);;

let vSUP_UNIQUE_FINITE = prove
 ((parse_term "!s. FINITE s /\\ ~(s = {})\n       ==> (sup s = a <=> a IN s /\\ !y. y IN s ==> y <= a)"),
   vASM_SIMP_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_LE_SUP_FINITE; vREAL_SUP_LE_FINITE;
               vNOT_INSERT_EMPTY; vFINITE_INSERT; vFINITE_EMPTY] ---->
   vMESON_TAC[vREAL_LE_REFL; vREAL_LE_TRANS; vREAL_LE_ANTISYM]);;

let vSUP_INSERT_FINITE = prove
 ((parse_term "!x s. FINITE s ==> sup(x INSERT s) = if s = {} then x else max x (sup s)"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vSUP_UNIQUE_FINITE;  vFINITE_INSERT; vFINITE_EMPTY;
               vNOT_INSERT_EMPTY; vFORALL_IN_INSERT; vNOT_IN_EMPTY] ---->
  vREWRITE_TAC[vIN_SING; vREAL_LE_REFL] ---->
  vREWRITE_TAC[real_max] ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vSUP_FINITE; vIN_INSERT; vREAL_LE_REFL] ---->
  vASM_MESON_TAC[vSUP_FINITE; vREAL_LE_TOTAL; vREAL_LE_TRANS]);;

let vSUP_SING = prove
 ((parse_term "!a. sup {a} = a"),
  vSIMP_TAC[vSUP_INSERT_FINITE; vFINITE_EMPTY]);;

let vSUP_INSERT_INSERT = prove
 ((parse_term "!a b s. sup (b INSERT a INSERT s) = sup (max a b INSERT s)"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vSUP_EQ ---->
  vX_GEN_TAC (parse_term "c:real") ----> vREWRITE_TAC[vFORALL_IN_INSERT] ---->
  vASM_CASES_TAC (parse_term "!x:real. x IN s ==> x <= c") ----> vASM_REWRITE_TAC[] ---->
  vREAL_ARITH_TAC);;

let vREAL_LE_SUP = prove
 ((parse_term "!s a b y. y IN s /\\ a <= y /\\ (!x. x IN s ==> x <= b) ==> a <= sup s"),
  vMESON_TAC[vSUP; vMEMBER_NOT_EMPTY; vREAL_LE_TRANS]);;

let vREAL_SUP_LE_EQ = prove
 ((parse_term "!s y. ~(s = {}) /\\ (?b. !x. x IN s ==> x <= b)\n         ==> (sup s <= y <=> !x. x IN s ==> x <= y)"),
  vMESON_TAC[vSUP; vREAL_LE_TRANS]);;

let vSUP_UNIQUE = prove
 ((parse_term "!s b. (!c. (!x. x IN s ==> x <= c) <=> b <= c) ==> sup s = b"),
  vREPEAT vSTRIP_TAC ----> vGEN_REWRITE_TAC vRAND_CONV [vGSYM vSUP_SING] ---->
  vMATCH_MP_TAC vSUP_EQ ----> vASM vSET_TAC[]);;

let vSUP_UNION = prove
 ((parse_term "!s t. ~(s = {}) /\\ ~(t = {}) /\\\n         (?b. !x. x IN s ==> x <= b) /\\ (?c. !x. x IN t ==> x <= c)\n         ==> sup(s UNION t) = max (sup s) (sup t)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUP_UNIQUE ---->
  vREWRITE_TAC[vFORALL_IN_UNION; vREAL_MAX_LE] ---->
  vASM_MESON_TAC[vSUP; vREAL_LE_TRANS]);;

let vELEMENT_LE_SUP = prove
 ((parse_term "!s a. (?b. !x. x IN s ==> x <= b) /\\ a IN s ==> a <= sup s"),
  vMESON_TAC[vREAL_LE_SUP; vREAL_LE_REFL]);;

let vSUP_APPROACH = prove
 ((parse_term "!s c. ~(s = {}) /\\ (?b. !x. x IN s ==> x <= b) /\\ c < sup s\n         ==> ?x. x IN s /\\ c < x"),
  vINTRO_TAC "!s c; npty bound lt" ---->
  vREFUTE_THEN (vLABEL_TAC "hp" -|
    vREWRITE_RULE[vNOT_EXISTS_THM; vDE_MORGAN_THM; vREAL_NOT_LT]) ---->
  vREMOVE_THEN "lt" vMP_TAC ----> vREWRITE_TAC[vREAL_NOT_LT] ---->
  vHYP (vMP_TAC -| vMATCH_MP vSUP -| end_itlist vCONJ) "npty bound" [] ---->
  vINTRO_TAC "_ sup" ----> vREMOVE_THEN "sup" vMATCH_MP_TAC ---->
  vASM_MESON_TAC[]);;

let vREAL_MAX_SUP = prove
 ((parse_term "!x y. max x y = sup {x,y}"),
  vSIMP_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_SUP_LE_FINITE; vREAL_LE_SUP_FINITE;
           vFINITE_RULES; vNOT_INSERT_EMPTY; vREAL_MAX_LE; vREAL_LE_MAX] ---->
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ----> vMESON_TAC[vREAL_LE_TOTAL]);;

let inf = new_definition
  (parse_term "inf s = @a:real. (!x. x IN s ==> a <= x) /\\\n                    !b. (!x. x IN s ==> b <= x) ==> b <= a");;

let vINF_EQ = prove
 ((parse_term "!s t. (!a. (!x. x IN s ==> a <= x) <=> (!x. x IN t ==> a <= x))\n         ==> inf s = inf t"),
  vSIMP_TAC[inf]);;

let vINF = prove
 ((parse_term "!s. ~(s = {}) /\\ (?b. !x. x IN s ==> b <= x)\n       ==> (!x. x IN s ==> inf s <= x) /\\\n           !b. (!x. x IN s ==> b <= x) ==> b <= inf s"),
  vGEN_TAC ----> vSTRIP_TAC ----> vREWRITE_TAC[inf] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vSELECT_CONV) ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_LE_NEG2] ---->
  vEXISTS_TAC (parse_term "--(sup (IMAGE (--) s))") ---->
  vMP_TAC(vSPEC (parse_term "IMAGE (--) (s:real->bool)") vSUP) ---->
  vREWRITE_TAC[vREAL_NEG_NEG] ---->
  vABBREV_TAC (parse_term "a = sup (IMAGE (--) s)") ---->
  vREWRITE_TAC[vGSYM vMEMBER_NOT_EMPTY; vIN_IMAGE] ---->
  vASM_MESON_TAC[vREAL_NEG_NEG; vMEMBER_NOT_EMPTY; vREAL_LE_NEG2]);;

let vINF_FINITE_LEMMA = prove
 ((parse_term "!s. FINITE s /\\ ~(s = {}) ==> ?b:real. b IN s /\\ !x. x IN s ==> b <= x"),
  vREWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vNOT_INSERT_EMPTY; vIN_INSERT] ---->
  vREWRITE_TAC[vGSYM vMEMBER_NOT_EMPTY] ---->
  vMESON_TAC[vREAL_LE_TOTAL; vREAL_LE_TRANS]);;

let vINF_FINITE = prove
 ((parse_term "!s. FINITE s /\\ ~(s = {}) ==> (inf s) IN s /\\ !x. x IN s ==> inf s <= x"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vINF_FINITE_LEMMA) ---->
  vASM_MESON_TAC[vREAL_LE_ANTISYM; vREAL_LE_TOTAL; vINF]);;

let vREAL_LE_INF_FINITE = prove
((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (a <= inf s <=> !x. x IN s ==> a <= x)"),
  vMESON_TAC[vINF_FINITE; vREAL_LE_TRANS]);;

let vREAL_INF_LE_FINITE = prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (inf s <= a <=> ?x. x IN s /\\ x <= a)"),
  vMESON_TAC[vINF_FINITE; vREAL_LE_TRANS]);;

let vREAL_LT_INF_FINITE = prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (a < inf s <=> !x. x IN s ==> a < x)"),
  vMESON_TAC[vINF_FINITE; vREAL_LTE_TRANS]);;

let vREAL_INF_LT_FINITE = prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (inf s < a <=> ?x. x IN s /\\ x < a)"),
  vMESON_TAC[vINF_FINITE; vREAL_LET_TRANS]);;

let vREAL_INF_UNIQUE = prove
 ((parse_term "!s b. (!x. x IN s ==> b <= x) /\\\n         (!b'. b < b' ==> ?x. x IN s /\\ x < b')\n         ==> inf s = b"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[inf] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vASM_MESON_TAC[vREAL_NOT_LE; vREAL_LE_ANTISYM]);;

let vREAL_LE_INF = prove
 ((parse_term "!b. ~(s = {}) /\\ (!x. x IN s ==> b <= x) ==> b <= inf s"),
  vMESON_TAC[vINF]);;

let vREAL_LE_INF_SUBSET = prove
 ((parse_term "!s t. ~(t = {}) /\\ t SUBSET s /\\ (?b. !x. x IN s ==> b <= x)\n         ==> inf s <= inf t"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_INF ---->
  vMP_TAC(vSPEC (parse_term "s:real->bool") vINF) ----> vASM vSET_TAC[]);;

let vREAL_INF_BOUNDS = prove
 ((parse_term "!s a b. ~(s = {}) /\\ (!x. x IN s ==> a <= x /\\ x <= b)\n           ==> a <= inf s /\\ inf s <= b"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPEC (parse_term "s:real->bool") vINF) ----> vANTS_TAC ++-->
   [vASM_MESON_TAC[]; vALL_TAC] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vGSYM vMEMBER_NOT_EMPTY]) ---->
  vASM_MESON_TAC[vREAL_LE_TRANS]);;

let vREAL_ABS_INF_LE = prove
 ((parse_term "!s a. ~(s = {}) /\\ (!x. x IN s ==> abs(x) <= a) ==> abs(inf s) <= a"),
  vREWRITE_TAC[vGSYM vREAL_BOUNDS_LE; vREAL_INF_BOUNDS]);;

let vREAL_INF_ASCLOSE = prove
 ((parse_term "!s l e. ~(s = {}) /\\ (!x. x IN s ==> abs(x - l) <= e)\n           ==> abs(inf s - l) <= e"),
  vSIMP_TAC[vREAL_ARITH (parse_term "abs(x - l):real <= e <=> l - e <= x /\\ x <= l + e")] ---->
  vREWRITE_TAC[vREAL_INF_BOUNDS]);;

let vINF_UNIQUE_FINITE = prove
 ((parse_term "!s. FINITE s /\\ ~(s = {})\n       ==> (inf s = a <=> a IN s /\\ !y. y IN s ==> a <= y)"),
   vASM_SIMP_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_LE_INF_FINITE; vREAL_INF_LE_FINITE;
               vNOT_INSERT_EMPTY; vFINITE_INSERT; vFINITE_EMPTY] ---->
   vMESON_TAC[vREAL_LE_REFL; vREAL_LE_TRANS; vREAL_LE_ANTISYM]);;

let vINF_INSERT_FINITE = prove
 ((parse_term "!x s. FINITE s ==> inf(x INSERT s) = if s = {} then x else min x (inf s)"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vINF_UNIQUE_FINITE;  vFINITE_INSERT; vFINITE_EMPTY;
               vNOT_INSERT_EMPTY; vFORALL_IN_INSERT; vNOT_IN_EMPTY] ---->
  vREWRITE_TAC[vIN_SING; vREAL_LE_REFL] ---->
  vREWRITE_TAC[real_min] ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vINF_FINITE; vIN_INSERT; vREAL_LE_REFL] ---->
  vASM_MESON_TAC[vINF_FINITE; vREAL_LE_TOTAL; vREAL_LE_TRANS]);;

let vINF_SING = prove
 ((parse_term "!a. inf {a} = a"),
  vSIMP_TAC[vINF_INSERT_FINITE; vFINITE_EMPTY]);;

let vINF_INSERT_INSERT = prove
 ((parse_term "!a b s. inf (b INSERT a INSERT s) = inf (min a b INSERT s)"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vINF_EQ ---->
  vX_GEN_TAC (parse_term "c:real") ----> vREWRITE_TAC[vFORALL_IN_INSERT] ---->
  vASM_CASES_TAC (parse_term "!x:real. x IN s ==> c <= x") ----> vASM_REWRITE_TAC[] ---->
  vREAL_ARITH_TAC);;

let vREAL_SUP_EQ_INF = prove
 ((parse_term "!s. ~(s = {}) /\\ (?B. !x. x IN s ==> abs(x) <= B)\n       ==> (sup s = inf s <=> ?a. s = {a})"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vEXISTS_TAC (parse_term "sup s") ----> vMATCH_MP_TAC
     (vSET_RULE (parse_term "~(s = {}) /\\ (!x. x IN s ==> x = a) ==> s = {a}")) ---->
    vASM_REWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
    vASM_MESON_TAC[vSUP; vREAL_ABS_BOUNDS; vINF];
    vSTRIP_TAC ---->
    vASM_SIMP_TAC[vSUP_INSERT_FINITE; vINF_INSERT_FINITE; vFINITE_EMPTY]]);;

let vREAL_INF_LE = prove
 ((parse_term "!s a b y. y IN s /\\ y <= b /\\ (!x. x IN s ==> a <= x) ==> inf s <= b"),
  vMESON_TAC[vINF; vMEMBER_NOT_EMPTY; vREAL_LE_TRANS]);;

let vREAL_LE_INF_EQ = prove
 ((parse_term "!s y. ~(s = {}) /\\ (?b. !x. x IN s ==> b <= x)\n         ==> (y <= inf s <=> !x. x IN s ==> y <= x)"),
  vMESON_TAC[vINF; vREAL_LE_TRANS]);;

let vINF_UNIQUE = prove
 ((parse_term "!s b. (!c. (!x. x IN s ==> c <= x) <=> c <= b) ==> inf s = b"),
  vREPEAT vSTRIP_TAC ----> vGEN_REWRITE_TAC vRAND_CONV [vGSYM vINF_SING] ---->
  vMATCH_MP_TAC vINF_EQ ----> vASM vSET_TAC[]);;

let vINF_UNION = prove
 ((parse_term "!s t. ~(s = {}) /\\ ~(t = {}) /\\\n         (?b. !x. x IN s ==> b <= x) /\\ (?c. !x. x IN t ==> c <= x)\n         ==> inf(s UNION t) = min (inf s) (inf t)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vINF_UNIQUE ---->
  vREWRITE_TAC[vFORALL_IN_UNION; vREAL_LE_MIN] ---->
  vASM_MESON_TAC[vINF; vREAL_LE_TRANS]);;

let vINF_LE_ELEMENT = prove
 ((parse_term "!s a. (?b. !x. x IN s ==> b <= x) /\\ a IN s ==> inf s <= a"),
  vMESON_TAC[vREAL_INF_LE; vREAL_LE_REFL]);;

let vINF_APPROACH = prove
 ((parse_term "!s c. ~(s = {}) /\\ (?b. !x. x IN s ==> b <= x) /\\ inf s < c\n         ==> ?x. x IN s /\\ x < c"),
  vINTRO_TAC "!s c; npty bound lt" ---->
  vREFUTE_THEN (vLABEL_TAC "hp" -|
    vREWRITE_RULE[vNOT_EXISTS_THM; vDE_MORGAN_THM; vREAL_NOT_LT]) ---->
  vREMOVE_THEN "lt" vMP_TAC ----> vREWRITE_TAC[vREAL_NOT_LT] ---->
  vHYP (vMP_TAC -| vMATCH_MP vINF -| end_itlist vCONJ) "npty bound" [] ---->
  vINTRO_TAC "_ inf" ----> vREMOVE_THEN "inf" vMATCH_MP_TAC ---->
  vASM_MESON_TAC[]);;

let vREAL_MIN_INF = prove
 ((parse_term "!x y. min x y = inf {x,y}"),
  vSIMP_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_INF_LE_FINITE; vREAL_LE_INF_FINITE;
           vFINITE_RULES; vNOT_INSERT_EMPTY; vREAL_MIN_LE; vREAL_LE_MIN] ---->
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ----> vMESON_TAC[vREAL_LE_TOTAL]);;

(* ------------------------------------------------------------------------- *)
(* Relational counterparts of sup and inf.                                   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("has_inf",(12,"right"));;
parse_as_infix ("has_sup",(12,"right"));;

let has_inf = new_definition
  (parse_term "s has_inf b <=> (!c. (!x:real. x IN s ==> c <= x) <=> c <= b)");;

let has_sup = new_definition
  (parse_term "s has_sup b <=> (!c. (!x:real. x IN s ==> x <= c) <=> b <= c)");;

let vHAS_INF_LBOUND = prove
 ((parse_term "!s b x. s has_inf b /\\ x IN s ==> b <= x"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[has_inf] ----> vMESON_TAC[vREAL_LE_REFL]);;

let vHAS_SUP_UBOUND = prove
 ((parse_term "!s b x. s has_sup b /\\ x IN s ==> x <= b"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[has_sup] ----> vMESON_TAC[vREAL_LE_REFL]);;

let vHAS_INF_INF = prove
 ((parse_term "!s l. s has_inf l <=>\n         ~(s = {}) /\\\n         (?b. !x. x IN s ==> b <= x) /\\\n         inf s = l"),
  vGEN_TAC ----> vGEN_TAC ----> vREWRITE_TAC[has_inf] ---->
  vEQ_TAC ----> vSTRIP_TAC ++-->
  [vCONJ_TAC ++-->
   [vREFUTE_THEN vSUBST_ALL_TAC ---->
    vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vNOT_IN_EMPTY; vNOT_FORALL_THM] ---->
    vEXISTS_TAC (parse_term "l + &1:real") ----> vREAL_ARITH_TAC;
    vALL_TAC] ---->
   vCONJ_TAC ++-->
   [vASM_REWRITE_TAC[] ----> vMESON_TAC[vREAL_LE_REFL]; vALL_TAC] ---->
   vMATCH_MP_TAC vINF_UNIQUE ----> vASM_REWRITE_TAC[];
   vGEN_TAC ----> vMP_TAC (vSPEC (parse_term "s:real->bool") vINF) ----> vANTS_TAC ++-->
   [vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[]; vALL_TAC] ---->
   vPOP_ASSUM vSUBST_ALL_TAC ----> vSTRIP_TAC ----> vEQ_TAC ---->
   vASM_REWRITE_TAC[] ----> vREPEAT vSTRIP_TAC ---->
   vTRANS_TAC vREAL_LE_TRANS (parse_term "l:real") ----> vASM_SIMP_TAC[]]);;

let vHAS_SUP_SUP = prove
 ((parse_term "!s l. s has_sup l <=>\n         ~(s = {}) /\\\n         (?b. !x. x IN s ==> x <= b) /\\\n         sup s = l"),
  vGEN_TAC ----> vGEN_TAC ----> vREWRITE_TAC[has_sup] ---->
  vEQ_TAC ----> vSTRIP_TAC ++-->
  [vCONJ_TAC ++-->
   [vREFUTE_THEN vSUBST_ALL_TAC ---->
    vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vNOT_IN_EMPTY; vNOT_FORALL_THM] ---->
    vEXISTS_TAC (parse_term "l - &1:real") ----> vREAL_ARITH_TAC;
    vALL_TAC] ---->
   vCONJ_TAC ++-->
   [vASM_REWRITE_TAC[] ----> vMESON_TAC[vREAL_LE_REFL]; vALL_TAC] ---->
   vMATCH_MP_TAC vSUP_UNIQUE ----> vASM_REWRITE_TAC[];
   vGEN_TAC ----> vMP_TAC (vSPEC (parse_term "s:real->bool") vSUP) ----> vANTS_TAC ++-->
   [vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[];
    vALL_TAC] ---->
   vPOP_ASSUM vSUBST_ALL_TAC ----> vSTRIP_TAC ----> vEQ_TAC ---->
   vASM_REWRITE_TAC[] ----> vREPEAT vSTRIP_TAC ---->
   vTRANS_TAC vREAL_LE_TRANS (parse_term "l:real") ----> vASM_SIMP_TAC[]]);;

let vINF_EXISTS = prove
 ((parse_term "!s. (?l. s has_inf l) <=> ~(s = {}) /\\ (?b. !x. x IN s ==> b <= x)"),
  vMESON_TAC[vHAS_INF_INF]);;

let vSUP_EXISTS = prove
 ((parse_term "!s. (?l. s has_sup l) <=> ~(s = {}) /\\ (?b. !x. x IN s ==> x <= b)"),
  vMESON_TAC[vHAS_SUP_SUP]);;

let vHAS_INF_APPROACH = prove
 ((parse_term "!s l c. s has_inf l /\\ l < c ==> ?x. x IN s /\\ x < c"),
  vREWRITE_TAC[vHAS_INF_INF] ----> vMESON_TAC[vINF_APPROACH]);;

let vHAS_SUP_APPROACH = prove
 ((parse_term "!s l c. s has_sup l /\\ c < l ==> ?x. x IN s /\\ c < x"),
  vREWRITE_TAC[vHAS_SUP_SUP] ----> vMESON_TAC[vSUP_APPROACH]);;

let vHAS_INF = prove
 ((parse_term "!s l. s has_inf l <=>\n         ~(s = {}) /\\\n         (!x. x IN s ==> l <= x) /\\\n         (!c. l < c ==> ?x. x IN s /\\ x < c)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
  [vINTRO_TAC "hp" ----> vCONJ_TAC ++-->
   [vHYP_TAC "hp" (vREWRITE_RULE[vHAS_INF_INF]) ----> vASM_REWRITE_TAC[];
    vALL_TAC] ---->
   vCONJ_TAC ++-->
   [vASM_MESON_TAC[vHAS_INF_LBOUND]; vASM_MESON_TAC[vHAS_INF_APPROACH]];
   vALL_TAC] ---->
  vINTRO_TAC "ne bound approach" ----> vASM_REWRITE_TAC[has_inf] ---->
  vGEN_TAC ----> vEQ_TAC ++-->
  [vINTRO_TAC "hp" ----> vREWRITE_TAC[vGSYM vREAL_NOT_LT] ----> vINTRO_TAC "lc" ---->
   vREMOVE_THEN "approach" (vMP_TAC -| vSPEC (parse_term "(l + c) / &2")) ---->
   vANTS_TAC ++--> [vASM_REAL_ARITH_TAC; vINTRO_TAC "@x0. x0 +"] ---->
   vUSE_THEN "x0" (vHYP_TAC "hp" -| vC vMATCH_MP) ----> vASM_REAL_ARITH_TAC;
   vINTRO_TAC "hp; !x; x" ----> vTRANS_TAC vREAL_LE_TRANS (parse_term "l:real") ---->
   vASM_SIMP_TAC[]]);;

let vHAS_SUP = prove
 ((parse_term "!s l. s has_sup l <=>\n         ~(s = {}) /\\\n         (!x. x IN s ==> x <= l) /\\\n         (!c. c < l ==> ?x. x IN s /\\ c < x)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
  [vINTRO_TAC "hp" ----> vCONJ_TAC ++-->
   [vHYP_TAC "hp" (vREWRITE_RULE[vHAS_SUP_SUP]) ----> vASM_REWRITE_TAC[];
    vALL_TAC] ---->
   vCONJ_TAC ++-->
   [vASM_MESON_TAC[vHAS_SUP_UBOUND]; vASM_MESON_TAC[vHAS_SUP_APPROACH]];
   vALL_TAC] ---->
  vINTRO_TAC "ne bound approach" ----> vASM_REWRITE_TAC[has_sup] ---->
  vGEN_TAC ----> vEQ_TAC ++-->
  [vINTRO_TAC "hp" ----> vREWRITE_TAC[vGSYM vREAL_NOT_LT] ----> vINTRO_TAC "lc" ---->
   vREMOVE_THEN "approach" (vMP_TAC -| vSPEC (parse_term "(l + c) / &2")) ---->
   vANTS_TAC ++--> [vASM_REAL_ARITH_TAC; vINTRO_TAC "@x0. x0 +"] ---->
   vUSE_THEN "x0" (vHYP_TAC "hp" -| vC vMATCH_MP) ----> vASM_REAL_ARITH_TAC;
   vINTRO_TAC "hp; !x; x" ----> vTRANS_TAC vREAL_LE_TRANS (parse_term "l:real") ---->
   vASM_SIMP_TAC[]]);;

let vHAS_INF_LE = prove
 ((parse_term "!s t l m. s has_inf l /\\ t has_inf m /\\\n             (!y. y IN t ==> ?x. x IN s /\\ x <= y)\n             ==> l <= m"),
  vINTRO_TAC "!s t l m; l m le" ---->
  vHYP_TAC "l: s l1 l2" (vREWRITE_RULE[vHAS_INF]) ---->
  vHYP_TAC "m: t m1 m2" (vREWRITE_RULE[vHAS_INF]) ---->
  vREFUTE_THEN (vLABEL_TAC "lt" -| vREWRITE_RULE[vREAL_NOT_LE]) ---->
  vCLAIM_TAC "@c. c1 c2" (parse_term "?c:real. m < c /\\ c < l") ++-->
  [vEXISTS_TAC (parse_term "(l + m) / &2") ----> vASM_REAL_ARITH_TAC; vALL_TAC] ---->
  vHYP_TAC "m2: +" (vSPEC (parse_term "c:real")) ----> vASM_REWRITE_TAC[vNOT_EXISTS_THM] ---->
  vINTRO_TAC "!x; x xc" ---->
  vCLAIM_TAC "@y. y yx" (parse_term "?y:real. y IN s /\\ y <= x") ++-->
  [vHYP vMESON_TAC "le x" []; vALL_TAC] ---->
  vHYP_TAC "l1: +" (vSPEC (parse_term "y:real")) ----> vASM_REWRITE_TAC[] ---->
  vASM_REAL_ARITH_TAC);;

let vHAS_SUP_LE = prove
 ((parse_term "!s t l m. s has_sup l /\\ t has_sup m /\\\n             (!y. y IN t ==> ?x. x IN s /\\ y <= x)\n             ==> m <= l"),
  vINTRO_TAC "!s t l m; l m le" ---->
  vHYP_TAC "l: s l1 l2" (vREWRITE_RULE[vHAS_SUP]) ---->
  vHYP_TAC "m: t m1 m2" (vREWRITE_RULE[vHAS_SUP]) ---->
  vREFUTE_THEN (vLABEL_TAC "lt" -| vREWRITE_RULE[vREAL_NOT_LE]) ---->
  vCLAIM_TAC "@c. c1 c2" (parse_term "?c:real. l < c /\\ c < m") ++-->
  [vEXISTS_TAC (parse_term "(l + m) / &2") ----> vASM_REAL_ARITH_TAC; vALL_TAC] ---->
  vHYP_TAC "m2: +" (vSPEC (parse_term "c:real")) ----> vASM_REWRITE_TAC[vNOT_EXISTS_THM] ---->
  vINTRO_TAC "!x; x xc" ---->
  vCLAIM_TAC "@y. y yx" (parse_term "?y:real. y IN s /\\ x <= y") ++-->
  [vHYP vMESON_TAC "le x" []; vALL_TAC] ---->
  vHYP_TAC "l1: +" (vSPEC (parse_term "y:real")) ----> vASM_REWRITE_TAC[] ---->
  vASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Inductive definition of sets, by reducing them to inductive relations.    *)
(* ------------------------------------------------------------------------- *)

let new_inductive_set =
  let const_of_var v = mk_mconst(name_of v,type_of v) in
  let comb_all =
    let rec f (n:int) (tm:term) : hol_type list -> term = function
      | [] -> tm
      | ty::tys ->
          let v = variant (variables tm) (mk_var("x"^string_of_int n,ty)) in
          f (n+1) (mk_comb(tm,v)) tys in
    fun tm -> let tys = fst (splitlist dest_fun_ty (type_of tm)) in
              f 0 tm tys in
  let mk_eqin = vREWR_CONV (vGSYM vIN) -| comb_all in
  let transf conv = rhs -| concl -| conv in
  let remove_in_conv ptm : conv =
    let rconv = vREWR_CONV(vSYM(mk_eqin ptm)) in
    fun tm -> let htm = fst(strip_comb(snd(dest_binary "IN" tm))) in
              if htm = ptm then rconv tm else fail() in
  let remove_in_transf =
    transf -| vONCE_DEPTH_CONV -| vFIRST_CONV -| map remove_in_conv in
  let rule_head tm =
    let tm = snd(strip_forall tm) in
    let tm = snd(splitlist(dest_binop (parse_term "(==>)")) tm) in
    let tm = snd(dest_binary "IN" tm) in
    fst(strip_comb tm) in
  let find_pvars = setify -| map rule_head -| binops (parse_term "(/\\)") in
  fun tm ->
    let pvars = find_pvars tm in
    let dtm = remove_in_transf pvars tm in
    let th_rules, th_induct, th_cases = new_inductive_definition dtm in
    let insert_in_rule = vREWRITE_RULE(map (mk_eqin -| const_of_var) pvars) in
    insert_in_rule th_rules,
    insert_in_rule th_induct,
    insert_in_rule th_cases;;
