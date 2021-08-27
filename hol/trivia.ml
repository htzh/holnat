(* ========================================================================= *)
(* Trivial odds and ends.                                                    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Printer
open Parser
open Equal
open Boolean
open Drule
open Tactics
open Simp
open Theorems
open Class
;;

(* ------------------------------------------------------------------------- *)
(* Combinators. We don't bother with S and K, which seem of little use.      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix ("o",(26,"right"));;

let o_DEF = new_definition
 (parse_term "(o) (f:B->C) g = \\x:A. f(g(x))");;

let vI_DEF = new_definition
 (parse_term "I = \\x:A. x");;

let o_THM = try Cache.lookup_thm "o_THM" with _ ->  prove
 ((parse_term "!f:B->C. !g:A->B. !x:A. (f o g) x = f(g(x))"),
  vPURE_REWRITE_TAC [o_DEF] ---->
  vCONV_TAC (vDEPTH_CONV vBETA_CONV) ---->
  vREPEAT vGEN_TAC ----> vREFL_TAC);;

let o_ASSOC = try Cache.lookup_thm "o_ASSOC" with _ ->  prove
 ((parse_term "!f:C->D. !g:B->C. !h:A->B. f o (g o h) = (f o g) o h"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC [o_DEF] ---->
  vCONV_TAC (vREDEPTH_CONV vBETA_CONV) ---->
  vREFL_TAC);;

let vI_THM = try Cache.lookup_thm "I_THM" with _ ->  prove
 ((parse_term "!x:A. I x = x"),
  vREWRITE_TAC [vI_DEF]);;

let vI_O_ID = try Cache.lookup_thm "I_O_ID" with _ ->  prove
 ((parse_term "!f:A->B. (I o f = f) /\\ (f o I = f)"),
  vREPEAT vSTRIP_TAC ---->
  vREWRITE_TAC[vFUN_EQ_THM; o_DEF; vI_THM]);;

(* ------------------------------------------------------------------------- *)
(* The theory "1" (a 1-element type).                                        *)
(* ------------------------------------------------------------------------- *)

let vEXISTS_ONE_REP = try Cache.lookup_thm "EXISTS_ONE_REP" with _ ->  prove
 ((parse_term "?b:bool. b"),
  vEXISTS_TAC (parse_term "T") ---->
  vBETA_TAC ----> vACCEPT_TAC vTRUTH);;

let one_tydef =
  new_type_definition "1" ("one_ABS","one_REP") vEXISTS_ONE_REP;;

let one_DEF = new_definition
 (parse_term "one = @x:1. T");;

let one = try Cache.lookup_thm "one" with _ ->  prove
 ((parse_term "!v:1. v = one"),
  vMP_TAC(vGEN_ALL (vSPEC (parse_term "one_REP a") (vCONJUNCT2 one_tydef))) ---->
  vREWRITE_TAC[vCONJUNCT1 one_tydef] ----> vDISCH_TAC ---->
  vONCE_REWRITE_TAC[vGSYM (vCONJUNCT1 one_tydef)] ---->
  vASM_REWRITE_TAC[]);;

let one_axiom = try Cache.lookup_thm "one_axiom" with _ ->  prove
 ((parse_term "!f g. f = (g:A->1)"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vFUN_EQ_THM] ---->
  vGEN_TAC ----> vONCE_REWRITE_TAC[one] ----> vREFL_TAC);;

let one_INDUCT = try Cache.lookup_thm "one_INDUCT" with _ ->  prove
 ((parse_term "!P. P one ==> !x. P x"),
  vONCE_REWRITE_TAC[one] ----> vREWRITE_TAC[]);;

let one_RECURSION = try Cache.lookup_thm "one_RECURSION" with _ ->  prove
 ((parse_term "!e:A. ?fn. fn one = e"),
  vGEN_TAC ----> vEXISTS_TAC (parse_term "\\x:1. e:A") ----> vBETA_TAC ----> vREFL_TAC);;

let one_Axiom = try Cache.lookup_thm "one_Axiom" with _ ->  prove
 ((parse_term "!e:A. ?!fn. fn one = e"),
  vGEN_TAC ----> vREWRITE_TAC[vEXISTS_UNIQUE_THM; one_RECURSION] ---->
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vFUN_EQ_THM] ---->
  vONCE_REWRITE_TAC [one] ----> vASM_REWRITE_TAC[]);;

let vFORALL_ONE_THM = try Cache.lookup_thm "FORALL_ONE_THM" with _ ->  prove
 ((parse_term "(!x. P x) <=> P one"),
  vEQ_TAC ----> vREWRITE_TAC[one_INDUCT] ----> vDISCH_THEN vMATCH_ACCEPT_TAC);;

let vEXISTS_ONE_THM = try Cache.lookup_thm "EXISTS_ONE_THM" with _ ->  prove
 ((parse_term "(?x. P x) <=> P one"),
  vGEN_REWRITE_TAC vI [vTAUT (parse_term "(p <=> q) <=> (~p <=> ~q)")] ---->
  vREWRITE_TAC[vNOT_EXISTS_THM; vFORALL_ONE_THM]);;

(* ------------------------------------------------------------------------- *)
(* Add the type "1" to the inductive type store.                             *)
(* ------------------------------------------------------------------------- *)

inductive_type_store :=
  ("1",(1,one_INDUCT,one_RECURSION))::(!inductive_type_store);;
