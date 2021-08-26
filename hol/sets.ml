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
include Sets1

(* ------------------------------------------------------------------------- *)
(* Cardinality of product.                                                   *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_PRODUCT_DEPENDENT = try Cache.lookup_thm "HAS_SIZE_PRODUCT_DEPENDENT" with _ ->  prove
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

let vFINITE_PRODUCT_DEPENDENT = try Cache.lookup_thm "FINITE_PRODUCT_DEPENDENT" with _ ->  prove
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

let vFINITE_PRODUCT = try Cache.lookup_thm "FINITE_PRODUCT" with _ ->  prove
 ((parse_term "!s t. FINITE s /\\ FINITE t ==> FINITE {(x:A,y:B) | x IN s /\\ y IN t}"),
  vSIMP_TAC[vFINITE_PRODUCT_DEPENDENT]);;

let vCARD_PRODUCT = try Cache.lookup_thm "CARD_PRODUCT" with _ ->  prove
 ((parse_term "!s t. FINITE s /\\ FINITE t\n         ==> (CARD {(x:A,y:B) | x IN s /\\ y IN t} = CARD s * CARD t)"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [(parse_term "s:A->bool"); (parse_term "CARD(s:A->bool)"); (parse_term "\\x:A. t:B->bool");
                  (parse_term "CARD(t:B->bool)")] vHAS_SIZE_PRODUCT_DEPENDENT) ---->
  vASM_SIMP_TAC[vHAS_SIZE]);;

let vHAS_SIZE_PRODUCT = try Cache.lookup_thm "HAS_SIZE_PRODUCT" with _ ->  prove
 ((parse_term "!s m t n. s HAS_SIZE m /\\ t HAS_SIZE n\n             ==> {(x:A,y:B) | x IN s /\\ y IN t} HAS_SIZE (m * n)"),
  vSIMP_TAC[vHAS_SIZE; vCARD_PRODUCT; vFINITE_PRODUCT]);;

(* ------------------------------------------------------------------------- *)
(* Actually introduce a Cartesian product operation.                         *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("CROSS",(22,"right"));;

let vCROSS = new_definition
 (parse_term "s CROSS t = {x,y | x IN s /\\ y IN t}");;

let vIN_CROSS = try Cache.lookup_thm "IN_CROSS" with _ ->  prove
 ((parse_term "!x y s t. (x,y) IN (s CROSS t) <=> x IN s /\\ y IN t"),
  vREWRITE_TAC[vCROSS; vIN_ELIM_PAIR_THM]);;

let vHAS_SIZE_CROSS = try Cache.lookup_thm "HAS_SIZE_CROSS" with _ ->  prove
 ((parse_term "!s t m n. s HAS_SIZE m /\\ t HAS_SIZE n ==> (s CROSS t) HAS_SIZE (m * n)"),
  vREWRITE_TAC[vCROSS; vHAS_SIZE_PRODUCT]);;

let vFINITE_CROSS = try Cache.lookup_thm "FINITE_CROSS" with _ ->  prove
 ((parse_term "!s t. FINITE s /\\ FINITE t ==> FINITE(s CROSS t)"),
  vSIMP_TAC[vCROSS; vFINITE_PRODUCT]);;

let vCARD_CROSS = try Cache.lookup_thm "CARD_CROSS" with _ ->  prove
 ((parse_term "!s t. FINITE s /\\ FINITE t ==> CARD(s CROSS t) = CARD s * CARD t"),
  vSIMP_TAC[vCROSS; vCARD_PRODUCT]);;

let vCROSS_EQ_EMPTY = try Cache.lookup_thm "CROSS_EQ_EMPTY" with _ ->  prove
 ((parse_term "!s t. s CROSS t = {} <=> s = {} \\/ t = {}"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_CROSS; vNOT_IN_EMPTY] ---->
  vMESON_TAC[]);;

let vCROSS_EMPTY = try Cache.lookup_thm "CROSS_EMPTY" with _ ->  prove
 ((parse_term "(!s:A->bool. s CROSS {} = {}) /\\ (!t:B->bool. {} CROSS t = {})"),
  vREWRITE_TAC[vCROSS_EQ_EMPTY]);;

let vCROSS_SING = try Cache.lookup_thm "CROSS_SING" with _ ->  prove
 ((parse_term "!x:A y:B. {x} CROSS {y} = {(x,y)}"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_SING; vIN_CROSS; vPAIR_EQ]);;

let vCROSS_UNIV = try Cache.lookup_thm "CROSS_UNIV" with _ ->  prove
 ((parse_term "(:A) CROSS (:B) = (:A#B)"),
  vREWRITE_TAC[vCROSS; vEXTENSION; vIN_ELIM_PAIR_THM; vFORALL_PAIR_THM; vIN_UNIV]);;

let vFINITE_CROSS_EQ = try Cache.lookup_thm "FINITE_CROSS_EQ" with _ ->  prove
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

let vINFINITE_CROSS_EQ = try Cache.lookup_thm "INFINITE_CROSS_EQ" with _ ->  prove
 ((parse_term "!(s:A->bool) (t:B->bool).\n        INFINITE(s CROSS t) <=>\n        ~(s = {}) /\\ INFINITE t \\/ INFINITE s /\\ ~(t = {})"),
  vREWRITE_TAC[vINFINITE; vFINITE_CROSS_EQ] ----> vMESON_TAC[vFINITE_EMPTY]);;

let vFINITE_CROSS_UNIV = try Cache.lookup_thm "FINITE_CROSS_UNIV" with _ ->  prove
 ((parse_term "FINITE(:A#B) <=> FINITE(:A) /\\ FINITE(:B)"),
  vREWRITE_TAC[vGSYM vCROSS_UNIV; vFINITE_CROSS_EQ; vUNIV_NOT_EMPTY]);;

let vINFINITE_CROSS_UNIV = try Cache.lookup_thm "INFINITE_CROSS_UNIV" with _ ->  prove
 ((parse_term "INFINITE(:A#B) <=> INFINITE(:A) \\/ INFINITE(:B)"),
  vREWRITE_TAC[vGSYM vCROSS_UNIV; vINFINITE_CROSS_EQ; vUNIV_NOT_EMPTY] ---->
  vMESON_TAC[]);;

let vFINITE_UNIV_PAIR = try Cache.lookup_thm "FINITE_UNIV_PAIR" with _ ->  prove
 ((parse_term "FINITE(:A#A) <=> FINITE(:A)"),
  vREWRITE_TAC[vFINITE_CROSS_UNIV]);;

let vINFINITE_UNIV_PAIR = try Cache.lookup_thm "INFINITE_UNIV_PAIR" with _ ->  prove
 ((parse_term "INFINITE(:A#A) <=> INFINITE(:A)"),
  vREWRITE_TAC[vINFINITE_CROSS_UNIV]);;

let vFORALL_IN_CROSS = try Cache.lookup_thm "FORALL_IN_CROSS" with _ ->  prove
 ((parse_term "!P s t. (!z. z IN s CROSS t ==> P z) <=>\n           (!x y. x IN s /\\ y IN t ==> P(x,y))"),
  vREWRITE_TAC[vFORALL_PAIR_THM; vIN_CROSS]);;

let vEXISTS_IN_CROSS = try Cache.lookup_thm "EXISTS_IN_CROSS" with _ ->  prove
 ((parse_term "!P s t. (?z. z IN s CROSS t /\\ P z) <=>\n           (?x y. x IN s /\\ y IN t /\\ P(x,y))"),
  vREWRITE_TAC[vEXISTS_PAIR_THM; vGSYM vCONJ_ASSOC; vIN_CROSS]);;

let vSUBSET_CROSS = try Cache.lookup_thm "SUBSET_CROSS" with _ ->  prove
 ((parse_term "!s t s' t'. s CROSS t SUBSET s' CROSS t' <=>\n                s = {} \\/ t = {} \\/ s SUBSET s' /\\ t SUBSET t'"),
  vSIMP_TAC[vCROSS; vEXTENSION; vIN_ELIM_PAIR_THM; vSUBSET;
   vFORALL_PAIR_THM; vIN_CROSS; vNOT_IN_EMPTY] ----> vMESON_TAC[]);;

let vCROSS_MONO = try Cache.lookup_thm "CROSS_MONO" with _ ->  prove
 ((parse_term "!s t s' t'. s SUBSET s' /\\ t SUBSET t' ==> s CROSS t SUBSET s' CROSS t'"),
  vSIMP_TAC[vSUBSET_CROSS]);;

let vCROSS_EQ = try Cache.lookup_thm "CROSS_EQ" with _ ->  prove
 ((parse_term "!s s':A->bool t t':B->bool.\n        s CROSS t = s' CROSS t' <=>\n        (s = {} \\/ t = {}) /\\ (s' = {} \\/ t' = {}) \\/ s = s' /\\ t = t'"),
  vREWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET_CROSS] ----> vSET_TAC[]);;

let vIMAGE_FST_CROSS = try Cache.lookup_thm "IMAGE_FST_CROSS" with _ ->  prove
 ((parse_term "!s:A->bool t:B->bool.\n        IMAGE FST (s CROSS t) = if t = {} then {} else s"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vCROSS_EMPTY; vIMAGE_CLAUSES] ---->
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE] ----> vONCE_REWRITE_TAC[vCONJ_SYM] ---->
  vREWRITE_TAC[vEXISTS_IN_CROSS; vFST] ----> vASM vSET_TAC[]);;

let vIMAGE_SND_CROSS = try Cache.lookup_thm "IMAGE_SND_CROSS" with _ ->  prove
 ((parse_term "!s:A->bool t:B->bool.\n        IMAGE SND (s CROSS t) = if s = {} then {} else t"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vCROSS_EMPTY; vIMAGE_CLAUSES] ---->
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE] ----> vONCE_REWRITE_TAC[vCONJ_SYM] ---->
  vREWRITE_TAC[vEXISTS_IN_CROSS; vSND] ----> vASM vSET_TAC[]);;

let vIMAGE_PAIRED_CROSS = try Cache.lookup_thm "IMAGE_PAIRED_CROSS" with _ ->  prove
 ((parse_term "!(f:A->B) (g:C->D) s t.\n         IMAGE (\\(x,y). f x,g y) (s CROSS t) = (IMAGE f s) CROSS (IMAGE g t)"),
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vEXISTS_PAIR_THM; vIN_CROSS; vFORALL_PAIR_THM;
              vPAIR_EQ] ---->
  vMESON_TAC[]);;

let vCROSS_INTER = try Cache.lookup_thm "CROSS_INTER" with _ ->  prove
 ((parse_term "(!s t u. s CROSS (t INTER u) = (s CROSS t) INTER (s CROSS u)) /\\\n   (!s t u. (s INTER t) CROSS u = (s CROSS u) INTER (t CROSS u))"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_INTER; vIN_CROSS] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vTAUT);;

let vCROSS_UNION = try Cache.lookup_thm "CROSS_UNION" with _ ->  prove
 ((parse_term "(!s t u. s CROSS (t UNION u) = (s CROSS t) UNION (s CROSS u)) /\\\n   (!s t u. (s UNION t) CROSS u = (s CROSS u) UNION (t CROSS u))"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_UNION; vIN_CROSS] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vTAUT);;

let vCROSS_DIFF = try Cache.lookup_thm "CROSS_DIFF" with _ ->  prove
 ((parse_term "(!s t u. s CROSS (t DIFF u) = (s CROSS t) DIFF (s CROSS u)) /\\\n   (!s t u. (s DIFF t) CROSS u = (s CROSS u) DIFF (t CROSS u))"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; vIN_DIFF; vIN_CROSS] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vTAUT);;

let vINTER_CROSS = try Cache.lookup_thm "INTER_CROSS" with _ ->  prove
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

let vDISJOINT_CROSS = try Cache.lookup_thm "DISJOINT_CROSS" with _ ->  prove
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

let vIN_EXTENSIONAL = try Cache.lookup_thm "IN_EXTENSIONAL" with _ ->  prove
 ((parse_term "!s f:A->B. f IN EXTENSIONAL s <=> (!x. ~(x IN s) ==> f x = ARB)"),
  vREWRITE_TAC[vEXTENSIONAL; vIN_ELIM_THM]);;

let vIN_EXTENSIONAL_UNDEFINED = try Cache.lookup_thm "IN_EXTENSIONAL_UNDEFINED" with _ ->  prove
 ((parse_term "!s f:A->B x. f IN EXTENSIONAL s /\\ ~(x IN s) ==> f x = ARB"),
  vSIMP_TAC[vIN_EXTENSIONAL]);;

let vEXTENSIONAL_EMPTY = try Cache.lookup_thm "EXTENSIONAL_EMPTY" with _ ->  prove
 ((parse_term "EXTENSIONAL {} = {\\x:A. ARB:B}"),
  vREWRITE_TAC[vEXTENSION; vIN_EXTENSIONAL; vIN_SING; vNOT_IN_EMPTY] ---->
  vREWRITE_TAC[vFUN_EQ_THM]);;

let vEXTENSIONAL_UNIV = try Cache.lookup_thm "EXTENSIONAL_UNIV" with _ ->  prove
 ((parse_term "!f. EXTENSIONAL (:A) f"),
  vREWRITE_TAC[vEXTENSIONAL; vIN_UNIV; vIN_ELIM_THM]);;

let vEXTENSIONAL_EQ = try Cache.lookup_thm "EXTENSIONAL_EQ" with _ ->  prove
 ((parse_term "!s f g:A->B.\n     f IN EXTENSIONAL s /\\ g IN EXTENSIONAL s /\\ (!x. x IN s ==> f x = g x)\n     ==> f = g"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vFUN_EQ_THM] ----> vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "x:A IN s") ++-->
  [vASM_SIMP_TAC[]; vASM_MESON_TAC[vIN_EXTENSIONAL_UNDEFINED]]);;

(* ------------------------------------------------------------------------- *)
(* Restriction of a function to an EXTENSIONAL one on a subset.              *)
(* ------------------------------------------------------------------------- *)

let vRESTRICTION = new_definition
  (parse_term "RESTRICTION s (f:A->B) x = if x IN s then f x else ARB");;

let vRESTRICTION_THM = try Cache.lookup_thm "RESTRICTION_THM" with _ ->  prove
 ((parse_term "!s (f:A->B). RESTRICTION s f = \\x. if x IN s then f x else ARB"),
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION]);;

let vRESTRICTION_DEFINED = try Cache.lookup_thm "RESTRICTION_DEFINED" with _ ->  prove
 ((parse_term "!s f:A->B x. x IN s ==> RESTRICTION s f x = f x"),
  vSIMP_TAC[vRESTRICTION]);;

let vRESTRICTION_UNDEFINED = try Cache.lookup_thm "RESTRICTION_UNDEFINED" with _ ->  prove
 ((parse_term "!s f:A->B x. ~(x IN s) ==> RESTRICTION s f x = ARB"),
  vSIMP_TAC[vRESTRICTION]);;

let vRESTRICTION_EQ = try Cache.lookup_thm "RESTRICTION_EQ" with _ ->  prove
 ((parse_term "!s f:A->B x y. x IN s /\\ f x = y ==> RESTRICTION s f x = y"),
  vSIMP_TAC[vRESTRICTION_DEFINED]);;

let vRESTRICTION_IN_EXTENSIONAL = try Cache.lookup_thm "RESTRICTION_IN_EXTENSIONAL" with _ ->  prove
 ((parse_term "!s f:A->B. RESTRICTION s f IN EXTENSIONAL s"),
  vSIMP_TAC[vIN_EXTENSIONAL; vRESTRICTION]);;

let vRESTRICTION_EXTENSION = try Cache.lookup_thm "RESTRICTION_EXTENSION" with _ ->  prove
 ((parse_term "!s f g:A->B. RESTRICTION s f = RESTRICTION s g <=>\n                (!x. x IN s ==> f x = g x)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vRESTRICTION; vFUN_EQ_THM] ----> vMESON_TAC[]);;

let vRESTRICTION_FIXPOINT = try Cache.lookup_thm "RESTRICTION_FIXPOINT" with _ ->  prove
 ((parse_term "!s f:A->B. RESTRICTION s f = f <=> f IN EXTENSIONAL s"),
  vREWRITE_TAC[vIN_EXTENSIONAL; vFUN_EQ_THM; vRESTRICTION] ----> vMESON_TAC[]);;

let vRESTRICTION_RESTRICTION = try Cache.lookup_thm "RESTRICTION_RESTRICTION" with _ ->  prove
 ((parse_term "!s t f:A->B.\n        s SUBSET t ==> RESTRICTION s (RESTRICTION t f) = RESTRICTION s f"),
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION] ----> vSET_TAC[]);;

let vRESTRICTION_IDEMP = try Cache.lookup_thm "RESTRICTION_IDEMP" with _ ->  prove
 ((parse_term "!s f:A->B. RESTRICTION s (RESTRICTION s f) = RESTRICTION s f"),
  vREWRITE_TAC[vRESTRICTION_FIXPOINT; vRESTRICTION_IN_EXTENSIONAL]);;

let vIMAGE_RESTRICTION = try Cache.lookup_thm "IMAGE_RESTRICTION" with _ ->  prove
 ((parse_term "!f:A->B s t. s SUBSET t ==> IMAGE (RESTRICTION t f) s = IMAGE f s"),
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vRESTRICTION] ----> vSET_TAC[]);;

let vRESTRICTION_COMPOSE_RIGHT = try Cache.lookup_thm "RESTRICTION_COMPOSE_RIGHT" with _ ->  prove
 ((parse_term "!f:A->B g:B->C s.\n        RESTRICTION s (g o RESTRICTION s f) =\n        RESTRICTION s (g o f)"),
  vREWRITE_TAC[vFUN_EQ_THM; o_DEF; vRESTRICTION] ---->
  vSIMP_TAC[vSUBSET; vFORALL_IN_IMAGE] ----> vSET_TAC[]);;

let vRESTRICTION_COMPOSE_LEFT = try Cache.lookup_thm "RESTRICTION_COMPOSE_LEFT" with _ ->  prove
 ((parse_term "!f:A->B g:B->C s t.\n        IMAGE f s SUBSET t\n        ==> RESTRICTION s (RESTRICTION t g o f) =\n            RESTRICTION s (g o f)"),
  vREWRITE_TAC[vFUN_EQ_THM; o_DEF; vRESTRICTION] ---->
  vSIMP_TAC[vSUBSET; vFORALL_IN_IMAGE] ----> vSET_TAC[]);;

let vRESTRICTION_COMPOSE = try Cache.lookup_thm "RESTRICTION_COMPOSE" with _ ->  prove
 ((parse_term "!f:A->B g:B->C s t.\n        IMAGE f s SUBSET t\n        ==> RESTRICTION s (RESTRICTION t g o RESTRICTION s f) =\n            RESTRICTION s (g o f)"),
  vSIMP_TAC[vRESTRICTION_COMPOSE_LEFT; vRESTRICTION_COMPOSE_RIGHT]);;

let vRESTRICTION_UNIQUE = try Cache.lookup_thm "RESTRICTION_UNIQUE" with _ ->  prove
 ((parse_term "!s (f:A->B) g.\n        RESTRICTION s f = g <=> EXTENSIONAL s g /\\ !x. x IN s ==> f x = g x"),
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION; vEXTENSIONAL; vIN_ELIM_THM] ---->
  vMESON_TAC[]);;

let vRESTRICTION_UNIQUE_ALT = try Cache.lookup_thm "RESTRICTION_UNIQUE_ALT" with _ ->  prove
 ((parse_term "!s (f:A->B) g.\n        f = RESTRICTION s g <=> EXTENSIONAL s f /\\ !x. x IN s ==> f x = g x"),
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION; vEXTENSIONAL; vIN_ELIM_THM] ---->
  vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* General Cartesian product / dependent function space.                     *)
(* ------------------------------------------------------------------------- *)

let cartesian_product = new_definition
 (parse_term "cartesian_product k s =\n        {f:K->A | EXTENSIONAL k f /\\ !i. i IN k ==> f i IN s i}");;

let vIN_CARTESIAN_PRODUCT = try Cache.lookup_thm "IN_CARTESIAN_PRODUCT" with _ ->  prove
 ((parse_term "!k s (x:K->A).\n        x IN cartesian_product k s <=>\n        EXTENSIONAL k x /\\ (!i. i IN k ==> x i IN s i)"),
  vREWRITE_TAC[cartesian_product; vIN_ELIM_THM]);;

let vCARTESIAN_PRODUCT = try Cache.lookup_thm "CARTESIAN_PRODUCT" with _ ->  prove
 ((parse_term "!k s. cartesian_product k s =\n         {f:K->A | !i. f i IN (if i IN k then s i else {ARB})}"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[cartesian_product; vIN_ELIM_THM; vEXTENSIONAL] ---->
  vMESON_TAC[vIN_SING]);;

let vRESTRICTION_IN_CARTESIAN_PRODUCT = try Cache.lookup_thm "RESTRICTION_IN_CARTESIAN_PRODUCT" with _ ->  prove
 ((parse_term "!k s (f:K->A).\n        RESTRICTION k f IN cartesian_product k s <=>\n        !i. i IN k ==> (f i) IN (s i)"),
  vREWRITE_TAC[vRESTRICTION; cartesian_product; vEXTENSIONAL; vIN_ELIM_THM] ---->
  vSET_TAC[]);;

let vCARTESIAN_PRODUCT_AS_RESTRICTIONS = try Cache.lookup_thm "CARTESIAN_PRODUCT_AS_RESTRICTIONS" with _ ->  prove
 ((parse_term "!k (s:K->A->bool).\n      cartesian_product k s =\n      {RESTRICTION k f |f| !i. i IN k ==> f i IN s i}"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET; vFORALL_IN_GSPEC] ---->
  vREWRITE_TAC[vRESTRICTION_IN_CARTESIAN_PRODUCT] ---->
  vX_GEN_TAC (parse_term "x:K->A") ---->
  vREWRITE_TAC[cartesian_product; vIN_ELIM_THM; vEXTENSIONAL] ---->
  vSTRIP_TAC ----> vEXISTS_TAC (parse_term "x:K->A") ---->
  vASM_REWRITE_TAC[vFUN_EQ_THM; vRESTRICTION] ----> vASM_MESON_TAC[]);;

let vCARTESIAN_PRODUCT_EQ_EMPTY = try Cache.lookup_thm "CARTESIAN_PRODUCT_EQ_EMPTY" with _ ->  prove
 ((parse_term "!k s:K->A->bool.\n        cartesian_product k s = {} <=> ?i. i IN k /\\ s i = {}"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vLAND_CONV [vEXTENSION] ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "(?i. i IN k /\\ s i = {}) <=> ~(!i. ?a. i IN k ==> a IN s i)")] ---->
  vREWRITE_TAC[vSKOLEM_THM; vNOT_EXISTS_THM; cartesian_product] ---->
  vREWRITE_TAC[vIN_ELIM_THM; vNOT_IN_EMPTY] ----> vEQ_TAC ---->
  vDISCH_TAC ----> vX_GEN_TAC (parse_term "f:K->A") ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "\\i. if i IN k then (f:K->A) i else ARB")) ---->
  vREWRITE_TAC[vEXTENSIONAL; vIN_ELIM_THM] ----> vSIMP_TAC[]);;

let vCARTESIAN_PRODUCT_EMPTY = try Cache.lookup_thm "CARTESIAN_PRODUCT_EMPTY" with _ ->  prove
 ((parse_term "!s. cartesian_product {} s = {(\\i. ARB)}"),
  vREWRITE_TAC[vCARTESIAN_PRODUCT; vNOT_IN_EMPTY; vEXTENSION] ---->
  vREWRITE_TAC[vIN_ELIM_THM; vIN_SING] ----> vREWRITE_TAC[vFUN_EQ_THM]);;

let vCARTESIAN_PRODUCT_EQ_MEMBERS = try Cache.lookup_thm "CARTESIAN_PRODUCT_EQ_MEMBERS" with _ ->  prove
 ((parse_term "!k s x y:K->A.\n        x IN cartesian_product k s /\\ y IN cartesian_product k s /\\\n        (!i. i IN k ==> x i = y i)\n        ==> x = y"),
  vREWRITE_TAC[cartesian_product; vIN_ELIM_THM] ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vEXTENSIONAL_EQ ---->
  vEXISTS_TAC (parse_term "k:K->bool") ----> vASM_REWRITE_TAC[vIN]);;

let vCARTESIAN_PRODUCT_EQ_MEMBERS_EQ = try Cache.lookup_thm "CARTESIAN_PRODUCT_EQ_MEMBERS_EQ" with _ ->  prove
 ((parse_term "!k s x y.\n        x IN cartesian_product k s /\\\n        y IN cartesian_product k s\n        ==> (x = y <=> !i. i IN k ==> x i = y i)"),
  vMESON_TAC[vCARTESIAN_PRODUCT_EQ_MEMBERS]);;

let vSUBSET_CARTESIAN_PRODUCT = try Cache.lookup_thm "SUBSET_CARTESIAN_PRODUCT" with _ ->  prove
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

let vCARTESIAN_PRODUCT_EQ = try Cache.lookup_thm "CARTESIAN_PRODUCT_EQ" with _ ->  prove
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

let vINTER_CARTESIAN_PRODUCT = try Cache.lookup_thm "INTER_CARTESIAN_PRODUCT" with _ ->  prove
 ((parse_term "!k s t:K->A->bool.\n        (cartesian_product k s) INTER (cartesian_product k t) =\n        cartesian_product k (\\i. s i INTER t i)"),
  vREWRITE_TAC[vEXTENSION; cartesian_product; vIN_INTER; vIN_ELIM_THM] ---->
  vSET_TAC[]);;

let vCARTESIAN_PRODUCT_UNIV = try Cache.lookup_thm "CARTESIAN_PRODUCT_UNIV" with _ ->  prove
 ((parse_term "cartesian_product (:K) (\\i. (:A)) = (:K->A)"),
  vREWRITE_TAC[vEXTENSION; vIN_UNIV; cartesian_product; vIN_ELIM_THM] ---->
  vREWRITE_TAC[vEXTENSIONAL_UNIV]);;

let vCARTESIAN_PRODUCT_SINGS = try Cache.lookup_thm "CARTESIAN_PRODUCT_SINGS" with _ ->  prove
 ((parse_term "!k x:K->A. EXTENSIONAL k x ==> cartesian_product k (\\i. {x i}) = {x}"),
  vREWRITE_TAC[cartesian_product; vIN_SING] ---->
  vREWRITE_TAC[vEXTENSION; vEXTENSIONAL; vIN_ELIM_THM; vIN_SING] ---->
  vREWRITE_TAC[vFUN_EQ_THM] ----> vMESON_TAC[]);;

let vCARTESIAN_PRODUCT_SINGS_GEN = try Cache.lookup_thm "CARTESIAN_PRODUCT_SINGS_GEN" with _ ->  prove
 ((parse_term "!k x. cartesian_product k (\\i. {x i}) = {RESTRICTION k x}"),
  vREWRITE_TAC[cartesian_product; vIN_SING] ---->
  vREWRITE_TAC[vEXTENSION; vEXTENSIONAL; vIN_ELIM_THM; vIN_SING] ---->
  vREWRITE_TAC[vFUN_EQ_THM; vRESTRICTION] ----> vMESON_TAC[]);;

let vIMAGE_PROJECTION_CARTESIAN_PRODUCT = try Cache.lookup_thm "IMAGE_PROJECTION_CARTESIAN_PRODUCT" with _ ->  prove
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

let vFORALL_CARTESIAN_PRODUCT_ELEMENTS = try Cache.lookup_thm "FORALL_CARTESIAN_PRODUCT_ELEMENTS" with _ ->  prove
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

let vFORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ = try Cache.lookup_thm "FORALL_CARTESIAN_PRODUCT_ELEMENTS_EQ" with _ ->  prove
 ((parse_term "!P k s.\n        ~(cartesian_product k s = {})\n        ==> ((!i x. i IN k /\\ x IN s i ==> P i x) <=>\n             !z i. z IN cartesian_product k s /\\ i IN k ==> P i (z i))"),
  vSIMP_TAC[vFORALL_CARTESIAN_PRODUCT_ELEMENTS]);;

let vEXISTS_CARTESIAN_PRODUCT_ELEMENT = try Cache.lookup_thm "EXISTS_CARTESIAN_PRODUCT_ELEMENT" with _ ->  prove
 ((parse_term "!P k s:K->A->bool.\n        (?z. z IN cartesian_product k s /\\ (!i. i IN k ==> P i (z i))) <=>\n        (!i. i IN k ==> ?x. x IN (s i) /\\ P i x)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vCARTESIAN_PRODUCT_AS_RESTRICTIONS; vEXISTS_IN_GSPEC] ---->
  vSIMP_TAC[vRESTRICTION] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Product of a family of maps.                                              *)
(* ------------------------------------------------------------------------- *)

let product_map = new_definition
 (parse_term "product_map k (f:K->A->B) = \\x. RESTRICTION k (\\i. f i (x i))");;

let vPRODUCT_MAP_RESTRICTION = try Cache.lookup_thm "PRODUCT_MAP_RESTRICTION" with _ ->  prove
 ((parse_term "!(f:K->A->B) k x.\n        product_map k f (RESTRICTION k x) = RESTRICTION k (\\i. f i (x i))"),
  vSIMP_TAC[product_map; vRESTRICTION; o_THM; vFUN_EQ_THM]);;

let vIMAGE_PRODUCT_MAP = try Cache.lookup_thm "IMAGE_PRODUCT_MAP" with _ ->  prove
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

let vSUBSET_DISJOINT_UNION = try Cache.lookup_thm "SUBSET_DISJOINT_UNION" with _ ->  prove
 ((parse_term "!k (s:K->A->bool) t.\n        disjoint_union k s SUBSET disjoint_union k t <=>\n        !i. i IN k ==> s i SUBSET t i"),
  vREWRITE_TAC[vSUBSET; disjoint_union; vFORALL_IN_GSPEC] ---->
  vREWRITE_TAC[vIN_ELIM_PAIR_THM] ----> vSET_TAC[]);;

let vDISJOINT_UNION_EQ = try Cache.lookup_thm "DISJOINT_UNION_EQ" with _ ->  prove
 ((parse_term "!k (s:K->A->bool) t.\n        disjoint_union k s = disjoint_union k t <=>\n        !i. i IN k ==> s i = t i"),
  vREWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET_DISJOINT_UNION] ---->
  vSET_TAC[]);;

let vSUBSET_DISJOINT_UNION_EXISTS = try Cache.lookup_thm "SUBSET_DISJOINT_UNION_EXISTS" with _ ->  prove
 ((parse_term "!k (s:K->A->bool) u.\n        u SUBSET disjoint_union k s <=>\n        ?t. u = disjoint_union k t /\\ !i. i IN k ==> t i SUBSET s i"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC; vMESON_TAC[vSUBSET_DISJOINT_UNION]] ---->
  vEXISTS_TAC (parse_term "\\i. {x | (i,x) IN (u:K#A->bool)}") ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vSUBSET; vEXTENSION] ---->
  vREWRITE_TAC[disjoint_union; vFORALL_PAIR_THM; vIN_ELIM_PAIR_THM] ---->
  vSET_TAC[]);;

let vINTER_DISJOINT_UNION = try Cache.lookup_thm "INTER_DISJOINT_UNION" with _ ->  prove
 ((parse_term "!k s t:K->A->bool.\n        (disjoint_union k s) INTER (disjoint_union k t) =\n        disjoint_union k (\\i. s i INTER t i)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vEXTENSION; disjoint_union; vIN_INTER; vIN_ELIM_THM] ---->
  vMESON_TAC[vPAIR_EQ]);;

let vUNION_DISJOINT_UNION = try Cache.lookup_thm "UNION_DISJOINT_UNION" with _ ->  prove
 ((parse_term "!k s t:K->A->bool.\n        (disjoint_union k s) UNION (disjoint_union k t) =\n        disjoint_union k (\\i. s i UNION t i)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vEXTENSION; disjoint_union; vIN_UNION; vIN_ELIM_THM] ---->
  vMESON_TAC[vPAIR_EQ]);;

let vDISJOINT_UNION_EQ_EMPTY = try Cache.lookup_thm "DISJOINT_UNION_EQ_EMPTY" with _ ->  prove
 ((parse_term "!k s:K->A->bool.\n        disjoint_union k s = {} <=> !i. i IN k ==> s i = {}"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PAIR_THM; disjoint_union; vIN_ELIM_PAIR_THM;
              vNOT_IN_EMPTY] ---->
  vSET_TAC[]);;

let vDISJOINT_DISJOINT_UNION = try Cache.lookup_thm "DISJOINT_DISJOINT_UNION" with _ ->  prove
 ((parse_term "!k s t:K->A->bool.\n        DISJOINT (disjoint_union k s) (disjoint_union k t) =\n        !i. i IN k ==> DISJOINT (s i) (t i)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vDISJOINT; vINTER_DISJOINT_UNION; vDISJOINT_UNION_EQ_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of functions with bounded domain (support) and range.         *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_FUNSPACE = try Cache.lookup_thm "HAS_SIZE_FUNSPACE" with _ ->  prove
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

let vCARD_FUNSPACE = try Cache.lookup_thm "CARD_FUNSPACE" with _ ->  prove
 ((parse_term "!s t. FINITE s /\\ FINITE t\n         ==> (CARD {f | (!x. x IN s ==> f(x) IN t) /\\\n                        (!x. ~(x IN s) ==> (f x = d))} =\n              (CARD t) EXP (CARD s))"),
  vMESON_TAC[vHAS_SIZE_FUNSPACE; vHAS_SIZE]);;

let vFINITE_FUNSPACE = try Cache.lookup_thm "FINITE_FUNSPACE" with _ ->  prove
 ((parse_term "!s t. FINITE s /\\ FINITE t\n         ==> FINITE {f | (!x. x IN s ==> f(x) IN t) /\\\n                         (!x. ~(x IN s) ==> (f x = d))}"),
  vMESON_TAC[vHAS_SIZE_FUNSPACE; vHAS_SIZE]);;

let vHAS_SIZE_FUNSPACE_UNIV = try Cache.lookup_thm "HAS_SIZE_FUNSPACE_UNIV" with _ ->  prove
 ((parse_term "!m n. (:A) HAS_SIZE m /\\ (:B) HAS_SIZE n ==> (:A->B) HAS_SIZE (n EXP m)"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vHAS_SIZE_FUNSPACE) ---->
  vREWRITE_TAC[vIN_UNIV; vUNIV_GSPEC]);;

let vCARD_FUNSPACE_UNIV = try Cache.lookup_thm "CARD_FUNSPACE_UNIV" with _ ->  prove
 ((parse_term "FINITE(:A) /\\ FINITE(:B) ==> CARD(:A->B) = CARD(:B) EXP CARD(:A)"),
  vMESON_TAC[vHAS_SIZE_FUNSPACE_UNIV; vHAS_SIZE]);;

let vFINITE_FUNSPACE_UNIV = try Cache.lookup_thm "FINITE_FUNSPACE_UNIV" with _ ->  prove
 ((parse_term "FINITE(:A) /\\ FINITE(:B) ==> FINITE(:A->B)"),
  vMESON_TAC[vHAS_SIZE_FUNSPACE_UNIV; vHAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Cardinality of type bool.                                                 *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_BOOL = try Cache.lookup_thm "HAS_SIZE_BOOL" with _ ->  prove
 ((parse_term "(:bool) HAS_SIZE 2"),
  vSUBGOAL_THEN (parse_term "(:bool) = {F,T}") vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_INSERT] ----> vCONV_TAC vTAUT;
    vSIMP_TAC[vHAS_SIZE; vCARD_CLAUSES; vFINITE_INSERT; vFINITE_EMPTY; vARITH;
             vIN_SING; vNOT_IN_EMPTY]]);;

let vCARD_BOOL = try Cache.lookup_thm "CARD_BOOL" with _ ->  prove
 ((parse_term "CARD(:bool) = 2"),
  vMESON_TAC[vHAS_SIZE_BOOL; vHAS_SIZE]);;

let vFINITE_BOOL = try Cache.lookup_thm "FINITE_BOOL" with _ ->  prove
 ((parse_term "FINITE(:bool)"),
  vMESON_TAC[vHAS_SIZE_BOOL; vHAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Hence cardinality of powerset.                                            *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_POWERSET = try Cache.lookup_thm "HAS_SIZE_POWERSET" with _ ->  prove
 ((parse_term "!(s:A->bool) n. s HAS_SIZE n ==> {t | t SUBSET s} HAS_SIZE (2 EXP n)"),
  vREPEAT vSTRIP_TAC ----> vSUBGOAL_THEN
   (parse_term "{t | t SUBSET s} =\n    {f | (!x:A. x IN s ==> f(x) IN UNIV) /\\ (!x. ~(x IN s) ==> (f x = F))}")
  vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vIN_UNIV; vSUBSET; vIN; vCONTRAPOS_THM];
    vMATCH_MP_TAC vHAS_SIZE_FUNSPACE ----> vASM_REWRITE_TAC[] ---->
    vCONV_TAC vHAS_SIZE_CONV ----> vMAP_EVERY vEXISTS_TAC [(parse_term "T"); (parse_term "F")] ---->
    vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_INSERT; vNOT_IN_EMPTY] ---->
    vCONV_TAC vTAUT]);;

let vCARD_POWERSET = try Cache.lookup_thm "CARD_POWERSET" with _ ->  prove
 ((parse_term "!s:A->bool. FINITE s ==> (CARD {t | t SUBSET s} = 2 EXP (CARD s))"),
  vMESON_TAC[vHAS_SIZE_POWERSET; vHAS_SIZE]);;

let vFINITE_POWERSET = try Cache.lookup_thm "FINITE_POWERSET" with _ ->  prove
 ((parse_term "!s:A->bool. FINITE s ==> FINITE {t | t SUBSET s}"),
  vMESON_TAC[vHAS_SIZE_POWERSET; vHAS_SIZE]);;

let vFINITE_POWERSET_EQ = try Cache.lookup_thm "FINITE_POWERSET_EQ" with _ ->  prove
 ((parse_term "!s:A->bool. FINITE {t | t SUBSET s} <=> FINITE s"),
  vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vFINITE_POWERSET] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN (parse_term "FINITE(IMAGE (\\x:A. {x}) s)") vMP_TAC ++-->
   [vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vREWRITE_RULE[vIMP_CONJ]
        vFINITE_SUBSET)) ---->
    vSIMP_TAC[vSUBSET; vFORALL_IN_IMAGE; vIN_ELIM_THM; vIN_SING];
    vMATCH_MP_TAC vEQ_IMP ----> vMATCH_MP_TAC vFINITE_IMAGE_INJ_EQ ---->
    vSET_TAC[]]);;

let vFINITE_RESTRICTED_SUBSETS = try Cache.lookup_thm "FINITE_RESTRICTED_SUBSETS" with _ ->  prove
 ((parse_term "!P s:A->bool. FINITE s ==> FINITE {t | t SUBSET s /\\ P t}"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC (parse_term "{t:A->bool | t SUBSET s}") ---->
  vASM_SIMP_TAC[vFINITE_POWERSET] ----> vSET_TAC[]);;

let vFINITE_UNIONS = try Cache.lookup_thm "FINITE_UNIONS" with _ ->  prove
 ((parse_term "!s:(A->bool)->bool.\n        FINITE(UNIONS s) <=> FINITE s /\\ (!t. t IN s ==> FINITE t)"),
  vGEN_TAC ----> vASM_CASES_TAC (parse_term "FINITE(s:(A->bool)->bool)") ---->
  vASM_SIMP_TAC[vFINITE_FINITE_UNIONS] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vFINITE_POWERSET) ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vCONTRAPOS_THM] ---->
  vMATCH_MP_TAC(vREWRITE_RULE[vIMP_CONJ_ALT] vFINITE_SUBSET) ----> vSET_TAC[]);;

let vFINITE_CARD_LE_UNIONS = try Cache.lookup_thm "FINITE_CARD_LE_UNIONS" with _ ->  prove
 ((parse_term "!s (t:A->B->bool) m n.\n        (!x. x IN s ==> FINITE(t x) /\\ CARD(t x) <= n) /\\\n        FINITE s /\\ CARD s <= m\n        ==> FINITE(UNIONS {t x | x IN s}) /\\\n            CARD(UNIONS {t x | x IN s}) <= m * n"),
  vREPEAT vSTRIP_TAC ---->
  vASM_SIMP_TAC[vFINITE_UNIONS; vFORALL_IN_GSPEC; vFINITE_IMAGE; vSIMPLE_IMAGE] ---->
  vTRANS_TAC vLE_TRANS (parse_term "CARD(s:A->bool) * n") ---->
  vASM_REWRITE_TAC[vGSYM vSIMPLE_IMAGE; vLE_MULT_RCANCEL] ---->
  vMATCH_MP_TAC vCARD_UNIONS_LE ----> vASM_REWRITE_TAC[vHAS_SIZE]);;

let vPOWERSET_CLAUSES = try Cache.lookup_thm "POWERSET_CLAUSES" with _ ->  prove
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

let vFINITE_IMAGE_INFINITE = try Cache.lookup_thm "FINITE_IMAGE_INFINITE" with _ ->  prove
 ((parse_term "!f:A->B s.\n        INFINITE s /\\ FINITE(IMAGE f s)\n        ==> ?a. a IN s /\\ INFINITE {x | x IN s /\\ f x = f a}"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ_ALT] ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC vI [vGSYM vCONTRAPOS_THM] ---->
  vREWRITE_TAC[vNOT_EXISTS_THM; vINFINITE; vTAUT (parse_term "~(p /\\ q) <=> p ==> ~q")] ---->
  vDISCH_TAC ---->
  vSUBGOAL_THEN (parse_term "s = UNIONS {{x | x IN s /\\ (f:A->B) x = y} |y| y IN IMAGE f s}")
  vSUBST1_TAC ++--> [vREWRITE_TAC[vUNIONS_GSPEC] ----> vSET_TAC[]; vALL_TAC] ---->
  vASM_SIMP_TAC[vFINITE_UNIONS; vSIMPLE_IMAGE; vFINITE_IMAGE; vFORALL_IN_IMAGE]);;

let vFINITE_RESTRICTED_POWERSET = try Cache.lookup_thm "FINITE_RESTRICTED_POWERSET" with _ ->  prove
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

let vFINITE_RESTRICTED_FUNSPACE = try Cache.lookup_thm "FINITE_RESTRICTED_FUNSPACE" with _ ->  prove
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

let vNUMSEG_CLAUSES_LT = try Cache.lookup_thm "NUMSEG_CLAUSES_LT" with _ ->  prove
 ((parse_term "{i | i < 0} = {} /\\\n   (!k. {i | i < SUC k} = k INSERT {i | i < k})"),
  vREWRITE_TAC[vLT] ----> vSET_TAC[]);;

let vHAS_SIZE_NUMSEG_LT = try Cache.lookup_thm "HAS_SIZE_NUMSEG_LT" with _ ->  prove
 ((parse_term "!n. {m | m < n} HAS_SIZE n"),
  vREWRITE_TAC[vHAS_SIZE] ----> vINDUCT_TAC ---->
  vASM_SIMP_TAC[vNUMSEG_CLAUSES_LT; vFINITE_EMPTY; vCARD_CLAUSES; vFINITE_INSERT;
               vIN_ELIM_THM; vLT_REFL]);;

let vCARD_NUMSEG_LT = try Cache.lookup_thm "CARD_NUMSEG_LT" with _ ->  prove
 ((parse_term "!n. CARD {m | m < n} = n"),
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vHAS_SIZE_NUMSEG_LT]);;

let vFINITE_NUMSEG_LT = try Cache.lookup_thm "FINITE_NUMSEG_LT" with _ ->  prove
 ((parse_term "!n:num. FINITE {m | m < n}"),
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vHAS_SIZE_NUMSEG_LT]);;

let vNUMSEG_CLAUSES_LE = try Cache.lookup_thm "NUMSEG_CLAUSES_LE" with _ ->  prove
 ((parse_term "{i | i <= 0} = {0} /\\\n   (!k. {i | i <= SUC k} = SUC k INSERT {i | i <= k})"),
  vREWRITE_TAC[vLE] ----> vSET_TAC[]);;

let vHAS_SIZE_NUMSEG_LE = try Cache.lookup_thm "HAS_SIZE_NUMSEG_LE" with _ ->  prove
 ((parse_term "!n. {m | m <= n} HAS_SIZE (n + 1)"),
  vREWRITE_TAC[vGSYM vLT_SUC_LE; vHAS_SIZE_NUMSEG_LT; vADD1]);;

let vFINITE_NUMSEG_LE = try Cache.lookup_thm "FINITE_NUMSEG_LE" with _ ->  prove
 ((parse_term "!n. FINITE {m | m <= n}"),
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vHAS_SIZE_NUMSEG_LE]);;

let vCARD_NUMSEG_LE = try Cache.lookup_thm "CARD_NUMSEG_LE" with _ ->  prove
 ((parse_term "!n. CARD {m | m <= n} = n + 1"),
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vHAS_SIZE_NUMSEG_LE]);;

let num_FINITE = try Cache.lookup_thm "num_FINITE" with _ ->  prove
 ((parse_term "!s:num->bool. FINITE s <=> ?a. !x. x IN s ==> x <= a"),
  vGEN_TAC ----> vEQ_TAC ++-->
   [vSPEC_TAC((parse_term "s:num->bool"),(parse_term "s:num->bool")) ---->
    vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
    vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ----> vMESON_TAC[vLE_CASES; vLE_TRANS];
    vDISCH_THEN(vX_CHOOSE_TAC (parse_term "n:num")) ----> vMATCH_MP_TAC vFINITE_SUBSET ---->
    vEXISTS_TAC (parse_term "{m:num | m <= n}") ----> vREWRITE_TAC[vFINITE_NUMSEG_LE] ---->
    vASM_SIMP_TAC[vSUBSET; vIN_ELIM_THM]]);;

let num_FINITE_AVOID = try Cache.lookup_thm "num_FINITE_AVOID" with _ ->  prove
 ((parse_term "!s:num->bool. FINITE(s) ==> ?a. ~(a IN s)"),
  vMESON_TAC[num_FINITE; vLT; vNOT_LT]);;

let num_INFINITE_EQ = try Cache.lookup_thm "num_INFINITE_EQ" with _ ->  prove
 ((parse_term "!s:num->bool. INFINITE s <=> !N. ?n. N <= n /\\ n IN s"),
  vGEN_TAC ----> vREWRITE_TAC[vINFINITE; num_FINITE] ---->
  vMESON_TAC[vNOT_LE; vLT_IMP_LE; vLE_SUC_LT]);;

let num_INFINITE = try Cache.lookup_thm "num_INFINITE" with _ ->  prove
 ((parse_term "INFINITE(:num)"),
  vREWRITE_TAC[vINFINITE] ----> vMESON_TAC[num_FINITE_AVOID; vIN_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Set of strings is infinite.                                               *)
(* ------------------------------------------------------------------------- *)

let string_INFINITE = try Cache.lookup_thm "string_INFINITE" with _ ->  prove
 ((parse_term "INFINITE(:string)"),
  vMP_TAC num_INFINITE ----> vREWRITE_TAC[vINFINITE; vCONTRAPOS_THM] ---->
  vDISCH_THEN(vMP_TAC -| vISPEC (parse_term "LENGTH:string->num") -| vMATCH_MP vFINITE_IMAGE) ---->
  vMATCH_MP_TAC vEQ_IMP ----> vAP_TERM_TAC ---->
  vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_IMAGE] ----> vMESON_TAC[vLENGTH_REPLICATE]);;

(* ------------------------------------------------------------------------- *)
(* Non-trivial intervals of reals are infinite.                              *)
(* ------------------------------------------------------------------------- *)

let vFINITE_REAL_INTERVAL = try Cache.lookup_thm "FINITE_REAL_INTERVAL" with _ ->  prove
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

let real_INFINITE = try Cache.lookup_thm "real_INFINITE" with _ ->  prove
 ((parse_term "INFINITE(:real)"),
  vREWRITE_TAC[vINFINITE] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "{x:real | &0 <= x}") -|
        vMATCH_MP(vREWRITE_RULE[vIMP_CONJ] vFINITE_SUBSET)) ---->
  vREWRITE_TAC[vFINITE_REAL_INTERVAL; vSUBSET_UNIV]);;

(* ------------------------------------------------------------------------- *)
(* Indexing of finite sets and enumeration of subsets of N in order.         *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_INDEX = try Cache.lookup_thm "HAS_SIZE_INDEX" with _ ->  prove
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

let vINFINITE_ENUMERATE = try Cache.lookup_thm "INFINITE_ENUMERATE" with _ ->  prove
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

let vINFINITE_ENUMERATE_EQ = try Cache.lookup_thm "INFINITE_ENUMERATE_EQ" with _ ->  prove
 ((parse_term "!s:num->bool.\n     INFINITE s <=> ?r. (!m n:num. m < n ==> r m < r n) /\\ IMAGE r (:num) = s"),
  vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vINFINITE_ENUMERATE] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "r:num->num") (vSTRIP_ASSUME_TAC -| vGSYM)) ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vINFINITE_IMAGE ---->
  vREWRITE_TAC[num_INFINITE; vIN_UNIV] ---->
  vMATCH_MP_TAC vWLOG_LT ----> vASM_MESON_TAC[vLT_REFL]);;

let vINFINITE_ENUMERATE_SUBSET = try Cache.lookup_thm "INFINITE_ENUMERATE_SUBSET" with _ ->  prove
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

let vLIST_OF_SET_PROPERTIES = try Cache.lookup_thm "LIST_OF_SET_PROPERTIES" with _ ->  prove
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

let vSET_OF_LIST_OF_SET = try Cache.lookup_thm "SET_OF_LIST_OF_SET" with _ ->  prove
 ((parse_term "!s. FINITE(s) ==> (set_of_list(list_of_set s) = s)"),
  vMESON_TAC[vLIST_OF_SET_PROPERTIES]);;

let vLENGTH_LIST_OF_SET = try Cache.lookup_thm "LENGTH_LIST_OF_SET" with _ ->  prove
 ((parse_term "!s. FINITE(s) ==> (LENGTH(list_of_set s) = CARD s)"),
  vMESON_TAC[vLIST_OF_SET_PROPERTIES]);;

let vMEM_LIST_OF_SET = try Cache.lookup_thm "MEM_LIST_OF_SET" with _ ->  prove
 ((parse_term "!s:A->bool. FINITE(s) ==> !x. MEM x (list_of_set s) <=> x IN s"),
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vSET_OF_LIST_OF_SET) ---->
  vDISCH_THEN(fun th -> vGEN_REWRITE_TAC (vBINDER_CONV -| funpow 2 vRAND_CONV)
    [vGSYM th]) ---->
  vSPEC_TAC((parse_term "list_of_set(s:A->bool)"),(parse_term "l:A list")) ---->
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vMEM; set_of_list; vNOT_IN_EMPTY] ---->
  vASM_REWRITE_TAC[vIN_INSERT]);;

let vFINITE_SET_OF_LIST = try Cache.lookup_thm "FINITE_SET_OF_LIST" with _ ->  prove
 ((parse_term "!l. FINITE(set_of_list l)"),
  vLIST_INDUCT_TAC ----> vASM_SIMP_TAC[set_of_list; vFINITE_RULES]);;

let vIN_SET_OF_LIST = try Cache.lookup_thm "IN_SET_OF_LIST" with _ ->  prove
 ((parse_term "!x l. x IN (set_of_list l) <=> MEM x l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY; vMEM; set_of_list] ---->
  vASM_MESON_TAC[]);;

let vSET_OF_LIST_APPEND = try Cache.lookup_thm "SET_OF_LIST_APPEND" with _ ->  prove
 ((parse_term "!l1 l2. set_of_list(APPEND l1 l2) = set_of_list(l1) UNION set_of_list(l2)"),
  vREWRITE_TAC[vEXTENSION; vIN_SET_OF_LIST; vIN_UNION; vMEM_APPEND]);;

let vSET_OF_LIST_MAP = try Cache.lookup_thm "SET_OF_LIST_MAP" with _ ->  prove
 ((parse_term "!f l. set_of_list(MAP f l) = IMAGE f (set_of_list l)"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[set_of_list; vMAP; vIMAGE_CLAUSES]);;

let vSET_OF_LIST_EQ_EMPTY = try Cache.lookup_thm "SET_OF_LIST_EQ_EMPTY" with _ ->  prove
 ((parse_term "!l. set_of_list l = {} <=> l = []"),
  vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[set_of_list; vNOT_CONS_NIL; vNOT_INSERT_EMPTY]);;

let vLIST_OF_SET_EMPTY = try Cache.lookup_thm "LIST_OF_SET_EMPTY" with _ ->  prove
 ((parse_term "list_of_set {} = []"),
  vREWRITE_TAC[vGSYM vLENGTH_EQ_NIL] ---->
  vSIMP_TAC[vLENGTH_LIST_OF_SET; vFINITE_EMPTY; vCARD_CLAUSES]);;

let vLIST_OF_SET_SING = try Cache.lookup_thm "LIST_OF_SET_SING" with _ ->  prove
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

let vPAIRWISE_EMPTY = try Cache.lookup_thm "PAIRWISE_EMPTY" with _ ->  prove
 ((parse_term "!r. pairwise r {} <=> T"),
  vREWRITE_TAC[pairwise; vNOT_IN_EMPTY] ----> vMESON_TAC[]);;

let vPAIRWISE_SING = try Cache.lookup_thm "PAIRWISE_SING" with _ ->  prove
 ((parse_term "!r x. pairwise r {x} <=> T"),
  vREWRITE_TAC[pairwise; vIN_SING] ----> vMESON_TAC[]);;

let vPAIRWISE_IMP = try Cache.lookup_thm "PAIRWISE_IMP" with _ ->  prove
 ((parse_term "!P Q s:A->bool.\n        pairwise P s /\\\n        (!x y. x IN s /\\ y IN s /\\ P x y /\\ ~(x = y) ==> Q x y)\n        ==> pairwise Q s"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vPAIRWISE_MONO = try Cache.lookup_thm "PAIRWISE_MONO" with _ ->  prove
 ((parse_term "!r s t. pairwise r s /\\ t SUBSET s ==> pairwise r t"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vPAIRWISE_AND = try Cache.lookup_thm "PAIRWISE_AND" with _ ->  prove
 ((parse_term "!R R' s. pairwise R s /\\ pairwise R' s <=>\n            pairwise (\\x y. R x y /\\ R' x y) s"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vPAIRWISE_INSERT = try Cache.lookup_thm "PAIRWISE_INSERT" with _ ->  prove
 ((parse_term "!r x s.\n        pairwise r (x INSERT s) <=>\n        (!y. y IN s /\\ ~(y = x) ==> r x y /\\ r y x) /\\\n        pairwise r s"),
  vREWRITE_TAC[pairwise; vIN_INSERT] ----> vMESON_TAC[]);;

let vPAIRWISE_INSERT_SYMMETRIC = try Cache.lookup_thm "PAIRWISE_INSERT_SYMMETRIC" with _ ->  prove
 ((parse_term "!r (x:A) s.\n        (!y. y IN s ==> (r x y <=> r y x))\n        ==> (pairwise r (x INSERT s) <=>\n             (!y. y IN s /\\ ~(y = x) ==> r x y) /\\ pairwise r s)"),
  vREWRITE_TAC[vPAIRWISE_INSERT] ----> vMESON_TAC[]);;

let vPAIRWISE_IMAGE = try Cache.lookup_thm "PAIRWISE_IMAGE" with _ ->  prove
 ((parse_term "!r f. pairwise r (IMAGE f s) <=>\n         pairwise (\\x y. ~(f x = f y) ==> r (f x) (f y)) s"),
  vREWRITE_TAC[pairwise; vIN_IMAGE] ----> vMESON_TAC[]);;

let vPAIRWISE_UNION = try Cache.lookup_thm "PAIRWISE_UNION" with _ ->  prove
 ((parse_term "!R s t. pairwise R (s UNION t) <=>\n           pairwise R s /\\ pairwise R t /\\\n           (!x y. x IN s DIFF t /\\ y IN t DIFF s ==> R x y /\\ R y x)"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vPAIRWISE_CHAIN_UNIONS = try Cache.lookup_thm "PAIRWISE_CHAIN_UNIONS" with _ ->  prove
 ((parse_term "!R:A->A->bool c.\n        (!s. s IN c ==> pairwise R s) /\\\n        (!s t. s IN c /\\ t IN c ==> s SUBSET t \\/ t SUBSET s)\n        ==> pairwise R (UNIONS c)"),
  vREWRITE_TAC[pairwise] ----> vSET_TAC[]);;

let vDIFF_UNIONS_PAIRWISE_DISJOINT = try Cache.lookup_thm "DIFF_UNIONS_PAIRWISE_DISJOINT" with _ ->  prove
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

let vINTER_UNIONS_PAIRWISE_DISJOINT = try Cache.lookup_thm "INTER_UNIONS_PAIRWISE_DISJOINT" with _ ->  prove
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

let vPSUBSET_UNIONS_PAIRWISE_DISJOINT = try Cache.lookup_thm "PSUBSET_UNIONS_PAIRWISE_DISJOINT" with _ ->  prove
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

let vUNION_OF_INC = try Cache.lookup_thm "UNION_OF_INC" with _ ->  prove
 ((parse_term "!P Q s:A->bool. P {s} /\\ Q s ==> (P UNION_OF Q) s"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vUNION_OF] ---->
  vEXISTS_TAC (parse_term "{s:A->bool}") ----> vASM_SIMP_TAC[vUNIONS_1; vIN_SING]);;

let vINTERSECTION_OF_INC = try Cache.lookup_thm "INTERSECTION_OF_INC" with _ ->  prove
 ((parse_term "!P Q s:A->bool. P {s} /\\ Q s ==> (P INTERSECTION_OF Q) s"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vINTERSECTION_OF] ---->
  vEXISTS_TAC (parse_term "{s:A->bool}") ----> vASM_SIMP_TAC[vINTERS_1; vIN_SING]);;

let vUNION_OF_MONO = try Cache.lookup_thm "UNION_OF_MONO" with _ ->  prove
 ((parse_term "!P Q Q' s:A->bool.\n        (P UNION_OF Q) s /\\ (!x. Q x ==> Q' x) ==> (P UNION_OF Q') s"),
  vREWRITE_TAC[vUNION_OF] ----> vMESON_TAC[]);;

let vINTERSECTION_OF_MONO = try Cache.lookup_thm "INTERSECTION_OF_MONO" with _ ->  prove
 ((parse_term "!P Q Q' s:A->bool.\n        (P INTERSECTION_OF Q) s /\\ (!x. Q x ==> Q' x)\n        ==> (P INTERSECTION_OF Q') s"),
  vREWRITE_TAC[vINTERSECTION_OF] ----> vMESON_TAC[]);;

let vFORALL_UNION_OF = try Cache.lookup_thm "FORALL_UNION_OF" with _ ->  prove
 ((parse_term "(!s. (P UNION_OF Q) s ==> R s) <=>\n   (!t. P t /\\ (!c. c IN t ==> Q c) ==> R(UNIONS t))"),
  vREWRITE_TAC[vUNION_OF] ----> vMESON_TAC[]);;

let vFORALL_INTERSECTION_OF = try Cache.lookup_thm "FORALL_INTERSECTION_OF" with _ ->  prove
 ((parse_term "(!s. (P INTERSECTION_OF Q) s ==> R s) <=>\n   (!t. P t /\\ (!c. c IN t ==> Q c) ==> R(INTERS t))"),
  vREWRITE_TAC[vINTERSECTION_OF] ----> vMESON_TAC[]);;

let vUNION_OF_EMPTY = try Cache.lookup_thm "UNION_OF_EMPTY" with _ ->  prove
 ((parse_term "!P Q:(A->bool)->bool. P {} ==> (P UNION_OF Q) {}"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vUNION_OF] ---->
  vEXISTS_TAC (parse_term "{}:(A->bool)->bool") ---->
  vASM_REWRITE_TAC[vUNIONS_0; vNOT_IN_EMPTY]);;

let vINTERSECTION_OF_EMPTY = try Cache.lookup_thm "INTERSECTION_OF_EMPTY" with _ ->  prove
 ((parse_term "!P Q:(A->bool)->bool. P {} ==> (P INTERSECTION_OF Q) UNIV"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vINTERSECTION_OF] ---->
  vEXISTS_TAC (parse_term "{}:(A->bool)->bool") ---->
  vASM_REWRITE_TAC[vINTERS_0; vNOT_IN_EMPTY]);;

(* ------------------------------------------------------------------------- *)
(* The ARBITRARY and FINITE cases of UNION_OF / INTERSECTION_OF              *)
(* ------------------------------------------------------------------------- *)

let vARBITRARY = new_definition
 (parse_term "ARBITRARY (s:(A->bool)->bool) <=> T");;

let vARBITRARY_UNION_OF_ALT = try Cache.lookup_thm "ARBITRARY_UNION_OF_ALT" with _ ->  prove
 ((parse_term "!B s:A->bool.\n        (ARBITRARY UNION_OF B) s <=>\n        !x. x IN s ==>  ?u. u IN B /\\ x IN u /\\ u SUBSET s"),
  vGEN_TAC ----> vREWRITE_TAC[vFORALL_AND_THM; vTAUT
   (parse_term "(p <=> q) <=> (p ==> q) /\\ (q ==> p)")] ---->
  vREWRITE_TAC[vFORALL_UNION_OF; vARBITRARY] ---->
  vCONJ_TAC ++--> [vSET_TAC[]; vALL_TAC] ---->
  vX_GEN_TAC (parse_term "s:A->bool") ----> vDISCH_TAC ---->
  vREWRITE_TAC[vARBITRARY; vUNION_OF] ---->
  vEXISTS_TAC (parse_term "{u:A->bool | u IN B /\\ u SUBSET s}") ----> vASM vSET_TAC[]);;

let vARBITRARY_UNION_OF_EMPTY = try Cache.lookup_thm "ARBITRARY_UNION_OF_EMPTY" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool. (ARBITRARY UNION_OF P) {}"),
  vSIMP_TAC[vUNION_OF_EMPTY; vARBITRARY]);;

let vARBITRARY_INTERSECTION_OF_EMPTY = try Cache.lookup_thm "ARBITRARY_INTERSECTION_OF_EMPTY" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool. (ARBITRARY INTERSECTION_OF P) UNIV"),
  vSIMP_TAC[vINTERSECTION_OF_EMPTY; vARBITRARY]);;

let vARBITRARY_UNION_OF_INC = try Cache.lookup_thm "ARBITRARY_UNION_OF_INC" with _ ->  prove
 ((parse_term "!P s:A->bool. P s ==> (ARBITRARY UNION_OF P) s"),
  vSIMP_TAC[vUNION_OF_INC; vARBITRARY]);;

let vARBITRARY_INTERSECTION_OF_INC = try Cache.lookup_thm "ARBITRARY_INTERSECTION_OF_INC" with _ ->  prove
 ((parse_term "!P s:A->bool. P s ==> (ARBITRARY INTERSECTION_OF P) s"),
  vSIMP_TAC[vINTERSECTION_OF_INC; vARBITRARY]);;

let vARBITRARY_UNION_OF_COMPLEMENT = try Cache.lookup_thm "ARBITRARY_UNION_OF_COMPLEMENT" with _ ->  prove
 ((parse_term "!P s. (ARBITRARY UNION_OF P) s <=>\n         (ARBITRARY INTERSECTION_OF (\\s. P((:A) DIFF s))) ((:A) DIFF s)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vUNION_OF; vINTERSECTION_OF] ---->
  vEQ_TAC ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "u:(A->bool)->bool") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "IMAGE (\\c. (:A) DIFF c) u") ---->
  vASM_SIMP_TAC[vARBITRARY; vFORALL_IN_IMAGE; vCOMPL_COMPL] ---->
  vONCE_REWRITE_TAC[vUNIONS_INTERS; vINTERS_UNIONS] ---->
  vREWRITE_TAC[vSET_RULE (parse_term "{f y | y IN IMAGE g s} = IMAGE (\\x. f(g x)) s")] ---->
  vASM_REWRITE_TAC[vIMAGE_ID; vCOMPL_COMPL]);;

let vARBITRARY_INTERSECTION_OF_COMPLEMENT = try Cache.lookup_thm "ARBITRARY_INTERSECTION_OF_COMPLEMENT" with _ ->  prove
 ((parse_term "!P s. (ARBITRARY INTERSECTION_OF P) s <=>\n         (ARBITRARY UNION_OF (\\s. P((:A) DIFF s))) ((:A) DIFF s)"),
  vREWRITE_TAC[vARBITRARY_UNION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vETA_AX; vCOMPL_COMPL]);;

let vARBITRARY_UNION_OF_IDEMPOT = try Cache.lookup_thm "ARBITRARY_UNION_OF_IDEMPOT" with _ ->  prove
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

let vARBITRARY_INTERSECTION_OF_IDEMPOT = try Cache.lookup_thm "ARBITRARY_INTERSECTION_OF_IDEMPOT" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool.\n        ARBITRARY INTERSECTION_OF ARBITRARY INTERSECTION_OF P =\n        ARBITRARY INTERSECTION_OF P"),
  vREWRITE_TAC[vCOMPL_COMPL; vETA_AX; vREWRITE_RULE[vGSYM vFUN_EQ_THM; vETA_AX]
              vARBITRARY_INTERSECTION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vARBITRARY_UNION_OF_IDEMPOT]);;

let vARBITRARY_UNION_OF_UNIONS = try Cache.lookup_thm "ARBITRARY_UNION_OF_UNIONS" with _ ->  prove
 ((parse_term "!P u:(A->bool)->bool.\n        (!s. s IN u ==> (ARBITRARY UNION_OF P) s)\n        ==> (ARBITRARY UNION_OF P) (UNIONS u)"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vARBITRARY_UNION_OF_IDEMPOT] ---->
  vONCE_REWRITE_TAC[vUNION_OF] ----> vREWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "u:(A->bool)->bool") ----> vASM_REWRITE_TAC[vARBITRARY]);;

let vARBITRARY_UNION_OF_UNION = try Cache.lookup_thm "ARBITRARY_UNION_OF_UNION" with _ ->  prove
 ((parse_term "!P s t. (ARBITRARY UNION_OF P) s /\\ (ARBITRARY UNION_OF P) t\n           ==> (ARBITRARY UNION_OF P) (s UNION t)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vUNIONS_2] ---->
  vMATCH_MP_TAC vARBITRARY_UNION_OF_UNIONS ---->
  vASM_REWRITE_TAC[vARBITRARY; vFORALL_IN_INSERT] ---->
  vREWRITE_TAC[vARBITRARY; vNOT_IN_EMPTY]);;

let vARBITRARY_INTERSECTION_OF_INTERS = try Cache.lookup_thm "ARBITRARY_INTERSECTION_OF_INTERS" with _ ->  prove
 ((parse_term "!P u:(A->bool)->bool.\n        (!s. s IN u ==> (ARBITRARY INTERSECTION_OF P) s)\n        ==> (ARBITRARY INTERSECTION_OF P) (INTERS u)"),
  vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vARBITRARY_INTERSECTION_OF_IDEMPOT] ---->
  vONCE_REWRITE_TAC[vINTERSECTION_OF] ----> vREWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "u:(A->bool)->bool") ----> vASM_REWRITE_TAC[vARBITRARY]);;

let vARBITRARY_INTERSECTION_OF_INTER = try Cache.lookup_thm "ARBITRARY_INTERSECTION_OF_INTER" with _ ->  prove
 ((parse_term "!P s t. (ARBITRARY INTERSECTION_OF P) s /\\ (ARBITRARY INTERSECTION_OF P) t\n           ==> (ARBITRARY INTERSECTION_OF P) (s INTER t)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vINTERS_2] ---->
  vMATCH_MP_TAC vARBITRARY_INTERSECTION_OF_INTERS ---->
  vASM_REWRITE_TAC[vARBITRARY; vFORALL_IN_INSERT] ---->
  vREWRITE_TAC[vARBITRARY; vNOT_IN_EMPTY]);;

let vARBITRARY_UNION_OF_INTER_EQ = try Cache.lookup_thm "ARBITRARY_UNION_OF_INTER_EQ" with _ ->  prove
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

let vARBITRARY_UNION_OF_INTER = try Cache.lookup_thm "ARBITRARY_UNION_OF_INTER" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. P s /\\ P t ==> P(s INTER t))\n        ==> (!s t. (ARBITRARY UNION_OF P) s /\\ (ARBITRARY UNION_OF P) t\n                   ==> (ARBITRARY UNION_OF P) (s INTER t))"),
  vREWRITE_TAC[vARBITRARY_UNION_OF_INTER_EQ] ---->
  vMESON_TAC[vARBITRARY_UNION_OF_INC]);;

let vARBITRARY_INTERSECTION_OF_UNION_EQ = try Cache.lookup_thm "ARBITRARY_INTERSECTION_OF_UNION_EQ" with _ ->  prove
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

let vARBITRARY_INTERSECTION_OF_UNION = try Cache.lookup_thm "ARBITRARY_INTERSECTION_OF_UNION" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. P s /\\ P t ==> P(s UNION t))\n        ==> (!s t. (ARBITRARY INTERSECTION_OF P) s /\\\n                   (ARBITRARY INTERSECTION_OF P) t\n                   ==> (ARBITRARY INTERSECTION_OF P) (s UNION t))"),
  vREWRITE_TAC[vARBITRARY_INTERSECTION_OF_UNION_EQ] ---->
  vMESON_TAC[vARBITRARY_INTERSECTION_OF_INC]);;

let vFINITE_UNION_OF_EMPTY = try Cache.lookup_thm "FINITE_UNION_OF_EMPTY" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool. (FINITE UNION_OF P) {}"),
  vSIMP_TAC[vUNION_OF_EMPTY; vFINITE_EMPTY]);;

let vFINITE_INTERSECTION_OF_EMPTY = try Cache.lookup_thm "FINITE_INTERSECTION_OF_EMPTY" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool. (FINITE INTERSECTION_OF P) UNIV"),
  vSIMP_TAC[vINTERSECTION_OF_EMPTY; vFINITE_EMPTY]);;

let vFINITE_UNION_OF_INC = try Cache.lookup_thm "FINITE_UNION_OF_INC" with _ ->  prove
 ((parse_term "!P s:A->bool. P s ==> (FINITE UNION_OF P) s"),
  vSIMP_TAC[vUNION_OF_INC; vFINITE_SING]);;

let vFINITE_INTERSECTION_OF_INC = try Cache.lookup_thm "FINITE_INTERSECTION_OF_INC" with _ ->  prove
 ((parse_term "!P s:A->bool. P s ==> (FINITE INTERSECTION_OF P) s"),
  vSIMP_TAC[vINTERSECTION_OF_INC; vFINITE_SING]);;

let vFINITE_UNION_OF_COMPLEMENT = try Cache.lookup_thm "FINITE_UNION_OF_COMPLEMENT" with _ ->  prove
 ((parse_term "!P s. (FINITE UNION_OF P) s <=>\n         (FINITE INTERSECTION_OF (\\s. P((:A) DIFF s))) ((:A) DIFF s)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vUNION_OF; vINTERSECTION_OF] ---->
  vEQ_TAC ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "u:(A->bool)->bool") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "IMAGE (\\c. (:A) DIFF c) u") ---->
  vASM_SIMP_TAC[vFINITE_IMAGE; vFORALL_IN_IMAGE; vCOMPL_COMPL] ---->
  vONCE_REWRITE_TAC[vUNIONS_INTERS; vINTERS_UNIONS] ---->
  vREWRITE_TAC[vSET_RULE (parse_term "{f y | y IN IMAGE g s} = IMAGE (\\x. f(g x)) s")] ---->
  vASM_REWRITE_TAC[vIMAGE_ID; vCOMPL_COMPL]);;

let vFINITE_INTERSECTION_OF_COMPLEMENT = try Cache.lookup_thm "FINITE_INTERSECTION_OF_COMPLEMENT" with _ ->  prove
 ((parse_term "!P s. (FINITE INTERSECTION_OF P) s <=>\n         (FINITE UNION_OF (\\s. P((:A) DIFF s))) ((:A) DIFF s)"),
  vREWRITE_TAC[vFINITE_UNION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vETA_AX; vCOMPL_COMPL]);;

let vFINITE_UNION_OF_IDEMPOT = try Cache.lookup_thm "FINITE_UNION_OF_IDEMPOT" with _ ->  prove
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

let vFINITE_INTERSECTION_OF_IDEMPOT = try Cache.lookup_thm "FINITE_INTERSECTION_OF_IDEMPOT" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool.\n        FINITE INTERSECTION_OF FINITE INTERSECTION_OF P =\n        FINITE INTERSECTION_OF P"),
  vREWRITE_TAC[vCOMPL_COMPL; vETA_AX; vREWRITE_RULE[vGSYM vFUN_EQ_THM; vETA_AX]
              vFINITE_INTERSECTION_OF_COMPLEMENT] ---->
  vREWRITE_TAC[vFINITE_UNION_OF_IDEMPOT]);;

let vFINITE_UNION_OF_UNIONS = try Cache.lookup_thm "FINITE_UNION_OF_UNIONS" with _ ->  prove
 ((parse_term "!P u:(A->bool)->bool.\n        FINITE u /\\ (!s. s IN u ==> (FINITE UNION_OF P) s)\n        ==> (FINITE UNION_OF P) (UNIONS u)"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vFINITE_UNION_OF_IDEMPOT] ---->
  vONCE_REWRITE_TAC[vUNION_OF] ----> vREWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "u:(A->bool)->bool") ----> vASM_REWRITE_TAC[]);;

let vFINITE_UNION_OF_UNION = try Cache.lookup_thm "FINITE_UNION_OF_UNION" with _ ->  prove
 ((parse_term "!P s t. (FINITE UNION_OF P) s /\\ (FINITE UNION_OF P) t\n           ==> (FINITE UNION_OF P) (s UNION t)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vUNIONS_2] ---->
  vMATCH_MP_TAC vFINITE_UNION_OF_UNIONS ---->
  vASM_REWRITE_TAC[vFINITE_INSERT; vFORALL_IN_INSERT] ---->
  vREWRITE_TAC[vFINITE_EMPTY; vNOT_IN_EMPTY]);;

let vFINITE_INTERSECTION_OF_INTERS = try Cache.lookup_thm "FINITE_INTERSECTION_OF_INTERS" with _ ->  prove
 ((parse_term "!P u:(A->bool)->bool.\n        FINITE u /\\ (!s. s IN u ==> (FINITE INTERSECTION_OF P) s)\n        ==> (FINITE INTERSECTION_OF P) (INTERS u)"),
  vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vFINITE_INTERSECTION_OF_IDEMPOT] ---->
  vONCE_REWRITE_TAC[vINTERSECTION_OF] ----> vREWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "u:(A->bool)->bool") ----> vASM_REWRITE_TAC[]);;

let vFINITE_INTERSECTION_OF_INTER = try Cache.lookup_thm "FINITE_INTERSECTION_OF_INTER" with _ ->  prove
 ((parse_term "!P s t. (FINITE INTERSECTION_OF P) s /\\ (FINITE INTERSECTION_OF P) t\n           ==> (FINITE INTERSECTION_OF P) (s INTER t)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vINTERS_2] ---->
  vMATCH_MP_TAC vFINITE_INTERSECTION_OF_INTERS ---->
  vASM_REWRITE_TAC[vFINITE_INSERT; vFORALL_IN_INSERT] ---->
  vREWRITE_TAC[vFINITE_EMPTY; vNOT_IN_EMPTY]);;

let vFINITE_UNION_OF_INTER_EQ = try Cache.lookup_thm "FINITE_UNION_OF_INTER_EQ" with _ ->  prove
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

let vFINITE_UNION_OF_INTER = try Cache.lookup_thm "FINITE_UNION_OF_INTER" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. P s /\\ P t ==> P(s INTER t))\n        ==> (!s t. (FINITE UNION_OF P) s /\\ (FINITE UNION_OF P) t\n                   ==> (FINITE UNION_OF P) (s INTER t))"),
  vREWRITE_TAC[vFINITE_UNION_OF_INTER_EQ] ---->
  vMESON_TAC[vFINITE_UNION_OF_INC]);;

let vFINITE_INTERSECTION_OF_UNION_EQ = try Cache.lookup_thm "FINITE_INTERSECTION_OF_UNION_EQ" with _ ->  prove
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

let vFINITE_INTERSECTION_OF_UNION = try Cache.lookup_thm "FINITE_INTERSECTION_OF_UNION" with _ ->  prove
 ((parse_term "!P:(A->bool)->bool.\n        (!s t. P s /\\ P t ==> P(s UNION t))\n        ==> (!s t. (FINITE INTERSECTION_OF P) s /\\\n                   (FINITE INTERSECTION_OF P) t\n                   ==> (FINITE INTERSECTION_OF P) (s UNION t))"),
  vREWRITE_TAC[vFINITE_INTERSECTION_OF_UNION_EQ] ---->
  vMESON_TAC[vFINITE_INTERSECTION_OF_INC]);;

(* ------------------------------------------------------------------------- *)
(* Some additional properties of "set_of_list".                              *)
(* ------------------------------------------------------------------------- *)

let vCARD_SET_OF_LIST_LE = try Cache.lookup_thm "CARD_SET_OF_LIST_LE" with _ ->  prove
 ((parse_term "!l. CARD(set_of_list l) <= LENGTH l"),
  vLIST_INDUCT_TAC ---->
  vSIMP_TAC[vLENGTH; set_of_list; vCARD_CLAUSES; vFINITE_SET_OF_LIST] ---->
  vASM_ARITH_TAC);;

let vHAS_SIZE_SET_OF_LIST = try Cache.lookup_thm "HAS_SIZE_SET_OF_LIST" with _ ->  prove
 ((parse_term "!l. (set_of_list l) HAS_SIZE (LENGTH l) <=> PAIRWISE (\\x y. ~(x = y)) l"),
  vREWRITE_TAC[vHAS_SIZE; vFINITE_SET_OF_LIST] ----> vLIST_INDUCT_TAC ---->
  vASM_SIMP_TAC[vCARD_CLAUSES; vLENGTH; set_of_list; vPAIRWISE; vALL;
               vFINITE_SET_OF_LIST; vGSYM vALL_MEM; vIN_SET_OF_LIST] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vSUC_INJ] ---->
  vASM_MESON_TAC[vCARD_SET_OF_LIST_LE; vARITH_RULE (parse_term "~(SUC n <= n)")]);;

(* ------------------------------------------------------------------------- *)
(* Classic result on function of finite set into itself.                     *)
(* ------------------------------------------------------------------------- *)

let vSURJECTIVE_IFF_INJECTIVE_GEN = try Cache.lookup_thm "SURJECTIVE_IFF_INJECTIVE_GEN" with _ ->  prove
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

let vSURJECTIVE_IFF_INJECTIVE = try Cache.lookup_thm "SURJECTIVE_IFF_INJECTIVE" with _ ->  prove
 ((parse_term "!s f:A->A.\n        FINITE s /\\ (IMAGE f s) SUBSET s\n        ==> ((!y. y IN s ==> ?x. x IN s /\\ (f x = y)) <=>\n             (!x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)))"),
  vSIMP_TAC[vSURJECTIVE_IFF_INJECTIVE_GEN]);;

let vIMAGE_IMP_INJECTIVE_GEN = try Cache.lookup_thm "IMAGE_IMP_INJECTIVE_GEN" with _ ->  prove
 ((parse_term "!s t f:A->B.\n        FINITE s /\\ (CARD s = CARD t) /\\ (IMAGE f s = t)\n        ==> !x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vASSUME_TAC -| vGSYM) ---->
  vMP_TAC(vISPECL [(parse_term "s:A->bool"); (parse_term "t:B->bool"); (parse_term "f:A->B")]
                vSURJECTIVE_IFF_INJECTIVE_GEN) ---->
  vASM_SIMP_TAC[vSUBSET_REFL; vFINITE_IMAGE] ---->
  vASM_MESON_TAC[vEXTENSION; vIN_IMAGE]);;

let vIMAGE_IMP_INJECTIVE = try Cache.lookup_thm "IMAGE_IMP_INJECTIVE" with _ ->  prove
 ((parse_term "!s f. FINITE s /\\ (IMAGE f s = s)\n       ==> !x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)"),
  vMESON_TAC[vIMAGE_IMP_INJECTIVE_GEN]);;

let vHAS_SIZE_IMAGE_INJ_RESTRICT = try Cache.lookup_thm "HAS_SIZE_IMAGE_INJ_RESTRICT" with _ ->  prove
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

let vCARD_LE_INJ = try Cache.lookup_thm "CARD_LE_INJ" with _ ->  prove
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

let vFORALL_IN_CLAUSES = try Cache.lookup_thm "FORALL_IN_CLAUSES" with _ ->  prove
 ((parse_term "(!P. (!x. x IN {} ==> P x) <=> T) /\\\n   (!P a s. (!x. x IN (a INSERT s) ==> P x) <=> P a /\\ (!x. x IN s ==> P x))"),
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ----> vMESON_TAC[]);;

let vEXISTS_IN_CLAUSES = try Cache.lookup_thm "EXISTS_IN_CLAUSES" with _ ->  prove
 ((parse_term "(!P. (?x. x IN {} /\\ P x) <=> F) /\\\n   (!P a s. (?x. x IN (a INSERT s) /\\ P x) <=> P a \\/ (?x. x IN s /\\ P x))"),
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Injectivity and surjectivity of image and preimage under a function.      *)
(* ------------------------------------------------------------------------- *)

let vINJECTIVE_ON_IMAGE = try Cache.lookup_thm "INJECTIVE_ON_IMAGE" with _ ->  prove
 ((parse_term "!f:A->B u.\n    (!s t. s SUBSET u /\\ t SUBSET u /\\ IMAGE f s = IMAGE f t ==> s = t) <=>\n    (!x y. x IN u /\\ y IN u /\\ f x = f y ==> x = y)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++--> [vDISCH_TAC; vSET_TAC[]] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "y:A")] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "{x:A}"); (parse_term "{y:A}")]) ---->
  vASM_REWRITE_TAC[vSING_SUBSET; vIMAGE_CLAUSES] ----> vSET_TAC[]);;

let vINJECTIVE_IMAGE = try Cache.lookup_thm "INJECTIVE_IMAGE" with _ ->  prove
 ((parse_term "!f:A->B.\n    (!s t. IMAGE f s = IMAGE f t ==> s = t) <=> (!x y. f x = f y ==> x = y)"),
  vGEN_TAC ----> vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "(:A)")] vINJECTIVE_ON_IMAGE) ---->
  vREWRITE_TAC[vIN_UNIV; vSUBSET_UNIV]);;

let vSURJECTIVE_ON_IMAGE = try Cache.lookup_thm "SURJECTIVE_ON_IMAGE" with _ ->  prove
 ((parse_term "!f:A->B u v.\n        (!t. t SUBSET v ==> ?s. s SUBSET u /\\ IMAGE f s = t) <=>\n        (!y. y IN v ==> ?x. x IN u /\\ f x = y)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vX_GEN_TAC (parse_term "y:B") ----> vDISCH_TAC ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "{y:B}")) ----> vASM vSET_TAC[];
    vDISCH_TAC ----> vX_GEN_TAC (parse_term "t:B->bool") ----> vDISCH_TAC ---->
    vEXISTS_TAC (parse_term "{x | x IN u /\\ (f:A->B) x IN t}") ----> vASM vSET_TAC[]]);;

let vSURJECTIVE_IMAGE = try Cache.lookup_thm "SURJECTIVE_IMAGE" with _ ->  prove
 ((parse_term "!f:A->B. (!t. ?s. IMAGE f s = t) <=> (!y. ?x. f x = y)"),
  vGEN_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "(:A)"); (parse_term "(:B)")] vSURJECTIVE_ON_IMAGE) ---->
  vREWRITE_TAC[vIN_UNIV; vSUBSET_UNIV]);;

let vINJECTIVE_ON_PREIMAGE = try Cache.lookup_thm "INJECTIVE_ON_PREIMAGE" with _ ->  prove
 ((parse_term "!f:A->B s u.\n        (!t t'. t SUBSET u /\\ t' SUBSET u /\\\n                {x | x IN s /\\ f x IN t} = {x | x IN s /\\ f x IN t'}\n                ==> t = t') <=>\n        u SUBSET IMAGE f s"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++--> [vALL_TAC; vASM vSET_TAC[]] ---->
  vREWRITE_TAC[vSUBSET] ----> vX_GEN_TAC (parse_term "y:B") ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "{y:B}"); (parse_term "{}:B->bool")]) ----> vASM vSET_TAC[]);;

let vSURJECTIVE_ON_PREIMAGE = try Cache.lookup_thm "SURJECTIVE_ON_PREIMAGE" with _ ->  prove
 ((parse_term "!f:A->B s u.\n        (!k. k SUBSET s\n             ==> ?t. t SUBSET u /\\ {x | x IN s /\\ f x IN t} = k) <=>\n        IMAGE f s SUBSET u /\\\n        (!x y. x IN s /\\ y IN s /\\ f x = f y ==> x = y)"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vCONJ_TAC ++-->
     [vREWRITE_TAC[vSUBSET; vFORALL_IN_IMAGE] ----> vX_GEN_TAC (parse_term "x:A") ---->
      vDISCH_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "{x:A}")) ----> vASM vSET_TAC[];
      vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "y:A")] ----> vSTRIP_TAC ---->
      vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "{x:A}")) ----> vASM vSET_TAC[]];
    vX_GEN_TAC (parse_term "k:A->bool") ----> vSTRIP_TAC ---->
    vEXISTS_TAC (parse_term "IMAGE (f:A->B) k") ----> vASM vSET_TAC[]]);;

let vINJECTIVE_PREIMAGE = try Cache.lookup_thm "INJECTIVE_PREIMAGE" with _ ->  prove
 ((parse_term "!f:A->B.\n        (!t t'. {x | f x IN t} = {x | f x IN t'} ==> t = t') <=>\n        IMAGE f UNIV = UNIV"),
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "(:A)"); (parse_term "(:B)")]
        vINJECTIVE_ON_PREIMAGE) ---->
  vREWRITE_TAC[vIN_UNIV; vSUBSET_UNIV] ----> vSET_TAC[]);;

let vSURJECTIVE_PREIMAGE = try Cache.lookup_thm "SURJECTIVE_PREIMAGE" with _ ->  prove
 ((parse_term "!f:A->B. (!k. ?t. {x | f x IN t} = k) <=> (!x y. f x = f y ==> x = y)"),
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "(:A)"); (parse_term "(:B)")]
        vSURJECTIVE_ON_PREIMAGE) ---->
  vREWRITE_TAC[vIN_UNIV; vSUBSET_UNIV] ----> vSET_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Existence of bijections between two finite sets of same size.             *)
(* ------------------------------------------------------------------------- *)

let vCARD_EQ_BIJECTION = try Cache.lookup_thm "CARD_EQ_BIJECTION" with _ ->  prove
 ((parse_term "!s t. FINITE s /\\ FINITE t /\\ CARD s = CARD t\n   ==> ?f:A->B. (!x. x IN s ==> f(x) IN t) /\\\n                (!y. y IN t ==> ?x. x IN s /\\ f x = y) /\\\n                !x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y)"),
  vMP_TAC vCARD_LE_INJ ----> vREPEAT(vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC) ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ---->
  vASM_REWRITE_TAC[vLE_REFL] ----> vMATCH_MP_TAC vMONO_EXISTS ---->
  vASM_SIMP_TAC[vSURJECTIVE_IFF_INJECTIVE_GEN] ---->
  vMESON_TAC[vSUBSET; vIN_IMAGE]);;

let vCARD_EQ_BIJECTIONS = try Cache.lookup_thm "CARD_EQ_BIJECTIONS" with _ ->  prove
 ((parse_term "!s t. FINITE s /\\ FINITE t /\\ CARD s = CARD t\n   ==> ?f:A->B g. (!x. x IN s ==> f(x) IN t /\\ g(f x) = x) /\\\n                  (!y. y IN t ==> g(y) IN s /\\ f(g y) = y)"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vCARD_EQ_BIJECTION) ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vREWRITE_TAC[vSURJECTIVE_ON_RIGHT_INVERSE] ---->
  vGEN_TAC ----> vREWRITE_TAC[vLEFT_AND_EXISTS_THM; vRIGHT_AND_EXISTS_THM] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vMESON_TAC[]);;

let vCARD_EQ_BIJECTIONS_SPECIAL = try Cache.lookup_thm "CARD_EQ_BIJECTIONS_SPECIAL" with _ ->  prove
 ((parse_term "!s t (a:A) (b:B).\n         FINITE s /\\ FINITE t /\\ CARD s = CARD t /\\ a IN s /\\ b IN t\n         ==> ?f g. f a = b /\\ g b = a /\\\n                   (!x. x IN s ==> f x IN t /\\ g (f x) = x) /\\\n                   (!y. y IN t ==> g y IN s /\\ f (g y) = y)"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "s DELETE (a:A)"); (parse_term "t DELETE (b:B)")]
        vCARD_EQ_BIJECTIONS) ---->
  vASM_SIMP_TAC[vFINITE_DELETE; vCARD_DELETE; vIN_DELETE; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "f:A->B"); (parse_term "g:B->A")] ----> vSTRIP_TAC ---->
  vEXISTS_TAC (parse_term "\\x. if x = a then b else (f:A->B) x") ---->
  vEXISTS_TAC (parse_term "\\y. if y = b then a else (g:B->A) y") ---->
  vASM_MESON_TAC[]);;

let vBIJECTIONS_HAS_SIZE = try Cache.lookup_thm "BIJECTIONS_HAS_SIZE" with _ ->  prove
 ((parse_term "!s t f:A->B g.\n        (!x. x IN s ==> f(x) IN t /\\ g(f x) = x) /\\\n        (!y. y IN t ==> g(y) IN s /\\ f(g y) = y) /\\\n        s HAS_SIZE n\n        ==> t HAS_SIZE n"),
  vREPEAT vSTRIP_TAC ----> vSUBGOAL_THEN (parse_term "t = IMAGE (f:A->B) s") vSUBST_ALL_TAC ++-->
   [vASM vSET_TAC[];
    vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ----> vASM_MESON_TAC[]]);;

let vBIJECTIONS_HAS_SIZE_EQ = try Cache.lookup_thm "BIJECTIONS_HAS_SIZE_EQ" with _ ->  prove
 ((parse_term "!s t f:A->B g.\n        (!x. x IN s ==> f(x) IN t /\\ g(f x) = x) /\\\n        (!y. y IN t ==> g(y) IN s /\\ f(g y) = y)\n        ==> !n. s HAS_SIZE n <=> t HAS_SIZE n"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ---->
  vMATCH_MP_TAC(vONCE_REWRITE_RULE
  [vTAUT (parse_term "a /\\ b /\\ c ==> d <=> a /\\ b ==> c ==> d")] vBIJECTIONS_HAS_SIZE) ++-->
   [vMAP_EVERY vEXISTS_TAC [(parse_term "f:A->B"); (parse_term "g:B->A")];
    vMAP_EVERY vEXISTS_TAC [(parse_term "g:B->A"); (parse_term "f:A->B")]] ---->
  vASM_MESON_TAC[]);;

let vBIJECTIONS_CARD_EQ = try Cache.lookup_thm "BIJECTIONS_CARD_EQ" with _ ->  prove
 ((parse_term "!s t f:A->B g.\n        (FINITE s \\/ FINITE t) /\\\n        (!x. x IN s ==> f(x) IN t /\\ g(f x) = x) /\\\n        (!y. y IN t ==> g(y) IN s /\\ f(g y) = y)\n        ==> CARD s = CARD t"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2
   vMP_TAC (vMP_TAC -| vMATCH_MP vBIJECTIONS_HAS_SIZE_EQ)) ---->
  vMESON_TAC[vHAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Transitive relation with finitely many predecessors is wellfounded.       *)
(* ------------------------------------------------------------------------- *)

let vWF_FINITE = try Cache.lookup_thm "WF_FINITE" with _ ->  prove
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

let vWF_PSUBSET = try Cache.lookup_thm "WF_PSUBSET" with _ ->  prove
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

let vLE_C = try Cache.lookup_thm "LE_C" with _ ->  prove
 ((parse_term "!s t. s <=_c t <=> ?g. !x. x IN s ==> ?y. y IN t /\\ (g y = x)"),
  vREWRITE_TAC[le_c; vINJECTIVE_ON_LEFT_INVERSE; vSURJECTIVE_ON_RIGHT_INVERSE;
              vRIGHT_IMP_EXISTS_THM; vSKOLEM_THM; vRIGHT_AND_EXISTS_THM] ---->
  vMESON_TAC[]);;

let vGE_C = try Cache.lookup_thm "GE_C" with _ ->  prove
 ((parse_term "!s t. s >=_c t <=> ?f. !y. y IN t ==> ?x. x IN s /\\ (y = f x)"),
  vREWRITE_TAC[ge_c; vLE_C] ----> vMESON_TAC[]);;

let vCOUNTABLE = new_definition
  (parse_term "COUNTABLE t <=> (:num) >=_c t");;

(* ------------------------------------------------------------------------- *)
(* Supremum and infimum.                                                     *)
(* ------------------------------------------------------------------------- *)

let sup = new_definition
  (parse_term "sup s = @a:real. (!x. x IN s ==> x <= a) /\\\n                    !b. (!x. x IN s ==> x <= b) ==> a <= b");;

let vSUP_EQ = try Cache.lookup_thm "SUP_EQ" with _ ->  prove
 ((parse_term "!s t. (!b. (!x. x IN s ==> x <= b) <=> (!x. x IN t ==> x <= b))\n         ==> sup s = sup t"),
  vSIMP_TAC[sup]);;

let vSUP = try Cache.lookup_thm "SUP" with _ ->  prove
 ((parse_term "!s. ~(s = {}) /\\ (?b. !x. x IN s ==> x <= b)\n       ==> (!x. x IN s ==> x <= sup s) /\\\n           !b. (!x. x IN s ==> x <= b) ==> sup s <= b"),
  vREWRITE_TAC[sup] ----> vCONV_TAC(vONCE_DEPTH_CONV vSELECT_CONV) ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_COMPLETE ---->
  vASM_MESON_TAC[vMEMBER_NOT_EMPTY]);;

let vSUP_FINITE_LEMMA = try Cache.lookup_thm "SUP_FINITE_LEMMA" with _ ->  prove
 ((parse_term "!s. FINITE s /\\ ~(s = {}) ==> ?b:real. b IN s /\\ !x. x IN s ==> x <= b"),
  vREWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vNOT_INSERT_EMPTY; vIN_INSERT] ---->
  vREWRITE_TAC[vGSYM vMEMBER_NOT_EMPTY] ---->
  vMESON_TAC[vREAL_LE_TOTAL; vREAL_LE_TRANS]);;

let vSUP_FINITE = try Cache.lookup_thm "SUP_FINITE" with _ ->  prove
 ((parse_term "!s. FINITE s /\\ ~(s = {}) ==> (sup s) IN s /\\ !x. x IN s ==> x <= sup s"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vSUP_FINITE_LEMMA) ---->
  vASM_MESON_TAC[vREAL_LE_ANTISYM; vREAL_LE_TOTAL; vSUP]);;

let vREAL_LE_SUP_FINITE = try Cache.lookup_thm "REAL_LE_SUP_FINITE" with _ ->  prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (a <= sup s <=> ?x. x IN s /\\ a <= x)"),
  vMESON_TAC[vSUP_FINITE; vREAL_LE_TRANS]);;

let vREAL_SUP_LE_FINITE = try Cache.lookup_thm "REAL_SUP_LE_FINITE" with _ ->  prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (sup s <= a <=> !x. x IN s ==> x <= a)"),
  vMESON_TAC[vSUP_FINITE; vREAL_LE_TRANS]);;

let vREAL_LT_SUP_FINITE = try Cache.lookup_thm "REAL_LT_SUP_FINITE" with _ ->  prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (a < sup s <=> ?x. x IN s /\\ a < x)"),
  vMESON_TAC[vSUP_FINITE; vREAL_LTE_TRANS]);;

let vREAL_SUP_LT_FINITE = try Cache.lookup_thm "REAL_SUP_LT_FINITE" with _ ->  prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (sup s < a <=> !x. x IN s ==> x < a)"),
  vMESON_TAC[vSUP_FINITE; vREAL_LET_TRANS]);;

let vREAL_SUP_UNIQUE = try Cache.lookup_thm "REAL_SUP_UNIQUE" with _ ->  prove
 ((parse_term "!s b. (!x. x IN s ==> x <= b) /\\\n         (!b'. b' < b ==> ?x. x IN s /\\ b' < x)\n         ==> sup s = b"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[sup] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vASM_MESON_TAC[vREAL_NOT_LE; vREAL_LE_ANTISYM]);;

let vREAL_SUP_LE = try Cache.lookup_thm "REAL_SUP_LE" with _ ->  prove
 ((parse_term "!b. ~(s = {}) /\\ (!x. x IN s ==> x <= b) ==> sup s <= b"),
  vMESON_TAC[vSUP]);;

let vREAL_SUP_LE_SUBSET = try Cache.lookup_thm "REAL_SUP_LE_SUBSET" with _ ->  prove
 ((parse_term "!s t. ~(s = {}) /\\ s SUBSET t /\\ (?b. !x. x IN t ==> x <= b)\n         ==> sup s <= sup t"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_SUP_LE ---->
  vMP_TAC(vSPEC (parse_term "t:real->bool") vSUP) ----> vASM vSET_TAC[]);;

let vREAL_SUP_BOUNDS = try Cache.lookup_thm "REAL_SUP_BOUNDS" with _ ->  prove
 ((parse_term "!s a b. ~(s = {}) /\\ (!x. x IN s ==> a <= x /\\ x <= b)\n           ==> a <= sup s /\\ sup s <= b"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPEC (parse_term "s:real->bool") vSUP) ----> vANTS_TAC ++-->
   [vASM_MESON_TAC[]; vALL_TAC] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vGSYM vMEMBER_NOT_EMPTY]) ---->
  vASM_MESON_TAC[vREAL_LE_TRANS]);;

let vREAL_ABS_SUP_LE = try Cache.lookup_thm "REAL_ABS_SUP_LE" with _ ->  prove
 ((parse_term "!s a. ~(s = {}) /\\ (!x. x IN s ==> abs(x) <= a) ==> abs(sup s) <= a"),
  vREWRITE_TAC[vGSYM vREAL_BOUNDS_LE; vREAL_SUP_BOUNDS]);;

let vREAL_SUP_ASCLOSE = try Cache.lookup_thm "REAL_SUP_ASCLOSE" with _ ->  prove
 ((parse_term "!s l e. ~(s = {}) /\\ (!x. x IN s ==> abs(x - l) <= e)\n           ==> abs(sup s - l) <= e"),
  vSIMP_TAC[vREAL_ARITH (parse_term "abs(x - l):real <= e <=> l - e <= x /\\ x <= l + e")] ---->
  vREWRITE_TAC[vREAL_SUP_BOUNDS]);;

let vSUP_UNIQUE_FINITE = try Cache.lookup_thm "SUP_UNIQUE_FINITE" with _ ->  prove
 ((parse_term "!s. FINITE s /\\ ~(s = {})\n       ==> (sup s = a <=> a IN s /\\ !y. y IN s ==> y <= a)"),
   vASM_SIMP_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_LE_SUP_FINITE; vREAL_SUP_LE_FINITE;
               vNOT_INSERT_EMPTY; vFINITE_INSERT; vFINITE_EMPTY] ---->
   vMESON_TAC[vREAL_LE_REFL; vREAL_LE_TRANS; vREAL_LE_ANTISYM]);;

let vSUP_INSERT_FINITE = try Cache.lookup_thm "SUP_INSERT_FINITE" with _ ->  prove
 ((parse_term "!x s. FINITE s ==> sup(x INSERT s) = if s = {} then x else max x (sup s)"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vSUP_UNIQUE_FINITE;  vFINITE_INSERT; vFINITE_EMPTY;
               vNOT_INSERT_EMPTY; vFORALL_IN_INSERT; vNOT_IN_EMPTY] ---->
  vREWRITE_TAC[vIN_SING; vREAL_LE_REFL] ---->
  vREWRITE_TAC[real_max] ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vSUP_FINITE; vIN_INSERT; vREAL_LE_REFL] ---->
  vASM_MESON_TAC[vSUP_FINITE; vREAL_LE_TOTAL; vREAL_LE_TRANS]);;

let vSUP_SING = try Cache.lookup_thm "SUP_SING" with _ ->  prove
 ((parse_term "!a. sup {a} = a"),
  vSIMP_TAC[vSUP_INSERT_FINITE; vFINITE_EMPTY]);;

let vSUP_INSERT_INSERT = try Cache.lookup_thm "SUP_INSERT_INSERT" with _ ->  prove
 ((parse_term "!a b s. sup (b INSERT a INSERT s) = sup (max a b INSERT s)"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vSUP_EQ ---->
  vX_GEN_TAC (parse_term "c:real") ----> vREWRITE_TAC[vFORALL_IN_INSERT] ---->
  vASM_CASES_TAC (parse_term "!x:real. x IN s ==> x <= c") ----> vASM_REWRITE_TAC[] ---->
  vREAL_ARITH_TAC);;

let vREAL_LE_SUP = try Cache.lookup_thm "REAL_LE_SUP" with _ ->  prove
 ((parse_term "!s a b y. y IN s /\\ a <= y /\\ (!x. x IN s ==> x <= b) ==> a <= sup s"),
  vMESON_TAC[vSUP; vMEMBER_NOT_EMPTY; vREAL_LE_TRANS]);;

let vREAL_SUP_LE_EQ = try Cache.lookup_thm "REAL_SUP_LE_EQ" with _ ->  prove
 ((parse_term "!s y. ~(s = {}) /\\ (?b. !x. x IN s ==> x <= b)\n         ==> (sup s <= y <=> !x. x IN s ==> x <= y)"),
  vMESON_TAC[vSUP; vREAL_LE_TRANS]);;

let vSUP_UNIQUE = try Cache.lookup_thm "SUP_UNIQUE" with _ ->  prove
 ((parse_term "!s b. (!c. (!x. x IN s ==> x <= c) <=> b <= c) ==> sup s = b"),
  vREPEAT vSTRIP_TAC ----> vGEN_REWRITE_TAC vRAND_CONV [vGSYM vSUP_SING] ---->
  vMATCH_MP_TAC vSUP_EQ ----> vASM vSET_TAC[]);;

let vSUP_UNION = try Cache.lookup_thm "SUP_UNION" with _ ->  prove
 ((parse_term "!s t. ~(s = {}) /\\ ~(t = {}) /\\\n         (?b. !x. x IN s ==> x <= b) /\\ (?c. !x. x IN t ==> x <= c)\n         ==> sup(s UNION t) = max (sup s) (sup t)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUP_UNIQUE ---->
  vREWRITE_TAC[vFORALL_IN_UNION; vREAL_MAX_LE] ---->
  vASM_MESON_TAC[vSUP; vREAL_LE_TRANS]);;

let vELEMENT_LE_SUP = try Cache.lookup_thm "ELEMENT_LE_SUP" with _ ->  prove
 ((parse_term "!s a. (?b. !x. x IN s ==> x <= b) /\\ a IN s ==> a <= sup s"),
  vMESON_TAC[vREAL_LE_SUP; vREAL_LE_REFL]);;

let vSUP_APPROACH = try Cache.lookup_thm "SUP_APPROACH" with _ ->  prove
 ((parse_term "!s c. ~(s = {}) /\\ (?b. !x. x IN s ==> x <= b) /\\ c < sup s\n         ==> ?x. x IN s /\\ c < x"),
  vINTRO_TAC "!s c; npty bound lt" ---->
  vREFUTE_THEN (vLABEL_TAC "hp" -|
    vREWRITE_RULE[vNOT_EXISTS_THM; vDE_MORGAN_THM; vREAL_NOT_LT]) ---->
  vREMOVE_THEN "lt" vMP_TAC ----> vREWRITE_TAC[vREAL_NOT_LT] ---->
  vHYP (vMP_TAC -| vMATCH_MP vSUP -| end_itlist vCONJ) "npty bound" [] ---->
  vINTRO_TAC "_ sup" ----> vREMOVE_THEN "sup" vMATCH_MP_TAC ---->
  vASM_MESON_TAC[]);;

let vREAL_MAX_SUP = try Cache.lookup_thm "REAL_MAX_SUP" with _ ->  prove
 ((parse_term "!x y. max x y = sup {x,y}"),
  vSIMP_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_SUP_LE_FINITE; vREAL_LE_SUP_FINITE;
           vFINITE_RULES; vNOT_INSERT_EMPTY; vREAL_MAX_LE; vREAL_LE_MAX] ---->
  vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ----> vMESON_TAC[vREAL_LE_TOTAL]);;

let inf = new_definition
  (parse_term "inf s = @a:real. (!x. x IN s ==> a <= x) /\\\n                    !b. (!x. x IN s ==> b <= x) ==> b <= a");;

let vINF_EQ = try Cache.lookup_thm "INF_EQ" with _ ->  prove
 ((parse_term "!s t. (!a. (!x. x IN s ==> a <= x) <=> (!x. x IN t ==> a <= x))\n         ==> inf s = inf t"),
  vSIMP_TAC[inf]);;

let vINF = try Cache.lookup_thm "INF" with _ ->  prove
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

let vINF_FINITE_LEMMA = try Cache.lookup_thm "INF_FINITE_LEMMA" with _ ->  prove
 ((parse_term "!s. FINITE s /\\ ~(s = {}) ==> ?b:real. b IN s /\\ !x. x IN s ==> b <= x"),
  vREWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vNOT_INSERT_EMPTY; vIN_INSERT] ---->
  vREWRITE_TAC[vGSYM vMEMBER_NOT_EMPTY] ---->
  vMESON_TAC[vREAL_LE_TOTAL; vREAL_LE_TRANS]);;

let vINF_FINITE = try Cache.lookup_thm "INF_FINITE" with _ ->  prove
 ((parse_term "!s. FINITE s /\\ ~(s = {}) ==> (inf s) IN s /\\ !x. x IN s ==> inf s <= x"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vINF_FINITE_LEMMA) ---->
  vASM_MESON_TAC[vREAL_LE_ANTISYM; vREAL_LE_TOTAL; vINF]);;

let vREAL_LE_INF_FINITE = try Cache.lookup_thm "REAL_LE_INF_FINITE" with _ ->  prove
((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (a <= inf s <=> !x. x IN s ==> a <= x)"),
  vMESON_TAC[vINF_FINITE; vREAL_LE_TRANS]);;

let vREAL_INF_LE_FINITE = try Cache.lookup_thm "REAL_INF_LE_FINITE" with _ ->  prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (inf s <= a <=> ?x. x IN s /\\ x <= a)"),
  vMESON_TAC[vINF_FINITE; vREAL_LE_TRANS]);;

let vREAL_LT_INF_FINITE = try Cache.lookup_thm "REAL_LT_INF_FINITE" with _ ->  prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (a < inf s <=> !x. x IN s ==> a < x)"),
  vMESON_TAC[vINF_FINITE; vREAL_LTE_TRANS]);;

let vREAL_INF_LT_FINITE = try Cache.lookup_thm "REAL_INF_LT_FINITE" with _ ->  prove
 ((parse_term "!s a. FINITE s /\\ ~(s = {}) ==> (inf s < a <=> ?x. x IN s /\\ x < a)"),
  vMESON_TAC[vINF_FINITE; vREAL_LET_TRANS]);;

let vREAL_INF_UNIQUE = try Cache.lookup_thm "REAL_INF_UNIQUE" with _ ->  prove
 ((parse_term "!s b. (!x. x IN s ==> b <= x) /\\\n         (!b'. b < b' ==> ?x. x IN s /\\ x < b')\n         ==> inf s = b"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[inf] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vASM_MESON_TAC[vREAL_NOT_LE; vREAL_LE_ANTISYM]);;

let vREAL_LE_INF = try Cache.lookup_thm "REAL_LE_INF" with _ ->  prove
 ((parse_term "!b. ~(s = {}) /\\ (!x. x IN s ==> b <= x) ==> b <= inf s"),
  vMESON_TAC[vINF]);;

let vREAL_LE_INF_SUBSET = try Cache.lookup_thm "REAL_LE_INF_SUBSET" with _ ->  prove
 ((parse_term "!s t. ~(t = {}) /\\ t SUBSET s /\\ (?b. !x. x IN s ==> b <= x)\n         ==> inf s <= inf t"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_INF ---->
  vMP_TAC(vSPEC (parse_term "s:real->bool") vINF) ----> vASM vSET_TAC[]);;

let vREAL_INF_BOUNDS = try Cache.lookup_thm "REAL_INF_BOUNDS" with _ ->  prove
 ((parse_term "!s a b. ~(s = {}) /\\ (!x. x IN s ==> a <= x /\\ x <= b)\n           ==> a <= inf s /\\ inf s <= b"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPEC (parse_term "s:real->bool") vINF) ----> vANTS_TAC ++-->
   [vASM_MESON_TAC[]; vALL_TAC] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vGSYM vMEMBER_NOT_EMPTY]) ---->
  vASM_MESON_TAC[vREAL_LE_TRANS]);;

let vREAL_ABS_INF_LE = try Cache.lookup_thm "REAL_ABS_INF_LE" with _ ->  prove
 ((parse_term "!s a. ~(s = {}) /\\ (!x. x IN s ==> abs(x) <= a) ==> abs(inf s) <= a"),
  vREWRITE_TAC[vGSYM vREAL_BOUNDS_LE; vREAL_INF_BOUNDS]);;

let vREAL_INF_ASCLOSE = try Cache.lookup_thm "REAL_INF_ASCLOSE" with _ ->  prove
 ((parse_term "!s l e. ~(s = {}) /\\ (!x. x IN s ==> abs(x - l) <= e)\n           ==> abs(inf s - l) <= e"),
  vSIMP_TAC[vREAL_ARITH (parse_term "abs(x - l):real <= e <=> l - e <= x /\\ x <= l + e")] ---->
  vREWRITE_TAC[vREAL_INF_BOUNDS]);;

let vINF_UNIQUE_FINITE = try Cache.lookup_thm "INF_UNIQUE_FINITE" with _ ->  prove
 ((parse_term "!s. FINITE s /\\ ~(s = {})\n       ==> (inf s = a <=> a IN s /\\ !y. y IN s ==> a <= y)"),
   vASM_SIMP_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_LE_INF_FINITE; vREAL_INF_LE_FINITE;
               vNOT_INSERT_EMPTY; vFINITE_INSERT; vFINITE_EMPTY] ---->
   vMESON_TAC[vREAL_LE_REFL; vREAL_LE_TRANS; vREAL_LE_ANTISYM]);;

let vINF_INSERT_FINITE = try Cache.lookup_thm "INF_INSERT_FINITE" with _ ->  prove
 ((parse_term "!x s. FINITE s ==> inf(x INSERT s) = if s = {} then x else min x (inf s)"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vINF_UNIQUE_FINITE;  vFINITE_INSERT; vFINITE_EMPTY;
               vNOT_INSERT_EMPTY; vFORALL_IN_INSERT; vNOT_IN_EMPTY] ---->
  vREWRITE_TAC[vIN_SING; vREAL_LE_REFL] ---->
  vREWRITE_TAC[real_min] ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vINF_FINITE; vIN_INSERT; vREAL_LE_REFL] ---->
  vASM_MESON_TAC[vINF_FINITE; vREAL_LE_TOTAL; vREAL_LE_TRANS]);;

let vINF_SING = try Cache.lookup_thm "INF_SING" with _ ->  prove
 ((parse_term "!a. inf {a} = a"),
  vSIMP_TAC[vINF_INSERT_FINITE; vFINITE_EMPTY]);;

let vINF_INSERT_INSERT = try Cache.lookup_thm "INF_INSERT_INSERT" with _ ->  prove
 ((parse_term "!a b s. inf (b INSERT a INSERT s) = inf (min a b INSERT s)"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vINF_EQ ---->
  vX_GEN_TAC (parse_term "c:real") ----> vREWRITE_TAC[vFORALL_IN_INSERT] ---->
  vASM_CASES_TAC (parse_term "!x:real. x IN s ==> c <= x") ----> vASM_REWRITE_TAC[] ---->
  vREAL_ARITH_TAC);;

let vREAL_SUP_EQ_INF = try Cache.lookup_thm "REAL_SUP_EQ_INF" with _ ->  prove
 ((parse_term "!s. ~(s = {}) /\\ (?B. !x. x IN s ==> abs(x) <= B)\n       ==> (sup s = inf s <=> ?a. s = {a})"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vEXISTS_TAC (parse_term "sup s") ----> vMATCH_MP_TAC
     (vSET_RULE (parse_term "~(s = {}) /\\ (!x. x IN s ==> x = a) ==> s = {a}")) ---->
    vASM_REWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
    vASM_MESON_TAC[vSUP; vREAL_ABS_BOUNDS; vINF];
    vSTRIP_TAC ---->
    vASM_SIMP_TAC[vSUP_INSERT_FINITE; vINF_INSERT_FINITE; vFINITE_EMPTY]]);;

let vREAL_INF_LE = try Cache.lookup_thm "REAL_INF_LE" with _ ->  prove
 ((parse_term "!s a b y. y IN s /\\ y <= b /\\ (!x. x IN s ==> a <= x) ==> inf s <= b"),
  vMESON_TAC[vINF; vMEMBER_NOT_EMPTY; vREAL_LE_TRANS]);;

let vREAL_LE_INF_EQ = try Cache.lookup_thm "REAL_LE_INF_EQ" with _ ->  prove
 ((parse_term "!s y. ~(s = {}) /\\ (?b. !x. x IN s ==> b <= x)\n         ==> (y <= inf s <=> !x. x IN s ==> y <= x)"),
  vMESON_TAC[vINF; vREAL_LE_TRANS]);;

let vINF_UNIQUE = try Cache.lookup_thm "INF_UNIQUE" with _ ->  prove
 ((parse_term "!s b. (!c. (!x. x IN s ==> c <= x) <=> c <= b) ==> inf s = b"),
  vREPEAT vSTRIP_TAC ----> vGEN_REWRITE_TAC vRAND_CONV [vGSYM vINF_SING] ---->
  vMATCH_MP_TAC vINF_EQ ----> vASM vSET_TAC[]);;

let vINF_UNION = try Cache.lookup_thm "INF_UNION" with _ ->  prove
 ((parse_term "!s t. ~(s = {}) /\\ ~(t = {}) /\\\n         (?b. !x. x IN s ==> b <= x) /\\ (?c. !x. x IN t ==> c <= x)\n         ==> inf(s UNION t) = min (inf s) (inf t)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vINF_UNIQUE ---->
  vREWRITE_TAC[vFORALL_IN_UNION; vREAL_LE_MIN] ---->
  vASM_MESON_TAC[vINF; vREAL_LE_TRANS]);;

let vINF_LE_ELEMENT = try Cache.lookup_thm "INF_LE_ELEMENT" with _ ->  prove
 ((parse_term "!s a. (?b. !x. x IN s ==> b <= x) /\\ a IN s ==> inf s <= a"),
  vMESON_TAC[vREAL_INF_LE; vREAL_LE_REFL]);;

let vINF_APPROACH = try Cache.lookup_thm "INF_APPROACH" with _ ->  prove
 ((parse_term "!s c. ~(s = {}) /\\ (?b. !x. x IN s ==> b <= x) /\\ inf s < c\n         ==> ?x. x IN s /\\ x < c"),
  vINTRO_TAC "!s c; npty bound lt" ---->
  vREFUTE_THEN (vLABEL_TAC "hp" -|
    vREWRITE_RULE[vNOT_EXISTS_THM; vDE_MORGAN_THM; vREAL_NOT_LT]) ---->
  vREMOVE_THEN "lt" vMP_TAC ----> vREWRITE_TAC[vREAL_NOT_LT] ---->
  vHYP (vMP_TAC -| vMATCH_MP vINF -| end_itlist vCONJ) "npty bound" [] ---->
  vINTRO_TAC "_ inf" ----> vREMOVE_THEN "inf" vMATCH_MP_TAC ---->
  vASM_MESON_TAC[]);;

let vREAL_MIN_INF = try Cache.lookup_thm "REAL_MIN_INF" with _ ->  prove
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

let vHAS_INF_LBOUND = try Cache.lookup_thm "HAS_INF_LBOUND" with _ ->  prove
 ((parse_term "!s b x. s has_inf b /\\ x IN s ==> b <= x"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[has_inf] ----> vMESON_TAC[vREAL_LE_REFL]);;

let vHAS_SUP_UBOUND = try Cache.lookup_thm "HAS_SUP_UBOUND" with _ ->  prove
 ((parse_term "!s b x. s has_sup b /\\ x IN s ==> x <= b"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[has_sup] ----> vMESON_TAC[vREAL_LE_REFL]);;

let vHAS_INF_INF = try Cache.lookup_thm "HAS_INF_INF" with _ ->  prove
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

let vHAS_SUP_SUP = try Cache.lookup_thm "HAS_SUP_SUP" with _ ->  prove
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

let vINF_EXISTS = try Cache.lookup_thm "INF_EXISTS" with _ ->  prove
 ((parse_term "!s. (?l. s has_inf l) <=> ~(s = {}) /\\ (?b. !x. x IN s ==> b <= x)"),
  vMESON_TAC[vHAS_INF_INF]);;

let vSUP_EXISTS = try Cache.lookup_thm "SUP_EXISTS" with _ ->  prove
 ((parse_term "!s. (?l. s has_sup l) <=> ~(s = {}) /\\ (?b. !x. x IN s ==> x <= b)"),
  vMESON_TAC[vHAS_SUP_SUP]);;

let vHAS_INF_APPROACH = try Cache.lookup_thm "HAS_INF_APPROACH" with _ ->  prove
 ((parse_term "!s l c. s has_inf l /\\ l < c ==> ?x. x IN s /\\ x < c"),
  vREWRITE_TAC[vHAS_INF_INF] ----> vMESON_TAC[vINF_APPROACH]);;

let vHAS_SUP_APPROACH = try Cache.lookup_thm "HAS_SUP_APPROACH" with _ ->  prove
 ((parse_term "!s l c. s has_sup l /\\ c < l ==> ?x. x IN s /\\ c < x"),
  vREWRITE_TAC[vHAS_SUP_SUP] ----> vMESON_TAC[vSUP_APPROACH]);;

let vHAS_INF = try Cache.lookup_thm "HAS_INF" with _ ->  prove
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

let vHAS_SUP = try Cache.lookup_thm "HAS_SUP" with _ ->  prove
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

let vHAS_INF_LE = try Cache.lookup_thm "HAS_INF_LE" with _ ->  prove
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

let vHAS_SUP_LE = try Cache.lookup_thm "HAS_SUP_LE" with _ ->  prove
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
