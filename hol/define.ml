(* ========================================================================= *)
(* Automated support for general recursive definitions.                      *)
(*                                                                           *)
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
open Simp
open Theorems
open Class
open Meson
open Pair
open Nums
open Recursion
open Arith
open Wf
open Calc_num
open Ind_types
open Lists
open Int
open Iterate

(* ------------------------------------------------------------------------- *)
(* Constant supporting casewise definitions.                                 *)
(* ------------------------------------------------------------------------- *)

let vCASEWISE_DEF = new_recursive_definition list_RECURSION
 (parse_term "(CASEWISE [] f x = @y. T) /\\\n  (CASEWISE (CONS h t) f x =\n        if ?y. FST h y = x then SND h f (@y. FST h y = x)\n        else CASEWISE t f x)");;

let vCASEWISE = prove
 ((parse_term "(CASEWISE [] f x = @y. T) /\\\n   (CASEWISE (CONS (s,t) clauses) f x =\n        if ?y. s y = x then t f (@y. s y = x) else CASEWISE clauses f x)"),
  vREWRITE_TAC[vCASEWISE_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Conditions for all the clauses in a casewise definition to hold.          *)
(* ------------------------------------------------------------------------- *)

let vCASEWISE_CASES = prove
 ((parse_term "!clauses c x.\n    (?s t a. MEM (s,t) clauses /\\ (s a = x) /\\\n             (CASEWISE clauses c x = t c a)) \\/\n    ~(?s t a. MEM (s,t) clauses /\\ (s a = x)) /\\\n    (CASEWISE clauses c x = @y. T)"),
  vMATCH_MP_TAC list_INDUCT ---->
  vREWRITE_TAC[vMEM; vCASEWISE; vFORALL_PAIR_THM; vPAIR_EQ] ---->
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ----> vASM_MESON_TAC[]);;

let vCASEWISE_WORKS = prove
 ((parse_term "!clauses c:C.\n     (!s t s' t' x y. MEM (s,t) clauses /\\ MEM (s',t') clauses /\\ (s x = s' y)\n                      ==> (t c x = t' c y))\n     ==> ALL (\\(s:P->A,t). !x. CASEWISE clauses c (s x) :B = t c x) clauses"),
  vREWRITE_TAC[vGSYM vALL_MEM; vFORALL_PAIR_THM] ---->
  vMESON_TAC[vCASEWISE_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Various notions of admissibility, with tail recursion and preconditions.  *)
(* ------------------------------------------------------------------------- *)

let admissible = new_definition
 (parse_term "admissible(<<) p s t <=>\n        !f g a. p f a /\\ p g a /\\ (!z. z << s(a) ==> (f z = g z))\n                ==> (t f a = t g a)");;

let tailadmissible = new_definition
 (parse_term "tailadmissible(<<) p s t <=>\n        ?P G H. (!f a y. P f a /\\ y << G f a ==> y << s a) /\\\n                (!f g a. (!z. z << s(a) ==> (f z = g z))\n                         ==> (P f a = P g a) /\\\n                             (G f a = G g a) /\\ (H f a = H g a)) /\\\n                (!f a:P. p f a ==> (t (f:A->B) a =\n                                    if P f a then f(G f a) else H f a))");;

let superadmissible = new_definition
 (parse_term "superadmissible(<<) p s t <=>\n        admissible(<<) (\\f a. T) s p ==> tailadmissible(<<) p s t");;

(* ------------------------------------------------------------------------- *)
(* A lemma.                                                                  *)
(* ------------------------------------------------------------------------- *)

let vMATCH_SEQPATTERN = prove
 ((parse_term "_MATCH x (_SEQPATTERN r s) =\n   if ?y. r x y then _MATCH x r else _MATCH x s"),
  vREWRITE_TAC[_MATCH; _SEQPATTERN] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Admissibility combinators.                                                *)
(* ------------------------------------------------------------------------- *)

let vADMISSIBLE_CONST = prove
 ((parse_term "!p s c. admissible(<<) p s (\\f. c)"),
  vREWRITE_TAC[admissible]);;

let vADMISSIBLE_BASE = prove
 ((parse_term "!(<<) p s t.\n        (!f a. p f a ==> t a << s a)\n        ==> admissible((<<):A->A->bool) p s (\\f:A->B x:P. f(t x))"),
  vREWRITE_TAC[admissible] ----> vMESON_TAC[]);;

let vADMISSIBLE_COMB = prove
 ((parse_term "!(<<) p s:P->A g:(A->B)->P->C->D y:(A->B)->P->C.\n        admissible(<<) p s g /\\ admissible(<<) p s y\n        ==> admissible(<<) p s (\\f x. (g f x) (y f x))"),
  vSIMP_TAC[admissible] ----> vMESON_TAC[]);;

let vADMISSIBLE_RAND = prove
 ((parse_term "!(<<) p s:P->A g:P->C->D y:(A->B)->P->C.\n        admissible(<<) p s y\n        ==> admissible(<<) p s (\\f x. (g x) (y f x))"),
  vSIMP_TAC[admissible] ----> vMESON_TAC[]);;

let vADMISSIBLE_LAMBDA = prove
 ((parse_term "!(<<) p s:P->A t:(A->B)->C->P->bool.\n     admissible(<<) (\\f (u,x). p f x) (\\(u,x). s x) (\\f (u,x). t f u x)\n     ==> admissible(<<) p s (\\f x. \\u. t f u x)"),
  vREWRITE_TAC[admissible; vFUN_EQ_THM; vFORALL_PAIR_THM] ----> vMESON_TAC[]);;

let vADMISSIBLE_NEST = prove
 ((parse_term "!(<<) p s t.\n        admissible(<<) p s t /\\\n        (!f a. p f a ==> t f a << s a)\n        ==> admissible((<<):A->A->bool) p s (\\f:A->B x:P. f(t f x))"),
  vREWRITE_TAC[admissible] ----> vMESON_TAC[]);;

let vADMISSIBLE_COND = prove
 ((parse_term "!(<<) p P s h k.\n        admissible(<<) p s P /\\\n        admissible(<<) (\\f x. p f x /\\ P f x) s h /\\\n        admissible(<<) (\\f x. p f x /\\ ~P f x) s k\n        ==> admissible(<<) p s (\\f x:P. if P f x then h f x else k f x)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[admissible; vAND_FORALL_THM] ---->
  vREPEAT(vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC) ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ---->
  vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[]);;

let vADMISSIBLE_MATCH = prove
 ((parse_term "!(<<) p s e c.\n        admissible(<<) p s e /\\ admissible(<<) p s (\\f x. c f x (e f x))\n        ==> admissible(<<) p s (\\f x:P. _MATCH (e f x) (c f x))"),
  vREWRITE_TAC[admissible; _MATCH] ---->
  vREPEAT vSTRIP_TAC ----> vREPEAT vCOND_CASES_TAC ----> vASM_MESON_TAC[]);;

let vADMISSIBLE_SEQPATTERN = prove
 ((parse_term "!(<<) p s c1 c2 e.\n        admissible(<<) p s (\\f x:P. ?y. c1 f x (e f x) y) /\\\n        admissible(<<) (\\f x. p f x /\\ ?y. c1 f x (e f x) y) s\n                       (\\f x. c1 f x (e f x)) /\\\n        admissible(<<) (\\f x. p f x /\\ ~(?y. c1 f x (e f x) y)) s\n                       (\\f x. c2 f x (e f x))\n        ==> admissible(<<) p s (\\f x. _SEQPATTERN (c1 f x) (c2 f x) (e f x))"),
  vREWRITE_TAC[_SEQPATTERN; admissible] ----> vMESON_TAC[]);;

let vADMISSIBLE_UNGUARDED_PATTERN = prove
 ((parse_term "!(<<) p s pat e t y.\n      admissible (<<) p s pat /\\\n      admissible (<<) p s e /\\\n      admissible (<<) (\\f x. p f x /\\ pat f x = e f x) s t /\\\n      admissible (<<) (\\f x. p f x /\\ pat f x = e f x) s y\n        ==> admissible(<<) p s\n             (\\f x:P. _UNGUARDED_PATTERN (GEQ (pat f x) (e f x))\n                                         (GEQ (t f x) (y f x)))"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[admissible; vFORALL_PAIR_THM; _UNGUARDED_PATTERN] ---->
  vREWRITE_TAC[vGEQ_DEF] ----> vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC(vTAUT (parse_term "(a <=> a') /\\ (a /\\ a' ==> (b <=> b'))\n                     ==> (a /\\ b <=> a' /\\ b')")) ---->
  vASM_MESON_TAC[]);;

let vADMISSIBLE_GUARDED_PATTERN = prove
 ((parse_term "!(<<) p s pat q e t y.\n      admissible (<<) p s pat /\\\n      admissible (<<) p s e /\\\n      admissible (<<) (\\f x. p f x /\\ pat f x = e f x /\\ q f x) s t /\\\n      admissible (<<) (\\f x. p f x /\\ pat f x = e f x) s q /\\\n      admissible (<<) (\\f x. p f x /\\ pat f x = e f x /\\ q f x) s y\n        ==> admissible(<<) p s\n             (\\f x:P. _GUARDED_PATTERN (GEQ (pat f x) (e f x))\n                                       (q f x)\n                                       (GEQ (t f x) (y f x)))"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[admissible; vFORALL_PAIR_THM; _GUARDED_PATTERN] ---->
  vREWRITE_TAC[vGEQ_DEF] ----> vREPEAT vSTRIP_TAC ---->
  vREPEAT(vMATCH_MP_TAC(vTAUT (parse_term "(a <=> a') /\\ (a /\\ a' ==> (b <=> b'))\n                            ==> (a /\\ b <=> a' /\\ b')")) ---->
         vREPEAT vSTRIP_TAC) ---->
  vTRY(vMATCH_MP_TAC(vMESON[] (parse_term "x = x' /\\ y = y' ==> (x = y <=> x' = y')"))) ---->
  vASM_MESON_TAC[]);;

let vADMISSIBLE_NSUM = prove
 ((parse_term "!(<<) p:(B->C)->P->bool s:P->A h a b.\n        admissible(<<) (\\f (k,x). a(x) <= k /\\ k <= b(x) /\\ p f x)\n                       (\\(k,x). s x) (\\f (k,x). h f x k)\n   ==> admissible(<<) p s (\\f x. nsum(a(x)..b(x)) (h f x))"),
  vREWRITE_TAC[admissible; vFORALL_PAIR_THM] ----> vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC vNSUM_EQ_NUMSEG ----> vASM_MESON_TAC[]);;

let vADMISSIBLE_SUM = prove
 ((parse_term "!(<<) p:(B->C)->P->bool s:P->A h a b.\n        admissible(<<) (\\f (k,x). a(x) <= k /\\ k <= b(x) /\\ p f x)\n                       (\\(k,x). s x) (\\f (k,x). h f x k)\n   ==> admissible(<<) p s (\\f x. sum(a(x)..b(x)) (h f x))"),
  vREWRITE_TAC[admissible; vFORALL_PAIR_THM] ----> vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC vSUM_EQ_NUMSEG ----> vASM_MESON_TAC[]);;

let vADMISSIBLE_MAP = prove
 ((parse_term "!(<<) p s h l.\n        admissible(<<) p s l /\\\n        admissible (<<) (\\f (y,x). p f x /\\ MEM y (l f x))\n                        (\\(y,x). s x) (\\f (y,x). h f x y)\n   ==> admissible (<<) p s (\\f:A->B x:P. MAP (h f x) (l f x))"),
  vREWRITE_TAC[admissible; vFORALL_PAIR_THM] ----> vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC(vMESON[] (parse_term "x = y /\\ MAP f x = MAP g x ==> MAP f x = MAP g y")) ---->
  vCONJ_TAC ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
  vMATCH_MP_TAC vMAP_EQ ----> vREWRITE_TAC[vGSYM vALL_MEM] ---->
  vREPEAT vSTRIP_TAC ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
  vASM_REWRITE_TAC[vFORALL_PAIR_THM] ----> vASM_MESON_TAC[]);;

let vADMISSIBLE_MATCH_SEQPATTERN = prove
 ((parse_term "!(<<) p s c1 c2 e.\n        admissible(<<) p s (\\f x. ?y. c1 f x (e f x) y) /\\\n        admissible(<<) (\\f x. p f x /\\ ?y. c1 f x (e f x) y) s\n                       (\\f x. _MATCH (e f x) (c1 f x)) /\\\n        admissible(<<) (\\f x. p f x /\\ ~(?y. c1 f x (e f x) y)) s\n                       (\\f x. _MATCH (e f x) (c2 f x))\n        ==> admissible(<<) p s\n              (\\f x:P. _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)))"),
  vREWRITE_TAC[vMATCH_SEQPATTERN; vADMISSIBLE_COND]);;

(* ------------------------------------------------------------------------- *)
(* Superadmissible generalizations where applicable.                         *)
(*                                                                           *)
(* Note that we can't take the "higher type" route in the simple theorem     *)
(* ADMISSIBLE_MATCH because that isn't a context where tail recursion makes  *)
(* sense. Instead, we use specific theorems for the two _MATCH instances.    *)
(* Note that also, because of some delicacy over assessing welldefinedness   *)
(* of patterns, a special well-formedness hypothesis crops up here. (We need *)
(* to separate it from the function f or we lose the "tail" optimization.)   *)
(* ------------------------------------------------------------------------- *)

let vADMISSIBLE_IMP_SUPERADMISSIBLE = prove
 ((parse_term "!(<<) p s t:(A->B)->P->B.\n      admissible(<<) p s t ==> superadmissible(<<) p s t"),
  vREWRITE_TAC[admissible; superadmissible; tailadmissible] ---->
  vREPEAT vSTRIP_TAC ---->
  vMAP_EVERY vEXISTS_TAC
   [(parse_term "\\f:A->B x:P. F");
    (parse_term "\\f:A->B. (anything:P->A)");
    (parse_term "\\f:A->B a:P. if p f a then t f a :B else fixed")] ---->
  vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[]);;

let vSUPERADMISSIBLE_CONST = prove
 ((parse_term "!p s c. superadmissible(<<) p s (\\f. c)"),
  vREPEAT vGEN_TAC ---->
  vMATCH_MP_TAC vADMISSIBLE_IMP_SUPERADMISSIBLE ---->
  vREWRITE_TAC[vADMISSIBLE_CONST]);;

let vSUPERADMISSIBLE_TAIL = prove
 ((parse_term "!(<<) p s t:(A->B)->P->A.\n      admissible(<<) p s t /\\\n      (!f a. p f a ==> !y. y << t f a ==> y << s a)\n      ==> superadmissible(<<) p s (\\f x. f(t f x))"),
  vREWRITE_TAC[admissible; superadmissible; tailadmissible] ---->
  vREPEAT vSTRIP_TAC ----> vMAP_EVERY vEXISTS_TAC
   [(parse_term "\\f:A->B x:P. T");
    (parse_term "\\f:A->B a:P. if p f a then t f a :A else s a");
    (parse_term "\\f:A->B. anything:P->B")] ---->
  vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[]);;

let vSUPERADMISSIBLE_COND = prove
 ((parse_term "!(<<) p P s h k:(A->B)->P->B.\n        admissible(<<) p s P /\\\n        superadmissible(<<) (\\f x. p f x /\\ P f x) s h /\\\n        superadmissible(<<) (\\f x. p f x /\\ ~P f x) s k\n        ==> superadmissible(<<) p s (\\f x. if P f x then h f x else k f x)"),
  vREWRITE_TAC[superadmissible; admissible] ----> vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(fun th -> vDISCH_TAC ----> vCONJUNCTS_THEN vMP_TAC th) ---->
  vANTS_TAC ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
  vDISCH_THEN(fun th -> vANTS_TAC ++--> [vASM_MESON_TAC[]; vMP_TAC th]) ---->
  vREWRITE_TAC[tailadmissible] ---->
  vREWRITE_TAC[vLEFT_IMP_EXISTS_THM; vRIGHT_IMP_FORALL_THM] ---->
  vMAP_EVERY vX_GEN_TAC
   [(parse_term "P1:(A->B)->P->bool"); (parse_term "G1:(A->B)->P->A"); (parse_term "H1:(A->B)->P->B");
    (parse_term "P2:(A->B)->P->bool"); (parse_term "G2:(A->B)->P->A"); (parse_term "H2:(A->B)->P->B")] ---->
  vREWRITE_TAC[vTAUT (parse_term "(a1 /\\ b1 /\\ c1 ==> a2 /\\ b2 /\\ c2 ==> x) <=>\n                    (a1 /\\ a2) /\\ (b1 /\\ b2) /\\ (c1 /\\ c2) ==> x")] ---->
  vDISCH_THEN(fun th ->
   vMAP_EVERY vEXISTS_TAC
   [(parse_term "\\f:A->B a:P. if p f a then if P f a then P2 f a else P1 f a else F");
   (parse_term "\\f:A->B a:P. if p f a then if P f a then G2 f a else G1 f a else z:A");
   (parse_term "\\f:A->B a:P. if p f a then if P f a then H2 f a else H1 f a else w:B")] ---->
   vMP_TAC th) ---->
  vREWRITE_TAC[] ----> vREPEAT(vMATCH_MP_TAC vMONO_AND ----> vCONJ_TAC) ++-->
   [vASM_MESON_TAC[];
    vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ);
    vALL_TAC] ---->
  vREWRITE_TAC[vIMP_IMP; vAND_FORALL_THM] ---->
  vREPEAT(vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC) ---->
  vDISCH_THEN(fun th -> vDISCH_TAC ----> vMP_TAC th) ---->
  vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[]);;

let vSUPERADMISSIBLE_MATCH_SEQPATTERN = prove
 ((parse_term "!(<<) p s c1 c2 e.\n        admissible(<<) p s (\\f x. ?y. c1 f x (e f x) y) /\\\n        superadmissible(<<) (\\f x. p f x /\\ ?y. c1 f x (e f x) y) s\n                            (\\f x. _MATCH (e f x) (c1 f x)) /\\\n        superadmissible(<<) (\\f x. p f x /\\ ~(?y. c1 f x (e f x) y)) s\n                            (\\f x. _MATCH (e f x) (c2 f x))\n        ==> superadmissible(<<) p s\n              (\\f x:P. _MATCH (e f x) (_SEQPATTERN (c1 f x) (c2 f x)))"),
  vREWRITE_TAC[vMATCH_SEQPATTERN; vSUPERADMISSIBLE_COND]);;

let vSUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN = prove
 ((parse_term "!(<<) p s e:P->D pat:Q->D arg.\n      (!f a t u. p f a /\\ pat t = e a /\\ pat u = e a ==> arg a t = arg a u) /\\\n      (!f a t. p f a /\\ pat t = e a ==> !y. y << arg a t ==> y << s a)\n      ==> superadmissible(<<) p s\n           (\\f:A->B x. _MATCH (e x)\n                    (\\u v. ?t. _UNGUARDED_PATTERN (GEQ (pat t) u)\n                                                  (GEQ (f(arg x t)) v)))"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vREWRITE_TAC[superadmissible] ----> vDISCH_TAC ---->
  vREWRITE_TAC[_UNGUARDED_PATTERN; vGEQ_DEF; _MATCH] ---->
  vREWRITE_TAC[tailadmissible] ---->
  vSUBGOAL_THEN
   (parse_term "!f:A->B x:P.\n     p f x ==> ((?!v. ?t:Q. pat t:D = e x /\\ f(arg x t) = v) <=>\n                ?t. pat t = e x)")
   (fun th -> vSIMP_TAC[th]) ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
  vMAP_EVERY vEXISTS_TAC
   [(parse_term "\\(f:A->B) x:P. p f x /\\ ?t:Q. pat t:D = e x");
    (parse_term "\\f:A->B x:P. arg x (@t. (pat:Q->D) t = e x):A");
    (parse_term "\\(f:A->B) x:P. (@z:B. F)")] ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[admissible]) ----> vSIMP_TAC[] ---->
  vASM_MESON_TAC[]);;

let vSUPERADMISSIBLE_MATCH_GUARDED_PATTERN = prove
 ((parse_term "!(<<) p s e:P->D pat:Q->D q arg.\n      (!f a t u. p f a /\\ pat t = e a /\\ q a t /\\ pat u = e a /\\ q a u\n                 ==> arg a t = arg a u) /\\\n      (!f a t. p f a /\\ q a t /\\ pat t = e a ==> !y. y << arg a t ==> y << s a)\n      ==> superadmissible(<<) p s\n           (\\f:A->B x. _MATCH (e x)\n                    (\\u v. ?t. _GUARDED_PATTERN (GEQ (pat t) u)\n                                                (q x t)\n                                                (GEQ (f(arg x t)) v)))"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vREWRITE_TAC[superadmissible] ----> vDISCH_TAC ---->
  vREWRITE_TAC[_GUARDED_PATTERN; vGEQ_DEF; _MATCH] ---->
  vREWRITE_TAC[tailadmissible] ---->
  vSUBGOAL_THEN
   (parse_term "!f:A->B x:P.\n     p f x ==> ((?!v. ?t:Q. pat t:D = e x /\\ q x t /\\ f(arg x t) = v) <=>\n                ?t. pat t = e x /\\ q x t)")
   (fun th -> vSIMP_TAC[th]) ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
  vMAP_EVERY vEXISTS_TAC
   [(parse_term "\\(f:A->B) x:P. p f x /\\ ?t:Q. pat t:D = e x /\\ q x t");
    (parse_term "\\f:A->B x:P. arg x (@t. (pat:Q->D) t = e x /\\ q x t):A");
    (parse_term "\\(f:A->B) x:P. (@z:B. F)")] ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[admissible]) ----> vSIMP_TAC[] ---->
  vASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Combine general WF/tail recursion theorem with casewise definitions.      *)
(* ------------------------------------------------------------------------- *)

let vWF_REC_TAIL_GENERAL' = prove
 ((parse_term "!P G H H'.\n         WF (<<) /\\\n         (!f g x. (!z. z << x ==> (f z = g z))\n                  ==> (P f x <=> P g x) /\\\n                      (G f x = G g x) /\\ (H' f x = H' g x)) /\\\n         (!f x y. P f x /\\ y << G f x ==> y << x) /\\\n         (!f x. H f x = if P f x then f(G f x) else H' f x)\n         ==> ?f. !x. f x = H f x"),
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vWF_REC_TAIL_GENERAL ----> vASM_MESON_TAC[]);;

let vWF_REC_CASES = prove
 ((parse_term "!(<<) clauses.\n        WF((<<):A->A->bool) /\\\n        ALL (\\(s,t). ?P G H.\n                     (!f a y. P f a /\\ y << G f a ==> y << s a) /\\\n                     (!f g a. (!z. z << s(a) ==> (f z = g z))\n                              ==> (P f a = P g a) /\\\n                                  (G f a = G g a) /\\ (H f a = H g a)) /\\\n                     (!f a:P. t f a = if P f a then f(G f a) else H f a))\n            clauses\n        ==> ?f:A->B. !x. f x = CASEWISE clauses f x"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vWF_REC_TAIL_GENERAL' ---->
  vFIRST_X_ASSUM(vMP_TAC -| check(is_binary "ALL" -| concl)) ---->
  vSPEC_TAC((parse_term "clauses:((P->A)#((A->B)->P->B))list"),
           (parse_term "clauses:((P->A)#((A->B)->P->B))list")) ---->
  vASM_REWRITE_TAC[] ----> vPOP_ASSUM(vK vALL_TAC) ---->
  vMATCH_MP_TAC list_INDUCT ---->
  vREWRITE_TAC[vALL; vCASEWISE; vFORALL_PAIR_THM] ----> vCONJ_TAC ++-->
   [vMAP_EVERY vEXISTS_TAC
     [(parse_term "\\f:A->B x:A. F"); (parse_term "\\f:A->B. anything:A->A"); (parse_term "\\f:A->B x:A. @y:B. T")] ---->
    vREWRITE_TAC[];
    vALL_TAC] ---->
  vMAP_EVERY vX_GEN_TAC
    [(parse_term "s:P->A"); (parse_term "t:(A->B)->P->B"); (parse_term "clauses:((P->A)#((A->B)->P->B))list")] ---->
  vDISCH_THEN(fun th -> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
                       vMP_TAC th) ---->
  vASM_REWRITE_TAC[] ----> vPOP_ASSUM_LIST(vK vALL_TAC) ---->
  vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ----> vREWRITE_TAC[vRIGHT_IMP_FORALL_THM] ---->
  vMAP_EVERY vX_GEN_TAC
   [(parse_term "P1:(A->B)->A->bool"); (parse_term "G1:(A->B)->A->A"); (parse_term "H1:(A->B)->A->B");
    (parse_term "P2:(A->B)->P->bool"); (parse_term "G2:(A->B)->P->A"); (parse_term "H2:(A->B)->P->B")] ---->
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vEXISTS_TAC
   (parse_term "\\f:A->B x:A. if ?y:P. s y = x then P2 f (@y. s y = x) else P1 f x:bool") ---->
  vEXISTS_TAC (parse_term "\\f:A->B x:A.\n     if ?y:P. s y = x then G2 f (@y. s y = x) else G1 f x:A") ---->
  vEXISTS_TAC (parse_term "\\f:A->B x:A. if ?y:P. s y = x\n                           then H2 f (@y. s y = x) else H1 f x:B") ---->
  vASM_MESON_TAC[]);;

let vWF_REC_CASES' = prove
 ((parse_term "!(<<) clauses.\n        WF((<<):A->A->bool) /\\\n        ALL (\\(s,t). tailadmissible(<<) (\\f a. T) s t) clauses\n        ==> ?f:A->B. !x. f x = CASEWISE clauses f x"),
  vREWRITE_TAC[vWF_REC_CASES; tailadmissible]);;

let vRECURSION_CASEWISE = prove
 ((parse_term "!clauses.\n   (?(<<). WF(<<) /\\\n           ALL (\\(s:P->A,t). tailadmissible(<<) (\\f a. T) s t) clauses) /\\\n   (!s t s' t' f x y. MEM (s,t) clauses /\\ MEM (s',t') clauses\n                      ==> (s x = s' y) ==> (t f x = t' f y))\n   ==> ?f:A->B. ALL (\\(s,t). !x. f (s x) = t f x) clauses"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vIMP_IMP; vCONJ_ASSOC] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vDISCH_THEN(vCHOOSE_THEN (vMP_TAC -| vMATCH_MP vWF_REC_CASES')) ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vREPEAT vSTRIP_TAC ---->
  vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[vCASEWISE_WORKS]);;

let vRECURSION_CASEWISE_PAIRWISE = prove
 ((parse_term "!clauses.\n        (?(<<). WF (<<) /\\\n                ALL (\\(s,t). tailadmissible(<<) (\\f a. T) s t) clauses) /\\\n        ALL (\\(s,t). !f x y. (s x = s y) ==> (t f x = t f y)) clauses /\\\n        PAIRWISE (\\(s,t) (s',t'). !f x y. (s x = s' y) ==> (t f x = t' f y))\n                 clauses\n        ==> (?f. ALL (\\(s,t). !x. f (s x) = t f x) clauses)"),
  let lemma = prove
   ((parse_term "!P. (!x y. P x y ==> P y x)\n         ==> !l. (!x y. MEM x l /\\ MEM y l ==> P x y) <=>\n                 ALL (\\x. P x x) l /\\ PAIRWISE P l"),
    vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM; vGSYM vALL_MEM] ---->
    vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vLIST_INDUCT_TAC ---->
    vREWRITE_TAC[vPAIRWISE; vMEM; vGSYM vALL_MEM] ----> vASM_MESON_TAC[])
  and paired_lambda = prove
   ((parse_term "(\\x. P x) = (\\(a,b). P (a,b))"),
    vREWRITE_TAC[vFUN_EQ_THM; vFORALL_PAIR_THM]) in
  let pth = vREWRITE_RULE[vFORALL_PAIR_THM; paired_lambda] (vISPEC
    (parse_term "\\(s,t) (s',t'). !c x:A y:A. (s x = s' y) ==> (t c x = t' c y)") lemma) in
  let cth = prove(lhand(concl pth),vMESON_TAC[]) in
  vREWRITE_TAC[vGSYM(vMATCH_MP pth cth); vRIGHT_IMP_FORALL_THM] ---->
  vREWRITE_TAC[vRECURSION_CASEWISE]);;

let vSUPERADMISSIBLE_T = prove
 ((parse_term "superadmissible(<<) (\\f x. T) s t <=> tailadmissible(<<) (\\f x. T) s t"),
  vREWRITE_TAC[superadmissible; admissible]);;

let vRECURSION_SUPERADMISSIBLE = vREWRITE_RULE[vGSYM vSUPERADMISSIBLE_T]
        vRECURSION_CASEWISE_PAIRWISE;;

(* ------------------------------------------------------------------------- *)
(* The main suite of functions for justifying recursion.                     *)
(* ------------------------------------------------------------------------- *)

let instantiate_casewise_recursion,
    pure_prove_recursive_function_exists,
    prove_general_recursive_function_exists =

(* ------------------------------------------------------------------------- *)
(* Make some basic simplification of conjunction of welldefinedness clauses. *)
(* ------------------------------------------------------------------------- *)

  let vSIMPLIFY_WELLDEFINEDNESS_CONV =
    let vLSYM =
      vGEN_ALL -| vCONV_RULE(vLAND_CONV(vONCE_DEPTH_CONV vSYM_CONV)) -| vSPEC_ALL
    and evensimps = prove
     ((parse_term "((2 * m + 2 = 2 * n + 1) <=> F) /\\\n       ((2 * m + 1 = 2 * n + 2) <=> F) /\\\n       ((2 * m = 2 * n + 1) <=> F) /\\\n       ((2 * m + 1 = 2 * n) <=> F) /\\\n       ((2 * m = SUC(2 * n)) <=> F) /\\\n       ((SUC(2 * m) = 2 * n) <=> F)"),
      vREWRITE_TAC[] ----> vREPEAT vCONJ_TAC ---->
      vDISCH_THEN(vMP_TAC -| vAP_TERM (parse_term "EVEN")) ---->
      vREWRITE_TAC[vEVEN_MULT; vEVEN_ADD; vARITH; vEVEN]) in
    let allsimps = itlist (mk_rewrites false)
     [vEQ_ADD_RCANCEL; vEQ_ADD_LCANCEL;
      vEQ_ADD_RCANCEL_0; vEQ_ADD_LCANCEL_0;
      vLSYM vEQ_ADD_RCANCEL_0; vLSYM vEQ_ADD_LCANCEL_0;
      vEQ_MULT_RCANCEL; vEQ_MULT_LCANCEL;
      vEQT_INTRO(vSPEC_ALL vEQ_REFL);
      vADD_EQ_0; vLSYM vADD_EQ_0;
      vMULT_EQ_0; vLSYM vMULT_EQ_0;
      vMULT_EQ_1; vLSYM vMULT_EQ_1;
      vARITH_RULE (parse_term "(m + n = 1) <=> (m = 1) /\\ (n = 0) \\/ (m = 0) /\\ (n = 1)");
      vARITH_RULE (parse_term "(1 = m + n) <=> (m = 1) /\\ (n = 0) \\/ (m = 0) /\\ (n = 1)");
      evensimps; vARITH_EQ] []
    and [@warning "-8"] [simp1; simp2; simp3] = map vMATCH_MP (vCONJUNCTS
      (vTAUT
       (parse_term "((a <=> F) /\\ (b <=> b) ==> ((a ==> b) <=> T)) /\\\n        ((a <=> a') /\\ (a' ==> (b <=> T)) ==> ((a ==> b) <=> T)) /\\\n        ((a <=> a') /\\ (a' ==> (b <=> b')) ==> ((a ==> b) <=> (a' ==> b')))")))
    and false_tm = (parse_term "F") and and_tm = (parse_term "(/\\)")
    and eq_refl = vEQT_INTRO(vSPEC_ALL vEQ_REFL) in
    fun tm ->
      let net = itlist (net_of_thm false) allsimps (!basic_rectype_net) in
      let vRECTYPE_ARITH_EQ_CONV =
        vTOP_SWEEP_CONV(vREWRITES_CONV net) +--->
        vGEN_REWRITE_CONV vDEPTH_CONV [vAND_CLAUSES; vOR_CLAUSES] in
      let vSIMPLIFY_CASE_DISTINCTNESS_CLAUSE tm =
        let avs,bod = strip_forall tm in
        let ant,cons = dest_imp bod in
        let ath = vRECTYPE_ARITH_EQ_CONV ant in
        let atm = rand(concl ath) in
        let bth = vCONJ ath
          (if atm = false_tm then vREFL cons
                    else vDISCH atm
                          (vPURE_REWRITE_CONV[eq_refl; vASSUME atm] cons)) in
        let cth = try simp1 bth with Failure _ -> try simp2 bth
                  with Failure _ -> simp3 bth in
        itlist vMK_FORALL avs cth in
      (vDEPTH_BINOP_CONV and_tm vSIMPLIFY_CASE_DISTINCTNESS_CLAUSE +--->
       vGEN_REWRITE_CONV vDEPTH_CONV [vFORALL_SIMP; vAND_CLAUSES]) tm in

(* ------------------------------------------------------------------------- *)
(* Simplify an existential question about a pattern.                         *)
(* ------------------------------------------------------------------------- *)

  let vEXISTS_PAT_CONV =
    let pth = prove
     ((parse_term "((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ z y)) <=> s = t) /\\\n       ((?y. _GUARDED_PATTERN (GEQ s t) g (GEQ z y)) <=> g /\\ s = t)"),
      vREWRITE_TAC[_UNGUARDED_PATTERN; _GUARDED_PATTERN; vGEQ_DEF] ---->
      vMESON_TAC[]) in
    let basecnv = vGEN_REWRITE_CONV vI [pth]
    and pushcnv = vGEN_REWRITE_CONV vI [vSWAP_EXISTS_THM] in
    let rec vEXISTS_PAT_CONV tm =
     ((pushcnv +---> vBINDER_CONV vEXISTS_PAT_CONV) ||-->
      basecnv) tm in
    fun tm -> if is_exists tm then vEXISTS_PAT_CONV tm
              else failwith "EXISTS_PAT_CONV" in

(* ------------------------------------------------------------------------- *)
(* Hack a proforma to introduce new pairing or pattern variables.            *)
(* ------------------------------------------------------------------------- *)

  let vHACK_PROFORMA,vEACK_PROFORMA =
    let elemma0 = prove
     ((parse_term "((!z. GEQ (f z) (g z)) <=> (!x y. GEQ (f(x,y)) (g(x,y)))) /\\\n       ((\\p. P p) = (\\(x,y). P(x,y)))"),
      vREWRITE_TAC[vFUN_EQ_THM; vFORALL_PAIR_THM])
    and elemma1 = prove
     ((parse_term "(!P. (!t:A->B->C#D->E. P t) <=> (!t. P (\\a b (c,d). t a b d c))) /\\\n       (!P. (!t:B->C#D->E. P t) <=> (!t. P (\\b (c,d). t b d c))) /\\\n       (!P. (!t:C#D->E. P t) <=> (!t. P (\\(c,d). t d c)))"),
      vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vREPEAT vSTRIP_TAC ---->
      vASM_REWRITE_TAC[] ++-->
       [vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "\\a b d c. (t:A->B->C#D->E) a b (c,d)"));
        vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "\\b d c. (t:B->C#D->E) b (c,d)"));
        vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "\\d c. (t:C#D->E) (c,d)"))] ---->
      vMATCH_MP_TAC vEQ_IMP ----> vAP_TERM_TAC ---->
      vREWRITE_TAC[vFUN_EQ_THM; vFORALL_PAIR_THM]) in
    let vHACK_PROFORMA n th =
      if n <= 1 then th else
      let mkname i = "_P"^string_of_int i in
      let ty = end_itlist (fun s t -> mk_type("prod",[s;t]))
                          (map (mk_vartype -| mkname) (1--n)) in
      let conv i =
        let name = "x"^string_of_int i in
        let cnv = vALPHA_CONV (mk_var(name,mk_vartype(mkname i))) in
        fun tm -> if is_abs tm && name_of(bndvar tm) <> name
                  then cnv tm else failwith "conv" in
      let convs = vFIRST_CONV (map conv (1--n)) in
      let th1 = vINST_TYPE [ty,(parse_type "P")] th in
      let th2 = vREWRITE_RULE[vFORALL_PAIR_THM] th1 in
      let th3 = vREWRITE_RULE[elemma0; elemma1] th2 in
      vCONV_RULE(vREDEPTH_CONV convs) th3
    and vEACK_PROFORMA n th =
      if n <= 1 then th else
      let mkname i = "_Q"^string_of_int i in
      let ty = end_itlist (fun s t -> mk_type("prod",[s;t]))
                          (map (mk_vartype -| mkname) (1--n)) in
      let conv i =
        let name = "t"^string_of_int i in
        let cnv = vALPHA_CONV (mk_var(name,mk_vartype(mkname i))) in
        fun tm -> if is_abs tm && name_of(bndvar tm) <> name
                  then cnv tm else failwith "conv" in
      let convs = vFIRST_CONV (map conv (1--n)) in
      let th1 = vINST_TYPE [ty,(parse_type "Q")] th in
      let th2 = vREWRITE_RULE[vEXISTS_PAIR_THM] th1 in
      let th3 = vREWRITE_RULE[elemma1] th2 in
      let th4 = vREWRITE_RULE[vFORALL_PAIR_THM] th3 in
      vCONV_RULE(vREDEPTH_CONV convs) th4 in
    vHACK_PROFORMA,vEACK_PROFORMA in

(* ------------------------------------------------------------------------- *)
(* Hack and apply.                                                           *)
(* ------------------------------------------------------------------------- *)

  let vAPPLY_PROFORMA_TAC th (_asl,w as gl) =
    let vs = fst(dest_gabs(body(rand w))) in
    let n = 1 + length(fst(splitlist dest_pair vs)) in
    (vMATCH_MP_TAC(vHACK_PROFORMA n th) ----> vBETA_TAC) gl in

  let is_pattern p n tm =
    try let f,args = strip_comb(snd(strip_exists (body(body tm)))) in
        is_const f && name_of f = p && length args = n
    with Failure _ -> false in

  let vSIMPLIFY_MATCH_WELLDEFINED_TAC =
    let pth0 = vMESON[]
     (parse_term "(a /\\ x = k ==> x = y ==> d) ==> (a /\\ x = k /\\ y = k ==> d)")
    and pth1 = vMESON[]
     (parse_term "(a /\\ b /\\ c /\\ x = k ==> x = y ==> d)\n      ==> (a /\\ x = k /\\ b /\\ y = k /\\ c ==> d)") in
    vREPEAT vGEN_TAC ---->
    (vMATCH_MP_TAC pth1 |---> vMATCH_MP_TAC pth0) ---->
    vCONV_TAC(vRAND_CONV vSIMPLIFY_WELLDEFINEDNESS_CONV) ---->
    vPURE_REWRITE_TAC
      [vAND_CLAUSES; vIMP_CLAUSES; vOR_CLAUSES; vEQ_CLAUSES; vNOT_CLAUSES] in

  let rec headonly f tm =
    match tm with
      Comb(s,t) -> headonly f s && headonly f t && not(t = f)
    | Abs(_x,t) -> headonly f t
    | _ -> true in

  let vMAIN_ADMISS_TAC (_asl,w as gl) =
    let had,args = strip_comb w in
    if not(is_const had) then failwith "ADMISS_TAC" else
    let f,fbod = dest_abs(last args) in
    let _xtup,bod = dest_gabs fbod in
    let hop,args = strip_comb bod in
    match (name_of had,name_of hop) with
      "superadmissible","COND"
          -> vAPPLY_PROFORMA_TAC vSUPERADMISSIBLE_COND gl
    | "superadmissible","_MATCH" when
          name_of(repeat rator (last args)) = "_SEQPATTERN"
          -> (vAPPLY_PROFORMA_TAC vSUPERADMISSIBLE_MATCH_SEQPATTERN ---->
              vCONV_TAC(vONCE_DEPTH_CONV vEXISTS_PAT_CONV)) gl
    | "superadmissible","_MATCH" when
         is_pattern "_UNGUARDED_PATTERN" 2 (last args)
          -> let n = length(fst(strip_exists(body(body(last args))))) in
             let th = vEACK_PROFORMA n vSUPERADMISSIBLE_MATCH_UNGUARDED_PATTERN in
             (vAPPLY_PROFORMA_TAC th ----> vCONJ_TAC ++-->
               [vSIMPLIFY_MATCH_WELLDEFINED_TAC; vALL_TAC]) gl
    | "superadmissible","_MATCH" when
         is_pattern "_GUARDED_PATTERN" 3 (last args)
          -> let n = length(fst(strip_exists(body(body(last args))))) in
             let th = vEACK_PROFORMA n vSUPERADMISSIBLE_MATCH_GUARDED_PATTERN in
             (vAPPLY_PROFORMA_TAC th ----> vCONJ_TAC ++-->
               [vSIMPLIFY_MATCH_WELLDEFINED_TAC; vALL_TAC]) gl
    | "superadmissible",_ when is_comb bod && rator bod = f
          -> vAPPLY_PROFORMA_TAC vSUPERADMISSIBLE_TAIL gl
    | "admissible","sum"
          -> vAPPLY_PROFORMA_TAC vADMISSIBLE_SUM gl
    | "admissible","nsum"
          -> vAPPLY_PROFORMA_TAC vADMISSIBLE_NSUM gl
    | "admissible","MAP"
          -> vAPPLY_PROFORMA_TAC vADMISSIBLE_MAP gl
    | "admissible","_MATCH" when
          name_of(repeat rator (last args)) = "_SEQPATTERN"
          -> (vAPPLY_PROFORMA_TAC vADMISSIBLE_MATCH_SEQPATTERN ---->
              vCONV_TAC(vONCE_DEPTH_CONV vEXISTS_PAT_CONV)) gl
    | "admissible","_MATCH"
          -> vAPPLY_PROFORMA_TAC vADMISSIBLE_MATCH gl
    | "admissible","_UNGUARDED_PATTERN"
          -> vAPPLY_PROFORMA_TAC vADMISSIBLE_UNGUARDED_PATTERN gl
    | "admissible","_GUARDED_PATTERN"
          -> vAPPLY_PROFORMA_TAC vADMISSIBLE_GUARDED_PATTERN gl
    | "admissible",_ when is_abs bod
          -> vAPPLY_PROFORMA_TAC vADMISSIBLE_LAMBDA gl
    | "admissible",_ when is_comb bod && rator bod = f
          -> if free_in f (rand bod) then
               vAPPLY_PROFORMA_TAC vADMISSIBLE_NEST gl
             else
               vAPPLY_PROFORMA_TAC vADMISSIBLE_BASE gl
    | "admissible",_ when is_comb bod && headonly f bod
          -> vAPPLY_PROFORMA_TAC vADMISSIBLE_COMB gl
    | _ -> failwith "MAIN_ADMISS_TAC" in

  let vADMISS_TAC =
    vCONJ_TAC |--->
    vMATCH_ACCEPT_TAC vADMISSIBLE_CONST |--->
    vMATCH_ACCEPT_TAC vSUPERADMISSIBLE_CONST |--->
    vMAIN_ADMISS_TAC |--->
    vMATCH_MP_TAC vADMISSIBLE_IMP_SUPERADMISSIBLE in

(* ------------------------------------------------------------------------- *)
(* Instantiate the casewise recursion theorem for existential claim.         *)
(* Also make a first attempt to simplify the distinctness clause. This may   *)
(* yield a theorem with just the wellfoundedness "?(<<)" assumption, or it   *)
(* may be that and an additional distinctness one.                           *)
(* ------------------------------------------------------------------------- *)

  let instantiate_casewise_recursion =
    let vEXPAND_PAIRED_ALL_CONV =
      let pth0,pth1 = (vCONJ_PAIR -| prove)
       ((parse_term "(ALL (\\(s,t). P s t) [a,b] <=> P a b) /\\\n         (ALL (\\(s,t). P s t) (CONS (a,b) l) <=>\n          P a b /\\ ALL (\\(s,t). P s t) l)"),
        vREWRITE_TAC[vALL]) in
      let conv0 = vREWR_CONV pth0 and conv1 = vREWR_CONV pth1 in
      let rec conv tm =
        try conv0 tm with Failure _ ->
        let th = conv1 tm in vCONV_RULE (funpow 2 vRAND_CONV conv) th in
      conv
    and vLAMBDA_PAIR_CONV =
      let rewr1 =  vGEN_REWRITE_RULE vI [vGSYM vFORALL_PAIR_THM]
      and rewr2 = vGEN_REWRITE_CONV vI [vFUN_EQ_THM] in
      fun parms tm ->
        let parm = end_itlist (curry mk_pair) parms in
        let x,bod = dest_abs tm in
        let tm' = mk_gabs(parm,vsubst[parm,x] bod) in
        let th1 = vBETA_CONV(mk_comb(tm,parm))
        and th2 = vGEN_BETA_CONV (mk_comb(tm',parm)) in
        let th3 = vTRANS th1 (vSYM th2) in
        let th4 = itlist (fun v th -> rewr1 (vGEN v th))
                         (butlast parms) (vGEN (last parms) th3) in
        vEQ_MP (vSYM(rewr2(mk_eq(tm,tm')))) th4
    and vFORALL_PAIR_CONV =
      let rule = vGEN_REWRITE_RULE vRAND_CONV [vGSYM vFORALL_PAIR_THM] in
      let rec depair l t =
        match l with
          [_v] -> vREFL t
        | _v::vs -> rule(vBINDER_CONV (depair vs) t) 
        | _ -> assert false in
      fun parm parms ->
        let p = mk_var("P",mk_fun_ty (type_of parm) bool_ty) in
        let tm = list_mk_forall(parms,mk_comb(p,parm)) in
        vGEN p (vSYM(depair parms tm)) in
    let vELIM_LISTOPS_CONV =
      vPURE_REWRITE_CONV[vPAIRWISE; vALL; vGSYM vCONJ_ASSOC; vAND_CLAUSES] +--->
      vTOP_DEPTH_CONV vGEN_BETA_CONV in
    let tuple_function_existence tm =
      let f,def = dest_exists tm in
      let domtys0,ranty0 = splitlist dest_fun_ty (type_of f) in
      let nargs =
        itlist
         (max -| length -| snd -| strip_comb -| lhs -| snd -| strip_forall)
         (conjuncts(snd(strip_forall def))) 0 in
      let domtys,midtys = chop_list nargs domtys0 in
      let ranty = itlist mk_fun_ty midtys ranty0 in
      if length domtys <= 1 then vASSUME tm else
      let dty = end_itlist (fun ty1 ty2 -> mk_type("prod",[ty1;ty2])) domtys in
      let f' = variant (frees tm)
                       (mk_var(fst(dest_var f),mk_fun_ty dty ranty)) in
      let gvs = map genvar domtys in
      let f'' = list_mk_abs(gvs,mk_comb(f',end_itlist (curry mk_pair) gvs)) in
      let def' = subst [f'',f] def in
      let th1 = vEXISTS (tm,f'') (vASSUME def')
      and bth = vBETAS_CONV (list_mk_comb(f'',gvs)) in
      let th2 = vGEN_REWRITE_CONV vTOP_DEPTH_CONV [bth] (hd(hyp th1)) in
      vSIMPLE_CHOOSE f' (vPROVE_HYP (vUNDISCH(snd(vEQ_IMP_RULE th2))) th1) in
    let pinstantiate_casewise_recursion def =
      try vPART_MATCH vI vEXISTS_REFL def with Failure _ ->
      let f,bod = dest_exists def in
      let cjs = conjuncts bod in
      let eqs = map (snd -| strip_forall) cjs in
      let lefts,rights = unzip(map dest_eq eqs) in
      let arglists = map (snd -| strip_comb) lefts in
      let parms0 = freesl(unions arglists) in
      let parms = if parms0 <> [] then parms0 else [genvar aty] in
      let parm = end_itlist (curry mk_pair) parms in
      let ss = map (fun a -> mk_gabs(parm,end_itlist (curry mk_pair) a))
                   arglists
      and ts = map (fun a -> mk_abs(f,mk_gabs(parm,a))) rights in
      let clauses = mk_flist(map2 (curry mk_pair) ss ts) in
      let pth = vISPEC clauses vRECURSION_SUPERADMISSIBLE in
      let vFIDDLE_CONV =
        (vLAND_CONV -| vLAND_CONV -| vBINDER_CONV -| vRAND_CONV -| vLAND_CONV -|
         vGABS_CONV -| vRATOR_CONV -| vLAND_CONV -| vABS_CONV) in
      let th0 = vUNDISCH(vCONV_RULE(vFIDDLE_CONV(vLAMBDA_PAIR_CONV parms)) pth) in
      let th1 = vEQ_MP (vGEN_ALPHA_CONV f (concl th0)) th0 in
      let rewr_forall_th = vREWR_CONV(vFORALL_PAIR_CONV parm parms) in
      let th2 = vCONV_RULE (vBINDER_CONV
                    (vLAND_CONV(vGABS_CONV rewr_forall_th) +--->
                     vEXPAND_PAIRED_ALL_CONV)) th1 in
      let _f2,bod2 = dest_exists(concl th2) in
      let ths3 = map
       (vCONV_RULE (vCOMB2_CONV (funpow 2 vRAND_CONV vGEN_BETA_CONV)
                  (vRATOR_CONV vBETA_CONV +---> vGEN_BETA_CONV)) -| vSPEC_ALL)
       (vCONJUNCTS(vASSUME bod2)) in
      let ths4 = map2
       (fun th t -> let avs,tbod = strip_forall t in
                    itlist vGEN avs (vPART_MATCH vI th tbod)) ths3 cjs in
      let th5 = vSIMPLE_EXISTS f (end_itlist vCONJ ths4) in
      let th6 = vPROVE_HYP th2 (vSIMPLE_CHOOSE f th5) in
      let th7 =
       (vRAND_CONV(vCOMB2_CONV
            (vRAND_CONV (vLAND_CONV (vGABS_CONV(vBINDER_CONV
                     (vBINDER_CONV(rewr_forall_th) +---> rewr_forall_th)))))
            (vLAND_CONV (funpow 2 vGABS_CONV(vBINDER_CONV
                     (vBINDER_CONV(rewr_forall_th) +--->
                      rewr_forall_th))))) +--->
        vELIM_LISTOPS_CONV) (hd(hyp th6)) in
      let th8 = vPROVE_HYP (vUNDISCH(snd(vEQ_IMP_RULE th7))) th6 in
      let wfasm,cdasm = dest_conj(hd(hyp th8)) in
      let th9 = vPROVE_HYP (vCONJ (vASSUME wfasm) (vASSUME cdasm)) th8 in
      let th10 = vSIMPLIFY_WELLDEFINEDNESS_CONV cdasm in
      let th11 = vPROVE_HYP (vUNDISCH(snd(vEQ_IMP_RULE th10))) th9 in
      vPROVE_HYP vTRUTH th11 in
    fun etm ->
      let eth = tuple_function_existence etm in
      let dtm = hd(hyp eth) in
      let dth = pinstantiate_casewise_recursion dtm in
      vPROVE_HYP dth eth in

(* ------------------------------------------------------------------------- *)
(* Justify existence assertion and try to simplify/remove side-conditions.   *)
(* ------------------------------------------------------------------------- *)

  let pure_prove_recursive_function_exists =
    let break_down_admissibility th1 =
      if hyp th1 = [] then th1 else
      let def = concl th1 in
      let _f,bod = dest_exists def in
      let cjs = conjuncts bod in
      let eqs = map (snd -| strip_forall) cjs in
      let lefts,_rights = unzip(map dest_eq eqs) in
      let arglists = map (snd -| strip_comb) lefts in
      let parms0 = freesl(unions arglists) in
      let parms = if parms0 <> [] then parms0 else [genvar aty] in
      let wfasm = find is_exists (hyp th1) in
      let ord,bod = dest_exists wfasm in
      let vSIMP_ADMISS_TAC =
        vREWRITE_TAC[vLET_DEF; vLET_END_DEF] ---->
        vREPEAT vADMISS_TAC ---->
        vTRY(vW(fun (_asl,w) -> let v = fst(dest_forall w) in
                vX_GEN_TAC v ---->
                vMAP_EVERY
                  (fun v -> vTRY(vGEN_REWRITE_TAC vI [vFORALL_PAIR_THM]) ---->
                            vX_GEN_TAC v)
                  parms ---->
                vCONV_TAC(vTOP_DEPTH_CONV vGEN_BETA_CONV) ---->
                vMAP_EVERY (fun v -> vSPEC_TAC(v,v)) (rev parms @ [v]))) ---->
        vPURE_REWRITE_TAC[vFORALL_SIMP] ---->
        vW(fun (_asl,w) -> vMAP_EVERY (fun t -> vSPEC_TAC(t,t))
                                   (subtract (frees w) [ord])) ---->
        vW(fun (_asl,w) -> vACCEPT_TAC(vASSUME w)) in
      let th2 = prove(bod,vSIMP_ADMISS_TAC) in
      let th3 = vSIMPLE_EXISTS ord th2 in
      let allasms = hyp th3 and wfasm = lhand(concl th2) in
      let th4 = vASSUME(list_mk_conj(wfasm::subtract allasms [wfasm])) in
      let th5 = vSIMPLE_CHOOSE ord (itlist vPROVE_HYP (vCONJUNCTS th4) th3) in
      vPROVE_HYP th5 th1 in
    fun dtm ->
      let th =  break_down_admissibility(instantiate_casewise_recursion dtm) in
      if concl th = dtm then th
      else failwith "prove_general_recursive_function_exists: sanity" in

(* ------------------------------------------------------------------------- *)
(* Same, but attempt to prove the wellfoundedness hyp by good guesses.       *)
(* ------------------------------------------------------------------------- *)

  let prove_general_recursive_function_exists =
    let prove_depth_measure_exists =
      let num_ty = (parse_type "num") in
      fun tyname ->
        let _,_,sth = assoc tyname (!inductive_type_store) in
        let ty,zty = dest_fun_ty
         (type_of(fst(dest_exists(snd(strip_forall(concl sth)))))) in
        let rth = vINST_TYPE [num_ty,zty] sth in
        let _avs,bod = strip_forall(concl rth) in
        let _ev,cbod = dest_exists bod in
        let process_clause k t =
          let avs,eq = strip_forall t in
          let l,_r = dest_eq eq in
          let fn,cargs = dest_comb l in
          let _con,args = strip_comb cargs in
          let bargs = filter (fun t -> type_of t = ty) args in
          let r' = list_mk_binop (parse_term "(+):num->num->num")
                    (mk_small_numeral k :: map (curry mk_comb fn) bargs) in
          list_mk_forall(avs,mk_eq(l,r')) in
        let cjs = conjuncts cbod in
        let def = map2 process_clause (1--length cjs) cjs in
        prove_recursive_functions_exist sth (list_mk_conj def) in
    let vINDUCTIVE_MEASURE_THEN tac (asl,w) =
      let ev,_bod = dest_exists w in
      let ty = fst(dest_type(fst(dest_fun_ty(type_of ev)))) in
      let th = prove_depth_measure_exists ty in
      let ev',_bod' = dest_exists(concl th) in
      let th' = vINST_TYPE(type_match (type_of ev') (type_of ev) []) th in
      (vMP_TAC th' ----> vMATCH_MP_TAC vMONO_EXISTS ---->
       vGEN_TAC ----> vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ----> tac) (asl,w) in
    let vCONSTANT_MEASURE_THEN =
      let one_tm = (parse_term "1") in
      fun tac (asl,w) ->
        let ev,_bod = dest_exists w in
        let ty = fst(dest_fun_ty(type_of ev)) in
        (vEXISTS_TAC(mk_abs(genvar ty,one_tm)) ----> tac) (asl,w) in
    let vGUESS_MEASURE_THEN tac =
      (vEXISTS_TAC (parse_term "\\n. n + 1") ----> tac) |--->
      (vINDUCTIVE_MEASURE_THEN tac) |--->
      vCONSTANT_MEASURE_THEN tac in
    let pth_lexleft = prove
     ((parse_term "(?r. WF(r) /\\\n            ?s. WF(s) /\\\n                P(\\(x1,y1) (x2,y2). r x1 x2 \\/ (x1 = x2) /\\ s y1 y2))\n       ==> ?t:A#B->A#B->bool. WF(t) /\\ P t"),
      vREPEAT vSTRIP_TAC ----> vEXISTS_TAC
       (parse_term "\\(x1:A,y1:B) (x2:A,y2:B). r x1 x2 \\/ (x1 = x2) /\\ s y1 y2") ---->
      vASM_SIMP_TAC[vWF_LEX]) in
    let pth_lexright = prove
     ((parse_term "(?r. WF(r) /\\\n            ?s. WF(s) /\\\n                P(\\(x1,y1) (x2,y2). r y1 y2 \\/ (y1 = y2) /\\ s x1 x2))\n       ==> ?t:A#B->A#B->bool. WF(t) /\\ P t"),
      vREPEAT vSTRIP_TAC ---->
      vEXISTS_TAC (parse_term "\\u:A#B v:A#B.\n                    (\\(x1:B,y1:A) (x2:B,y2:A). r x1 x2 \\/ (x1 = x2) /\\ s y1 y2)\n                     ((\\(a,b). b,a) u) ((\\(a,b). b,a) v)") ---->
      vASM_SIMP_TAC[vWF_LEX; vETA_AX;
       vISPECL [(parse_term "R:A#B->A#B->bool"); (parse_term "\\(b:B,a:A). a,b")] vWF_MEASURE_GEN] ---->
      vFIRST_X_ASSUM(fun th -> vMP_TAC th ---->
                              vMATCH_MP_TAC vEQ_IMP ---->
                              vAP_TERM_TAC) ---->
      vREWRITE_TAC[vFUN_EQ_THM; vFORALL_PAIR_THM]) in
    let pth_measure = prove
     ((parse_term "(?m:A->num. P(MEASURE m)) ==> ?r:A->A->bool. WF(r) /\\ P r"),
      vMESON_TAC[vWF_MEASURE]) in
    let rec vGUESS_WF_THEN tac (asl,w) =
     ((vMATCH_MP_TAC pth_lexleft ----> vGUESS_WF_THEN (vGUESS_WF_THEN tac)) |--->
      (vMATCH_MP_TAC pth_lexright ----> vGUESS_WF_THEN (vGUESS_WF_THEN tac)) |--->
      (vMATCH_MP_TAC pth_measure ---->
       vREWRITE_TAC[vMEASURE; vMEASURE_LE] ---->
       vREWRITE_TAC[vFORALL_PAIR_THM] ---->
       vGUESS_MEASURE_THEN tac)) (asl,w) in
    let vPRE_GUESS_TAC =
      vCONV_TAC(vBINDER_CONV(vDEPTH_BINOP_CONV (parse_term "(/\\)")
       (vTRY_CONV vSIMPLIFY_WELLDEFINEDNESS_CONV +--->
        vTRY_CONV vFORALL_UNWIND_CONV))) in
    let vGUESS_ORDERING_TAC =
      let false_tm = (parse_term "\\x:A y:A. F") in
      vW(fun (_asl,w) ->
            let ty = fst(dest_fun_ty(type_of(fst(dest_exists w)))) in
            vEXISTS_TAC(inst [ty,aty] false_tm) ---->
            vREWRITE_TAC[vWF_FALSE] ----> vNO_TAC) |--->
      vGUESS_WF_THEN
       (vREWRITE_TAC[vFORALL_PAIR_THM] ----> vARITH_TAC) in
    fun etm ->
      let th = pure_prove_recursive_function_exists etm in
      try let wtm = find is_exists (hyp th) in
          let wth = prove(wtm,vPRE_GUESS_TAC ----> vGUESS_ORDERING_TAC) in
          vPROVE_HYP wth th
      with Failure _ -> th in

  instantiate_casewise_recursion,
  pure_prove_recursive_function_exists,
  prove_general_recursive_function_exists;;

(* ------------------------------------------------------------------------- *)
(* Simple "define" function.                                                 *)
(* ------------------------------------------------------------------------- *)

let define =
  let close_definition_clauses tm =
    let avs,bod = strip_forall tm in
    let cjs = conjuncts bod in
    let fs =
      try map (repeat rator -| lhs -| snd -| strip_forall) cjs
      with Failure _ -> failwith "close_definition_clauses: non-equation" in
    if length (setify fs) <> 1
    then failwith "close_definition_clauses: defining multiple functions" else
    let f = hd fs in
    if mem f avs then failwith "close_definition_clauses: fn quantified" else
    let do_clause t =
      let lvs,bod = strip_forall t in
      let fvs = subtract (frees(lhs bod)) (f::lvs) in
      vSPECL fvs (vASSUME(list_mk_forall(fvs,t))) in
    let ths = map do_clause cjs in
    let ajs = map (hd -| hyp) ths in
    let th = vASSUME(list_mk_conj ajs) in
    f,itlist vGEN avs (itlist vPROVE_HYP (vCONJUNCTS th) (end_itlist vCONJ ths)) in
  fun tm ->
    let tm' = snd(strip_forall tm) in
    try let th,th' = tryfind (fun th -> th,vPART_MATCH vI th tm')
                             (!the_definitions) in
        if can (vPART_MATCH vI th') (concl th) then
         (warn true "Benign redefinition"; th')
        else failwith ""
    with Failure _ ->
      let f,th = close_definition_clauses tm in
      let etm = mk_exists(f,hd(hyp th)) in
      let th1 = prove_general_recursive_function_exists etm in
      let th2 = new_specification[fst(dest_var f)] th1 in
      let g = mk_mconst(dest_var f) in
      let th3 = vPROVE_HYP th2 (vINST [g,f] th) in
      the_definitions := th3::(!the_definitions); th3;;
