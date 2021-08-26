(* ========================================================================= *)
(* Theory of wellfounded relations.                                          *)
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
open Simp
open Theorems
open Ind_defs
open Class
open Meson
open Pair
open Nums
open Recursion
open Arith
;;

(* ------------------------------------------------------------------------- *)
(* Definition of wellfoundedness for arbitrary (infix) relation <<           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<<",(12,"right"));;

let vWF = new_definition
  (parse_term "WF(<<) <=> !P:A->bool. (?x. P(x)) ==> (?x. P(x) /\\ !y. y << x ==> ~P(y))");;

(* ------------------------------------------------------------------------- *)
(* Strengthen it to equality.                                                *)
(* ------------------------------------------------------------------------- *)

let vWF_EQ = try Cache.lookup_thm "WF_EQ" with _ ->  prove
 ((parse_term "WF(<<) <=> !P:A->bool. (?x. P(x)) <=> (?x. P(x) /\\ !y. y << x ==> ~P(y))"),
  vREWRITE_TAC[vWF] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence of wellfounded induction.                                     *)
(* ------------------------------------------------------------------------- *)

let vWF_IND = try Cache.lookup_thm "WF_IND" with _ ->  prove
 ((parse_term "WF(<<) <=> !P:A->bool. (!x. (!y. y << x ==> P(y)) ==> P(x)) ==> !x. P(x)"),
  vREWRITE_TAC[vWF] ----> vEQ_TAC ----> vDISCH_TAC ----> vGEN_TAC ---->
  vPOP_ASSUM(vMP_TAC -| vSPEC (parse_term "\\x:A. ~P(x)")) ----> vREWRITE_TAC[] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence of the "infinite descending chains" version.                  *)
(* ------------------------------------------------------------------------- *)

let vWF_DCHAIN = try Cache.lookup_thm "WF_DCHAIN" with _ ->  prove
 ((parse_term "WF(<<) <=> ~(?s:num->A. !n. s(SUC n) << s(n))"),
  vREWRITE_TAC[vWF; vTAUT (parse_term "(a <=> ~b) <=> (~a <=> b)"); vNOT_FORALL_THM] ---->
  vEQ_TAC ----> vDISCH_THEN vCHOOSE_TAC ++-->
   [vPOP_ASSUM(vMP_TAC -| vREWRITE_RULE[vNOT_IMP]) ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "a:A")) vASSUME_TAC) ---->
    vSUBGOAL_THEN (parse_term "!x:A. ?y. P(x) ==> P(y) /\\ y << x") vMP_TAC ++-->
     [vASM_MESON_TAC[]; vREWRITE_TAC[vSKOLEM_THM]] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "f:A->A") vSTRIP_ASSUME_TAC) ---->
    vCHOOSE_TAC(prove_recursive_functions_exist num_RECURSION
     (parse_term "(s(0) = a:A) /\\ (!n. s(SUC n) = f(s n))")) ---->
    vEXISTS_TAC (parse_term "s:num->A") ----> vASM_REWRITE_TAC[] ---->
    vSUBGOAL_THEN (parse_term "!n. P(s n) /\\ s(SUC n):A << s(n)")
      (fun th -> vASM_MESON_TAC[th]) ---->
    vINDUCT_TAC ----> vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[];
    vEXISTS_TAC (parse_term "\\y:A. ?n:num. y = s(n)") ----> vREWRITE_TAC[] ---->
    vASM_MESON_TAC[]]);;

let vWF_DHAIN_TRANSITIVE = try Cache.lookup_thm "WF_DHAIN_TRANSITIVE" with _ ->  prove
 ((parse_term "!(<<):A->A->bool.\n        (!x y z. x << y /\\ y << z ==> x << z)\n        ==> (WF(<<) <=> ~(?s:num->A. !i j. i < j ==> s j << s i))"),
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vWF_DCHAIN] ---->
  vAP_TERM_TAC ----> vEQ_TAC ----> vMATCH_MP_TAC vMONO_EXISTS ---->
  vX_GEN_TAC (parse_term "s:num->A") ----> vSIMP_TAC[vLT] ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vTRANSITIVE_STEPWISE_LT ----> vASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *uniqueness* part of recursion.                        *)
(* ------------------------------------------------------------------------- *)

let vWF_UREC = try Cache.lookup_thm "WF_UREC" with _ ->  prove
 ((parse_term "WF(<<) ==>\n       !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))\n            ==> !(f:A->B) g. (!x. f x = H f x) /\\ (!x. g x = H g x)\n                              ==> (f = g)"),
  vREWRITE_TAC[vWF_IND] ----> vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vFUN_EQ_THM] ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vGEN_TAC ---->
  vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ----> vASM_REWRITE_TAC[]);;

let vWF_UREC_WF = try Cache.lookup_thm "WF_UREC_WF" with _ ->  prove
 ((parse_term "(!H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))\n        ==> !(f:A->bool) g. (!x. f x = H f x) /\\ (!x. g x = H g x)\n                          ==> (f = g))\n   ==> WF(<<)"),
  vREWRITE_TAC[vWF_IND] ----> vDISCH_TAC ----> vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "\\f x. P(x:A) \\/ !z:A. z << x ==> f(z)")) ---->
  vREWRITE_TAC[] ---->
  vW(vC vSUBGOAL_THEN (fun t -> vREWRITE_TAC[t]) -| funpow 2 lhand -| snd) ++-->
   [vMESON_TAC[]; vDISCH_THEN(vMP_TAC -| vSPECL [(parse_term "P:A->bool"); (parse_term "\\x:A. T")]) ---->
    vREWRITE_TAC[vFUN_EQ_THM] ----> vASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Stronger form of recursion with "inductive invariant" (Krstic/Matthews).  *)
(* ------------------------------------------------------------------------- *)

let vWF_REC_INVARIANT = try Cache.lookup_thm "WF_REC_INVARIANT" with _ ->  prove
 ((parse_term "WF(<<)\n   ==> !H S. (!f g x. (!z. z << x ==> (f z = g z) /\\ S z (f z))\n                      ==> (H f x = H g x) /\\ S x (H f x))\n             ==> ?f:A->B. !x. (f x = H f x)"),
  let lemma = prove_inductive_relations_exist
    (parse_term "!f:A->B x. (!z. z << x ==> R z (f z)) ==> R x (H f x)") in
  vREWRITE_TAC[vWF_IND] ----> vREPEAT vSTRIP_TAC ---->
  vX_CHOOSE_THEN (parse_term "R:A->B->bool") vSTRIP_ASSUME_TAC lemma ---->
  vSUBGOAL_THEN (parse_term "!x:A. ?!y:B. R x y") (fun th -> vASM_MESON_TAC[th]) ---->
  vFIRST_X_ASSUM vMATCH_MP_TAC ----> vREPEAT vSTRIP_TAC ---->
  vFIRST_X_ASSUM(fun th -> vGEN_REWRITE_TAC vBINDER_CONV [th]) ---->
  vSUBGOAL_THEN (parse_term "!x:A y:B. R x y ==> S x y") vMP_TAC ----> vASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Equivalent to just *existence* part of recursion.                         *)
(* ------------------------------------------------------------------------- *)

let vWF_REC = try Cache.lookup_thm "WF_REC" with _ ->  prove
 ((parse_term "WF(<<)\n   ==> !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))\n           ==> ?f:A->B. !x. f x = H f x"),
  vREPEAT vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vWF_REC_INVARIANT) ---->
  vEXISTS_TAC (parse_term "\\x:A y:B. T") ----> vASM_REWRITE_TAC[]);;

let vWF_REC_WF = try Cache.lookup_thm "WF_REC_WF" with _ ->  prove
 ((parse_term "(!H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))\n                 ==> ?f:A->num. !x. f x = H f x)\n   ==> WF(<<)"),
  vDISCH_TAC ----> vREWRITE_TAC[vWF_DCHAIN] ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "x:num->A")) ---->
  vSUBGOAL_THEN (parse_term "!n. (x:num->A)(@m. x(m) << x(n)) << x(n)") vASSUME_TAC ++-->
   [vCONV_TAC(vBINDER_CONV vSELECT_CONV) ----> vASM_MESON_TAC[]; vALL_TAC] ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC
   (parse_term "\\f:A->num. \\y:A. if ?p:num. y = x(p)\n                     then SUC(f(x(@m. x(m) << y)))\n                     else 0")) ---->
  vREWRITE_TAC[vNOT_IMP] ----> vCONJ_TAC ++-->
   [vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ----> vREWRITE_TAC[] ---->
    vFIRST_ASSUM(vX_CHOOSE_THEN (parse_term "p:num") vSUBST_ALL_TAC) ---->
    vAP_TERM_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vFIRST_ASSUM vMATCH_ACCEPT_TAC; vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "f:A->num") vMP_TAC) ---->
  vDISCH_THEN(vMP_TAC -| vGEN (parse_term "n:num") -| vSPEC (parse_term "(x:num->A) n")) ---->
  vSUBGOAL_THEN (parse_term "!n. ?p. (x:num->A) n = x p") (fun th -> vREWRITE_TAC[th]) ++-->
   [vMESON_TAC[]; vDISCH_TAC] ---->
  vSUBGOAL_THEN (parse_term "!n:num. ?k. f(x(k):A) < f(x(n))") vASSUME_TAC ++-->
   [vGEN_TAC ----> vEXISTS_TAC (parse_term "@m:num. x(m):A << x(n)") ---->
    vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vRAND_CONV [th]) ----> vREWRITE_TAC[vLT];
    vMP_TAC(vSPEC (parse_term "\\n:num. ?i:num. n = f(x(i):A)") num_WOP) ---->
    vREWRITE_TAC[] ----> vASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Combine the two versions of the recursion theorem.                        *)
(* ------------------------------------------------------------------------- *)

let vWF_EREC = try Cache.lookup_thm "WF_EREC" with _ ->  prove
 ((parse_term "WF(<<) ==>\n       !H. (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x))\n            ==> ?!f:A->B. !x. f x = H f x"),
  vMESON_TAC[vWF_REC; vWF_UREC]);;

(* ------------------------------------------------------------------------- *)
(* Defining a recursive function via an existence condition.                 *)
(* ------------------------------------------------------------------------- *)

let vWF_REC_EXISTS = try Cache.lookup_thm "WF_REC_EXISTS" with _ ->  prove
 ((parse_term "WF((<<):A->A->bool)\n   ==> !P. (!f g x y. (!z. z << x ==> f z = g z) ==> (P f x y <=> P g x y)) /\\\n           (!f x. (!z. z << x ==> P f z (f z)) ==> ?y. P f x y)\n           ==> ?f:A->B. !x. P f x (f x)"),
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "?f:A->B. !x. f x = @y. P f x y") vMP_TAC ++-->
   [vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vWF_REC) ---->
    vREPEAT vSTRIP_TAC ----> vAP_TERM_TAC ----> vABS_TAC ---->
    vFIRST_X_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
    vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC (parse_term "f:A->B") ---->
    vDISCH_THEN(fun th ->
      vONCE_REWRITE_TAC[th] ----> vASSUME_TAC(vGSYM th)) ---->
    vCONV_TAC(vBINDER_CONV vSELECT_CONV) ---->
    vFIRST_ASSUM(vMATCH_MP_TAC -| vGEN_REWRITE_RULE vI [vWF_IND]) ---->
    vASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Some preservation theorems for wellfoundedness.                           *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<<<",(12,"right"));;

let vWF_SUBSET = try Cache.lookup_thm "WF_SUBSET" with _ ->  prove
 ((parse_term "!(<<) (<<<). (!(x:A) y. x << y ==> x <<< y) /\\ WF(<<<) ==> WF(<<)"),
  vREPEAT vGEN_TAC ----> 
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ----> vREWRITE_TAC[vWF] ---->
  vDISCH_TAC ----> vGEN_TAC ----> vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
  vUNDISCH_TAC (parse_term "!(x:A) (y:A). x << y ==> x <<< y") ----> vMESON_TAC[]);;

let vWF_RESTRICT = try Cache.lookup_thm "WF_RESTRICT" with _ ->  prove
 ((parse_term "!(<<) P:A->bool. WF(<<) ==> WF(\\x y. P x /\\ P y /\\ x << y)"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC(vREWRITE_RULE[vIMP_CONJ] vWF_SUBSET) ---->
  vSIMP_TAC[]);;

let vWF_MEASURE_GEN = try Cache.lookup_thm "WF_MEASURE_GEN" with _ ->  prove
 ((parse_term "!(<<) (m:A->B). WF(<<) ==> WF(\\x x'. m x << m x')"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vWF_IND] ----> vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC (parse_term "\\y:B. !x:A. (m(x) = y) ==> P x")) ---->
  vUNDISCH_TAC (parse_term "!x. (!y. (m:A->B) y << m x ==> P y) ==> P x") ---->
  vREWRITE_TAC[] ----> vMESON_TAC[]);;

let vWF_LEX_DEPENDENT = try Cache.lookup_thm "WF_LEX_DEPENDENT" with _ ->  prove
 ((parse_term "!R:A->A->bool S:A->B->B->bool. WF(R) /\\ (!a. WF(S a))\n         ==> WF(\\(r1,s1) (r2,s2). R r1 r2 \\/ (r1 = r2) /\\ S r1 s1 s2)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vWF] ----> vSTRIP_TAC ---->
  vX_GEN_TAC (parse_term "P:A#B->bool") ----> vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vGEN_REWRITE_TAC vI [vFORALL_PAIR_THM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "a0:A"); (parse_term "b0:B")] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "\\a:A. ?b:B. P(a,b)")) ---->
  vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [(parse_term "a0:A"); (parse_term "b0:B")]) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "a:A") (vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC)) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "b1:B")) ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "a:A"); (parse_term "\\b. (P:A#B->bool) (a,b)")]) ---->
  vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "b1:B")) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "b:B") (vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC)) ---->
  vDISCH_TAC ----> vEXISTS_TAC (parse_term "(a:A,b:B)") ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vFORALL_PAIR_THM] ----> vASM_MESON_TAC[]);;

let vWF_LEX = try Cache.lookup_thm "WF_LEX" with _ ->  prove
 ((parse_term "!R:A->A->bool S:B->B->bool. WF(R) /\\ WF(S)\n         ==> WF(\\(r1,s1) (r2,s2). R r1 r2 \\/ (r1 = r2) /\\ S s1 s2)"),
  vSIMP_TAC[vWF_LEX_DEPENDENT; vETA_AX]);;

let vWF_POINTWISE = try Cache.lookup_thm "WF_POINTWISE" with _ ->  prove
 ((parse_term "WF((<<) :A->A->bool) /\\ WF((<<<) :B->B->bool)\n   ==> WF(\\(x1,y1) (x2,y2). x1 << x2 /\\ y1 <<< y2)"),
  vSTRIP_TAC ----> vMATCH_MP_TAC vWF_SUBSET ----> vEXISTS_TAC
   (parse_term "\\(x1,y1) (x2,y2). x1 << x2 \\/ (x1:A = x2) /\\ (y1:B) <<< (y2:B)") ---->
  vCONJ_TAC ++-->
   [vREWRITE_TAC[vFORALL_PAIR_THM] ----> vCONV_TAC vTAUT;
    vMATCH_MP_TAC vWF_LEX ----> vASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Wellfoundedness properties of natural numbers.                            *)
(* ------------------------------------------------------------------------- *)

let vWF_num = try Cache.lookup_thm "WF_num" with _ ->  prove
 ((parse_term "WF(<)"),
  vREWRITE_TAC[vWF_IND; num_WF]);;

let vWF_REC_num = try Cache.lookup_thm "WF_REC_num" with _ ->  prove
 ((parse_term "!H. (!f g n. (!m. m < n ==> (f m = g m)) ==> (H f n = H g n))\n        ==> ?f:num->A. !n. f n = H f n"),
  vMATCH_ACCEPT_TAC(vMATCH_MP vWF_REC vWF_num));;

(* ------------------------------------------------------------------------- *)
(* Natural number measures (useful in program verification).                 *)
(* ------------------------------------------------------------------------- *)

let vMEASURE = new_definition
  (parse_term "MEASURE m = \\x y. m(x) < m(y)");;

let vWF_MEASURE = try Cache.lookup_thm "WF_MEASURE" with _ ->  prove
 ((parse_term "!m:A->num. WF(MEASURE m)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMEASURE] ---->
  vMATCH_MP_TAC vWF_MEASURE_GEN ---->
  vMATCH_ACCEPT_TAC vWF_num);;

let vMEASURE_LE = try Cache.lookup_thm "MEASURE_LE" with _ ->  prove
 ((parse_term "(!y. MEASURE m y a ==> MEASURE m y b) <=> m(a) <= m(b)"),
    vREWRITE_TAC[vMEASURE] ----> vMESON_TAC[vNOT_LE; vLTE_TRANS; vLT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Trivially, a WF relation is irreflexive and antisymmetric.                *)
(* ------------------------------------------------------------------------- *)

let vWF_ANTISYM = try Cache.lookup_thm "WF_ANTISYM" with _ ->  prove
 ((parse_term "!(<<) x y:A. WF(<<) ==> ~(x << y /\\ y << x)"),
  vREPEAT vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vWF]) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "\\z:A. z = x \\/ z = y")) ---->
  vASM_MESON_TAC[]);;

let vWF_REFL = try Cache.lookup_thm "WF_REFL" with _ ->  prove
 ((parse_term "!x:A. WF(<<) ==> ~(x << x)"),
  vMESON_TAC[vWF_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Even more trivially, the everywhere-false relation is wellfounded.        *)
(* ------------------------------------------------------------------------- *)

let vWF_FALSE = try Cache.lookup_thm "WF_FALSE" with _ ->  prove
 ((parse_term "WF(\\x y:A. F)"),
  vREWRITE_TAC[vWF]);;

(* ------------------------------------------------------------------------- *)
(* The Nash-Williams minimal bad sequence argument for some predicate `bad`  *)
(* that is a "safety property" in the Lamport/Alpern/Schneider sense.        *)
(* ------------------------------------------------------------------------- *)

let vMINIMAL_BAD_SEQUENCE = try Cache.lookup_thm "MINIMAL_BAD_SEQUENCE" with _ ->  prove
 ((parse_term "!(<<) (bad:(num->A)->bool).\n        WF(<<) /\\\n        (!x. ~bad x ==> ?n. !y. (!k. k < n ==> y k = x k) ==> ~bad y) /\\\n        (?x. bad x)\n         ==> ?y. bad y /\\\n                 !z n. bad z /\\ (!k. k < n ==> z k = y k) ==> ~(z n << y n)"),
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vSUBGOAL_THEN
   (parse_term "?x:num->A. !n. (?y. bad y /\\ (!k. k < n ==> y k = x k) /\\ y n = x n) /\\\n                   !z. bad z /\\ (!k. k < n ==> z k = x k) ==> ~(z n << x n)")
  vMP_TAC ++-->
   [vMATCH_MP_TAC(vMATCH_MP vWF_REC_EXISTS vWF_num) ----> vSIMP_TAC[];
    vMATCH_MP_TAC vMONO_EXISTS ----> vASM_MESON_TAC[]] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x:num->A"); (parse_term "n:num")] ---->
  vDISCH_TAC ----> vREWRITE_TAC[vMESON[]
    (parse_term "(?a. (?y. P y /\\ Q y /\\ f y = a) /\\ (!z. A z ==> ~B a z)) <=>\n     ?y. (P y /\\ Q y) /\\ (!z. B (f y) z ==> ~A z)")] ---->
  vMP_TAC(vISPECL [(parse_term "(<<):A->A->bool"); (parse_term "\\x:num->A. x n")] vWF_MEASURE_GEN) ---->
  vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vWF] ----> vDISCH_THEN vMATCH_MP_TAC ---->
  vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ----> vSPEC_TAC((parse_term "n:num"),(parse_term "n:num")) ---->
  vINDUCT_TAC ----> vSIMP_TAC[vLT] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tail recursion.                                                           *)
(* ------------------------------------------------------------------------- *)

let vWF_REC_TAIL = try Cache.lookup_thm "WF_REC_TAIL" with _ ->  prove
 ((parse_term "!P g h. ?f:A->B. !x. f x = if P(x) then f(g x) else h x"),
  let lemma1 = prove
   ((parse_term "~(P 0) ==> ((?n. P(SUC n)) <=> (?n. P(n)))"),
    vMESON_TAC[num_CASES; vNOT_SUC])
  and lemma2 = prove
   ((parse_term "(P 0) ==> ((!m. m < n ==> P(SUC m)) <=> (!m. m < SUC n ==> P(m)))"),
    vREPEAT(vDISCH_TAC |---> vEQ_TAC) ----> vINDUCT_TAC ---->
    vASM_MESON_TAC[vLT_SUC; vLT_0]) in
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vGEN (parse_term "x:A") (vISPECL [(parse_term "x:A"); (parse_term "\\y:A n:num. g(y):A")] num_RECURSION)) ---->
  vREWRITE_TAC[vSKOLEM_THM; vFORALL_AND_THM] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "s:A->num->A") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "\\x:A. if ?n:num. ~P(s x n)\n                    then (h:A->B)(@y. ?n. (y = s x n) /\\ ~P(s x n) /\\\n                                          !m. m < n ==> P(s x m))\n                    else something_arbitrary:B") ---->
  vX_GEN_TAC (parse_term "x:A") ---->
  vSUBGOAL_THEN (parse_term "!n x:A. s (g x) n :A = s x (SUC n)") vASSUME_TAC ++-->
   [vINDUCT_TAC ----> vASM_REWRITE_TAC[];
    vUNDISCH_THEN (parse_term "!x:A n. s x (SUC n) :A = g (s x n)") (vK vALL_TAC)] ---->
  vASM_CASES_TAC (parse_term "(P:A->bool) x") ----> vASM_REWRITE_TAC[] ++-->
   [vASM_SIMP_TAC[lemma1] ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
    vCONV_TAC vSYM_CONV ----> vASM_SIMP_TAC[lemma2; lemma1];
    vCOND_CASES_TAC ++--> [vALL_TAC; vASM_MESON_TAC[]] ---->
    vAP_TERM_TAC ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
    vREWRITE_TAC[] ----> vX_GEN_TAC (parse_term "y:A") ----> vEQ_TAC ++-->
     [vSIMP_TAC[vLEFT_IMP_EXISTS_THM] ---->
      vINDUCT_TAC ----> vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[vLT_0];
      vASM_MESON_TAC[vLT]]]);;

(* ------------------------------------------------------------------------- *)
(* A more general mix of tail and wellfounded recursion.                     *)
(* ------------------------------------------------------------------------- *)

let vWF_REC_TAIL_GENERAL = try Cache.lookup_thm "WF_REC_TAIL_GENERAL" with _ ->  prove
 ((parse_term "!P G H. WF(<<) /\\\n           (!f g x. (!z. z << x ==> (f z = g z))\n                    ==> (P f x <=> P g x) /\\ G f x = G g x /\\ H f x = H g x) /\\\n           (!f g x. (!z. z << x ==> (f z = g z)) ==> (H f x = H g x)) /\\\n           (!f x y. P f x /\\ y << G f x ==> y << x)\n           ==> ?f:A->B. !x. f x = if P f x then f(G f x) else H f x"),
  vREPEAT vSTRIP_TAC ---->
  vCHOOSE_THEN vMP_TAC
   (prove_inductive_relations_exist
     (parse_term "(!x:A. ~(P f x) ==> terminates f x) /\\\n      (!x. P (f:A->B) x /\\ terminates f (G f x) ==> terminates f x)")) ---->
  vREWRITE_TAC[vFORALL_AND_THM] ---->
  vDISCH_THEN(vSTRIP_ASSUME_TAC -| vGSYM) ---->
  vSUBGOAL_THEN
   (parse_term "?while. !f:A->B x:A. while f x = if P f x then while f (G f x) else x")
   (vSTRIP_ASSUME_TAC -| vGSYM)
  ++--> [vREWRITE_TAC[vGSYM vSKOLEM_THM; vWF_REC_TAIL]; vALL_TAC] ---->
  vSUBGOAL_THEN
   (parse_term "?f:A->B. !x. f x = if terminates f x then H f (while f x :A) else anything")
  vMP_TAC ++-->
   [vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vWF_REC) ---->
    vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC(vMESON[]
     (parse_term "(a = b) /\\ (a /\\ b ==> (x = y) /\\ (f x = g x))\n      ==> ((if a then f x else d) = (if b then g y else d))")) ---->
    vREPEAT vSTRIP_TAC ++-->
     [vSUBGOAL_THEN
       (parse_term "!f g x.\n           (!x y. P f x /\\ y << G (f:A->B) x ==> y << x) /\\\n           (!y:A. (!z:A. z << y ==> z << x)\n                  ==> (P f y = P g y) /\\ (G f y = G g y))\n               ==> terminates f x ==> terminates g x")
       (fun th -> vEQ_TAC ----> vMATCH_MP_TAC th ----> vASM_MESON_TAC[]) ---->
      vGEN_TAC ----> vGEN_TAC ---->
      vREWRITE_TAC[vRIGHT_FORALL_IMP_THM; vIMP_CONJ] ----> vDISCH_TAC ---->
      vONCE_REWRITE_TAC[vTAUT (parse_term "a ==> b ==> c <=> b ==> a ==> c")] ---->
      vFIRST_X_ASSUM vMATCH_MP_TAC ----> vASM_MESON_TAC[];
      vSUBGOAL_THEN
       (parse_term "!x:A. terminates (f:A->B) x /\\\n              (!y:A. (!z:A. z << y ==> z << x)\n                     ==> (P f y <=> P g y) /\\ (G f y :A = G g y))\n              ==> (while f x :A = while g x)")
       (fun th -> vMATCH_MP_TAC th ----> vASM_MESON_TAC[]) ---->
      vREWRITE_TAC[vIMP_CONJ] ---->
      vFIRST_X_ASSUM vMATCH_MP_TAC ----> vASM_MESON_TAC[];
      vFIRST_X_ASSUM vMATCH_MP_TAC ---->
      vSUBGOAL_THEN
       (parse_term "!f:A->B. (!x:A y:A. P f x /\\ y << G f x ==> y << x)\n         ==> !x. terminates f x ==> !y. y << while f x ==> y << x")
       (fun th -> vASM_MESON_TAC[th]) ---->
      vGEN_TAC ----> vDISCH_TAC ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
      vASM_MESON_TAC[]];
    vMATCH_MP_TAC vMONO_EXISTS ----> vGEN_TAC ---->
    vDISCH_THEN(fun th -> vASSUME_TAC(vGSYM th) ----> vMP_TAC th) ---->
    vMATCH_MP_TAC vMONO_FORALL ----> vX_GEN_TAC (parse_term "x:A") ---->
    vASM_CASES_TAC (parse_term "P (f:A->B) (x:A) :bool") ----> vASM_MESON_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Tactic to apply WF induction on a free "measured" term in the goal.       *)
(* ------------------------------------------------------------------------- *)

let vWF_INDUCT_TAC =
  let qqconv =
    let pth = prove
     ((parse_term "(!x. P x ==> !y. Q x y) <=> !y x. P x ==> Q x y"), vMESON_TAC[]) in
    vGEN_REWRITE_CONV vI [pth]
  and eqconv =
    let pth = prove
     ((parse_term "(!m. P m ==> (m = e) ==> Q) <=> (P e ==> Q)"), vMESON_TAC[]) in
    vREWR_CONV pth in
  let rec qqconvs tm =
    try (qqconv +---> vBINDER_CONV qqconvs) tm
    with Failure _ -> eqconv tm in
  fun tm (_asl,w as gl) ->
    let fvs = frees tm
    and gv = genvar(type_of tm) in
    let pat = list_mk_forall(gv::fvs,mk_imp(mk_eq(gv,tm),w)) in
    let th0 = vUNDISCH(vPART_MATCH rand num_WF pat) in
    let th1 = vMP (vSPECL (tm::fvs) th0) (vREFL tm) in
    let th2 = vCONV_RULE(vLAND_CONV qqconvs) (vDISCH_ALL th1) in
    (vMATCH_MP_TAC th2 ----> vMAP_EVERY vX_GEN_TAC fvs ---->
     vCONV_TAC(vLAND_CONV qqconvs) ----> vDISCH_THEN vASSUME_TAC) gl;;
