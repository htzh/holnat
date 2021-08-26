(* ========================================================================= *)
(* Theory of real numbers.                                                   *)
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
open Preterm
open Parser
open Equal
open Boolean
open Drule
open Tactics
open Itab
open Simp
open Theorems
open Class
open Meson
open Quot
open Pair
open Nums
open Recursion
open Arith
open Calc_num

let [@warning "-33"] () = let open Grobner in ()(* Ensures normalizer and grobner run before the operators are overloaded otherwise NUM_NORMALIZE_CONV and others may fail *)
;;

(* ------------------------------------------------------------------------- *)
(* The main infix overloaded operations                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("++",(16,"right"));;
parse_as_infix("**",(20,"right"));;
parse_as_infix("<<=",(12,"right"));;
parse_as_infix("===",(10,"right"));;

parse_as_infix ("treal_mul",(20,"right"));;
parse_as_infix ("treal_add",(16,"right"));;
parse_as_infix ("treal_le",(12,"right"));;
parse_as_infix ("treal_eq",(10,"right"));;

make_overloadable "+" (parse_type "A->A->A");;
make_overloadable "-" (parse_type "A->A->A");;
make_overloadable "*" (parse_type "A->A->A");;
make_overloadable "/" (parse_type "A->A->A");;
make_overloadable "<" (parse_type "A->A->bool");;
make_overloadable "<=" (parse_type "A->A->bool");;
make_overloadable ">" (parse_type "A->A->bool");;
make_overloadable ">=" (parse_type "A->A->bool");;
make_overloadable "--" (parse_type "A->A");;
make_overloadable "pow" (parse_type "A->num->A");;
make_overloadable "inv" (parse_type "A->A");;
make_overloadable "abs" (parse_type "A->A");;
make_overloadable "max" (parse_type "A->A->A");;
make_overloadable "min" (parse_type "A->A->A");;
make_overloadable "&" (parse_type "num->A");;

do_list overload_interface
 ["+",(parse_term "(+):num->num->num"); "-",(parse_term "(-):num->num->num");
  "*",(parse_term "(*):num->num->num"); "<",(parse_term "(<):num->num->bool");
  "<=",(parse_term "(<=):num->num->bool"); ">",(parse_term "(>):num->num->bool");
  ">=",(parse_term "(>=):num->num->bool")];;

let prioritize_num() = prioritize_overload(mk_type("num",[]));;

(* ------------------------------------------------------------------------- *)
(* Absolute distance function on the naturals.                               *)
(* ------------------------------------------------------------------------- *)

let dist = new_definition
  (parse_term "dist(m,n) = (m - n) + (n - m)");;

(* ------------------------------------------------------------------------- *)
(* Some easy theorems.                                                       *)
(* ------------------------------------------------------------------------- *)

let vDIST_REFL = try Cache.lookup_thm "DIST_REFL" with _ ->  prove
 ((parse_term "!n. dist(n,n) = 0"),
  vREWRITE_TAC[dist; vSUB_REFL; vADD_CLAUSES]);;

let vDIST_LZERO = try Cache.lookup_thm "DIST_LZERO" with _ ->  prove
 ((parse_term "!n. dist(0,n) = n"),
  vREWRITE_TAC[dist; vSUB_0; vADD_CLAUSES]);;

let vDIST_RZERO = try Cache.lookup_thm "DIST_RZERO" with _ ->  prove
 ((parse_term "!n. dist(n,0) = n"),
  vREWRITE_TAC[dist; vSUB_0; vADD_CLAUSES]);;

let vDIST_SYM = try Cache.lookup_thm "DIST_SYM" with _ ->  prove
 ((parse_term "!m n. dist(m,n) = dist(n,m)"),
  vREWRITE_TAC[dist] ----> vMATCH_ACCEPT_TAC vADD_SYM);;

let vDIST_LADD = try Cache.lookup_thm "DIST_LADD" with _ ->  prove
 ((parse_term "!m p n. dist(m + n,m + p) = dist(n,p)"),
  vREWRITE_TAC[dist; vSUB_ADD_LCANCEL]);;

let vDIST_RADD = try Cache.lookup_thm "DIST_RADD" with _ ->  prove
 ((parse_term "!m p n. dist(m + p,n + p) = dist(m,n)"),
  vREWRITE_TAC[dist; vSUB_ADD_RCANCEL]);;

let vDIST_LADD_0 = try Cache.lookup_thm "DIST_LADD_0" with _ ->  prove
 ((parse_term "!m n. dist(m + n,m) = n"),
  vREWRITE_TAC[dist; vADD_SUB2; vADD_SUBR2; vADD_CLAUSES]);;

let vDIST_RADD_0 = try Cache.lookup_thm "DIST_RADD_0" with _ ->  prove
 ((parse_term "!m n. dist(m,m + n) = n"),
  vONCE_REWRITE_TAC[vDIST_SYM] ----> vMATCH_ACCEPT_TAC vDIST_LADD_0);;

let vDIST_LMUL = try Cache.lookup_thm "DIST_LMUL" with _ ->  prove
 ((parse_term "!m n p. m * dist(n,p) = dist(m * n,m * p)"),
  vREWRITE_TAC[dist; vLEFT_ADD_DISTRIB; vLEFT_SUB_DISTRIB]);;

let vDIST_RMUL = try Cache.lookup_thm "DIST_RMUL" with _ ->  prove
 ((parse_term "!m n p. dist(m,n) * p = dist(m * p,n * p)"),
  vREWRITE_TAC[dist; vRIGHT_ADD_DISTRIB; vRIGHT_SUB_DISTRIB]);;

let vDIST_EQ_0 = try Cache.lookup_thm "DIST_EQ_0" with _ ->  prove
 ((parse_term "!m n. (dist(m,n) = 0) <=> (m = n)"),
  vREWRITE_TAC[dist; vADD_EQ_0; vSUB_EQ_0; vLE_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Simplifying theorem about the distance operation.                         *)
(* ------------------------------------------------------------------------- *)

let vDIST_ELIM_THM = try Cache.lookup_thm "DIST_ELIM_THM" with _ ->  prove
 ((parse_term "P(dist(x,y)) <=> !d. ((x = y + d) ==> P(d)) /\\ ((y = x + d) ==> P(d))"),
  vDISJ_CASES_TAC(vSPECL [(parse_term "x:num"); (parse_term "y:num")] vLE_CASES) ---->
  vPOP_ASSUM(vX_CHOOSE_THEN (parse_term "e:num") vSUBST1_TAC -| vREWRITE_RULE[vLE_EXISTS]) ---->
  vREWRITE_TAC[dist; vADD_SUB; vADD_SUB2; vADD_SUBR; vADD_SUBR2] ---->
  vREWRITE_TAC[vADD_CLAUSES; vEQ_ADD_LCANCEL] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vEQ_SYM_EQ] ---->
  vREWRITE_TAC[vGSYM vADD_ASSOC; vEQ_ADD_LCANCEL_0; vADD_EQ_0] ---->
  vASM_CASES_TAC (parse_term "e = 0") ----> vASM_REWRITE_TAC[] ---->
  vEQ_TAC ----> vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Now some more theorems.                                                   *)
(* ------------------------------------------------------------------------- *)

let vDIST_LE_CASES,vDIST_ADDBOUND,vDIST_TRIANGLE,vDIST_ADD2,vDIST_ADD2_REV =
  let vDIST_ELIM_TAC =
    let conv =
      vHIGHER_REWRITE_CONV[vSUB_ELIM_THM; vCOND_ELIM_THM; vDIST_ELIM_THM] false in
    vCONV_TAC conv ----> vTRY vGEN_TAC ----> vCONJ_TAC ---->
    vDISCH_THEN(fun th -> vSUBST_ALL_TAC th ---->
                         (let l,r = dest_eq (concl th) in
                          if is_var l && not (vfree_in l r) then vALL_TAC
                          else vASSUME_TAC th)) in
  let vDIST_ELIM_TAC' =
    vREPEAT vSTRIP_TAC ----> vREPEAT vDIST_ELIM_TAC ---->
    vREWRITE_TAC[vGSYM vNOT_LT; vLT_EXISTS] ---->
    vDISCH_THEN(vCHOOSE_THEN vSUBST_ALL_TAC) ----> vPOP_ASSUM vMP_TAC ---->
    vCONV_TAC(vLAND_CONV vNUM_CANCEL_CONV) ---->
    vREWRITE_TAC[vADD_CLAUSES; vNOT_SUC] in
  let vDIST_LE_CASES = prove
   ((parse_term "!m n p. dist(m,n) <= p <=> (m <= n + p) /\\ (n <= m + p)"),
    vREPEAT vGEN_TAC ----> vREPEAT vDIST_ELIM_TAC ---->
    vREWRITE_TAC[vGSYM vADD_ASSOC; vLE_ADD; vLE_ADD_LCANCEL])
  and vDIST_ADDBOUND = prove
   ((parse_term "!m n. dist(m,n) <= m + n"),
    vREPEAT vGEN_TAC ----> vDIST_ELIM_TAC ++-->
     [vONCE_REWRITE_TAC[vADD_SYM]; vALL_TAC] ---->
    vREWRITE_TAC[vADD_ASSOC; vLE_ADDR])
  and [@warning "-8"] [vDIST_TRIANGLE; vDIST_ADD2; vDIST_ADD2_REV] = (vCONJUNCTS -| prove)
   ((parse_term "(!m n p. dist(m,p) <= dist(m,n) + dist(n,p)) /\\\n     (!m n p q. dist(m + n,p + q) <= dist(m,p) + dist(n,q)) /\\\n     (!m n p q. dist(m,p) <= dist(m + n,p + q) + dist(n,q))"),
    vDIST_ELIM_TAC') in
  vDIST_LE_CASES,vDIST_ADDBOUND,vDIST_TRIANGLE,vDIST_ADD2,vDIST_ADD2_REV;;

let vDIST_TRIANGLE_LE = try Cache.lookup_thm "DIST_TRIANGLE_LE" with _ ->  prove
 ((parse_term "!m n p q. dist(m,n) + dist(n,p) <= q ==> dist(m,p) <= q"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
  vEXISTS_TAC (parse_term "dist(m,n) + dist(n,p)") ----> vASM_REWRITE_TAC[vDIST_TRIANGLE]);;

let vDIST_TRIANGLES_LE = try Cache.lookup_thm "DIST_TRIANGLES_LE" with _ ->  prove
 ((parse_term "!m n p q r s.\n        dist(m,n) <= r /\\ dist(p,q) <= s ==> dist(m,p) <= dist(n,q) + r + s"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDIST_TRIANGLE_LE ---->
  vEXISTS_TAC (parse_term "n:num") ----> vGEN_REWRITE_TAC vRAND_CONV [vADD_SYM] ---->
  vREWRITE_TAC[vGSYM vADD_ASSOC] ----> vMATCH_MP_TAC vLE_ADD2 ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vDIST_TRIANGLE_LE ---->
  vEXISTS_TAC (parse_term "q:num") ----> vGEN_REWRITE_TAC vRAND_CONV [vADD_SYM] ---->
  vREWRITE_TAC[vLE_ADD_LCANCEL] ----> vONCE_REWRITE_TAC[vDIST_SYM] ---->
  vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Useful lemmas about bounds.                                               *)
(* ------------------------------------------------------------------------- *)

let vBOUNDS_LINEAR = try Cache.lookup_thm "BOUNDS_LINEAR" with _ ->  prove
 ((parse_term "!A B C. (!n. A * n <= B * n + C) <=> A <= B"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vNOT_LE] ---->
    vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC -| vREWRITE_RULE[vLT_EXISTS]) ---->
    vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vLE_ADD_LCANCEL] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "SUC C")) ---->
    vREWRITE_TAC[vNOT_LE; vMULT_CLAUSES; vADD_CLAUSES; vLT_SUC_LE] ---->
    vREWRITE_TAC[vADD_ASSOC; vLE_ADDR];
    vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC -| vREWRITE_RULE[vLE_EXISTS]) ---->
    vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vGSYM vADD_ASSOC; vLE_ADD]]);;

let vBOUNDS_LINEAR_0 = try Cache.lookup_thm "BOUNDS_LINEAR_0" with _ ->  prove
 ((parse_term "!A B. (!n. A * n <= B) <=> (A = 0)"),
  vREPEAT vGEN_TAC ----> vMP_TAC(vSPECL [(parse_term "A:num"); (parse_term "0"); (parse_term "B:num")] vBOUNDS_LINEAR) ---->
  vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vLE]);;

let vBOUNDS_DIVIDED = try Cache.lookup_thm "BOUNDS_DIVIDED" with _ ->  prove
 ((parse_term "!P. (?B. !n. P(n) <= B) <=>\n       (?A B. !n. n * P(n) <= A * n + B)"),
  vGEN_TAC ----> vEQ_TAC ----> vSTRIP_TAC ++-->
   [vMAP_EVERY vEXISTS_TAC [(parse_term "B:num"); (parse_term "0")] ---->
    vGEN_TAC ----> vREWRITE_TAC[vADD_CLAUSES] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vMULT_SYM] ---->
    vASM_REWRITE_TAC[vLE_MULT_LCANCEL];
    vEXISTS_TAC (parse_term "P(0) + A + B") ----> vGEN_TAC ---->
    vMP_TAC(vSPECL [(parse_term "n:num"); (parse_term "(P:num->num) n"); (parse_term "P(0) + A + B")]
     vLE_MULT_LCANCEL) ---->
    vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vLE_ADD] ---->
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "A * n + B") ---->
    vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vLEFT_ADD_DISTRIB] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vADD_SYM] ---->
    vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vMULT_SYM] ---->
    vREWRITE_TAC[vGSYM vADD_ASSOC; vLE_ADD_LCANCEL] ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "B * n") ---->
    vREWRITE_TAC[vLE_ADD] ----> vUNDISCH_TAC (parse_term "~(n = 0)") ---->
    vSPEC_TAC((parse_term "n:num"),(parse_term "n:num")) ----> vINDUCT_TAC ---->
    vASM_REWRITE_TAC[vMULT_CLAUSES; vLE_ADD]]);;

let vBOUNDS_NOTZERO = try Cache.lookup_thm "BOUNDS_NOTZERO" with _ ->  prove
 ((parse_term "!P A B. (P 0 0 = 0) /\\ (!m n. P m n <= A * (m + n) + B) ==>\n       (?B. !m n. P m n <= B * (m + n))"),
  vREPEAT vSTRIP_TAC ----> vEXISTS_TAC (parse_term "A + B") ---->
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "m + n = 0") ++-->
   [vRULE_ASSUM_TAC(vREWRITE_RULE[vADD_EQ_0]) ----> vASM_REWRITE_TAC[vLE_0];
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "A * (m + n) + B") ---->
    vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vLE_ADD_LCANCEL] ---->
    vUNDISCH_TAC (parse_term "~(m + n = 0)") ----> vSPEC_TAC((parse_term "m + n"),(parse_term "p:num")) ---->
    vINDUCT_TAC ----> vREWRITE_TAC[vMULT_CLAUSES; vLE_ADD]]);;

let vBOUNDS_IGNORE = try Cache.lookup_thm "BOUNDS_IGNORE" with _ ->  prove
 ((parse_term "!P Q. (?B. !i. P(i) <= Q(i) + B) <=>\n         (?B N. !i. N <= i ==> P(i) <= Q(i) + B)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vSTRIP_TAC ++-->
   [vEXISTS_TAC (parse_term "B:num") ----> vASM_REWRITE_TAC[];
    vPOP_ASSUM vMP_TAC ----> vSPEC_TAC((parse_term "B:num"),(parse_term "B:num")) ---->
    vSPEC_TAC((parse_term "N:num"),(parse_term "N:num")) ----> vINDUCT_TAC ++-->
     [vREWRITE_TAC[vLE_0] ----> vGEN_TAC ----> vDISCH_TAC ---->
      vEXISTS_TAC (parse_term "B:num") ----> vASM_REWRITE_TAC[];
      vGEN_TAC ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vEXISTS_TAC (parse_term "B + P(N:num)") ----> vX_GEN_TAC (parse_term "i:num") ---->
      vDISCH_TAC ----> vASM_CASES_TAC (parse_term "SUC N <= i") ++-->
       [vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "Q(i:num) + B") ---->
        vREWRITE_TAC[vLE_ADD; vADD_ASSOC] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
        vASM_REWRITE_TAC[];
        vUNDISCH_TAC (parse_term "~(SUC N <= i)") ----> vREWRITE_TAC[vNOT_LE; vLT] ---->
        vASM_REWRITE_TAC[vGSYM vNOT_LE] ----> vDISCH_THEN vSUBST1_TAC ---->
        vREWRITE_TAC[vADD_ASSOC] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
        vREWRITE_TAC[vLE_ADD]]]]);;

(* ------------------------------------------------------------------------- *)
(* Define type of nearly additive functions.                                 *)
(* ------------------------------------------------------------------------- *)

let is_nadd = new_definition
  (parse_term "is_nadd x <=> (?B. !m n. dist(m * x(n),n * x(m)) <= B * (m + n))");;

let is_nadd_0 = try Cache.lookup_thm "is_nadd_0" with _ ->  prove
 ((parse_term "is_nadd (\\n. 0)"),
  vREWRITE_TAC[is_nadd; vMULT_CLAUSES; vDIST_REFL; vLE_0]);;

let nadd_abs,nadd_rep =
  new_basic_type_definition "nadd" ("mk_nadd","dest_nadd") is_nadd_0;;

override_interface ("fn",(parse_term "dest_nadd"));;
override_interface ("afn",(parse_term "mk_nadd"));;

(* ------------------------------------------------------------------------- *)
(* Properties of nearly-additive functions.                                  *)
(* ------------------------------------------------------------------------- *)

let vNADD_CAUCHY = try Cache.lookup_thm "NADD_CAUCHY" with _ ->  prove
 ((parse_term "!x. ?B. !m n. dist(m * fn x n,n * fn x m) <= B * (m + n)"),
  vREWRITE_TAC[vGSYM is_nadd; nadd_rep; nadd_abs; vETA_AX]);;

let vNADD_BOUND = try Cache.lookup_thm "NADD_BOUND" with _ ->  prove
 ((parse_term "!x. ?A B. !n. fn x n <= A * n + B"),
  vGEN_TAC ----> vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "x:nadd") vNADD_CAUCHY) ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "B + fn x 1"); (parse_term "B:num")] ----> vGEN_TAC ---->
  vPOP_ASSUM(vMP_TAC -| vSPECL [(parse_term "n:num"); (parse_term "1")]) ---->
  vREWRITE_TAC[vDIST_LE_CASES; vMULT_CLAUSES] ---->
  vDISCH_THEN(vMP_TAC -| vCONJUNCT2) ---->
  vREWRITE_TAC[vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB; vMULT_CLAUSES] ---->
  vREWRITE_TAC[vADD_AC; vMULT_AC]);;

let vNADD_MULTIPLICATIVE = try Cache.lookup_thm "NADD_MULTIPLICATIVE" with _ ->  prove
 ((parse_term "!x. ?B. !m n. dist(fn x (m * n),m * fn x n) <= B * m + B"),
  vGEN_TAC ----> vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "x:nadd") vNADD_CAUCHY) ---->
  vEXISTS_TAC (parse_term "B + fn x 0") ----> vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n = 0") ++-->
   [vMATCH_MP_TAC (vLE_IMP vDIST_ADDBOUND) ---->
    vASM_REWRITE_TAC[vMULT_CLAUSES; vRIGHT_ADD_DISTRIB; vMULT_AC] ---->
    vREWRITE_TAC[vLE_EXISTS] ----> vCONV_TAC(vONCE_DEPTH_CONV vNUM_CANCEL_CONV) ---->
    vREWRITE_TAC[vGSYM vEXISTS_REFL]; vUNDISCH_TAC (parse_term "~(n = 0)")] ---->
  vREWRITE_TAC[vTAUT (parse_term "(~a ==> b) <=> a \\/ b"); vGSYM vLE_MULT_LCANCEL;
              vDIST_LMUL] ---->
  vREWRITE_TAC[vMULT_ASSOC] ----> vGEN_REWRITE_TAC
   (vLAND_CONV -| vRAND_CONV -| vRAND_CONV -| vLAND_CONV) [vMULT_SYM] ---->
  vPOP_ASSUM(vMATCH_MP_TAC -| vLE_IMP) ---->
  vREWRITE_TAC[vLE_EXISTS; vRIGHT_ADD_DISTRIB; vLEFT_ADD_DISTRIB; vMULT_AC] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vNUM_CANCEL_CONV) ---->
  vREWRITE_TAC[vGSYM vEXISTS_REFL]);;

let vNADD_ADDITIVE = try Cache.lookup_thm "NADD_ADDITIVE" with _ ->  prove
 ((parse_term "!x. ?B. !m n. dist(fn x (m + n),fn x m + fn x n) <= B"),
  vGEN_TAC ----> vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "x:nadd") vNADD_CAUCHY) ---->
  vEXISTS_TAC (parse_term "3 * B + fn x 0") ----> vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "m + n = 0") ++-->
   [vRULE_ASSUM_TAC(vREWRITE_RULE[vADD_EQ_0]) ----> vONCE_REWRITE_TAC[vDIST_SYM] ---->
    vASM_REWRITE_TAC[vADD_CLAUSES; vDIST_LADD_0; vLE_ADDR];
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "3 * B") ---->
    vREWRITE_TAC[vLE_ADD] ----> vUNDISCH_TAC (parse_term "~(m + n = 0)")] ---->
  vREWRITE_TAC[vTAUT (parse_term "(~a ==> b) <=> a \\/ b"); vGSYM vLE_MULT_LCANCEL] ---->
  vREWRITE_TAC[vDIST_LMUL; vLEFT_ADD_DISTRIB] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV -| vLAND_CONV) [vRIGHT_ADD_DISTRIB] ---->
  vMATCH_MP_TAC(vLE_IMP vDIST_ADD2) ---->
  vSUBGOAL_THEN (parse_term "(m + n) * 3 * B = B * (m + m + n) + B * (n + m + n)")
  vSUBST1_TAC ++-->
   [vREWRITE_TAC[vSYM(vREWRITE_CONV [vARITH] (parse_term "1 + 1 + 1"))] ---->
    vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vLEFT_ADD_DISTRIB; vMULT_CLAUSES] ---->
    vREWRITE_TAC[vMULT_AC] ----> vCONV_TAC vNUM_CANCEL_CONV ----> vREFL_TAC;
    vMATCH_MP_TAC vLE_ADD2 ----> vASM_REWRITE_TAC[]]);;

let vNADD_SUC = try Cache.lookup_thm "NADD_SUC" with _ ->  prove
 ((parse_term "!x. ?B. !n. dist(fn x (SUC n),fn x n) <= B"),
  vGEN_TAC ----> vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "x:nadd") vNADD_ADDITIVE) ---->
  vEXISTS_TAC (parse_term "B + fn x 1") ----> vGEN_TAC ---->
  vMATCH_MP_TAC(vLE_IMP vDIST_TRIANGLE) ---->
  vEXISTS_TAC (parse_term "fn x n + fn x 1") ---->
  vASM_REWRITE_TAC[vADD1] ----> vMATCH_MP_TAC vLE_ADD2 ---->
  vASM_REWRITE_TAC[vDIST_LADD_0; vLE_REFL]);;

let vNADD_DIST_LEMMA = try Cache.lookup_thm "NADD_DIST_LEMMA" with _ ->  prove
 ((parse_term "!x. ?B. !m n. dist(fn x (m + n),fn x m) <= B * n"),
  vGEN_TAC ----> vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "x:nadd") vNADD_SUC) ---->
  vEXISTS_TAC (parse_term "B:num") ----> vGEN_TAC ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vADD_CLAUSES; vDIST_REFL; vLE_0] ---->
  vMATCH_MP_TAC(vLE_IMP vDIST_TRIANGLE) ---->
  vEXISTS_TAC (parse_term "fn x (m + n)") ---->
  vREWRITE_TAC[vADD1; vLEFT_ADD_DISTRIB] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vADD_SYM] ---->
  vMATCH_MP_TAC vLE_ADD2 ----> vASM_REWRITE_TAC[vGSYM vADD1; vMULT_CLAUSES]);;

let vNADD_DIST = try Cache.lookup_thm "NADD_DIST" with _ ->  prove
 ((parse_term "!x. ?B. !m n. dist(fn x m,fn x n) <= B * dist(m,n)"),
  vGEN_TAC ----> vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "x:nadd") vNADD_DIST_LEMMA) ---->
  vEXISTS_TAC (parse_term "B:num") ----> vREPEAT vGEN_TAC ---->
  vDISJ_CASES_THEN vMP_TAC (vSPECL [(parse_term "m:num"); (parse_term "n:num")] vLE_CASES) ---->
  vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC -| vONCE_REWRITE_RULE[vLE_EXISTS]) ++-->
   [vONCE_REWRITE_TAC[vDIST_SYM]; vALL_TAC] ---->
  vASM_REWRITE_TAC[vDIST_LADD_0]);;

let vNADD_ALTMUL = try Cache.lookup_thm "NADD_ALTMUL" with _ ->  prove
 ((parse_term "!x y. ?A B. !n. dist(n * fn x (fn y n),fn x n * fn y n) <= A * n + B"),
  vREPEAT vGEN_TAC ----> vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "x:nadd") vNADD_CAUCHY) ---->
  vMP_TAC(vSPEC (parse_term "y:nadd") vNADD_BOUND) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "M:num") (vX_CHOOSE_TAC (parse_term "L:num"))) ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "B * (1 + M)"); (parse_term "B * L")] ----> vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV -| vRAND_CONV) [vMULT_SYM] ---->
  vMATCH_MP_TAC vLE_TRANS ---->  vEXISTS_TAC (parse_term "B * (n + fn y n)") ---->
  vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB] ---->
  vREWRITE_TAC[vMULT_CLAUSES; vGSYM vADD_ASSOC; vLE_ADD_LCANCEL] ---->
  vASM_REWRITE_TAC[vGSYM vLEFT_ADD_DISTRIB; vGSYM vMULT_ASSOC; vLE_MULT_LCANCEL]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the equivalence relation and proof that it *is* one.        *)
(* ------------------------------------------------------------------------- *)

override_interface ("===",(parse_term "(nadd_eq):nadd->nadd->bool"));;

let nadd_eq = new_definition
  (parse_term "x === y <=> ?B. !n. dist(fn x n,fn y n) <= B");;

let vNADD_EQ_REFL = try Cache.lookup_thm "NADD_EQ_REFL" with _ ->  prove
 ((parse_term "!x. x === x"),
  vGEN_TAC ----> vREWRITE_TAC[nadd_eq; vDIST_REFL; vLE_0]);;

let vNADD_EQ_SYM = try Cache.lookup_thm "NADD_EQ_SYM" with _ ->  prove
 ((parse_term "!x y. x === y <=> y === x"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_eq] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vDIST_SYM] ----> vREFL_TAC);;

let vNADD_EQ_TRANS = try Cache.lookup_thm "NADD_EQ_TRANS" with _ ->  prove
 ((parse_term "!x y z. x === y /\\ y === z ==> x === z"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_eq] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2
    (vX_CHOOSE_TAC (parse_term "B1:num")) (vX_CHOOSE_TAC (parse_term "B2:num"))) ---->
  vEXISTS_TAC (parse_term "B1 + B2") ----> vX_GEN_TAC (parse_term "n:num") ---->
  vMATCH_MP_TAC (vLE_IMP vDIST_TRIANGLE) ----> vEXISTS_TAC (parse_term "fn y n") ---->
  vMATCH_MP_TAC vLE_ADD2 ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Injection of the natural numbers.                                         *)
(* ------------------------------------------------------------------------- *)

override_interface ("&",(parse_term "nadd_of_num:num->nadd"));;

let nadd_of_num = new_definition
  (parse_term "&k = afn(\\n. k * n)");;

let vNADD_OF_NUM = try Cache.lookup_thm "NADD_OF_NUM" with _ ->  prove
 ((parse_term "!k. fn(&k) = \\n. k * n"),
  vREWRITE_TAC[nadd_of_num; vGSYM nadd_rep; is_nadd] ---->
  vREWRITE_TAC[vDIST_REFL; vLE_0; vMULT_AC]);;

let vNADD_OF_NUM_WELLDEF = try Cache.lookup_thm "NADD_OF_NUM_WELLDEF" with _ ->  prove
 ((parse_term "!m n. (m = n) ==> &m === &n"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN vSUBST1_TAC ---->
  vMATCH_ACCEPT_TAC vNADD_EQ_REFL);;

let vNADD_OF_NUM_EQ = try Cache.lookup_thm "NADD_OF_NUM_EQ" with _ ->  prove
 ((parse_term "!m n. (&m === &n) <=> (m = n)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vNADD_OF_NUM_WELLDEF] ---->
  vREWRITE_TAC[nadd_eq; vNADD_OF_NUM] ---->
  vREWRITE_TAC[vGSYM vDIST_RMUL; vBOUNDS_LINEAR_0; vDIST_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Definition of (reflexive) ordering and the only special property needed.  *)
(* ------------------------------------------------------------------------- *)

override_interface ("<<=",(parse_term "nadd_le:nadd->nadd->bool"));;

let nadd_le = new_definition
  (parse_term "x <<= y <=> ?B. !n. fn x n <= fn y n + B");;

let vNADD_LE_WELLDEF_LEMMA = try Cache.lookup_thm "NADD_LE_WELLDEF_LEMMA" with _ ->  prove
 ((parse_term "!x x' y y'. x === x' /\\ y === y' /\\ x <<= y ==> x' <<= y'"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_eq; nadd_le] ---->
  vREWRITE_TAC[vDIST_LE_CASES; vFORALL_AND_THM] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "B1:num")) vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "B2:num")) vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "B:num")) ---->
  vEXISTS_TAC (parse_term "(B2 + B) + B1") ----> vX_GEN_TAC (parse_term "n:num") ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vLE_IMP -| vCONJUNCT2) ---->
  vREWRITE_TAC[vADD_ASSOC; vLE_ADD_RCANCEL] ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vLE_IMP) ----> vASM_REWRITE_TAC[vLE_ADD_RCANCEL]);;

let vNADD_LE_WELLDEF = try Cache.lookup_thm "NADD_LE_WELLDEF" with _ ->  prove
 ((parse_term "!x x' y y'. x === x' /\\ y === y' ==> (x <<= y <=> x' <<= y')"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vNADD_LE_WELLDEF_LEMMA ----> vASM_REWRITE_TAC[] ++-->
   [vMAP_EVERY vEXISTS_TAC [(parse_term "x:nadd"); (parse_term "y:nadd")];
    vMAP_EVERY vEXISTS_TAC [(parse_term "x':nadd"); (parse_term "y':nadd")] ---->
    vONCE_REWRITE_TAC[vNADD_EQ_SYM]] ---->
  vASM_REWRITE_TAC[]);;

let vNADD_LE_REFL = try Cache.lookup_thm "NADD_LE_REFL" with _ ->  prove
 ((parse_term "!x. x <<= x"),
  vREWRITE_TAC[nadd_le; vLE_ADD]);;

let vNADD_LE_TRANS = try Cache.lookup_thm "NADD_LE_TRANS" with _ ->  prove
 ((parse_term "!x y z. x <<= y /\\ y <<= z ==> x <<= z"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_le] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "B1:num")) vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "B2:num")) ---->
  vEXISTS_TAC (parse_term "B2 + B1") ----> vGEN_TAC ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vLE_IMP) ---->
  vASM_REWRITE_TAC[vADD_ASSOC; vLE_ADD_RCANCEL]);;

let vNADD_LE_ANTISYM = try Cache.lookup_thm "NADD_LE_ANTISYM" with _ ->  prove
 ((parse_term "!x y. x <<= y /\\ y <<= x <=> (x === y)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_le; nadd_eq; vDIST_LE_CASES] ---->
  vEQ_TAC ++-->
   [vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "B1:num"))
      (vX_CHOOSE_TAC (parse_term "B2:num"))) ---->
    vEXISTS_TAC (parse_term "B1 + B2") ----> vGEN_TAC ----> vCONJ_TAC ---->
    vFIRST_ASSUM(vMATCH_MP_TAC -| vLE_IMP) ---->
    vASM_REWRITE_TAC[vADD_ASSOC; vLE_ADD_RCANCEL; vLE_ADD; vLE_ADDR];
    vDISCH_THEN(vX_CHOOSE_TAC (parse_term "B:num")) ---->
    vCONJ_TAC ----> vEXISTS_TAC (parse_term "B:num") ----> vASM_REWRITE_TAC[]]);;

let vNADD_LE_TOTAL_LEMMA = try Cache.lookup_thm "NADD_LE_TOTAL_LEMMA" with _ ->  prove
 ((parse_term "!x y. ~(x <<= y) ==> !B. ?n. ~(n = 0) /\\ fn y n + B < fn x n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_le; vNOT_FORALL_THM; vNOT_EXISTS_THM] ---->
  vREWRITE_TAC[vNOT_LE] ----> vDISCH_TAC ----> vGEN_TAC ---->
  vPOP_ASSUM(vX_CHOOSE_TAC (parse_term "n:num") -| vSPEC (parse_term "B + fn x 0")) ---->
  vEXISTS_TAC (parse_term "n:num") ----> vPOP_ASSUM vMP_TAC ---->
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vNOT_LT; vADD_ASSOC; vLE_ADDR] ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vNOT_LT] ---->
  vDISCH_THEN(vMATCH_MP_TAC -| vLE_IMP) ----> vREWRITE_TAC[vADD_ASSOC; vLE_ADD]);;

let vNADD_LE_TOTAL = try Cache.lookup_thm "NADD_LE_TOTAL" with _ ->  prove
 ((parse_term "!x y. x <<= y \\/ y <<= x"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vI [vTAUT (parse_term "a <=> ~ ~ a")] ---->
  vX_CHOOSE_TAC (parse_term "B1:num") (vSPEC (parse_term "x:nadd") vNADD_CAUCHY) ---->
  vX_CHOOSE_TAC (parse_term "B2:num") (vSPEC (parse_term "y:nadd") vNADD_CAUCHY) ---->
  vPURE_ONCE_REWRITE_TAC[vDE_MORGAN_THM] ---->
  vDISCH_THEN(vMP_TAC -| end_itlist vCONJ -|
    map (vMATCH_MP vNADD_LE_TOTAL_LEMMA) -| vCONJUNCTS) ---->
  vREWRITE_TAC[vAND_FORALL_THM] ----> vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "B1 + B2")) ---->
  vREWRITE_TAC[vRIGHT_AND_EXISTS_THM] ----> vREWRITE_TAC[vLEFT_AND_EXISTS_THM] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "m:num") (vX_CHOOSE_THEN (parse_term "n:num") vMP_TAC)) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP
    (vITAUT (parse_term "(~a /\\ b) /\\ (~c /\\ d) ==> ~(c \\/ ~b) /\\ ~(a \\/ ~d)"))) ---->
  vREWRITE_TAC[vNOT_LT; vGSYM vLE_MULT_LCANCEL] ----> vREWRITE_TAC[vNOT_LE] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vLT_ADD2) ----> vREWRITE_TAC[vNOT_LT] ---->
  vREWRITE_TAC[vLEFT_ADD_DISTRIB] ---->
  vONCE_REWRITE_TAC[vAC vADD_AC
    (parse_term "(a + b + c) + (d + e + f) = (d + b + e) + (a + c + f)")] ---->
  vMATCH_MP_TAC vLE_ADD2 ----> vREWRITE_TAC[vGSYM vRIGHT_ADD_DISTRIB] ---->
  vCONJ_TAC ----> vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vMULT_SYM] ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vDIST_LE_CASES]) ----> vASM_REWRITE_TAC[]);;

let vNADD_ARCH = try Cache.lookup_thm "NADD_ARCH" with _ ->  prove
 ((parse_term "!x. ?n. x <<= &n"),
  vREWRITE_TAC[nadd_le; vNADD_OF_NUM; vNADD_BOUND]);;

let vNADD_OF_NUM_LE = try Cache.lookup_thm "NADD_OF_NUM_LE" with _ ->  prove
 ((parse_term "!m n. (&m <<= &n) <=> m <= n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_le; vNADD_OF_NUM] ---->
  vREWRITE_TAC[vBOUNDS_LINEAR]);;

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)

override_interface ("++",(parse_term "nadd_add:nadd->nadd->nadd"));;

let nadd_add = new_definition
  (parse_term "x ++ y = afn(\\n. fn x n + fn y n)");;

let vNADD_ADD = try Cache.lookup_thm "NADD_ADD" with _ ->  prove
 ((parse_term "!x y. fn(x ++ y) = \\n. fn x n + fn y n"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[nadd_add; vGSYM nadd_rep; is_nadd] ---->
  vX_CHOOSE_TAC (parse_term "B1:num") (vSPEC (parse_term "x:nadd") vNADD_CAUCHY) ---->
  vX_CHOOSE_TAC (parse_term "B2:num") (vSPEC (parse_term "y:nadd") vNADD_CAUCHY) ---->
  vEXISTS_TAC (parse_term "B1 + B2") ----> vMAP_EVERY vX_GEN_TAC [(parse_term "m:num"); (parse_term "n:num")] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vLEFT_ADD_DISTRIB] ---->
  vMATCH_MP_TAC (vLE_IMP vDIST_ADD2) ----> vREWRITE_TAC[vRIGHT_ADD_DISTRIB] ---->
  vMATCH_MP_TAC vLE_ADD2 ----> vASM_REWRITE_TAC[]);;

let vNADD_ADD_WELLDEF = try Cache.lookup_thm "NADD_ADD_WELLDEF" with _ ->  prove
 ((parse_term "!x x' y y'. x === x' /\\ y === y' ==> (x ++ y === x' ++ y')"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_eq; vNADD_ADD] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2
    (vX_CHOOSE_TAC (parse_term "B1:num")) (vX_CHOOSE_TAC (parse_term "B2:num"))) ---->
  vEXISTS_TAC (parse_term "B1 + B2") ----> vX_GEN_TAC (parse_term "n:num") ---->
  vMATCH_MP_TAC (vLE_IMP vDIST_ADD2) ---->
  vMATCH_MP_TAC vLE_ADD2 ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic properties of addition.                                             *)
(* ------------------------------------------------------------------------- *)

let vNADD_ADD_SYM = try Cache.lookup_thm "NADD_ADD_SYM" with _ ->  prove
 ((parse_term "!x y. (x ++ y) === (y ++ x)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_add] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vADD_SYM] ---->
  vREWRITE_TAC[vNADD_EQ_REFL]);;

let vNADD_ADD_ASSOC = try Cache.lookup_thm "NADD_ADD_ASSOC" with _ ->  prove
 ((parse_term "!x y z. (x ++ (y ++ z)) === ((x ++ y) ++ z)"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[nadd_add] ---->
  vREWRITE_TAC[vNADD_ADD; vADD_ASSOC; vNADD_EQ_REFL]);;

let vNADD_ADD_LID = try Cache.lookup_thm "NADD_ADD_LID" with _ ->  prove
 ((parse_term "!x. (&0 ++ x) === x"),
  vGEN_TAC ----> vREWRITE_TAC[nadd_eq; vNADD_ADD; vNADD_OF_NUM] ---->
  vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vDIST_REFL; vLE_0]);;

let vNADD_ADD_LCANCEL = try Cache.lookup_thm "NADD_ADD_LCANCEL" with _ ->  prove
 ((parse_term "!x y z. (x ++ y) === (x ++ z) ==> y === z"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_eq; vNADD_ADD; vDIST_LADD]);;

let vNADD_LE_ADD = try Cache.lookup_thm "NADD_LE_ADD" with _ ->  prove
 ((parse_term "!x y. x <<= (x ++ y)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_le; vNADD_ADD] ---->
  vEXISTS_TAC (parse_term "0") ----> vREWRITE_TAC[vADD_CLAUSES; vLE_ADD]);;

let vNADD_LE_EXISTS = try Cache.lookup_thm "NADD_LE_EXISTS" with _ ->  prove
 ((parse_term "!x y. x <<= y ==> ?d. y === x ++ d"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_le] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "B:num") vMP_TAC) ---->
  vREWRITE_TAC[vLE_EXISTS; vSKOLEM_THM] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:num->num") (vASSUME_TAC -| vGSYM)) ---->
  vEXISTS_TAC (parse_term "afn d") ----> vREWRITE_TAC[nadd_eq; vNADD_ADD] ---->
  vEXISTS_TAC (parse_term "B:num") ----> vX_GEN_TAC (parse_term "n:num") ---->
  vSUBGOAL_THEN (parse_term "fn(afn d) = d") vSUBST1_TAC ++-->
   [vREWRITE_TAC[vGSYM nadd_rep; is_nadd] ---->
    vX_CHOOSE_TAC (parse_term "B1:num") (vSPEC (parse_term "x:nadd") vNADD_CAUCHY) ---->
    vX_CHOOSE_TAC (parse_term "B2:num") (vSPEC (parse_term "y:nadd") vNADD_CAUCHY) ---->
    vEXISTS_TAC (parse_term "B1 + (B2 + B)") ----> vREPEAT vGEN_TAC ---->
    vMATCH_MP_TAC(vLE_IMP vDIST_ADD2_REV) ---->
    vMAP_EVERY vEXISTS_TAC [(parse_term "m * fn x n"); (parse_term "n * fn x m")] ---->
    vONCE_REWRITE_TAC[vRIGHT_ADD_DISTRIB] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vADD_SYM] ---->
    vMATCH_MP_TAC vLE_ADD2 ----> vASM_REWRITE_TAC[] ---->
    vONCE_REWRITE_TAC[vADD_SYM] ---->
    vASM_REWRITE_TAC[vGSYM vLEFT_ADD_DISTRIB] ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vLEFT_ADD_DISTRIB] ---->
    vMATCH_MP_TAC(vLE_IMP vDIST_ADD2) ----> vREWRITE_TAC[vRIGHT_ADD_DISTRIB] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vADD_SYM] ----> vMATCH_MP_TAC vLE_ADD2 ---->
    vONCE_REWRITE_TAC[vADD_SYM] ----> vASM_REWRITE_TAC[] ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vMULT_SYM] ---->
    vREWRITE_TAC[vGSYM vDIST_LMUL; vDIST_ADDBOUND; vLE_MULT_LCANCEL];
    vASM_REWRITE_TAC[vDIST_RADD_0; vLE_REFL]]);;

let vNADD_OF_NUM_ADD = try Cache.lookup_thm "NADD_OF_NUM_ADD" with _ ->  prove
 ((parse_term "!m n. &m ++ &n === &(m + n)"),
  vREWRITE_TAC[nadd_eq; vNADD_OF_NUM; vNADD_ADD] ---->
  vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vDIST_REFL; vLE_0]);;

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)

override_interface ("**",(parse_term "nadd_mul:nadd->nadd->nadd"));;

let nadd_mul = new_definition
  (parse_term "x ** y = afn(\\n. fn x (fn y n))");;

let vNADD_MUL = try Cache.lookup_thm "NADD_MUL" with _ ->  prove
 ((parse_term "!x y. fn(x ** y) = \\n. fn x (fn y n)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[nadd_mul; vGSYM nadd_rep; is_nadd] ---->
  vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "y:nadd") vNADD_CAUCHY) ---->
  vX_CHOOSE_TAC (parse_term "C:num") (vSPEC (parse_term "x:nadd") vNADD_DIST) ---->
  vX_CHOOSE_TAC (parse_term "D:num") (vSPEC (parse_term "x:nadd") vNADD_MULTIPLICATIVE) ---->
  vMATCH_MP_TAC vBOUNDS_NOTZERO ---->
  vREWRITE_TAC[vMULT_CLAUSES; vDIST_REFL] ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "D + C * B"); (parse_term "D + D")] ---->
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
  vEXISTS_TAC (parse_term "(D * m + D) + (D * n + D) + C * B * (m + n)") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC (vLE_IMP vDIST_TRIANGLE) ---->
    vEXISTS_TAC (parse_term "fn x (m * fn y n)") ---->
    vMATCH_MP_TAC vLE_ADD2 ---->
    vONCE_REWRITE_TAC[vDIST_SYM] ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC (vLE_IMP vDIST_TRIANGLE) ---->
    vEXISTS_TAC (parse_term "fn x (n * fn y m)") ---->
    vMATCH_MP_TAC vLE_ADD2 ---->
    vONCE_REWRITE_TAC[vDIST_SYM] ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vLE_TRANS ---->
    vEXISTS_TAC (parse_term "C * dist(m * fn y n,n * fn y m)") ---->
    vASM_REWRITE_TAC[vLE_MULT_LCANCEL];
    vMATCH_MP_TAC vEQ_IMP_LE ---->
    vREWRITE_TAC[vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB; vMULT_ASSOC; vADD_AC]]);;

(* ------------------------------------------------------------------------- *)
(* Properties of multiplication.                                             *)
(* ------------------------------------------------------------------------- *)

let vNADD_MUL_SYM = try Cache.lookup_thm "NADD_MUL_SYM" with _ ->  prove
 ((parse_term "!x y. (x ** y) === (y ** x)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_eq; vNADD_MUL] ---->
  vX_CHOOSE_THEN (parse_term "A1:num") vMP_TAC (vSPECL [(parse_term "x:nadd"); (parse_term "y:nadd")] vNADD_ALTMUL) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "B1:num")) ---->
  vX_CHOOSE_THEN (parse_term "A2:num") vMP_TAC (vSPECL [(parse_term "y:nadd"); (parse_term "x:nadd")] vNADD_ALTMUL) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "B2:num")) ----> vREWRITE_TAC[vBOUNDS_DIVIDED] ---->
  vREWRITE_TAC[vDIST_LMUL] ----> vMAP_EVERY vEXISTS_TAC [(parse_term "A1 + A2"); (parse_term "B1 + B2")] ---->
  vGEN_TAC ----> vREWRITE_TAC[vRIGHT_ADD_DISTRIB] ---->
  vONCE_REWRITE_TAC[vAC vADD_AC (parse_term "(a + b) + (c + d) = (a + c) + (b + d)")] ---->
  vMATCH_MP_TAC (vLE_IMP vDIST_TRIANGLE) ---->
  vEXISTS_TAC (parse_term "fn x n * fn y n") ---->
  vMATCH_MP_TAC vLE_ADD2 ----> vASM_REWRITE_TAC[] ---->
  vONCE_REWRITE_TAC [vDIST_SYM] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| funpow 2 vRAND_CONV) [vMULT_SYM] ---->
  vASM_REWRITE_TAC[]);;

let vNADD_MUL_ASSOC = try Cache.lookup_thm "NADD_MUL_ASSOC" with _ ->  prove
 ((parse_term "!x y z. (x ** (y ** z)) === ((x ** y) ** z)"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[nadd_mul] ---->
  vREWRITE_TAC[vNADD_MUL; vNADD_EQ_REFL]);;

let vNADD_MUL_LID = try Cache.lookup_thm "NADD_MUL_LID" with _ ->  prove
 ((parse_term "!x. (&1 ** x) === x"),
  vREWRITE_TAC[vNADD_OF_NUM; nadd_mul; vMULT_CLAUSES] ---->
  vREWRITE_TAC[nadd_abs; vNADD_EQ_REFL; vETA_AX]);;

let vNADD_LDISTRIB = try Cache.lookup_thm "NADD_LDISTRIB" with _ ->  prove
 ((parse_term "!x y z. x ** (y ++ z) === (x ** y) ++ (x ** z)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_eq] ---->
  vREWRITE_TAC[vNADD_ADD; vNADD_MUL] ---->
  vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "x:nadd") vNADD_ADDITIVE) ---->
  vEXISTS_TAC (parse_term "B:num") ----> vASM_REWRITE_TAC[]);;

let vNADD_MUL_WELLDEF_LEMMA = try Cache.lookup_thm "NADD_MUL_WELLDEF_LEMMA" with _ ->  prove
 ((parse_term "!x y y'. y === y' ==> (x ** y) === (x ** y')"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_eq; vNADD_MUL] ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "B1:num")) ---->
  vX_CHOOSE_TAC (parse_term "B2:num") (vSPEC (parse_term "x:nadd") vNADD_DIST) ---->
  vEXISTS_TAC (parse_term "B2 * B1") ----> vX_GEN_TAC (parse_term "n:num") ---->
  vMATCH_MP_TAC vLE_TRANS ---->
  vEXISTS_TAC (parse_term "B2 * dist(fn y n,fn y' n)") ---->
  vASM_REWRITE_TAC[vLE_MULT_LCANCEL]);;

let vNADD_MUL_WELLDEF = try Cache.lookup_thm "NADD_MUL_WELLDEF" with _ ->  prove
 ((parse_term "!x x' y y'. x === x' /\\ y === y'\n               ==> (x ** y) === (x' ** y')"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ----> vMATCH_MP_TAC vNADD_EQ_TRANS ---->
  vEXISTS_TAC (parse_term "x' ** y") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vNADD_EQ_TRANS ----> vEXISTS_TAC (parse_term "y ** x'") ---->
    vREWRITE_TAC[vNADD_MUL_SYM] ----> vMATCH_MP_TAC vNADD_EQ_TRANS ---->
    vEXISTS_TAC (parse_term "y ** x") ----> vREWRITE_TAC[vNADD_MUL_SYM]; vALL_TAC] ---->
  vMATCH_MP_TAC vNADD_MUL_WELLDEF_LEMMA ----> vASM_REWRITE_TAC[]);;

let vNADD_OF_NUM_MUL = try Cache.lookup_thm "NADD_OF_NUM_MUL" with _ ->  prove
 ((parse_term "!m n. &m ** &n === &(m * n)"),
  vREWRITE_TAC[nadd_eq; vNADD_OF_NUM; vNADD_MUL] ---->
  vREWRITE_TAC[vMULT_ASSOC; vDIST_REFL; vLE_0]);;

(* ------------------------------------------------------------------------- *)
(* A few handy lemmas.                                                       *)
(* ------------------------------------------------------------------------- *)

let vNADD_LE_0 = try Cache.lookup_thm "NADD_LE_0" with _ ->  prove
 ((parse_term "!x. &0 <<= x"),
  vGEN_TAC ---->
  vREWRITE_TAC[nadd_le; vNADD_OF_NUM; vMULT_CLAUSES; vLE_0]);;

let vNADD_EQ_IMP_LE = try Cache.lookup_thm "NADD_EQ_IMP_LE" with _ ->  prove
 ((parse_term "!x y. x === y ==> x <<= y"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[nadd_eq; nadd_le; vDIST_LE_CASES] ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "B:num")) ----> vEXISTS_TAC (parse_term "B:num") ---->
  vASM_REWRITE_TAC[]);;

let vNADD_LE_LMUL = try Cache.lookup_thm "NADD_LE_LMUL" with _ ->  prove
 ((parse_term "!x y z. y <<= z ==> (x ** y) <<= (x ** z)"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "d:nadd") -| vMATCH_MP vNADD_LE_EXISTS) ---->
  vMATCH_MP_TAC vNADD_LE_TRANS ---->
  vEXISTS_TAC (parse_term "x ** y ++ x ** d") ----> vREWRITE_TAC[vNADD_LE_ADD] ---->
  vMATCH_MP_TAC vNADD_EQ_IMP_LE ---->
  vMATCH_MP_TAC vNADD_EQ_TRANS ---->
  vEXISTS_TAC (parse_term "x ** (y ++ d)") ---->
  vONCE_REWRITE_TAC[vNADD_EQ_SYM] ---->
  vREWRITE_TAC[vNADD_LDISTRIB] ---->
  vMATCH_MP_TAC vNADD_MUL_WELLDEF ---->
  vASM_REWRITE_TAC[vNADD_EQ_REFL]);;

let vNADD_LE_RMUL = try Cache.lookup_thm "NADD_LE_RMUL" with _ ->  prove
 ((parse_term "!x y z. x <<= y ==> (x ** z) <<= (y ** z)"),
  vMESON_TAC[vNADD_LE_LMUL; vNADD_LE_WELLDEF; vNADD_MUL_SYM]);;

let vNADD_LE_RADD = try Cache.lookup_thm "NADD_LE_RADD" with _ ->  prove
 ((parse_term "!x y z. x ++ z <<= y ++ z <=> x <<= y"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_le; vNADD_ADD] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| funpow 2 vBINDER_CONV -| vRAND_CONV)
    [vADD_SYM] ---->
  vREWRITE_TAC[vADD_ASSOC; vLE_ADD_RCANCEL] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| funpow 2 vBINDER_CONV -| vRAND_CONV)
    [vADD_SYM] ----> vREFL_TAC);;

let vNADD_LE_LADD = try Cache.lookup_thm "NADD_LE_LADD" with _ ->  prove
 ((parse_term "!x y z. x ++ y <<= x ++ z <=> y <<= z"),
  vMESON_TAC[vNADD_LE_RADD; vNADD_ADD_SYM; vNADD_LE_WELLDEF]);;

let vNADD_RDISTRIB = try Cache.lookup_thm "NADD_RDISTRIB" with _ ->  prove
 ((parse_term "!x y z. (x ++ y) ** z === x ** z ++ y ** z"),
  vMESON_TAC[vNADD_LDISTRIB; vNADD_MUL_SYM; vNADD_ADD_WELLDEF;
    vNADD_EQ_TRANS; vNADD_EQ_REFL; vNADD_EQ_SYM]);;

(* ------------------------------------------------------------------------- *)
(* The Archimedean property in a more useful form.                           *)
(* ------------------------------------------------------------------------- *)

let vNADD_ARCH_MULT = try Cache.lookup_thm "NADD_ARCH_MULT" with _ ->  prove
 ((parse_term "!x k. ~(x === &0) ==> ?N. &k <<= &N ** x"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nadd_eq; nadd_le; vNOT_EXISTS_THM] ---->
  vX_CHOOSE_TAC (parse_term "B:num") (vSPEC (parse_term "x:nadd") vNADD_CAUCHY) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "B + k")) ---->
  vREWRITE_TAC[vNOT_FORALL_THM; vNADD_OF_NUM] ---->
  vREWRITE_TAC[vMULT_CLAUSES; vDIST_RZERO; vNOT_LE] ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "N:num")) ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "N:num"); (parse_term "B * N")] ----> vX_GEN_TAC (parse_term "i:num") ---->
  vREWRITE_TAC[vNADD_MUL; vNADD_OF_NUM] ---->
  vMATCH_MP_TAC(vGEN_ALL(fst(vEQ_IMP_RULE(vSPEC_ALL vLE_ADD_RCANCEL)))) ---->
  vEXISTS_TAC (parse_term "B * i") ---->
  vREWRITE_TAC[vGSYM vADD_ASSOC; vGSYM vLEFT_ADD_DISTRIB] ---->
  vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "i * fn x N") ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vDIST_LE_CASES]) ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vGSYM vRIGHT_ADD_DISTRIB] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vMULT_SYM] ---->
  vREWRITE_TAC[vLE_MULT_RCANCEL] ----> vDISJ1_TAC ---->
  vMATCH_MP_TAC vLT_IMP_LE ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
  vFIRST_ASSUM vACCEPT_TAC);;

let vNADD_ARCH_ZERO = try Cache.lookup_thm "NADD_ARCH_ZERO" with _ ->  prove
 ((parse_term "!x k. (!n. &n ** x <<= k) ==> (x === &0)"),
  vREPEAT vGEN_TAC ----> vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_TAC ---->
  vREWRITE_TAC[vNOT_FORALL_THM] ---->
  vX_CHOOSE_TAC (parse_term "p:num") (vSPEC (parse_term "k:nadd") vNADD_ARCH) ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vNADD_ARCH_MULT) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "N:num") -| vSPEC (parse_term "p:num")) ---->
  vEXISTS_TAC (parse_term "N + 1") ----> vDISCH_TAC ----> vUNDISCH_TAC (parse_term "~(x === &0)") ---->
  vREWRITE_TAC[vGSYM vNADD_LE_ANTISYM; vNADD_LE_0] ---->
  vMATCH_MP_TAC(vGEN_ALL(fst(vEQ_IMP_RULE(vSPEC_ALL vNADD_LE_RADD)))) ---->
  vEXISTS_TAC (parse_term "&N ** x") ----> vMATCH_MP_TAC vNADD_LE_TRANS ---->
  vEXISTS_TAC (parse_term "k:nadd") ----> vCONJ_TAC ++-->
   [vSUBGOAL_THEN (parse_term "&(N + 1) ** x === x ++ &N ** x") vMP_TAC ++-->
     [vONCE_REWRITE_TAC[vADD_SYM] ---->
      vMATCH_MP_TAC vNADD_EQ_TRANS ---->
      vEXISTS_TAC (parse_term "&1 ** x ++ &N ** x") ----> vCONJ_TAC ++-->
       [vMATCH_MP_TAC vNADD_EQ_TRANS ---->
        vEXISTS_TAC (parse_term "(&1 ++ &N) ** x") ----> vCONJ_TAC ++-->
         [vMESON_TAC[vNADD_OF_NUM_ADD; vNADD_MUL_WELLDEF; vNADD_EQ_REFL;
            vNADD_EQ_SYM];
          vMESON_TAC[vNADD_RDISTRIB; vNADD_MUL_SYM; vNADD_EQ_SYM; vNADD_EQ_TRANS]];
        vMESON_TAC[vNADD_ADD_WELLDEF; vNADD_EQ_REFL; vNADD_MUL_LID]];
      vASM_MESON_TAC[vNADD_LE_WELLDEF; vNADD_EQ_REFL]];
    vASM_MESON_TAC[vNADD_LE_TRANS; vNADD_LE_WELLDEF; vNADD_EQ_REFL;
      vNADD_ADD_LID]]);;

let vNADD_ARCH_LEMMA = try Cache.lookup_thm "NADD_ARCH_LEMMA" with _ ->  prove
 ((parse_term "!x y z. (!n. &n ** x <<= &n ** y ++ z) ==> x <<= y"),
  vREPEAT vSTRIP_TAC ---->
  vDISJ_CASES_TAC(vSPECL [(parse_term "x:nadd"); (parse_term "y:nadd")] vNADD_LE_TOTAL) ---->
  vASM_REWRITE_TAC[] ---->
  vFIRST_ASSUM(vX_CHOOSE_TAC (parse_term "d:nadd") -| vMATCH_MP vNADD_LE_EXISTS) ---->
  vMATCH_MP_TAC vNADD_EQ_IMP_LE ---->
  vMATCH_MP_TAC vNADD_EQ_TRANS ----> vEXISTS_TAC (parse_term "y ++ d") ---->
  vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vNADD_EQ_TRANS ----> vEXISTS_TAC (parse_term "y ++ &0") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vNADD_ADD_WELLDEF ----> vREWRITE_TAC[vNADD_EQ_REFL] ---->
    vMATCH_MP_TAC vNADD_ARCH_ZERO ----> vEXISTS_TAC (parse_term "z:nadd") ---->
    vASM_MESON_TAC[vNADD_MUL_WELLDEF; vNADD_LE_WELLDEF; vNADD_LDISTRIB;
      vNADD_LE_LADD; vNADD_EQ_REFL];
    vASM_MESON_TAC[vNADD_ADD_LID; vNADD_ADD_WELLDEF; vNADD_EQ_TRANS;
      vNADD_ADD_SYM]]);;

(* ------------------------------------------------------------------------- *)
(* Completeness.                                                             *)
(* ------------------------------------------------------------------------- *)

let vNADD_COMPLETE = try Cache.lookup_thm "NADD_COMPLETE" with _ ->  prove
 ((parse_term "!P. (?x. P x) /\\ (?M. !x. P x ==> x <<= M) ==>\n       ?M. (!x. P x ==> x <<= M) /\\\n           !M'. (!x. P x ==> x <<= M') ==> M <<= M'"),
  vGEN_TAC ----> vDISCH_THEN
    (vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "a:nadd")) (vX_CHOOSE_TAC (parse_term "m:nadd"))) ---->
  vSUBGOAL_THEN
    (parse_term "!n. ?r. (?x. P x /\\ &r <<= &n ** x) /\\\n             !r'. (?x. P x /\\ &r' <<= &n ** x) ==> r' <= r") vMP_TAC ++-->
   [vGEN_TAC ----> vREWRITE_TAC[vGSYM num_MAX] ----> vCONJ_TAC ++-->
     [vMAP_EVERY vEXISTS_TAC [(parse_term "0"); (parse_term "a:nadd")] ----> vASM_REWRITE_TAC[vNADD_LE_0];
      vX_CHOOSE_TAC (parse_term "N:num") (vSPEC (parse_term "m:nadd") vNADD_ARCH) ---->
      vEXISTS_TAC (parse_term "n * N") ----> vX_GEN_TAC (parse_term "p:num") ---->
      vDISCH_THEN(vX_CHOOSE_THEN (parse_term "w:nadd") vSTRIP_ASSUME_TAC) ---->
      vONCE_REWRITE_TAC[vGSYM vNADD_OF_NUM_LE] ---->
      vMATCH_MP_TAC vNADD_LE_TRANS ----> vEXISTS_TAC (parse_term "&n ** w") ---->
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vNADD_LE_TRANS ---->
      vEXISTS_TAC (parse_term "&n ** &N") ----> vCONJ_TAC ++-->
       [vMATCH_MP_TAC vNADD_LE_LMUL ----> vMATCH_MP_TAC vNADD_LE_TRANS ---->
        vEXISTS_TAC (parse_term "m:nadd") ----> vASM_REWRITE_TAC[] ---->
        vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
        vMATCH_MP_TAC vNADD_EQ_IMP_LE ---->
        vMATCH_ACCEPT_TAC vNADD_OF_NUM_MUL]];
    vONCE_REWRITE_TAC[vSKOLEM_THM] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "r:num->num")
     (fun th -> let th1,th2 = vCONJ_PAIR(vSPEC (parse_term "n:num") th) in
                vMAP_EVERY (vMP_TAC -| vGEN (parse_term "n:num")) [th1; th2])) ---->
    vDISCH_THEN(vMP_TAC -| vGEN (parse_term "n:num") -| vSPECL [(parse_term "n:num"); (parse_term "SUC(r(n:num))")]) ---->
    vREWRITE_TAC[vLE_SUC_LT; vLT_REFL; vNOT_EXISTS_THM] ---->
    vDISCH_THEN(vASSUME_TAC -| vGENL [(parse_term "n:num"); (parse_term "x:nadd")] -| vMATCH_MP
     (vITAUT (parse_term "(a \\/ b) /\\ ~(c /\\ b) ==> c ==> a")) -| vCONJ
      (vSPECL [(parse_term "&n ** x"); (parse_term "&(SUC(r(n:num)))")] vNADD_LE_TOTAL) -| vSPEC_ALL) ---->
    vDISCH_TAC] ---->
  vSUBGOAL_THEN (parse_term "!n i. i * r(n) <= n * r(i) + n") vASSUME_TAC ++-->
   [vREPEAT vGEN_TAC ---->
    vFIRST_ASSUM(vX_CHOOSE_THEN (parse_term "x:nadd") vSTRIP_ASSUME_TAC -| vSPEC (parse_term "n:num")) ---->
    vONCE_REWRITE_TAC[vGSYM vNADD_OF_NUM_LE] ---->
    vMATCH_MP_TAC vNADD_LE_TRANS ---->
    vEXISTS_TAC (parse_term "&i ** &n ** x") ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vNADD_LE_TRANS ---->
      vEXISTS_TAC (parse_term "&i ** &(r(n:num))") ----> vCONJ_TAC ++-->
       [vMATCH_MP_TAC vNADD_EQ_IMP_LE ---->
        vONCE_REWRITE_TAC[vNADD_EQ_SYM] ----> vMATCH_ACCEPT_TAC vNADD_OF_NUM_MUL;
        vMATCH_MP_TAC vNADD_LE_LMUL ----> vASM_REWRITE_TAC[]];
      vMATCH_MP_TAC vNADD_LE_TRANS ---->
      vEXISTS_TAC (parse_term "&n ** &(SUC(r(i:num)))") ----> vCONJ_TAC ++-->
       [vMATCH_MP_TAC vNADD_LE_TRANS ----> vEXISTS_TAC (parse_term "&n ** &i ** x") ---->
        vCONJ_TAC ++-->
         [vMATCH_MP_TAC vNADD_EQ_IMP_LE ---->
          vMATCH_MP_TAC vNADD_EQ_TRANS ---->
          vEXISTS_TAC (parse_term "(&i ** &n) ** x") ---->
          vREWRITE_TAC[vNADD_MUL_ASSOC] ---->
          vMATCH_MP_TAC vNADD_EQ_TRANS ---->
          vEXISTS_TAC (parse_term "(&n ** &i) ** x") ---->
          vREWRITE_TAC[vONCE_REWRITE_RULE[vNADD_EQ_SYM] vNADD_MUL_ASSOC] ---->
          vMATCH_MP_TAC vNADD_MUL_WELLDEF ---->
          vREWRITE_TAC[vNADD_MUL_SYM; vNADD_EQ_REFL];
          vMATCH_MP_TAC vNADD_LE_LMUL ---->
          vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]];
        vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vGSYM vMULT_SUC] ---->
        vMATCH_MP_TAC vNADD_EQ_IMP_LE ---->
        vREWRITE_TAC[vNADD_OF_NUM_MUL]]]; vALL_TAC] ---->
  vEXISTS_TAC (parse_term "afn r") ----> vSUBGOAL_THEN (parse_term "fn(afn r) = r") vASSUME_TAC ++-->
   [vREWRITE_TAC[vGSYM nadd_rep] ----> vREWRITE_TAC[is_nadd; vDIST_LE_CASES] ---->
    vEXISTS_TAC (parse_term "1") ----> vREWRITE_TAC[vMULT_CLAUSES] ---->
    vREWRITE_TAC[vFORALL_AND_THM] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vSWAP_FORALL_THM] ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| funpow 2 vBINDER_CONV -|
      funpow 2 vRAND_CONV) [vADD_SYM] ---->
    vREWRITE_TAC[] ----> vMAP_EVERY vX_GEN_TAC [(parse_term "i:num"); (parse_term "n:num")] ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "n * r(i:num) + n") ---->
    vASM_REWRITE_TAC[vADD_ASSOC; vLE_ADD]; vALL_TAC] ---->
  vCONJ_TAC ++-->
   [vX_GEN_TAC (parse_term "x:nadd") ----> vDISCH_TAC ---->
    vMATCH_MP_TAC vNADD_ARCH_LEMMA ---->
    vEXISTS_TAC (parse_term "&2") ----> vX_GEN_TAC (parse_term "n:num") ---->
    vMATCH_MP_TAC vNADD_LE_TRANS ---->
    vEXISTS_TAC (parse_term "&(SUC(r(n:num)))") ----> vCONJ_TAC ++-->
     [vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
      vASM_REWRITE_TAC[nadd_le; vNADD_ADD; vNADD_MUL; vNADD_OF_NUM] ---->
      vONCE_REWRITE_TAC[vADD_SYM] ---->
      vREWRITE_TAC[vADD1; vRIGHT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vMULT_2; vMULT_CLAUSES; vADD_ASSOC; vLE_ADD_RCANCEL] ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
      vONCE_REWRITE_TAC[vBOUNDS_IGNORE] ---->
      vMAP_EVERY vEXISTS_TAC [(parse_term "0"); (parse_term "n:num")] ---->
      vX_GEN_TAC (parse_term "i:num") ----> vDISCH_TAC ---->
      vGEN_REWRITE_TAC vLAND_CONV [vMULT_SYM] ---->
      vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "n * r(i:num) + n") ---->
      vASM_REWRITE_TAC[vLE_ADD_LCANCEL; vADD_CLAUSES]];
    vX_GEN_TAC (parse_term "z:nadd") ----> vDISCH_TAC ---->
    vMATCH_MP_TAC vNADD_ARCH_LEMMA ----> vEXISTS_TAC (parse_term "&1") ---->
    vX_GEN_TAC (parse_term "n:num") ----> vMATCH_MP_TAC vNADD_LE_TRANS ---->
    vEXISTS_TAC (parse_term "&(r(n:num)) ++ &1") ----> vCONJ_TAC ++-->
     [vASM_REWRITE_TAC[nadd_le; vNADD_ADD; vNADD_MUL; vNADD_OF_NUM] ---->
      vEXISTS_TAC (parse_term "0") ----> vREWRITE_TAC[vADD_CLAUSES; vMULT_CLAUSES] ---->
      vGEN_TAC ----> vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vMULT_SYM] ---->
      vASM_REWRITE_TAC[];
      vREWRITE_TAC[vNADD_LE_RADD] ---->
      vFIRST_ASSUM(vX_CHOOSE_THEN (parse_term "x:nadd") vMP_TAC -| vSPEC (parse_term "n:num")) ---->
      vDISCH_THEN vSTRIP_ASSUME_TAC ---->
      vMATCH_MP_TAC vNADD_LE_TRANS ----> vEXISTS_TAC (parse_term "&n ** x") ---->
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vNADD_LE_LMUL ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* A bit more on nearly-multiplicative functions.                            *)
(* ------------------------------------------------------------------------- *)

let vNADD_UBOUND = try Cache.lookup_thm "NADD_UBOUND" with _ ->  prove
 ((parse_term "!x. ?B N. !n. N <= n ==> fn x n <= B * n"),
  vGEN_TAC ----> vX_CHOOSE_THEN (parse_term "A1:num")
    (vX_CHOOSE_TAC (parse_term "A2:num")) (vSPEC (parse_term "x:nadd") vNADD_BOUND) ---->
  vEXISTS_TAC (parse_term "A1 + A2") ----> vEXISTS_TAC (parse_term "1") ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
  vEXISTS_TAC (parse_term "A1 * n + A2") ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vLE_ADD_LCANCEL] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM(el 3 (vCONJUNCTS vMULT_CLAUSES))] ---->
  vASM_REWRITE_TAC[vLE_MULT_LCANCEL]);;

let vNADD_NONZERO = try Cache.lookup_thm "NADD_NONZERO" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> ?N. !n. N <= n ==> ~(fn x n = 0)"),
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vNADD_ARCH_MULT) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "1")) ---->
  vREWRITE_TAC[nadd_le; vNADD_MUL; vNADD_OF_NUM; vMULT_CLAUSES] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "A1:num") (vX_CHOOSE_TAC (parse_term "A2:num"))) ---->
  vEXISTS_TAC (parse_term "A2 + 1") ----> vX_GEN_TAC (parse_term "n:num") ----> vREPEAT vDISCH_TAC ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
  vREWRITE_TAC[vNOT_FORALL_THM; vNOT_LE; vGSYM vLE_SUC_LT; vADD1] ---->
  vEXISTS_TAC (parse_term "n:num") ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES]);;

let vNADD_LBOUND = try Cache.lookup_thm "NADD_LBOUND" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> ?A N. !n. N <= n ==> n <= A * fn x n"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vX_CHOOSE_TAC (parse_term "N:num") -| vMATCH_MP vNADD_NONZERO) ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vNADD_ARCH_MULT) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "1")) ---->
  vREWRITE_TAC[nadd_le; vNADD_MUL; vNADD_OF_NUM; vMULT_CLAUSES] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "A1:num") (vX_CHOOSE_TAC (parse_term "A2:num"))) ---->
  vEXISTS_TAC (parse_term "A1 + A2") ----> vEXISTS_TAC (parse_term "N:num") ----> vGEN_TAC ---->
  vDISCH_THEN(vANTE_RES_THEN vASSUME_TAC) ---->
  vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "A1 * fn x n + A2") ---->
  vASM_REWRITE_TAC[vRIGHT_ADD_DISTRIB; vLE_ADD_LCANCEL] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM(el 3 (vCONJUNCTS vMULT_CLAUSES))] ---->
  vREWRITE_TAC[vLE_MULT_LCANCEL] ----> vDISJ2_TAC ---->
  vREWRITE_TAC[vGSYM(vREWRITE_CONV[vARITH_SUC] (parse_term "SUC 0"))] ---->
  vASM_REWRITE_TAC[vGSYM vNOT_LT; vLT]);;

(* ------------------------------------------------------------------------- *)
(* Auxiliary function for the multiplicative inverse.                        *)
(* ------------------------------------------------------------------------- *)

let nadd_rinv = new_definition
 (parse_term "nadd_rinv(x) = \\n. (n * n) DIV (fn x n)");;

let vNADD_MUL_LINV_LEMMA0 = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA0" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> ?A B. !n. nadd_rinv x n <= A * n + B"),
  vGEN_TAC ----> vDISCH_TAC ----> vONCE_REWRITE_TAC[vBOUNDS_IGNORE] ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vNADD_LBOUND) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "A:num") (vX_CHOOSE_TAC (parse_term "N:num"))) ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "A:num"); (parse_term "0"); (parse_term "SUC N")] ---->
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vADD_CLAUSES] ---->
  vMP_TAC(vSPECL [(parse_term "nadd_rinv x n"); (parse_term "A * n"); (parse_term "n:num")] vLE_MULT_RCANCEL) ---->
  vUNDISCH_TAC (parse_term "SUC N <= n") ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vLE; vNOT_SUC] ----> vDISCH_TAC ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "nadd_rinv x n * A * fn x n") ---->
  vASM_REWRITE_TAC[vLE_MULT_LCANCEL] ----> vCONJ_TAC ++-->
   [vDISJ2_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
    vEXISTS_TAC (parse_term "SUC N") ----> vASM_REWRITE_TAC[vLE; vLE_REFL];
    vGEN_REWRITE_TAC vLAND_CONV [vMULT_SYM] ---->
    vREWRITE_TAC[vGSYM vMULT_ASSOC; vLE_MULT_LCANCEL] ---->
    vDISJ2_TAC ----> vASM_CASES_TAC (parse_term "fn x n = 0") ---->
    vASM_REWRITE_TAC[vMULT_CLAUSES; vLE_0; nadd_rinv] ---->
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vDIVISION) ---->
    vDISCH_THEN(fun t -> vGEN_REWRITE_TAC vRAND_CONV [vCONJUNCT1(vSPEC_ALL t)]) ---->
    vGEN_REWRITE_TAC vLAND_CONV [vMULT_SYM] ----> vREWRITE_TAC[vLE_ADD]]);;

let vNADD_MUL_LINV_LEMMA1 = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA1" with _ ->  prove
 ((parse_term "!x n. ~(fn x n = 0) ==> dist(fn x n * nadd_rinv(x) n, n * n) <= fn x n"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIVISION) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vSUBST1_TAC vASSUME_TAC -| vSPEC (parse_term "n * n")) ---->
  vREWRITE_TAC[nadd_rinv] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV -| vLAND_CONV) [vMULT_SYM] ---->
  vREWRITE_TAC[vDIST_RADD_0] ----> vMATCH_MP_TAC vLT_IMP_LE ---->
  vFIRST_ASSUM vMATCH_ACCEPT_TAC);;

let vNADD_MUL_LINV_LEMMA2 = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA2" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> ?N. !n. N <= n ==>\n         dist(fn x n * nadd_rinv(x) n, n * n) <= fn x n"),
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vNADD_NONZERO) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "N:num")) ----> vEXISTS_TAC (parse_term "N:num") ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vNADD_MUL_LINV_LEMMA1 ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]);;

let vNADD_MUL_LINV_LEMMA3 = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA3" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> ?N. !m n. N <= n ==>\n        dist(m * fn x m * fn x n * nadd_rinv(x) n,\n             m * fn x m * n * n) <= m * fn x m * fn x n"),
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vNADD_MUL_LINV_LEMMA2) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "N:num")) ----> vEXISTS_TAC (parse_term "N:num") ---->
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vDIST_LMUL; vMULT_ASSOC] ---->
  vREWRITE_TAC[vLE_MULT_LCANCEL] ----> vDISJ2_TAC ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]);;

let vNADD_MUL_LINV_LEMMA4 = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA4" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> ?N. !m n. N <= m /\\ N <= n ==>\n        (fn x m * fn x n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=\n          (m * n) * dist(m * fn x n,n * fn x m) + (fn x m * fn x n) * (m + n)"),
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vNADD_MUL_LINV_LEMMA3) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "N:num")) ----> vEXISTS_TAC (parse_term "N:num") ---->
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vDIST_LMUL; vLEFT_ADD_DISTRIB] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vDIST_SYM] ---->
  vMATCH_MP_TAC vDIST_TRIANGLES_LE ----> vCONJ_TAC ++-->
   [vANTE_RES_THEN(vMP_TAC -| vSPEC (parse_term "m:num")) (vASSUME (parse_term "N <= n"));
    vANTE_RES_THEN(vMP_TAC -| vSPEC (parse_term "n:num")) (vASSUME (parse_term "N <= m"))] ---->
  vMATCH_MP_TAC vEQ_IMP ----> vREWRITE_TAC[vMULT_AC]);;

let vNADD_MUL_LINV_LEMMA5 = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA5" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> ?B N. !m n. N <= m /\\ N <= n ==>\n        (fn x m * fn x n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=\n        B * (m * n) * (m + n)"),
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vNADD_MUL_LINV_LEMMA4) ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "N1:num")) ---->
  vX_CHOOSE_TAC (parse_term "B1:num") (vSPEC (parse_term "x:nadd") vNADD_CAUCHY) ---->
  vX_CHOOSE_THEN (parse_term "B2:num") (vX_CHOOSE_TAC (parse_term "N2:num"))
    (vSPEC (parse_term "x:nadd") vNADD_UBOUND) ---->
  vEXISTS_TAC (parse_term "B1 + B2 * B2") ----> vEXISTS_TAC (parse_term "N1 + N2") ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
  vEXISTS_TAC (parse_term "(m * n) * dist(m * fn x n,n * fn x m) +\n              (fn x m * fn x n) * (m + n)") ---->
  vCONJ_TAC ++-->
   [vFIRST_ASSUM vMATCH_MP_TAC ----> vCONJ_TAC ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "N1 + N2") ---->
    vASM_REWRITE_TAC[vLE_ADD; vLE_ADDR];
    vREWRITE_TAC[vRIGHT_ADD_DISTRIB] ----> vMATCH_MP_TAC vLE_ADD2] ---->
  vCONJ_TAC ++-->
   [vGEN_REWRITE_TAC vRAND_CONV [vMULT_SYM] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vMULT_ASSOC] ---->
    vGEN_REWRITE_TAC (funpow 2 vRAND_CONV) [vMULT_SYM] ---->
    vASM_REWRITE_TAC[vLE_MULT_LCANCEL];
    vONCE_REWRITE_TAC[vAC vMULT_AC
      (parse_term "(a * b) * (c * d) * e = ((a * c) * (b * d)) * e")] ---->
    vREWRITE_TAC[vLE_MULT_RCANCEL] ----> vDISJ1_TAC ---->
    vMATCH_MP_TAC vLE_MULT2 ----> vCONJ_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "N1 + N2") ---->
    vASM_REWRITE_TAC[vLE_ADD; vLE_ADDR]]);;

let vNADD_MUL_LINV_LEMMA6 = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA6" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> ?B N. !m n. N <= m /\\ N <= n ==>\n        (m * n) * dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <=\n        B * (m * n) * (m + n)"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vNADD_MUL_LINV_LEMMA5) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "B1:num") (vX_CHOOSE_TAC (parse_term "N1:num"))) ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vNADD_LBOUND) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "B2:num") (vX_CHOOSE_TAC (parse_term "N2:num"))) ---->
  vEXISTS_TAC (parse_term "B1 * B2 * B2") ----> vEXISTS_TAC (parse_term "N1 + N2") ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
  vEXISTS_TAC (parse_term "(B2 * B2) * (fn x m * fn x n) *\n              dist (m * nadd_rinv x n,n * nadd_rinv x m)") ---->
  vCONJ_TAC ++-->
   [vREWRITE_TAC[vMULT_ASSOC; vLE_MULT_RCANCEL] ----> vDISJ1_TAC ---->
    vONCE_REWRITE_TAC[vAC vMULT_AC (parse_term "((a * b) * c) * d = (a * c) * (b * d)")] ---->
    vMATCH_MP_TAC vLE_MULT2 ----> vCONJ_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC;
    vONCE_REWRITE_TAC[vAC vMULT_AC
      (parse_term "(a * b * c) * (d * e) * f = (b * c) * (a * (d * e) * f)")] ---->
    vREWRITE_TAC[vLE_MULT_LCANCEL] ----> vDISJ2_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vCONJ_TAC] ---->
  vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "N1 + N2") ---->
  vASM_REWRITE_TAC[vLE_ADD; vLE_ADDR]);;

let vNADD_MUL_LINV_LEMMA7 = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA7" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> ?B N. !m n. N <= m /\\ N <= n ==>\n        dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= B * (m + n)"),
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vNADD_MUL_LINV_LEMMA6) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "B:num") (vX_CHOOSE_TAC (parse_term "N:num"))) ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "B:num"); (parse_term "N + 1")] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "m:num"); (parse_term "n:num")] ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "N <= m /\\ N <= n") vMP_TAC ++-->
   [vCONJ_TAC ----> vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "N + 1") ---->
    vASM_REWRITE_TAC[vLE_ADD];
    vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
    vONCE_REWRITE_TAC[vAC vMULT_AC (parse_term "a * b * c = b * a * c")] ---->
    vREWRITE_TAC[vLE_MULT_LCANCEL] ---->
    vDISCH_THEN(vDISJ_CASES_THEN2 vMP_TAC vACCEPT_TAC) ---->
    vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_THEN(vK vALL_TAC) ---->
    vONCE_REWRITE_TAC[vGSYM(vCONJUNCT1 vLE)] ---->
    vREWRITE_TAC[vNOT_LE; vGSYM vLE_SUC_LT] ---->
    vREWRITE_TAC[vEQT_ELIM(vREWRITE_CONV[vARITH] (parse_term "SUC 0 = 1 * 1"))] ---->
    vMATCH_MP_TAC vLE_MULT2 ----> vCONJ_TAC ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "N + 1") ---->
    vASM_REWRITE_TAC[vLE_ADDR]]);;

let vNADD_MUL_LINV_LEMMA7a = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA7a" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> !N. ?A B. !m n. m <= N ==>\n        dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= A * n + B"),
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vNADD_MUL_LINV_LEMMA0) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "A0:num") (vX_CHOOSE_TAC (parse_term "B0:num"))) ---->
  vINDUCT_TAC ++-->
   [vMAP_EVERY vEXISTS_TAC [(parse_term "nadd_rinv x 0"); (parse_term "0")] ---->
    vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLE] ----> vDISCH_THEN vSUBST1_TAC ---->
    vREWRITE_TAC[vMULT_CLAUSES; vDIST_LZERO; vADD_CLAUSES] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vMULT_SYM] ----> vMATCH_ACCEPT_TAC vLE_REFL;
    vFIRST_ASSUM(vX_CHOOSE_THEN (parse_term "A:num") (vX_CHOOSE_TAC (parse_term "B:num"))) ---->
    vEXISTS_TAC (parse_term "A + (nadd_rinv(x)(SUC N) + SUC N * A0)") ---->
    vEXISTS_TAC (parse_term "SUC N * B0 + B") ---->
    vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLE] ---->
    vDISCH_THEN(vDISJ_CASES_THEN2 vSUBST1_TAC vASSUME_TAC) ++-->
     [vMATCH_MP_TAC vLE_TRANS ---->
      vEXISTS_TAC (parse_term "SUC N * nadd_rinv x n + n * nadd_rinv x (SUC N)") ---->
      vREWRITE_TAC[vDIST_ADDBOUND] ----> vREWRITE_TAC[vRIGHT_ADD_DISTRIB] ---->
      vONCE_REWRITE_TAC[vAC vADD_AC
        (parse_term "(a + b + c) + d + e = (c + d) + (b + a + e)")] ---->
      vMATCH_MP_TAC vLE_ADD2 ----> vCONJ_TAC ++-->
       [vREWRITE_TAC[vGSYM vMULT_ASSOC; vGSYM vLEFT_ADD_DISTRIB] ---->
        vASM_REWRITE_TAC[vLE_MULT_LCANCEL];
        vGEN_REWRITE_TAC vLAND_CONV [vMULT_SYM] ---->
        vMATCH_ACCEPT_TAC vLE_ADD];
      vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "A * n + B") ----> vCONJ_TAC ++-->
       [vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
        vREWRITE_TAC[vADD_ASSOC; vLE_ADD_RCANCEL] ---->
        vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vGSYM vADD_ASSOC; vLE_ADD]]]]);;

let vNADD_MUL_LINV_LEMMA8 = try Cache.lookup_thm "NADD_MUL_LINV_LEMMA8" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==>\n        ?B. !m n. dist(m * nadd_rinv(x) n,n * nadd_rinv(x) m) <= B * (m + n)"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vNADD_MUL_LINV_LEMMA7) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "B0:num") (vX_CHOOSE_TAC (parse_term "N:num"))) ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC (parse_term "N:num") -| vMATCH_MP vNADD_MUL_LINV_LEMMA7a) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "A:num") (vX_CHOOSE_TAC (parse_term "B:num"))) ---->
  vMATCH_MP_TAC vBOUNDS_NOTZERO ----> vREWRITE_TAC[vDIST_REFL] ---->
  vEXISTS_TAC (parse_term "A + B0") ----> vEXISTS_TAC (parse_term "B:num") ----> vREPEAT vGEN_TAC ---->
  vDISJ_CASES_THEN2 vASSUME_TAC vMP_TAC (vSPECL [(parse_term "N:num"); (parse_term "m:num")] vLE_CASES) ++-->
   [vDISJ_CASES_THEN2 vASSUME_TAC vMP_TAC (vSPECL [(parse_term "N:num"); (parse_term "n:num")] vLE_CASES)
    ++-->
     [vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "B0 * (m + n)") ----> vCONJ_TAC ++-->
       [vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
        vGEN_REWRITE_TAC (vRAND_CONV -| funpow 2 vLAND_CONV) [vADD_SYM] ---->
        vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vGSYM vADD_ASSOC; vLE_ADD]];
      vDISCH_THEN(vANTE_RES_THEN vASSUME_TAC) ---->
      vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "A * m + B") ---->
      vONCE_REWRITE_TAC[vDIST_SYM] ---->
      vASM_REWRITE_TAC[vLE_ADD_RCANCEL] ---->
      vREWRITE_TAC[vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB; vGSYM vADD_ASSOC;
        vLE_ADD]];
    vDISCH_THEN(vANTE_RES_THEN vASSUME_TAC) ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "A * n + B") ---->
    vASM_REWRITE_TAC[vLE_ADD_RCANCEL] ---->
    vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vADD_SYM] ---->
    vREWRITE_TAC[vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB; vGSYM vADD_ASSOC;
      vLE_ADD]]);;

(* ------------------------------------------------------------------------- *)
(* Now the multiplicative inverse proper.                                    *)
(* ------------------------------------------------------------------------- *)

let nadd_inv = new_definition
  (parse_term "nadd_inv(x) = if x === &0 then &0 else afn(nadd_rinv x)");;

override_interface ("inv",(parse_term "nadd_inv:nadd->nadd"));;

let vNADD_INV = try Cache.lookup_thm "NADD_INV" with _ ->  prove
 ((parse_term "!x. fn(nadd_inv x) = if x === &0 then (\\n. 0) else nadd_rinv x"),
  vGEN_TAC ----> vREWRITE_TAC[nadd_inv] ---->
  vASM_CASES_TAC (parse_term "x === &0") ----> vASM_REWRITE_TAC[vNADD_OF_NUM; vMULT_CLAUSES] ---->
  vREWRITE_TAC[vGSYM nadd_rep; is_nadd] ---->
  vMATCH_MP_TAC vNADD_MUL_LINV_LEMMA8 ----> vPOP_ASSUM vACCEPT_TAC);;

let vNADD_MUL_LINV = try Cache.lookup_thm "NADD_MUL_LINV" with _ ->  prove
 ((parse_term "!x. ~(x === &0) ==> inv(x) ** x === &1"),
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[nadd_eq; vNADD_MUL] ---->
  vONCE_REWRITE_TAC[vBOUNDS_DIVIDED] ---->
  vX_CHOOSE_THEN (parse_term "A1:num") (vX_CHOOSE_TAC (parse_term "B1:num"))
   (vSPECL [(parse_term "inv(x)"); (parse_term "x:nadd")] vNADD_ALTMUL) ---->
  vREWRITE_TAC[vDIST_LMUL; vNADD_OF_NUM; vMULT_CLAUSES] ---->
  vFIRST_ASSUM(vX_CHOOSE_TAC (parse_term "N:num") -| vMATCH_MP vNADD_MUL_LINV_LEMMA2) ---->
  vX_CHOOSE_THEN (parse_term "A':num") (vX_CHOOSE_TAC (parse_term "B':num"))
    (vSPEC (parse_term "x:nadd") vNADD_BOUND) ---->
  vSUBGOAL_THEN (parse_term "?A2 B2. !n. dist(fn x n * nadd_rinv x n,n * n) <= A2 * n + B2")
  vSTRIP_ASSUME_TAC ++-->
   [vEXISTS_TAC (parse_term "A':num") ----> vONCE_REWRITE_TAC[vBOUNDS_IGNORE] ---->
    vMAP_EVERY vEXISTS_TAC [(parse_term "B':num"); (parse_term "N:num")] ----> vREPEAT vSTRIP_TAC ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "fn x n") ----> vASM_REWRITE_TAC[] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
    vMAP_EVERY vEXISTS_TAC [(parse_term "A1 + A2"); (parse_term "B1 + B2")] ---->
    vGEN_TAC ----> vMATCH_MP_TAC vDIST_TRIANGLE_LE ---->
    vEXISTS_TAC (parse_term "fn (inv x) n * fn x n") ---->
    vREWRITE_TAC[vRIGHT_ADD_DISTRIB] ---->
    vONCE_REWRITE_TAC[vAC vADD_AC (parse_term "(a + b) + c + d = (a + c) + (b + d)")] ---->
    vMATCH_MP_TAC vLE_ADD2 ----> vASM_REWRITE_TAC[] ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV -| vLAND_CONV) [vMULT_SYM] ---->
    vASM_REWRITE_TAC[vNADD_INV]]);;

let vNADD_INV_0 = try Cache.lookup_thm "NADD_INV_0" with _ ->  prove
 ((parse_term "inv(&0) === &0"),
  vREWRITE_TAC[nadd_inv; vNADD_EQ_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Welldefinedness follows from already established principles because if    *)
(* x = y then y' = y' 1 = y' (x' x) = y' (x' y) = (y' y) x' = 1 x' = x'      *)
(* ------------------------------------------------------------------------- *)

let vNADD_INV_WELLDEF = try Cache.lookup_thm "NADD_INV_WELLDEF" with _ ->  prove
 ((parse_term "!x y. x === y ==> inv(x) === inv(y)"),
  let vTAC tm ths =
    vMATCH_MP_TAC vNADD_EQ_TRANS ----> vEXISTS_TAC tm ---->
    vCONJ_TAC ++--> [vALL_TAC; vASM_MESON_TAC ths] in
  vREPEAT vSTRIP_TAC ---->
  vASM_CASES_TAC (parse_term "x === &0") ++-->
   [vSUBGOAL_THEN (parse_term "y === &0") vASSUME_TAC ++-->
     [vASM_MESON_TAC[vNADD_EQ_TRANS; vNADD_EQ_SYM];
      vASM_REWRITE_TAC[nadd_inv; vNADD_EQ_REFL]];
    vSUBGOAL_THEN (parse_term "~(y === &0)") vASSUME_TAC ++-->
     [vASM_MESON_TAC[vNADD_EQ_TRANS; vNADD_EQ_SYM]; vALL_TAC]] ---->
  vTAC (parse_term "inv(y) ** &1")
      [vNADD_MUL_SYM; vNADD_MUL_LID; vNADD_EQ_TRANS] ---->
  vTAC (parse_term "inv(y) ** (inv(x) ** x)")
      [vNADD_MUL_LINV; vNADD_MUL_WELLDEF; vNADD_EQ_REFL] ---->
  vTAC (parse_term "inv(y) ** (inv(x) ** y)")
      [vNADD_MUL_WELLDEF; vNADD_EQ_REFL; vNADD_EQ_SYM] ---->
  vTAC (parse_term "(inv(y) ** y) ** inv(x)")
      [vNADD_MUL_ASSOC; vNADD_MUL_SYM; vNADD_EQ_TRANS;
       vNADD_MUL_WELLDEF; vNADD_EQ_REFL] ---->
  vASM_MESON_TAC[vNADD_MUL_LINV; vNADD_MUL_WELLDEF; vNADD_EQ_REFL;
    vNADD_MUL_LID; vNADD_EQ_TRANS; vNADD_EQ_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Definition of the new type.                                               *)
(* ------------------------------------------------------------------------- *)

let hreal_tybij =
  define_quotient_type "hreal" ("mk_hreal","dest_hreal") (parse_term "(===)");;

do_list overload_interface
 ["+",(parse_term "hreal_add:hreal->hreal->hreal");
  "*",(parse_term "hreal_mul:hreal->hreal->hreal");
  "<=",(parse_term "hreal_le:hreal->hreal->bool")];;

do_list override_interface
 ["&",(parse_term "hreal_of_num:num->hreal");
  "inv",(parse_term "hreal_inv:hreal->hreal")];;

let hreal_of_num,hreal_of_num_th =
  lift_function (snd hreal_tybij) (vNADD_EQ_REFL,vNADD_EQ_TRANS)
  "hreal_of_num" vNADD_OF_NUM_WELLDEF;;

let hreal_add,hreal_add_th =
  lift_function (snd hreal_tybij) (vNADD_EQ_REFL,vNADD_EQ_TRANS)
  "hreal_add" vNADD_ADD_WELLDEF;;

let hreal_mul,hreal_mul_th =
  lift_function (snd hreal_tybij) (vNADD_EQ_REFL,vNADD_EQ_TRANS)
  "hreal_mul" vNADD_MUL_WELLDEF;;

let hreal_le,hreal_le_th =
  lift_function (snd hreal_tybij) (vNADD_EQ_REFL,vNADD_EQ_TRANS)
  "hreal_le" vNADD_LE_WELLDEF;;

let hreal_inv,hreal_inv_th =
  lift_function (snd hreal_tybij) (vNADD_EQ_REFL,vNADD_EQ_TRANS)
  "hreal_inv" vNADD_INV_WELLDEF;;

let vHREAL_COMPLETE =
  let th1 = vASSUME (parse_term "(P:nadd->bool) = (\\x. Q(mk_hreal((===) x)))") in
  let th2 = vBETA_RULE(vAP_THM th1 (parse_term "x:nadd")) in
  let th3 = lift_theorem hreal_tybij
              (vNADD_EQ_REFL,vNADD_EQ_SYM,vNADD_EQ_TRANS)
              [hreal_of_num_th; hreal_add_th; hreal_mul_th; hreal_le_th; th2]
              (vSPEC_ALL vNADD_COMPLETE) in
  let th4 = vMATCH_MP (vDISCH_ALL th3) (vREFL (parse_term "\\x. Q(mk_hreal((===) x)):bool")) in
  vCONV_RULE(vGEN_ALPHA_CONV (parse_term "P:hreal->bool")) (vGEN_ALL th4);;

let [@warning "-8"] [vHREAL_OF_NUM_EQ; vHREAL_OF_NUM_LE; vHREAL_OF_NUM_ADD; vHREAL_OF_NUM_MUL;
     vHREAL_LE_REFL; vHREAL_LE_TRANS; vHREAL_LE_ANTISYM; vHREAL_LE_TOTAL;
     vHREAL_LE_ADD; vHREAL_LE_EXISTS; vHREAL_ARCH; vHREAL_ADD_SYM; vHREAL_ADD_ASSOC;
     vHREAL_ADD_LID; vHREAL_ADD_LCANCEL; vHREAL_MUL_SYM; vHREAL_MUL_ASSOC;
     vHREAL_MUL_LID; vHREAL_ADD_LDISTRIB; vHREAL_MUL_LINV; vHREAL_INV_0] =
  map (lift_theorem hreal_tybij
         (vNADD_EQ_REFL,vNADD_EQ_SYM,vNADD_EQ_TRANS)
             [hreal_of_num_th; hreal_add_th; hreal_mul_th;
              hreal_le_th; hreal_inv_th])
 [vNADD_OF_NUM_EQ; vNADD_OF_NUM_LE; vNADD_OF_NUM_ADD; vNADD_OF_NUM_MUL;
  vNADD_LE_REFL; vNADD_LE_TRANS; vNADD_LE_ANTISYM; vNADD_LE_TOTAL; vNADD_LE_ADD;
  vNADD_LE_EXISTS; vNADD_ARCH; vNADD_ADD_SYM; vNADD_ADD_ASSOC; vNADD_ADD_LID;
  vNADD_ADD_LCANCEL; vNADD_MUL_SYM; vNADD_MUL_ASSOC; vNADD_MUL_LID; vNADD_LDISTRIB;
  vNADD_MUL_LINV; vNADD_INV_0];;

(* ------------------------------------------------------------------------- *)
(* Consequential theorems needed later.                                      *)
(* ------------------------------------------------------------------------- *)

let vHREAL_LE_EXISTS_DEF = try Cache.lookup_thm "HREAL_LE_EXISTS_DEF" with _ ->  prove
 ((parse_term "!m n. m <= n <=> ?d. n = m + d"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vHREAL_LE_EXISTS] ---->
  vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC) ----> vREWRITE_TAC[vHREAL_LE_ADD]);;

let vHREAL_EQ_ADD_LCANCEL = try Cache.lookup_thm "HREAL_EQ_ADD_LCANCEL" with _ ->  prove
 ((parse_term "!m n p. (m + n = m + p) <=> (n = p)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vHREAL_ADD_LCANCEL] ---->
  vDISCH_THEN vSUBST1_TAC ----> vREFL_TAC);;

let vHREAL_EQ_ADD_RCANCEL = try Cache.lookup_thm "HREAL_EQ_ADD_RCANCEL" with _ ->  prove
 ((parse_term "!m n p. (m + p = n + p) <=> (m = n)"),
  vONCE_REWRITE_TAC[vHREAL_ADD_SYM] ----> vREWRITE_TAC[vHREAL_EQ_ADD_LCANCEL]);;

let vHREAL_LE_ADD_LCANCEL = try Cache.lookup_thm "HREAL_LE_ADD_LCANCEL" with _ ->  prove
 ((parse_term "!m n p. (m + n <= m + p) <=> (n <= p)"),
  vREWRITE_TAC[vHREAL_LE_EXISTS_DEF; vGSYM vHREAL_ADD_ASSOC;
    vHREAL_EQ_ADD_LCANCEL]);;

let vHREAL_LE_ADD_RCANCEL = try Cache.lookup_thm "HREAL_LE_ADD_RCANCEL" with _ ->  prove
 ((parse_term "!m n p. (m + p <= n + p) <=> (m <= n)"),
  vONCE_REWRITE_TAC[vHREAL_ADD_SYM] ----> vMATCH_ACCEPT_TAC vHREAL_LE_ADD_LCANCEL);;

let vHREAL_ADD_RID = try Cache.lookup_thm "HREAL_ADD_RID" with _ ->  prove
 ((parse_term "!n. n + &0 = n"),
  vONCE_REWRITE_TAC[vHREAL_ADD_SYM] ----> vMATCH_ACCEPT_TAC vHREAL_ADD_LID);;

let vHREAL_ADD_RDISTRIB = try Cache.lookup_thm "HREAL_ADD_RDISTRIB" with _ ->  prove
 ((parse_term "!m n p. (m + n) * p = m * p + n * p"),
  vONCE_REWRITE_TAC[vHREAL_MUL_SYM] ----> vMATCH_ACCEPT_TAC vHREAL_ADD_LDISTRIB);;

let vHREAL_MUL_LZERO = try Cache.lookup_thm "HREAL_MUL_LZERO" with _ ->  prove
 ((parse_term "!m. &0 * m = &0"),
  vGEN_TAC ----> vMP_TAC(vSPECL [(parse_term "&0"); (parse_term "&1"); (parse_term "m:hreal")] vHREAL_ADD_RDISTRIB) ---->
  vREWRITE_TAC[vHREAL_ADD_LID] ---->
  vGEN_REWRITE_TAC (funpow 2 vLAND_CONV) [vGSYM vHREAL_ADD_LID] ---->
  vREWRITE_TAC[vHREAL_EQ_ADD_RCANCEL] ---->
  vDISCH_THEN(vACCEPT_TAC -| vSYM));;

let vHREAL_MUL_RZERO = try Cache.lookup_thm "HREAL_MUL_RZERO" with _ ->  prove
 ((parse_term "!m. m * &0 = &0"),
  vONCE_REWRITE_TAC[vHREAL_MUL_SYM] ----> vMATCH_ACCEPT_TAC vHREAL_MUL_LZERO);;

let vHREAL_ADD_AC = try Cache.lookup_thm "HREAL_ADD_AC" with _ ->  prove
 ((parse_term "(m + n = n + m) /\\\n   ((m + n) + p = m + (n + p)) /\\\n   (m + (n + p) = n + (m + p))"),
  vREWRITE_TAC[vHREAL_ADD_ASSOC; vEQT_INTRO(vSPEC_ALL vHREAL_ADD_SYM)] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vMATCH_ACCEPT_TAC vHREAL_ADD_SYM);;

let vHREAL_LE_ADD2 = try Cache.lookup_thm "HREAL_LE_ADD2" with _ ->  prove
 ((parse_term "!a b c d. a <= b /\\ c <= d ==> a + c <= b + d"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vHREAL_LE_EXISTS_DEF] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "d1:hreal"))
    (vX_CHOOSE_TAC (parse_term "d2:hreal"))) ---->
  vEXISTS_TAC (parse_term "d1 + d2") ----> vASM_REWRITE_TAC[vHREAL_ADD_AC]);;

let vHREAL_LE_MUL_RCANCEL_IMP = try Cache.lookup_thm "HREAL_LE_MUL_RCANCEL_IMP" with _ ->  prove
 ((parse_term "!a b c. a <= b ==> a * c <= b * c"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vHREAL_LE_EXISTS_DEF] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:hreal") vSUBST1_TAC) ---->
  vEXISTS_TAC (parse_term "d * c") ----> vREWRITE_TAC[vHREAL_ADD_RDISTRIB]);;

(* ------------------------------------------------------------------------- *)
(* Define operations on representatives of signed reals.                     *)
(* ------------------------------------------------------------------------- *)

let treal_of_num = new_definition
  (parse_term "treal_of_num n = (&n, &0)");;

let treal_neg = new_definition
  (parse_term "treal_neg ((x:hreal),(y:hreal)) = (y,x)");;

let treal_add = new_definition
  (parse_term "(x1,y1) treal_add (x2,y2) = (x1 + x2, y1 + y2)");;

let treal_mul = new_definition
  (parse_term "(x1,y1) treal_mul (x2,y2) = ((x1 * x2) + (y1 * y2),(x1 * y2) + (y1 * x2))");;

let treal_le = new_definition
  (parse_term "(x1,y1) treal_le (x2,y2) <=> x1 + y2 <= x2 + y1");;

let treal_inv = new_definition
  (parse_term "treal_inv(x,y) = if x = y then (&0, &0)\n                    else if y <= x then (inv(@d. x = y + d), &0)\n                    else (&0, inv(@d. y = x + d))");;

(* ------------------------------------------------------------------------- *)
(* Define the equivalence relation and prove it *is* one.                    *)
(* ------------------------------------------------------------------------- *)

let treal_eq = new_definition
  (parse_term "(x1,y1) treal_eq (x2,y2) <=> (x1 + y2 = x2 + y1)");;

let vTREAL_EQ_REFL = try Cache.lookup_thm "TREAL_EQ_REFL" with _ ->  prove
 ((parse_term "!x. x treal_eq x"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_eq]);;

let vTREAL_EQ_SYM = try Cache.lookup_thm "TREAL_EQ_SYM" with _ ->  prove
 ((parse_term "!x y. x treal_eq y <=> y treal_eq x"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_eq; vEQ_SYM_EQ]);;

let vTREAL_EQ_TRANS = try Cache.lookup_thm "TREAL_EQ_TRANS" with _ ->  prove
 ((parse_term "!x y z. x treal_eq y /\\ y treal_eq z ==> x treal_eq z"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_eq] ----> vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vMK_COMB -| (vAP_TERM (parse_term "(+)") $-$ vI) -| vCONJ_PAIR) ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV) [vHREAL_ADD_SYM] ---->
  vREWRITE_TAC[vGSYM vHREAL_ADD_ASSOC; vHREAL_EQ_ADD_LCANCEL] ---->
  vREWRITE_TAC[vHREAL_ADD_ASSOC; vHREAL_EQ_ADD_RCANCEL] ---->
  vDISCH_THEN(vMATCH_ACCEPT_TAC -| vONCE_REWRITE_RULE[vHREAL_ADD_SYM]));;

(* ------------------------------------------------------------------------- *)
(* Useful to avoid unnecessary use of the equivalence relation.              *)
(* ------------------------------------------------------------------------- *)

let vTREAL_EQ_AP = try Cache.lookup_thm "TREAL_EQ_AP" with _ ->  prove
 ((parse_term "!x y. (x = y) ==> x treal_eq y"),
  vSIMP_TAC[vTREAL_EQ_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Commutativity properties for injector.                                    *)
(* ------------------------------------------------------------------------- *)

let vTREAL_OF_NUM_EQ = try Cache.lookup_thm "TREAL_OF_NUM_EQ" with _ ->  prove
 ((parse_term "!m n. (treal_of_num m treal_eq treal_of_num n) <=> (m = n)"),
  vREWRITE_TAC[treal_of_num; treal_eq; vHREAL_OF_NUM_EQ; vHREAL_ADD_RID]);;

let vTREAL_OF_NUM_LE = try Cache.lookup_thm "TREAL_OF_NUM_LE" with _ ->  prove
 ((parse_term "!m n. (treal_of_num m treal_le treal_of_num n) <=> m <= n"),
  vREWRITE_TAC[treal_of_num; treal_le; vHREAL_OF_NUM_LE; vHREAL_ADD_RID]);;

let vTREAL_OF_NUM_ADD = try Cache.lookup_thm "TREAL_OF_NUM_ADD" with _ ->  prove
 ((parse_term "!m n. (treal_of_num m treal_add treal_of_num n) treal_eq\n         (treal_of_num(m + n))"),
  vREWRITE_TAC[treal_of_num; treal_eq; treal_add;
   vHREAL_OF_NUM_ADD; vHREAL_ADD_RID; vADD_CLAUSES]);;

let vTREAL_OF_NUM_MUL = try Cache.lookup_thm "TREAL_OF_NUM_MUL" with _ ->  prove
 ((parse_term "!m n. (treal_of_num m treal_mul treal_of_num n) treal_eq\n         (treal_of_num(m * n))"),
  vREWRITE_TAC[treal_of_num; treal_eq; treal_mul;
   vHREAL_OF_NUM_MUL; vHREAL_MUL_RZERO; vHREAL_MUL_LZERO; vHREAL_ADD_RID;
   vHREAL_ADD_LID; vHREAL_ADD_RID; vMULT_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Strong forms of equality are useful to simplify welldefinedness proofs.   *)
(* ------------------------------------------------------------------------- *)

let vTREAL_ADD_SYM_EQ = try Cache.lookup_thm "TREAL_ADD_SYM_EQ" with _ ->  prove
 ((parse_term "!x y. x treal_add y = y treal_add x"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_add; vPAIR_EQ; vHREAL_ADD_SYM]);;

let vTREAL_MUL_SYM_EQ = try Cache.lookup_thm "TREAL_MUL_SYM_EQ" with _ ->  prove
 ((parse_term "!x y. x treal_mul y = y treal_mul x"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_mul; vHREAL_MUL_SYM; vHREAL_ADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Prove the properties of operations on representatives.                    *)
(* ------------------------------------------------------------------------- *)

let vTREAL_ADD_SYM = try Cache.lookup_thm "TREAL_ADD_SYM" with _ ->  prove
 ((parse_term "!x y. (x treal_add y) treal_eq (y treal_add x)"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vTREAL_EQ_AP ---->
  vMATCH_ACCEPT_TAC vTREAL_ADD_SYM_EQ);;

let vTREAL_ADD_ASSOC = try Cache.lookup_thm "TREAL_ADD_ASSOC" with _ ->  prove
 ((parse_term "!x y z. (x treal_add (y treal_add z)) treal_eq\n           ((x treal_add y) treal_add z)"),
  vSIMP_TAC[vFORALL_PAIR_THM; vTREAL_EQ_AP; treal_add; vHREAL_ADD_ASSOC]);;

let vTREAL_ADD_LID = try Cache.lookup_thm "TREAL_ADD_LID" with _ ->  prove
 ((parse_term "!x. ((treal_of_num 0) treal_add x) treal_eq x"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_of_num; treal_add; treal_eq;
              vHREAL_ADD_LID]);;

let vTREAL_ADD_LINV = try Cache.lookup_thm "TREAL_ADD_LINV" with _ ->  prove
 ((parse_term "!x. ((treal_neg x) treal_add x) treal_eq (treal_of_num 0)"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_neg; treal_add; treal_eq; treal_of_num;
              vHREAL_ADD_LID; vHREAL_ADD_RID; vHREAL_ADD_SYM]);;

let vTREAL_MUL_SYM = try Cache.lookup_thm "TREAL_MUL_SYM" with _ ->  prove
 ((parse_term "!x y. (x treal_mul y) treal_eq (y treal_mul x)"),
  vSIMP_TAC[vTREAL_EQ_AP; vTREAL_MUL_SYM_EQ]);;

let vTREAL_MUL_ASSOC = try Cache.lookup_thm "TREAL_MUL_ASSOC" with _ ->  prove
 ((parse_term "!x y z. (x treal_mul (y treal_mul z)) treal_eq\n           ((x treal_mul y) treal_mul z)"),
  vSIMP_TAC[vFORALL_PAIR_THM; vTREAL_EQ_AP; treal_mul; vHREAL_ADD_LDISTRIB;
           vHREAL_ADD_RDISTRIB; vGSYM vHREAL_MUL_ASSOC; vHREAL_ADD_AC]);;

let vTREAL_MUL_LID = try Cache.lookup_thm "TREAL_MUL_LID" with _ ->  prove
 ((parse_term "!x. ((treal_of_num 1) treal_mul x) treal_eq x"),
  vSIMP_TAC[vFORALL_PAIR_THM; treal_of_num; treal_mul; treal_eq] ---->
  vREWRITE_TAC[vHREAL_MUL_LZERO; vHREAL_MUL_LID; vHREAL_ADD_LID; vHREAL_ADD_RID]);;

let vTREAL_ADD_LDISTRIB = try Cache.lookup_thm "TREAL_ADD_LDISTRIB" with _ ->  prove
 ((parse_term "!x y z. (x treal_mul (y treal_add z)) treal_eq\n           ((x treal_mul y) treal_add (x treal_mul z))"),
  vSIMP_TAC[vFORALL_PAIR_THM; vTREAL_EQ_AP; treal_mul; treal_add;
           vHREAL_ADD_LDISTRIB; vPAIR_EQ; vHREAL_ADD_AC]);;

let vTREAL_LE_REFL = try Cache.lookup_thm "TREAL_LE_REFL" with _ ->  prove
 ((parse_term "!x. x treal_le x"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_le; vHREAL_LE_REFL]);;

let vTREAL_LE_ANTISYM = try Cache.lookup_thm "TREAL_LE_ANTISYM" with _ ->  prove
 ((parse_term "!x y. x treal_le y /\\ y treal_le x <=> (x treal_eq y)"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_le; treal_eq; vHREAL_LE_ANTISYM]);;

let vTREAL_LE_TRANS = try Cache.lookup_thm "TREAL_LE_TRANS" with _ ->  prove
 ((parse_term "!x y z. x treal_le y /\\ y treal_le z ==> x treal_le z"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_le] ----> vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vHREAL_LE_ADD2) ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV) [vHREAL_ADD_SYM] ---->
  vREWRITE_TAC[vGSYM vHREAL_ADD_ASSOC; vHREAL_LE_ADD_LCANCEL] ---->
  vREWRITE_TAC[vHREAL_ADD_ASSOC; vHREAL_LE_ADD_RCANCEL] ---->
  vDISCH_THEN(vMATCH_ACCEPT_TAC -| vONCE_REWRITE_RULE[vHREAL_ADD_SYM]));;

let vTREAL_LE_TOTAL = try Cache.lookup_thm "TREAL_LE_TOTAL" with _ ->  prove
 ((parse_term "!x y. x treal_le y \\/ y treal_le x"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_le; vHREAL_LE_TOTAL]);;

let vTREAL_LE_LADD_IMP = try Cache.lookup_thm "TREAL_LE_LADD_IMP" with _ ->  prove
 ((parse_term "!x y z. (y treal_le z) ==> (x treal_add y) treal_le (x treal_add z)"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_le; treal_add] ---->
  vREWRITE_TAC[vGSYM vHREAL_ADD_ASSOC; vHREAL_LE_ADD_LCANCEL] ---->
  vONCE_REWRITE_TAC[vHREAL_ADD_SYM] ---->
  vREWRITE_TAC[vGSYM vHREAL_ADD_ASSOC; vHREAL_LE_ADD_LCANCEL]);;

let vTREAL_LE_MUL = try Cache.lookup_thm "TREAL_LE_MUL" with _ ->  prove
 ((parse_term "!x y. (treal_of_num 0) treal_le x /\\ (treal_of_num 0) treal_le y\n         ==> (treal_of_num 0) treal_le (x treal_mul y)"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_of_num; treal_le; treal_mul] ---->
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vHREAL_ADD_LID; vHREAL_ADD_RID] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC -| vMATCH_MP vHREAL_LE_EXISTS) ---->
  vREWRITE_TAC[vHREAL_ADD_LDISTRIB; vHREAL_LE_ADD_LCANCEL;
    vGSYM vHREAL_ADD_ASSOC] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vHREAL_ADD_SYM] ---->
  vASM_REWRITE_TAC[vHREAL_LE_ADD_LCANCEL] ---->
  vMATCH_MP_TAC vHREAL_LE_MUL_RCANCEL_IMP ----> vASM_REWRITE_TAC[]);;

let vTREAL_INV_0 = try Cache.lookup_thm "TREAL_INV_0" with _ ->  prove
 ((parse_term "treal_inv (treal_of_num 0) treal_eq (treal_of_num 0)"),
  vREWRITE_TAC[treal_inv; treal_eq; treal_of_num]);;

let vTREAL_MUL_LINV = try Cache.lookup_thm "TREAL_MUL_LINV" with _ ->  prove
 ((parse_term "!x. ~(x treal_eq treal_of_num 0) ==>\n        (treal_inv(x) treal_mul x) treal_eq (treal_of_num 1)"),
  vREWRITE_TAC[vFORALL_PAIR_THM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x:hreal"); (parse_term "y:hreal")] ---->
  vPURE_REWRITE_TAC[treal_eq; treal_of_num; treal_mul; treal_inv] ---->
  vPURE_REWRITE_TAC[vHREAL_ADD_LID; vHREAL_ADD_RID] ----> vDISCH_TAC ---->
  vPURE_ASM_REWRITE_TAC[vCOND_CLAUSES] ----> vCOND_CASES_TAC ---->
  vPURE_REWRITE_TAC[treal_mul; treal_eq] ---->
  vREWRITE_TAC[vHREAL_ADD_LID; vHREAL_ADD_RID;
              vHREAL_MUL_LZERO; vHREAL_MUL_RZERO] ++-->
   [vALL_TAC;
    vDISJ_CASES_THEN vMP_TAC(vSPECL [(parse_term "x:hreal"); (parse_term "y:hreal")] vHREAL_LE_TOTAL) ---->
    vASM_REWRITE_TAC[] ----> vDISCH_TAC] ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vHREAL_LE_EXISTS) ---->
  vDISCH_THEN(vMP_TAC -| vSELECT_RULE) ---->
  vDISCH_THEN(fun th -> vASSUME_TAC (vSYM th) ---->
                       vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [th]) ---->
  vREWRITE_TAC[vHREAL_ADD_LDISTRIB] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vHREAL_ADD_SYM] ---->
  vAP_TERM_TAC ----> vMATCH_MP_TAC vHREAL_MUL_LINV ---->
  vDISCH_THEN vSUBST_ALL_TAC ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_eq -| concl) ---->
  vASM_REWRITE_TAC[vHREAL_ADD_RID] ---->
  vPURE_ONCE_REWRITE_TAC[vEQ_SYM_EQ] ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Show that the operations respect the equivalence relation.                *)
(* ------------------------------------------------------------------------- *)

let vTREAL_OF_NUM_WELLDEF = try Cache.lookup_thm "TREAL_OF_NUM_WELLDEF" with _ ->  prove
 ((parse_term "!m n. (m = n) ==> (treal_of_num m) treal_eq (treal_of_num n)"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN vSUBST1_TAC ---->
  vMATCH_ACCEPT_TAC vTREAL_EQ_REFL);;

let vTREAL_NEG_WELLDEF = try Cache.lookup_thm "TREAL_NEG_WELLDEF" with _ ->  prove
 ((parse_term "!x1 x2. x1 treal_eq x2 ==> (treal_neg x1) treal_eq (treal_neg x2)"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_neg; treal_eq] ----> vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vHREAL_ADD_SYM] ----> vASM_REWRITE_TAC[]);;

let vTREAL_ADD_WELLDEFR = try Cache.lookup_thm "TREAL_ADD_WELLDEFR" with _ ->  prove
 ((parse_term "!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_add y) treal_eq (x2 treal_add y)"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_add; treal_eq] ---->
  vREWRITE_TAC[vHREAL_EQ_ADD_RCANCEL; vHREAL_ADD_ASSOC] ---->
  vONCE_REWRITE_TAC[vHREAL_ADD_SYM] ---->
  vREWRITE_TAC[vHREAL_EQ_ADD_RCANCEL; vHREAL_ADD_ASSOC]);;

let vTREAL_ADD_WELLDEF = try Cache.lookup_thm "TREAL_ADD_WELLDEF" with _ ->  prove
 ((parse_term "!x1 x2 y1 y2. x1 treal_eq x2 /\\ y1 treal_eq y2 ==>\n     (x1 treal_add y1) treal_eq (x2 treal_add y2)"),
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vTREAL_EQ_TRANS ----> vEXISTS_TAC (parse_term "x1 treal_add y2") ---->
  vCONJ_TAC ++--> [vONCE_REWRITE_TAC[vTREAL_ADD_SYM_EQ]; vALL_TAC] ---->
  vMATCH_MP_TAC vTREAL_ADD_WELLDEFR ----> vASM_REWRITE_TAC[]);;

let vTREAL_MUL_WELLDEFR = try Cache.lookup_thm "TREAL_MUL_WELLDEFR" with _ ->  prove
 ((parse_term "!x1 x2 y. x1 treal_eq x2 ==> (x1 treal_mul y) treal_eq (x2 treal_mul y)"),
  vREWRITE_TAC[vFORALL_PAIR_THM; treal_mul; treal_eq] ----> vREPEAT vGEN_TAC ---->
  vONCE_REWRITE_TAC[vAC vHREAL_ADD_AC
    (parse_term "(a + b) + (c + d) = (a + d) + (b + c)")] ---->
  vREWRITE_TAC[vGSYM vHREAL_ADD_RDISTRIB] ----> vDISCH_TAC ---->
  vASM_REWRITE_TAC[] ----> vAP_TERM_TAC ---->
  vONCE_REWRITE_TAC[vHREAL_ADD_SYM] ----> vPOP_ASSUM vSUBST1_TAC ----> vREFL_TAC);;

let vTREAL_MUL_WELLDEF = try Cache.lookup_thm "TREAL_MUL_WELLDEF" with _ ->  prove
 ((parse_term "!x1 x2 y1 y2. x1 treal_eq x2 /\\ y1 treal_eq y2 ==>\n     (x1 treal_mul y1) treal_eq (x2 treal_mul y2)"),
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vTREAL_EQ_TRANS ----> vEXISTS_TAC (parse_term "x1 treal_mul y2") ---->
  vCONJ_TAC ++--> [vONCE_REWRITE_TAC[vTREAL_MUL_SYM_EQ]; vALL_TAC] ---->
  vMATCH_MP_TAC vTREAL_MUL_WELLDEFR ----> vASM_REWRITE_TAC[]);;

let vTREAL_EQ_IMP_LE = try Cache.lookup_thm "TREAL_EQ_IMP_LE" with _ ->  prove
 ((parse_term "!x y. x treal_eq y ==> x treal_le y"),
  vSIMP_TAC[vFORALL_PAIR_THM; treal_eq; treal_le; vHREAL_LE_REFL]);;

let vTREAL_LE_WELLDEF = try Cache.lookup_thm "TREAL_LE_WELLDEF" with _ ->  prove
 ((parse_term "!x1 x2 y1 y2. x1 treal_eq x2 /\\ y1 treal_eq y2 ==>\n     (x1 treal_le y1 <=> x2 treal_le y2)"),
  vREPEAT (vSTRIP_TAC |---> vEQ_TAC) ++-->
   [vMATCH_MP_TAC vTREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "y1:hreal#hreal") ---->
    vCONJ_TAC ++-->
     [vMATCH_MP_TAC vTREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "x1:hreal#hreal") ---->
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vTREAL_EQ_IMP_LE ---->
      vONCE_REWRITE_TAC[vTREAL_EQ_SYM];
      vMATCH_MP_TAC vTREAL_EQ_IMP_LE];
    vMATCH_MP_TAC vTREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "y2:hreal#hreal") ---->
    vCONJ_TAC ++-->
     [vMATCH_MP_TAC vTREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "x2:hreal#hreal") ---->
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vTREAL_EQ_IMP_LE;
      vMATCH_MP_TAC vTREAL_EQ_IMP_LE ----> vONCE_REWRITE_TAC[vTREAL_EQ_SYM]]] ---->
  vASM_REWRITE_TAC[]);;

let vTREAL_INV_WELLDEF = try Cache.lookup_thm "TREAL_INV_WELLDEF" with _ ->  prove
 ((parse_term "!x y. x treal_eq y ==> (treal_inv x) treal_eq (treal_inv y)"),
  let lemma = prove
   ((parse_term "(@d. x = x + d) = &0"),
    vMATCH_MP_TAC vSELECT_UNIQUE ----> vBETA_TAC ---->
    vGEN_TAC ----> vGEN_REWRITE_TAC (funpow 2 vLAND_CONV) [vGSYM vHREAL_ADD_RID] ---->
    vREWRITE_TAC[vHREAL_EQ_ADD_LCANCEL] ---->
    vMATCH_ACCEPT_TAC vEQ_SYM_EQ) in
  vREWRITE_TAC[vFORALL_PAIR_THM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x1:hreal"); (parse_term "x2:hreal"); (parse_term "y1:hreal"); (parse_term "y2:hreal")] ---->
  vPURE_REWRITE_TAC[treal_eq; treal_inv] ---->
  vASM_CASES_TAC (parse_term "x1 :hreal = x2") ---->
  vASM_CASES_TAC (parse_term "y1 :hreal = y2") ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vTREAL_EQ_REFL] ---->
  vDISCH_THEN(vMP_TAC -| vGEN_REWRITE_RULE vRAND_CONV [vHREAL_ADD_SYM]) ---->
  vREWRITE_TAC[vHREAL_EQ_ADD_LCANCEL; vHREAL_EQ_ADD_RCANCEL] ----> vDISCH_TAC ---->
  vASM_REWRITE_TAC[vHREAL_LE_REFL; lemma; vHREAL_INV_0;vTREAL_EQ_REFL] ---->
  vASM_CASES_TAC (parse_term "x2 <= x1") ----> vASM_REWRITE_TAC[] ++-->
   [vFIRST_ASSUM(vASSUME_TAC -| vSYM -| vSELECT_RULE -| vMATCH_MP vHREAL_LE_EXISTS) ---->
    vUNDISCH_TAC (parse_term "x1 + y2 = x2 + y1") ---->
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM) ---->
    vREWRITE_TAC[vHREAL_EQ_ADD_LCANCEL; vGSYM vHREAL_ADD_ASSOC] ---->
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
    vREWRITE_TAC[vONCE_REWRITE_RULE[vHREAL_ADD_SYM] vHREAL_LE_ADD] ---->
    vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV -| vRAND_CONV -| vBINDER_CONV -|
      vLAND_CONV) [vHREAL_ADD_SYM] ---->
    vREWRITE_TAC[vHREAL_EQ_ADD_LCANCEL; vTREAL_EQ_REFL];
    vDISJ_CASES_THEN vMP_TAC
      (vSPECL [(parse_term "x1:hreal"); (parse_term "x2:hreal")] vHREAL_LE_TOTAL) ---->
    vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
    vFIRST_ASSUM(vASSUME_TAC -| vSYM -| vSELECT_RULE -| vMATCH_MP vHREAL_LE_EXISTS) ---->
    vUNDISCH_TAC (parse_term "x1 + y2 = x2 + y1") ---->
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM) ---->
    vREWRITE_TAC[vHREAL_EQ_ADD_LCANCEL; vGSYM vHREAL_ADD_ASSOC] ---->
    vDISCH_THEN vSUBST1_TAC ---->
    vREWRITE_TAC[vONCE_REWRITE_RULE[vHREAL_ADD_SYM] vHREAL_LE_ADD] ---->
    vCOND_CASES_TAC ++-->
     [vUNDISCH_TAC (parse_term "(@d. x2 = x1 + d) + y1 <= y1:hreal") ---->
      vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vHREAL_ADD_LID] ---->
      vREWRITE_TAC[vONCE_REWRITE_RULE[vHREAL_ADD_SYM] vHREAL_LE_ADD_LCANCEL] ---->
      vDISCH_TAC ----> vSUBGOAL_THEN (parse_term "(@d. x2 = x1 + d) = &0") vMP_TAC ++-->
       [vASM_REWRITE_TAC[vGSYM vHREAL_LE_ANTISYM] ---->
        vGEN_REWRITE_TAC vRAND_CONV [vGSYM vHREAL_ADD_LID] ---->
        vREWRITE_TAC[vHREAL_LE_ADD];
        vDISCH_THEN vSUBST_ALL_TAC ---->
        vUNDISCH_TAC (parse_term "x1 + &0 = x2") ---->
        vASM_REWRITE_TAC[vHREAL_ADD_RID]];
      vGEN_REWRITE_TAC (funpow 3 vRAND_CONV -| vBINDER_CONV -| vLAND_CONV)
        [vHREAL_ADD_SYM] ---->
      vREWRITE_TAC[vHREAL_EQ_ADD_LCANCEL; vTREAL_EQ_REFL]]]);;

(* ------------------------------------------------------------------------- *)
(* Now define the quotient type -- the reals at last!                        *)
(* ------------------------------------------------------------------------- *)

let real_tybij =
  define_quotient_type "real" ("mk_real","dest_real") (parse_term "(treal_eq)");;

let real_of_num,real_of_num_th =
  lift_function (snd real_tybij) (vTREAL_EQ_REFL,vTREAL_EQ_TRANS)
  "real_of_num" vTREAL_OF_NUM_WELLDEF;;

let real_neg,real_neg_th =
  lift_function (snd real_tybij) (vTREAL_EQ_REFL,vTREAL_EQ_TRANS)
  "real_neg" vTREAL_NEG_WELLDEF;;

let real_add,real_add_th =
  lift_function (snd real_tybij) (vTREAL_EQ_REFL,vTREAL_EQ_TRANS)
  "real_add" vTREAL_ADD_WELLDEF;;

let real_mul,real_mul_th =
  lift_function (snd real_tybij) (vTREAL_EQ_REFL,vTREAL_EQ_TRANS)
  "real_mul" vTREAL_MUL_WELLDEF;;

let real_le,real_le_th =
  lift_function (snd real_tybij) (vTREAL_EQ_REFL,vTREAL_EQ_TRANS)
  "real_le" vTREAL_LE_WELLDEF;;

let real_inv,real_inv_th =
  lift_function (snd real_tybij) (vTREAL_EQ_REFL,vTREAL_EQ_TRANS)
  "real_inv" vTREAL_INV_WELLDEF;;

let [@warning "-8"] [vREAL_ADD_SYM; vREAL_ADD_ASSOC; vREAL_ADD_LID; vREAL_ADD_LINV;
     vREAL_MUL_SYM; vREAL_MUL_ASSOC; vREAL_MUL_LID;
     vREAL_ADD_LDISTRIB;
     vREAL_LE_REFL; vREAL_LE_ANTISYM; vREAL_LE_TRANS; vREAL_LE_TOTAL;
     vREAL_LE_LADD_IMP; vREAL_LE_MUL;
     vREAL_INV_0; vREAL_MUL_LINV;
     vREAL_OF_NUM_EQ; vREAL_OF_NUM_LE; vREAL_OF_NUM_ADD; vREAL_OF_NUM_MUL] =
  map
    (lift_theorem real_tybij (vTREAL_EQ_REFL,vTREAL_EQ_SYM,vTREAL_EQ_TRANS)
      [real_of_num_th; real_neg_th; real_add_th;
       real_mul_th; real_le_th; real_inv_th])
    [vTREAL_ADD_SYM; vTREAL_ADD_ASSOC; vTREAL_ADD_LID; vTREAL_ADD_LINV;
     vTREAL_MUL_SYM; vTREAL_MUL_ASSOC; vTREAL_MUL_LID;
     vTREAL_ADD_LDISTRIB;
     vTREAL_LE_REFL; vTREAL_LE_ANTISYM; vTREAL_LE_TRANS; vTREAL_LE_TOTAL;
     vTREAL_LE_LADD_IMP; vTREAL_LE_MUL;
     vTREAL_INV_0; vTREAL_MUL_LINV;
     vTREAL_OF_NUM_EQ; vTREAL_OF_NUM_LE; vTREAL_OF_NUM_ADD; vTREAL_OF_NUM_MUL];;

(* ------------------------------------------------------------------------- *)
(* Set up a friendly interface.                                              *)
(* ------------------------------------------------------------------------- *)

parse_as_prefix "--";;
parse_as_infix ("/",(22,"left"));;
parse_as_infix ("pow",(24,"left"));;

do_list overload_interface
 ["+",(parse_term "real_add:real->real->real"); "-",(parse_term "real_sub:real->real->real");
  "*",(parse_term "real_mul:real->real->real"); "/",(parse_term "real_div:real->real->real");
  "<",(parse_term "real_lt:real->real->bool"); "<=",(parse_term "real_le:real->real->bool");
  ">",(parse_term "real_gt:real->real->bool"); ">=",(parse_term "real_ge:real->real->bool");
  "--",(parse_term "real_neg:real->real"); "pow",(parse_term "real_pow:real->num->real");
  "inv",(parse_term "real_inv:real->real"); "abs",(parse_term "real_abs:real->real");
  "max",(parse_term "real_max:real->real->real"); "min",(parse_term "real_min:real->real->real");
  "&",(parse_term "real_of_num:num->real")];;

let prioritize_real() = prioritize_overload(mk_type("real",[]));;

(* ------------------------------------------------------------------------- *)
(* Additional definitions.                                                   *)
(* ------------------------------------------------------------------------- *)

let real_sub = new_definition
  (parse_term "x - y = x + --y");;

let real_lt = new_definition
  (parse_term "x < y <=> ~(y <= x)");;

let real_ge = new_definition
  (parse_term "x >= y <=> y <= x");;

let real_gt = new_definition
  (parse_term "x > y <=> y < x");;

let real_abs = new_definition
  (parse_term "abs(x) = if &0 <= x then x else --x");;

let real_pow = new_recursive_definition num_RECURSION
  (parse_term "(x pow 0 = &1) /\\\n   (!n. x pow (SUC n) = x * (x pow n))");;

let real_div = new_definition
  (parse_term "x / y = x * inv(y)");;

let real_max = new_definition
  (parse_term "real_max m n = if m <= n then n else m");;

let real_min = new_definition
  (parse_term "real_min m n = if m <= n then m else n");;

(*----------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set         *)
(*----------------------------------------------------------------------------*)

let vREAL_HREAL_LEMMA1 = try Cache.lookup_thm "REAL_HREAL_LEMMA1" with _ ->  prove
 ((parse_term "?r:hreal->real.\n       (!x. &0 <= x <=> ?y. x = r y) /\\\n       (!y z. y <= z <=> r y <= r z)"),
  vEXISTS_TAC (parse_term "\\y. mk_real((treal_eq)(y,hreal_of_num 0))") ---->
  vREWRITE_TAC[vGSYM real_le_th] ---->
  vREWRITE_TAC[treal_le; vHREAL_ADD_LID; vHREAL_ADD_RID] ---->
  vGEN_TAC ----> vEQ_TAC ++-->
   [vMP_TAC(vINST [(parse_term "dest_real x"),(parse_term "r:hreal#hreal->bool")] (snd real_tybij)) ---->
    vREWRITE_TAC[fst real_tybij] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "p:hreal#hreal") vMP_TAC) ---->
    vDISCH_THEN(vMP_TAC -| vAP_TERM (parse_term "mk_real")) ---->
    vREWRITE_TAC[fst real_tybij] ----> vDISCH_THEN vSUBST1_TAC ---->
    vREWRITE_TAC[vGSYM real_of_num_th; vGSYM real_le_th] ---->
    vSUBST1_TAC(vGSYM(vISPEC (parse_term "p:hreal#hreal") vPAIR)) ---->
    vPURE_REWRITE_TAC[treal_of_num; treal_le] ---->
    vPURE_REWRITE_TAC[vHREAL_ADD_LID; vHREAL_ADD_RID] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:hreal") vSUBST1_TAC -|
      vMATCH_MP vHREAL_LE_EXISTS) ---->
    vEXISTS_TAC (parse_term "d:hreal") ----> vAP_TERM_TAC ---->
    vONCE_REWRITE_TAC[vFUN_EQ_THM] ----> vX_GEN_TAC (parse_term "q:hreal#hreal") ---->
    vSUBST1_TAC(vGSYM(vISPEC (parse_term "q:hreal#hreal") vPAIR)) ---->
    vPURE_REWRITE_TAC[treal_eq] ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vHREAL_ADD_SYM] ---->
    vREWRITE_TAC[vGSYM vHREAL_ADD_ASSOC; vHREAL_EQ_ADD_LCANCEL] ---->
    vREWRITE_TAC[vHREAL_ADD_RID];
    vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC) ---->
    vREWRITE_TAC[vGSYM real_of_num_th; vGSYM real_le_th] ---->
    vREWRITE_TAC[treal_of_num; treal_le] ---->
    vREWRITE_TAC[vHREAL_ADD_LID; vHREAL_ADD_RID] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vHREAL_ADD_LID] ---->
    vREWRITE_TAC[vHREAL_LE_ADD]]);;

let vREAL_HREAL_LEMMA2 = try Cache.lookup_thm "REAL_HREAL_LEMMA2" with _ ->  prove
 ((parse_term "?h r. (!x:hreal. h(r x) = x) /\\\n         (!x. &0 <= x ==> (r(h x) = x)) /\\\n         (!x:hreal. &0 <= r x) /\\\n         (!x y. x <= y <=> r x <= r y)"),
  vSTRIP_ASSUME_TAC vREAL_HREAL_LEMMA1 ---->
  vEXISTS_TAC (parse_term "\\x:real. @y:hreal. x = r y") ---->
  vEXISTS_TAC (parse_term "r:hreal->real") ---->
  vASM_REWRITE_TAC[vBETA_THM] ---->
  vSUBGOAL_THEN (parse_term "!y z. ((r:hreal->real) y = r z) <=> (y = z)") vASSUME_TAC ++-->
   [vASM_REWRITE_TAC[vGSYM vREAL_LE_ANTISYM; vGSYM vHREAL_LE_ANTISYM]; vALL_TAC] ---->
  vASM_REWRITE_TAC[vGEN_REWRITE_RULE (vLAND_CONV -| vBINDER_CONV) [vEQ_SYM_EQ]
    (vSPEC_ALL vSELECT_REFL); vGSYM vEXISTS_REFL] ---->
  vGEN_TAC ----> vDISCH_THEN(vACCEPT_TAC -| vSYM -| vSELECT_RULE));;

let vREAL_COMPLETE_SOMEPOS = try Cache.lookup_thm "REAL_COMPLETE_SOMEPOS" with _ ->  prove
 ((parse_term "!P. (?x. P x /\\ &0 <= x) /\\\n       (?M. !x. P x ==> x <= M)\n       ==> ?M. (!x. P x ==> x <= M) /\\\n               !M'. (!x. P x ==> x <= M') ==> M <= M'"),
  vREPEAT vSTRIP_TAC ----> vSTRIP_ASSUME_TAC vREAL_HREAL_LEMMA2 ---->
  vMP_TAC(vSPEC (parse_term "\\y:hreal. (P:real->bool)(r y)") vHREAL_COMPLETE) ---->
  vBETA_TAC ---->
  vW(vC vSUBGOAL_THEN vMP_TAC -| funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vCONJ_TAC ++-->
     [vEXISTS_TAC (parse_term "(h:real->hreal) x") ---->
      vUNDISCH_TAC (parse_term "(P:real->bool) x") ---->
      vMATCH_MP_TAC(vTAUT (parse_term "(b <=> a) ==> a ==> b")) ---->
      vAP_TERM_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
      vEXISTS_TAC (parse_term "(h:real->hreal) M") ---->
      vX_GEN_TAC (parse_term "y:hreal") ----> vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
      vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC(vTAUT (parse_term "(b <=> a) ==> a ==> b")) ---->
      vAP_TERM_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "x:real") ---->
      vASM_REWRITE_TAC[] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vASM_REWRITE_TAC[]];
    vMATCH_MP_TAC(vTAUT (parse_term "(b ==> c) ==> a ==> (a ==> b) ==> c")) ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "B:hreal") vSTRIP_ASSUME_TAC)] ---->
  vEXISTS_TAC (parse_term "(r:hreal->real) B") ----> vCONJ_TAC ++-->
   [vX_GEN_TAC (parse_term "z:real") ----> vDISCH_TAC ---->
    vDISJ_CASES_TAC(vSPECL [(parse_term "&0"); (parse_term "z:real")] vREAL_LE_TOTAL) ++-->
     [vANTE_RES_THEN(vSUBST1_TAC -| vSYM) (vASSUME (parse_term "&0 <= z")) ---->
      vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vI [vGSYM th]) ---->
      vFIRST_ASSUM vMATCH_MP_TAC ---->
      vUNDISCH_TAC (parse_term "(P:real->bool) z") ---->
      vMATCH_MP_TAC(vTAUT (parse_term "(b <=> a) ==> a ==> b")) ---->
      vAP_TERM_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vASM_REWRITE_TAC[];
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "&0") ---->
      vASM_REWRITE_TAC[]];
    vX_GEN_TAC (parse_term "C:real") ----> vDISCH_TAC ---->
    vSUBGOAL_THEN (parse_term "B:hreal <= (h(C:real))") vMP_TAC ++-->
     [vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
      vSUBGOAL_THEN (parse_term "(r:hreal->real)(h C) = C") (fun th -> vASM_REWRITE_TAC[th]);
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vEQ_IMP ----> vAP_TERM_TAC] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "x:real") ---->
    vASM_REWRITE_TAC[] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[]]);;

let vREAL_COMPLETE = try Cache.lookup_thm "REAL_COMPLETE" with _ ->  prove
 ((parse_term "!P. (?x. P x) /\\\n       (?M. !x. P x ==> x <= M)\n       ==> ?M. (!x. P x ==> x <= M) /\\\n               !M'. (!x. P x ==> x <= M') ==> M <= M'"),
  let lemma = prove
   ((parse_term "y = (y - x) + x"),
    vREWRITE_TAC[real_sub; vGSYM vREAL_ADD_ASSOC; vREAL_ADD_LINV] ---->
    vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vREWRITE_TAC[vREAL_ADD_LID]) in
  vREPEAT vSTRIP_TAC ---->
  vDISJ_CASES_TAC (vSPECL [(parse_term "&0"); (parse_term "x:real")] vREAL_LE_TOTAL) ++-->
   [vMATCH_MP_TAC vREAL_COMPLETE_SOMEPOS ----> vCONJ_TAC ++-->
     [vEXISTS_TAC (parse_term "x:real"); vEXISTS_TAC (parse_term "M:real")] ---->
    vASM_REWRITE_TAC[];
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vREAL_LE_LADD_IMP) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "--x")) ---->
    vREWRITE_TAC[vREAL_ADD_LINV] ---->
    vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vREWRITE_TAC[vREAL_ADD_LID] ---->
    vDISCH_TAC ---->
    vMP_TAC(vSPEC (parse_term "\\y. P(y + x) :bool") vREAL_COMPLETE_SOMEPOS) ---->
    vBETA_TAC ---->
    vW(vC vSUBGOAL_THEN vMP_TAC -| funpow 2 (fst -| dest_imp) -| snd) ++-->
     [vCONJ_TAC ++-->
       [vEXISTS_TAC (parse_term "&0") ----> vASM_REWRITE_TAC[vREAL_LE_REFL; vREAL_ADD_LID];
        vEXISTS_TAC (parse_term "M + --x") ----> vGEN_TAC ---->
        vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
        vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "--x") -| vMATCH_MP vREAL_LE_LADD_IMP) ---->
        vDISCH_THEN(vMP_TAC -| vONCE_REWRITE_RULE[vREAL_ADD_SYM]) ---->
        vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC] ---->
        vREWRITE_TAC[vONCE_REWRITE_RULE[vREAL_ADD_SYM] vREAL_ADD_LINV] ---->
        vREWRITE_TAC[vONCE_REWRITE_RULE[vREAL_ADD_SYM] vREAL_ADD_LID]];
      vMATCH_MP_TAC(vTAUT (parse_term "(b ==> c) ==> a ==> (a ==> b) ==> c")) ---->
      vDISCH_THEN(vX_CHOOSE_THEN (parse_term "B:real") vSTRIP_ASSUME_TAC)] ---->
    vEXISTS_TAC (parse_term "B + x") ----> vCONJ_TAC ++-->
     [vGEN_TAC ----> vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [lemma] ---->
      vDISCH_THEN(vANTE_RES_THEN
        (vMP_TAC -| vSPEC (parse_term "x:real") -| vMATCH_MP vREAL_LE_LADD_IMP)) ---->
      vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
      vREWRITE_TAC[real_sub; vGSYM vREAL_ADD_ASSOC; vREAL_ADD_LINV] ---->
      vREWRITE_TAC[vONCE_REWRITE_RULE[vREAL_ADD_SYM] vREAL_ADD_LID] ---->
      vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
      vASM_REWRITE_TAC[];
      vREPEAT vSTRIP_TAC ----> vSUBGOAL_THEN (parse_term "B <= M' - x") vMP_TAC ++-->
       [vFIRST_ASSUM vMATCH_MP_TAC ----> vX_GEN_TAC (parse_term "z:real") ----> vDISCH_TAC ---->
        vSUBGOAL_THEN (parse_term "z + x <= M'") vMP_TAC ++-->
         [vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
          vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "--x") -| vMATCH_MP vREAL_LE_LADD_IMP) ---->
          vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
          vREWRITE_TAC[real_sub] ----> vMATCH_MP_TAC vEQ_IMP ----> vAP_THM_TAC ---->
          vAP_TERM_TAC ----> vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC] ---->
          vREWRITE_TAC[vONCE_REWRITE_RULE[vREAL_ADD_SYM] vREAL_ADD_LINV] ---->
          vREWRITE_TAC[vONCE_REWRITE_RULE[vREAL_ADD_SYM] vREAL_ADD_LID]];
         vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "x:real") -| vMATCH_MP vREAL_LE_LADD_IMP) ---->
         vMATCH_MP_TAC vEQ_IMP ----> vBINOP_TAC ++-->
          [vMATCH_ACCEPT_TAC vREAL_ADD_SYM;
           vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vREWRITE_TAC[real_sub] ---->
           vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC; vREAL_ADD_LINV] ---->
           vREWRITE_TAC[vONCE_REWRITE_RULE[vREAL_ADD_SYM] vREAL_ADD_LID]]]]]);;

do_list reduce_interface
 ["+",(parse_term "hreal_add:hreal->hreal->hreal");
  "*",(parse_term "hreal_mul:hreal->hreal->hreal");
  "<=",(parse_term "hreal_le:hreal->hreal->bool");
  "inv",(parse_term "hreal_inv:hreal->hreal")];;

do_list remove_interface ["**"; "++"; "<<="; "==="; "fn"; "afn"];;
