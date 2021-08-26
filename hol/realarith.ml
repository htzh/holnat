(* ========================================================================= *)
(* Framework for universal real decision procedures, and a simple instance.  *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Nets
open Parser
open Equal
open Boolean
open Drule
open Tactics
open Simp
open Class
open Canon
open Meson
open Nums
open Arith
open Calc_num
open Normalizer
open Realax
open Calc_int

open Num

(* ------------------------------------------------------------------------- *)
(* Some lemmas needed now just to drive the decision procedure.              *)
(* ------------------------------------------------------------------------- *)

let vREAL_LTE_TOTAL = try Cache.lookup_thm "REAL_LTE_TOTAL" with _ ->  prove
 ((parse_term "!x y. x < y \\/ y <= x"),
  vREWRITE_TAC[real_lt] ----> vCONV_TAC vTAUT);;

let vREAL_LET_TOTAL = try Cache.lookup_thm "REAL_LET_TOTAL" with _ ->  prove
 ((parse_term "!x y. x <= y \\/ y < x"),
  vREWRITE_TAC[real_lt] ----> vCONV_TAC vTAUT);;

let vREAL_LT_IMP_LE = try Cache.lookup_thm "REAL_LT_IMP_LE" with _ ->  prove
 ((parse_term "!x y. x < y ==> x <= y"),
  vMESON_TAC[real_lt; vREAL_LE_TOTAL]);;

let vREAL_LTE_TRANS = try Cache.lookup_thm "REAL_LTE_TRANS" with _ ->  prove
 ((parse_term "!x y z. x < y /\\ y <= z ==> x < z"),
  vMESON_TAC[real_lt; vREAL_LE_TRANS]);;

let vREAL_LET_TRANS = try Cache.lookup_thm "REAL_LET_TRANS" with _ ->  prove
 ((parse_term "!x y z. x <= y /\\ y < z ==> x < z"),
  vMESON_TAC[real_lt; vREAL_LE_TRANS]);;

let vREAL_LT_TRANS = try Cache.lookup_thm "REAL_LT_TRANS" with _ ->  prove
 ((parse_term "!x y z. x < y /\\ y < z ==> x < z"),
  vMESON_TAC[vREAL_LTE_TRANS; vREAL_LT_IMP_LE]);;

let vREAL_LE_ADD = try Cache.lookup_thm "REAL_LE_ADD" with _ ->  prove
 ((parse_term "!x y. &0 <= x /\\ &0 <= y ==> &0 <= x + y"),
  vMESON_TAC[vREAL_LE_LADD_IMP; vREAL_ADD_RID; vREAL_LE_TRANS]);;

let vREAL_LTE_ANTISYM = try Cache.lookup_thm "REAL_LTE_ANTISYM" with _ ->  prove
 ((parse_term "!x y. ~(x < y /\\ y <= x)"),
  vMESON_TAC[real_lt]);;

let vREAL_SUB_LE = try Cache.lookup_thm "REAL_SUB_LE" with _ ->  prove
 ((parse_term "!x y. &0 <= (x - y) <=> y <= x"),
  vREWRITE_TAC[real_sub; vGSYM vREAL_LE_LNEG; vREAL_LE_NEG2]);;

let vREAL_NEG_SUB = try Cache.lookup_thm "REAL_NEG_SUB" with _ ->  prove
 ((parse_term "!x y. --(x - y) = y - x"),
  vREWRITE_TAC[real_sub; vREAL_NEG_ADD; vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_ADD_AC]);;

let vREAL_LE_LT = try Cache.lookup_thm "REAL_LE_LT" with _ ->  prove
 ((parse_term "!x y. x <= y <=> x < y \\/ (x = y)"),
  vREWRITE_TAC[real_lt] ----> vMESON_TAC[vREAL_LE_ANTISYM; vREAL_LE_TOTAL]);;

let vREAL_SUB_LT = try Cache.lookup_thm "REAL_SUB_LT" with _ ->  prove
 ((parse_term "!x y. &0 < (x - y) <=> y < x"),
  vREWRITE_TAC[real_lt] ----> vONCE_REWRITE_TAC[vGSYM vREAL_NEG_SUB] ---->
  vREWRITE_TAC[vREAL_LE_LNEG; vREAL_ADD_RID; vREAL_SUB_LE]);;

let vREAL_NOT_LT = try Cache.lookup_thm "REAL_NOT_LT" with _ ->  prove
 ((parse_term "!x y. ~(x < y) <=> y <= x"),
  vREWRITE_TAC[real_lt]);;

let vREAL_SUB_0 = try Cache.lookup_thm "REAL_SUB_0" with _ ->  prove
 ((parse_term "!x y. (x - y = &0) <=> (x = y)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV) [vGSYM vREAL_NOT_LT] ---->
  vREWRITE_TAC[vREAL_SUB_LE; vREAL_SUB_LT] ----> vREWRITE_TAC[vREAL_NOT_LT]);;

let vREAL_LT_LE = try Cache.lookup_thm "REAL_LT_LE" with _ ->  prove
 ((parse_term "!x y. x < y <=> x <= y /\\ ~(x = y)"),
  vMESON_TAC[real_lt; vREAL_LE_TOTAL; vREAL_LE_ANTISYM]);;

let vREAL_LT_REFL = try Cache.lookup_thm "REAL_LT_REFL" with _ ->  prove
 ((parse_term "!x. ~(x < x)"),
  vREWRITE_TAC[real_lt; vREAL_LE_REFL]);;

let vREAL_LTE_ADD = try Cache.lookup_thm "REAL_LTE_ADD" with _ ->  prove
 ((parse_term "!x y. &0 < x /\\ &0 <= y ==> &0 < x + y"),
  vMESON_TAC[vREAL_LE_LADD_IMP; vREAL_ADD_RID; vREAL_LTE_TRANS]);;

let vREAL_LET_ADD = try Cache.lookup_thm "REAL_LET_ADD" with _ ->  prove
 ((parse_term "!x y. &0 <= x /\\ &0 < y ==> &0 < x + y"),
  vMESON_TAC[vREAL_LTE_ADD; vREAL_ADD_SYM]);;

let vREAL_LT_ADD = try Cache.lookup_thm "REAL_LT_ADD" with _ ->  prove
 ((parse_term "!x y. &0 < x /\\ &0 < y ==> &0 < x + y"),
  vMESON_TAC[vREAL_LT_IMP_LE; vREAL_LTE_ADD]);;

let vREAL_ENTIRE = try Cache.lookup_thm "REAL_ENTIRE" with _ ->  prove
 ((parse_term "!x y. (x * y = &0) <=> (x = &0) \\/ (y = &0)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vSTRIP_TAC ---->
  vASM_REWRITE_TAC[vREAL_MUL_LZERO; vREAL_MUL_RZERO] ---->
  vASM_CASES_TAC (parse_term "x = &0") ----> vASM_REWRITE_TAC[] ---->
  vFIRST_ASSUM(vMP_TAC -| vAP_TERM (parse_term "(*) (inv x)")) ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV th]) ---->
  vREWRITE_TAC[vREAL_MUL_LID; vREAL_MUL_RZERO]);;

let vREAL_LE_NEGTOTAL = try Cache.lookup_thm "REAL_LE_NEGTOTAL" with _ ->  prove
 ((parse_term "!x. &0 <= x \\/ &0 <= --x"),
  vREWRITE_TAC[vREAL_LE_RNEG; vREAL_ADD_LID; vREAL_LE_TOTAL]);;

let vREAL_LE_SQUARE = try Cache.lookup_thm "REAL_LE_SQUARE" with _ ->  prove
 ((parse_term "!x. &0 <= x * x"),
  vGEN_TAC ----> vDISJ_CASES_TAC(vSPEC (parse_term "x:real") vREAL_LE_NEGTOTAL) ---->
  vPOP_ASSUM(fun th -> vMP_TAC(vMATCH_MP vREAL_LE_MUL (vCONJ th th))) ---->
  vREWRITE_TAC[vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG]);;

let vREAL_MUL_RID = try Cache.lookup_thm "REAL_MUL_RID" with _ ->  prove
 ((parse_term "!x. x * &1 = x"),
  vMESON_TAC[vREAL_MUL_LID; vREAL_MUL_SYM]);;

let vREAL_POW_2 = try Cache.lookup_thm "REAL_POW_2" with _ ->  prove
 ((parse_term "!x. x pow 2 = x * x"),
  vREWRITE_TAC[num_CONV (parse_term "2"); num_CONV (parse_term "1")] ---->
  vREWRITE_TAC[real_pow; vREAL_MUL_RID]);;

let vREAL_POLY_CLAUSES = try Cache.lookup_thm "REAL_POLY_CLAUSES" with _ ->  prove
 ((parse_term "(!x y z. x + (y + z) = (x + y) + z) /\\\n   (!x y. x + y = y + x) /\\\n   (!x. &0 + x = x) /\\\n   (!x y z. x * (y * z) = (x * y) * z) /\\\n   (!x y. x * y = y * x) /\\\n   (!x. &1 * x = x) /\\\n   (!x. &0 * x = &0) /\\\n   (!x y z. x * (y + z) = x * y + x * z) /\\\n   (!x. x pow 0 = &1) /\\\n   (!x n. x pow (SUC n) = x * x pow n)"),
  vREWRITE_TAC[real_pow; vREAL_ADD_LDISTRIB; vREAL_MUL_LZERO] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC; vREAL_ADD_LID; vREAL_MUL_LID] ---->
  vREWRITE_TAC[vREAL_ADD_AC] ----> vREWRITE_TAC[vREAL_MUL_SYM]);;

let vREAL_POLY_NEG_CLAUSES = try Cache.lookup_thm "REAL_POLY_NEG_CLAUSES" with _ ->  prove
 ((parse_term "(!x. --x = --(&1) * x) /\\\n   (!x y. x - y = x + --(&1) * y)"),
  vREWRITE_TAC[vREAL_MUL_LNEG; real_sub; vREAL_MUL_LID]);;

let vREAL_POS = try Cache.lookup_thm "REAL_POS" with _ ->  prove
 ((parse_term "!n. &0 <= &n"),
  vREWRITE_TAC[vREAL_OF_NUM_LE; vLE_0]);;

(* ------------------------------------------------------------------------- *)
(* Data structure for Positivstellensatz refutations.                        *)
(* ------------------------------------------------------------------------- *)

type positivstellensatz =
   Axiom_eq of int
 | Axiom_le of int
 | Axiom_lt of int
 | Rational_eq of num
 | Rational_le of num
 | Rational_lt of num
 | Square of term
 | Eqmul of term * positivstellensatz
 | Sum of positivstellensatz * positivstellensatz
 | Product of positivstellensatz * positivstellensatz;;

(* ------------------------------------------------------------------------- *)
(* Parametrized reals decision procedure.                                    *)
(*                                                                           *)
(* This is a bootstrapping version, and subsequently gets overwritten twice  *)
(* with more specialized versions, once here and finally in "calc_rat.ml".   *)
(* ------------------------------------------------------------------------- *)

let vGEN_REAL_ARITH =
  let pth = prove
   ((parse_term "(x < y <=> y - x > &0) /\\\n     (x <= y <=> y - x >= &0) /\\\n     (x > y <=> x - y > &0) /\\\n     (x >= y <=> x - y >= &0) /\\\n     ((x = y) <=> (x - y = &0)) /\\\n     (~(x < y) <=> x - y >= &0) /\\\n     (~(x <= y) <=> x - y > &0) /\\\n     (~(x > y) <=> y - x >= &0) /\\\n     (~(x >= y) <=> y - x > &0) /\\\n     (~(x = y) <=> x - y > &0 \\/ --(x - y) > &0)"),
    vREWRITE_TAC[real_gt; real_ge; vREAL_SUB_LT; vREAL_SUB_LE; vREAL_NEG_SUB] ---->
    vREWRITE_TAC[vREAL_SUB_0; real_lt] ----> vMESON_TAC[vREAL_LE_ANTISYM])
  and pth_final = vTAUT (parse_term "(~p ==> F) ==> p")
  and pth_add = prove
   ((parse_term "((x = &0) /\\ (y = &0) ==> (x + y = &0)) /\\\n     ((x = &0) /\\ y >= &0 ==> x + y >= &0) /\\\n     ((x = &0) /\\ y > &0 ==> x + y > &0) /\\\n     (x >= &0 /\\ (y = &0) ==> x + y >= &0) /\\\n     (x >= &0 /\\ y >= &0 ==> x + y >= &0) /\\\n     (x >= &0 /\\ y > &0 ==> x + y > &0) /\\\n     (x > &0 /\\ (y = &0) ==> x + y > &0) /\\\n     (x > &0 /\\ y >= &0 ==> x + y > &0) /\\\n     (x > &0 /\\ y > &0 ==> x + y > &0)"),
    vSIMP_TAC[vREAL_ADD_LID; vREAL_ADD_RID; real_ge; real_gt] ---->
    vREWRITE_TAC[vREAL_LE_LT] ---->
    vMESON_TAC[vREAL_ADD_LID; vREAL_ADD_RID; vREAL_LT_ADD])
  and pth_mul = prove
   ((parse_term "((x = &0) /\\ (y = &0) ==> (x * y = &0)) /\\\n     ((x = &0) /\\ y >= &0 ==> (x * y = &0)) /\\\n     ((x = &0) /\\ y > &0 ==> (x * y = &0)) /\\\n     (x >= &0 /\\ (y = &0) ==> (x * y = &0)) /\\\n     (x >= &0 /\\ y >= &0 ==> x * y >= &0) /\\\n     (x >= &0 /\\ y > &0 ==> x * y >= &0) /\\\n     (x > &0 /\\ (y = &0) ==> (x * y = &0)) /\\\n     (x > &0 /\\ y >= &0 ==> x * y >= &0) /\\\n     (x > &0 /\\ y > &0 ==> x * y > &0)"),
    vSIMP_TAC[vREAL_MUL_LZERO; vREAL_MUL_RZERO; real_ge; real_gt] ---->
    vSIMP_TAC[vREAL_LT_LE; vREAL_LE_MUL] ----> vMESON_TAC[vREAL_ENTIRE])
  and pth_emul = prove
   ((parse_term "(y = &0) ==> !x. x * y = &0"),
    vSIMP_TAC[vREAL_MUL_RZERO])
  and pth_square = prove
   ((parse_term "!x. x * x >= &0"),
    vREWRITE_TAC[real_ge; vREAL_POW_2; vREAL_LE_SQUARE])
  and vMATCH_MP_RULE th =
    let net = itlist
     (fun th -> net_of_conv (lhand(concl th)) (vPART_MATCH lhand th))
     (vCONJUNCTS th) empty_net in
    fun th -> vMP (vREWRITES_CONV net (concl th)) th
  and x_tm = (parse_term "x:real") and y_tm = (parse_term "y:real")
  and neg_tm = (parse_term "(--):real->real")
  and gt_tm = (parse_term "(>):real->real->bool")
  and ge_tm = (parse_term "(>=):real->real->bool")
  and eq_tm = (parse_term "(=):real->real->bool")
  and p_tm = (parse_term "p:bool")
  and or_tm = (parse_term "(\\/)")
  and false_tm = (parse_term "F")
  and z_tm = (parse_term "&0 :real")
  and xy_lt = (parse_term "(x:real) < y")
  and xy_nlt = (parse_term "~((x:real) < y)")
  and xy_le = (parse_term "(x:real) <= y")
  and xy_nle = (parse_term "~((x:real) <= y)")
  and xy_gt = (parse_term "(x:real) > y")
  and xy_ngt = (parse_term "~((x:real) > y)")
  and xy_ge = (parse_term "(x:real) >= y")
  and xy_nge = (parse_term "~((x:real) >= y)")
  and xy_eq = (parse_term "x:real = y")
  and xy_ne = (parse_term "~(x:real = y)") in
  let is_ge = is_binop ge_tm
  and is_gt = is_binop gt_tm
  and is_req = is_binop eq_tm in
  fun (mk_numeric,
       vNUMERIC_EQ_CONV,vNUMERIC_GE_CONV,vNUMERIC_GT_CONV,
       vPOLY_CONV,vPOLY_NEG_CONV,vPOLY_ADD_CONV,vPOLY_MUL_CONV,
       absconv1,absconv2,prover) ->
  let vREAL_INEQ_CONV pth tm =
    let lop,r = dest_comb tm in
    let th = vINST [rand lop,x_tm; r,y_tm] pth in
    vTRANS th (vLAND_CONV vPOLY_CONV (rand(concl th))) in
  let [@warning "-8"] [vREAL_LT_CONV; vREAL_LE_CONV; vREAL_GT_CONV; vREAL_GE_CONV; vREAL_EQ_CONV;
       vREAL_NOT_LT_CONV; vREAL_NOT_LE_CONV; vREAL_NOT_GT_CONV;
       vREAL_NOT_GE_CONV; _] =
       map vREAL_INEQ_CONV (vCONJUNCTS pth)
  and vREAL_NOT_EQ_CONV =
     let pth = last(vCONJUNCTS pth) in
     fun tm ->
      let l,r = dest_eq tm in
      let th = vINST [l,x_tm; r,y_tm] pth in
      let th_p = vPOLY_CONV(lhand(lhand(rand(concl th)))) in
      let th_x = vAP_TERM neg_tm th_p in
      let th_n = vCONV_RULE (vRAND_CONV vPOLY_NEG_CONV) th_x in
      let th' = vMK_DISJ (vAP_THM (vAP_TERM gt_tm th_p) z_tm)
                        (vAP_THM (vAP_TERM gt_tm th_n) z_tm) in
      vTRANS th th' in
  let net_single = itlist (uncurry net_of_conv)
   [xy_lt,vREAL_LT_CONV;
    xy_nlt,(fun t -> vREAL_NOT_LT_CONV(rand t));
    xy_le,vREAL_LE_CONV;
    xy_nle,(fun t -> vREAL_NOT_LE_CONV(rand t));
    xy_gt,vREAL_GT_CONV;
    xy_ngt,(fun t -> vREAL_NOT_GT_CONV(rand t));
    xy_ge,vREAL_GE_CONV;
    xy_nge,(fun t -> vREAL_NOT_GE_CONV(rand t));
    xy_eq,vREAL_EQ_CONV;
    xy_ne,(fun t -> vREAL_NOT_EQ_CONV(rand t))]
   empty_net
  and net_double = itlist (uncurry net_of_conv)
   [xy_lt,(fun t -> vREAL_LT_CONV t,vREAL_NOT_LT_CONV t);
    xy_le,(fun t -> vREAL_LE_CONV t,vREAL_NOT_LE_CONV t);
    xy_gt,(fun t -> vREAL_GT_CONV t,vREAL_NOT_GT_CONV t);
    xy_ge,(fun t -> vREAL_GE_CONV t,vREAL_NOT_GE_CONV t);
    xy_eq,(fun t -> vREAL_EQ_CONV t,vREAL_NOT_EQ_CONV t)]
   empty_net in
  let vREAL_INEQ_NORM_CONV = vREWRITES_CONV net_single
  and vREAL_INEQ_NORM_DCONV = vREWRITES_CONV net_double in
  let vNNF_NORM_CONV =
    vGEN_NNF_CONV false (vREAL_INEQ_NORM_CONV,vREAL_INEQ_NORM_DCONV) in
  let vMUL_RULE =
    let rules = vMATCH_MP_RULE pth_mul in
    fun th -> vCONV_RULE(vLAND_CONV vPOLY_MUL_CONV) (rules th)
  and vADD_RULE =
    let rules = vMATCH_MP_RULE pth_add in
    fun th -> vCONV_RULE(vLAND_CONV vPOLY_ADD_CONV) (rules th)
  and vEMUL_RULE =
    let rule = vMATCH_MP pth_emul in
    fun tm th -> vCONV_RULE (vLAND_CONV vPOLY_MUL_CONV)
                           (vSPEC tm (rule th))
  and vSQUARE_RULE t =
    vCONV_RULE (vLAND_CONV vPOLY_MUL_CONV) (vSPEC t pth_square) in
  let hol_of_positivstellensatz(eqs,les,lts) =
    let rec translate prf =
      match prf with
        Axiom_eq n -> el n eqs
      | Axiom_le n -> el n les
      | Axiom_lt n -> el n lts
      | Rational_eq x ->
          vEQT_ELIM(vNUMERIC_EQ_CONV(mk_comb(mk_comb(eq_tm,mk_numeric x),z_tm)))
      | Rational_le x ->
          vEQT_ELIM(vNUMERIC_GE_CONV(mk_comb(mk_comb(ge_tm,mk_numeric x),z_tm)))
      | Rational_lt x ->
          vEQT_ELIM(vNUMERIC_GT_CONV(mk_comb(mk_comb(gt_tm,mk_numeric x),z_tm)))
      | Square t -> vSQUARE_RULE t
      | Eqmul(t,p) -> vEMUL_RULE t (translate p)
      | Sum(p1,p2) -> vADD_RULE (vCONJ (translate p1) (translate p2))
      | Product(p1,p2) -> vMUL_RULE (vCONJ (translate p1) (translate p2)) in
    fun prf ->
      vCONV_RULE(vFIRST_CONV[vNUMERIC_GE_CONV; vNUMERIC_GT_CONV; vNUMERIC_EQ_CONV])
               (translate prf) in
  let init_conv =
    vTOP_DEPTH_CONV vBETA_CONV +--->
    vPRESIMP_CONV +--->
    vNNF_CONV +---> vDEPTH_BINOP_CONV or_tm vCONDS_ELIM_CONV +--->
    vNNF_NORM_CONV +--->
    vSKOLEM_CONV +--->
    vPRENEX_CONV +--->
    vWEAK_DNF_CONV in
  let rec overall dun ths =
    match ths with
      [] ->
        let eq,ne = partition (is_req -| concl) dun in
        let le,nl = partition (is_ge -| concl) ne in
        let lt = filter (is_gt -| concl) nl in
        prover hol_of_positivstellensatz (eq,le,lt)
    | th::oths ->
        let tm = concl th in
        if is_conj tm then
          let th1,th2 = vCONJ_PAIR th in
          overall dun (th1::th2::oths)
        else if is_disj tm then
          let th1 = overall dun (vASSUME (lhand tm)::oths)
          and th2 = overall dun (vASSUME (rand tm)::oths) in
          vDISJ_CASES th th1 th2
        else overall (th::dun) oths in
  fun tm ->
    let vNNF_NORM_CONV' =
      vGEN_NNF_CONV false
        (vCACHE_CONV vREAL_INEQ_NORM_CONV,fun _t -> failwith "") in
    let rec absremover t =
     (vTOP_DEPTH_CONV(absconv1 +---> vBINOP_CONV (vLAND_CONV vPOLY_CONV)) +--->
      vTRY_CONV(absconv2 +---> vNNF_NORM_CONV' +---> vBINOP_CONV absremover)) t in
    let th0 = init_conv(mk_neg tm) in
    let tm0 = rand(concl th0) in
    let th =
      if tm0 = false_tm then fst(vEQ_IMP_RULE th0) else
      let evs,bod = strip_exists tm0 in
      let avs,ibod = strip_forall bod in
      let th1 = itlist vMK_FORALL avs (vDEPTH_BINOP_CONV or_tm absremover ibod) in
      let th2 = overall [] [vSPECL avs (vASSUME(rand(concl th1)))] in
      let th3 =
        itlist vSIMPLE_CHOOSE evs (vPROVE_HYP (vEQ_MP th1 (vASSUME bod)) th2) in
      vDISCH_ALL(vPROVE_HYP (vEQ_MP th0 (vASSUME (mk_neg tm))) th3) in
    vMP (vINST [tm,p_tm] pth_final) th;;

(* ------------------------------------------------------------------------- *)
(* Linear prover. This works over the rationals in general, but is designed  *)
(* to be OK on integers provided the input contains only integers.           *)
(* ------------------------------------------------------------------------- *)

let vREAL_LINEAR_PROVER =
  let linear_add = combine (+/) (fun z -> z =/ num_0)
  and linear_cmul c = mapf (fun x -> c */ x)
  and one_tm = (parse_term "&1") in
  let contradictory p (e,_) =
    (is_undefined e && not(p num_0)) ||
    (dom e = [one_tm] && not(p(apply e one_tm))) in
  let rec linear_ineqs vars (les,lts) =
    try find (contradictory (fun x -> x >/ num_0)) lts with Failure _ ->
    try find (contradictory (fun x -> x >=/ num_0)) les with Failure _ ->
    if vars = [] then failwith "linear_ineqs: no contradiction" else
    let ineqs = les @ lts in
    let blowup v =
      length(filter (fun (e,_) -> tryapplyd e v num_0 >/ num_0) ineqs) *
      length(filter (fun (e,_) -> tryapplyd e v num_0 </ num_0) ineqs) in
    let v =
     fst(hd(sort (fun (_,i) (_,j) -> i < j)
                 (map (fun v -> v,blowup v) vars))) in
    let addup (e1,p1) (e2,p2) acc =
      let c1 = tryapplyd e1 v num_0 and c2 = tryapplyd e2 v num_0 in
      if c1 */ c2 >=/ num_0 then acc else
      let e1' = linear_cmul (abs_num c2) e1
      and e2' = linear_cmul (abs_num c1) e2
      and p1' = Product(Rational_lt(abs_num c2),p1)
      and p2' = Product(Rational_lt(abs_num c1),p2) in
      (linear_add e1' e2',Sum(p1',p2'))::acc in
    let les0,les1 = partition (fun (e,_) -> tryapplyd e v num_0 =/ num_0) les
    and lts0,lts1 = partition (fun (e,_) -> tryapplyd e v num_0 =/ num_0) lts in
    let lesp,lesn = partition (fun (e,_) -> tryapplyd e v num_0 >/ num_0) les1
    and ltsp,ltsn = partition
     (fun (e,_) -> tryapplyd e v num_0 >/ num_0) lts1 in
    let les' = itlist (fun ep1 -> itlist (addup ep1) lesp) lesn les0
    and lts' = itlist (fun ep1 -> itlist (addup ep1) (lesp@ltsp)) ltsn
                      (itlist (fun ep1 -> itlist (addup ep1) (lesn@ltsn)) ltsp
                              lts0) in
    linear_ineqs (subtract vars [v]) (les',lts') in
  let rec linear_eqs(eqs,les,lts) =
    try find (contradictory (fun x -> x =/ num_0)) eqs with Failure _ ->
    match eqs with
      [] -> let vars = subtract
             (itlist (union -| dom -| fst) (les@lts) []) [one_tm] in
            linear_ineqs vars (les,lts)
    | (e,p)::es -> if is_undefined e then linear_eqs(es,les,lts) else
                   let x,c = choose (undefine one_tm e) in
                   let xform(t,q as inp) =
                     let d = tryapplyd t x num_0 in
                     if d =/ num_0 then inp else
                     let k = minus_num d */ abs_num c // c in
                     let e' = linear_cmul k e
                     and t' = linear_cmul (abs_num c) t
                     and p' = Eqmul(term_of_rat k,p)
                     and q' = Product(Rational_lt(abs_num c),q) in
                     linear_add e' t',Sum(p',q') in
                   linear_eqs(map xform es,map xform les,map xform lts) in
  let linear_prover =
   fun (eq,le,lt) ->
    let eqs = map2 (fun p n -> p,Axiom_eq n) eq (0--(length eq-1))
    and les = map2 (fun p n -> p,Axiom_le n) le (0--(length le-1))
    and lts = map2 (fun p n -> p,Axiom_lt n) lt (0--(length lt-1)) in
    linear_eqs(eqs,les,lts) in
  let lin_of_hol =
    let one_tm = (parse_term "&1")
    and zero_tm = (parse_term "&0")
    and add_tm = (parse_term "(+):real->real->real")
    and mul_tm = (parse_term "(*):real->real->real") in
    let rec lin_of_hol tm =
      if tm = zero_tm then undefined
      else if not (is_comb tm) then (tm |=> Int 1)
      else if is_ratconst tm then (one_tm |=> rat_of_term tm) else
      let lop,r = dest_comb tm in
      if not (is_comb lop) then (tm |=> Int 1) else
      let op,l = dest_comb lop in
      if op = add_tm then linear_add (lin_of_hol l) (lin_of_hol r)
      else if op = mul_tm && is_ratconst l then (r |=> rat_of_term l)
      else (tm |=> Int 1) in
    lin_of_hol in
  let is_alien tm =
    match tm with
      Comb(Const("real_of_num",_),n) when not(is_numeral n) -> true
    | _ -> false in
  let n_tm = (parse_term "n:num") in
  let pth = vREWRITE_RULE[vGSYM real_ge] (vSPEC n_tm vREAL_POS) in
  fun translator (eq,le,lt) ->
    let eq_pols = map (lin_of_hol -| lhand -| concl) eq
    and le_pols = map (lin_of_hol -| lhand -| concl) le
    and lt_pols = map (lin_of_hol -| lhand -| concl) lt in
    let aliens =  filter is_alien
      (itlist (union -| dom) (eq_pols @ le_pols @ lt_pols) []) in
    let le_pols' = le_pols @ map (fun v -> (v |=> Int 1)) aliens in
    let _,proof = linear_prover(eq_pols,le_pols',lt_pols) in
    let le' = le @ map (fun a -> vINST [rand a,n_tm] pth) aliens in
    translator (eq,le',lt) proof;;

(* ------------------------------------------------------------------------- *)
(* Bootstrapping REAL_ARITH: trivial abs-elim and only integer constants.    *)
(* ------------------------------------------------------------------------- *)

let vREAL_ARITH =
  let vREAL_POLY_NEG_CONV,vREAL_POLY_ADD_CONV,_vREAL_POLY_SUB_CONV,
    vREAL_POLY_MUL_CONV,_vREAL_POLY_POW_CONV,vREAL_POLY_CONV =
  vSEMIRING_NORMALIZERS_CONV vREAL_POLY_CLAUSES vREAL_POLY_NEG_CLAUSES
   (is_realintconst,
    vREAL_INT_ADD_CONV,vREAL_INT_MUL_CONV,vREAL_INT_POW_CONV)
   (<) in
  let rule =
   vGEN_REAL_ARITH
   (mk_realintconst,
    vREAL_INT_EQ_CONV,vREAL_INT_GE_CONV,vREAL_INT_GT_CONV,
    vREAL_POLY_CONV,vREAL_POLY_NEG_CONV,vREAL_POLY_ADD_CONV,vREAL_POLY_MUL_CONV,
    vNO_CONV,vNO_CONV,vREAL_LINEAR_PROVER)
  and deabs_conv = vREWRITE_CONV[real_abs; real_max; real_min] in
  fun tm ->
    let th1 = deabs_conv tm in
    vEQ_MP (vSYM th1) (rule(rand(concl th1)));;

(* ------------------------------------------------------------------------- *)
(* Slightly less parametrized GEN_REAL_ARITH with more intelligent           *)
(* elimination of abs, max and min hardwired in.                             *)
(* ------------------------------------------------------------------------- *)

let vGEN_REAL_ARITH =
  let vABSMAXMIN_ELIM_CONV1 =
    vGEN_REWRITE_CONV vI [vREAL_ARITH
     (parse_term "(--(&1) * abs(x) >= r <=>\n       --(&1) * x >= r /\\ &1 * x >= r) /\\\n      (--(&1) * abs(x) + a >= r <=>\n       a + --(&1) * x >= r /\\ a + &1 * x >= r) /\\\n      (a + --(&1) * abs(x) >= r <=>\n       a + --(&1) * x >= r /\\ a + &1 * x >= r) /\\\n      (a + --(&1) * abs(x) + b >= r <=>\n       a + --(&1) * x + b >= r /\\ a + &1 * x + b >= r) /\\\n      (a + b + --(&1) * abs(x) >= r <=>\n       a + b + --(&1) * x >= r /\\ a + b + &1 * x >= r) /\\\n      (a + b + --(&1) * abs(x) + c >= r <=>\n       a + b + --(&1) * x + c >= r /\\ a + b + &1 * x + c >= r) /\\\n      (--(&1) * max x y >= r <=>\n       --(&1) * x >= r /\\ --(&1) * y >= r) /\\\n      (--(&1) * max x y + a >= r <=>\n       a + --(&1) * x >= r /\\ a + --(&1) * y >= r) /\\\n      (a + --(&1) * max x y >= r <=>\n       a + --(&1) * x >= r /\\ a + --(&1) * y >= r) /\\\n      (a + --(&1) * max x y + b >= r <=>\n       a + --(&1) * x + b >= r /\\ a + --(&1) * y  + b >= r) /\\\n      (a + b + --(&1) * max x y >= r <=>\n       a + b + --(&1) * x >= r /\\ a + b + --(&1) * y >= r) /\\\n      (a + b + --(&1) * max x y + c >= r <=>\n       a + b + --(&1) * x + c >= r /\\ a + b + --(&1) * y  + c >= r) /\\\n      (&1 * min x y >= r <=>\n       &1 * x >= r /\\ &1 * y >= r) /\\\n      (&1 * min x y + a >= r <=>\n       a + &1 * x >= r /\\ a + &1 * y >= r) /\\\n      (a + &1 * min x y >= r <=>\n       a + &1 * x >= r /\\ a + &1 * y >= r) /\\\n      (a + &1 * min x y + b >= r <=>\n       a + &1 * x + b >= r /\\ a + &1 * y  + b >= r) /\\\n      (a + b + &1 * min x y >= r <=>\n       a + b + &1 * x >= r /\\ a + b + &1 * y >= r) /\\\n      (a + b + &1 * min x y + c >= r <=>\n       a + b + &1 * x + c >= r /\\ a + b + &1 * y  + c >= r) /\\\n      (min x y >= r <=>\n        x >= r /\\  y >= r) /\\\n      (min x y + a >= r <=>\n       a + x >= r /\\ a + y >= r) /\\\n      (a + min x y >= r <=>\n       a + x >= r /\\ a + y >= r) /\\\n      (a + min x y + b >= r <=>\n       a + x + b >= r /\\ a + y  + b >= r) /\\\n      (a + b + min x y >= r <=>\n       a + b + x >= r /\\ a + b + y >= r) /\\\n      (a + b + min x y + c >= r <=>\n       a + b + x + c >= r /\\ a + b + y + c >= r) /\\\n      (--(&1) * abs(x) > r <=>\n       --(&1) * x > r /\\ &1 * x > r) /\\\n      (--(&1) * abs(x) + a > r <=>\n       a + --(&1) * x > r /\\ a + &1 * x > r) /\\\n      (a + --(&1) * abs(x) > r <=>\n       a + --(&1) * x > r /\\ a + &1 * x > r) /\\\n      (a + --(&1) * abs(x) + b > r <=>\n       a + --(&1) * x + b > r /\\ a + &1 * x + b > r) /\\\n      (a + b + --(&1) * abs(x) > r <=>\n       a + b + --(&1) * x > r /\\ a + b + &1 * x > r) /\\\n      (a + b + --(&1) * abs(x) + c > r <=>\n       a + b + --(&1) * x + c > r /\\ a + b + &1 * x + c > r) /\\\n      (--(&1) * max x y > r <=>\n       --(&1) * x > r /\\ --(&1) * y > r) /\\\n      (--(&1) * max x y + a > r <=>\n       a + --(&1) * x > r /\\ a + --(&1) * y > r) /\\\n      (a + --(&1) * max x y > r <=>\n       a + --(&1) * x > r /\\ a + --(&1) * y > r) /\\\n      (a + --(&1) * max x y + b > r <=>\n       a + --(&1) * x + b > r /\\ a + --(&1) * y  + b > r) /\\\n      (a + b + --(&1) * max x y > r <=>\n       a + b + --(&1) * x > r /\\ a + b + --(&1) * y > r) /\\\n      (a + b + --(&1) * max x y + c > r <=>\n       a + b + --(&1) * x + c > r /\\ a + b + --(&1) * y  + c > r) /\\\n      (min x y > r <=>\n        x > r /\\  y > r) /\\\n      (min x y + a > r <=>\n       a + x > r /\\ a + y > r) /\\\n      (a + min x y > r <=>\n       a + x > r /\\ a + y > r) /\\\n      (a + min x y + b > r <=>\n       a + x + b > r /\\ a + y  + b > r) /\\\n      (a + b + min x y > r <=>\n       a + b + x > r /\\ a + b + y > r) /\\\n      (a + b + min x y + c > r <=>\n       a + b + x + c > r /\\ a + b + y + c > r)")]
  and vABSMAXMIN_ELIM_CONV2 =
    let pth_abs = prove
     ((parse_term "P(abs x) <=> (x >= &0 /\\ P x) \\/ (&0 > x /\\ P (--x))"),
      vREWRITE_TAC[real_abs; real_gt; real_ge] ----> vCOND_CASES_TAC ---->
      vASM_REWRITE_TAC[real_lt])
    and pth_max = prove
     ((parse_term "P(max x y) <=> (y >= x /\\ P y) \\/ (x > y /\\ P x)"),
      vREWRITE_TAC[real_max; real_gt; real_ge] ---->
      vCOND_CASES_TAC ----> vASM_REWRITE_TAC[real_lt])
    and pth_min = prove
    ((parse_term "P(min x y) <=> (y >= x /\\ P x) \\/ (x > y /\\ P y)"),
      vREWRITE_TAC[real_min; real_gt; real_ge] ---->
      vCOND_CASES_TAC ----> vASM_REWRITE_TAC[real_lt])
    and abs_tm = (parse_term "real_abs")
    and p_tm = (parse_term "P:real->bool")
    and x_tm = (parse_term "x:real")
    and y_tm = (parse_term "y:real") in
    let is_max = is_binop (parse_term "real_max")
    and is_min = is_binop (parse_term "real_min")
    and is_abs t = is_comb t && rator t = abs_tm in
    let eliminate_construct p c tm =
      let t = find_term (fun t -> p t && free_in t tm) tm in
      let v = genvar(type_of t) in
      let th0 = vSYM(vBETA_CONV(mk_comb(mk_abs(v,subst[v,t] tm),t))) in
      let p,ax = dest_comb(rand(concl th0)) in
      vCONV_RULE(vRAND_CONV(vBINOP_CONV(vRAND_CONV vBETA_CONV)))
               (vTRANS th0 (c p ax)) in
    let elim_abs =
      eliminate_construct is_abs
        (fun p ax -> vINST [p,p_tm; rand ax,x_tm] pth_abs)
    and elim_max =
      eliminate_construct is_max
        (fun p ax -> let ax,y = dest_comb ax in
                     vINST [p,p_tm; rand ax,x_tm; y,y_tm] pth_max)
    and elim_min =
      eliminate_construct is_min
        (fun p ax -> let ax,y = dest_comb ax in
                     vINST [p,p_tm; rand ax,x_tm; y,y_tm] pth_min) in
    vFIRST_CONV [elim_abs; elim_max; elim_min] in
  fun (mkconst,vEQ,vGE,vGT,vNORM,vNEG,vADD,vMUL,vPROVER) ->
        vGEN_REAL_ARITH(mkconst,vEQ,vGE,vGT,vNORM,vNEG,vADD,vMUL,
                       vABSMAXMIN_ELIM_CONV1,vABSMAXMIN_ELIM_CONV2,vPROVER);;

(* ------------------------------------------------------------------------- *)
(* Incorporate that. This gets overwritten again in "calc_rat.ml".           *)
(* ------------------------------------------------------------------------- *)

let vREAL_ARITH =
  let vREAL_POLY_NEG_CONV,vREAL_POLY_ADD_CONV,_vREAL_POLY_SUB_CONV,
    vREAL_POLY_MUL_CONV,_vREAL_POLY_POW_CONV,vREAL_POLY_CONV =
  vSEMIRING_NORMALIZERS_CONV vREAL_POLY_CLAUSES vREAL_POLY_NEG_CLAUSES
   (is_realintconst,
    vREAL_INT_ADD_CONV,vREAL_INT_MUL_CONV,vREAL_INT_POW_CONV)
   (<) in
  vGEN_REAL_ARITH
   (mk_realintconst,
    vREAL_INT_EQ_CONV,vREAL_INT_GE_CONV,vREAL_INT_GT_CONV,
    vREAL_POLY_CONV,vREAL_POLY_NEG_CONV,vREAL_POLY_ADD_CONV,vREAL_POLY_MUL_CONV,
    vREAL_LINEAR_PROVER);;
