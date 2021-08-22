(* ========================================================================= *)
(* Calculation with naturals.                                                *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                (c) Copyright, Mario Carneiro 2020                         *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Parser
open Equal
open Bool
open Drule
open Tactics
open Simp
open Theorems
open Class
open Meson
open Nums
open Arith

(* ------------------------------------------------------------------------- *)
(* Simple rule to get rid of NUMERAL constant.                               *)
(* ------------------------------------------------------------------------- *)

let vDENUMERAL = vGEN_REWRITE_RULE vDEPTH_CONV [vNUMERAL];;

(* ------------------------------------------------------------------------- *)
(* Big collection of rewrites to do trivial arithmetic.                      *)
(*                                                                           *)
(* Note that we have none for DIV and MOD, and that PRE and SUB are a bit    *)
(* inefficient; log(n)^2 instead of log(n).                                  *)
(* ------------------------------------------------------------------------- *)

let vARITH_ZERO = prove
 ((parse_term "(NUMERAL 0 = 0) /\\\n   (BIT0 _0 = _0)"),
  vREWRITE_TAC[vNUMERAL; vBIT0; vDENUMERAL vADD_CLAUSES]);;

let vBIT0_0 = prove
  ((parse_term "BIT0 0 = 0"),
   vREWRITE_TAC [vNUMERAL; vARITH_ZERO]);;

let vBIT1_0 = prove
 ((parse_term "BIT1 0 = 1"),
  vREWRITE_TAC [vNUMERAL]);;

let vARITH_SUC = prove
 ((parse_term "(!n. SUC(NUMERAL n) = NUMERAL(SUC n)) /\\\n   (SUC _0 = BIT1 _0) /\\\n   (!n. SUC (BIT0 n) = BIT1 n) /\\\n   (!n. SUC (BIT1 n) = BIT0 (SUC n))"),
  vREWRITE_TAC[vNUMERAL; vBIT0; vBIT1; vDENUMERAL vADD_CLAUSES]);;

let vARITH_PRE = prove
 ((parse_term "(!n. PRE(NUMERAL n) = NUMERAL(PRE n)) /\\\n   (PRE _0 = _0) /\\\n   (!n. PRE(BIT0 n) = if n = _0 then _0 else BIT1 (PRE n)) /\\\n   (!n. PRE(BIT1 n) = BIT0 n)"),
  vREWRITE_TAC[vNUMERAL; vBIT1; vBIT0; vDENUMERAL vPRE] ----> vINDUCT_TAC ---->
  vREWRITE_TAC[vNUMERAL; vDENUMERAL vPRE; vDENUMERAL vADD_CLAUSES; vDENUMERAL vNOT_SUC;
              vARITH_ZERO]);;

let vARITH_ADD = prove
 ((parse_term "(!m n. NUMERAL(m) + NUMERAL(n) = NUMERAL(m + n)) /\\\n   (_0 + _0 = _0) /\\\n   (!n. _0 + BIT0 n = BIT0 n) /\\\n   (!n.        _0 + BIT1 n = BIT1 n) /\\\n   (!n.   BIT0 n + _0 = BIT0 n) /\\\n   (!n.   BIT1 n + _0 = BIT1 n) /\\\n   (!m n. BIT0 m + BIT0 n = BIT0 (m + n)) /\\\n   (!m n. BIT0 m + BIT1 n = BIT1 (m + n)) /\\\n   (!m n. BIT1 m + BIT0 n = BIT1 (m + n)) /\\\n   (!m n. BIT1 m + BIT1 n = BIT0 (SUC(m + n)))"),
  vPURE_REWRITE_TAC[vNUMERAL; vBIT0; vBIT1; vDENUMERAL vADD_CLAUSES; vSUC_INJ] ---->
  vREWRITE_TAC[vADD_AC]);;

let vARITH_MULT = prove
 ((parse_term "(!m n. NUMERAL(m) * NUMERAL(n) = NUMERAL(m * n)) /\\\n   (_0 * _0 = _0) /\\\n   (!n. _0 * BIT0 n = _0) /\\\n   (!n. _0 * BIT1 n = _0) /\\\n   (!n. BIT0 n * _0 = _0) /\\\n   (!n. BIT1 n * _0 = _0) /\\\n   (!m n. BIT0 m * BIT0 n = BIT0 (BIT0 (m * n))) /\\\n   (!m n. BIT0 m * BIT1 n = BIT0 m + BIT0 (BIT0 (m * n))) /\\\n   (!m n. BIT1 m * BIT0 n = BIT0 n + BIT0 (BIT0 (m * n))) /\\\n   (!m n. BIT1 m * BIT1 n = BIT1 m + BIT0 n + BIT0 (BIT0 (m * n)))"),
  vPURE_REWRITE_TAC[vNUMERAL; vBIT0; vBIT1; vDENUMERAL vMULT_CLAUSES;
                   vDENUMERAL vADD_CLAUSES; vSUC_INJ] ---->
  vREWRITE_TAC[vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB; vADD_AC]);;

let vARITH_EXP = prove
 ((parse_term "(!m n. (NUMERAL m) EXP (NUMERAL n) = NUMERAL(m EXP n)) /\\\n   (_0 EXP _0 = BIT1 _0) /\\\n   (!m. (BIT0 m) EXP _0 = BIT1 _0) /\\\n   (!m. (BIT1 m) EXP _0 = BIT1 _0) /\\\n   (!n. _0 EXP (BIT0 n) = (_0 EXP n) * (_0 EXP n)) /\\\n   (!m n. (BIT0 m) EXP (BIT0 n) = ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\\\n   (!m n. (BIT1 m) EXP (BIT0 n) = ((BIT1 m) EXP n) * ((BIT1 m) EXP n)) /\\\n   (!n. _0 EXP (BIT1 n) = _0) /\\\n   (!m n. (BIT0 m) EXP (BIT1 n) =\n        BIT0 m * ((BIT0 m) EXP n) * ((BIT0 m) EXP n)) /\\\n   (!m n. (BIT1 m) EXP (BIT1 n) =\n        BIT1 m * ((BIT1 m) EXP n) * ((BIT1 m) EXP n))"),
  vREWRITE_TAC[vNUMERAL] ----> vREPEAT vSTRIP_TAC ---->
  vTRY(vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vBIT0; vBIT1]) ---->
  vREWRITE_TAC[vDENUMERAL vEXP; vDENUMERAL vMULT_CLAUSES; vEXP_ADD]);;

let vARITH_EVEN = prove
 ((parse_term "(!n. EVEN(NUMERAL n) <=> EVEN n) /\\\n   (EVEN _0 <=> T) /\\\n   (!n. EVEN(BIT0 n) <=> T) /\\\n   (!n. EVEN(BIT1 n) <=> F)"),
  vREWRITE_TAC[vNUMERAL; vBIT1; vBIT0; vDENUMERAL vEVEN; vEVEN_ADD]);;

let vARITH_ODD = prove
 ((parse_term "(!n. ODD(NUMERAL n) <=> ODD n) /\\\n   (ODD _0 <=> F) /\\\n   (!n. ODD(BIT0 n) <=> F) /\\\n   (!n. ODD(BIT1 n) <=> T)"),
  vREWRITE_TAC[vNUMERAL; vBIT1; vBIT0; vDENUMERAL vODD; vODD_ADD]);;

let vARITH_LE = prove
 ((parse_term "(!m n. NUMERAL m <= NUMERAL n <=> m <= n) /\\\n   ((_0 <= _0) <=> T) /\\\n   (!n. (BIT0 n <= _0) <=> n <= _0) /\\\n   (!n. (BIT1 n <= _0) <=> F) /\\\n   (!n. (_0 <= BIT0 n) <=> T) /\\\n   (!n. (_0 <= BIT1 n) <=> T) /\\\n   (!m n. (BIT0 m <= BIT0 n) <=> m <= n) /\\\n   (!m n. (BIT0 m <= BIT1 n) <=> m <= n) /\\\n   (!m n. (BIT1 m <= BIT0 n) <=> m < n) /\\\n   (!m n. (BIT1 m <= BIT1 n) <=> m <= n)"),
  vREWRITE_TAC[vNUMERAL; vBIT1; vBIT0; vDENUMERAL vNOT_SUC;
      vDENUMERAL(vGSYM vNOT_SUC); vSUC_INJ] ---->
  vREWRITE_TAC[vDENUMERAL vLE_0] ----> vREWRITE_TAC[vDENUMERAL vLE; vGSYM vMULT_2] ---->
  vREWRITE_TAC[vLE_MULT_LCANCEL; vSUC_INJ;
              vDENUMERAL vMULT_EQ_0; vDENUMERAL vNOT_SUC] ---->
  vREWRITE_TAC[vDENUMERAL vNOT_SUC] ----> vREWRITE_TAC[vLE_SUC_LT] ---->
  vREWRITE_TAC[vLT_MULT_LCANCEL] ---->
  vSUBGOAL_THEN (parse_term "2 = SUC 1") (fun th -> vREWRITE_TAC[th]) ++-->
   [vREWRITE_TAC[vNUMERAL; vBIT0; vBIT1; vDENUMERAL vADD_CLAUSES];
    vREWRITE_TAC[vDENUMERAL vNOT_SUC; vNOT_SUC; vEQ_MULT_LCANCEL] ---->
    vREWRITE_TAC[vONCE_REWRITE_RULE[vDISJ_SYM] vLE_LT] ---->
    vMAP_EVERY vX_GEN_TAC [(parse_term "m:num"); (parse_term "n:num")] ---->
    vSUBGOAL_THEN (parse_term "~(SUC 1 * m = SUC (SUC 1 * n))")
      (fun th -> vREWRITE_TAC[th]) ---->
    vDISCH_THEN(vMP_TAC -| vAP_TERM (parse_term "EVEN")) ---->
    vREWRITE_TAC[vEVEN_MULT; vEVEN_ADD; vNUMERAL; vBIT1; vEVEN]]);;

let vARITH_LT = prove
 ((parse_term "(!m n. NUMERAL m < NUMERAL n <=> m < n) /\\\n   ((_0 < _0) <=> F) /\\\n   (!n. (BIT0 n < _0) <=> F) /\\\n   (!n. (BIT1 n < _0) <=> F) /\\\n   (!n. (_0 < BIT0 n) <=> _0 < n) /\\\n   (!n. (_0 < BIT1 n) <=> T) /\\\n   (!m n. (BIT0 m < BIT0 n) <=> m < n) /\\\n   (!m n. (BIT0 m < BIT1 n) <=> m <= n) /\\\n   (!m n. (BIT1 m < BIT0 n) <=> m < n) /\\\n   (!m n. (BIT1 m < BIT1 n) <=> m < n)"),
  vREWRITE_TAC[vNUMERAL; vGSYM vNOT_LE; vARITH_LE] ---->
  vREWRITE_TAC[vDENUMERAL vLE]);;

let vARITH_GE = vREWRITE_RULE[vGSYM vGE; vGSYM vGT] vARITH_LE;;

let vARITH_GT = vREWRITE_RULE[vGSYM vGE; vGSYM vGT] vARITH_LT;;

let vARITH_EQ = prove
 ((parse_term "(!m n. (NUMERAL m = NUMERAL n) <=> (m = n)) /\\\n   ((_0 = _0) <=> T) /\\\n   (!n. (BIT0 n = _0) <=> (n = _0)) /\\\n   (!n. (BIT1 n = _0) <=> F) /\\\n   (!n. (_0 = BIT0 n) <=> (_0 = n)) /\\\n   (!n. (_0 = BIT1 n) <=> F) /\\\n   (!m n. (BIT0 m = BIT0 n) <=> (m = n)) /\\\n   (!m n. (BIT0 m = BIT1 n) <=> F) /\\\n   (!m n. (BIT1 m = BIT0 n) <=> F) /\\\n   (!m n. (BIT1 m = BIT1 n) <=> (m = n))"),
  vREWRITE_TAC[vNUMERAL; vGSYM vLE_ANTISYM; vARITH_LE] ---->
  vREWRITE_TAC[vLET_ANTISYM; vLTE_ANTISYM; vDENUMERAL vLE_0]);;

let vARITH_SUB = prove
 ((parse_term "(!m n. NUMERAL m - NUMERAL n = NUMERAL(m - n)) /\\\n   (_0 - _0 = _0) /\\\n   (!n. _0 - BIT0 n = _0) /\\\n   (!n. _0 - BIT1 n = _0) /\\\n   (!n. BIT0 n - _0 = BIT0 n) /\\\n   (!n. BIT1 n - _0 = BIT1 n) /\\\n   (!m n. BIT0 m - BIT0 n = BIT0 (m - n)) /\\\n   (!m n. BIT0 m - BIT1 n = PRE(BIT0 (m - n))) /\\\n   (!m n. BIT1 m - BIT0 n = if n <= m then BIT1 (m - n) else _0) /\\\n   (!m n. BIT1 m - BIT1 n = BIT0 (m - n))"),
  vREWRITE_TAC[vNUMERAL; vDENUMERAL vSUB_0] ----> vPURE_REWRITE_TAC[vBIT0; vBIT1] ---->
  vREWRITE_TAC[vGSYM vMULT_2; vSUB_SUC; vLEFT_SUB_DISTRIB] ---->
  vREWRITE_TAC[vSUB] ----> vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vREWRITE_TAC[vDENUMERAL vSUB_EQ_0] ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vNOT_LE]) ---->
  vASM_REWRITE_TAC[vLE_SUC_LT; vLT_MULT_LCANCEL; vARITH_EQ] ---->
  vPOP_ASSUM(vCHOOSE_THEN vSUBST1_TAC -| vREWRITE_RULE[vLE_EXISTS]) ---->
  vREWRITE_TAC[vADD1; vLEFT_ADD_DISTRIB] ---->
  vREWRITE_TAC[vADD_SUB2; vGSYM vADD_ASSOC]);;

let vARITH = end_itlist vCONJ
  [vARITH_ZERO; vARITH_SUC; vARITH_PRE;
   vARITH_ADD; vARITH_MULT; vARITH_EXP;
   vARITH_EVEN; vARITH_ODD;
   vARITH_EQ; vARITH_LE; vARITH_LT; vARITH_GE; vARITH_GT;
   vARITH_SUB];;

let vEXP_2_NE_0 = prove
 ((parse_term "!n. ~(2 EXP n = 0)"),
  vREWRITE_TAC [vEXP_EQ_0; vARITH_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Now more delicate conversions for situations where efficiency matters.    *)
(* ------------------------------------------------------------------------- *)
open Num

let vNUM_EVEN_CONV =
  let tth,rths = vCONJ_PAIR vARITH_EVEN in
  vGEN_REWRITE_CONV vI [tth] +---> vGEN_REWRITE_CONV vI [rths];;

let vNUM_ODD_CONV =
  let tth,rths = vCONJ_PAIR vARITH_ODD in
  vGEN_REWRITE_CONV vI [tth] +---> vGEN_REWRITE_CONV vI [rths];;

let vNUM_SUC_CONV,vNUM_ADD_CONV,vNUM_MULT_CONV,vNUM_EXP_CONV,
    vNUM_LT_CONV,vNUM_LE_CONV,vNUM_EQ_CONV =
  let num_ty = type_of(lhand(concl vZERO_DEF)) in
  let vNUMERAL_tm,vBIT0_tm,vBIT1_tm,zero_tm =
    match mk_small_numeral 2 with Comb(vNUMERAL_tm,Comb(vBIT0_tm,Comb(vBIT1_tm,zero_tm))) -> vNUMERAL_tm, vBIT0_tm, vBIT1_tm, zero_tm
    | _ -> assert false
  and suc_tm = rator(rand(concl vTWO))
  and one_tm = rand(mk_small_numeral 1)
  and add_tm = rator(rator(lhand(snd(strip_forall(concl vADD_0)))))
  and mul_tm = rator(rator(rand(snd(strip_forall(concl vEXP_2)))))
  and exp_tm = rator(rator(lhand(snd(strip_forall(concl vEXP_2)))))
  and eq_tm = rator(rator(concl vTWO)) in
  let num_0 = Int 0 and num_1 = Int 1 and num_2 = Int 2 in
  let a_tm = mk_var("a",num_ty)
  and b_tm = mk_var("b",num_ty)
  and c_tm = mk_var("c",num_ty)
  and d_tm = mk_var("d",num_ty)
  and e_tm = mk_var("e",num_ty)
  and h_tm = mk_var("h",num_ty)
  and l_tm = mk_var("l",num_ty)
  and m_tm = mk_var("m",num_ty)
  and n_tm = mk_var("n",num_ty)
  and p_tm = mk_var("p",num_ty) in
  let vSTANDARDIZE =
    let ilist = [vBIT0_tm,vBIT0_tm; vBIT1_tm,vBIT1_tm; zero_tm,zero_tm;
                 suc_tm,suc_tm; add_tm,add_tm; mul_tm,mul_tm;
                 exp_tm,exp_tm; eq_tm,eq_tm; vNUMERAL_tm,vNUMERAL_tm;
                 a_tm,a_tm; b_tm,b_tm; c_tm,c_tm; d_tm,d_tm; e_tm,e_tm;
                 h_tm,h_tm; l_tm,l_tm; m_tm,m_tm; n_tm,n_tm; p_tm,p_tm] in
    let rec replace tm =
      match tm with
        Var(_,_) | Const(_,_) -> rev_assocd tm ilist tm
      | Comb(s,t) -> mk_comb(replace s,replace t)
      | Abs(_,_) -> failwith "replace" in
    fun th -> let tm' = replace (concl th) in vEQ_MP (vREFL tm') th in
  let vREFL_bit0 = vSTANDARDIZE(vREFL vBIT0_tm)
  and vREFL_bit1 = vSTANDARDIZE(vREFL vBIT1_tm) in
  let vAP_BIT0 th = vMK_COMB(vREFL_bit0,th)
  and vAP_BIT1 th = vMK_COMB(vREFL_bit1,th)
  and vQUICK_PROVE_HYP ath bth = vEQ_MP (vDEDUCT_ANTISYM_RULE ath bth) ath in
  let rec dest_raw_numeral tm =
    match tm with
      Comb(Const("BIT1",_),t) -> num_2 */ dest_raw_numeral t +/ num_1
    | Comb(Const("BIT0",_),t) -> num_2 */ dest_raw_numeral t
    | Const("_0",_) -> num_0 | _ -> assert false in
  let bitcounts =
    let rec bctr w z tm =
      match tm with
        Const("_0",_) -> (w,z)
      | Comb(Const("BIT0",_),t) -> bctr w (z + 1) t
      | Comb(Const("BIT1",_),t) -> bctr (w + 1) z t
      | _ -> failwith "malformed numeral" in
    bctr 0 0 in
  let rec wellformed tm =
    match tm with
      Const("_0",_) -> true
    | Comb(Const("BIT0",_),t)|Comb(Const("BIT1",_),t) -> wellformed t
    | _ -> false in
  let rec orderrelation mtm ntm =
    if mtm == ntm then
      if wellformed mtm then 0 else failwith "orderrelation"
    else
      match (mtm,ntm) with
        Const("_0",_),Const("_0",_) -> 0
      | Const("_0",_),_ ->
           if wellformed ntm then -1 else failwith "orderrelation"
      | _, Const("_0",_) ->
           if wellformed ntm then 1 else failwith "orderrelation"
      | Comb(Const("BIT0",_),mt),Comb(Const("BIT0",_),nt)
      | Comb(Const("BIT1",_),mt),Comb(Const("BIT1",_),nt) ->
          orderrelation mt nt
      | Comb(Const("BIT0",_),mt),Comb(Const("BIT1",_),nt) ->
          if orderrelation mt nt > 0 then 1 else -1
      | Comb(Const("BIT1",_),mt),Comb(Const("BIT0",_),nt) ->
          if orderrelation mt nt < 0 then -1 else 1
      | _ -> assert false in
  let doublebn tm = if tm = zero_tm then tm else mk_comb(vBIT0_tm,tm) in
  let rec subbn mtm ntm =
    match (mtm,ntm) with
      (_,Const("_0",_)) -> mtm
    | (Comb(Const("BIT0",_),mt),Comb(Const("BIT0",_),nt)) ->
          doublebn (subbn mt nt)
    | (Comb(Const("BIT1",_),mt),Comb(Const("BIT1",_),nt)) ->
          doublebn (subbn mt nt)
    | (Comb(Const("BIT1",_),mt),Comb(Const("BIT0",_),nt)) ->
          mk_comb(vBIT1_tm,subbn mt nt)
    | (Comb(Const("BIT0",_),mt),Comb(Const("BIT1",_),nt)) ->
          mk_comb(vBIT1_tm,sbcbn mt nt)
    | _ -> failwith "malformed numeral or wrong relation"
  and sbcbn mtm ntm =
    match (mtm,ntm) with
    | (Comb(Const("BIT0",_),mt),Const("_0",_)) ->
          mk_comb(vBIT1_tm,sbcbn mt ntm)
    | (Comb(Const("BIT1",_),mt),Const("_0",_)) ->
          doublebn mt
    | (Comb(Const("BIT0",_),mt),Comb(Const("BIT0",_),nt)) ->
          mk_comb(vBIT1_tm,sbcbn mt nt)
    | (Comb(Const("BIT1",_),mt),Comb(Const("BIT1",_),nt)) ->
          mk_comb(vBIT1_tm,sbcbn mt nt)
    | (Comb(Const("BIT1",_),mt),Comb(Const("BIT0",_),nt)) ->
          doublebn (subbn mt nt)
    | (Comb(Const("BIT0",_),mt),Comb(Const("BIT1",_),nt)) ->
          doublebn (sbcbn mt nt)
    | _ -> failwith "malformed numeral or wrong relation" in
  let topsplit tm =
    match tm with
     Const("_0",_) -> 0,zero_tm
   | Comb(Const("BIT1",_),Const("_0",_)) -> 1,zero_tm
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Const("_0",_))) -> 2,zero_tm
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Const("_0",_))) -> 3,zero_tm
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Const("_0",_)))) -> 4,zero_tm
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Const("_0",_)))) -> 5,zero_tm
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Const("_0",_)))) -> 6,zero_tm
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Const("_0",_)))) -> 7,zero_tm
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),n)))) -> 0,n
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),n)))) -> 1,n
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),n)))) -> 2,n
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),n)))) -> 3,n
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),n)))) -> 4,n
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),n)))) -> 5,n
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),n)))) -> 6,n
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),n)))) -> 7,n
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),n)))) -> 8,n
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),n)))) -> 9,n
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),n)))) -> 10,n
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),n)))) -> 11,n
   | Comb(Const("BIT0",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),n)))) -> 12,n
   | Comb(Const("BIT1",_),Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),n)))) -> 13,n
   | Comb(Const("BIT0",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),n)))) -> 14,n
   | Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),Comb(Const("BIT1",_),n)))) -> 15,n
   | _ -> failwith "malformed numeral" in
  let vNUM_ADD_RULE,vNUM_ADC_RULE =
    let rec mk_compnumeral k base =
      if k = 0 then base else
      let t = mk_compnumeral (k / 2) base in
      if k mod 2 = 1 then mk_comb(vBIT1_tm,t) else mk_comb(vBIT0_tm,t) in
    let bases v =
        let part2 = map (fun k -> mk_compnumeral k v) (8--15) in
        let part1 = map (subst[mk_comb(vBIT0_tm,v),mk_comb(vBIT1_tm,v)])
                        part2
        and part0 = map (fun k -> mk_compnumeral k zero_tm) (0--15) in
        part0 @ part1 @ part2 in
    let starts =
      allpairs (fun mtm ntm ->
        mk_comb(mk_comb(add_tm,mtm),ntm)) (bases m_tm) (bases n_tm) in
    let vBITS_INJ = (vSTANDARDIZE -| prove)
     ((parse_term "(BIT0 m = BIT0 n <=> m = n) /\\\n       (BIT1 m = BIT1 n <=> m = n)"),
      vREWRITE_TAC[vBIT0; vBIT1] ---->
      vREWRITE_TAC[vGSYM vMULT_2] ---->
      vREWRITE_TAC[vSUC_INJ; vEQ_MULT_LCANCEL; vARITH_EQ]) in
    let vARITH_0 = (vSTANDARDIZE -| vMESON[vNUMERAL; vADD_CLAUSES])
      (parse_term "m + _0 = m /\\ _0 + n = n") in
    let patadj = subst[(parse_term "SUC(m + _0)"),(parse_term "SUC m"); (parse_term "SUC(_0 + n)"),(parse_term "SUC n")] in
    let mkclauses sucflag t =
      let tm = if sucflag then mk_comb(suc_tm,t) else t in
      let th1 = vPURE_REWRITE_CONV[vARITH_ADD; vARITH_SUC; vARITH_0] tm in
      let tm1 = patadj(rand(concl th1)) in
      if not(free_in add_tm tm1) then th1,
         (if free_in m_tm tm1 then 0 else 1) else
      let ptm = rand(rand(rand(rand tm1))) in
      let tmc = mk_eq(mk_eq(ptm,p_tm),mk_eq(tm,subst[p_tm,ptm] tm1)) in
      vEQT_ELIM(vREWRITE_CONV[vARITH_ADD; vARITH_SUC; vARITH_0; vBITS_INJ] tmc),
      (if free_in suc_tm tm1 then 3 else 2) in
    let add_clauses,add_flags =
      let l1,l2 = unzip(map (mkclauses false) starts) in
      Array.of_list(map vSTANDARDIZE l1),Array.of_list l2 in
    let adc_clauses,adc_flags =
      let l1,l2 = unzip(map (mkclauses true) starts) in
      Array.of_list(map vSTANDARDIZE l1),Array.of_list l2 in
    let rec vNUM_ADD_RULE mtm ntm =
      let m_lo,m_hi = topsplit mtm
      and n_lo,n_hi = topsplit ntm in
      let m_ind = if m_hi = zero_tm then m_lo else m_lo + 16
      and n_ind = if n_hi = zero_tm then n_lo else n_lo + 16 in
      let ind = 32 * m_ind + n_ind in
      let th1 = Array.get add_clauses ind
      and fl = Array.get add_flags ind in
      match fl with
        0 -> vINST [m_hi,m_tm] th1
      | 1 -> vINST [n_hi,n_tm] th1
      | 2 -> let th2 = vNUM_ADD_RULE m_hi n_hi in
             (match concl th2 with Comb(_,ptm) ->
              let th3 = vINST [m_hi,m_tm; n_hi,n_tm;ptm,p_tm] th1 in
              vEQ_MP th3 th2 | _ -> assert false)
      | 3 -> let th2 = vNUM_ADC_RULE m_hi n_hi in
             (match concl th2 with Comb(_,ptm) ->
              let th3 = vINST [m_hi,m_tm; n_hi,n_tm;ptm,p_tm] th1 in
              vEQ_MP th3 th2 | _ -> assert false)
      | _ -> assert false
    and vNUM_ADC_RULE mtm ntm =
      let m_lo,m_hi = topsplit mtm
      and n_lo,n_hi = topsplit ntm in
      let m_ind = if m_hi = zero_tm then m_lo else m_lo + 16
      and n_ind = if n_hi = zero_tm then n_lo else n_lo + 16 in
      let ind = 32 * m_ind + n_ind in
      let th1 = Array.get adc_clauses ind
      and fl = Array.get adc_flags ind in
      match fl with
        0 -> vINST [m_hi,m_tm] th1
      | 1 -> vINST [n_hi,n_tm] th1
      | 2 -> let th2 = vNUM_ADD_RULE m_hi n_hi in
             (match concl th2 with Comb(_,ptm) ->
              let th3 = vINST [m_hi,m_tm; n_hi,n_tm;ptm,p_tm] th1 in
              vEQ_MP th3 th2 | _ -> assert false)
      | 3 -> let th2 = vNUM_ADC_RULE m_hi n_hi in
             (match concl th2 with Comb(_,ptm) ->
              let th3 = vINST [m_hi,m_tm; n_hi,n_tm;ptm,p_tm] th1 in
              vEQ_MP th3 th2 | _ -> assert false) 
      | _ -> assert false in
    vNUM_ADD_RULE,vNUM_ADC_RULE in
  let vNUM_SHIFT_CONV =
    let pth_0 = (vSTANDARDIZE -| prove)
     ((parse_term "(n = a + p * b <=> BIT0 n = BIT0 a + BIT0 p * b)"),
      vREWRITE_TAC[vBIT0; vBIT1] ---->
      vREWRITE_TAC[vGSYM vMULT_2; vGSYM vMULT_ASSOC; vGSYM vLEFT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vEQ_MULT_LCANCEL; vARITH_EQ])
    and pth_z = (vSTANDARDIZE -| prove)
     ((parse_term "n = _0 + p * b <=> BIT0 n = _0 + BIT0 p * b"),
      vSUBST1_TAC(vSYM(vSPEC (parse_term "_0") vNUMERAL)) ---->
      vREWRITE_TAC[vBIT1; vBIT0] ---->
      vREWRITE_TAC[vADD_CLAUSES; vGSYM vMULT_2] ---->
      vREWRITE_TAC[vGSYM vMULT_ASSOC; vEQ_MULT_LCANCEL; vARITH_EQ])
    and pth_1 = (vSTANDARDIZE -| prove)
     ((parse_term "(n = a + p * b <=> BIT1 n = BIT1 a + BIT0 p * b)"),
      vREWRITE_TAC[vBIT0; vBIT1] ---->
      vREWRITE_TAC[vGSYM vMULT_2; vGSYM vMULT_ASSOC; vGSYM vLEFT_ADD_DISTRIB;
                  vADD_CLAUSES; vSUC_INJ] ---->
      vREWRITE_TAC[vEQ_MULT_LCANCEL; vARITH_EQ])
    and pth_base = (vSTANDARDIZE -| prove)
     ((parse_term "n = _0 + BIT1 _0 * n"),
      vMESON_TAC[vADD_CLAUSES; vMULT_CLAUSES; vNUMERAL])
    and pth_triv = (vSTANDARDIZE -| prove)
     ((parse_term "_0 = a + p * b <=> _0 = a + BIT0 p * b"),
      vCONV_TAC(vBINOP_CONV vSYM_CONV) ---->
      vSUBST1_TAC(vSYM(vSPEC (parse_term "_0") vNUMERAL)) ---->
      vREWRITE_TAC[vADD_EQ_0; vMULT_EQ_0; vBIT0])
    and pths_1 = (Array.of_list -| vCONJUNCTS -| vSTANDARDIZE -| prove)
     ((parse_term "(n = a + p * b <=>\n        BIT0(BIT0(BIT0(BIT0 n))) =\n        BIT0(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT1(BIT0(BIT0(BIT0 n))) =\n        BIT1(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT0(BIT1(BIT0(BIT0 n))) =\n        BIT0(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT1(BIT1(BIT0(BIT0 n))) =\n        BIT1(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT0(BIT0(BIT1(BIT0 n))) =\n        BIT0(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT1(BIT0(BIT1(BIT0 n))) =\n        BIT1(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT0(BIT1(BIT1(BIT0 n))) =\n        BIT0(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT1(BIT1(BIT1(BIT0 n))) =\n        BIT1(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT0(BIT0(BIT0(BIT1 n))) =\n        BIT0(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT1(BIT0(BIT0(BIT1 n))) =\n        BIT1(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT0(BIT1(BIT0(BIT1 n))) =\n        BIT0(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT1(BIT1(BIT0(BIT1 n))) =\n        BIT1(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT0(BIT0(BIT1(BIT1 n))) =\n        BIT0(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT1(BIT0(BIT1(BIT1 n))) =\n        BIT1(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT0(BIT1(BIT1(BIT1 n))) =\n        BIT0(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = a + p * b <=>\n        BIT1(BIT1(BIT1(BIT1 n))) =\n        BIT1(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b)"),
      vMP_TAC(vREWRITE_RULE[vGSYM vMULT_2] vBIT0) ---->
      vMP_TAC(vREWRITE_RULE[vGSYM vMULT_2] vBIT1) ---->
      vABBREV_TAC (parse_term "two = 2") ---->
      vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
      vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
      vFIRST_X_ASSUM(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vADD_CLAUSES; vSUC_INJ; vEQ_MULT_LCANCEL; vARITH_EQ;
                  vGSYM vLEFT_ADD_DISTRIB; vGSYM vMULT_ASSOC])
    and pths_0 = (Array.of_list -| vCONJUNCTS -| vSTANDARDIZE -| prove)
     ((parse_term "(n = _0 + p * b <=>\n        BIT0(BIT0(BIT0(BIT0 n))) =\n        _0 + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT1(BIT0(BIT0(BIT0 n))) =\n        BIT1 _0 + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT0(BIT1(BIT0(BIT0 n))) =\n        BIT0(BIT1 _0) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT1(BIT1(BIT0(BIT0 n))) =\n        BIT1(BIT1 _0) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT0(BIT0(BIT1(BIT0 n))) =\n        BIT0(BIT0(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT1(BIT0(BIT1(BIT0 n))) =\n        BIT1(BIT0(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT0(BIT1(BIT1(BIT0 n))) =\n        BIT0(BIT1(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT1(BIT1(BIT1(BIT0 n))) =\n        BIT1(BIT1(BIT1 _0)) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT0(BIT0(BIT0(BIT1 n))) =\n        BIT0(BIT0(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT1(BIT0(BIT0(BIT1 n))) =\n        BIT1(BIT0(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT0(BIT1(BIT0(BIT1 n))) =\n        BIT0(BIT1(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT1(BIT1(BIT0(BIT1 n))) =\n        BIT1(BIT1(BIT0(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT0(BIT0(BIT1(BIT1 n))) =\n        BIT0(BIT0(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT1(BIT0(BIT1(BIT1 n))) =\n        BIT1(BIT0(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT0(BIT1(BIT1(BIT1 n))) =\n        BIT0(BIT1(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b) /\\\n       (n = _0 + p * b <=>\n        BIT1(BIT1(BIT1(BIT1 n))) =\n        BIT1(BIT1(BIT1(BIT1 _0))) + BIT0(BIT0(BIT0(BIT0 p))) * b)"),
      vSUBST1_TAC(vMESON[vNUMERAL] (parse_term "_0 = 0")) ---->
      vMP_TAC(vREWRITE_RULE[vGSYM vMULT_2] vBIT0) ---->
      vMP_TAC(vREWRITE_RULE[vGSYM vMULT_2] vBIT1) ---->
      vABBREV_TAC (parse_term "two = 2") ---->
      vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
      vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
      vFIRST_X_ASSUM(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vADD_CLAUSES; vSUC_INJ; vEQ_MULT_LCANCEL; vARITH_EQ;
                  vGSYM vLEFT_ADD_DISTRIB; vGSYM vMULT_ASSOC]) in
    let rec vNUM_SHIFT_CONV k tm =
      if k <= 0 then vINST [tm,n_tm] pth_base else
      match tm with
        Comb(_,Comb(_,Comb(_,Comb(_,_)))) when k >= 4 ->
          let i,ntm = topsplit tm in
          let th1 = vNUM_SHIFT_CONV (k - 4) ntm in
          (match concl th1 with
               Comb(_,Comb(Comb(_,Const("_0",_)),Comb(Comb(_,ptm),btm))) ->
                  let th2 = Array.get pths_0 i in
                  let th3 = vINST [ntm,n_tm; btm,b_tm; ptm,p_tm] th2 in
                  vEQ_MP th3 th1
             | Comb(_,Comb(Comb(_,atm),Comb(Comb(_,ptm),btm))) ->
                  let th2 = Array.get pths_1 i in
                  let th3 = vINST[ntm,n_tm; atm,a_tm; btm,b_tm; ptm,p_tm] th2 in
                  vEQ_MP th3 th1 | _ -> assert false)
      | Comb(Const("BIT0",_),ntm) ->
            let th1 = vNUM_SHIFT_CONV (k - 1) ntm in
            (match concl th1 with
               Comb(_,Comb(Comb(_,Const("_0",_)),Comb(Comb(_,ptm),btm))) ->
                 vEQ_MP (vINST [ntm,n_tm; btm,b_tm; ptm,p_tm] pth_z) th1
             | Comb(_,Comb(Comb(_,atm),Comb(Comb(_,ptm),btm))) ->
                 vEQ_MP
                  (vINST[ntm,n_tm; atm,a_tm; btm,b_tm; ptm,p_tm] pth_0) th1 | _ -> assert false)
      | Comb(Const("BIT1",_),ntm) ->
            let th1 = vNUM_SHIFT_CONV (k - 1) ntm in
            (match concl th1 with
               Comb(_,Comb(Comb(_,atm),Comb(Comb(_,ptm),btm))) ->
                 vEQ_MP
                  (vINST [ntm,n_tm; atm,a_tm; btm,b_tm; ptm,p_tm] pth_1) th1 | _ -> assert false)
      | Const("_0",_) ->
            let th1 = vNUM_SHIFT_CONV (k - 1) tm in
            (match concl th1 with
               Comb(_,Comb(Comb(_,atm),Comb(Comb(_,ptm),btm))) ->
                 vEQ_MP (vINST [atm,a_tm; btm,b_tm; ptm,p_tm] pth_triv)
                       th1 | _ -> assert false)
      | _ -> failwith "malformed numeral" in
    vNUM_SHIFT_CONV in
  let vNUM_UNSHIFT_CONV =
    let pth_triv = (vSTANDARDIZE -| prove)
     ((parse_term "a + p * _0 = a"),
      vSUBST1_TAC(vSYM(vSPEC (parse_term "_0") vNUMERAL)) ---->
      vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES])
    and pth_base = (vSTANDARDIZE -| prove)
     ((parse_term "a + BIT1 _0 * b = a + b"),
      vSUBST1_TAC(vSYM(vSPEC (parse_term "BIT1 _0") vNUMERAL)) ---->
      vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES])
    and pth_0 = (vSTANDARDIZE -| prove)
     ((parse_term "BIT0 a + BIT0 p * b = BIT0(a + p * b)"),
      vREWRITE_TAC[vBIT0] ----> vREWRITE_TAC[vGSYM vMULT_2] ---->
      vREWRITE_TAC[vGSYM vMULT_ASSOC; vGSYM vLEFT_ADD_DISTRIB])
    and pth_1 = (vSTANDARDIZE -| prove)
     ((parse_term "BIT1 a + BIT0 p * b = BIT1(a + p * b)"),
      vREWRITE_TAC[vBIT0; vBIT1] ----> vREWRITE_TAC[vGSYM vMULT_2] ---->
      vREWRITE_TAC[vADD_CLAUSES; vSUC_INJ] ---->
      vREWRITE_TAC[vGSYM vMULT_ASSOC; vGSYM vLEFT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vEQ_MULT_LCANCEL; vARITH_EQ])
    and pth_z = (vSTANDARDIZE -| prove)
     ((parse_term "_0 + BIT0 p * b = BIT0(_0 + p * b)"),
      vSUBST1_TAC(vSYM(vSPEC (parse_term "_0") vNUMERAL)) ---->
      vREWRITE_TAC[vBIT1; vBIT0] ----> vREWRITE_TAC[vADD_CLAUSES] ---->
      vREWRITE_TAC[vRIGHT_ADD_DISTRIB])
    and puths_1 = (Array.of_list -| vCONJUNCTS -| vSTANDARDIZE -| prove)
       ((parse_term "(a + p * b = n <=>\n          BIT0(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT0(BIT0(BIT0(BIT0 n)))) /\\\n         (a + p * b = n <=>\n          BIT1(BIT0(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT1(BIT0(BIT0(BIT0 n)))) /\\\n         (a + p * b = n <=>\n          BIT0(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT0(BIT1(BIT0(BIT0 n)))) /\\\n         (a + p * b = n <=>\n          BIT1(BIT1(BIT0(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT1(BIT1(BIT0(BIT0 n)))) /\\\n         (a + p * b = n <=>\n          BIT0(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT0(BIT0(BIT1(BIT0 n)))) /\\\n         (a + p * b = n <=>\n          BIT1(BIT0(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT1(BIT0(BIT1(BIT0 n)))) /\\\n         (a + p * b = n <=>\n          BIT0(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT0(BIT1(BIT1(BIT0 n)))) /\\\n         (a + p * b = n <=>\n          BIT1(BIT1(BIT1(BIT0 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT1(BIT1(BIT1(BIT0 n)))) /\\\n         (a + p * b = n <=>\n          BIT0(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT0(BIT0(BIT0(BIT1 n)))) /\\\n         (a + p * b = n <=>\n          BIT1(BIT0(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT1(BIT0(BIT0(BIT1 n)))) /\\\n         (a + p * b = n <=>\n          BIT0(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT0(BIT1(BIT0(BIT1 n)))) /\\\n         (a + p * b = n <=>\n          BIT1(BIT1(BIT0(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT1(BIT1(BIT0(BIT1 n)))) /\\\n         (a + p * b = n <=>\n          BIT0(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT0(BIT0(BIT1(BIT1 n)))) /\\\n         (a + p * b = n <=>\n          BIT1(BIT0(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT1(BIT0(BIT1(BIT1 n)))) /\\\n         (a + p * b = n <=>\n          BIT0(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT0(BIT1(BIT1(BIT1 n)))) /\\\n         (a + p * b = n <=>\n          BIT1(BIT1(BIT1(BIT1 a))) + BIT0(BIT0(BIT0(BIT0 p))) * b =\n          BIT1(BIT1(BIT1(BIT1 n))))"),
      vSUBST1_TAC(vMESON[vNUMERAL] (parse_term "_0 = 0")) ---->
      vMP_TAC(vREWRITE_RULE[vGSYM vMULT_2] vBIT0) ---->
      vMP_TAC(vREWRITE_RULE[vGSYM vMULT_2] vBIT1) ---->
      vABBREV_TAC (parse_term "two = 2") ---->
      vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
      vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
      vFIRST_X_ASSUM(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vADD_CLAUSES; vSUC_INJ; vEQ_MULT_LCANCEL; vARITH_EQ;
                  vGSYM vLEFT_ADD_DISTRIB; vGSYM vMULT_ASSOC]) in
    let puths_2 = Array.of_list
     (map (fun i -> let th1 = Array.get puths_1 (i mod 16)
                    and th2 = Array.get puths_1 (i / 16) in
                    let th3 = vGEN_REWRITE_RULE vRAND_CONV [th1] th2 in
                    vSTANDARDIZE th3) (0--255)) in
    let rec vNUM_UNSHIFT_CONV tm =
      match tm with
        Comb(Comb(Const("+",_),atm),Comb(Comb(Const("*",_),ptm),btm)) ->
         (match (atm,ptm,btm) with
            (_,_,Const("_0",_)) ->
                vINST [atm,a_tm; ptm,p_tm] pth_triv
          | (_,Comb(Const("BIT1",_),Const("_0",_)),_) ->
                let th1 = vINST [atm,a_tm; btm,b_tm] pth_base in
                (match concl th1 with Comb(_,Comb(Comb(_,mtm),ntm)) ->
                vTRANS th1 (vNUM_ADD_RULE mtm ntm) | _ -> assert false)
          | (Comb(_,Comb(_,Comb(_,Comb(_,atm')))),
              Comb(_,Comb(_,Comb(_,Comb(_,(Comb(_,_) as ptm'))))),_) ->
                let i,_ = topsplit atm in
                (match (atm',ptm') with
                   (Comb(_,Comb(_,Comb(_,Comb(_,atm'')))),
                      Comb(_,Comb(_,Comb(_,Comb(_,(Comb(_,_) as ptm'')))))) ->
                     let j,_ = topsplit atm' in
                     let tm' = mk_comb(mk_comb(add_tm,atm''),
                                       mk_comb(mk_comb(mul_tm,ptm''),btm)) in
                     let th1 = vNUM_UNSHIFT_CONV tm' in
                     let th2 = vINST [atm'',a_tm; ptm'',p_tm; btm,b_tm;
                                     rand(concl th1),n_tm]
                                    (Array.get puths_2 (16 * j + i)) in
                     vEQ_MP th2 th1
                 | _ ->
                   let tm' = mk_comb(mk_comb(add_tm,atm'),
                                     mk_comb(mk_comb(mul_tm,ptm'),btm)) in
                   let th1 = vNUM_UNSHIFT_CONV tm' in
                   let th2 = vINST [atm',a_tm; ptm',p_tm; btm,b_tm;
                                   rand(concl th1),n_tm]
                                  (Array.get puths_1 i) in
                   vEQ_MP th2 th1)
          | (Const("_0",_),Comb(Const("BIT0",_),qtm),_) ->
                let th1 = vINST [btm,b_tm; qtm,p_tm] pth_z in
                vCONV_RULE(vRAND_CONV(vRAND_CONV vNUM_UNSHIFT_CONV)) th1
          | (Comb(Const("BIT0",_),ctm),Comb(Const("BIT0",_),qtm),_) ->
                let th1 = vINST [ctm,a_tm; btm,b_tm; qtm,p_tm] pth_0 in
                vCONV_RULE(vRAND_CONV(vRAND_CONV vNUM_UNSHIFT_CONV)) th1
          | (Comb(Const("BIT1",_),ctm),Comb(Const("BIT0",_),qtm),_) ->
                let th1 = vINST [ctm,a_tm; btm,b_tm; qtm,p_tm] pth_1 in
                vCONV_RULE(vRAND_CONV(vRAND_CONV vNUM_UNSHIFT_CONV)) th1
          | _ -> failwith "malformed numeral")
      | _ -> failwith "malformed numeral" in
    vNUM_UNSHIFT_CONV in
  let vNUM_SQUARE_RULE =
    let pth_0 = (vSTANDARDIZE -| prove)
     ((parse_term "_0 EXP 2 = _0"),
      vMESON_TAC[vNUMERAL; vREWRITE_CONV[vARITH] (parse_term "0 EXP 2")])
    and pth_1 = (vSTANDARDIZE -| prove)
     ((parse_term "(BIT1 _0) EXP 2 = BIT1 _0"),
      vMESON_TAC[vNUMERAL; vREWRITE_CONV[vARITH] (parse_term "1 EXP 2")])
    and pth_even = (vSTANDARDIZE -| prove)
     ((parse_term "m EXP 2 = n <=> (BIT0 m) EXP 2 = BIT0(BIT0 n)"),
      vABBREV_TAC (parse_term "two = 2") ---->
      vREWRITE_TAC[vBIT0] ----> vEXPAND_TAC "two" ---->
      vREWRITE_TAC[vGSYM vMULT_2] ----> vREWRITE_TAC[vEXP_2] ---->
      vREWRITE_TAC[vAC vMULT_AC (parse_term "(2 * m) * (2 * n) = 2 * 2 * m * n")] ---->
      vREWRITE_TAC[vEQ_MULT_LCANCEL; vARITH_EQ])
    and pth_odd = (vSTANDARDIZE -| prove)
     ((parse_term "m EXP 2 = n <=> (BIT1 m) EXP 2 = BIT1(BIT0(m + n))"),
      vABBREV_TAC (parse_term "two = 2") ---->
      vREWRITE_TAC[vNUMERAL; vBIT0; vBIT1] ---->
      vEXPAND_TAC "two" ----> vREWRITE_TAC[vGSYM vMULT_2] ---->
      vREWRITE_TAC[vEXP_2; vMULT_CLAUSES; vADD_CLAUSES] ---->
      vREWRITE_TAC[vSUC_INJ; vGSYM vMULT_ASSOC; vGSYM vLEFT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vAC vADD_AC (parse_term "(m + m * 2 * m) + m = m * 2 * m + m + m")] ---->
      vREWRITE_TAC[vGSYM vMULT_2; vAC vMULT_AC (parse_term "m * 2 * m = 2 * m * m")] ---->
      vREWRITE_TAC[vGSYM vMULT_ASSOC; vGSYM vLEFT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vEQ_MULT_LCANCEL; vARITH_EQ] ---->
      vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vADD_SYM] ---->
      vREWRITE_TAC[vEQ_ADD_RCANCEL])
    and pth_qstep = (vUNDISCH -| vSTANDARDIZE -| prove)
     ((parse_term "n + BIT1 _0 = m /\\\n       m EXP 2 = p /\\\n       m + a = BIT0(BIT0 p)\n       ==> (BIT1(BIT1(BIT1 n))) EXP 2 = BIT1(BIT0(BIT0(BIT0 a)))"),
      vABBREV_TAC (parse_term "two = 2") ---->
      vSUBST1_TAC(vMESON[vNUMERAL] (parse_term "_0 = 0")) ---->
      vREWRITE_TAC[vBIT1; vBIT0] ----> vEXPAND_TAC "two" ---->
      vREWRITE_TAC[vGSYM vMULT_2] ---->
      vREWRITE_TAC[vADD1; vLEFT_ADD_DISTRIB; vGSYM vADD_ASSOC] ---->
      vREWRITE_TAC[vMULT_ASSOC] ----> vREWRITE_TAC[vARITH] ---->
      vREWRITE_TAC[vIMP_CONJ] ---->
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vDISCH_TAC ---->
      vMATCH_MP_TAC(vMESON[vEQ_ADD_LCANCEL]
       (parse_term "!m:num. m + n = m + p ==> n = p")) ---->
      vEXISTS_TAC (parse_term "16 * (n + 1)") ---->
      vASM_REWRITE_TAC[vADD_ASSOC; vGSYM vLEFT_ADD_DISTRIB] ---->
      vEXPAND_TAC "two" ----> vREWRITE_TAC[vEXP_2] ---->
      vREWRITE_TAC[vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vMULT_CLAUSES; vMULT_ASSOC] ---->
      vREWRITE_TAC[vAC vMULT_AC (parse_term "(8 * n) * NUMERAL p = (8 * NUMERAL p) * n")] ---->
      vREWRITE_TAC[vARITH] ---->
      vREWRITE_TAC[vAC vADD_AC
         (parse_term "(n + 16) + p + q + 49 = (n + p + q) + (16 + 49)")] ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC] ----> vREWRITE_TAC[vARITH] ---->
      vREWRITE_TAC[vADD_ASSOC; vEQ_ADD_RCANCEL] ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC; vGSYM vMULT_2; vMULT_ASSOC] ---->
      vONCE_REWRITE_TAC[vAC vADD_AC (parse_term "a + b + c:num = b + a + c")] ---->
      vREWRITE_TAC[vGSYM vRIGHT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vARITH])
    and pth_rec = (vUNDISCH -| vSTANDARDIZE -| prove)
     ((parse_term "n = l + p * h /\\\n       h + l = m /\\\n       h EXP 2 = a /\\\n       l EXP 2 = c /\\\n       m EXP 2 = d /\\\n       a + c = e /\\\n       e + b = d\n       ==> n EXP 2 = c + p * (b + p * a)"),
      vREWRITE_TAC[vIMP_CONJ] ---->
      vDISCH_THEN vSUBST1_TAC ---->
      vREPLICATE_TAC 5 (vDISCH_THEN(vSUBST1_TAC -| vSYM)) ---->
      vREWRITE_TAC[vEXP_2; vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vMULT_AC] ----> vCONV_TAC(vBINOP_CONV vNUM_CANCEL_CONV) ---->
      vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vRIGHT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vMULT_AC] ----> vREWRITE_TAC[vADD_AC])
    and pth_toom3 = (vSTANDARDIZE -| prove)
     ((parse_term "h EXP 2 = e /\\\n       l EXP 2 = a /\\\n       (l + BIT1 _0 * (m + BIT1 _0 * h)) EXP 2 =\n       a +  BIT1 _0 * (b +  BIT1 _0 * (c +  BIT1 _0 * (d +  BIT1 _0 * e))) /\\\n       (l + BIT0(BIT1 _0) * (m + BIT0(BIT1 _0) * h)) EXP 2 =\n       a + BIT0(BIT1 _0) * (b + BIT0(BIT1 _0) *\n       (c + BIT0(BIT1 _0) * (d + BIT0(BIT1 _0) * e))) /\\\n       (h + BIT0(BIT1 _0) * (m + BIT0(BIT1 _0) * l)) EXP 2 =\n       e + BIT0(BIT1 _0) * (d + BIT0(BIT1 _0) *\n       (c + BIT0(BIT1 _0) * (b + BIT0(BIT1 _0) * a)))\n       ==> (l + p * (m + p * h)) EXP 2 =\n           a + p * (b + p * (c + p * (d + p * e)))"),
      vABBREV_TAC (parse_term "two = 2") ---->
      vSUBST1_TAC(vMESON[vNUMERAL] (parse_term "_0 = 0")) ---->
      vREWRITE_TAC[vBIT1; vBIT0] ---->
      vEXPAND_TAC "two" ----> vREWRITE_TAC[vGSYM vMULT_2] ---->
      vREWRITE_TAC[vARITH] ---->
      vSUBGOAL_THEN
       (parse_term "!p x y z. (x + p * (y + p * z)) EXP 2 =\n                  x * x + p * (2 * x * y + p * ((2 * x * z + y * y) +\n                            p * (2 * y * z + p * z * z)))")
       (fun th -> vREWRITE_TAC[th])
      ++-->
       [vREWRITE_TAC[vEXP_2; vMULT_2; vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB] ---->
        vREWRITE_TAC[vMULT_AC] ----> vREWRITE_TAC[vADD_AC];
        vREWRITE_TAC[vEXP_2]] ---->
      vMAP_EVERY vABBREV_TAC
       [(parse_term "a':num = l * l");  (parse_term "b' = 2 * l * m"); (parse_term "c' = 2 * l * h + m * m");
        (parse_term "d' = 2 * m * h"); (parse_term "e':num = h * h")] ---->
      vSUBST1_TAC(vAC vMULT_AC (parse_term "2 * m * l = 2 * l * m")) ---->
      vSUBST1_TAC(vAC vMULT_AC (parse_term "2 * h * l = 2 * l * h")) ---->
      vSUBST1_TAC(vAC vMULT_AC (parse_term "2 * h * m = 2 * m * h")) ---->
      vASM_REWRITE_TAC[] ----> vEXPAND_TAC "two" ---->
      vPOP_ASSUM_LIST(vK vALL_TAC) ---->
      vASM_CASES_TAC (parse_term "a':num = a") ----> vASM_REWRITE_TAC[] ---->
      vASM_CASES_TAC (parse_term "e':num = e") ----> vASM_REWRITE_TAC[] ---->
      vPOP_ASSUM_LIST(vK vALL_TAC) ---->
      vREWRITE_TAC[vEQ_ADD_LCANCEL; vEQ_MULT_LCANCEL] ---->
      vREWRITE_TAC[vLEFT_ADD_DISTRIB; vMULT_ASSOC] ---->
      vREWRITE_TAC[vARITH] ---->
      vREWRITE_TAC[vMULT_CLAUSES; vEQ_ADD_LCANCEL] ---->
      vREWRITE_TAC[vADD_ASSOC; vEQ_ADD_RCANCEL] ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC] ----> vDISCH_TAC ---->
      vFIRST_ASSUM(vMP_TAC -| vMATCH_MP (vMESON[]
       (parse_term "b = b' /\\ c = c' /\\ d = d'\n        ==> 5 * b + c' + d' = 5 * b' + c + d"))) ---->
      vREWRITE_TAC[vLEFT_ADD_DISTRIB; vMULT_ASSOC] ---->
      vREWRITE_TAC(map (fun k ->
          vSYM(vREWRITE_CONV[vARITH_SUC]
          (mk_comb(suc_tm,mk_small_numeral(k - 1)))))
         (1--5)) ---->
      vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES] ---->
      vCONV_TAC(vLAND_CONV vNUM_CANCEL_CONV) ----> vDISCH_THEN vSUBST_ALL_TAC ---->
      vFIRST_ASSUM(vMP_TAC -| vMATCH_MP (vMESON[]
       (parse_term "b = b' /\\ c = c' /\\ d = d'\n        ==> b + d':num = b' + d /\\ 4 * b + d' = 4 * b' + d"))) ---->
      vREWRITE_TAC[vLEFT_ADD_DISTRIB; vMULT_ASSOC] ---->
      vREWRITE_TAC(map (fun k ->
          vSYM(vREWRITE_CONV[vARITH_SUC]
          (mk_comb(suc_tm,mk_small_numeral(k - 1)))))
         (1--4)) ---->
      vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES] ---->
      vCONV_TAC(vLAND_CONV(vBINOP_CONV vNUM_CANCEL_CONV)) ---->
      vREWRITE_TAC[vGSYM vMULT_2] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
      vREWRITE_TAC[vGSYM(el 4 (vCONJUNCTS vMULT_CLAUSES))] ---->
      vSIMP_TAC[vEQ_MULT_LCANCEL; vNOT_SUC])
    and pth_even3 = (vSTANDARDIZE -| prove)
     ((parse_term "m EXP 2 = n <=>\n       (BIT0(BIT0(BIT0 m))) EXP 2 = BIT0(BIT0(BIT0(BIT0(BIT0(BIT0 n)))))"),
      vABBREV_TAC (parse_term "two = 2") ---->
      vREWRITE_TAC[vBIT0] ----> vREWRITE_TAC[vGSYM vMULT_2] ---->
      vEXPAND_TAC "two" ----> vREWRITE_TAC[vEXP_2] ---->
      vREWRITE_TAC[vAC vMULT_AC
       (parse_term "(2 * 2 * 2 * m) * 2 * 2 * 2 * m = 2 * 2 * 2 * 2 * 2 * 2 * m * m")] ---->
      vREWRITE_TAC[vEQ_MULT_LCANCEL; vARITH_EQ]) in
    let vNUM_UNSHIFT2_CONV =
      vRAND_CONV(vRAND_CONV vNUM_UNSHIFT_CONV) +---> vNUM_UNSHIFT_CONV in
    let vNUM_UNSHIFT3_CONV =
      vRAND_CONV(vRAND_CONV vNUM_UNSHIFT2_CONV) +---> vNUM_UNSHIFT_CONV in
    let vNUM_UNSHIFT4_CONV =
      vRAND_CONV(vRAND_CONV vNUM_UNSHIFT3_CONV) +---> vNUM_UNSHIFT_CONV in
    let vBINOP2_CONV conv1 conv2 = vCOMB2_CONV (vRAND_CONV conv1) conv2 in
    let vTOOM3_CONV = vBINOP2_CONV
      (vLAND_CONV vNUM_UNSHIFT2_CONV) vNUM_UNSHIFT4_CONV in
    let rec vGEN_NUM_SQUARE_RULE w z tm =
      match tm with
        Const("_0",_) -> pth_0
      | Comb(Const("BIT0",_),mtm) ->
           (match mtm with
              Comb(Const("BIT0",_),Comb(Const("BIT0",_),ptm)) ->
                 let th1 = vGEN_NUM_SQUARE_RULE w (z - 3) ptm in
                 let ntm = rand(concl th1) in
                 vEQ_MP (vINST [ptm,m_tm; ntm,n_tm] pth_even3) th1
            | _ ->
                 let th1 = vGEN_NUM_SQUARE_RULE w (z - 1) mtm in
                 let ntm = rand(concl th1) in
                 vEQ_MP (vINST [mtm,m_tm; ntm,n_tm] pth_even) th1)
      | Comb(Const("BIT1",_),mtm) ->
            if mtm = zero_tm then pth_1 else
            if (w < 100 || z < 20) && w + z < 150 then
              match mtm with
                Comb(Const("BIT1",_),Comb(Const("BIT1",_),ntm)) ->
                    let th1 = vNUM_ADD_RULE ntm one_tm in
                    let mtm = rand(concl th1) in
                    let th2 = vNUM_SQUARE_RULE mtm in
                    let ptm = rand(concl th2) in
                    let atm = subbn
                      (mk_comb(vBIT0_tm,mk_comb(vBIT0_tm,ptm))) mtm in
                    let th3 = vNUM_ADD_RULE mtm atm in
                    let th4 = vINST
                      [atm,a_tm; mtm,m_tm; ntm,n_tm; ptm,p_tm] pth_qstep in
                    vQUICK_PROVE_HYP (vCONJ th1 (vCONJ th2 th3)) th4
              | _ ->
                    let th1 = vGEN_NUM_SQUARE_RULE (w - 1) z mtm in
                    let ntm = rand(concl th1) in
                    let th2 = vEQ_MP (vINST [mtm,m_tm; ntm,n_tm] pth_odd) th1 in
                    (match concl th2 with
                      Comb(_,Comb(_,Comb(_,Comb(Comb(_,ptm),qtm)))) ->
                        let th3 = vNUM_ADD_RULE ptm qtm in
                        vTRANS th2 (vAP_BIT1 (vAP_BIT0 th3)) | _ -> assert false)
            else if w + z < 800 then
              let k2 = (w + z) / 2 in
              let th1 = vNUM_SHIFT_CONV k2 tm in
              let htm,ltm,ptm = match rand(concl th1) with Comb(Comb(_,ltm),Comb(Comb(_,ptm),htm)) -> htm,ltm,ptm | _ -> assert false in
              let th2 = vNUM_ADD_RULE htm ltm in
              let mtm = rand(concl th2) in
              let th3 = vNUM_SQUARE_RULE htm
              and th4 = vNUM_SQUARE_RULE ltm
              and th5 = vNUM_SQUARE_RULE mtm in
              let atm = rand(concl th3)
              and ctm = rand(concl th4)
              and dtm = rand(concl th5) in
              let th6 = vNUM_ADD_RULE atm ctm in
              let etm = rand(concl th6) in
              let btm = subbn dtm etm in
              let th7 = vNUM_ADD_RULE etm btm in
              let dtm = rand(concl th7) in
              let th8 = vINST [atm,a_tm; btm,b_tm; ctm,c_tm; dtm,d_tm; etm,e_tm;
                              htm,h_tm; ltm,l_tm; mtm,m_tm; tm,n_tm; ptm,p_tm]
                        pth_rec in
              let th9 = vQUICK_PROVE_HYP (end_itlist vCONJ
                   [th1;th2;th3;th4;th5;th6;th7]) th8 in
              vCONV_RULE(vRAND_CONV(vRAND_CONV(vRAND_CONV vNUM_UNSHIFT_CONV) +--->
                                  vNUM_UNSHIFT_CONV)) th9
            else
              let k3 = (w + z) / 3 in
              let th0 = (vNUM_SHIFT_CONV k3 +--->
                         vRAND_CONV(vRAND_CONV(vNUM_SHIFT_CONV k3))) tm in
              let htm,ltm,mtm,ptm = match rand(concl th0) with Comb(Comb(_,ltm),Comb(Comb(_,ptm),
                   Comb(Comb(_,mtm),Comb(Comb(_,_),htm)))) -> htm,ltm,mtm,ptm | _ -> assert false in
              let th1 = vNUM_SQUARE_RULE htm
              and th2 = vNUM_SQUARE_RULE ltm in
              let atm = rand(concl th2) and etm = rand(concl th1) in
              let lnum = dest_raw_numeral ltm
              and mnum = dest_raw_numeral mtm
              and hnum = dest_raw_numeral htm in
              let btm = rand(mk_numeral(num_2 */ lnum */ mnum))
              and ctm = rand(mk_numeral(mnum */ mnum +/ num_2 */ lnum */ hnum))
              and dtm = rand(mk_numeral(num_2 */ hnum */ mnum)) in
              let th = vINST
                [atm,a_tm; btm,b_tm; ctm,c_tm; dtm,d_tm; etm,e_tm;
                 htm,h_tm; mtm,m_tm; ltm,l_tm; ptm,p_tm] pth_toom3 in
              let th' = vCONV_RULE
               (vBINOP2_CONV
                (vRAND_CONV(vRAND_CONV
                 (vBINOP2_CONV vTOOM3_CONV (vBINOP2_CONV vTOOM3_CONV vTOOM3_CONV))))
                vTOOM3_CONV) th in
              let tm3,tm4,tm5 = match conjuncts(rand(rand(lhand(concl th')))) with [a;b;c] -> a,b,c | _ -> assert false in
              let th3 = vNUM_SQUARE_RULE (lhand(lhand tm3))
              and th4 = vNUM_SQUARE_RULE (lhand(lhand tm4))
              and th5 = vNUM_SQUARE_RULE (lhand(lhand tm5)) in
              vMP th' (end_itlist vCONJ [th1;th2;th3;th4;th5])
      | _ -> assert false
    and vNUM_SQUARE_RULE tm =
      let w,z = bitcounts tm in vGEN_NUM_SQUARE_RULE w z tm in
    vNUM_SQUARE_RULE in
  let vNUM_MUL_RULE =
    let vQUICK_PROVE_HYP ath bth =
      vEQ_MP (vDEDUCT_ANTISYM_RULE ath bth) ath
    and pth_0l,pth_0r = (vCONJ_PAIR -| vSTANDARDIZE -| prove)
     ((parse_term "_0 * n = _0 /\\ m * _0 = _0"),
      vMESON_TAC[vNUMERAL; vMULT_CLAUSES])
    and pth_1l,pth_1r = (vCONJ_PAIR -| vSTANDARDIZE -| prove)
     ((parse_term "(BIT1 _0) * n = n /\\ m * (BIT1 _0) = m"),
      vMESON_TAC[vNUMERAL; vMULT_CLAUSES])
    and pth_evenl,pth_evenr = (vCONJ_PAIR -| vSTANDARDIZE -| prove)
     ((parse_term "(m * n = p <=> (BIT0 m) * n = BIT0 p) /\\\n       (m * n = p <=> m * BIT0 n = BIT0 p)"),
      vREWRITE_TAC[vBIT0] ----> vREWRITE_TAC[vGSYM vMULT_2] ---->
      vREWRITE_TAC[vAC vMULT_AC (parse_term "m * 2 * n = 2 * m * n")] ---->
      vREWRITE_TAC[vGSYM vMULT_ASSOC; vEQ_MULT_LCANCEL; vARITH_EQ])
    and pth_oddl,pth_oddr = (vCONJ_PAIR -| vSTANDARDIZE -| prove)
     ((parse_term "(m * n = p <=> BIT1 m * n = BIT0 p + n) /\\\n       (m * n = p <=> m * BIT1 n = BIT0 p + m)"),
      vREWRITE_TAC[vBIT0; vBIT1] ----> vREWRITE_TAC[vGSYM vMULT_2] ---->
      vREWRITE_TAC[vMULT_CLAUSES] ---->
      vREWRITE_TAC[vMESON[vMULT_AC; vADD_SYM] (parse_term "m + m * 2 * n = 2 * m * n + m")] ---->
      vREWRITE_TAC[vGSYM vMULT_ASSOC; vEQ_MULT_LCANCEL; vEQ_ADD_RCANCEL] ---->
      vREWRITE_TAC[vARITH_EQ]) in
    let pth_oo1 = (vUNDISCH_ALL -| vSTANDARDIZE -| prove)
     ((parse_term "n + p = m /\\ SUC(m + n) = a /\\ p EXP 2 = b /\\ a EXP 2 = c /\\ b + d = c\n        ==> ((BIT1 m) * (BIT1 n) = d)"),
      vABBREV_TAC (parse_term "two = 2") ----> vREWRITE_TAC[vBIT1; vIMP_CONJ] ---->
      vFIRST_X_ASSUM(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vEXP_2; vGSYM vMULT_2] ---->
      vREPLICATE_TAC 4 (vDISCH_THEN(vSUBST1_TAC -| vSYM)) ---->
      vREWRITE_TAC[vADD1; vAC vADD_AC (parse_term "((n + p) + n) + 1 = (p + (n + n)) + 1")] ---->
      vREWRITE_TAC[vGSYM vMULT_2] ---->
      vREWRITE_TAC[vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC; vMULT_CLAUSES; vEQ_ADD_LCANCEL] ---->
      vDISCH_THEN vSUBST1_TAC ---->
      vREWRITE_TAC[vMULT_2; vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB] ---->
      vREWRITE_TAC[vMULT_AC] ----> vREWRITE_TAC[vADD_AC]) in
    let pth_oo2 = vPURE_ONCE_REWRITE_RULE[vMULT_SYM]
                   (vINST [n_tm,m_tm; m_tm,n_tm] pth_oo1) in
    let pth_recodel = (vUNDISCH_ALL -| vSTANDARDIZE -| prove)
     ((parse_term "SUC(_0 + m) = p ==> (p * n = a + n <=> m * n = a)"),
      vSUBST1_TAC(vMESON[vNUMERAL] (parse_term "_0 = 0")) ---->
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vADD_CLAUSES; vMULT_CLAUSES; vEQ_ADD_RCANCEL])
    and pth_recoder = (vUNDISCH_ALL -| vSTANDARDIZE -| prove)
     ((parse_term "SUC(_0 + n) = p ==> (m * p = a + m <=> m * n = a)"),
      vONCE_REWRITE_TAC[vMULT_SYM] ---->
      vSUBST1_TAC(vMESON[vNUMERAL] (parse_term "_0 = 0")) ---->
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vADD_CLAUSES; vMULT_CLAUSES; vEQ_ADD_RCANCEL]) in
    let rec vNUM_MUL_RULE k l tm tm' =
      match (tm,tm') with
        (Const("_0",_),_) -> vINST [tm',n_tm] pth_0l
      | (_,Const("_0",_)) -> vINST [tm,m_tm] pth_0r
      | (Comb(Const("BIT1",_),Const("_0",_)),_) -> vINST [tm',n_tm] pth_1l
      | (_,Comb(Const("BIT1",_),Const("_0",_))) -> vINST [tm,m_tm] pth_1r
      | (Comb(Const("BIT0",_),mtm),_) ->
            let th0 = vNUM_MUL_RULE (k - 1) l mtm tm' in
            let th1 = vINST
             [mtm,m_tm; tm',n_tm; rand(concl th0),p_tm] pth_evenl in
            vEQ_MP th1 th0
      | (_,Comb(Const("BIT0",_),ntm)) ->
            let th0 = vNUM_MUL_RULE k (l - 1) tm ntm in
            let th1 = vINST
             [tm,m_tm; ntm,n_tm; rand(concl th0),p_tm] pth_evenr in
            vEQ_MP th1 th0
      | (Comb(Const("BIT1",_),mtm),Comb(Const("BIT1",_),ntm)) ->
          if k <= 50 || l <= 50 ||
             Int k */ Int k <=/ Int l ||
             Int l */ Int l <= Int k then
            match (mtm,ntm) with
              (Comb(Const("BIT1",_),Comb(Const("BIT1",_),_)),_) ->
                 let th1 = vNUM_ADC_RULE zero_tm tm in
                 let ptm = rand(concl th1) in
                 let th2 = vNUM_MUL_RULE k l ptm tm' in
                 let atm = subbn (rand(concl th2)) tm' in
                 let th3 = vINST [tm,m_tm; tm',n_tm; ptm,p_tm; atm,a_tm]
                                pth_recodel in
                 let th4 = vPROVE_HYP th1 th3 in
                 vEQ_MP th4 (vTRANS th2 (vSYM(vNUM_ADD_RULE atm tm')))
            | (_,Comb(Const("BIT1",_),Comb(Const("BIT1",_),_))) ->
                 let th1 = vNUM_ADC_RULE zero_tm tm' in
                 let ptm = rand(concl th1) in
                 let th2 = vNUM_MUL_RULE k l tm ptm in
                 let atm = subbn (rand(concl th2)) tm in
                 let th3 = vINST [tm,m_tm; tm',n_tm; ptm,p_tm; atm,a_tm]
                                pth_recoder in
                 let th4 = vPROVE_HYP th1 th3 in
                 vEQ_MP th4 (vTRANS th2 (vSYM(vNUM_ADD_RULE atm tm)))
            | _ ->
                 if k <= l then
                   let th0 = vNUM_MUL_RULE (k - 1) l mtm tm' in
                   let ptm = rand(concl th0) in
                   let th1 =
                    vEQ_MP (vINST [mtm,m_tm; tm',n_tm; ptm,p_tm] pth_oddl) th0 in
                   let tm1 = lhand(rand(concl th1)) in
                   vTRANS th1 (vNUM_ADD_RULE tm1 tm')
                 else
                   let th0 = vNUM_MUL_RULE k (l - 1) tm ntm in
                   let ptm = rand(concl th0) in
                   let th1 =
                     vEQ_MP (vINST [tm,m_tm; ntm,n_tm; ptm,p_tm] pth_oddr) th0 in
                   let tm1 = lhand(rand(concl th1)) in
                   vTRANS th1 (vNUM_ADD_RULE tm1 tm)
          else
             let mval = dest_raw_numeral mtm
             and nval = dest_raw_numeral ntm in
             if nval <=/ mval then
               let ptm = rand(mk_numeral(mval -/ nval)) in
               let th2 = vNUM_ADD_RULE ntm ptm
               and th3 = vNUM_ADC_RULE mtm ntm in
               let atm = rand(concl th3) in
               let th4 = vNUM_SQUARE_RULE ptm in
               let btm = rand(concl th4) in
               let th5 = vNUM_SQUARE_RULE atm in
               let ctm = rand(concl th5) in
               let dtm = subbn ctm btm in
               let th6 = vNUM_ADD_RULE btm dtm in
               let th1 = vINST [atm,a_tm; btm,b_tm; ctm,c_tm; dtm,d_tm;
                               mtm,m_tm; ntm,n_tm; ptm,p_tm] pth_oo1 in
               vQUICK_PROVE_HYP  (end_itlist vCONJ
                   [th2;th3;th4;th5;th6]) th1
             else
               let ptm = rand(mk_numeral(nval -/ mval)) in
               let th2 = vNUM_ADD_RULE mtm ptm
               and th3 = vNUM_ADC_RULE ntm mtm in
               let atm = rand(concl th3) in
               let th4 = vNUM_SQUARE_RULE ptm in
               let btm = rand(concl th4) in
               let th5 = vNUM_SQUARE_RULE atm in
               let ctm = rand(concl th5) in
               let dtm = subbn ctm btm in
               let th6 = vNUM_ADD_RULE btm dtm in
               let th1 = vINST [atm,a_tm; btm,b_tm; ctm,c_tm; dtm,d_tm;
                               mtm,m_tm; ntm,n_tm; ptm,p_tm] pth_oo2 in
               vQUICK_PROVE_HYP  (end_itlist vCONJ
                   [th2;th3;th4;th5;th6]) th1
      | _ -> failwith "NUM_MUL_RULE" in
    vNUM_MUL_RULE in
  let vNUM_MULT_CONV' =
    let pth_refl = (vSTANDARDIZE -| vMESON[vEXP_2])
      (parse_term "m EXP 2 = p <=> m * m = p") in
    fun tm ->
      match tm with
        Comb(Comb(Const("*",_),mtm),ntm) ->
            if Stdlib.compare mtm ntm = 0 then
              let th1 = vNUM_SQUARE_RULE mtm in
              let ptm = rand(concl th1) in
              vEQ_MP (vINST [mtm,m_tm;ptm,p_tm] pth_refl) th1
            else
              let w1,z1 = bitcounts mtm and w2,z2 = bitcounts ntm in
              vNUM_MUL_RULE (w1+z1) (w2+z2) mtm ntm
    | _ -> failwith "NUM_MULT_CONV'" in
  let vNUM_SUC_CONV =
    let pth = (vSTANDARDIZE -| prove)
     ((parse_term "SUC(_0 + m) = n <=> SUC(NUMERAL m) = NUMERAL n"),
      vBINOP_TAC ----> vMESON_TAC[vNUMERAL; vADD_CLAUSES]) in
    fun tm ->
      match tm with
        Comb(Const("SUC",_),Comb(Const("NUMERAL",_),mtm))
        when wellformed mtm ->
          let th1 = vNUM_ADC_RULE zero_tm mtm in
          let ntm = rand(concl th1) in
          vEQ_MP(vINST [mtm,m_tm; ntm,n_tm] pth) th1
      | _ -> failwith "NUM_SUC_CONV" in
  let vNUM_ADD_CONV =
    let topthm_add = (vSTANDARDIZE -| vMESON[vNUMERAL])
      (parse_term "m + n = p <=> NUMERAL m + NUMERAL n = NUMERAL p") in
    fun tm ->
      match tm with
        Comb(Comb(Const("+",_),Comb(Const("NUMERAL",_),mtm)),
          Comb(Const("NUMERAL",_),ntm))
        when wellformed mtm && wellformed ntm ->
        let th1 = vNUM_ADD_RULE mtm ntm in
        let ptm = rand(concl th1) in
        let th2 = vINST [mtm,m_tm; ntm,n_tm; ptm,p_tm] topthm_add in
        vEQ_MP th2 th1
      | _ -> failwith "NUM_ADD_CONV" in
  let vNUM_MULT_CONV =
    let topthm_mul = (vSTANDARDIZE -| vMESON[vNUMERAL])
      (parse_term "m * n = p <=> NUMERAL m * NUMERAL n = NUMERAL p")
    and pth_refl = (vSTANDARDIZE -| vMESON[vNUMERAL; vEXP_2])
      (parse_term "m EXP 2 = p <=> NUMERAL m * NUMERAL m = NUMERAL p") in
    fun tm ->
      match tm with
        Comb(Comb(Const("*",_),Comb(Const("NUMERAL",_),mtm)),
          Comb(Const("NUMERAL",_),ntm)) ->
            if Stdlib.compare mtm ntm = 0 then
              let th1 = vNUM_SQUARE_RULE mtm in
              let ptm = rand(concl th1) in
              vEQ_MP (vINST [mtm,m_tm;ptm,p_tm] pth_refl) th1
            else
              let w1,z1 = bitcounts mtm and w2,z2 = bitcounts ntm in
              let th1 = vNUM_MUL_RULE (w1+z1) (w2+z2) mtm ntm in
              let ptm = rand(concl th1) in
              let th2 = vINST [mtm,m_tm; ntm,n_tm; ptm,p_tm] topthm_mul in
              vEQ_MP th2 th1
      | _ -> failwith "NUM_MULT_CONV" in
  let vNUM_EXP_CONV =
    let pth0 = (vSTANDARDIZE -| prove)
     ((parse_term "(m EXP n = p) ==> (p * p = a) ==> (m EXP (BIT0 n) = a)"),
       vREPEAT(vDISCH_THEN(vSUBST1_TAC -| vSYM)) ---->
       vREWRITE_TAC[vBIT0; vEXP_ADD])
    and pth1 = (vSTANDARDIZE -| prove)
     ((parse_term "(m EXP n = p) ==> (p * p = b) ==> (m * b = a) ==> (m EXP (BIT1 n) = a)"),
      vREPEAT(vDISCH_THEN(vSUBST1_TAC -| vSYM)) ---->
      vREWRITE_TAC[vBIT1; vEXP_ADD; vEXP])
    and pth = (vSTANDARDIZE -| prove)
     ((parse_term "m EXP _0 = BIT1 _0"),
      vMP_TAC (vCONJUNCT1 vEXP) ----> vREWRITE_TAC[vNUMERAL; vBIT1] ---->
      vDISCH_THEN vMATCH_ACCEPT_TAC)
    and tth = (vSTANDARDIZE -| prove)
     ((parse_term "(NUMERAL m) EXP (NUMERAL n) = m EXP n"),
      vREWRITE_TAC[vNUMERAL])
    and fth = (vSTANDARDIZE -| prove)
     ((parse_term "m = NUMERAL m"),
      vREWRITE_TAC[vNUMERAL]) in
    let tconv = vGEN_REWRITE_CONV vI [tth] in
    let rec vNUM_EXP_CONV l r =
      if r = zero_tm then vINST [l,m_tm] pth else
      let b,r' = dest_comb r in
      if b = vBIT0_tm then
        let th1 = vNUM_EXP_CONV l r' in
        let tm1 = rand(concl th1) in
        let th2 = vNUM_MULT_CONV' (mk_binop mul_tm tm1 tm1) in
        let tm2 = rand(concl th2) in
        vMP (vMP (vINST [l,m_tm; r',n_tm; tm1,p_tm; tm2,a_tm] pth0) th1) th2
      else
        let th1 = vNUM_EXP_CONV l r' in
        let tm1 = rand(concl th1) in
        let th2 = vNUM_MULT_CONV' (mk_binop mul_tm tm1 tm1) in
        let tm2 = rand(concl th2) in
        let th3 = vNUM_MULT_CONV' (mk_binop mul_tm l tm2) in
        let tm3 = rand(concl th3) in
        vMP (vMP (vMP (vINST [l,m_tm; r',n_tm; tm1,p_tm; tm2,b_tm; tm3,a_tm]
                         pth1) th1) th2) th3 in
    fun tm -> try let th = tconv tm in
                  let lop,r = dest_comb (rand(concl th)) in
                  let _,l = dest_comb lop in
                  if not (wellformed l && wellformed r) then failwith "" else
                  let th' = vNUM_EXP_CONV l r in
                  let tm' = rand(concl th') in
                  vTRANS (vTRANS th th') (vINST [tm',m_tm] fth)
              with Failure _ -> failwith "NUM_EXP_CONV" in
  let vNUM_LT_CONV =
    let pth = (vUNDISCH -| vSTANDARDIZE -| prove)
     ((parse_term "SUC(m + n) = p ==> ((NUMERAL n < NUMERAL p) <=> T)"),
      vREWRITE_TAC[vNUMERAL; vLT_EXISTS; vADD_CLAUSES] ---->
      vMESON_TAC[vADD_SYM])
    and qth = (vUNDISCH -| vSTANDARDIZE -| prove)
     ((parse_term "m + p = n ==> (NUMERAL n < NUMERAL p <=> F)"),
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vNOT_LT; vNUMERAL] ---->
      vMESON_TAC[vLE_ADD; vADD_SYM])
    and rth = (vSTANDARDIZE -| prove)
     ((parse_term "NUMERAL n < NUMERAL n <=> F"),
      vMESON_TAC[vLT_REFL]) in
    fun tm ->
      match tm with
        Comb(Comb(Const("<",_),Comb(Const("NUMERAL",_),mtm)),
             Comb(Const("NUMERAL",_),ntm)) ->
          let rel = orderrelation mtm ntm in
          if rel = 0 then vINST[ntm,n_tm] rth
          else if rel < 0 then
            let dtm = sbcbn ntm mtm in
            let th = vNUM_ADC_RULE dtm mtm in
            vQUICK_PROVE_HYP th (vINST [dtm,m_tm; mtm,n_tm; ntm,p_tm] pth)
          else
            let dtm = subbn mtm ntm in
            let th = vNUM_ADD_RULE dtm ntm in
            vQUICK_PROVE_HYP th (vINST [dtm,m_tm; mtm,n_tm; ntm,p_tm] qth)
      | _ -> failwith "NUM_LT_CONV"
  and vNUM_LE_CONV =
    let pth = (vUNDISCH -| vSTANDARDIZE -| prove)
     ((parse_term "m + n = p ==> ((NUMERAL n <= NUMERAL p) <=> T)"),
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vNUMERAL] ---->
      vMESON_TAC[vLE_ADD; vADD_SYM])
    and qth = (vUNDISCH -| vSTANDARDIZE -| prove)
     ((parse_term "SUC(m + p) = n ==> (NUMERAL n <= NUMERAL p <=> F)"),
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vNUMERAL; vNOT_LE; vADD_CLAUSES; vLT_EXISTS] ---->
      vMESON_TAC[vADD_SYM])
    and rth = (vSTANDARDIZE -| prove)
     ((parse_term "NUMERAL n <= NUMERAL n <=> T"),
      vREWRITE_TAC[vLE_REFL]) in
    fun tm ->
      match tm with
        Comb(Comb(Const("<=",_),Comb(Const("NUMERAL",_),mtm)),
             Comb(Const("NUMERAL",_),ntm)) ->
          let rel = orderrelation mtm ntm in
          if rel = 0 then vINST[ntm,n_tm] rth
          else if rel < 0 then
            let dtm = subbn ntm mtm in
            let th = vNUM_ADD_RULE dtm mtm in
            vQUICK_PROVE_HYP th (vINST [dtm,m_tm; mtm,n_tm; ntm,p_tm] pth)
          else
            let dtm = sbcbn mtm ntm in
            let th = vNUM_ADC_RULE dtm ntm in
            vQUICK_PROVE_HYP th (vINST [dtm,m_tm; mtm,n_tm; ntm,p_tm] qth)
      | _ -> failwith "NUM_LE_CONV"
  and vNUM_EQ_CONV =
    let pth = (vUNDISCH -| vSTANDARDIZE -| prove)
     ((parse_term "SUC(m + n) = p ==> ((NUMERAL n = NUMERAL p) <=> F)"),
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vNUMERAL; vGSYM vLE_ANTISYM; vDE_MORGAN_THM] ---->
      vREWRITE_TAC[vNOT_LE; vLT_EXISTS; vADD_CLAUSES] ---->
      vMESON_TAC[vADD_SYM])
    and qth = (vUNDISCH -| vSTANDARDIZE -| prove)
     ((parse_term "SUC(m + p) = n ==> ((NUMERAL n = NUMERAL p) <=> F)"),
      vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vNUMERAL; vGSYM vLE_ANTISYM; vDE_MORGAN_THM] ---->
      vREWRITE_TAC[vNOT_LE; vLT_EXISTS; vADD_CLAUSES] ---->
      vMESON_TAC[vADD_SYM])
    and rth = (vSTANDARDIZE -| prove)
     ((parse_term "(NUMERAL n = NUMERAL n) <=> T"),
      vREWRITE_TAC[]) in
    fun tm ->
      match tm with
        Comb(Comb(Const("=",_),Comb(Const("NUMERAL",_),mtm)),
             Comb(Const("NUMERAL",_),ntm)) ->
          let rel = orderrelation mtm ntm in
          if rel = 0 then vINST [ntm,n_tm] rth
          else if rel < 0 then
             let dtm = sbcbn ntm mtm in
             let th = vNUM_ADC_RULE dtm mtm in
             vQUICK_PROVE_HYP th (vINST [dtm,m_tm; mtm,n_tm; ntm,p_tm] pth)
          else
             let dtm = sbcbn mtm ntm in
             let th = vNUM_ADC_RULE dtm ntm in
             vQUICK_PROVE_HYP th (vINST [dtm,m_tm; mtm,n_tm; ntm,p_tm] qth)
      | _ -> failwith "NUM_EQ_CONV" in
  vNUM_SUC_CONV,vNUM_ADD_CONV,vNUM_MULT_CONV,vNUM_EXP_CONV,
  vNUM_LT_CONV,vNUM_LE_CONV,vNUM_EQ_CONV;;

let vNUM_GT_CONV = vGEN_REWRITE_CONV vI [vGT] +---> vNUM_LT_CONV;;

let vNUM_GE_CONV = vGEN_REWRITE_CONV vI [vGE] +---> vNUM_LE_CONV;;

let vNUM_PRE_CONV =
  let tth = prove
   ((parse_term "PRE 0 = 0"),
    vREWRITE_TAC[vPRE]) in
  let pth = prove
   ((parse_term "(SUC m = n) ==> (PRE n = m)"),
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vPRE])
  and m = (parse_term "m:num") and n = (parse_term "n:num") in
  let suc = (parse_term "SUC") in
  let pre = (parse_term "PRE") in
  fun tm -> try let l,r = dest_comb tm in
                if not (l = pre) then fail() else
                let x = dest_numeral r in
                if x =/ Int 0 then tth else
                let tm' = mk_numeral (x -/ Int 1) in
                let th1 = vNUM_SUC_CONV (mk_comb(suc,tm')) in
                vMP (vINST [tm',m; r,n] pth) th1
            with Failure _ -> failwith "NUM_PRE_CONV";;

let vNUM_SUB_CONV =
  let pth0 = prove
   ((parse_term "p <= n ==> (p - n = 0)"),
    vREWRITE_TAC[vSUB_EQ_0])
  and pth1 = prove
   ((parse_term "(m + n = p) ==> (p - n = m)"),
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
    vREWRITE_TAC[vADD_SUB])
  and m = (parse_term "m:num") and n = (parse_term "n:num") and p = (parse_term "p:num")
  and minus = (parse_term "(-)")
  and plus = (parse_term "(+)")
  and le = (parse_term "(<=)") in
  fun tm -> try let l,r = dest_binop minus tm in
                let ln = dest_numeral l
                and rn = dest_numeral r in
                if  ln <=/ rn then
                  let pth = vINST [l,p; r,n] pth0
                  and th0 = vEQT_ELIM(vNUM_LE_CONV (mk_binop le l r)) in
                  vMP pth th0
                else
                  let kn = ln -/ rn in
                  let k = mk_numeral kn in
                  let pth = vINST [k,m; l,p; r,n] pth1
                  and th0 = vNUM_ADD_CONV (mk_binop plus k r) in
                  vMP pth th0
            with Failure _ -> failwith "NUM_SUB_CONV";;

let vNUM_DIV_CONV,vNUM_MOD_CONV =
  let pth = prove
   ((parse_term "(q * n + r = m) ==> r < n ==> (m DIV n = q) /\\ (m MOD n = r)"),
    vMESON_TAC[vDIVMOD_UNIQ])
  and m = (parse_term "m:num") and n = (parse_term "n:num") and q = (parse_term "q:num") and r = (parse_term "r:num")
  and dtm = (parse_term "(DIV)") and mtm = (parse_term "(MOD)") in
  let vNUM_DIVMOD_CONV x y =
    let k = quo_num x y
    and l = mod_num x y in
    let th0 = vINST [mk_numeral x,m; mk_numeral y,n;
                    mk_numeral k,q; mk_numeral l,r] pth in
    let tm0 = lhand(lhand(concl th0)) in
    let th1 = (vLAND_CONV vNUM_MULT_CONV +---> vNUM_ADD_CONV) tm0 in
    let th2 = vMP th0 th1 in
    let tm2 = lhand(concl th2) in
    vMP th2 (vEQT_ELIM(vNUM_LT_CONV tm2)) in
  (fun tm -> try let xt,yt = dest_binop dtm tm in
                 vCONJUNCT1(vNUM_DIVMOD_CONV (dest_numeral xt) (dest_numeral yt))
             with Failure _ -> failwith "NUM_DIV_CONV"),
  (fun tm -> try let xt,yt = dest_binop mtm tm in
                 vCONJUNCT2(vNUM_DIVMOD_CONV (dest_numeral xt) (dest_numeral yt))
             with Failure _ -> failwith "NUM_MOD_CONV");;

let vNUM_FACT_CONV =
  let suc = (parse_term "SUC")
  and mul = (parse_term "(*)") in
  let pth_0 = prove
   ((parse_term "FACT 0 = 1"),
    vREWRITE_TAC[vFACT])
  and pth_suc = prove
   ((parse_term "(SUC x = y) ==> (FACT x = w) ==> (y * w = z) ==> (FACT y = z)"),
    vREPEAT (vDISCH_THEN(vSUBST1_TAC -| vSYM)) ---->
    vREWRITE_TAC[vFACT])
  and w = (parse_term "w:num") and x = (parse_term "x:num") and y = (parse_term "y:num") and z = (parse_term "z:num") in
  let mksuc n =
    let n' = n -/ (Int 1) in
    vNUM_SUC_CONV (mk_comb(suc,mk_numeral n')) in
  let rec vNUM_FACT_CONV n =
    if n =/ Int 0 then pth_0 else
    let th0 = mksuc n in
    let tmx = rand(lhand(concl th0)) in
    let tm0 = rand(concl th0) in
    let th1 = vNUM_FACT_CONV (n -/ Int 1) in
    let tm1 = rand(concl th1) in
    let th2 = vNUM_MULT_CONV (mk_binop mul tm0 tm1) in
    let tm2 = rand(concl th2) in
    let pth = vINST [tmx,x; tm0, y; tm1,w; tm2,z] pth_suc in
    vMP (vMP (vMP pth th0) th1) th2 in
  fun tm ->
    try let l,r = dest_comb tm in
        if fst(dest_const l) = "FACT"
        then vNUM_FACT_CONV (dest_numeral r)
        else fail()
    with Failure _ -> failwith "NUM_FACT_CONV";;

let vNUM_MAX_CONV =
  vREWR_CONV vMAX +--->
  vRATOR_CONV(vRATOR_CONV(vRAND_CONV vNUM_LE_CONV)) +--->
  vGEN_REWRITE_CONV vI [vCOND_CLAUSES];;

let vNUM_MIN_CONV =
  vREWR_CONV vMIN +--->
  vRATOR_CONV(vRATOR_CONV(vRAND_CONV vNUM_LE_CONV)) +--->
  vGEN_REWRITE_CONV vI [vCOND_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Final hack-together.                                                      *)
(* ------------------------------------------------------------------------- *)

let vNUM_REL_CONV =
  let gconv_net = itlist (uncurry net_of_conv)
    [(parse_term "NUMERAL m < NUMERAL n"),vNUM_LT_CONV;
     (parse_term "NUMERAL m <= NUMERAL n"),vNUM_LE_CONV;
     (parse_term "NUMERAL m > NUMERAL n"),vNUM_GT_CONV;
     (parse_term "NUMERAL m >= NUMERAL n"),vNUM_GE_CONV;
     (parse_term "NUMERAL m = NUMERAL n"),vNUM_EQ_CONV]
    (basic_net()) in
  vREWRITES_CONV gconv_net;;

let vNUM_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv)
    [(parse_term "SUC(NUMERAL n)"),vNUM_SUC_CONV;
     (parse_term "PRE(NUMERAL n)"),vNUM_PRE_CONV;
     (parse_term "FACT(NUMERAL n)"),vNUM_FACT_CONV;
     (parse_term "NUMERAL m < NUMERAL n"),vNUM_LT_CONV;
     (parse_term "NUMERAL m <= NUMERAL n"),vNUM_LE_CONV;
     (parse_term "NUMERAL m > NUMERAL n"),vNUM_GT_CONV;
     (parse_term "NUMERAL m >= NUMERAL n"),vNUM_GE_CONV;
     (parse_term "NUMERAL m = NUMERAL n"),vNUM_EQ_CONV;
     (parse_term "EVEN(NUMERAL n)"),vNUM_EVEN_CONV;
     (parse_term "ODD(NUMERAL n)"),vNUM_ODD_CONV;
     (parse_term "NUMERAL m + NUMERAL n"),vNUM_ADD_CONV;
     (parse_term "NUMERAL m - NUMERAL n"),vNUM_SUB_CONV;
     (parse_term "NUMERAL m * NUMERAL n"),vNUM_MULT_CONV;
     (parse_term "(NUMERAL m) EXP (NUMERAL n)"),vNUM_EXP_CONV;
     (parse_term "(NUMERAL m) DIV (NUMERAL n)"),vNUM_DIV_CONV;
     (parse_term "(NUMERAL m) MOD (NUMERAL n)"),vNUM_MOD_CONV;
     (parse_term "MAX (NUMERAL m) (NUMERAL n)"),vNUM_MAX_CONV;
     (parse_term "MIN (NUMERAL m) (NUMERAL n)"),vNUM_MIN_CONV]
    (basic_net()) in
  vREWRITES_CONV gconv_net;;

let vNUM_REDUCE_CONV = vDEPTH_CONV vNUM_RED_CONV;;

let vNUM_REDUCE_TAC = vCONV_TAC vNUM_REDUCE_CONV;;

(* ------------------------------------------------------------------------- *)
(* I do like this after all...                                               *)
(* ------------------------------------------------------------------------- *)

let num_CONV =
  let vSUC_tm = (parse_term "SUC") in
  fun tm ->
    let n = dest_numeral tm -/ Int 1 in
    if n </ Int 0 then failwith "num_CONV" else
    let tm' = mk_numeral n in
    vSYM(vNUM_SUC_CONV (mk_comb(vSUC_tm,tm')));;

(* ------------------------------------------------------------------------- *)
(* Expands "!n. n < numeral-constant ==> P(n)" into all the cases.           *)
(* ------------------------------------------------------------------------- *)

let vEXPAND_CASES_CONV =
  let pth_base = prove
   ((parse_term "(!n. n < 0 ==> P n) <=> T"),
    vREWRITE_TAC[vLT])
  and pth_step = prove
   ((parse_term "(!n. n < SUC k ==> P n) <=> (!n. n < k ==> P n) /\\ P k"),
    vREWRITE_TAC[vLT] ----> vMESON_TAC[]) in
  let base_CONV = vGEN_REWRITE_CONV vI [pth_base]
  and step_CONV =
    vBINDER_CONV(vLAND_CONV(vRAND_CONV num_CONV)) +--->
    vGEN_REWRITE_CONV vI [pth_step] in
  let rec conv tm =
    (base_CONV ||--> (step_CONV +---> vLAND_CONV conv)) tm in
  conv +---> (vREWRITE_CONV[vGSYM vCONJ_ASSOC]);;
