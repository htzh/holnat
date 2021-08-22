(* ========================================================================= *)
(* Calculation with integer-valued reals.                                    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Parser
open Equal
open Boolean
open Drule
open Tactics
open Simp
open Theorems
open Class
open Meson
open Nums
open Arith
open Calc_num
open Realax

open Num

(* ------------------------------------------------------------------------- *)
(* Syntax operations on integer constants of type ":real".                   *)
(* ------------------------------------------------------------------------- *)

let is_realintconst tm =
  match tm with
    Comb(Const("real_of_num",_),n) -> is_numeral n
  | Comb(Const("real_neg",_),Comb(Const("real_of_num",_),n)) ->
      is_numeral n && not(dest_numeral n = num_0)
  | _ -> false;;

let dest_realintconst tm =
  match tm with
    Comb(Const("real_of_num",_),n) -> dest_numeral n
  | Comb(Const("real_neg",_),Comb(Const("real_of_num",_),n)) ->
        let nn = dest_numeral n in
        if nn <>/ num_0 then minus_num(dest_numeral n)
        else failwith "dest_realintconst"
  | _ -> failwith "dest_realintconst";;

let mk_realintconst =
  let cast_tm = (parse_term "real_of_num") and neg_tm = (parse_term "(--)") in
  let mk_numconst n = mk_comb(cast_tm,mk_numeral n) in
  fun x -> if x </ num_0 then mk_comb(neg_tm,mk_numconst(minus_num x))
           else mk_numconst x;;

let is_ratconst tm =
  match tm with
    Comb(Comb(Const("real_div",_),p),q) ->
        is_realintconst p && is_realintconst q &&
        (let m = dest_realintconst p and n = dest_realintconst q in
         n >/ num_1 && gcd_num m n =/ num_1)
  | _ -> is_realintconst tm;;

let rat_of_term tm =
  match tm with
    Comb(Comb(Const("real_div",_),p),q) ->
        let m = dest_realintconst p and n = dest_realintconst q in
        if n >/ num_1 && gcd_num m n =/ num_1 then m // n
        else failwith "rat_of_term"
  | _ -> dest_realintconst tm;;

let term_of_rat =
  let div_tm = (parse_term "(/)") in
  fun x ->
    let p,q = numdom x in
    let ptm = mk_realintconst p in
    if q = num_1 then ptm
    else mk_comb(mk_comb(div_tm,ptm),mk_realintconst q);;

(* ------------------------------------------------------------------------- *)
(* Some elementary "bootstrapping" lemmas we need below.                     *)
(* ------------------------------------------------------------------------- *)

let vREAL_ADD_AC = prove
 ((parse_term "(m + n = n + m) /\\\n   ((m + n) + p = m + (n + p)) /\\\n   (m + (n + p) = n + (m + p))"),
  vMESON_TAC[vREAL_ADD_ASSOC; vREAL_ADD_SYM]);;

let vREAL_ADD_RINV = prove
 ((parse_term "!x. x + --x = &0"),
  vMESON_TAC[vREAL_ADD_SYM; vREAL_ADD_LINV]);;

let vREAL_EQ_ADD_LCANCEL = prove
 ((parse_term "!x y z. (x + y = x + z) <=> (y = z)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM(vMP_TAC -| vAP_TERM (parse_term "(+) (--x)")) ---->
  vREWRITE_TAC[vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_LID]);;

let vREAL_EQ_ADD_RCANCEL = prove
 ((parse_term "!x y z. (x + z = y + z) <=> (x = y)"),
  vMESON_TAC[vREAL_ADD_SYM; vREAL_EQ_ADD_LCANCEL]);;

let vREAL_MUL_RZERO = prove
 ((parse_term "!x. x * &0 = &0"),
  vMESON_TAC[vREAL_EQ_ADD_RCANCEL; vREAL_ADD_LDISTRIB; vREAL_ADD_LID]);;

let vREAL_MUL_LZERO = prove
 ((parse_term "!x. &0 * x = &0"),
  vMESON_TAC[vREAL_MUL_SYM; vREAL_MUL_RZERO]);;

let vREAL_NEG_NEG = prove
 ((parse_term "!x. --(--x) = x"),
  vMESON_TAC
   [vREAL_EQ_ADD_RCANCEL; vREAL_ADD_LINV; vREAL_ADD_SYM; vREAL_ADD_LINV]);;

let vREAL_MUL_RNEG = prove
 ((parse_term "!x y. x * (--y) = -- (x * y)"),
  vMESON_TAC[vREAL_EQ_ADD_RCANCEL; vREAL_ADD_LDISTRIB; vREAL_ADD_LINV;
            vREAL_MUL_RZERO]);;

let vREAL_MUL_LNEG = prove
 ((parse_term "!x y. (--x) * y = -- (x * y)"),
  vMESON_TAC[vREAL_MUL_SYM; vREAL_MUL_RNEG]);;

let vREAL_NEG_ADD = prove
 ((parse_term "!x y. --(x + y) = --x + --y"),
  vREPEAT vGEN_TAC ---->
  vMATCH_MP_TAC(vGEN_ALL(fst(vEQ_IMP_RULE(vSPEC_ALL vREAL_EQ_ADD_RCANCEL)))) ---->
  vEXISTS_TAC (parse_term "x + y") ----> vREWRITE_TAC[vREAL_ADD_LINV] ---->
  vONCE_REWRITE_TAC[vAC vREAL_ADD_AC (parse_term "(a + b) + (c + d) = (a + c) + (b + d)")] ---->
  vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID]);;

let vREAL_ADD_RID = prove
 ((parse_term "!x. x + &0 = x"),
  vMESON_TAC[vREAL_ADD_SYM; vREAL_ADD_LID]);;

let vREAL_NEG_0 = prove
 ((parse_term "--(&0) = &0"),
  vMESON_TAC[vREAL_ADD_LINV; vREAL_ADD_RID]);;

let vREAL_LE_LNEG = prove
 ((parse_term "!x y. --x <= y <=> &0 <= x + y"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LE_LADD_IMP) ++-->
   [vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "x:real")) ---->
    vREWRITE_TAC[vONCE_REWRITE_RULE[vREAL_ADD_SYM] vREAL_ADD_LINV];
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "--x")) ---->
    vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_ASSOC; vREAL_ADD_LID;
        vONCE_REWRITE_RULE[vREAL_ADD_SYM] vREAL_ADD_LID]]);;

let vREAL_LE_NEG2 = prove
 ((parse_term "!x y. --x <= --y <=> y <= x"),
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vGSYM vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_LE_LNEG] ---->
  vAP_TERM_TAC ----> vMATCH_ACCEPT_TAC vREAL_ADD_SYM);;

let vREAL_LE_RNEG = prove
 ((parse_term "!x y. x <= --y <=> x + y <= &0"),
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV) [vGSYM vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_LE_LNEG; vGSYM vREAL_NEG_ADD] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_LE_NEG2] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vREWRITE_TAC[vGSYM vREAL_ADD_LINV] ---->
  vREWRITE_TAC[vREAL_NEG_ADD; vREAL_NEG_NEG] ---->
  vMATCH_ACCEPT_TAC vREAL_ADD_SYM);;

let vREAL_OF_NUM_POW = prove
 ((parse_term "!x n. (&x) pow n = &(x EXP n)"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[real_pow; vEXP; vREAL_OF_NUM_MUL]);;

let vREAL_POW_NEG = prove
 ((parse_term "!x n. (--x) pow n = if EVEN n then x pow n else --(x pow n)"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[real_pow; vEVEN] ---->
  vASM_CASES_TAC (parse_term "EVEN n") ---->
  vASM_REWRITE_TAC[vREAL_MUL_RNEG; vREAL_MUL_LNEG; vREAL_NEG_NEG]);;

let vREAL_ABS_NUM = prove
 ((parse_term "!n. abs(&n) = &n"),
  vREWRITE_TAC[real_abs; vREAL_OF_NUM_LE; vLE_0]);;

let vREAL_ABS_NEG = prove
 ((parse_term "!x. abs(--x) = abs x"),
  vREWRITE_TAC[real_abs; vREAL_LE_RNEG; vREAL_NEG_NEG; vREAL_ADD_LID] ---->
  vMESON_TAC[vREAL_LE_TOTAL; vREAL_LE_ANTISYM; vREAL_NEG_0]);;

(* ------------------------------------------------------------------------- *)
(* First, the conversions on integer constants.                              *)
(* ------------------------------------------------------------------------- *)

let vREAL_INT_LE_CONV,vREAL_INT_LT_CONV,
    vREAL_INT_GE_CONV,vREAL_INT_GT_CONV,vREAL_INT_EQ_CONV =
  let tth =
    vTAUT (parse_term "(F /\\ F <=> F) /\\ (F /\\ T <=> F) /\\\n          (T /\\ F <=> F) /\\ (T /\\ T <=> T)") in
  let nth = vTAUT (parse_term "(~T <=> F) /\\ (~F <=> T)") in
  let vNUM2_EQ_CONV = vBINOP_CONV vNUM_EQ_CONV +---> vGEN_REWRITE_CONV vI [tth] in
  let vNUM2_NE_CONV =
    vRAND_CONV vNUM2_EQ_CONV +--->
    vGEN_REWRITE_CONV vI [nth] in
  let [@warning "-8"] [pth_le1; pth_le2a; pth_le2b; pth_le3] = (vCONJUNCTS -| prove)
   ((parse_term "(--(&m) <= &n <=> T) /\\\n     (&m <= &n <=> m <= n) /\\\n     (--(&m) <= --(&n) <=> n <= m) /\\\n     (&m <= --(&n) <=> (m = 0) /\\ (n = 0))"),
    vREWRITE_TAC[vREAL_LE_NEG2] ---->
    vREWRITE_TAC[vREAL_LE_LNEG; vREAL_LE_RNEG] ---->
    vREWRITE_TAC[vREAL_OF_NUM_ADD; vREAL_OF_NUM_LE; vLE_0] ---->
    vREWRITE_TAC[vLE; vADD_EQ_0]) in
  let vREAL_INT_LE_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_le1];
    vGEN_REWRITE_CONV vI [pth_le2a; pth_le2b] +---> vNUM_LE_CONV;
    vGEN_REWRITE_CONV vI [pth_le3] +---> vNUM2_EQ_CONV] in
  let [@warning "-8"] [pth_lt1; pth_lt2a; pth_lt2b; pth_lt3] = (vCONJUNCTS -| prove)
   ((parse_term "(&m < --(&n) <=> F) /\\\n     (&m < &n <=> m < n) /\\\n     (--(&m) < --(&n) <=> n < m) /\\\n     (--(&m) < &n <=> ~((m = 0) /\\ (n = 0)))"),
    vREWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3;
                vGSYM vNOT_LE; real_lt] ---->
    vCONV_TAC vTAUT) in
  let vREAL_INT_LT_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_lt1];
    vGEN_REWRITE_CONV vI [pth_lt2a; pth_lt2b] +---> vNUM_LT_CONV;
    vGEN_REWRITE_CONV vI [pth_lt3] +---> vNUM2_NE_CONV] in
  let [@warning "-8"] [pth_ge1; pth_ge2a; pth_ge2b; pth_ge3] = (vCONJUNCTS -| prove)
   ((parse_term "(&m >= --(&n) <=> T) /\\\n     (&m >= &n <=> n <= m) /\\\n     (--(&m) >= --(&n) <=> m <= n) /\\\n     (--(&m) >= &n <=> (m = 0) /\\ (n = 0))"),
    vREWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; real_ge] ---->
    vCONV_TAC vTAUT) in
  let vREAL_INT_GE_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_ge1];
    vGEN_REWRITE_CONV vI [pth_ge2a; pth_ge2b] +---> vNUM_LE_CONV;
    vGEN_REWRITE_CONV vI [pth_ge3] +---> vNUM2_EQ_CONV] in
  let [@warning "-8"] [pth_gt1; pth_gt2a; pth_gt2b; pth_gt3] = (vCONJUNCTS -| prove)
   ((parse_term "(--(&m) > &n <=> F) /\\\n     (&m > &n <=> n < m) /\\\n     (--(&m) > --(&n) <=> m < n) /\\\n     (&m > --(&n) <=> ~((m = 0) /\\ (n = 0)))"),
    vREWRITE_TAC[pth_lt1; pth_lt2a; pth_lt2b; pth_lt3; real_gt] ---->
    vCONV_TAC vTAUT) in
  let vREAL_INT_GT_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_gt1];
    vGEN_REWRITE_CONV vI [pth_gt2a; pth_gt2b] +---> vNUM_LT_CONV;
    vGEN_REWRITE_CONV vI [pth_gt3] +---> vNUM2_NE_CONV] in
  let [@warning "-8"] [pth_eq1a; pth_eq1b; pth_eq2a; pth_eq2b] = (vCONJUNCTS -| prove)
   ((parse_term "((&m = &n) <=> (m = n)) /\\\n     ((--(&m) = --(&n)) <=> (m = n)) /\\\n     ((--(&m) = &n) <=> (m = 0) /\\ (n = 0)) /\\\n     ((&m = --(&n)) <=> (m = 0) /\\ (n = 0))"),
    vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM; vGSYM vLE_ANTISYM] ---->
    vREWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; vLE; vLE_0] ---->
    vCONV_TAC vTAUT) in
  let vREAL_INT_EQ_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_eq1a; pth_eq1b] +---> vNUM_EQ_CONV;
    vGEN_REWRITE_CONV vI [pth_eq2a; pth_eq2b] +---> vNUM2_EQ_CONV] in
  vREAL_INT_LE_CONV,vREAL_INT_LT_CONV,
  vREAL_INT_GE_CONV,vREAL_INT_GT_CONV,vREAL_INT_EQ_CONV;;

let vREAL_INT_NEG_CONV =
  let pth = prove
   ((parse_term "(--(&0) = &0) /\\\n     (--(--(&x)) = &x)"),
    vREWRITE_TAC[vREAL_NEG_NEG; vREAL_NEG_0]) in
  vGEN_REWRITE_CONV vI [pth];;

let vREAL_INT_MUL_CONV =
  let pth0 = prove
   ((parse_term "(&0 * &x = &0) /\\\n     (&0 * --(&x) = &0) /\\\n     (&x * &0 = &0) /\\\n     (--(&x) * &0 = &0)"),
    vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_MUL_RZERO])
  and pth1,pth2 = (vCONJ_PAIR -| prove)
   ((parse_term "((&m * &n = &(m * n)) /\\\n      (--(&m) * --(&n) = &(m * n))) /\\\n     ((--(&m) * &n = --(&(m * n))) /\\\n      (&m * --(&n) = --(&(m * n))))"),
    vREWRITE_TAC[vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG] ---->
    vREWRITE_TAC[vREAL_OF_NUM_MUL]) in
  vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth0];
    vGEN_REWRITE_CONV vI [pth1] +---> vRAND_CONV vNUM_MULT_CONV;
    vGEN_REWRITE_CONV vI [pth2] +---> vRAND_CONV(vRAND_CONV vNUM_MULT_CONV)];;

let vREAL_INT_ADD_CONV =
  let neg_tm = (parse_term "(--)") in
  let amp_tm = (parse_term "&") in
  let add_tm = (parse_term "(+)") in
  let dest = dest_binop (parse_term "(+)") in
  let m_tm = (parse_term "m:num") and n_tm = (parse_term "n:num") in
  let pth0 = prove
   ((parse_term "(--(&m) + &m = &0) /\\\n     (&m + --(&m) = &0)"),
    vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_RINV]) in
  let [@warning "-8"] [pth1; pth2; pth3; pth4; pth5; pth6] = (vCONJUNCTS -| prove)
   ((parse_term "(--(&m) + --(&n) = --(&(m + n))) /\\\n     (--(&m) + &(m + n) = &n) /\\\n     (--(&(m + n)) + &m = --(&n)) /\\\n     (&(m + n) + --(&m) = &n) /\\\n     (&m + --(&(m + n)) = --(&n)) /\\\n     (&m + &n = &(m + n))"),
    vREWRITE_TAC[vGSYM vREAL_OF_NUM_ADD; vREAL_NEG_ADD] ---->
    vREWRITE_TAC[vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_LID] ---->
    vREWRITE_TAC[vREAL_ADD_RINV; vREAL_ADD_LID] ---->
    vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
    vREWRITE_TAC[vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_LID] ---->
    vREWRITE_TAC[vREAL_ADD_RINV; vREAL_ADD_LID]) in
  vGEN_REWRITE_CONV vI [pth0] ||-->
  (fun tm ->
    try let l,r = dest tm in
        if rator l = neg_tm then
          if rator r = neg_tm then
            let th1 = vINST [rand(rand l),m_tm; rand(rand r),n_tm] pth1 in
            let tm1 = rand(rand(rand(concl th1))) in
            let th2 = vAP_TERM neg_tm (vAP_TERM amp_tm (vNUM_ADD_CONV tm1)) in
            vTRANS th1 th2
          else
            let m = rand(rand l) and n = rand r in
            let m' = dest_numeral m and n' = dest_numeral n in
            if m' <=/ n' then
              let p = mk_numeral (n' -/ m') in
              let th1 = vINST [m,m_tm; p,n_tm] pth2 in
              let th2 = vNUM_ADD_CONV (rand(rand(lhand(concl th1)))) in
              let th3 = vAP_TERM (rator tm) (vAP_TERM amp_tm (vSYM th2)) in
              vTRANS th3 th1
            else
              let p = mk_numeral (m' -/ n') in
              let th1 = vINST [n,m_tm; p,n_tm] pth3 in
              let th2 = vNUM_ADD_CONV (rand(rand(lhand(lhand(concl th1))))) in
              let th3 = vAP_TERM neg_tm (vAP_TERM amp_tm (vSYM th2)) in
              let th4 = vAP_THM (vAP_TERM add_tm th3) (rand tm) in
              vTRANS th4 th1
        else
          if rator r = neg_tm then
            let m = rand l and n = rand(rand r) in
            let m' = dest_numeral m and n' = dest_numeral n in
            if n' <=/ m' then
              let p = mk_numeral (m' -/ n') in
              let th1 = vINST [n,m_tm; p,n_tm] pth4 in
              let th2 = vNUM_ADD_CONV (rand(lhand(lhand(concl th1)))) in
              let th3 = vAP_TERM add_tm (vAP_TERM amp_tm (vSYM th2)) in
              let th4 = vAP_THM th3 (rand tm) in
              vTRANS th4 th1
            else
             let p = mk_numeral (n' -/ m') in
             let th1 = vINST [m,m_tm; p,n_tm] pth5 in
             let th2 = vNUM_ADD_CONV (rand(rand(rand(lhand(concl th1))))) in
             let th3 = vAP_TERM neg_tm (vAP_TERM amp_tm (vSYM th2)) in
             let th4 = vAP_TERM (rator tm) th3 in
             vTRANS th4 th1
          else
            let th1 = vINST [rand l,m_tm; rand r,n_tm] pth6 in
            let tm1 = rand(rand(concl th1)) in
            let th2 = vAP_TERM amp_tm (vNUM_ADD_CONV tm1) in
            vTRANS th1 th2
    with Failure _ -> failwith "REAL_INT_ADD_CONV");;

let vREAL_INT_SUB_CONV =
  vGEN_REWRITE_CONV vI [real_sub] +--->
  vTRY_CONV(vRAND_CONV vREAL_INT_NEG_CONV) +--->
  vREAL_INT_ADD_CONV;;

let vREAL_INT_POW_CONV =
  let pth1,pth2 = (vCONJ_PAIR -| prove)
   ((parse_term "(&x pow n = &(x EXP n)) /\\\n     ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))"),
    vREWRITE_TAC[vREAL_OF_NUM_POW; vREAL_POW_NEG]) in
  let tth = prove
   ((parse_term "((if T then x:real else y) = x) /\\ ((if F then x:real else y) = y)"),
    vREWRITE_TAC[]) in
  let neg_tm = (parse_term "(--)") in
  (vGEN_REWRITE_CONV vI [pth1] +---> vRAND_CONV vNUM_EXP_CONV) ||-->
  (vGEN_REWRITE_CONV vI [pth2] +--->
   vRATOR_CONV(vRATOR_CONV(vRAND_CONV vNUM_EVEN_CONV)) +--->
   vGEN_REWRITE_CONV vI [tth] +--->
   (fun tm -> if rator tm = neg_tm then vRAND_CONV(vRAND_CONV vNUM_EXP_CONV) tm
              else vRAND_CONV vNUM_EXP_CONV  tm));;

let vREAL_INT_ABS_CONV =
  let pth = prove
   ((parse_term "(abs(--(&x)) = &x) /\\\n     (abs(&x) = &x)"),
    vREWRITE_TAC[vREAL_ABS_NEG; vREAL_ABS_NUM]) in
  vGEN_REWRITE_CONV vI [pth];;

let vREAL_INT_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv)
    [(parse_term "x <= y"),vREAL_INT_LE_CONV;
     (parse_term "x < y"),vREAL_INT_LT_CONV;
     (parse_term "x >= y"),vREAL_INT_GE_CONV;
     (parse_term "x > y"),vREAL_INT_GT_CONV;
     (parse_term "x:real = y"),vREAL_INT_EQ_CONV;
     (parse_term "--x"),vCHANGED_CONV vREAL_INT_NEG_CONV;
     (parse_term "abs(x)"),vREAL_INT_ABS_CONV;
     (parse_term "x + y"),vREAL_INT_ADD_CONV;
     (parse_term "x - y"),vREAL_INT_SUB_CONV;
     (parse_term "x * y"),vREAL_INT_MUL_CONV;
     (parse_term "x pow n"),vREAL_INT_POW_CONV]
    (basic_net()) in
  vREWRITES_CONV gconv_net;;

let vREAL_INT_REDUCE_CONV = vDEPTH_CONV vREAL_INT_RED_CONV;;
