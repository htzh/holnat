(* ========================================================================= *)
(* Calculation with rational-valued reals.                                   *)
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
open Theorems
open Class
open Canon
open Meson
open Nums
open Arith
open Calc_num
open Normalizer
open Grobner
open Realax
open Calc_int
open Realarith
open Real

open Num

(* ------------------------------------------------------------------------- *)
(* Constant for decimal fractions written #xxx.yyy                           *)
(* ------------------------------------------------------------------------- *)

let vDECIMAL = new_definition
  (parse_term "DECIMAL x y = &x / &y");;

(* ------------------------------------------------------------------------- *)
(* Various handy lemmas.                                                     *)
(* ------------------------------------------------------------------------- *)

let vRAT_LEMMA1 = prove
 ((parse_term "~(y1 = &0) /\\ ~(y2 = &0) ==>\n      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))"),
  vSTRIP_TAC ----> vREWRITE_TAC[real_div; vREAL_ADD_RDISTRIB] ----> vBINOP_TAC ++-->
   [vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vAP_TERM_TAC ----> vONCE_REWRITE_TAC
     [vAC vREAL_MUL_AC (parse_term "a * b * c = (b * a) * c")];
    vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_RID] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vREWRITE_TAC[vREAL_EQ_MUL_LCANCEL] ---->
  vDISJ2_TAC ----> vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_MUL_RINV ---->
  vASM_REWRITE_TAC[]);;

let vRAT_LEMMA2 = prove
 ((parse_term "&0 < y1 /\\ &0 < y2 ==>\n      ((x1 / y1) + (x2 / y2) = (x1 * y2 + x2 * y1) * inv(y1) * inv(y2))"),
  vDISCH_TAC ----> vMATCH_MP_TAC vRAT_LEMMA1 ----> vPOP_ASSUM vMP_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vCONTRAPOS_THM] ---->
  vREWRITE_TAC[vDE_MORGAN_THM] ----> vSTRIP_TAC ---->
  vASM_REWRITE_TAC[vREAL_LT_REFL]);;

let vRAT_LEMMA3 = prove
 ((parse_term "&0 < y1 /\\ &0 < y2 ==>\n      ((x1 / y1) - (x2 / y2) = (x1 * y2 - x2 * y1) * inv(y1) * inv(y2))"),
  vDISCH_THEN(vMP_TAC -| vGEN_ALL -| vMATCH_MP vRAT_LEMMA2) ---->
  vREWRITE_TAC[real_div] ----> vDISCH_TAC ---->
  vASM_REWRITE_TAC[real_sub; vGSYM vREAL_MUL_LNEG]);;

let vRAT_LEMMA4 = prove
 ((parse_term "&0 < y1 /\\ &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)"),
  let lemma = prove
   ((parse_term "&0 < y ==> (&0 <= x * y <=> &0 <= x)"),
    vDISCH_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
     [vSUBGOAL_THEN (parse_term "&0 <= x * (y * inv y)") vMP_TAC ++-->
       [vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vMATCH_MP_TAC vREAL_LE_MUL ---->
        vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LE_INV ---->
        vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
        vSUBGOAL_THEN (parse_term "y * inv y = &1") (fun th ->
          vREWRITE_TAC[th; vREAL_MUL_RID]) ---->
        vMATCH_MP_TAC vREAL_MUL_RINV ---->
        vUNDISCH_TAC (parse_term "&0 < y") ----> vREAL_ARITH_TAC];
      vMATCH_MP_TAC vREAL_LE_MUL ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]]) in
  vONCE_REWRITE_TAC[vCONJ_SYM] ----> vDISCH_TAC ---->
  vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "a <= b <=> &0 <= b - a")] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vRAT_LEMMA3 th]) ---->
  vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "&0 <= (x2 * y1 - x1 * y2) * inv y2") ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vCONJ_TAC ---->
  vMATCH_MP_TAC lemma ----> vMATCH_MP_TAC vREAL_LT_INV ---->
  vASM_REWRITE_TAC[]);;

let vRAT_LEMMA5 = prove
 ((parse_term "&0 < y1 /\\ &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))"),
  vREPEAT vDISCH_TAC ----> vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
  vMATCH_MP_TAC(vTAUT (parse_term "(a <=> a') /\\ (b <=> b') ==> (a /\\ b <=> a' /\\ b')")) ---->
  vCONJ_TAC ----> vMATCH_MP_TAC vRAT_LEMMA4 ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Create trivial rational from integer or decimal, and postconvert back.    *)
(* ------------------------------------------------------------------------- *)

let vREAL_INT_RAT_CONV =
  let pth = prove
   ((parse_term "(&x = &x / &1) /\\\n     (--(&x) = --(&x) / &1) /\\\n     (DECIMAL x y = &x / &y) /\\\n     (--(DECIMAL x y) = --(&x) / &y)"),
    vREWRITE_TAC[vREAL_DIV_1; vDECIMAL] ---->
    vREWRITE_TAC[real_div; vREAL_MUL_LNEG]) in
  vTRY_CONV(vGEN_REWRITE_CONV vI [pth]);;

(* ------------------------------------------------------------------------- *)
(* Relational operations.                                                    *)
(* ------------------------------------------------------------------------- *)

let vREAL_RAT_LE_CONV =
  let pth = prove
   ((parse_term "&0 < y1 ==> &0 < y2 ==> (x1 / y1 <= x2 / y2 <=> x1 * y2 <= x2 * y1)"),
    vREWRITE_TAC[vIMP_IMP; vRAT_LEMMA4])
  and x1 = (parse_term "x1:real") and x2 = (parse_term "x2:real")
  and y1 = (parse_term "y1:real") and y2 = (parse_term "y2:real")
  and dest_le = dest_binop (parse_term "(<=)")
  and dest_div = dest_binop (parse_term "(/)") in
  let vRAW_REAL_RAT_LE_CONV tm =
    let l,r = dest_le tm in
    let lx,ly = dest_div l
    and rx,ry = dest_div r in
    let th0 = vINST [lx,x1; ly,y1; rx,x2; ry,y2] pth in
    let th1 = funpow 2 (vMP_CONV vREAL_INT_LT_CONV) th0 in
    let th2 = (vBINOP_CONV vREAL_INT_MUL_CONV +---> vREAL_INT_LE_CONV)
              (rand(concl th1)) in
    vTRANS th1 th2 in
   vBINOP_CONV vREAL_INT_RAT_CONV +---> vRAW_REAL_RAT_LE_CONV;;

let vREAL_RAT_LT_CONV =
  let pth = prove
   ((parse_term "&0 < y1 ==> &0 < y2 ==> (x1 / y1 < x2 / y2 <=> x1 * y2 < x2 * y1)"),
    vREWRITE_TAC[vIMP_IMP] ---->
    vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vGSYM vREAL_NOT_LE] ---->
    vSIMP_TAC[vTAUT (parse_term "(~a <=> ~b) <=> (a <=> b)"); vRAT_LEMMA4])
  and x1 = (parse_term "x1:real") and x2 = (parse_term "x2:real")
  and y1 = (parse_term "y1:real") and y2 = (parse_term "y2:real")
  and dest_lt = dest_binop (parse_term "(<)")
  and dest_div = dest_binop (parse_term "(/)") in
  let vRAW_REAL_RAT_LT_CONV tm =
    let l,r = dest_lt tm in
    let lx,ly = dest_div l
    and rx,ry = dest_div r in
    let th0 = vINST [lx,x1; ly,y1; rx,x2; ry,y2] pth in
    let th1 = funpow 2 (vMP_CONV vREAL_INT_LT_CONV) th0 in
    let th2 = (vBINOP_CONV vREAL_INT_MUL_CONV +---> vREAL_INT_LT_CONV)
              (rand(concl th1)) in
    vTRANS th1 th2 in
   vBINOP_CONV vREAL_INT_RAT_CONV +---> vRAW_REAL_RAT_LT_CONV;;

let vREAL_RAT_GE_CONV =
  vGEN_REWRITE_CONV vI [real_ge] +---> vREAL_RAT_LE_CONV;;

let vREAL_RAT_GT_CONV =
  vGEN_REWRITE_CONV vI [real_gt] +---> vREAL_RAT_LT_CONV;;

let vREAL_RAT_EQ_CONV =
  let pth = prove
   ((parse_term "&0 < y1 ==> &0 < y2 ==> ((x1 / y1 = x2 / y2) <=> (x1 * y2 = x2 * y1))"),
    vREWRITE_TAC[vIMP_IMP; vRAT_LEMMA5])
  and x1 = (parse_term "x1:real") and x2 = (parse_term "x2:real")
  and y1 = (parse_term "y1:real") and y2 = (parse_term "y2:real")
  and dest_eq = dest_binop (parse_term "(=) :real->real->bool")
  and dest_div = dest_binop (parse_term "(/)") in
  let vRAW_REAL_RAT_EQ_CONV tm =
    let l,r = dest_eq tm in
    let lx,ly = dest_div l
    and rx,ry = dest_div r in
    let th0 = vINST [lx,x1; ly,y1; rx,x2; ry,y2] pth in
    let th1 = funpow 2 (vMP_CONV vREAL_INT_LT_CONV) th0 in
    let th2 = (vBINOP_CONV vREAL_INT_MUL_CONV +---> vREAL_INT_EQ_CONV)
              (rand(concl th1)) in
    vTRANS th1 th2 in
   vBINOP_CONV vREAL_INT_RAT_CONV +---> vRAW_REAL_RAT_EQ_CONV;;

let vREAL_RAT_SGN_CONV =
  vGEN_REWRITE_CONV vI [real_sgn] +--->
  vRATOR_CONV(vLAND_CONV vREAL_RAT_LT_CONV) +--->
  (vGEN_REWRITE_CONV vI [vCONJUNCT1(vSPEC_ALL vCOND_CLAUSES)] ||-->
   (vGEN_REWRITE_CONV vI [vCONJUNCT2(vSPEC_ALL vCOND_CLAUSES)] +--->
    vRATOR_CONV(vLAND_CONV vREAL_RAT_LT_CONV) +--->
    vGEN_REWRITE_CONV vI [vCOND_CLAUSES]));;

(* ------------------------------------------------------------------------- *)
(* The unary operations; all easy.                                           *)
(* ------------------------------------------------------------------------- *)

let vREAL_RAT_NEG_CONV =
  let pth = prove
   ((parse_term "(--(&0) = &0) /\\\n     (--(--(&n)) = &n) /\\\n     (--(&m / &n) = --(&m) / &n) /\\\n     (--(--(&m) / &n) = &m / &n) /\\\n     (--(DECIMAL m n) = --(&m) / &n)"),
    vREWRITE_TAC[real_div; vREAL_INV_NEG; vREAL_MUL_LNEG; vREAL_NEG_NEG;
     vREAL_NEG_0; vDECIMAL])
  and ptm = (parse_term "(--)") in
  let conv1 = vGEN_REWRITE_CONV vI [pth] in
  fun tm -> try conv1 tm
            with Failure _ -> try
                let l,r = dest_comb tm in
                if l = ptm && is_realintconst r && dest_realintconst r >/ num_0
                then vREFL tm
                else fail()
            with Failure _ -> failwith "REAL_RAT_NEG_CONV";;

let vREAL_RAT_ABS_CONV =
  let pth = prove
   ((parse_term "(abs(&n) = &n) /\\\n     (abs(--(&n)) = &n) /\\\n     (abs(&m / &n) = &m / &n) /\\\n     (abs(--(&m) / &n) = &m / &n) /\\\n     (abs(DECIMAL m n) = &m / &n) /\\\n     (abs(--(DECIMAL m n)) = &m / &n)"),
    vREWRITE_TAC[vDECIMAL; vREAL_ABS_DIV; vREAL_ABS_NEG; vREAL_ABS_NUM]) in
  vGEN_REWRITE_CONV vI [pth];;

let vREAL_RAT_INV_CONV =
  let pth1 = prove
   ((parse_term "(inv(&0) = &0) /\\\n     (inv(&1) = &1) /\\\n     (inv(-- &1) = --(&1)) /\\\n     (inv(&1 / &n) = &n) /\\\n     (inv(-- &1 / &n) = -- &n)"),
    vREWRITE_TAC[vREAL_INV_0; vREAL_INV_1; vREAL_INV_NEG;
                vREAL_INV_DIV; vREAL_DIV_1] ---->
    vREWRITE_TAC[real_div; vREAL_INV_NEG; vREAL_MUL_RNEG; vREAL_INV_1;
                vREAL_MUL_RID])
  and pth2 = prove
   ((parse_term "(inv(&n) = &1 / &n) /\\\n     (inv(--(&n)) = --(&1) / &n) /\\\n     (inv(&m / &n) = &n / &m) /\\\n     (inv(--(&m) / &n) = --(&n) / &m) /\\\n     (inv(DECIMAL m n) = &n / &m) /\\\n     (inv(--(DECIMAL m n)) = --(&n) / &m)"),
    vREWRITE_TAC[vDECIMAL; vREAL_INV_DIV] ---->
    vREWRITE_TAC[vREAL_INV_NEG; real_div; vREAL_MUL_RNEG; vREAL_MUL_AC;
      vREAL_MUL_LID; vREAL_MUL_LNEG; vREAL_INV_MUL; vREAL_INV_INV]) in
  vGEN_REWRITE_CONV vI [pth1] ||-->
  vGEN_REWRITE_CONV vI [pth2];;

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)

let vREAL_RAT_ADD_CONV =
  let pth = prove
   ((parse_term "&0 < y1 ==> &0 < y2 ==> &0 < y3 ==>\n     ((x1 * y2 + x2 * y1) * y3 = x3 * y1 * y2)\n     ==> (x1 / y1 + x2 / y2 = x3 / y3)"),
    vREPEAT vDISCH_TAC ---->
    vMP_TAC vRAT_LEMMA2 ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN vSUBST1_TAC ---->
    vREWRITE_TAC[vGSYM vREAL_INV_MUL; vGSYM real_div] ---->
    vSUBGOAL_THEN (parse_term "&0 < y1 * y2 /\\ &0 < y3") vMP_TAC ++-->
     [vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_MUL ---->
      vASM_REWRITE_TAC[];
      vDISCH_THEN(fun th -> vASM_REWRITE_TAC[vMATCH_MP vRAT_LEMMA5 th])])
  and dest_divop = dest_binop (parse_term "(/)")
  and dest_addop = dest_binop (parse_term "(+)")
  and x1 = (parse_term "x1:real") and x2 = (parse_term "x2:real") and x3 = (parse_term "x3:real")
  and y1 = (parse_term "y1:real") and y2 = (parse_term "y2:real") and y3 = (parse_term "y3:real") in
  let vRAW_REAL_RAT_ADD_CONV tm =
    let r1,r2 = dest_addop tm in
    let x1',y1' = dest_divop r1
    and x2',y2' = dest_divop r2 in
    let x1n = dest_realintconst x1' and y1n = dest_realintconst y1'
    and x2n = dest_realintconst x2' and y2n = dest_realintconst y2' in
    let x3n = x1n */ y2n +/ x2n */ y1n
    and y3n = y1n */ y2n in
    let d = gcd_num x3n y3n in
    let x3n' = quo_num x3n d and y3n' = quo_num y3n d in
    let x3n'',y3n'' = if y3n' >/ Int 0 then x3n',y3n'
                      else minus_num x3n',minus_num y3n' in
    let x3' = mk_realintconst x3n'' and y3' = mk_realintconst y3n'' in
    let th0 = vINST [x1',x1; y1',y1; x2',x2; y2',y2; x3',x3; y3',y3] pth in
    let th1 = funpow 3 (vMP_CONV vREAL_INT_LT_CONV) th0 in
    let tm2,tm3 = dest_eq(fst(dest_imp(concl th1))) in
    let th2 = (vLAND_CONV (vBINOP_CONV vREAL_INT_MUL_CONV +--->
                          vREAL_INT_ADD_CONV) +--->
               vREAL_INT_MUL_CONV) tm2
    and th3 = (vRAND_CONV vREAL_INT_MUL_CONV +---> vREAL_INT_MUL_CONV) tm3 in
    vMP th1 (vTRANS th2 (vSYM th3)) in
   vBINOP_CONV vREAL_INT_RAT_CONV +--->
   vRAW_REAL_RAT_ADD_CONV +---> vTRY_CONV(vGEN_REWRITE_CONV vI [vREAL_DIV_1]);;

(* ------------------------------------------------------------------------- *)
(* Subtraction.                                                              *)
(* ------------------------------------------------------------------------- *)

let vREAL_RAT_SUB_CONV =
  let pth = prove
   ((parse_term "x - y = x + --y"),
    vREWRITE_TAC[real_sub]) in
  vGEN_REWRITE_CONV vI [pth] +--->
  vRAND_CONV vREAL_RAT_NEG_CONV +---> vREAL_RAT_ADD_CONV;;

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)

let vREAL_RAT_MUL_CONV =
  let pth_nocancel = prove
   ((parse_term "(x1 / y1) * (x2 / y2) = (x1 * x2) / (y1 * y2)"),
    vREWRITE_TAC[real_div; vREAL_INV_MUL; vREAL_MUL_AC])
  and pth_cancel = prove
   ((parse_term "~(d1 = &0) /\\ ~(d2 = &0) /\\\n     (d1 * u1 = x1) /\\ (d2 * u2 = x2) /\\\n     (d2 * v1 = y1) /\\ (d1 * v2 = y2)\n     ==> ((x1 / y1) * (x2 / y2) = (u1 * u2) / (v1 * v2))"),
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vDISCH_THEN(vREPEAT_TCL vCONJUNCTS_THEN (vSUBST1_TAC -| vSYM)) ---->
    vASM_REWRITE_TAC[real_div; vREAL_INV_MUL] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
     (parse_term "((d1 * u1) * (id2 * iv1)) * ((d2 * u2) * id1 * iv2) =\n      (u1 * u2) * (iv1 * iv2) * (id2 * d2) * (id1 * d1)")] ---->
    vASM_SIMP_TAC[vREAL_MUL_LINV; vREAL_MUL_RID])
  and dest_divop = dest_binop (parse_term "(/)")
  and dest_mulop = dest_binop (parse_term "(*)")
  and x1 = (parse_term "x1:real") and x2 = (parse_term "x2:real")
  and y1 = (parse_term "y1:real") and y2 = (parse_term "y2:real")
  and u1 = (parse_term "u1:real") and u2 = (parse_term "u2:real")
  and v1 = (parse_term "v1:real") and v2 = (parse_term "v2:real")
  and d1 = (parse_term "d1:real") and d2 = (parse_term "d2:real") in
  let vRAW_REAL_RAT_MUL_CONV tm =
    let r1,r2 = dest_mulop tm in
    let x1',y1' = dest_divop r1
    and x2',y2' = dest_divop r2 in
    let x1n = dest_realintconst x1' and y1n = dest_realintconst y1'
    and x2n = dest_realintconst x2' and y2n = dest_realintconst y2' in
    let d1n = gcd_num x1n y2n
    and d2n = gcd_num x2n y1n in
    if d1n = num_1 && d2n = num_1 then
      let th0 = vINST [x1',x1; y1',y1; x2',x2; y2',y2] pth_nocancel in
      let th1 = vBINOP_CONV vREAL_INT_MUL_CONV (rand(concl th0)) in
      vTRANS th0 th1
    else
      let u1n = quo_num x1n d1n
      and u2n = quo_num x2n d2n
      and v1n = quo_num y1n d2n
      and v2n = quo_num y2n d1n in
      let u1' = mk_realintconst u1n
      and u2' = mk_realintconst u2n
      and v1' = mk_realintconst v1n
      and v2' = mk_realintconst v2n
      and d1' = mk_realintconst d1n
      and d2' = mk_realintconst d2n in
      let th0 = vINST [x1',x1; y1',y1; x2',x2; y2',y2;
                      u1',u1; v1',v1; u2',u2; v2',v2; d1',d1; d2',d2]
                     pth_cancel in
      let th1 = vEQT_ELIM(vREAL_INT_REDUCE_CONV(lhand(concl th0))) in
      let th2 = vMP th0 th1 in
      let th3 = vBINOP_CONV vREAL_INT_MUL_CONV (rand(concl th2)) in
      vTRANS th2 th3 in
   vBINOP_CONV vREAL_INT_RAT_CONV +--->
   vRAW_REAL_RAT_MUL_CONV +---> vTRY_CONV(vGEN_REWRITE_CONV vI [vREAL_DIV_1]);;

(* ------------------------------------------------------------------------- *)
(* Division.                                                                 *)
(* ------------------------------------------------------------------------- *)

let vREAL_RAT_DIV_CONV =
  let pth = prove
   ((parse_term "x / y = x * inv(y)"),
    vREWRITE_TAC[real_div]) in
  vGEN_REWRITE_CONV vI [pth] +--->
  vRAND_CONV vREAL_RAT_INV_CONV +---> vREAL_RAT_MUL_CONV;;

(* ------------------------------------------------------------------------- *)
(* Powers.                                                                   *)
(* ------------------------------------------------------------------------- *)

let vREAL_RAT_POW_CONV =
  let pth = prove
   ((parse_term "(x / y) pow n = (x pow n) / (y pow n)"),
    vREWRITE_TAC[vREAL_POW_DIV]) in
  vREAL_INT_POW_CONV ||-->
  (vLAND_CONV vREAL_INT_RAT_CONV +--->
   vGEN_REWRITE_CONV vI [pth] +--->
   vBINOP_CONV vREAL_INT_POW_CONV);;

(* ------------------------------------------------------------------------- *)
(* Max and min.                                                              *)
(* ------------------------------------------------------------------------- *)

let vREAL_RAT_MAX_CONV =
  vREWR_CONV real_max +--->
  vRATOR_CONV(vRATOR_CONV(vRAND_CONV vREAL_RAT_LE_CONV)) +--->
  vGEN_REWRITE_CONV vI [vCOND_CLAUSES];;

let vREAL_RAT_MIN_CONV =
  vREWR_CONV real_min +--->
  vRATOR_CONV(vRATOR_CONV(vRAND_CONV vREAL_RAT_LE_CONV)) +--->
  vGEN_REWRITE_CONV vI [vCOND_CLAUSES];;

(* ------------------------------------------------------------------------- *)
(* Everything.                                                               *)
(* ------------------------------------------------------------------------- *)

let vREAL_RAT_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv)
    [(parse_term "x <= y"),vREAL_RAT_LE_CONV;
     (parse_term "x < y"),vREAL_RAT_LT_CONV;
     (parse_term "x >= y"),vREAL_RAT_GE_CONV;
     (parse_term "x > y"),vREAL_RAT_GT_CONV;
     (parse_term "x:real = y"),vREAL_RAT_EQ_CONV;
     (parse_term "--x"),vCHANGED_CONV vREAL_RAT_NEG_CONV;
     (parse_term "real_sgn(x)"),vREAL_RAT_SGN_CONV;
     (parse_term "abs(x)"),vREAL_RAT_ABS_CONV;
     (parse_term "inv(x)"),vREAL_RAT_INV_CONV;
     (parse_term "x + y"),vREAL_RAT_ADD_CONV;
     (parse_term "x - y"),vREAL_RAT_SUB_CONV;
     (parse_term "x * y"),vREAL_RAT_MUL_CONV;
     (parse_term "x / y"),vCHANGED_CONV vREAL_RAT_DIV_CONV;
     (parse_term "x pow n"),vREAL_RAT_POW_CONV;
     (parse_term "max x y"),vREAL_RAT_MAX_CONV;
     (parse_term "min x y"),vREAL_RAT_MIN_CONV]
    (basic_net()) in
  vREWRITES_CONV gconv_net;;

let vREAL_RAT_REDUCE_CONV = vDEPTH_CONV vREAL_RAT_RED_CONV;;

(* ------------------------------------------------------------------------- *)
(* Real normalizer dealing with rational constants.                          *)
(* ------------------------------------------------------------------------- *)

let vREAL_POLY_NEG_CONV,vREAL_POLY_ADD_CONV,vREAL_POLY_SUB_CONV,
    vREAL_POLY_MUL_CONV,vREAL_POLY_POW_CONV,_vREAL_POLY_CONV =
  vSEMIRING_NORMALIZERS_CONV vREAL_POLY_CLAUSES vREAL_POLY_NEG_CLAUSES
   (is_ratconst,
    vREAL_RAT_ADD_CONV,vREAL_RAT_MUL_CONV,vREAL_RAT_POW_CONV)
   (<);;

(* ------------------------------------------------------------------------- *)
(* Extend normalizer to handle "inv" and division by rational constants, and *)
(* normalize inside nested "max", "min" and "abs" terms.                     *)
(* ------------------------------------------------------------------------- *)

let vREAL_POLY_CONV =
  let neg_tm = (parse_term "(--):real->real")
  and inv_tm = (parse_term "inv:real->real")
  and add_tm = (parse_term "(+):real->real->real")
  and sub_tm = (parse_term "(-):real->real->real")
  and mul_tm = (parse_term "(*):real->real->real")
  and div_tm = (parse_term "(/):real->real->real")
  and pow_tm = (parse_term "(pow):real->num->real")
  and abs_tm = (parse_term "abs:real->real")
  and max_tm = (parse_term "max:real->real->real")
  and min_tm = (parse_term "min:real->real->real")
  and div_conv = vREWR_CONV real_div in
  let rec vREAL_POLY_CONV tm =
    if not(is_comb tm) || is_ratconst tm then vREFL tm else
    let lop,r = dest_comb tm in
    if lop = neg_tm then
      let th1 = vAP_TERM lop (vREAL_POLY_CONV r) in
      vTRANS th1 (vREAL_POLY_NEG_CONV (rand(concl th1)))
    else if lop = inv_tm then
      let th1 = vAP_TERM lop (vREAL_POLY_CONV r) in
      vTRANS th1 (vTRY_CONV vREAL_RAT_INV_CONV (rand(concl th1)))
    else if lop = abs_tm then
      vAP_TERM lop (vREAL_POLY_CONV r)
    else if not(is_comb lop) then vREFL tm else
    let op,l = dest_comb lop in
    if op = pow_tm then
      let th1 = vAP_THM (vAP_TERM op (vREAL_POLY_CONV l)) r in
      vTRANS th1 (vTRY_CONV vREAL_POLY_POW_CONV (rand(concl th1)))
    else if op = add_tm || op = mul_tm || op = sub_tm then
      let th1 = vMK_COMB(vAP_TERM op (vREAL_POLY_CONV l),
                        vREAL_POLY_CONV r) in
      let fn = if op = add_tm then vREAL_POLY_ADD_CONV
               else if op = mul_tm then vREAL_POLY_MUL_CONV
               else vREAL_POLY_SUB_CONV in
      vTRANS th1 (fn (rand(concl th1)))
    else if op = div_tm then
      let th1 = div_conv tm in
      vTRANS th1 (vREAL_POLY_CONV (rand(concl th1)))
    else if op = min_tm || op = max_tm then
      vMK_COMB(vAP_TERM op (vREAL_POLY_CONV l),vREAL_POLY_CONV r)
    else vREFL tm in
  vREAL_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Basic ring and ideal conversions.                                         *)
(* ------------------------------------------------------------------------- *)

let vREAL_RING,real_ideal_cofactors =
  let vREAL_INTEGRAL = prove
   ((parse_term "(!x. &0 * x = &0) /\\\n     (!x y z. (x + y = x + z) <=> (y = z)) /\\\n     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \\/ (y = z))"),
    vREWRITE_TAC[vMULT_CLAUSES; vEQ_ADD_LCANCEL] ---->
    vREWRITE_TAC[vGSYM vREAL_OF_NUM_EQ;
                vGSYM vREAL_OF_NUM_ADD; vGSYM vREAL_OF_NUM_MUL] ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_SUB_0] ---->
    vREWRITE_TAC[vGSYM vREAL_ENTIRE] ----> vREAL_ARITH_TAC)
  and vREAL_RABINOWITSCH = prove
   ((parse_term "!x y:real. ~(x = y) <=> ?z. (x - y) * z = &1"),
    vREPEAT vGEN_TAC ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vREAL_SUB_0] ---->
    vMESON_TAC[vREAL_MUL_RINV; vREAL_MUL_LZERO; vREAL_ARITH (parse_term "~(&1 = &0)")])
  and init = vGEN_REWRITE_CONV vONCE_DEPTH_CONV [vDECIMAL]
  and real_ty = (parse_type "real") in
  let pure,ideal =
    vRING_AND_IDEAL_CONV
        (rat_of_term,term_of_rat,vREAL_RAT_EQ_CONV,
         (parse_term "(--):real->real"),(parse_term "(+):real->real->real"),(parse_term "(-):real->real->real"),
         (parse_term "(inv):real->real"),(parse_term "(*):real->real->real"),(parse_term "(/):real->real->real"),
         (parse_term "(pow):real->num->real"),
         vREAL_INTEGRAL,vREAL_RABINOWITSCH,vREAL_POLY_CONV) in
  (fun tm -> let th = init tm in vEQ_MP (vSYM th) (pure(rand(concl th)))),
  (fun tms tm -> if forall (fun t -> type_of t = real_ty) (tm::tms)
                 then ideal tms tm
                 else failwith
                   "real_ideal_cofactors: not all terms have type :real");;

(* ------------------------------------------------------------------------- *)
(* Conversion for ideal membership.                                          *)
(* ------------------------------------------------------------------------- *)

let vREAL_IDEAL_CONV =
  let mk_add = mk_binop (parse_term "( + ):real->real->real")
  and mk_mul = mk_binop (parse_term "( * ):real->real->real") in
  fun tms tm ->
    let cfs = real_ideal_cofactors tms tm in
    let tm' = end_itlist mk_add (map2 mk_mul cfs tms) in
    let th = vREAL_POLY_CONV tm and th' = vREAL_POLY_CONV tm' in
    vTRANS th (vSYM th');;

(* ------------------------------------------------------------------------- *)
(* Further specialize GEN_REAL_ARITH and REAL_ARITH (final versions).        *)
(* ------------------------------------------------------------------------- *)

let vGEN_REAL_ARITH vPROVER =
  vGEN_REAL_ARITH
   (term_of_rat,
    vREAL_RAT_EQ_CONV,vREAL_RAT_GE_CONV,vREAL_RAT_GT_CONV,
    vREAL_POLY_CONV,vREAL_POLY_NEG_CONV,vREAL_POLY_ADD_CONV,vREAL_POLY_MUL_CONV,
    vPROVER);;

let vREAL_ARITH =
  let init = vGEN_REWRITE_CONV vONCE_DEPTH_CONV [vDECIMAL]
  and pure = vGEN_REAL_ARITH vREAL_LINEAR_PROVER in
  fun tm -> let th = init tm in vEQ_MP (vSYM th) (pure(rand(concl th)));;

let vREAL_ARITH_TAC = vCONV_TAC vREAL_ARITH;;

let vASM_REAL_ARITH_TAC =
  vREPEAT(vFIRST_X_ASSUM(vMP_TAC -| check (not -| is_forall -| concl))) ---->
  vREAL_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* A few handy equivalential forms of transitivity.                          *)
(* ------------------------------------------------------------------------- *)

let vREAL_LE_TRANS_LE = prove
 ((parse_term "!x y:real. x <= y <=> (!z. y <= z ==> x <= z)"),
  vMESON_TAC[vREAL_LE_TRANS; vREAL_LE_REFL]);;

let vREAL_LE_TRANS_LTE = prove
 ((parse_term "!x y:real. x <= y <=> (!z. y < z ==> x <= z)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++--> [vREAL_ARITH_TAC; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "y + (x - y) / &2")) ----> vREAL_ARITH_TAC);;

let vREAL_LE_TRANS_LT = prove
 ((parse_term "!x y:real. x <= y <=> (!z. y < z ==> x < z)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++--> [vREAL_ARITH_TAC; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "y + (x - y) / &2")) ----> vREAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A simple "field" rule.                                                    *)
(* ------------------------------------------------------------------------- *)

let vREAL_FIELD =
  let norm_net =
    itlist (net_of_thm false -| vSPEC_ALL)
     [vFORALL_SIMP; vEXISTS_SIMP; real_div; vREAL_INV_INV; vREAL_INV_MUL;
      vREAL_POW_ADD]
    (net_of_conv
      (parse_term "inv((x:real) pow n)")
      (vREWR_CONV(vGSYM vREAL_POW_INV) -| check (is_numeral -| rand -| rand))
      empty_net)
  and easy_nz_conv =
    vLAND_CONV
     (vGEN_REWRITE_CONV vTRY_CONV [vMESON[vREAL_POW_EQ_0; vREAL_OF_NUM_EQ]
       (parse_term "~(x pow n = &0) <=>\n        ~((x:real) = &0) \\/ (&n = &0) \\/ ~(x pow n = &0)")]) +--->
    vTRY_CONV(vLAND_CONV vREAL_RAT_REDUCE_CONV +--->
             vGEN_REWRITE_CONV vI [vTAUT (parse_term "(T ==> p) <=> p")]) in
  let prenex_conv =
    vTOP_DEPTH_CONV vBETA_CONV +--->
    vNUM_REDUCE_CONV +--->
    vTOP_DEPTH_CONV(vREWRITES_CONV norm_net) +--->
    vNNFC_CONV +---> vDEPTH_BINOP_CONV (parse_term "(/\\)") vCONDS_CELIM_CONV +--->
    vPRENEX_CONV +--->
    vONCE_REWRITE_CONV[vREAL_ARITH (parse_term "x < y <=> x < y /\\ ~(x = y)")]
  and setup_conv = vNNF_CONV +---> vWEAK_CNF_CONV +---> vCONJ_CANON_CONV
  and core_rule t = try vREAL_RING t with Failure _ -> vREAL_ARITH t
  and is_inv =
    let inv_tm = (parse_term "inv:real->real")
    and is_div = is_binop (parse_term "(/):real->real->real") in
    fun tm -> (is_div tm || (is_comb tm && rator tm = inv_tm)) &&
              not(is_ratconst(rand tm)) in
  let vBASIC_REAL_FIELD tm =
    let is_freeinv t = is_inv t && free_in t tm in
    let itms = setify(map rand (find_terms is_freeinv tm)) in
    let hyps = map
     (fun t -> vCONV_RULE easy_nz_conv (vSPEC t vREAL_MUL_RINV)) itms in
    let tm' = itlist (fun th t -> mk_imp(concl th,t)) hyps tm in
    let th1 = setup_conv tm' in
    let cjs = conjuncts(rand(concl th1)) in
    let ths = map core_rule cjs in
    let th2 = vEQ_MP (vSYM th1) (end_itlist vCONJ ths) in
    rev_itlist (vC vMP) hyps th2 in
  fun tm ->
    let th0 = prenex_conv tm in
    let tm0 = rand(concl th0) in
    let avs,bod = strip_forall tm0 in
    let th1 = setup_conv bod in
    let ths = map vBASIC_REAL_FIELD (conjuncts(rand(concl th1))) in
    vEQ_MP (vSYM th0) (vGENL avs (vEQ_MP (vSYM th1) (end_itlist vCONJ ths)));;

(* ------------------------------------------------------------------------- *)
(* Useful monotone mappings between R and (-1,1)                             *)
(* ------------------------------------------------------------------------- *)

let vREAL_SHRINK_RANGE = prove
 ((parse_term "!x. abs(x / (&1 + abs x)) < &1"),
  vGEN_TAC ---->
  vREWRITE_TAC[vREAL_ABS_DIV; vREAL_ARITH (parse_term "abs(&1 + abs x) = &1 + abs x")] ---->
  vSIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_ARITH (parse_term "&0 < &1 + abs x")] ---->
  vREAL_ARITH_TAC);;

let vREAL_SHRINK_LT = prove
 ((parse_term "!x y. x / (&1 + abs x) < y / (&1 + abs y) <=> x < y"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC(vREAL_ARITH
   (parse_term "(&0 < x' <=> &0 < x) /\\ (&0 < y' <=> &0 < y) /\\\n    (abs x' < abs y' <=> abs x < abs y) /\\ (abs y' < abs x' <=> abs y < abs x)\n    ==> (x' < y' <=> x < y)")) ---->
  vSIMP_TAC[vREAL_LT_RDIV_EQ; vREAL_ARITH (parse_term "&0 < &1 + abs x"); vREAL_MUL_LZERO] ---->
  vMAP_EVERY (fun t -> vSPEC_TAC(t,t)) [(parse_term "y:real"); (parse_term "x:real")] ---->
  vREWRITE_TAC[vMESON[] (parse_term "(!x y. P x y /\\ P y x) <=> (!x y. P x y)")] ---->
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vREAL_ABS_DIV; vREAL_ARITH (parse_term "abs(&1 + abs x) = &1 + abs x")] ---->
  vSIMP_TAC[vREAL_LT_RDIV_EQ; vREAL_ARITH (parse_term "&0 < &1 + abs x")] ---->
  vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "a / b * c:real = (a * c) / b")] ---->
  vSIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_ARITH (parse_term "&0 < &1 + abs x")] ---->
  vREAL_ARITH_TAC);;

let vREAL_SHRINK_LE = prove
 ((parse_term "!x y. x / (&1 + abs x) <= y / (&1 + abs y) <=> x <= y"),
  vREWRITE_TAC[vGSYM vREAL_NOT_LT; vREAL_SHRINK_LT]);;

let vREAL_SHRINK_EQ = prove
 ((parse_term "!x y. x / (&1 + abs x) = y / (&1 + abs y) <=> x = y"),
  vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_SHRINK_LE]);;

let vREAL_SHRINK_GALOIS = prove
 ((parse_term "!x y. x / (&1 + abs x) = y <=> abs y < &1 /\\ y / (&1 - abs y) = x"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vSUBST1_TAC -| vSYM) ---->
  vASM_REWRITE_TAC[vREAL_SHRINK_RANGE] ---->
  vASM_SIMP_TAC[vREAL_ABS_DIV; vREAL_ARITH (parse_term "abs(&1 + abs x) = &1 + abs x");
               vREAL_ARITH (parse_term "abs y < &1 ==> abs(&1 - abs y) = &1 - abs y")] ---->
  vMATCH_MP_TAC(vREAL_ARITH (parse_term "x * inv y * inv z = x * &1 ==> x / y / z = x")) ---->
  vAP_TERM_TAC ---->
  vMATCH_MP_TAC(vREAL_FIELD (parse_term "x * y = &1 ==> inv x * inv y = &1")) ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ----> vCONV_TAC vREAL_FIELD);;

let vREAL_GROW_SHRINK = prove
 ((parse_term "!x. x / (&1 + abs x) / (&1 - abs(x / (&1 + abs x))) = x"),
  vMESON_TAC[vREAL_SHRINK_GALOIS; vREAL_SHRINK_RANGE]);;

let vREAL_SHRINK_GROW_EQ = prove
 ((parse_term "!x. x / (&1 - abs x) / (&1 + abs(x / (&1 - abs x))) = x <=> abs x < &1"),
  vMESON_TAC[vREAL_SHRINK_GALOIS; vREAL_SHRINK_RANGE]);;

let vREAL_SHRINK_GROW = prove
 ((parse_term "!x. abs x < &1\n       ==> x / (&1 - abs x) / (&1 + abs(x / (&1 - abs x))) = x"),
  vREWRITE_TAC[vREAL_SHRINK_GROW_EQ]);;
