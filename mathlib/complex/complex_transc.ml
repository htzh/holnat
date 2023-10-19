[@@@warning "-27-8"]
open Hol.All
open Hol.Accept
open Transc
include Complexnumbers
;;
(* ========================================================================= *)
(* Complex transcendental functions.                                         *)
(* ========================================================================= *)

unparse_as_infix "exp";;
remove_interface "exp";;

(* ------------------------------------------------------------------------- *)
(* Complex square roots.                                                     *)
(* ------------------------------------------------------------------------- *)

let csqrt = new_definition
  [%q {|csqrt(z) = if Im(z) = &0 then
                if &0 <= Re(z) then complex(sqrt(Re(z)),&0)
                else complex(&0,sqrt(--Re(z)))
              else complex(sqrt((norm(z) + Re(z)) / &2),
                           (Im(z) / abs(Im(z))) *
                           sqrt((norm(z) - Re(z)) / &2))|} ];;

let%a vCOMPLEX_NORM_GE_RE_IM = prove
 ([%q {|!z. abs(Re(z)) <= norm(z) /\ abs(Im(z)) <= norm(z)|} ],
  vGEN_TAC ----> vONCE_REWRITE_TAC[vGSYM vPOW_2_SQRT_ABS] ---->
  vREWRITE_TAC[complex_norm] ---->
  vCONJ_TAC ---->
  vMATCH_MP_TAC vSQRT_MONO_LE ---->
  vASM_SIMP_TAC[vREAL_LE_ADDR; vREAL_LE_ADDL; vREAL_POW_2; vREAL_LE_SQUARE]);;

let%a vCSQRT = prove
 ([%q {|!z. csqrt(z) pow 2 = z|} ],
  vGEN_TAC ----> vREWRITE_TAC[vCOMPLEX_POW_2; csqrt] ----> vCOND_CASES_TAC ++-->
   [vCOND_CASES_TAC ---->
    vASM_REWRITE_TAC[vCX_DEF; complex_mul; vRE; vIM; vREAL_MUL_RZERO; vREAL_MUL_LZERO;
      vREAL_SUB_LZERO; vREAL_SUB_RZERO; vREAL_ADD_LID; vCOMPLEX_EQ] ---->
    vREWRITE_TAC[vREAL_NEG_EQ; vGSYM vREAL_POW_2] ---->
    vASM_SIMP_TAC[vSQRT_POW_2; vREAL_ARITH [%q {|~(&0 <= x) ==> &0 <= --x|} ]];
    vALL_TAC] ---->
  vREWRITE_TAC[complex_mul; vRE; vIM] ---->
  vONCE_REWRITE_TAC[vREAL_ARITH
   [%q {|(s * s - (i * s') * (i * s') = s * s - (i * i) * (s' * s')) /\
    (s * i * s' + (i * s')* s = &2 * i * s * s')|} ]] ---->
  vREWRITE_TAC[vGSYM vREAL_POW_2] ---->
  vSUBGOAL_THEN [%q {|&0 <= norm(z) + Re(z) /\ &0 <= norm(z) - Re(z)|} ]
  vSTRIP_ASSUME_TAC ++-->
   [vMP_TAC(vSPEC [%q {|z:complex|} ] vCOMPLEX_NORM_GE_RE_IM) ----> vREAL_ARITH_TAC;
    vALL_TAC] ---->
  vASM_SIMP_TAC[vREAL_LE_DIV; vREAL_POS; vGSYM vSQRT_MUL; vSQRT_POW_2] ---->
  vREWRITE_TAC[vCOMPLEX_EQ; vRE; vIM] ----> vCONJ_TAC ++-->
   [vASM_SIMP_TAC[vREAL_POW_DIV; vREAL_POW2_ABS;
                 vREAL_POW_EQ_0; vREAL_DIV_REFL] ---->
    vREWRITE_TAC[real_div; vREAL_MUL_LID; vGSYM vREAL_SUB_RDISTRIB] ---->
    vREWRITE_TAC[vREAL_ARITH [%q {|(m + r) - (m - r) = r * &2|} ]] ---->
    vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vCONV_TAC vREAL_RAT_REDUCE_CONV ---->
    vREWRITE_TAC[vREAL_MUL_RID]; vALL_TAC] ---->
  vREWRITE_TAC[real_div] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
    [%q {|(a * b) * a' * b = (a * a') * (b * b:real)|} ]] ---->
  vREWRITE_TAC[vREAL_DIFFSQ] ---->
  vREWRITE_TAC[complex_norm; vGSYM vREAL_POW_2] ---->
  vSIMP_TAC[vSQRT_POW_2; vREAL_LE_ADD;
           vREWRITE_RULE[vGSYM vREAL_POW_2] vREAL_LE_SQUARE] ---->
  vREWRITE_TAC[vREAL_ADD_SUB; vGSYM vREAL_POW_MUL] ---->
  vREWRITE_TAC[vPOW_2_SQRT_ABS] ---->
  vREWRITE_TAC[vREAL_ABS_MUL; vREAL_ABS_INV; vREAL_ABS_NUM] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
    [%q {|&2 * (i * a') * a * h = i * (&2 * h) * a * a'|} ]] ---->
  vCONV_TAC vREAL_RAT_REDUCE_CONV ---->
  vREWRITE_TAC[vREAL_MUL_LID; vGSYM real_div] ---->
  vASM_SIMP_TAC[vREAL_DIV_REFL; vREAL_ABS_ZERO; vREAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Complex exponential.                                                      *)
(* ------------------------------------------------------------------------- *)

let cexp = new_definition
 [%q {|cexp z = Cx(exp(Re z)) * complex(cos(Im z),sin(Im z))|} ];;

let%a vCX_CEXP = prove
 ([%q {|!x. Cx(exp x) = cexp(Cx x)|} ],
  vREWRITE_TAC[cexp; vCX_DEF; vRE; vIM; vSIN_0; vCOS_0] ---->
  vREWRITE_TAC[vGSYM vCX_DEF; vGSYM vCX_MUL; vREAL_MUL_RID]);;

let%a vCEXP_0 = prove
 ([%q {|cexp(Cx(&0)) = Cx(&1)|} ],
  vREWRITE_TAC[vGSYM vCX_CEXP; vREAL_EXP_0]);;

let%a vCEXP_ADD = prove
 ([%q {|!w z. cexp(w + z) = cexp(w) * cexp(z)|} ],
  vREWRITE_TAC[vCOMPLEX_EQ; cexp; complex_mul; complex_add; vRE; vIM; vCX_DEF] ---->
  vREWRITE_TAC[vREAL_EXP_ADD; vSIN_ADD; vCOS_ADD] ----> vCONV_TAC vREAL_RING);;

let%a vCEXP_MUL = prove
 ([%q {|!n z. cexp(Cx(&n) * z) = cexp(z) pow n|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[complex_pow] ---->
  vREWRITE_TAC[vCOMPLEX_MUL_LZERO; vCEXP_0] ---->
  vREWRITE_TAC[vGSYM vREAL_OF_NUM_SUC; vCOMPLEX_ADD_RDISTRIB; vCX_ADD] ---->
  vASM_REWRITE_TAC[vCEXP_ADD; vCOMPLEX_MUL_LID] ---->
  vREWRITE_TAC[vCOMPLEX_MUL_AC]);;

let%a vCEXP_NONZERO = prove
 ([%q {|!z. ~(cexp z = Cx(&0))|} ],
  vGEN_TAC ----> vREWRITE_TAC[cexp; vCOMPLEX_ENTIRE; vCX_INJ; vREAL_EXP_NZ] ---->
  vREWRITE_TAC[vCX_DEF; vRE; vIM; vCOMPLEX_EQ] ---->
  vMP_TAC(vSPEC [%q {|Im z|} ] vSIN_CIRCLE) ----> vCONV_TAC vREAL_RING);;

let%a vCEXP_NEG_LMUL = prove
 ([%q {|!z. cexp(--z) * cexp(z) = Cx(&1)|} ],
  vREWRITE_TAC[vGSYM vCEXP_ADD; vCOMPLEX_ADD_LINV; vCEXP_0]);;

let%a vCEXP_NEG_RMUL = prove
 ([%q {|!z. cexp(z) * cexp(--z) = Cx(&1)|} ],
  vREWRITE_TAC[vGSYM vCEXP_ADD; vCOMPLEX_ADD_RINV; vCEXP_0]);;

let%a vCEXP_NEG = prove
 ([%q {|!z. cexp(--z) = inv(cexp z)|} ],
  vMESON_TAC[vCEXP_NEG_LMUL; vCOMPLEX_MUL_LINV_UNIQ]);;

let%a vCEXP_SUB = prove
 ([%q {|!w z. cexp(w - z) = cexp(w) / cexp(z)|} ],
  vREWRITE_TAC[complex_sub; complex_div; vCEXP_NEG; vCEXP_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Complex trig functions.                                                   *)
(* ------------------------------------------------------------------------- *)

let ccos = new_definition
  [%q {|ccos z = (cexp(ii * z) + cexp(--ii * z)) / Cx(&2)|} ];;

let csin = new_definition
  [%q {|csin z = (cexp(ii * z) - cexp(--ii * z)) / (Cx(&2) * ii)|} ];;

let vCX_CSIN,vCX_CCOS = (vCONJ_PAIR -| prove)
 ([%q {|(!x. Cx(sin x) = csin(Cx x)) /\ (!x. Cx(cos x) = ccos(Cx x))|} ],
  vREWRITE_TAC[csin; ccos; cexp; vCX_DEF; ii; vRE; vIM; complex_mul; complex_add;
              vREAL_MUL_RZERO; vREAL_MUL_LZERO; vREAL_SUB_RZERO;
              vREAL_MUL_LID; complex_neg; vREAL_EXP_0; vREAL_ADD_LID;
              vREAL_MUL_LNEG; vREAL_NEG_0; vREAL_ADD_RID; complex_sub;
              vSIN_NEG; vCOS_NEG; vGSYM vREAL_MUL_2; vGSYM real_sub;
              complex_div; vREAL_SUB_REFL; complex_inv; vREAL_SUB_RNEG] ---->
  vCONJ_TAC ----> vGEN_TAC ----> vCONV_TAC vREAL_RAT_REDUCE_CONV ---->
  vREWRITE_TAC[vREAL_MUL_RZERO] ---->
  vAP_TERM_TAC ----> vAP_THM_TAC ----> vAP_TERM_TAC ----> vCONV_TAC vREAL_RING);;

let%a vCSIN_0 = prove
 ([%q {|csin(Cx(&0)) = Cx(&0)|} ],
  vREWRITE_TAC[vGSYM vCX_CSIN; vSIN_0]);;

let%a vCCOS_0 = prove
 ([%q {|ccos(Cx(&0)) = Cx(&1)|} ],
  vREWRITE_TAC[vGSYM vCX_CCOS; vCOS_0]);;

let%a vCSIN_CIRCLE = prove
 ([%q {|!z. csin(z) pow 2 + ccos(z) pow 2 = Cx(&1)|} ],
  vGEN_TAC ----> vREWRITE_TAC[csin; ccos] ---->
  vMP_TAC(vSPEC [%q {|ii * z|} ] vCEXP_NEG_LMUL) ---->
  vMP_TAC vCOMPLEX_POW_II_2 ----> vREWRITE_TAC[vCOMPLEX_MUL_LNEG] ---->
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vCSIN_ADD = prove
 ([%q {|!w z. csin(w + z) = csin(w) * ccos(z) + ccos(w) * csin(z)|} ],
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[csin; ccos; vCOMPLEX_ADD_LDISTRIB; vCEXP_ADD] ---->
  vMP_TAC vCOMPLEX_POW_II_2 ----> vCONV_TAC vCOMPLEX_FIELD);;

let%a vCCOS_ADD = prove
 ([%q {|!w z. ccos(w + z) = ccos(w) * ccos(z) - csin(w) * csin(z)|} ],
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[csin; ccos; vCOMPLEX_ADD_LDISTRIB; vCEXP_ADD] ---->
  vMP_TAC vCOMPLEX_POW_II_2 ----> vCONV_TAC vCOMPLEX_FIELD);;

let%a vCSIN_NEG = prove
 ([%q {|!z. csin(--z) = --(csin(z))|} ],
  vREWRITE_TAC[csin; vCOMPLEX_MUL_LNEG; vCOMPLEX_MUL_RNEG; vCOMPLEX_NEG_NEG] ---->
  vGEN_TAC ----> vMP_TAC vCOMPLEX_POW_II_2 ---->
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vCCOS_NEG = prove
 ([%q {|!z. ccos(--z) = ccos(z)|} ],
  vREWRITE_TAC[ccos; vCOMPLEX_MUL_LNEG; vCOMPLEX_MUL_RNEG; vCOMPLEX_NEG_NEG] ---->
  vGEN_TAC ----> vMP_TAC vCOMPLEX_POW_II_2 ---->
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vCSIN_DOUBLE = prove
 ([%q {|!z. csin(Cx(&2) * z) = Cx(&2) * csin(z) * ccos(z)|} ],
  vREWRITE_TAC[vCOMPLEX_RING [%q {|Cx(&2) * x = x + x|} ]; vCSIN_ADD] ---->
  vCONV_TAC vCOMPLEX_RING);;

let%a vCCOS_DOUBLE = prove
 ([%q {|!z. ccos(Cx(&2) * z) = (ccos(z) pow 2) - (csin(z) pow 2)|} ],
  vREWRITE_TAC[vCOMPLEX_RING [%q {|Cx(&2) * x = x + x|} ]; vCCOS_ADD] ---->
  vCONV_TAC vCOMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* Euler and de Moivre formulas.                                             *)
(* ------------------------------------------------------------------------- *)

let%a vCEXP_EULER = prove
 ([%q {|!z. cexp(ii * z) = ccos(z) + ii * csin(z)|} ],
  vREWRITE_TAC[ccos; csin] ----> vMP_TAC vCOMPLEX_POW_II_2 ---->
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vDEMOIVRE = prove
 ([%q {|!z n. (ccos z + ii * csin z) pow n =
         ccos(Cx(&n) * z) + ii * csin(Cx(&n) * z)|} ],
  vREWRITE_TAC[vGSYM vCEXP_EULER; vGSYM vCEXP_MUL] ---->
  vREWRITE_TAC[vCOMPLEX_MUL_AC]);;

(* ------------------------------------------------------------------------- *)
(* Some lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let%a vEXISTS_COMPLEX = prove
 ([%q {|!P. (?z. P (Re z) (Im z)) <=> ?x y. P x y|} ],
  vMESON_TAC[vRE; vIM; vCOMPLEX]);;

let%a vCOMPLEX_UNIMODULAR_POLAR = prove
 ([%q {|!z. (norm z = &1) ==> ?x. z = complex(cos(x),sin(x))|} ],
  vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vC vAP_THM [%q {|2|} ] -| vAP_TERM [%q {|(pow):real->num->real|} ]) ---->
  vREWRITE_TAC[complex_norm] ---->
  vSIMP_TAC[vREAL_POW_2; vREWRITE_RULE[vREAL_POW_2] vSQRT_POW_2;
           vREAL_LE_SQUARE; vREAL_LE_ADD] ---->
  vREWRITE_TAC[vGSYM vREAL_POW_2; vREAL_MUL_LID] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|t:real|} ] -| vMATCH_MP vCIRCLE_SINCOS) ---->
  vEXISTS_TAC [%q {|t:real|} ] ----> vASM_REWRITE_TAC[vCOMPLEX_EQ; vRE; vIM]);;

let%a vSIN_INTEGER_2PI = prove
 ([%q {|!n. integer n ==> sin((&2 * pi) * n) = &0|} ],
  vREWRITE_TAC[integer; vREAL_ARITH [%q {|abs(x) = &n <=> x = &n \/ x = -- &n|} ]] ---->
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[vREAL_MUL_RNEG; vSIN_NEG] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC; vSIN_DOUBLE] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|pi * &n = &n * pi|} ]; vSIN_NPI] ---->
  vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_MUL_RZERO; vREAL_NEG_0]);;

let%a vCOS_INTEGER_2PI = prove
 ([%q {|!n. integer n ==> cos((&2 * pi) * n) = &1|} ],
  vREWRITE_TAC[integer; vREAL_ARITH [%q {|abs(x) = &n <=> x = &n \/ x = -- &n|} ]] ---->
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[vREAL_MUL_RNEG; vCOS_NEG] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC; vCOS_DOUBLE] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|pi * &n = &n * pi|} ]; vSIN_NPI; vCOS_NPI] ---->
  vREWRITE_TAC[vREAL_POW_POW] ----> vONCE_REWRITE_TAC[vMULT_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_POW_POW; vREAL_POW_2] ---->
  vCONV_TAC vREAL_RAT_REDUCE_CONV ---->
  vREWRITE_TAC[vREAL_POW_ONE; vREAL_SUB_RZERO]);;

let%a vSINCOS_PRINCIPAL_VALUE = prove
 ([%q {|!x. ?y. (--pi < y /\ y <= pi) /\ (sin(y) = sin(x) /\ cos(y) = cos(x))|} ],
  vGEN_TAC ----> vEXISTS_TAC [%q {|pi - (&2 * pi) * frac((pi - x) / (&2 * pi))|} ] ---->
  vCONJ_TAC ++-->
   [vSIMP_TAC[vREAL_ARITH [%q {|--p < p - x <=> x < (&2 * p) * &1|} ];
             vREAL_ARITH [%q {|p - x <= p <=> (&2 * p) * &0 <= x|} ];
             vREAL_LT_LMUL_EQ; vREAL_LE_LMUL_EQ; vREAL_LT_MUL;
             vPI_POS; vREAL_OF_NUM_LT; vARITH; vFLOOR_FRAC];
   vREWRITE_TAC[vFRAC_FLOOR; vREAL_SUB_LDISTRIB] ---->
   vSIMP_TAC[vREAL_DIV_LMUL; vREAL_ENTIRE; vREAL_OF_NUM_EQ; vARITH; vREAL_LT_IMP_NZ;
    vPI_POS; vREAL_ARITH [%q {|a - (a - b - c):real = b + c|} ]; vSIN_ADD; vCOS_ADD] ---->
   vSIMP_TAC[vFLOOR_FRAC; vSIN_INTEGER_2PI; vCOS_INTEGER_2PI] ---->
   vCONV_TAC vREAL_RING]);;

(* ------------------------------------------------------------------------- *)
(* Complex logarithms (the conventional principal value).                    *)
(* ------------------------------------------------------------------------- *)

let clog = new_definition
 [%q {|clog z = @w. cexp(w) = z /\ --pi < Im(w) /\ Im(w) <= pi|} ];;

let%a vCLOG_WORKS = prove
 ([%q {|!z. ~(z = Cx(&0))
       ==> cexp(clog z) = z /\ --pi < Im(clog z) /\ Im(clog z) <= pi|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[clog] ----> vCONV_TAC vSELECT_CONV ---->
  vREWRITE_TAC[cexp; vEXISTS_COMPLEX] ---->
  vEXISTS_TAC [%q {|ln(norm(z:complex))|} ] ---->
  vSUBGOAL_THEN [%q {|exp(ln(norm(z:complex))) = norm(z)|} ] vSUBST1_TAC ++-->
   [vASM_MESON_TAC[vREAL_EXP_LN; vCOMPLEX_NORM_NZ]; vALL_TAC] ---->
  vMP_TAC(vSPEC [%q {|z / Cx(norm z)|} ] vCOMPLEX_UNIMODULAR_POLAR) ----> vANTS_TAC ++-->
   [vASM_SIMP_TAC[vCOMPLEX_NORM_DIV; vCOMPLEX_NORM_CX] ---->
    vASM_SIMP_TAC[vCOMPLEX_ABS_NORM; vREAL_DIV_REFL; vCOMPLEX_NORM_ZERO];
    vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vSINCOS_PRINCIPAL_VALUE) ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|y:real|} ] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vASM_MESON_TAC[vCX_INJ; vCOMPLEX_DIV_LMUL; vCOMPLEX_NORM_ZERO]);;

let%a vCEXP_CLOG = prove
 ([%q {|!z. ~(z = Cx(&0)) ==> cexp(clog z) = z|} ],
  vSIMP_TAC[vCLOG_WORKS]);;

(* ------------------------------------------------------------------------- *)
(* Unwinding number.                                                         *)
(* ------------------------------------------------------------------------- *)

let unwinding = new_definition
 [%q {|unwinding(z) = (z - clog(cexp z)) / (Cx(&2 * pi) * ii)|} ];;

let%a vCOMPLEX_II_NZ = prove
 ([%q {|~(ii = Cx(&0))|} ],
  vMP_TAC vCOMPLEX_POW_II_2 ----> vCONV_TAC vCOMPLEX_RING);;

let%a vUNWINDING_2PI = prove
 ([%q {|Cx(&2 * pi) * ii * unwinding(z) = z - clog(cexp z)|} ],
  vREWRITE_TAC[unwinding; vCOMPLEX_MUL_ASSOC] ---->
  vMATCH_MP_TAC vCOMPLEX_DIV_LMUL ---->
  vREWRITE_TAC[vCOMPLEX_ENTIRE; vCX_INJ; vCOMPLEX_II_NZ] ---->
  vMP_TAC vPI_POS ----> vREAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* An example of how to get nice identities with unwinding number.           *)
(* ------------------------------------------------------------------------- *)

let%a vCLOG_MUL = prove
 ([%q {|!w z. ~(w = Cx(&0)) /\ ~(z = Cx(&0))
           ==> clog(w * z) =
               clog(w) + clog(z) -
               Cx(&2 * pi) * ii * unwinding(clog w + clog z)|} ],
  vREWRITE_TAC[vUNWINDING_2PI;
    vCOMPLEX_RING [%q {|w + z - ((w + z) - c) = c:complex|} ]] ---->
  vASM_SIMP_TAC[vCEXP_ADD; vCEXP_CLOG]);;
