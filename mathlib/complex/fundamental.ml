[@@@warning "-33-27-8"]
open Hol.All
open Hol.Accept
include Cpoly (* need to ensure parsing *)
;;
(* ========================================================================= *)
(* Fundamental theorem of algebra.                                           *)
(* ========================================================================= *)

prioritize_complex();;

(* ------------------------------------------------------------------------- *)
(* A cute trick to reduce magnitude of unimodular number.                    *)
(* ------------------------------------------------------------------------- *)

let%a vSQRT_SOS_LT_1 = prove
 ([%q {|!x y. sqrt(x pow 2 + y pow 2) < &1 <=> x pow 2 + y pow 2 < &1|} ],
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vSQRT_1] ---->
  vREWRITE_TAC[vREAL_POW_2] ---->
  vSIMP_TAC[vSQRT_MONO_LT_EQ; vREAL_POS; vREAL_LE_ADD; vREAL_LE_SQUARE]);;

let%a vSQRT_SOS_EQ_1 = prove
 ([%q {|!x y. (sqrt(x pow 2 + y pow 2) = &1) <=> (x pow 2 + y pow 2 = &1)|} ],
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vSQRT_1] ---->
  vREWRITE_TAC[vREAL_POW_2] ---->
  vSIMP_TAC[vSQRT_INJ; vREAL_POS; vREAL_LE_ADD; vREAL_LE_SQUARE]);;

let%a vUNIMODULAR_REDUCE_NORM = prove
 ([%q {|!z. (norm(z) = &1)
       ==> norm(z + Cx(&1)) < &1 \/
           norm(z - Cx(&1)) < &1 \/
           norm(z + ii) < &1 \/
           norm(z - ii) < &1|} ],
  vGEN_TAC ---->
  vREWRITE_TAC[ii; vCX_DEF; complex_add; complex_sub; complex_neg; complex_norm;
        vRE; vIM; vREAL_ADD_RID; vREAL_NEG_0; vSQRT_SOS_LT_1; vSQRT_SOS_EQ_1] ---->
  vSIMP_TAC[vREAL_POW_2;
           vREAL_ARITH [%q {|a * a + (b + c) * (b + c) =
                       (a * a + b * b) + (&2 * b * c + c * c)|} ];
           vREAL_ARITH [%q {|(b + c) * (b + c) + a * a =
                       (b * b + a * a) + (&2 * b * c + c * c)|} ]] ---->
  vDISCH_TAC ----> vREWRITE_TAC[vREAL_ARITH [%q {|&1 + x < &1 <=> &0 < --x|} ]] ---->
  vREWRITE_TAC[vREAL_NEG_ADD; vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_MUL_RID] ---->
  vMATCH_MP_TAC(vREAL_ARITH
    [%q {|~(abs(a) <= &1 /\ abs(b) <= &1)
     ==> &0 < --a + --(&1) \/ &0 < a + --(&1) \/
         &0 < --b + --(&1) \/ &0 < b + --(&1)|} ]) ---->
  vSTRIP_TAC ----> vUNDISCH_TAC [%q {|Re z * Re z + Im z * Im z = &1|} ] ---->
  vREWRITE_TAC[] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|(&2 * r) * (&2 * r) <= &1 /\ (&2 * i) * (&2 * i) <= &1
    ==> ~(r * r + i * i = &1)|} ]) ---->
  vREWRITE_TAC[vGSYM vREAL_POW_2] ----> vONCE_REWRITE_TAC[vGSYM vREAL_POW2_ABS] ---->
  vASM_SIMP_TAC[vREAL_POW_1_LE; vREAL_ABS_POS]);;

(* ------------------------------------------------------------------------- *)
(* Hence we can always reduce modulus of 1 + b z^n if nonzero                *)
(* ------------------------------------------------------------------------- *)

let%a vREDUCE_POLY_SIMPLE = prove
 ([%q {|!b n. ~(b = Cx(&0)) /\ ~(n = 0)
         ==> ?z. norm(Cx(&1) + b * z pow n) < &1|} ],
  vGEN_TAC ----> vMATCH_MP_TAC num_WF ----> vREPEAT vSTRIP_TAC ---->
  vASM_CASES_TAC [%q {|EVEN(n)|} ] ++-->
   [vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vEVEN_EXISTS]) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:num|} ] vSUBST_ALL_TAC) ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|m:num|} ]) ---->
    vASM_SIMP_TAC[vARITH_RULE [%q {|~(2 * m = 0) ==> m < 2 * m /\ ~(m = 0)|} ]] ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|w:complex|} ]) ----> vEXISTS_TAC [%q {|csqrt w|} ] ---->
    vASM_REWRITE_TAC[vGSYM vCOMPLEX_POW_POW; vCSQRT]; vALL_TAC] ---->
  vMP_TAC(vSPEC [%q {|Cx(norm b) / b|} ] vUNIMODULAR_REDUCE_NORM) ----> vANTS_TAC ++-->
   [vREWRITE_TAC[vCOMPLEX_NORM_DIV; vCOMPLEX_NORM_CX] ---->
    vASM_SIMP_TAC[vCOMPLEX_ABS_NORM; vREAL_DIV_REFL; vCOMPLEX_NORM_ZERO];
    vALL_TAC] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|?v. norm(Cx(norm b) / b + v pow n) < &1|} ] vMP_TAC ++-->
   [vSUBGOAL_THEN [%q {|(Cx(&1) pow n = Cx(&1)) /\
                  (--Cx(&1) pow n = --Cx(&1)) /\
                  (((ii pow n = ii) /\ (--ii pow n = --ii)) \/
                   ((ii pow n = --ii) /\ (--ii pow n = ii)))|} ]
    vMP_TAC ++-->
     [vALL_TAC;
      vRULE_ASSUM_TAC(vREWRITE_RULE[complex_sub]) ----> vASM_MESON_TAC[]] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vNOT_EVEN]) ---->
    vSIMP_TAC[vODD_EXISTS; vLEFT_IMP_EXISTS_THM] ---->
    vX_GEN_TAC [%q {|m:num|} ] ----> vDISCH_THEN(vK vALL_TAC) ---->
    vREWRITE_TAC[complex_pow; vCOMPLEX_POW_NEG; vEVEN; vEVEN_MULT; vARITH_EVEN] ---->
    vREWRITE_TAC[vGSYM vCOMPLEX_POW_POW] ---->
    vREWRITE_TAC[vCOMPLEX_POW_ONE; vCOMPLEX_POW_II_2; vCOMPLEX_MUL_LID;
                vCOMPLEX_POW_NEG] ---->
    vCOND_CASES_TAC ---->
    vREWRITE_TAC[vCOMPLEX_MUL_RID; vCOMPLEX_MUL_RNEG; vCOMPLEX_NEG_NEG];
    vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|v:complex|} ] vASSUME_TAC) ---->
  vEXISTS_TAC [%q {|v / Cx(root(n) (norm b))|} ] ---->
  vREWRITE_TAC[vCOMPLEX_POW_DIV; vGSYM vCX_POW] ---->
  vSUBGOAL_THEN [%q {|root n (norm b) pow n = norm b|} ] vSUBST1_TAC ++-->
   [vUNDISCH_TAC [%q {|~(EVEN n)|} ] ----> vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ---->
    vINDUCT_TAC ----> vSIMP_TAC[vEVEN; vROOT_POW_POS; vCOMPLEX_NORM_POS];
    vALL_TAC] ---->
  vMATCH_MP_TAC vREAL_LT_LCANCEL_IMP ----> vEXISTS_TAC [%q {|norm(Cx(norm b) / b)|} ] ---->
  vREWRITE_TAC[vGSYM vCOMPLEX_NORM_MUL; vCOMPLEX_ADD_LDISTRIB] ---->
  vREWRITE_TAC[vCOMPLEX_MUL_RID; vREAL_MUL_RID] ---->
  vSUBGOAL_THEN [%q {|norm(Cx(norm b) / b) = &1|} ] vSUBST1_TAC ++-->
   [vREWRITE_TAC[vCOMPLEX_NORM_DIV; vCOMPLEX_NORM_CX; vCOMPLEX_ABS_NORM] ---->
    vASM_SIMP_TAC[vREAL_DIV_REFL; vCOMPLEX_NORM_ZERO]; vALL_TAC] ---->
  vREWRITE_TAC[vREAL_LT_01; complex_div] ---->
  vONCE_REWRITE_TAC[vAC vCOMPLEX_MUL_AC
   [%q {|(m * b') * b * p * m' = (m * m') * (b * b') * p|} ]] ---->
  vASM_SIMP_TAC[vCOMPLEX_MUL_RINV; vCOMPLEX_MUL_LID;
               vCX_INJ; vCOMPLEX_NORM_ZERO] ---->
  vASM_REWRITE_TAC[vGSYM complex_div]);;

(* ------------------------------------------------------------------------- *)
(* Basic lemmas about polynomials.                                           *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_CMUL_MAP = prove
 ([%q {|!p c x. poly (MAP (( * ) c) p) x = c * poly p x|} ],
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vMAP; poly; vCOMPLEX_MUL_RZERO] ---->
  vASM_REWRITE_TAC[vCOMPLEX_ADD_LDISTRIB] ----> vREWRITE_TAC[vCOMPLEX_MUL_AC]);;

let%a vPOLY_0 = prove
 ([%q {|!p x. ALL (\b. b = Cx(&0)) p ==> (poly p x = Cx(&0))|} ],
  vLIST_INDUCT_TAC ---->
  vASM_SIMP_TAC[vALL; poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID]);;

let%a vPOLY_BOUND_EXISTS = prove
 ([%q {|!p r. ?m. &0 < m /\ !z. norm(z) <= r ==> norm(poly p z) <= m|} ],
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ----> vGEN_TAC ---->
  vLIST_INDUCT_TAC ++-->
   [vEXISTS_TAC [%q {|&1|} ] ----> vREWRITE_TAC[poly; vCOMPLEX_NORM_CX] ---->
    vREWRITE_TAC[vREAL_ABS_NUM; vREAL_LT_01; vREAL_POS]; vALL_TAC] ---->
  vPOP_ASSUM(vX_CHOOSE_THEN [%q {|m:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|&1 + norm(h) + abs(r * m)|} ] ---->
  vASM_SIMP_TAC[vREAL_ARITH [%q {|&0 <= x /\ &0 <= y ==> &0 < &1 + x + y|} ];
               vREAL_ABS_POS; vCOMPLEX_NORM_POS] ---->
  vX_GEN_TAC [%q {|z:complex|} ] ----> vDISCH_TAC ---->
  vREWRITE_TAC[poly] ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|norm(h) + norm(z * poly t z)|} ] ---->
  vREWRITE_TAC[vCOMPLEX_NORM_TRIANGLE] ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|y <= z ==> x + y <= &1 + x + abs(z)|} ]) ---->
  vREWRITE_TAC[vCOMPLEX_NORM_MUL] ----> vMATCH_MP_TAC vREAL_LE_MUL2 ---->
  vASM_SIMP_TAC[vCOMPLEX_NORM_POS]);;

(* ------------------------------------------------------------------------- *)
(* Offsetting the variable in a polynomial gives another of same degree.     *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_OFFSET_LEMMA = prove
 ([%q {|!a p. ?b q. (LENGTH q = LENGTH p) /\
               !x. poly (CONS b q) x = (a + x) * poly p x|} ],
  vGEN_TAC ----> vLIST_INDUCT_TAC ++-->
   [vEXISTS_TAC [%q {|Cx(&0)|} ] ----> vEXISTS_TAC [%q {|[]:complex list|} ] ---->
    vREWRITE_TAC[poly; vLENGTH; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID];
    vALL_TAC] ---->
  vPOP_ASSUM vSTRIP_ASSUME_TAC ---->
  vEXISTS_TAC [%q {|a * h|} ] ----> vEXISTS_TAC [%q {|CONS (b + h) q|} ] ---->
  vASM_REWRITE_TAC[vLENGTH; poly] ----> vX_GEN_TAC [%q {|x:complex |} ] ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|x:complex|} ]) ---->
  vREWRITE_TAC[poly] ----> vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|( * ) x|} ]) ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_OFFSET = prove
 ([%q {|!a p. ?q. (LENGTH q = LENGTH p) /\ !x. poly q x = poly p (a + x)|} ],
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vREWRITE_TAC[vLENGTH; poly] ++-->
   [vEXISTS_TAC [%q {|[]:complex list|} ] ----> vREWRITE_TAC[poly; vLENGTH]; vALL_TAC] ---->
  vPOP_ASSUM(vX_CHOOSE_THEN [%q {|p:complex list|} ] (vSTRIP_ASSUME_TAC -| vGSYM)) ---->
  vASM_REWRITE_TAC[] ---->
  vMP_TAC(vSPECL [[%q {|a:complex|} ]; [%q {|p:complex list|} ]] vPOLY_OFFSET_LEMMA) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|b:complex|} ] (vX_CHOOSE_THEN [%q {|r: complex list|} ]
        (vSTRIP_ASSUME_TAC -| vGSYM))) ---->
  vEXISTS_TAC [%q {|CONS (h + b) r|} ] ----> vASM_REWRITE_TAC[vLENGTH] ---->
  vREWRITE_TAC[poly] ----> vSIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Bolzano-Weierstrass type property for closed disc in complex plane.       *)
(* ------------------------------------------------------------------------- *)

let%a vMETRIC_BOUND_LEMMA = prove
 ([%q {|!x y. norm(x - y) <= abs(Re(x) - Re(y)) + abs(Im(x) - Im(y))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[complex_norm] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|a <= abs(abs x + abs y) ==> a <= abs x + abs y|} ]) ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vPOW_2_SQRT_ABS] ---->
  vMATCH_MP_TAC vSQRT_MONO_LE ---->
  vSIMP_TAC[vREAL_POW_2; vREAL_LE_ADD; vREAL_LE_SQUARE] ---->
  vREWRITE_TAC[complex_add; complex_sub; complex_neg; vRE; vIM] ---->
  vREWRITE_TAC[vGSYM real_sub] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|(a + b) * (a + b) = a * a + b * b + &2 * a * b|} ]] ---->
  vREWRITE_TAC[vGSYM vREAL_ABS_MUL] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|a + b <= abs a + abs b + &2 * abs c|} ]]);;

let%a vBOLZANO_WEIERSTRASS_COMPLEX_DISC = prove
 ([%q {|!s r. (!n. norm(s n) <= r)
         ==> ?f z. subseq f /\
                   !e. &0 < e ==> ?N. !n. n >= N ==> norm(s(f n) - z) < e|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|Re o (s:num->complex)|} ] vSEQ_MONOSUB) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|f:num->num|} ] vMP_TAC) ---->
  vREWRITE_TAC[o_THM] ----> vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|Im o (s:num->complex) o (f:num->num)|} ] vSEQ_MONOSUB) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g:num->num|} ] vMP_TAC) ---->
  vREWRITE_TAC[o_THM] ----> vSTRIP_TAC ---->
  vEXISTS_TAC [%q {|(f:num->num) o (g:num->num)|} ] ---->
  vSUBGOAL_THEN [%q {|convergent (\n. Re(s(f n :num))) /\
                convergent (\n. Im(s((f:num->num)(g n))))|} ]
  vMP_TAC ++-->
   [vCONJ_TAC ----> vMATCH_MP_TAC vSEQ_BCONV ----> vASM_REWRITE_TAC[bounded] ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|r + &1|} ]; [%q {|&0|} ]; [%q {|0|} ]] ---->
    vREWRITE_TAC[vGE; vLE_0; vMR1_DEF; vREAL_SUB_LZERO; vREAL_ABS_NEG] ---->
    vX_GEN_TAC [%q {|n:num|} ] ---->
    vW(fun (_,w) -> vFIRST_ASSUM(vMP_TAC -| vSPEC (funpow 3 rand (lhand w)))) ---->
    vREWRITE_TAC[complex_norm] ---->
    vMATCH_MP_TAC(vREAL_ARITH [%q {|a <= b ==> b <= r ==> a < r + &1|} ]) ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vPOW_2_SQRT_ABS] ---->
    vMATCH_MP_TAC vSQRT_MONO_LE ---->
    vREWRITE_TAC[vREAL_POW_2; vREAL_LE_SQUARE; vREAL_LE_ADDR; vREAL_LE_ADDL];
    vALL_TAC] ---->
  vREWRITE_TAC[convergent; vSEQ; vGE] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2
    (vX_CHOOSE_TAC [%q {|x:real|} ]) (vX_CHOOSE_TAC [%q {|y:real|} ])) ---->
  vEXISTS_TAC [%q {|complex(x,y)|} ] ----> vCONJ_TAC ++-->
   [vMAP_EVERY vUNDISCH_TAC [[%q {|subseq f|} ]; [%q {|subseq g|} ]] ---->
    vREWRITE_TAC[subseq; o_THM] ----> vMESON_TAC[]; vALL_TAC] ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vUNDISCH_TAC
   [%q {|!e. &0 < e
        ==> (?N. !n. N <= n ==> abs(Re(s ((f:num->num) n)) - x) < e)|} ] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|N2:num|} ]) ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|N1:num|} ]) ---->
  vEXISTS_TAC [%q {|N1 + N2:num|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|&2 * e / &2|} ] ---->
  vCONJ_TAC ++-->
   [vALL_TAC;
    vSIMP_TAC[vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH; vREAL_LE_REFL]] ---->
  vW(vMP_TAC -| vPART_MATCH lhand vMETRIC_BOUND_LEMMA -| lhand -| snd) ---->
  vMATCH_MP_TAC(vREAL_ARITH
    [%q {|a < c /\ b < c ==> x <= a + b ==> x < &2 * c|} ]) ---->
  vREWRITE_TAC[o_THM; vRE; vIM] ----> vCONJ_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vASM_MESON_TAC[vLE_ADD; vSEQ_SUBLE; vLE_TRANS; vADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Polynomial is continuous.                                                 *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_CONT = prove
 ([%q {|!p z e. &0 < e
           ==> ?d. &0 < d /\ !w. &0 < norm(w - z) /\ norm(w - z) < d
                   ==> norm(poly p w - poly p z) < e|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|z:complex|} ]; [%q {|p:complex list|} ]] vPOLY_OFFSET) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|q:complex list|} ] (vMP_TAC -| vCONJUNCT2)) ---->
  vDISCH_THEN(vMP_TAC -| vGEN [%q {|w:complex|} ] -| vSYM -| vSPEC [%q {|w - z|} ]) ---->
  vREWRITE_TAC[vCOMPLEX_SUB_ADD2] ---->
  vDISCH_THEN(fun th -> vONCE_REWRITE_TAC[th]) ---->
  vREWRITE_TAC[vCOMPLEX_SUB_REFL] ---->
  vSPEC_TAC([%q {|q:complex list|} ],[%q {|p:complex list|} ]) ---->
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[poly] ++-->
   [vEXISTS_TAC [%q {|e:real|} ] ---->
    vASM_REWRITE_TAC[vCOMPLEX_SUB_REFL; vCOMPLEX_NORM_CX; vREAL_ABS_NUM];
    vALL_TAC] ---->
  vREWRITE_TAC[vCOMPLEX_MUL_LZERO; vCOMPLEX_ADD_RID; vCOMPLEX_ADD_SUB] ---->
  vMP_TAC(vSPECL [[%q {|t:complex list|} ]; [%q {|&1|} ]] vPOLY_BOUND_EXISTS) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|&1|} ]; [%q {|e / m:real|} ]] vREAL_DOWN2) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_LT_01] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|d:real|} ] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|w:complex|} ] ---->
  vSTRIP_TAC ----> vREWRITE_TAC[vCOMPLEX_NORM_MUL] ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|d * m:real|} ] ---->
  vASM_SIMP_TAC[vGSYM vREAL_LT_RDIV_EQ] ----> vMATCH_MP_TAC vREAL_LE_MUL2 ---->
  vASM_MESON_TAC[vREAL_LT_TRANS; vREAL_LT_IMP_LE; vCOMPLEX_NORM_POS]);;

(* ------------------------------------------------------------------------- *)
(* Hence a polynomial attains minimum on a closed disc in the complex plane. *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_MINIMUM_MODULUS_DISC = prove
 ([%q {|!p r. ?z. !w. norm(w) <= r ==> norm(poly p z) <= norm(poly p w)|} ],
  let lemma = prove
   ([%q {|P /\ (m = --x) /\ --x < y <=> (--x = m) /\ P /\ m < y|} ],
    vMESON_TAC[]) in
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC [%q {|&0 <= r|} ] ++-->
   [vALL_TAC; vASM_MESON_TAC[vCOMPLEX_NORM_POS; vREAL_LE_TRANS]] ---->
  vMP_TAC(vSPEC [%q {|\x. ?z. norm(z) <= r /\ (norm(poly p z) = --x)|} ]
    vREAL_SUP_EXISTS) ---->
  vREWRITE_TAC[] ----> vANTS_TAC ++-->
   [vCONJ_TAC ++-->
     [vMAP_EVERY vEXISTS_TAC [[%q {|--norm(poly p (Cx(&0)))|} ]; [%q {|Cx(&0)|} ]] ---->
      vASM_REWRITE_TAC[vREAL_NEG_NEG; vCOMPLEX_NORM_CX; vREAL_ABS_NUM];
      vEXISTS_TAC [%q {|&1|} ] ---->
      vREWRITE_TAC[vREAL_ARITH [%q {|(a = --b) <=> (--b = a:real)|} ]] ---->
      vREWRITE_TAC[vREAL_ARITH [%q {|x < &1 <=>  --(&1) < --x|} ]] ---->
      vSIMP_TAC[vLEFT_IMP_EXISTS_THM] ---->
      vSIMP_TAC[vREAL_ARITH [%q {|&0 <= x ==> --(&1) < x|} ]; vCOMPLEX_NORM_POS]];
    vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:real|} ] vMP_TAC) ---->
  vONCE_REWRITE_TAC[vREAL_ARITH [%q {|a < b <=> --b < --a:real|} ]] ---->
  vABBREV_TAC [%q {|m = --s:real|} ] ---->
  vDISCH_THEN(vMP_TAC -| vGEN [%q {|y:real|} ] -| vSPEC [%q {|--y:real|} ]) ---->
  vREWRITE_TAC[vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vLEFT_AND_EXISTS_THM; vGSYM vCONJ_ASSOC; lemma] ---->
  vONCE_REWRITE_TAC[vSWAP_EXISTS_THM] ---->
  vONCE_REWRITE_TAC[vREAL_ARITH [%q {|(--a = b) <=> (a = --b:real)|} ]] ---->
  vREWRITE_TAC[vLEFT_EXISTS_AND_THM; vEXISTS_REFL] ---->
  vDISCH_THEN(fun th -> vMP_TAC th ----> vMP_TAC(vSPEC [%q {|m:real|} ] th)) ---->
  vREWRITE_TAC[vREAL_LT_REFL; vNOT_EXISTS_THM] ---->
  vREWRITE_TAC[vTAUT [%q {|~(a /\ b) <=> a ==> ~b|} ]] ---->
  vREWRITE_TAC[vREAL_NOT_LT] ----> vDISCH_TAC ---->
  vDISCH_THEN(vMP_TAC -| vGEN [%q {|n:num|} ] -| vSPEC [%q {|m + inv(&(SUC n))|} ]) ---->
  vREWRITE_TAC[vREAL_LT_ADDR; vREAL_LT_INV_EQ; vREAL_OF_NUM_LT; vLT_0] ---->
  vREWRITE_TAC[vSKOLEM_THM; vFORALL_AND_THM] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:num->complex|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|s:num->complex|} ]; [%q {|r:real|} ]]
    vBOLZANO_WEIERSTRASS_COMPLEX_DISC) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|f:num->num|} ] (vX_CHOOSE_THEN [%q {|z:complex|} ]
    vSTRIP_ASSUME_TAC)) ---->
  vEXISTS_TAC [%q {|z:complex|} ] ----> vX_GEN_TAC [%q {|w:complex|} ] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|norm(poly p z) = m|} ] (fun th -> vASM_SIMP_TAC[th]) ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|~(&0 < abs(a - b)) ==> (a = b)|} ]) ----> vDISCH_TAC ---->
  vABBREV_TAC [%q {|e = abs(norm(poly p z) - m)|} ] ---->
  vMP_TAC(vSPECL [[%q {|p:complex list|} ]; [%q {|z:complex|} ]; [%q {|e / &2|} ]] vPOLY_CONT) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|!w. norm(w - z) < d ==> norm(poly p w - poly p z) < e / &2|} ]
  vMP_TAC ++-->
   [vX_GEN_TAC [%q {|u:complex|} ] ---->
    vASM_CASES_TAC [%q {|u = z:complex|} ] ---->
    vASM_SIMP_TAC[vCOMPLEX_SUB_REFL; vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH;
                 vCOMPLEX_NORM_CX; vREAL_ABS_NUM] ---->
    vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
    vASM_REWRITE_TAC[vCOMPLEX_NORM_NZ; vCOMPLEX_SUB_0]; vALL_TAC] ---->
  vFIRST_ASSUM(vK vALL_TAC -| check (is_conj -| lhand -|
    snd -| dest_forall -| concl)) ---->
  vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|d:real|} ]) ----> vASM_REWRITE_TAC[vGE] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N1:num|} ] vASSUME_TAC) ---->
  vMP_TAC(vSPEC [%q {|&2 / e|} ] vREAL_ARCH_SIMPLE) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N2:num|} ] vASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|norm(poly p (s((f:num->num) (N1 + N2))) - poly p z) < e / &2|} ]
  vMP_TAC ++-->
   [vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_SIMP_TAC[vLE_ADD]; vALL_TAC] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|!m. abs(norm(psfn) - m) < e2 /\
        &2 * e2 <= abs(norm(psfn) - m) + norm(psfn - pz)
        ==> norm(psfn - pz) < e2 ==> F|} ]) ---->
  vEXISTS_TAC [%q {|m:real|} ] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|inv(&(SUC(N1 + N2)))|} ] ---->
    vCONJ_TAC ++-->
     [vMATCH_MP_TAC(vREAL_ARITH
       [%q {|m <= x /\ x < m + e ==> abs(x - m:real) < e|} ]) ---->
      vASM_SIMP_TAC[] ---->
      vMATCH_MP_TAC vREAL_LTE_TRANS ---->
      vEXISTS_TAC [%q {|m + inv(&(SUC(f(N1 + N2:num))))|} ] ---->
      vASM_REWRITE_TAC[vREAL_LE_LADD] ----> vMATCH_MP_TAC vREAL_LE_INV2 ---->
      vASM_SIMP_TAC[vREAL_OF_NUM_LT; vREAL_OF_NUM_LE; vLT_0; vLE_SUC; vSEQ_SUBLE];
      vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_INV_DIV] ---->
      vMATCH_MP_TAC vREAL_LE_INV2 ---->
      vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|&N2|} ] ---->
      vASM_REWRITE_TAC[vREAL_OF_NUM_LE] ----> vARITH_TAC]; vALL_TAC] ---->
  vSIMP_TAC[vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH] ---->
  vEXPAND_TAC "e" ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|abs(norm(psfn) - norm(pz)) <= norm(psfn - pz)
    ==> abs(norm(pz) - m) <= abs(norm(psfn) - m) + norm(psfn - pz)|} ]) ---->
  vREWRITE_TAC[vCOMPLEX_NORM_ABS_NORM]);;

(* ------------------------------------------------------------------------- *)
(* Nonzero polynomial in z goes to infinity as z does.                       *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_INFINITY = prove
 ([%q {|!p a. EX (\b. ~(b = Cx(&0))) p
         ==> !d. ?r. !z. r <= norm(z) ==> d <= norm(poly (CONS a p) z)|} ],
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vEX] ----> vX_GEN_TAC [%q {|a:complex|} ] ---->
  vASM_CASES_TAC [%q {|EX (\b. ~(b = Cx(&0))) t|} ] ----> vASM_REWRITE_TAC[] ++-->
   [vX_GEN_TAC [%q {|d:real|} ] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|h:complex|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|r:real|} ] -| vSPEC [%q {|d + norm(a)|} ]) ---->
    vEXISTS_TAC [%q {|&1 + abs(r)|} ] ----> vX_GEN_TAC [%q {|z:complex|} ] ----> vDISCH_TAC ---->
    vONCE_REWRITE_TAC[poly] ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ---->
    vEXISTS_TAC [%q {|norm(z * poly (CONS h t) z) - norm(a)|} ] ----> vCONJ_TAC ++-->
     [vALL_TAC;
      vONCE_REWRITE_TAC[vCOMPLEX_ADD_SYM] ---->
      vREWRITE_TAC[vREAL_LE_SUB_RADD; vCOMPLEX_NORM_TRIANGLE_SUB]] ---->
    vREWRITE_TAC[vREAL_LE_SUB_LADD] ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ---->
    vEXISTS_TAC [%q {|&1 * norm(poly (CONS h t) z)|} ] ----> vCONJ_TAC ++-->
     [vREWRITE_TAC[vREAL_MUL_LID] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vASM_SIMP_TAC[vREAL_ARITH [%q {|&1 + abs(r) <= x ==> r <= x|} ]];
      vREWRITE_TAC[vCOMPLEX_NORM_MUL] ----> vMATCH_MP_TAC vREAL_LE_RMUL ---->
      vREWRITE_TAC[vCOMPLEX_NORM_POS] ---->
      vASM_MESON_TAC[vREAL_ARITH [%q {|&1 + abs(r) <= x ==> &1 <= x|} ]]];
    vRULE_ASSUM_TAC(vREWRITE_RULE[vNOT_EX]) ---->
    vASM_SIMP_TAC[poly; vPOLY_0; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
    vDISCH_TAC ----> vX_GEN_TAC [%q {|d:real|} ] ---->
    vEXISTS_TAC [%q {|(abs(d) + norm(a)) / norm(h)|} ] ----> vX_GEN_TAC [%q {|z:complex|} ] ---->
    vASM_SIMP_TAC[vREAL_LE_LDIV_EQ; vCOMPLEX_NORM_NZ; vGSYM vCOMPLEX_NORM_MUL] ---->
    vMATCH_MP_TAC(vREAL_ARITH
     [%q {|mzh <= mazh + ma ==> abs(d) + ma <= mzh ==> d <= mazh|} ]) ---->
    vONCE_REWRITE_TAC[vCOMPLEX_ADD_SYM] ---->
    vREWRITE_TAC[vCOMPLEX_NORM_TRIANGLE_SUB]]);;

(* ------------------------------------------------------------------------- *)
(* Hence polynomial's modulus attains its minimum somewhere.                 *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_MINIMUM_MODULUS = prove
 ([%q {|!p. ?z. !w. norm(poly p z) <= norm(poly p w)|} ],
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[poly; vREAL_LE_REFL] ---->
  vASM_CASES_TAC [%q {|EX (\b. ~(b = Cx(&0))) t|} ] ++-->
   [vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|h:complex|} ] -| vMATCH_MP vPOLY_INFINITY) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|norm(poly (CONS h t) (Cx(&0)))|} ]) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|r:real|} ] vASSUME_TAC) ---->
    vMP_TAC(vSPECL [[%q {|CONS (h:complex) t|} ]; [%q {|abs(r)|} ]]
       vPOLY_MINIMUM_MODULUS_DISC) ---->
    vREWRITE_TAC[vGSYM(vCONJUNCT2 poly)] ---->
    vASM_MESON_TAC[vREAL_ARITH [%q {|r <= z \/ z <= abs(r)|} ]; vREAL_LE_TRANS;
                  vCOMPLEX_NORM_CX; vREAL_ABS_NUM; vREAL_ABS_POS];
    vFIRST_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vNOT_EX]) ---->
    vREWRITE_TAC[] ----> vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vPOLY_0) ---->
    vASM_REWRITE_TAC[vCOMPLEX_MUL_RZERO; vREAL_LE_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Constant function (non-syntactic characterization).                       *)
(* ------------------------------------------------------------------------- *)

let constant = new_definition
  [%q {|constant f = !w z. f(w) = f(z)|} ];;

let%a vNONCONSTANT_LENGTH = prove
 ([%q {|!p. ~constant(poly p) ==> 2 <= LENGTH p|} ],
  vREWRITE_TAC[constant] ---->
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[poly] ---->
  vREWRITE_TAC[vLENGTH; vARITH_RULE [%q {|2 <= SUC n <=> ~(n = 0)|} ]] ---->
  vSIMP_TAC[vTAUT [%q {|~a ==> ~b <=> b ==> a|} ]; vLENGTH_EQ_NIL; poly] ---->
  vREWRITE_TAC[vCOMPLEX_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* Decomposition of polynomial, skipping zero coefficients after the first.  *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_DECOMPOSE_LEMMA = prove
 ([%q {|!p. ~(!z. ~(z = Cx(&0)) ==> (poly p z = Cx(&0)))
       ==> ?k a q. ~(a = Cx(&0)) /\
                   (SUC(LENGTH q + k) = LENGTH p) /\
                   !z. poly p z = z pow k * poly (CONS a q) z|} ],
  vLIST_INDUCT_TAC ++--> [vREWRITE_TAC[poly]; vALL_TAC] ---->
  vASM_CASES_TAC [%q {|h = Cx(&0)|} ] ++-->
   [vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [poly] ---->
    vASM_SIMP_TAC[vCOMPLEX_ADD_LID; vCOMPLEX_ENTIRE] ---->
    vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:num|} ] (vX_CHOOSE_THEN [%q {|a:complex|} ]
     (vX_CHOOSE_THEN [%q {|q:complex list|} ] vSTRIP_ASSUME_TAC))) ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|k + 1|} ]; [%q {|a:complex|} ]; [%q {|q:complex list|} ]] ---->
    vASM_REWRITE_TAC[poly; vLENGTH; vGSYM vADD1; vADD_CLAUSES] ---->
    vREWRITE_TAC[vCOMPLEX_ADD_LID; complex_pow; vGSYM vCOMPLEX_MUL_ASSOC];
    vDISCH_THEN(vK vALL_TAC) ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|0|} ]; [%q {|h:complex|} ]; [%q {|t:complex list|} ]] ---->
    vASM_REWRITE_TAC[complex_pow; vCOMPLEX_MUL_LID; vADD_CLAUSES; vLENGTH]]);;

let%a vPOLY_DECOMPOSE = prove
 ([%q {|!p. ~constant(poly p)
       ==> ?k a q. ~(a = Cx(&0)) /\ ~(k = 0) /\
                   (LENGTH q + k + 1 = LENGTH p) /\
                   !z. poly p z = poly p (Cx(&0)) +
                                  z pow k * poly (CONS a q) z|} ],
  vLIST_INDUCT_TAC ++--> [vREWRITE_TAC[constant; poly]; vALL_TAC] ---->
  vPOP_ASSUM(vK vALL_TAC) ----> vDISCH_TAC ---->
  vMP_TAC(vSPEC [%q {|t:complex list|} ] vPOLY_DECOMPOSE_LEMMA) ----> vANTS_TAC ++-->
   [vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[constant; poly] ---->
    vREWRITE_TAC[vTAUT [%q {|~b ==> ~a <=> a ==> b|} ]; vCOMPLEX_EQ_ADD_LCANCEL] ---->
    vSIMP_TAC[vTAUT [%q {|~a ==> b <=> a \/ b|} ]; vGSYM vCOMPLEX_ENTIRE]; vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:num|} ] (vX_CHOOSE_THEN [%q {|a:complex|} ]
     (vX_CHOOSE_THEN [%q {|q:complex list|} ] vSTRIP_ASSUME_TAC))) ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|SUC k|} ]; [%q {|a:complex|} ]; [%q {|q:complex list|} ]] ---->
  vASM_REWRITE_TAC[vADD_CLAUSES; vGSYM vADD1; vLENGTH; vNOT_SUC] ---->
  vASM_REWRITE_TAC[poly; vCOMPLEX_MUL_LZERO; vCOMPLEX_ADD_RID; complex_pow] ---->
  vREWRITE_TAC[vGSYM vCOMPLEX_MUL_ASSOC]);;

let%a vPOLY_REPLICATE_APPEND = prove
 ([%q {|!n p x. poly (APPEND (REPLICATE n (Cx(&0))) p) x = x pow n * poly p x|} ],
  vINDUCT_TAC ---->
  vREWRITE_TAC[vREPLICATE; vAPPEND; complex_pow; vCOMPLEX_MUL_LID] ---->
  vASM_REWRITE_TAC[poly; vCOMPLEX_ADD_LID] ----> vREWRITE_TAC[vCOMPLEX_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Fundamental theorem.                                                      *)
(* ------------------------------------------------------------------------- *)

let%a vFUNDAMENTAL_THEOREM_OF_ALGEBRA = prove
 ([%q {|!p. ~constant(poly p) ==> ?z. poly p z = Cx(&0)|} ],
  vSUBGOAL_THEN
   [%q {|!n p. (LENGTH p = n) /\ ~constant(poly p) ==> ?z. poly p z = Cx(&0)|} ]
   (fun th -> vMESON_TAC[th]) ---->
  vMATCH_MP_TAC num_WF ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vSTRIP_TAC ---->
  vX_GEN_TAC [%q {|p:complex list|} ] ----> vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vNONCONSTANT_LENGTH) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vX_CHOOSE_TAC [%q {|c:complex|} ] (vSPEC [%q {|p:complex list|} ] vPOLY_MINIMUM_MODULUS) ---->
  vASM_CASES_TAC [%q {|poly p c = Cx(&0)|} ] ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
  vMP_TAC(vSPECL [[%q {|c:complex|} ]; [%q {|p:complex list|} ]] vPOLY_OFFSET) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|q:complex list|} ] vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vSUBST_ALL_TAC -| vSYM) vASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|~constant(poly q)|} ] vASSUME_TAC ++-->
   [vUNDISCH_TAC [%q {|~(constant(poly p))|} ] ---->
    vSUBGOAL_THEN [%q {|!z. poly q (z - c) = poly p z|} ]
      (fun th -> vMESON_TAC[th; constant]) ---->
    vASM_MESON_TAC[vSIMPLE_COMPLEX_ARITH [%q {|a + (x - a) = x|} ]]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|poly p c = poly q (Cx(&0))|} ] vSUBST_ALL_TAC ++-->
   [vASM_MESON_TAC[vCOMPLEX_ADD_RID]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!w. norm(poly q (Cx(&0))) <= norm(poly q w)|} ] vMP_TAC ++-->
   [vASM_MESON_TAC[]; vALL_TAC] ---->
  vPOP_ASSUM_LIST(vMAP_EVERY (fun th ->
    if free_in [%q {|p:complex list|} ] (concl th)
    then vALL_TAC else vASSUME_TAC th)) ---->
  vMATCH_MP_TAC(vTAUT [%q {|~a ==> a ==> b|} ]) ---->
  vREWRITE_TAC[vNOT_FORALL_THM; vREAL_NOT_LE] ---->
  vABBREV_TAC [%q {|a0 = poly q (Cx(&0))|} ] ---->
  vSUBGOAL_THEN
   [%q {|!z. poly q z = poly (MAP (( * ) (inv(a0))) q) z * a0|} ]
  vASSUME_TAC ++-->
   [vREWRITE_TAC[vPOLY_CMUL_MAP] ---->
    vONCE_REWRITE_TAC[vAC vCOMPLEX_MUL_AC [%q {|(a * b) * c = b * c * a|} ]] ---->
    vASM_SIMP_TAC[vCOMPLEX_MUL_RINV; vCOMPLEX_MUL_RID];
    vALL_TAC] ---->
  vABBREV_TAC [%q {|r = MAP (( * ) (inv(a0))) q|} ] ---->
  vSUBGOAL_THEN [%q {|LENGTH(q:complex list) = LENGTH(r:complex list)|} ]
  vSUBST_ALL_TAC ++-->
   [vEXPAND_TAC "r" ----> vREWRITE_TAC[vLENGTH_MAP]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|~(constant(poly r))|} ] vASSUME_TAC ++-->
   [vUNDISCH_TAC [%q {|~constant(poly q)|} ] ---->
    vASM_REWRITE_TAC[constant; vCOMPLEX_EQ_MUL_RCANCEL] ----> vMESON_TAC[];
    vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|poly r (Cx(&0)) = Cx(&1)|} ] vASSUME_TAC ++-->
   [vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|Cx(&0)|} ]) ---->
    vASM_REWRITE_TAC[] ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV) [vGSYM vCOMPLEX_MUL_LID] ---->
    vASM_SIMP_TAC[vCOMPLEX_EQ_MUL_RCANCEL]; vALL_TAC] ---->
  vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM_LIST(vMAP_EVERY (fun th ->
    if free_in [%q {|q:complex list|} ] (concl th)
    then vALL_TAC else vASSUME_TAC th)) ---->
  vASM_SIMP_TAC[vGSYM vREAL_LT_RDIV_EQ; vCOMPLEX_NORM_NZ; vCOMPLEX_NORM_MUL;
               vREAL_DIV_REFL; vCOMPLEX_NORM_ZERO] ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vPOLY_DECOMPOSE) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:num|} ] (vX_CHOOSE_THEN [%q {|a:complex|} ]
        (vX_CHOOSE_THEN [%q {|s:complex list|} ] vMP_TAC))) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vSUBST_ALL_TAC -| vSYM) vMP_TAC) ---->
  vDISCH_THEN(fun th -> vONCE_REWRITE_TAC[th]) ----> vASM_REWRITE_TAC[] ---->
  vASM_CASES_TAC [%q {|k + 1 = n|} ] ++-->
   [vUNDISCH_TAC [%q {|LENGTH(s:complex list) + k + 1 = n|} ] ---->
    vASM_REWRITE_TAC[vARITH_RULE [%q {|(s + m = m) <=> (s = 0)|} ]; vLENGTH_EQ_NIL] ---->
    vREWRITE_TAC[vLENGTH_EQ_NIL] ----> vDISCH_THEN vSUBST1_TAC ---->
    vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
    vONCE_REWRITE_TAC[vCOMPLEX_MUL_SYM] ---->
    vMATCH_MP_TAC vREDUCE_POLY_SIMPLE ----> vASM_REWRITE_TAC[] ---->
    vMAP_EVERY vUNDISCH_TAC [[%q {|k + 1 = n|} ]; [%q {|2 <= n|} ]] ----> vARITH_TAC; vALL_TAC] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|k + 1|} ]) ----> vANTS_TAC ++-->
   [vUNDISCH_TAC [%q {|~(k + 1 = n)|} ] ---->
    vUNDISCH_TAC [%q {|LENGTH(s:complex list) + k + 1 = n|} ] ----> vARITH_TAC;
    vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC
   [%q {|CONS (Cx(&1)) (APPEND (REPLICATE (k - 1) (Cx(&0))) [a])|} ]) ---->
  vANTS_TAC ++-->
   [vCONJ_TAC ++-->
     [vREWRITE_TAC[vLENGTH; vLENGTH_APPEND; vLENGTH_REPLICATE] ---->
      vUNDISCH_TAC [%q {|~(k = 0)|} ] ----> vARITH_TAC; vALL_TAC] ---->
    vREWRITE_TAC[constant; vPOLY_REPLICATE_APPEND; poly] ---->
    vREWRITE_TAC[vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|Cx(&0)|} ]; [%q {|Cx(&1)|} ]]) ---->
    vREWRITE_TAC[vCOMPLEX_MUL_LID; vCOMPLEX_MUL_LZERO; vCOMPLEX_ADD_RID] ---->
    vASM_REWRITE_TAC[vCOMPLEX_ENTIRE; vCOMPLEX_POW_ONE; vSIMPLE_COMPLEX_ARITH
                  [%q {|(a = a + b) <=> (b = Cx(&0))|} ]] ---->
    vREWRITE_TAC[vCX_INJ; vREAL_OF_NUM_EQ; vARITH_EQ]; vALL_TAC] ---->
  vREWRITE_TAC[constant; vPOLY_REPLICATE_APPEND; poly] ---->
  vREWRITE_TAC[vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
  vONCE_REWRITE_TAC[vAC vCOMPLEX_MUL_AC [%q {|a * b * c = (a * b) * c|} ]] ---->
  vREWRITE_TAC[vGSYM(vCONJUNCT2 complex_pow)] ---->
  vASM_SIMP_TAC[vARITH_RULE [%q {|~(k = 0) ==> (SUC(k - 1) = k)|} ]] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|w:complex|} ]) ---->
  vMP_TAC(vSPECL [[%q {|s:complex list|} ]; [%q {|norm(w)|} ]] vPOLY_BOUND_EXISTS) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:real|} ] vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|~(w = Cx(&0))|} ] vASSUME_TAC ++-->
   [vUNDISCH_TAC [%q {|Cx(&1) + w pow k * a = Cx(&0)|} ] ---->
    vONCE_REWRITE_TAC[vTAUT [%q {|a ==> ~b <=> b ==> ~a|} ]] ---->
    vDISCH_THEN vSUBST1_TAC ---->
    vUNDISCH_TAC [%q {|~(k = 0)|} ] ----> vSPEC_TAC([%q {|k:num|} ],[%q {|k:num|} ]) ---->
    vINDUCT_TAC ----> vREWRITE_TAC[complex_pow; vCOMPLEX_MUL_LZERO] ---->
    vREWRITE_TAC[vCOMPLEX_ADD_RID; vCX_INJ; vREAL_OF_NUM_EQ; vARITH_EQ];
    vALL_TAC] ---->
  vMP_TAC(vSPECL [[%q {|&1|} ]; [%q {|inv(norm(w) pow (k + 1) * m)|} ]] vREAL_DOWN2) ---->
  vASM_SIMP_TAC[vREAL_LT_01; vREAL_LT_INV_EQ; vREAL_LT_MUL; vREAL_POW_LT;
               vCOMPLEX_NORM_NZ] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|Cx(t) * w|} ] ----> vREWRITE_TAC[vCOMPLEX_POW_MUL] ---->
  vREWRITE_TAC[vCOMPLEX_ADD_LDISTRIB; vGSYM vCOMPLEX_MUL_ASSOC] ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP (vSIMPLE_COMPLEX_ARITH
   [%q {|(a + w = Cx(&0)) ==> (w = --a)|} ])) ---->
  vREWRITE_TAC[vGSYM vCX_NEG; vGSYM vCX_POW; vGSYM vCX_MUL] ---->
  vREWRITE_TAC[vCOMPLEX_ADD_ASSOC; vGSYM vCX_ADD] ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|norm(Cx(&1 + t pow k * -- &1)) +
              norm(Cx(t pow k) * w pow k * Cx t * w * poly s (Cx t * w))|} ] ---->
  vREWRITE_TAC[vCOMPLEX_NORM_TRIANGLE] ----> vREWRITE_TAC[vCOMPLEX_NORM_CX] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|&0 <= x /\ x < t /\ t <= &1 ==> abs(&1 + t * --(&1)) + x < &1|} ]) ---->
  vREWRITE_TAC[vCOMPLEX_NORM_POS] ---->
  vASM_SIMP_TAC[vREAL_POW_1_LE; vREAL_LT_IMP_LE] ---->
  vONCE_REWRITE_TAC[vCOMPLEX_NORM_MUL] ----> vREWRITE_TAC[vCOMPLEX_NORM_CX] ---->
  vASM_SIMP_TAC[real_abs; vREAL_LT_IMP_LE; vREAL_POW_LE] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_RID] ---->
  vMATCH_MP_TAC vREAL_LT_LMUL ----> vASM_SIMP_TAC[vREAL_POW_LT] ---->
  vONCE_REWRITE_TAC[vAC vCOMPLEX_MUL_AC [%q {|a * b * c * d = b * (c * a) * d|} ]] ---->
  vREWRITE_TAC[vGSYM(vCONJUNCT2 complex_pow)] ---->
  vREWRITE_TAC[vCOMPLEX_NORM_MUL; vADD1; vCOMPLEX_NORM_CX] ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|abs t * norm(w pow (k + 1)) * m|} ] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LE_LMUL ----> vREWRITE_TAC[vREAL_ABS_POS] ---->
    vMATCH_MP_TAC vREAL_LE_LMUL ----> vREWRITE_TAC[vCOMPLEX_NORM_POS] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vREWRITE_TAC[vCOMPLEX_NORM_MUL] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
    vMATCH_MP_TAC vREAL_LE_RMUL ----> vREWRITE_TAC[vCOMPLEX_NORM_POS] ---->
    vASM_SIMP_TAC[vCOMPLEX_NORM_CX; vREAL_ARITH
      [%q {|&0 < t /\ t < &1 ==> abs(t) <= &1|} ]]; vALL_TAC] ---->
  vASM_SIMP_TAC[vGSYM vREAL_LT_RDIV_EQ; vREAL_LT_MUL; vCOMPLEX_NORM_POW;
               vREAL_POW_LT; vCOMPLEX_NORM_NZ] ---->
  vASM_SIMP_TAC[real_div; vREAL_MUL_LID;
               vREAL_ARITH [%q {|&0 < t /\ t < x ==> abs(t) < x|} ]]);;

(* ------------------------------------------------------------------------- *)
(* Alternative version with a syntactic notion of constant polynomial.       *)
(* ------------------------------------------------------------------------- *)

let%a vFUNDAMENTAL_THEOREM_OF_ALGEBRA_ALT = prove
 ([%q {|!p. ~(?a l. ~(a = Cx(&0)) /\ ALL (\b. b = Cx(&0)) l /\ (p = CONS a l))
       ==> ?z. poly p z = Cx(&0)|} ],
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[poly; vCONS_11] ---->
  vPOP_ASSUM_LIST(vK vALL_TAC) ---->
  vONCE_REWRITE_TAC[vAC vCONJ_ACI [%q {|a /\ b /\ c /\ d <=> c /\ d /\ a /\ b|} ]] ---->
  vREWRITE_TAC[vRIGHT_EXISTS_AND_THM; vUNWIND_THM1] ---->
  vASM_CASES_TAC [%q {|h = Cx(&0)|} ] ----> vASM_REWRITE_TAC[vCOMPLEX_ADD_LID] ++-->
   [vEXISTS_TAC [%q {|Cx(&0)|} ] ----> vASM_REWRITE_TAC[vCOMPLEX_MUL_LZERO]; vALL_TAC] ---->
  vDISCH_TAC ----> vREWRITE_TAC[vGSYM(vCONJUNCT2 poly)] ---->
  vMATCH_MP_TAC vFUNDAMENTAL_THEOREM_OF_ALGEBRA ---->
  vUNDISCH_TAC [%q {|~ALL (\b. b = Cx (&0)) t|} ] ---->
  vREWRITE_TAC[vTAUT [%q {|~b ==> ~a <=> a ==> b|} ]] ----> vPOP_ASSUM(vK vALL_TAC) ---->
  vREWRITE_TAC[constant; poly; vREAL_EQ_LADD] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|Cx(&0)|} ] -| vONCE_REWRITE_RULE[vSWAP_FORALL_THM]) ---->
  vREWRITE_TAC[vCOMPLEX_MUL_LZERO; vCOMPLEX_EQ_ADD_LCANCEL] ---->
  vREWRITE_TAC[vCOMPLEX_ENTIRE; vTAUT [%q {|a \/ b <=> ~a ==> b|} ]] ---->
  vSPEC_TAC([%q {|t:complex list|} ],[%q {|p:complex list|} ]) ---->
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vALL] ---->
  vASM_CASES_TAC [%q {|h = Cx(&0)|} ] ---->
  vASM_SIMP_TAC[poly; vCOMPLEX_ADD_LID; vCOMPLEX_ENTIRE] ---->
  vMP_TAC(vSPECL [[%q {|t:complex list|} ]; [%q {|&1|} ]] vPOLY_BOUND_EXISTS) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|norm(h) / m|} ]; [%q {|&1|} ]] vREAL_DOWN2) ---->
  vASM_SIMP_TAC[vREAL_LT_01; vREAL_LT_DIV; vCOMPLEX_NORM_NZ] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vSTRIP_ASSUME_TAC) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|Cx(x)|} ]) ---->
  vASM_SIMP_TAC[vCX_INJ; vREAL_LT_IMP_NZ] ---->
  vREWRITE_TAC[vSIMPLE_COMPLEX_ARITH [%q {|(x + y = Cx(&0)) <=> (y = --x)|} ]] ---->
  vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|norm|} ]) ----> vREWRITE_TAC[vCOMPLEX_NORM_NEG] ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|abs(a) < abs(b) ==> ~(a = b)|} ]) ---->
  vREWRITE_TAC[real_abs; vCOMPLEX_NORM_POS] ---->
  vREWRITE_TAC[vCOMPLEX_NORM_MUL; vCOMPLEX_NORM_CX] ---->
  vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|norm(h) / m * m|} ] ---->
  vCONJ_TAC ++-->
   [vALL_TAC; vASM_SIMP_TAC[vREAL_LE_REFL; vREAL_DIV_RMUL; vREAL_LT_IMP_NZ]] ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|abs(x) * m|} ] ---->
  vASM_SIMP_TAC[vREAL_LT_RMUL; vREAL_ARITH [%q {|&0 < x /\ x < a ==> abs(x) < a|} ]] ---->
  vASM_MESON_TAC[vREAL_LE_LMUL; vREAL_ABS_POS; vCOMPLEX_NORM_CX;
                vREAL_ARITH [%q {|&0 < x /\ x < &1 ==> abs(x) <= &1|} ]]);;
