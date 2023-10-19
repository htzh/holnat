[@@@warning "-27-26-8"]
open Hol.All
open Hol.Accept
include Fundamental
;;
(* ========================================================================= *)
(* Naive quantifier elimination for complex numbers.                         *)
(* ========================================================================= *)

let%a vNULLSTELLENSATZ_LEMMA = prove
 ([%q {|!n p q. (!x. (poly p x = Cx(&0)) ==> (poly q x = Cx(&0))) /\
           (degree p = n) /\ ~(n = 0)
           ==> p divides (q exp n)|} ],
  vMATCH_MP_TAC num_WF ----> vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_TAC ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|p:complex list|} ]; [%q {|q:complex list|} ]] ---->
  vASM_CASES_TAC [%q {|?a. poly p a = Cx(&0)|} ] ++-->
   [vALL_TAC;
    vDISCH_THEN(vK vALL_TAC) ---->
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP
     (vONCE_REWRITE_RULE[vTAUT [%q {|a ==> b <=> ~b ==> ~a|} ]]
                       vFUNDAMENTAL_THEOREM_OF_ALGEBRA_ALT)) ---->
    vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
    vMAP_EVERY vX_GEN_TAC [[%q {|k:complex|} ]; [%q {|zeros:complex list|} ]] ---->
    vSTRIP_TAC ----> vREWRITE_TAC[divides] ---->
    vEXISTS_TAC [%q {|[inv(k)] ** q exp n|} ] ---->
    vASM_REWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL] ----> vX_GEN_TAC [%q {|z:complex|} ] ---->
    vASM_SIMP_TAC[vCOMPLEX_MUL_ASSOC; vCOMPLEX_MUL_RINV; vCOMPLEX_MUL_LID;
                 poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID; vPOLY_0]] ---->
  vFIRST_X_ASSUM(vX_CHOOSE_THEN [%q {|a:complex|} ] vMP_TAC) ---->
  vDISCH_THEN(fun th -> vASSUME_TAC th ----> vMP_TAC th) ---->
  vGEN_REWRITE_TAC vLAND_CONV [vORDER_ROOT] ---->
  vASM_CASES_TAC [%q {|poly p = poly []|} ] ----> vASM_REWRITE_TAC[] ++-->
   [vASM_SIMP_TAC[vDEGREE_ZERO] ----> vMESON_TAC[]; vALL_TAC] ---->
  vSTRIP_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|p:complex list|} ]; [%q {|a:complex|} ]; [%q {|order a p|} ]] vORDER) ---->
  vASM_REWRITE_TAC[] ----> vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|a:complex|} ] -| vMATCH_MP vORDER_DEGREE) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|a:complex|} ]) ---->
  vREWRITE_TAC[vASSUME [%q {|poly p a = Cx(&0)|} ]] ---->
  vREWRITE_TAC[vPOLY_LINEAR_DIVIDES] ---->
  vASM_CASES_TAC [%q {|q:complex list = []|} ] ++-->
   [vDISCH_TAC ----> vMATCH_MP_TAC vPOLY_DIVIDES_ZERO ---->
    vUNDISCH_TAC [%q {|~(n = 0)|} ] ----> vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ---->
    vINDUCT_TAC ----> vASM_REWRITE_TAC[poly_exp] ----> vDISCH_TAC ---->
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; vCOMPLEX_MUL_LZERO; poly];
    vALL_TAC] ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|r:complex list|} ] vSUBST_ALL_TAC) ---->
  vUNDISCH_TAC [%q {|[--a; Cx (&1)] exp (order a p) divides p|} ] ---->
  vGEN_REWRITE_TAC vLAND_CONV [divides] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:complex list|} ] vASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|~(poly s = poly [])|} ] vASSUME_TAC ++-->
   [vDISCH_TAC ----> vUNDISCH_TAC [%q {|~(poly p = poly [])|} ] ---->
    vASM_REWRITE_TAC[vPOLY_ENTIRE]; vALL_TAC] ---->
  vASM_CASES_TAC [%q {|degree s = 0|} ] ++-->
   [vSUBGOAL_THEN [%q {|?k. ~(k = Cx(&0)) /\ (poly s = poly [k])|} ] vMP_TAC ++-->
     [vEXISTS_TAC [%q {|LAST(normalize s)|} ] ---->
      vASM_SIMP_TAC[vNORMAL_NORMALIZE; vGSYM vPOLY_NORMALIZE_ZERO] ---->
      vGEN_REWRITE_TAC vLAND_CONV [vGSYM vPOLY_NORMALIZE] ---->
      vUNDISCH_TAC [%q {|degree s = 0|} ] ---->
      vFIRST_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vRAND_CONV
        [vPOLY_NORMALIZE_ZERO]) ---->
      vREWRITE_TAC[degree] ---->
      vSPEC_TAC([%q {|normalize s|} ],[%q {|s:complex list|} ]) ---->
      vLIST_INDUCT_TAC ----> vREWRITE_TAC[vNOT_CONS_NIL] ---->
      vREWRITE_TAC[vLENGTH; vPRE; poly; vLAST] ---->
      vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
      vASM_REWRITE_TAC[vLENGTH_EQ_NIL]; vALL_TAC] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:complex|} ] vSTRIP_ASSUME_TAC) ---->
    vREWRITE_TAC[divides] ---->
    vEXISTS_TAC [%q {|[inv(k)] ** [--a; Cx (&1)] exp (n - order a p) ** r exp n|} ] ---->
    vASM_REWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; vPOLY_EXP; vCOMPLEX_POW_MUL] ---->
    vX_GEN_TAC [%q {|z:complex|} ] ---->
    vONCE_REWRITE_TAC[vAC vCOMPLEX_MUL_AC
     [%q {|(a * b) * c * d * e = ((d * a) * (c * b)) * e|} ]] ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vGSYM vCOMPLEX_POW_ADD] ----> vASM_SIMP_TAC[vSUB_ADD] ---->
    vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID; vCOMPLEX_MUL_RID] ---->
    vASM_SIMP_TAC[vCOMPLEX_MUL_LINV; vCOMPLEX_MUL_RID]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|degree s < n|} ] vASSUME_TAC ++-->
   [vEXPAND_TAC "n" ---->
    vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP vDEGREE_WELLDEF) ---->
    vREWRITE_TAC[vLINEAR_POW_MUL_DEGREE] ---->
    vASM_REWRITE_TAC[] ----> vUNDISCH_TAC [%q {|~(order a p = 0)|} ] ----> vARITH_TAC;
    vALL_TAC] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|degree s|} ]) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|s:complex list|} ]; [%q {|r:complex list|} ]]) ---->
  vASM_REWRITE_TAC[] ----> vANTS_TAC ++-->
   [vX_GEN_TAC [%q {|z:complex|} ] ----> vDISCH_TAC ---->
    vUNDISCH_TAC
     [%q {|!x. (poly p x = Cx(&0)) ==> (poly([--a; Cx (&1)] ** r) x = Cx(&0))|} ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|z:complex|} ]) ----> vASM_REWRITE_TAC[] ---->
    vASM_REWRITE_TAC[vPOLY_MUL; vCOMPLEX_MUL_RID] ---->
    vREWRITE_TAC[vCOMPLEX_ENTIRE] ---->
    vMATCH_MP_TAC(vTAUT [%q {|~a ==> (a \/ b ==> b)|} ]) ---->
    vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
    vREWRITE_TAC[vSIMPLE_COMPLEX_ARITH
     [%q {|(--a + z * Cx(&1) = Cx(&0)) <=> (z = a)|} ]] ---->
    vDISCH_THEN vSUBST_ALL_TAC ---->
    vUNDISCH_TAC [%q {|poly s a = Cx (&0)|} ] ---->
    vASM_REWRITE_TAC[vPOLY_LINEAR_DIVIDES; vDE_MORGAN_THM] ---->
    vCONJ_TAC ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|u:complex list|} ] vSUBST_ALL_TAC) ---->
    vUNDISCH_TAC [%q {|~([--a; Cx (&1)] exp SUC (order a p) divides p)|} ] ---->
    vREWRITE_TAC[divides] ---->
    vEXISTS_TAC [%q {|u:complex list|} ] ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vPOLY_MUL; poly_exp; vCOMPLEX_MUL_AC; vFUN_EQ_THM];
    vALL_TAC] ---->
  vREWRITE_TAC[divides] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|u:complex list|} ] vASSUME_TAC) ---->
  vEXISTS_TAC
   [%q {|u ** [--a; Cx(&1)] exp (n - order a p) ** r exp (n - degree s)|} ] ---->
  vASM_REWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; vPOLY_EXP; vCOMPLEX_POW_MUL] ---->
  vX_GEN_TAC [%q {|z:complex|} ] ---->
  vONCE_REWRITE_TAC[vAC vCOMPLEX_MUL_AC
   [%q {|(ap * s) * u * anp * rns = (anp * ap) * rns * s * u|} ]] ---->
  vREWRITE_TAC[vGSYM vCOMPLEX_POW_ADD] ---->
  vASM_SIMP_TAC[vSUB_ADD] ----> vAP_TERM_TAC ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vGSYM vPOLY_MUL] ---->
  vSUBST1_TAC(vSYM(vASSUME [%q {|poly (r exp degree s) = poly (s ** u)|} ])) ---->
  vREWRITE_TAC[vPOLY_EXP; vGSYM vCOMPLEX_POW_ADD] ---->
  vASM_SIMP_TAC[vSUB_ADD; vLT_IMP_LE]);;

let%a vNULLSTELLENSATZ_UNIVARIATE = prove
 ([%q {|!p q. (!x. (poly p x = Cx(&0)) ==> (poly q x = Cx(&0))) <=>
         p divides (q exp (degree p)) \/
         ((poly p = poly []) /\ (poly q = poly []))|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|poly p = poly []|} ] ++-->
   [vASM_REWRITE_TAC[poly] ---->
    vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP vDEGREE_WELLDEF) ---->
    vREWRITE_TAC[degree; normalize; vLENGTH; vARITH; poly_exp] ---->
    vASM_REWRITE_TAC[divides; vFUN_EQ_THM; vPOLY_MUL; poly;
                    vCOMPLEX_MUL_LZERO; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
    vREWRITE_TAC[vCX_INJ; vREAL_OF_NUM_EQ; vARITH]; vALL_TAC] ---->
  vASM_CASES_TAC [%q {|degree p = 0|} ] ++-->
   [vALL_TAC;
    vMP_TAC(vSPECL [[%q {|degree p|} ]; [%q {|p:complex list|} ]; [%q {|q:complex list|} ]]
                 vNULLSTELLENSATZ_LEMMA) ---->
    vASM_REWRITE_TAC[] ----> vDISCH_TAC ----> vEQ_TAC ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(fun th ->
      vX_GEN_TAC [%q {|z:complex|} ] ----> vDISCH_TAC ----> vMP_TAC th) ---->
    vASM_REWRITE_TAC[divides; vFUN_EQ_THM; vPOLY_MUL] ---->
    vDISCH_THEN(vCHOOSE_THEN (vMP_TAC -| vSPEC [%q {|z:complex|} ])) ---->
    vASM_REWRITE_TAC[vPOLY_EXP; vCOMPLEX_MUL_LZERO; vCOMPLEX_POW_EQ_0]] ---->
  vASM_REWRITE_TAC[poly_exp] ---->
  vSUBGOAL_THEN [%q {|?k. ~(k = Cx(&0)) /\ (poly p = poly [k])|} ] vMP_TAC ++-->
   [vSUBST1_TAC(vSYM(vSPEC [%q {|p:complex list|} ] vPOLY_NORMALIZE)) ---->
    vEXISTS_TAC [%q {|LAST(normalize p)|} ] ---->
    vASM_SIMP_TAC[vNORMAL_NORMALIZE; vGSYM vPOLY_NORMALIZE_ZERO] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vPOLY_NORMALIZE] ---->
    vUNDISCH_TAC [%q {|degree p = 0|} ] ---->
    vFIRST_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vRAND_CONV
      [vPOLY_NORMALIZE_ZERO]) ---->
    vREWRITE_TAC[degree] ---->
    vSPEC_TAC([%q {|normalize p|} ],[%q {|p:complex list|} ]) ---->
    vLIST_INDUCT_TAC ----> vREWRITE_TAC[vNOT_CONS_NIL] ---->
    vREWRITE_TAC[vLENGTH; vPRE; poly; vLAST] ---->
    vSIMP_TAC[vLENGTH_EQ_NIL; vPOLY_NORMALIZE]; vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:complex|} ] vSTRIP_ASSUME_TAC) ---->
  vASM_REWRITE_TAC[divides; poly; vFUN_EQ_THM; vPOLY_MUL] ---->
  vASM_REWRITE_TAC[vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
  vEXISTS_TAC [%q {|[inv(k)]|} ] ---->
  vASM_REWRITE_TAC[divides; poly; vFUN_EQ_THM; vPOLY_MUL] ---->
  vASM_REWRITE_TAC[vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
  vASM_SIMP_TAC[vCOMPLEX_MUL_RINV]);;

(* ------------------------------------------------------------------------- *)
(* Useful lemma I should have proved ages ago.                               *)
(* ------------------------------------------------------------------------- *)

let%a vCONSTANT_DEGREE = prove
 ([%q {|!p. constant(poly p) <=> (degree p = 0)|} ],
  vGEN_TAC ----> vREWRITE_TAC[constant] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vASSUME_TAC -| vGSYM -| vSPEC [%q {|Cx(&0)|} ]) ---->
    vSUBGOAL_THEN [%q {|degree [poly p (Cx(&0))] = 0|} ] vMP_TAC ++-->
     [vREWRITE_TAC[degree; normalize] ---->
      vCOND_CASES_TAC ----> vREWRITE_TAC[vLENGTH] ----> vCONV_TAC vNUM_REDUCE_CONV;
      vALL_TAC] ---->
    vMATCH_MP_TAC(vARITH_RULE [%q {|(x = y) ==> (x = 0) ==> (y = 0)|} ]) ---->
    vMATCH_MP_TAC vDEGREE_WELLDEF ---->
    vREWRITE_TAC[vFUN_EQ_THM; poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
    vFIRST_ASSUM(vACCEPT_TAC -| vGSYM);
    vONCE_REWRITE_TAC[vGSYM vPOLY_NORMALIZE] ----> vREWRITE_TAC[degree] ---->
    vSPEC_TAC([%q {|normalize p|} ],[%q {|l:complex list|} ]) ---->
    vMATCH_MP_TAC list_INDUCT ----> vREWRITE_TAC[poly] ---->
    vSIMP_TAC[vLENGTH; vPRE; vLENGTH_EQ_NIL; poly; vCOMPLEX_MUL_RZERO]]);;

(* ------------------------------------------------------------------------- *)
(* It would be nicer to prove this without using algebraic closure...        *)
(* ------------------------------------------------------------------------- *)

let%a vDIVIDES_DEGREE_LEMMA = prove
 ([%q {|!n p q. (degree(p) = n)
           ==> n <= degree(p ** q) \/ (poly(p ** q) = poly [])|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[vLE_0] ----> vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|p:complex list|} ] vFUNDAMENTAL_THEOREM_OF_ALGEBRA) ---->
  vASM_REWRITE_TAC[vCONSTANT_DEGREE; vNOT_SUC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|a:complex|} ] vMP_TAC) ---->
  vGEN_REWRITE_TAC vLAND_CONV [vPOLY_LINEAR_DIVIDES] ---->
  vDISCH_THEN(vDISJ_CASES_THEN2 vSUBST_ALL_TAC vMP_TAC) ++-->
   [vREWRITE_TAC[vPOLY_MUL; poly; vCOMPLEX_MUL_LZERO; vFUN_EQ_THM];
    vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|r:complex list|} ] vSUBST_ALL_TAC) ---->
  vSUBGOAL_THEN [%q {|poly (([--a; Cx (&1)] ** r) ** q) =
                poly ([--a; Cx (&1)] ** (r ** q))|} ]
  vASSUME_TAC ++-->
   [vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; vCOMPLEX_MUL_ASSOC]; vALL_TAC] ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP vDEGREE_WELLDEF) ---->
  vASM_REWRITE_TAC[] ---->
  vMP_TAC(vSPECL [[%q {|r ** q|} ]; [%q {|--a|} ]] vLINEAR_MUL_DEGREE) ---->
  vASM_CASES_TAC [%q {|poly (r ** q) = poly []|} ] ++-->
   [vREWRITE_TAC[vFUN_EQ_THM] ---->
    vONCE_REWRITE_TAC[vPOLY_MUL] ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO]; vALL_TAC] ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vSUBGOAL_THEN [%q {|n <= degree(r ** q) \/ (poly(r ** q) = poly [])|} ] vMP_TAC ++-->
   [vALL_TAC;
    vREWRITE_TAC[vARITH_RULE [%q {|SUC n <= m + 1 <=> n <= m|} ]] ---->
    vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vFUN_EQ_THM] ---->
    vONCE_REWRITE_TAC[vPOLY_MUL] ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO]] ---->
  vMP_TAC(vSPECL [[%q {|r:complex list|} ]; [%q {|--a|} ]] vLINEAR_MUL_DEGREE) ----> vANTS_TAC ++-->
   [vUNDISCH_TAC [%q {|~(poly (r ** q) = poly [])|} ] ---->
    vREWRITE_TAC[vTAUT [%q {|~b ==> ~a <=> a ==> b|} ]] ---->
    vSIMP_TAC[poly; vFUN_EQ_THM; vPOLY_MUL; vCOMPLEX_ENTIRE]; vALL_TAC] ---->
  vDISCH_THEN vSUBST_ALL_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vUNDISCH_TAC [%q {|degree r + 1 = SUC n|} ] ----> vARITH_TAC);;

let%a vDIVIDES_DEGREE = prove
 ([%q {|!p q. p divides q ==> degree(p) <= degree(q) \/ (poly q = poly [])|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[divides; vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC [%q {|r:complex list|} ] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP vDEGREE_WELLDEF) ----> vASM_REWRITE_TAC[] ---->
  vASM_MESON_TAC[vDIVIDES_DEGREE_LEMMA]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on multivariate polynomials.                        *)
(* ------------------------------------------------------------------------- *)

let vMPOLY_BASE_CONV =
  let pth_0 = prove
   ([%q {|Cx(&0) = poly [] x|} ],
    vREWRITE_TAC[poly])
  and pth_1 = prove
   ([%q {|c = poly [c] x|} ],
    vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID])
  and pth_var = prove
   ([%q {|x = poly [Cx(&0); Cx(&1)] x|} ],
    vREWRITE_TAC[poly; vCOMPLEX_ADD_LID; vCOMPLEX_MUL_RZERO] ---->
    vREWRITE_TAC[vCOMPLEX_ADD_RID; vCOMPLEX_MUL_RID])
  and zero_tm = [%q {|Cx(&0)|} ]
  and c_tm = [%q {|c:complex|} ]
  and x_tm = [%q {|x:complex|} ] in
  let rec vMPOLY_BASE_CONV avs tm =
    if avs = [] then vREFL tm
    else if tm = zero_tm then vINST [hd avs,x_tm] pth_0
    else if tm = hd avs then
      let th1 = vINST [tm,x_tm] pth_var in
      let th2 =
        (vLAND_CONV
          (vCOMB2_CONV (vRAND_CONV (vMPOLY_BASE_CONV (tl avs)))
                      (vLAND_CONV (vMPOLY_BASE_CONV (tl avs)))))
        (rand(concl th1)) in
      vTRANS th1 th2
    else
      let th1 = vMPOLY_BASE_CONV (tl avs) tm in
      let th2 = vINST [hd avs,x_tm; rand(concl th1),c_tm] pth_1 in
      vTRANS th1 th2 in
  vMPOLY_BASE_CONV;;

let vMPOLY_NORM_CONV =
  let pth_0 = prove
   ([%q {|poly [Cx(&0)] x = poly [] x|} ],
    vREWRITE_TAC[poly; vCOMPLEX_ADD_RID; vCOMPLEX_MUL_RZERO])
  and pth_1 = prove
   ([%q {|poly [poly [] y] x = poly [] x|} ],
    vREWRITE_TAC[poly; vCOMPLEX_ADD_RID; vCOMPLEX_MUL_RZERO]) in
  let conv_fwd = vREWR_CONV(vCONJUNCT2 poly)
  and conv_bck = vREWR_CONV(vGSYM(vCONJUNCT2 poly))
  and conv_0 = vGEN_REWRITE_CONV vI [pth_0]
  and conv_1 = vGEN_REWRITE_CONV vI [pth_1] in
  let rec vNORM0_CONV tm =
   (conv_0 ||-->
    (conv_fwd +---> vRAND_CONV(vRAND_CONV vNORM0_CONV) +---> conv_bck +--->
     vTRY_CONV vNORM0_CONV)) tm
  and vNORM1_CONV tm =
   (conv_1 ||-->
    (conv_fwd +---> vRAND_CONV(vRAND_CONV vNORM1_CONV) +---> conv_bck +--->
     vTRY_CONV vNORM1_CONV)) tm in
  fun avs -> vTRY_CONV(if avs = [] then vNORM0_CONV else vNORM1_CONV);;

let vMPOLY_ADD_CONV,vMPOLY_TADD_CONV =
  let add_conv0 = vGEN_REWRITE_CONV vI (butlast (vCONJUNCTS vPOLY_ADD_CLAUSES))
  and add_conv1 = vGEN_REWRITE_CONV vI [last (vCONJUNCTS vPOLY_ADD_CLAUSES)]
  and add_conv = vREWR_CONV(vGSYM vPOLY_ADD) in
  let rec vMPOLY_ADD_CONV avs tm =
    if avs = [] then vCOMPLEX_RAT_ADD_CONV tm else
    (add_conv +---> vLAND_CONV(vMPOLY_TADD_CONV avs) +--->
     vMPOLY_NORM_CONV (tl avs)) tm
  and vMPOLY_TADD_CONV avs tm =
    (add_conv0 ||-->
      (add_conv1 +--->
       vLAND_CONV (vMPOLY_ADD_CONV (tl avs)) +--->
       vRAND_CONV (vMPOLY_TADD_CONV avs))) tm in
  vMPOLY_ADD_CONV,vMPOLY_TADD_CONV;;

let vMPOLY_CMUL_CONV,vMPOLY_TCMUL_CONV,vMPOLY_MUL_CONV,vMPOLY_TMUL_CONV =
  let cmul_conv0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 poly_cmul]
    and cmul_conv1 = vGEN_REWRITE_CONV vI [vCONJUNCT2 poly_cmul]
    and cmul_conv = vREWR_CONV(vGSYM vPOLY_CMUL)
    and mul_conv0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 vPOLY_MUL_CLAUSES]
    and mul_conv1 = vGEN_REWRITE_CONV vI [vCONJUNCT1(vCONJUNCT2 vPOLY_MUL_CLAUSES)]
    and mul_conv2 = vGEN_REWRITE_CONV vI [vCONJUNCT2(vCONJUNCT2 vPOLY_MUL_CLAUSES)]
    and mul_conv = vREWR_CONV(vGSYM vPOLY_MUL) in
  let rec vMPOLY_CMUL_CONV avs tm =
    (cmul_conv +---> vLAND_CONV(vMPOLY_TCMUL_CONV avs)) tm
  and vMPOLY_TCMUL_CONV avs tm =
    (cmul_conv0 ||-->
      (cmul_conv1 +--->
       vLAND_CONV (vMPOLY_MUL_CONV (tl avs)) +--->
       vRAND_CONV (vMPOLY_TCMUL_CONV avs))) tm
  and vMPOLY_MUL_CONV avs tm =
    if avs = [] then vCOMPLEX_RAT_MUL_CONV tm else
    (mul_conv +---> vLAND_CONV(vMPOLY_TMUL_CONV avs)) tm
  and vMPOLY_TMUL_CONV avs tm =
    (mul_conv0 ||-->
     (mul_conv1 +---> vMPOLY_TCMUL_CONV avs) ||-->
     (mul_conv2 +--->
      vCOMB2_CONV (vRAND_CONV(vMPOLY_TCMUL_CONV avs))
                 (vCOMB2_CONV (vRAND_CONV(vMPOLY_BASE_CONV (tl avs)))
                             (vMPOLY_TMUL_CONV avs)) +--->
      vMPOLY_TADD_CONV avs)) tm in
  vMPOLY_CMUL_CONV,vMPOLY_TCMUL_CONV,vMPOLY_MUL_CONV,vMPOLY_TMUL_CONV;;

let vMPOLY_SUB_CONV =
  let pth = prove
   ([%q {|(poly p x - poly q x) = (poly p x + Cx(--(&1)) * poly q x)|} ],
    vSIMPLE_COMPLEX_ARITH_TAC) in
  let vAPPLY_PTH_CONV = vREWR_CONV pth in
  fun avs ->
     vAPPLY_PTH_CONV +--->
     vRAND_CONV(vLAND_CONV (vMPOLY_BASE_CONV (tl avs)) +--->
               vMPOLY_CMUL_CONV avs) +--->
     vMPOLY_ADD_CONV avs;;

let vMPOLY_POW_CONV =
  let cnv_0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 complex_pow]
  and cnv_1 = vGEN_REWRITE_CONV vI [vCONJUNCT2 complex_pow] in
  let rec vMPOLY_POW_CONV avs tm =
    try (cnv_0 +---> vMPOLY_BASE_CONV avs) tm with Failure _ ->
    (vRAND_CONV num_CONV +--->
     cnv_1 +---> (vRAND_CONV (vMPOLY_POW_CONV avs)) +--->
     vMPOLY_MUL_CONV avs) tm in
  vMPOLY_POW_CONV;;

(* ------------------------------------------------------------------------- *)
(* Recursive conversion to polynomial form.                                  *)
(* ------------------------------------------------------------------------- *)

let vPOLYNATE_CONV =
  let vELIM_SUB_CONV = vREWR_CONV
    (vSIMPLE_COMPLEX_ARITH [%q {|x - y = x + Cx(--(&1)) * y|} ])
  and vELIM_NEG_CONV = vREWR_CONV
    (vSIMPLE_COMPLEX_ARITH [%q {|--x = Cx(--(&1)) * x|} ])
  and vELIM_POW_0_CONV = vGEN_REWRITE_CONV vI [vCONJUNCT1 complex_pow]
  and vELIM_POW_1_CONV =
    vRAND_CONV num_CONV +---> vGEN_REWRITE_CONV vI [vCONJUNCT2 complex_pow] in
  let rec vELIM_POW_CONV tm =
    (vELIM_POW_0_CONV ||--> (vELIM_POW_1_CONV +---> vRAND_CONV vELIM_POW_CONV))
    tm in
  let polynet = itlist (uncurry net_of_conv)
    [[%q {|x pow n|} ],(fun cnv avs -> vLAND_CONV (cnv avs) +---> vMPOLY_POW_CONV avs);
     [%q {|x * y|} ],(fun cnv avs -> vBINOP_CONV (cnv avs) +---> vMPOLY_MUL_CONV avs);
     [%q {|x + y|} ],(fun cnv avs -> vBINOP_CONV (cnv avs) +---> vMPOLY_ADD_CONV avs);
     [%q {|x - y|} ],(fun cnv avs -> vBINOP_CONV (cnv avs) +---> vMPOLY_SUB_CONV avs);
     [%q {|--x|} ],(fun cnv avs -> vELIM_NEG_CONV +---> (cnv avs))]
    empty_net in
  let rec vPOLYNATE_CONV avs tm =
    try snd(hd(lookup tm polynet)) vPOLYNATE_CONV avs tm
    with Failure _ -> vMPOLY_BASE_CONV avs tm in
  vPOLYNATE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Cancellation conversion.                                                  *)
(* ------------------------------------------------------------------------- *)

let vPOLY_PAD_RULE =
  let pth = prove
   ([%q {|(poly p x = Cx(&0)) ==> (poly (CONS (Cx(&0)) p) x = Cx(&0))|} ],
    vSIMP_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_LID]) in
  let vMATCH_pth = vMATCH_MP pth in
  fun avs th ->
     let th1 = vMATCH_pth th in
     vCONV_RULE(funpow 3 vLAND_CONV (vMPOLY_BASE_CONV (tl avs))) th1;;

let vPOLY_CANCEL_EQ_CONV =
  let pth_1 = prove
   ([%q {|(p = Cx(&0)) /\ ~(a = Cx(&0))
     ==> !q b. (q = Cx(&0)) <=> (a * q - b * p = Cx(&0))|} ],
    vSIMP_TAC[vCOMPLEX_MUL_RZERO; vCOMPLEX_SUB_RZERO; vCOMPLEX_ENTIRE]) in
  let vMATCH_CANCEL_THM = vMATCH_MP pth_1 in
  let rec vPOLY_CANCEL_EQ_CONV avs n ath eth tm =
    let m = length(dest_list(lhand(lhand tm))) in
    if m < n then vREFL tm else
    let th1 = funpow (m - n) (vPOLY_PAD_RULE avs) eth in
    let th2 = vMATCH_CANCEL_THM (vCONJ th1 ath) in
    let th3 = vSPECL [lhs tm; last(dest_list(lhand(lhs tm)))] th2 in
    let th4 = vCONV_RULE(vRAND_CONV(vLAND_CONV
                (vBINOP_CONV(vMPOLY_CMUL_CONV avs)))) th3 in
    let th5 = vCONV_RULE(vRAND_CONV(vLAND_CONV (vMPOLY_SUB_CONV avs))) th4 in
    vTRANS th5 (vPOLY_CANCEL_EQ_CONV avs n ath eth (rand(concl th5))) in
  vPOLY_CANCEL_EQ_CONV;;

let vRESOLVE_EQ_RAW =
  let pth = prove
   ([%q {|(poly [] x = Cx(&0)) /\
     (poly [c] x = c)|} ],
    vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID]) in
  let vREWRITE_pth = vGEN_REWRITE_CONV vLAND_CONV [pth] in
  let rec vRESOLVE_EQ asm tm =
    try vEQT_INTRO(find (fun th -> concl th = tm) asm) with Failure _ ->
    let tm' = mk_neg tm in
    try vEQF_INTRO(find (fun th -> concl th = tm') asm) with Failure _ ->
    try let th1 = vREWRITE_pth tm in
        vTRANS th1 (vRESOLVE_EQ asm (rand(concl th1)))
    with Failure _ -> vCOMPLEX_RAT_EQ_CONV tm in
  vRESOLVE_EQ;;

let vRESOLVE_EQ asm tm =
  let th = vRESOLVE_EQ_RAW asm tm in
  try vEQF_ELIM th with Failure _ -> vEQT_ELIM th;;

let vRESOLVE_EQ_THEN =
  let vMATCH_pth = vMATCH_MP
  (vTAUT [%q {|(p ==> (q <=> q1)) /\ (~p ==> (q <=> q2))
         ==> (q <=> (p /\ q1 \/ ~p /\ q2))|} ]) in
  fun asm tm yfn nfn  ->
    try let th = vRESOLVE_EQ asm tm in
        if is_neg(concl th) then nfn (th::asm) th else yfn (th::asm) th
    with Failure _ ->
        let tm' = mk_neg tm in
        let yth = vDISCH tm (yfn (vASSUME tm :: asm) (vASSUME tm))
        and nth = vDISCH tm' (nfn (vASSUME tm' :: asm) (vASSUME tm')) in
    vMATCH_pth (vCONJ yth nth);;

let vPOLY_CANCEL_ENE_CONV avs n ath eth tm =
  if is_neg tm then vRAND_CONV(vPOLY_CANCEL_EQ_CONV avs n ath eth) tm
  else vPOLY_CANCEL_EQ_CONV avs n ath eth tm;;

let vRESOLVE_NE =
  let vNEGATE_NEGATE_RULE = vGEN_REWRITE_RULE vI [vTAUT [%q {|p <=> (~p <=> F)|} ]] in
  fun asm tm ->
    try let th = vRESOLVE_EQ asm (rand tm) in
        if is_neg(concl th) then vEQT_INTRO th
        else vNEGATE_NEGATE_RULE th
    with Failure _ -> vREFL tm;;

(* ------------------------------------------------------------------------- *)
(* Conversion for division of polynomials.                                   *)
(* ------------------------------------------------------------------------- *)

let vLAST_CONV = vGEN_REWRITE_CONV vREPEATC [vLAST_CLAUSES];;

let vLENGTH_CONV =
  let cnv_0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 vLENGTH]
  and cnv_1 = vGEN_REWRITE_CONV vI [vCONJUNCT2 vLENGTH] in
  let rec vLENGTH_CONV tm =
    try cnv_0 tm with Failure _ ->
    (cnv_1 +---> vRAND_CONV vLENGTH_CONV +---> vNUM_SUC_CONV) tm in
  vLENGTH_CONV;;

let vEXPAND_EX_BETA_CONV =
  let pth = prove([%q {|EX P [c] = P c|} ],vREWRITE_TAC[vEX]) in
  let cnv_0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 vEX]
  and cnv_1 = vGEN_REWRITE_CONV vI [pth]
  and cnv_2 = vGEN_REWRITE_CONV vI [vCONJUNCT2 vEX] in
  let rec vEXPAND_EX_BETA_CONV tm =
    try (cnv_1 +---> vBETA_CONV) tm with Failure _ -> try
        (cnv_2 +---> vCOMB2_CONV (vRAND_CONV vBETA_CONV)
                                vEXPAND_EX_BETA_CONV) tm
    with Failure _ -> cnv_0 tm in
  vEXPAND_EX_BETA_CONV;;

let vPOLY_DIVIDES_PAD_RULE =
  let pth = prove
   ([%q {|p divides q ==> p divides (CONS (Cx(&0)) q)|} ],
    vREWRITE_TAC[divides; vFUN_EQ_THM; vPOLY_MUL; poly; vCOMPLEX_ADD_LID] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|r:complex list|} ] vASSUME_TAC) ---->
    vEXISTS_TAC [%q {|[Cx(&0); Cx(&1)] ** r|} ] ---->
    vASM_REWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_LID; vCOMPLEX_ADD_RID;
                    vCOMPLEX_MUL_RID; vPOLY_MUL] ---->
    vREWRITE_TAC[vCOMPLEX_MUL_AC]) in
  let vAPPLY_pth = vMATCH_MP pth in
  fun avs n tm ->
    funpow n
     (vCONV_RULE(vRAND_CONV(vLAND_CONV(vMPOLY_BASE_CONV (tl avs)))) -| vAPPLY_pth)
     (vSPEC tm vPOLY_DIVIDES_REFL);;

let vPOLY_DIVIDES_PAD_CONST_RULE =
  let pth = prove
   ([%q {|p divides q ==> !a. p divides (a ## q)|} ],
    vREWRITE_TAC[vFUN_EQ_THM; divides; vPOLY_CMUL; vPOLY_MUL] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|r:complex list|} ] vASSUME_TAC) ---->
    vX_GEN_TAC [%q {|a:complex|} ] ----> vEXISTS_TAC [%q {|[a] ** r|} ] ---->
    vASM_REWRITE_TAC[vPOLY_MUL; poly] ----> vSIMPLE_COMPLEX_ARITH_TAC) in
  let vAPPLY_pth = vMATCH_MP pth in
  fun avs n a tm ->
    let th1 = vPOLY_DIVIDES_PAD_RULE avs n tm in
    let th2 = vSPEC a (vAPPLY_pth th1) in
    vCONV_RULE(vRAND_CONV(vMPOLY_TCMUL_CONV avs)) th2;;

let vEXPAND_EX_BETA_RESOLVE_CONV asm tm =
  let th1 = vEXPAND_EX_BETA_CONV tm in
  let djs = disjuncts(rand(concl th1)) in
  let th2 = end_itlist vMK_DISJ (map (vRESOLVE_NE asm) djs) in
  vTRANS th1 th2;;

let vPOLY_DIVIDES_CONV =
  let pth_0 = prove
   ([%q {|LENGTH q < LENGTH p
     ==> ~(LAST p = Cx(&0))
         ==> (p divides q <=> ~(EX (\c. ~(c = Cx(&0))) q))|} ],
    vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vNOT_EX; vGSYM vPOLY_ZERO] ----> vEQ_TAC ++-->
     [vALL_TAC;
      vSIMP_TAC[divides; vPOLY_MUL; vFUN_EQ_THM] ---->
      vDISCH_TAC ----> vEXISTS_TAC [%q {|[]:complex list|} ] ---->
      vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO]] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIVIDES_DEGREE) ---->
    vMATCH_MP_TAC(vTAUT [%q {|(~b ==> ~a) ==> (a \/ b ==> b)|} ]) ---->
    vDISCH_TAC ----> vREWRITE_TAC[vNOT_LE] ----> vASM_SIMP_TAC[vNORMAL_DEGREE] ---->
    vREWRITE_TAC[degree] ---->
    vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vARITH_RULE
     [%q {|lq < lp ==> ~(lq = 0) /\ dq <= lq - 1 ==> dq < lp - 1|} ])) ---->
    vCONJ_TAC ++--> [vASM_MESON_TAC[vLENGTH_EQ_NIL]; vALL_TAC] ---->
    vMATCH_MP_TAC(vARITH_RULE [%q {|m <= n ==> PRE m <= n - 1|} ]) ---->
    vREWRITE_TAC[vLENGTH_NORMALIZE_LE]) in
  let vAPPLY_pth0 = vPART_MATCH (lhand -| rand -| rand) pth_0 in
  let pth_1 = prove
   ([%q {|~(a = Cx(&0))
     ==> p divides p'
         ==> (!x. a * poly q x - poly p' x = poly r x)
             ==> (p divides q <=> p divides r)|} ],
    vDISCH_TAC ----> vREWRITE_TAC[divides; vLEFT_IMP_EXISTS_THM] ---->
    vX_GEN_TAC [%q {|t:complex list|} ] ----> vDISCH_THEN vSUBST1_TAC ---->
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL] ---->
    vDISCH_THEN(fun th -> vREWRITE_TAC[vGSYM th]) ----> vEQ_TAC ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:complex list|} ] vMP_TAC) ++-->
     [vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
      vEXISTS_TAC [%q {|a ## s ++ --(Cx(&1)) ## t|} ] ---->
      vREWRITE_TAC[vPOLY_MUL; vPOLY_ADD; vPOLY_CMUL] ---->
      vREWRITE_TAC[poly] ----> vSIMPLE_COMPLEX_ARITH_TAC;
      vREWRITE_TAC[vPOLY_MUL] ----> vDISCH_TAC ---->
      vEXISTS_TAC [%q {|[inv(a)] ** (t ++ s)|} ] ---->
      vX_GEN_TAC [%q {|z:complex|} ] ---->
      vONCE_REWRITE_TAC[vCOMPLEX_MUL_SYM] ---->
      vREWRITE_TAC[vPOLY_MUL; vPOLY_ADD; vGSYM vCOMPLEX_MUL_ASSOC] ---->
      vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID] ---->
      vSUBGOAL_THEN [%q {|a * poly q z = (poly t z + poly s z) * poly p z|} ]
      vMP_TAC ++-->
       [vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|z:complex|} ]) ----> vSIMPLE_COMPLEX_ARITH_TAC;
        vALL_TAC] ---->
      vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|( * ) (inv a)|} ]) ---->
      vASM_SIMP_TAC[vCOMPLEX_MUL_ASSOC; vCOMPLEX_MUL_LINV; vCOMPLEX_MUL_LID]]) in
  let vMATCH_pth1 = vMATCH_MP pth_1 in
  let rec vDIVIDE_STEP_CONV avs sfn n tm =
    let m = length(dest_list(rand tm)) in
    if m < n then vREFL tm else
    let th1 = vPOLY_DIVIDES_PAD_CONST_RULE avs (m - n)
                 (last(dest_list(rand tm))) (lhand tm) in
    let th2 = vMATCH_MP (sfn tm) th1 in
    let av,bod = dest_forall(lhand(concl th2)) in
    let tm1 = vsubst [hd avs,av] (lhand bod) in
    let th3 = (vLAND_CONV (vMPOLY_CMUL_CONV avs) +---> vMPOLY_SUB_CONV avs) tm1 in
    let th4 = vMATCH_MP th2 (vGEN (hd avs) th3) in
    vTRANS th4 (vDIVIDE_STEP_CONV avs sfn n (rand(concl th4))) in
  let zero_tm = [%q {|Cx(&0)|} ] in
  fun asm avs tm ->
    let ath = vRESOLVE_EQ asm (mk_eq(last(dest_list(lhand tm)),zero_tm)) in
    let sfn = vPART_MATCH (lhand -| rand -| rand) (vMATCH_pth1 ath)
    and n = length(dest_list(lhand tm)) in
    let th1 = vDIVIDE_STEP_CONV avs sfn n tm in
    let th2 = vAPPLY_pth0 (rand(concl th1)) in
    let th3 = (vBINOP_CONV vLENGTH_CONV +---> vNUM_LT_CONV) (lhand(concl th2)) in
    let th4 = vMP th2 (vEQT_ELIM th3) in
    let th5 = vCONV_RULE(vLAND_CONV(vRAND_CONV(vLAND_CONV vLAST_CONV))) th4 in
    let th6 = vTRANS th1 (vMP th5 ath) in
    vCONV_RULE(vRAND_CONV(vRAND_CONV(vEXPAND_EX_BETA_RESOLVE_CONV asm))) th6;;

(* ------------------------------------------------------------------------- *)
(* Apply basic Nullstellensatz principle.                                    *)
(* ------------------------------------------------------------------------- *)

let vBASIC_QUELIM_CONV =
  let pth_1 = prove
   ([%q {|((?x. (poly p x = Cx(&0)) /\ ~(poly [] x = Cx(&0))) <=> F) /\
     ((?x. ~(poly [] x = Cx(&0))) <=> F) /\
     ((?x. ~(poly [c] x = Cx(&0))) <=> ~(c = Cx(&0))) /\
     ((?x. (poly [] x = Cx(&0))) <=> T) /\
     ((?x. (poly [c] x = Cx(&0))) <=> (c = Cx(&0)))|} ],
    vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID]) in
  let vAPPLY_pth1 = vGEN_REWRITE_CONV vI [pth_1] in
  let pth_2 = prove
   ([%q {|~(LAST(CONS a (CONS b p)) = Cx(&0))
     ==> ((?x. poly (CONS a (CONS b p)) x = Cx(&0)) <=> T)|} ],
    vREPEAT vSTRIP_TAC ---->
    vMP_TAC(vSPEC [%q {|CONS (a:complex) (CONS b p)|} ]
             vFUNDAMENTAL_THEOREM_OF_ALGEBRA_ALT) ---->
    vREWRITE_TAC[] ----> vDISCH_THEN vMATCH_MP_TAC ---->
    vREWRITE_TAC[vNOT_EXISTS_THM; vCONS_11] ---->
    vREPEAT vSTRIP_TAC ---->
    vSUBGOAL_THEN [%q {|~(ALL (\c. c = Cx(&0)) (CONS b p))|} ]
     (fun th -> vMP_TAC th ----> vASM_REWRITE_TAC[]) ---->
    vUNDISCH_TAC [%q {|~(LAST (CONS a (CONS b p)) = Cx (&0))|} ] ---->
    vONCE_REWRITE_TAC[vLAST] ----> vREWRITE_TAC[vNOT_CONS_NIL] ---->
    vREWRITE_TAC[vTAUT [%q {|~a ==> ~b <=> b ==> a|} ]] ---->
    vSPEC_TAC([%q {|p:complex list|} ],[%q {|p:complex list|} ]) ---->
    vLIST_INDUCT_TAC ----> vONCE_REWRITE_TAC[vLAST] ---->
    vREWRITE_TAC[vALL; vNOT_CONS_NIL] ---->
    vSTRIP_TAC ----> vFIRST_ASSUM(vUNDISCH_TAC -| check is_imp -| concl) ---->
    vREWRITE_TAC[vLAST] ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vALL]) in
  let vAPPLY_pth2 = vPART_MATCH (lhand -| rand) pth_2 in
  let pth_2b = prove
   ([%q {|(?x. ~(poly p x = Cx(&0))) <=> EX (\c. ~(c = Cx(&0))) p|} ],
    vREWRITE_TAC[vGSYM vNOT_FORALL_THM] ---->
    vONCE_REWRITE_TAC[vTAUT [%q {|(~a <=> b) <=> (a <=> ~b)|} ]] ---->
    vREWRITE_TAC[vNOT_EX; vGSYM vPOLY_ZERO; poly; vFUN_EQ_THM]) in
  let vAPPLY_pth2b = vGEN_REWRITE_CONV vI [pth_2b] in
  let pth_3 = prove
   ([%q {|~(LAST(CONS a p) = Cx(&0))
     ==> ((?x. (poly (CONS a p) x = Cx(&0)) /\ ~(poly q x = Cx(&0))) <=>
          ~((CONS a p) divides (q exp (LENGTH p))))|} ],
    vREPEAT vSTRIP_TAC ---->
    vMP_TAC(vSPECL [[%q {|CONS (a:complex) p|} ]; [%q {|q:complex list|} ]]
                 vNULLSTELLENSATZ_UNIVARIATE) ---->
    vASM_SIMP_TAC[degree; vNORMALIZE_EQ; vLENGTH; vPRE] ---->
    vSUBGOAL_THEN [%q {|~(poly (CONS a p) = poly [])|} ]
     (fun th -> vREWRITE_TAC[th] ----> vMESON_TAC[]) ---->
    vREWRITE_TAC[vPOLY_ZERO] ----> vPOP_ASSUM vMP_TAC ---->
    vSPEC_TAC([%q {|p:complex list|} ],[%q {|p:complex list|} ]) ---->
    vREWRITE_TAC[vLAST] ---->
    vLIST_INDUCT_TAC ----> vREWRITE_TAC[vLAST; vALL; vNOT_CONS_NIL] ---->
    vPOP_ASSUM vMP_TAC ----> vCOND_CASES_TAC ----> vASM_SIMP_TAC[vALL] ---->
    vCONV_TAC vTAUT) in
  let vAPPLY_pth3 = vPART_MATCH (lhand -| rand) pth_3 in
  let vPOLY_EXP_DIVIDES_CONV =
    let pth_4 = prove
     ([%q {|(!x. (poly (q exp n) x = poly r x))
       ==> (p divides (q exp n) <=> p divides r)|} ],
      vSIMP_TAC[divides; vPOLY_EXP; vFUN_EQ_THM]) in
    let vAPPLY_pth4 = vMATCH_MP pth_4
    and poly_tm = [%q {|poly|} ]
    and vREWR_POLY_EXP_CONV = vREWR_CONV vPOLY_EXP in
    let vPOLY_EXP_DIVIDES_CONV avs tm =
      let tm1 = mk_comb(mk_comb(poly_tm,rand tm),hd avs) in
      let th1 = vREWR_POLY_EXP_CONV tm1 in
      let th2 = vTRANS th1 (vMPOLY_POW_CONV avs (rand(concl th1))) in
      vPART_MATCH lhand (vAPPLY_pth4 (vGEN (hd avs) th2)) tm in
    vPOLY_EXP_DIVIDES_CONV in
  fun asm avs tm ->
    try vAPPLY_pth1 tm with Failure _ ->
    try let th1 = vAPPLY_pth2 tm in
        let th2 = vCONV_RULE(vLAND_CONV(vRAND_CONV(vLAND_CONV vLAST_CONV))) th1 in
        let th3 = try vMATCH_MP th2 (vRESOLVE_EQ asm (rand(lhand(concl th2))))
                  with Failure _ -> failwith "Sanity failure (2a)" in
        th3
    with Failure _ -> try
        let th1 = vAPPLY_pth2b tm in
        vTRANS th1 (vEXPAND_EX_BETA_RESOLVE_CONV asm (rand(concl th1)))
    with Failure _ ->
        let th1 = vAPPLY_pth3 tm in
        let th2 = vCONV_RULE(vLAND_CONV(vRAND_CONV(vLAND_CONV vLAST_CONV))) th1 in
        let th3 = try vMATCH_MP th2 (vRESOLVE_EQ asm (rand(lhand(concl th2))))
                  with Failure _ -> failwith "Sanity failure (2b)" in
        let th4 = vCONV_RULE (funpow 4 vRAND_CONV vLENGTH_CONV) th3 in
        let th5 =
           vCONV_RULE(vRAND_CONV(vRAND_CONV(vPOLY_EXP_DIVIDES_CONV avs))) th4 in
        vCONV_RULE(vRAND_CONV(vRAND_CONV(vPOLY_DIVIDES_CONV asm avs))) th5;;

(* ------------------------------------------------------------------------- *)
(* Put into canonical form by multiplying inequalities.                      *)
(* ------------------------------------------------------------------------- *)

let vPOLY_NE_MULT_CONV =
  let pth = prove
   ([%q {|~(poly p x = Cx(&0)) /\ ~(poly q x = Cx(&0)) <=>
     ~(poly p x * poly q x = Cx(&0))|} ],
    vREWRITE_TAC[vCOMPLEX_ENTIRE; vDE_MORGAN_THM]) in
  let vAPPLY_pth = vREWR_CONV pth in
  let rec vPOLY_NE_MULT_CONV avs tm =
    if not(is_conj tm) then vREFL tm else
    let l,r = dest_conj tm in
    let th1 = vMK_COMB(vAP_TERM (rator(rator tm)) (vPOLY_NE_MULT_CONV avs l),
                      vPOLY_NE_MULT_CONV avs r) in
    let th2 = vTRANS th1 (vAPPLY_pth (rand(concl th1))) in
    vCONV_RULE(vRAND_CONV(vRAND_CONV(vLAND_CONV(vMPOLY_MUL_CONV avs)))) th2 in
  vPOLY_NE_MULT_CONV;;

let vCORE_QUELIM_CONV =
  let vCONJ_AC_RULE = vAC vCONJ_ACI in
  let vCORE_QUELIM_CONV asm avs tm =
    let ev,bod = dest_exists tm in
    let cjs = conjuncts bod in
    let eqs,neqs = partition is_eq cjs in
    if eqs = [] then
      let th1 = vMK_EXISTS ev (vPOLY_NE_MULT_CONV avs bod) in
      vTRANS th1 (vBASIC_QUELIM_CONV asm avs (rand(concl th1)))
    else if length eqs > 1 then failwith "CORE_QUELIM_CONV: Sanity failure"
    else if neqs = [] then vBASIC_QUELIM_CONV asm avs tm else
    let tm1 = mk_conj(hd eqs,list_mk_conj neqs) in
    let th1 = vCONJ_AC_RULE(mk_eq(bod,tm1)) in
    let th2 = vCONV_RULE(funpow 2 vRAND_CONV(vPOLY_NE_MULT_CONV avs)) th1 in
    let th3 = vMK_EXISTS ev th2 in
    vTRANS th3 (vBASIC_QUELIM_CONV asm avs (rand(concl th3))) in
  vCORE_QUELIM_CONV;;

(* ------------------------------------------------------------------------- *)
(* Main elimination coversion (for a single quantifier).                     *)
(* ------------------------------------------------------------------------- *)

let vRESOLVE_EQ_NE =
  let vDNE_RULE = vGEN_REWRITE_RULE vI
   [vTAUT [%q {|((p <=> T) <=> (~p <=> F)) /\ ((p <=> F) <=> (~p <=> T))|} ]] in
  fun asm tm ->
    if is_neg tm then vDNE_RULE(vRESOLVE_EQ_RAW asm (rand tm))
    else vRESOLVE_EQ_RAW asm tm;;

let vCOMPLEX_QUELIM_CONV =
  let pth_0 = prove
   ([%q {|((poly [] x = Cx(&0)) <=> T) /\
     ((poly [] x = Cx(&0)) /\ p <=> p)|} ],
    vREWRITE_TAC[poly])
  and pth_1 = prove
   ([%q {|(~(poly [] x = Cx(&0)) <=> F) /\
     (~(poly [] x = Cx(&0)) /\ p <=> F)|} ],
    vREWRITE_TAC[poly])
  and pth_2 = prove
   ([%q {|(p ==> (q <=> r)) ==> (p /\ q <=> p /\ r)|} ],
    vCONV_TAC vTAUT)
  and zero_tm = [%q {|Cx(&0)|} ]
  and true_tm = [%q {|T|} ] in
  let vELIM_ZERO_RULE = vGEN_REWRITE_RULE vRAND_CONV [pth_0]
  and vELIM_NONZERO_RULE = vGEN_REWRITE_RULE vRAND_CONV [pth_1]
  and vINCORP_ASSUM_THM = vMATCH_MP pth_2
  and vCONJ_AC_RULE = vAC vCONJ_ACI in
  let vPOLY_CONST_CONV =
    let pth = prove
     ([%q {|((poly [c] x = y) <=> (c = y)) /\
       (~(poly [c] x = y) <=> ~(c = y))|} ],
      vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID]) in
    vTRY_CONV(vGEN_REWRITE_CONV vI [pth]) in
  let vEXISTS_TRIV_CONV = vREWR_CONV vEXISTS_SIMP
  and vEXISTS_PUSH_CONV = vREWR_CONV vRIGHT_EXISTS_AND_THM
  and vAND_SIMP_CONV = vGEN_REWRITE_CONV vDEPTH_CONV
    [vTAUT [%q {|(p /\ F <=> F) /\ (p /\ T <=> p) /\
           (F /\ p <=> F) /\ (T /\ p <=> p)|} ]]
  and vRESOLVE_OR_CONST_CONV asm tm =
    try vRESOLVE_EQ_NE asm tm with Failure _ -> vPOLY_CONST_CONV tm
  and false_tm = [%q {|F|} ] in
  let rec vCOMPLEX_QUELIM_CONV asm avs tm =
    let ev,bod = dest_exists tm in
    let cjs = conjuncts bod in
    let cjs_set = setify cjs in
    if length cjs_set < length cjs then
      let th1 = vCONJ_AC_RULE(mk_eq(bod,list_mk_conj cjs_set)) in
      let th2 = vMK_EXISTS ev th1 in
      vTRANS th2 (vCOMPLEX_QUELIM_CONV asm avs (rand(concl th2)))
    else
    let eqs,neqs = partition is_eq cjs in
    let lens = map (length -| dest_list -| lhand -| lhs) eqs
    and nens = map (length -| dest_list -| lhand -| lhs -| rand) neqs in
    try let zeq = el (index 0 lens) eqs in
        if cjs = [zeq] then vBASIC_QUELIM_CONV asm avs tm else
        let cjs' = zeq::(subtract cjs [zeq]) in
        let th1 = vELIM_ZERO_RULE(vCONJ_AC_RULE(mk_eq(bod,list_mk_conj cjs'))) in
        let th2 = vMK_EXISTS ev th1 in
        vTRANS th2 (vCOMPLEX_QUELIM_CONV asm avs (rand(concl th2)))
    with Failure _ -> try
        let zne = el (index 0 nens) neqs in
        if cjs = [zne] then vBASIC_QUELIM_CONV asm avs tm else
        let cjs' = zne::(subtract cjs [zne]) in
        let th1 = vELIM_NONZERO_RULE
          (vCONJ_AC_RULE(mk_eq(bod,list_mk_conj cjs'))) in
        vCONV_RULE (vRAND_CONV vEXISTS_TRIV_CONV) (vMK_EXISTS ev th1)
    with Failure _ -> try
        let ones = map snd (filter (fun (n,_) -> n = 1)
                                   (zip lens eqs @ zip nens neqs)) in
        if ones = [] then failwith "" else
        let cjs' = subtract cjs ones in
        if cjs' = [] then
          let th1 = vMK_EXISTS ev (vSUBS_CONV(map vPOLY_CONST_CONV cjs) bod) in
          vTRANS th1 (vEXISTS_TRIV_CONV (rand(concl th1)))
        else
          let tha = vSUBS_CONV (map (vRESOLVE_OR_CONST_CONV asm) ones)
                              (list_mk_conj ones) in
          let thb = vCONV_RULE (vRAND_CONV vAND_SIMP_CONV) tha in
          if rand(concl thb) = false_tm then
            let thc = vMK_CONJ thb (vREFL(list_mk_conj cjs')) in
            let thd = vCONV_RULE(vRAND_CONV vAND_SIMP_CONV) thc in
            let the = vCONJ_AC_RULE(mk_eq(bod,lhand(concl thd))) in
            let thf = vMK_EXISTS ev (vTRANS the thd) in
            vCONV_RULE(vRAND_CONV vEXISTS_TRIV_CONV) thf
          else
            let thc = vMK_CONJ thb (vREFL(list_mk_conj cjs')) in
            let thd = vCONJ_AC_RULE(mk_eq(bod,lhand(concl thc))) in
            let the =  vMK_EXISTS ev (vTRANS thd thc) in
            let th4 = vTRANS  the(vEXISTS_PUSH_CONV(rand(concl the))) in
            let tm4 = rand(concl th4) in
            let th5 = vCOMPLEX_QUELIM_CONV asm avs (rand tm4) in
            vTRANS th4 (vAP_TERM (rator tm4) th5)
    with Failure _ ->
    if eqs = [] ||
       (length eqs = 1 &&
        (let ceq = mk_eq(last(dest_list(lhand(lhs(hd eqs)))),zero_tm) in
         try concl(vRESOLVE_EQ asm ceq) = mk_neg ceq with Failure _ -> false) &&
        (let h = hd lens in forall (fun n -> n < h) nens))
    then
      vCORE_QUELIM_CONV asm avs tm
    else
      let n = end_itlist min lens in
      let eq = el (index n lens) eqs in
      let pol = lhand(lhand eq) in
      let atm = last(dest_list pol) in
      let zeq = mk_eq(atm,zero_tm) in
      vRESOLVE_EQ_THEN asm zeq
       (fun asm' yth ->
          let th0 = vTRANS yth (vMPOLY_BASE_CONV (tl avs) zero_tm) in
          let th1 =
            vGEN_REWRITE_CONV
             (vLAND_CONV -| vLAND_CONV -| funpow (n - 1) vRAND_CONV -| vLAND_CONV)
             [th0] eq in
          let th2 = vLAND_CONV(vMPOLY_NORM_CONV avs) (rand(concl th1)) in
          let th3 = vMK_EXISTS ev (vSUBS_CONV[vTRANS th1 th2] bod) in
          vTRANS th3 (vCOMPLEX_QUELIM_CONV asm' avs (rand(concl th3))))
       (fun asm' nth ->
          let oth = subtract cjs [eq] in
          if oth = [] then vCOMPLEX_QUELIM_CONV asm' avs tm else
          let eth = vASSUME eq in
          let ths = map (vPOLY_CANCEL_ENE_CONV avs n nth eth) oth in
          let th1 = vDISCH eq (end_itlist vMK_CONJ ths) in
          let th2 = vINCORP_ASSUM_THM th1 in
          let th3 = vTRANS (vCONJ_AC_RULE(mk_eq(bod,lhand(concl th2)))) th2 in
          let th4 = vMK_EXISTS ev th3 in
          vTRANS th4 (vCOMPLEX_QUELIM_CONV asm' avs (rand(concl th4)))) in
  fun asm avs -> (vCOMPLEX_QUELIM_CONV asm avs);;

(* ------------------------------------------------------------------------- *)
(* NNF conversion doing "conditionals" ~(p /\ q \/ ~p /\ r) intelligently.   *)
(* ------------------------------------------------------------------------- *)

let vNNF_COND_CONV =
  let vNOT_EXISTS_UNIQUE_THM = prove
   ([%q {|~(?!x. P x) <=> (!x. ~P x) \/ ?x x'. P x /\ P x' /\ ~(x = x')|} ],
    vREWRITE_TAC[vEXISTS_UNIQUE_THM; vDE_MORGAN_THM; vNOT_EXISTS_THM] ---->
    vREWRITE_TAC[vNOT_FORALL_THM; vNOT_IMP; vCONJ_ASSOC]) in
  let tauts =
    [vTAUT [%q {|~(~p) <=> p|} ];
     vTAUT [%q {|~(p /\ q) <=> ~p \/ ~q|} ];
     vTAUT [%q {|~(p \/ q) <=> ~p /\ ~q|} ];
     vTAUT [%q {|~(p ==> q) <=> p /\ ~q|} ];
     vTAUT [%q {|p ==> q <=> ~p \/ q|} ];
     vNOT_FORALL_THM;
     vNOT_EXISTS_THM;
     vEXISTS_UNIQUE_THM;
     vNOT_EXISTS_UNIQUE_THM;
     vTAUT [%q {|~(p <=> q) <=> (p /\ ~q) \/ (~p /\ q)|} ];
     vTAUT [%q {|(p <=> q) <=> (p /\ q) \/ (~p /\ ~q)|} ];
     vTAUT [%q {|~(p /\ q \/ ~p /\ r) <=> p /\ ~q \/ ~p /\ ~r|} ]] in
  vGEN_REWRITE_CONV vTOP_SWEEP_CONV tauts;;

(* ------------------------------------------------------------------------- *)
(* Overall procedure for multiple quantifiers in any first order formula.    *)
(* ------------------------------------------------------------------------- *)

let vFULL_COMPLEX_QUELIM_CONV =
  let vELIM_FORALL_CONV =
    let pth = prove([%q {|(!x. P x) <=> ~(?x. ~(P x))|} ],vMESON_TAC[]) in
    vREWR_CONV pth in
  let vELIM_EQ_CONV =
    let pth = vSIMPLE_COMPLEX_ARITH [%q {|(x = y) <=> (x - y = Cx(&0))|} ]
    and zero_tm = [%q {|Cx(&0)|} ] in
    let vREWR_pth = vREWR_CONV pth in
    fun avs tm ->
      if rand tm = zero_tm then vLAND_CONV(vPOLYNATE_CONV avs) tm
      else (vREWR_pth +---> vLAND_CONV(vPOLYNATE_CONV avs)) tm in
  let vSIMP_DNF_CONV =
    vGEN_REWRITE_CONV vTOP_DEPTH_CONV (basic_rewrites()) +--->
    vNNF_COND_CONV +---> vDNF_CONV in
  let vDISTRIB_EXISTS_CONV = vGEN_REWRITE_CONV vI [vEXISTS_OR_THM] in
  let vTRIV_EXISTS_CONV = vGEN_REWRITE_CONV vI [vEXISTS_SIMP] in
  let complex_ty = [%q {|:complex|} ] in
  let vFINAL_SIMP_CONV =
    vGEN_REWRITE_CONV vDEPTH_CONV [vCX_INJ] +--->
    vREAL_RAT_REDUCE_CONV +--->
    vGEN_REWRITE_CONV vTOP_DEPTH_CONV (basic_rewrites()) in
  let rec vFULL_COMPLEX_QUELIM_CONV avs tm =
     if is_forall tm then
        let th1 = vELIM_FORALL_CONV tm in
        let th2 = vFULL_COMPLEX_QUELIM_CONV avs (rand(concl th1)) in
        vTRANS th1 th2
     else if is_neg tm then
        vAP_TERM (rator tm) (vFULL_COMPLEX_QUELIM_CONV avs (rand tm))
     else if is_conj tm || is_disj tm || is_imp tm || is_iff tm then
        let lop,r = dest_comb tm in
        let op,l = dest_comb lop in
        let thl = vFULL_COMPLEX_QUELIM_CONV avs l
        and thr = vFULL_COMPLEX_QUELIM_CONV avs r in
        vMK_COMB(vAP_TERM(rator(rator tm)) thl,thr)
     else if is_exists tm then
        let ev,bod = dest_exists tm in
        let th0 = vFULL_COMPLEX_QUELIM_CONV (ev::avs) bod in
        let th1 = vMK_EXISTS ev (vCONV_RULE(vRAND_CONV vSIMP_DNF_CONV) th0) in
        vTRANS th1 (vDISTRIB_AND_COMPLEX_QUELIM_CONV (ev::avs) (rand(concl th1)))
     else if is_eq tm then
        vELIM_EQ_CONV avs tm
     else failwith "unexpected type of formula"
  and vDISTRIB_AND_COMPLEX_QUELIM_CONV avs tm =
    try vTRIV_EXISTS_CONV tm
    with Failure _ -> try
        (vDISTRIB_EXISTS_CONV +--->
         vBINOP_CONV (vDISTRIB_AND_COMPLEX_QUELIM_CONV avs)) tm
    with Failure _ -> vCOMPLEX_QUELIM_CONV [] avs tm in
  fun tm ->
        let avs = filter (fun t -> type_of t = complex_ty) (frees tm) in
        (vFULL_COMPLEX_QUELIM_CONV avs +---> vFINAL_SIMP_CONV) tm;;
