[@@@warning "-33-27-8"]
open Hol.All
open Hol.Accept
open Analysis
(* ======================================================================== *)
(* Properties of power series.                                              *)
(* ======================================================================== *)

(* needs "Library/analysis.ml";; *)

(* ------------------------------------------------------------------------ *)
(* More theorems about rearranging finite sums                              *)
(* ------------------------------------------------------------------------ *)

let%a vPOWDIFF_LEMMA = prove(
  [%q {|!n x y. sum(0,SUC n)(\p. (x pow p) * y pow ((SUC n) - p)) =
                y * sum(0,SUC n)(\p. (x pow p) * (y pow (n - p)))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vSUM_CMUL] ---->
  vMATCH_MP_TAC vSUM_SUBST ----> vX_GEN_TAC [%q {|p:num|} ] ----> vDISCH_TAC ---->
  vBETA_TAC ----> vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vAP_TERM_TAC ---->
  vSUBGOAL_THEN [%q {|~(n < p:num)|} ] vASSUME_TAC ++-->
   [vPOP_ASSUM(vMP_TAC -| vCONJUNCT2) ----> vREWRITE_TAC[vADD_CLAUSES] ---->
    vREWRITE_TAC[vNOT_LT; vCONJUNCT2 vLT] ---->
    vDISCH_THEN(vDISJ_CASES_THEN2 vSUBST1_TAC vMP_TAC) ---->
    vREWRITE_TAC[vLE_REFL; vLT_IMP_LE];
    vASM_REWRITE_TAC[vSUB_OLD] ----> vREWRITE_TAC[pow] ---->
    vMATCH_ACCEPT_TAC vREAL_MUL_SYM]);;

let%a vPOWDIFF = prove(
  [%q {|!n x y. (x pow (SUC n)) - (y pow (SUC n)) =
                (x - y) * sum(0,SUC n)(\p. (x pow p) * (y pow (n - p)))|} ],
  vINDUCT_TAC ++-->
   [vREPEAT vGEN_TAC ----> vREWRITE_TAC[sum] ---->
    vREWRITE_TAC[vREAL_ADD_LID; vADD_CLAUSES; vSUB_0] ---->
    vBETA_TAC ----> vREWRITE_TAC[pow] ---->
    vREWRITE_TAC[vREAL_MUL_RID];
    vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[sum] ---->
    vREWRITE_TAC[vADD_CLAUSES] ----> vBETA_TAC ---->
    vREWRITE_TAC[vPOWDIFF_LEMMA] ----> vREWRITE_TAC[vREAL_LDISTRIB] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
      [%q {|a * (b * c) = b * (a * c)|} ]] ---->
    vPOP_ASSUM(fun th -> vONCE_REWRITE_TAC[vGSYM th]) ---->
    vREWRITE_TAC[vSUB_REFL] ---->
    vSPEC_TAC([%q {|SUC n|} ],[%q {|n:num|} ]) ----> vGEN_TAC ---->
    vREWRITE_TAC[pow; vREAL_MUL_RID] ---->
    vREWRITE_TAC[vREAL_LDISTRIB; vREAL_SUB_LDISTRIB] ---->
    vREWRITE_TAC[real_sub] ---->
    vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
      [%q {|(a + b) + (c + d) = (d + a) + (c + b)|} ]] ---->
    vGEN_REWRITE_TAC (funpow 2 vLAND_CONV) [vREAL_MUL_SYM] ---->
    vCONV_TAC vSYM_CONV ----> vREWRITE_TAC[vREAL_ADD_LID_UNIQ] ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vREAL_MUL_SYM] ---->
    vREWRITE_TAC[vREAL_ADD_LINV]]);;

let%a vPOWREV = prove(
  [%q {|!n x y. sum(0,SUC n)(\p. (x pow p) * (y pow (n - p))) =
                sum(0,SUC n)(\p. (x pow (n - p)) * (y pow p))|} ],
  let vREAL_EQ_LMUL2' = vCONV_RULE(vREDEPTH_CONV vFORALL_IMP_CONV) vREAL_EQ_LMUL2 in
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|x:real = y|} ] ++-->
   [vASM_REWRITE_TAC[vGSYM vPOW_ADD] ---->
    vMATCH_MP_TAC vSUM_SUBST ----> vX_GEN_TAC [%q {|p:num|} ] ---->
    vBETA_TAC ----> vDISCH_TAC ----> vAP_TERM_TAC ---->
    vMATCH_ACCEPT_TAC vADD_SYM;
    vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vREAL_MUL_SYM] ---->
    vRULE_ASSUM_TAC(vONCE_REWRITE_RULE[vGSYM vREAL_SUB_0]) ---->
    vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vI [vMATCH_MP vREAL_EQ_LMUL2' th]) ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_NEG_NEG] ---->
    vONCE_REWRITE_TAC[vREAL_NEG_LMUL] ---->
    vONCE_REWRITE_TAC[vREAL_NEG_SUB] ---->
    vREWRITE_TAC[vGSYM vPOWDIFF] ----> vREWRITE_TAC[vREAL_NEG_SUB]]);;

(* ------------------------------------------------------------------------ *)
(* Show (essentially) that a power series has a "circle" of convergence,    *)
(* i.e. if it sums for x, then it sums absolutely for z with |z| < |x|.     *)
(* ------------------------------------------------------------------------ *)

let%a vPOWSER_INSIDEA = prove(
  [%q {|!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. abs(f(n)) * (z pow n))|} ],
  let th = (vGEN_ALL -| vCONV_RULE vLEFT_IMP_EXISTS_CONV -| snd -|
              vEQ_IMP_RULE -| vSPEC_ALL) convergent in
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_ZERO) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP th) ----> vREWRITE_TAC[vGSYM vSEQ_CAUCHY] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSEQ_CBOUNDED) ---->
  vREWRITE_TAC[vSEQ_BOUNDED] ----> vBETA_TAC ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|K:real|} ]) ----> vMATCH_MP_TAC vSER_COMPAR ---->
  vEXISTS_TAC [%q {|\n. (K * abs(z pow n)) / abs(x pow n)|} ] ----> vCONJ_TAC ++-->
   [vEXISTS_TAC [%q {|0|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_THEN(vK vALL_TAC) ---->
    vBETA_TAC ----> vMATCH_MP_TAC vREAL_LE_RDIV ----> vCONJ_TAC ++-->
     [vREWRITE_TAC[vGSYM vABS_NZ] ----> vMATCH_MP_TAC vPOW_NZ ---->
      vREWRITE_TAC[vABS_NZ] ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
      vEXISTS_TAC [%q {|abs(z)|} ] ----> vASM_REWRITE_TAC[vABS_POS];
      vREWRITE_TAC[vABS_MUL; vABS_ABS; vGSYM vREAL_MUL_ASSOC] ---->
      vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
       [%q {|a * b * c = (a * c) * b|} ]] ---->
      vDISJ_CASES_TAC(vSPEC [%q {|z pow n|} ] vABS_CASES) ---->
      vASM_REWRITE_TAC[vABS_0; vREAL_MUL_RZERO; vREAL_LE_REFL] ---->
      vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_LE_RMUL_EQ th]) ---->
      vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[vGSYM vABS_MUL]];
    vREWRITE_TAC[summable] ---->
    vEXISTS_TAC [%q {|K * inv(&1 - (abs(z) / abs(x)))|} ] ---->
    vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ----> vREWRITE_TAC[] ---->
    vMATCH_MP_TAC vSER_CMUL ---->
    vGEN_REWRITE_TAC (vRATOR_CONV -| vONCE_DEPTH_CONV) [vGSYM real_div] ---->
    vSUBGOAL_THEN [%q {|!n. abs(z pow n) / abs(x pow n) =
                        (abs(z) / abs(x)) pow n|} ]
    (fun th -> vONCE_REWRITE_TAC[th]) ++-->
     [vALL_TAC; vREWRITE_TAC[vGSYM real_div] ---->
      vMATCH_MP_TAC vGP ----> vREWRITE_TAC[real_div; vABS_MUL] ---->
      vSUBGOAL_THEN [%q {|~(abs(x) = &0)|} ] (vSUBST1_TAC -| vMATCH_MP vABS_INV) ++-->
       [vDISCH_THEN vSUBST_ALL_TAC ----> vUNDISCH_TAC [%q {|abs(z) < &0|} ] ---->
        vREWRITE_TAC[vREAL_NOT_LT; vABS_POS];
        vREWRITE_TAC[vABS_ABS; vGSYM real_div] ---->
        vMATCH_MP_TAC vREAL_LT_1 ----> vASM_REWRITE_TAC[vABS_POS]]] ---->
    vREWRITE_TAC[vGSYM vPOW_ABS] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
    vREWRITE_TAC[real_div; vPOW_MUL] ----> vAP_TERM_TAC ---->
    vMATCH_MP_TAC vPOW_INV ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|abs(z)|} ] ---->
    vASM_REWRITE_TAC[vABS_POS]]);;

(* ------------------------------------------------------------------------ *)
(* Weaker but more commonly useful form for non-absolute convergence        *)
(* ------------------------------------------------------------------------ *)

let%a vPOWSER_INSIDE = prove(
  [%q {|!f x z. summable (\n. f(n) * (x pow n)) /\ abs(z) < abs(x)
        ==> summable (\n. f(n) * (z pow n))|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPEC [%q {|z:real|} ] vABS_ABS)) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vPOWSER_INSIDEA) ---->
  vREWRITE_TAC[vPOW_ABS; vGSYM vABS_MUL] ---->
  vDISCH_THEN((---->) (vMATCH_MP_TAC vSER_ACONV) -| vMP_TAC) ---->
  vBETA_TAC ----> vDISCH_THEN vACCEPT_TAC);;

(* ------------------------------------------------------------------------ *)
(* Define formal differentiation of power series                            *)
(* ------------------------------------------------------------------------ *)

let diffs = new_definition
  [%q {|diffs c = (\n. &(SUC n) * c(SUC n))|} ];;

(* ------------------------------------------------------------------------ *)
(* Lemma about distributing negation over it                                *)
(* ------------------------------------------------------------------------ *)

let%a vDIFFS_NEG = prove(
  [%q {|!c. diffs(\n. --(c n)) = \n. --((diffs c) n)|} ],
  vGEN_TAC ----> vREWRITE_TAC[diffs] ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_NEG_RMUL]);;

(* ------------------------------------------------------------------------ *)
(* Show that we can shift the terms down one                                *)
(* ------------------------------------------------------------------------ *)

let%a vDIFFS_LEMMA = prove(
  [%q {|!n c x. sum(0,n) (\n. (diffs c)(n) * (x pow n)) =
           sum(0,n) (\n. &n * c(n) * (x pow (n - 1))) +
             (&n * c(n) * x pow (n - 1))|} ],
  vINDUCT_TAC ----> vASM_REWRITE_TAC[sum; vREAL_MUL_LZERO; vREAL_ADD_LID] ---->
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC] ---->
  vAP_TERM_TAC ----> vBETA_TAC ----> vREWRITE_TAC[vADD_CLAUSES] ---->
  vAP_TERM_TAC ----> vREWRITE_TAC[diffs] ----> vBETA_TAC ---->
  vREWRITE_TAC[vSUC_SUB1; vREAL_MUL_ASSOC]);;

let%a vDIFFS_LEMMA2 = prove(
  [%q {|!n c x. sum(0,n) (\n. &n * c(n) * (x pow (n - 1))) =
           sum(0,n) (\n. (diffs c)(n) * (x pow n)) -
                (&n * c(n) * x pow (n - 1))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_EQ_SUB_LADD; vDIFFS_LEMMA]);;

let%a vDIFFS_EQUIV = prove(
  [%q {|!c x. summable(\n. (diffs c)(n) * (x pow n)) ==>
      (\n. &n * c(n) * (x pow (n - 1))) sums
         (suminf(\n. (diffs c)(n) * (x pow n)))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vREWRITE_RULE[diffs] -| vMATCH_MP vSER_ZERO) ---->
  vBETA_TAC ----> vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|(\n. &n * c(n) * (x pow (n - 1))) tends_num_real &0|} ]
  vMP_TAC ++-->
   [vONCE_REWRITE_TAC[vSEQ_SUC] ----> vBETA_TAC ---->
    vASM_REWRITE_TAC[vSUC_SUB1]; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vCONJ (vMATCH_MP vSUMMABLE_SUM
   (vASSUME [%q {|summable(\n. (diffs c)(n) * (x pow n))|} ]))) ---->
  vREWRITE_TAC[sums] ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vSEQ_SUB) ---->
  vBETA_TAC ----> vREWRITE_TAC[vGSYM vDIFFS_LEMMA2] ---->
  vREWRITE_TAC[vREAL_SUB_RZERO]);;

(* ======================================================================== *)
(* Show term-by-term differentiability of power series                      *)
(* (NB we hypothesize convergence of first two derivatives; we could prove  *)
(*  they all have the same radius of convergence, but we don't need to.)    *)
(* ======================================================================== *)

let%a vTERMDIFF_LEMMA1 = prove(
  [%q {|!m z h.
     sum(0,m)(\p. (((z + h) pow (m - p)) * (z pow p)) - (z pow m)) =
       sum(0,m)(\p. (z pow p) *
       (((z + h) pow (m - p)) - (z pow (m - p))))|} ],
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vSUM_SUBST ---->
  vX_GEN_TAC [%q {|p:num|} ] ----> vDISCH_TAC ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_SUB_LDISTRIB; vGSYM vPOW_ADD] ----> vBINOP_TAC ++-->
   [vMATCH_ACCEPT_TAC vREAL_MUL_SYM;
    vAP_TERM_TAC ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
    vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSUB_ADD ---->
    vMATCH_MP_TAC vLT_IMP_LE ---->
    vPOP_ASSUM(vMP_TAC -| vCONJUNCT2) ----> vREWRITE_TAC[vADD_CLAUSES]]);;

let%a vTERMDIFF_LEMMA2 = prove(
  [%q {|!z h. ~(h = &0) ==>
       (((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))) =
        h * sum(0,n - 1)(\p. (z pow p) *
              sum(0,(n - 1) - p)
                (\q. ((z + h) pow q) *
                       (z pow (((n - 2) - p) - q)))))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vI [vMATCH_MP vREAL_EQ_LMUL2 th]) ---->
  vREWRITE_TAC[vREAL_SUB_LDISTRIB] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_DIV_LMUL th]) ---->
  vDISJ_CASES_THEN2 vSUBST1_TAC (vX_CHOOSE_THEN [%q {|m:num|} ] vSUBST1_TAC)
  (vSPEC [%q {|n:num|} ] num_CASES) ++-->
   [vREWRITE_TAC[pow; vREAL_MUL_LZERO; vREAL_MUL_RZERO; vREAL_SUB_REFL] ---->
    vREWRITE_TAC[vSUB_0; sum; vREAL_MUL_RZERO]; vALL_TAC] ---->
  vREWRITE_TAC[vPOWDIFF; vREAL_ADD_SUB] ---->
  vASM_REWRITE_TAC[vGSYM vREAL_SUB_LDISTRIB; vREAL_EQ_LMUL] ---->
  vREWRITE_TAC[vSUC_SUB1] ---->
  vGEN_REWRITE_TAC (vRATOR_CONV -| vONCE_DEPTH_CONV) [vPOWREV] ---->
  vREWRITE_TAC[sum] ----> vREWRITE_TAC[vADD_CLAUSES] ----> vBETA_TAC ---->
  vREWRITE_TAC[vSUB_REFL] ----> vREWRITE_TAC[vREAL; pow] ---->
  vREWRITE_TAC[vREAL_MUL_LID; vREAL_MUL_RID; vREAL_RDISTRIB] ---->
  vREWRITE_TAC[vREAL_ADD2_SUB2; vREAL_SUB_REFL; vREAL_ADD_RID] ---->
  vREWRITE_TAC[vSUM_NSUB] ----> vBETA_TAC ---->
  vREWRITE_TAC[vTERMDIFF_LEMMA1] ---->
  vONCE_REWRITE_TAC[vGSYM vSUM_CMUL] ----> vBETA_TAC ---->
  vMATCH_MP_TAC vSUM_SUBST ----> vX_GEN_TAC [%q {|p:num|} ] ---->
  vREWRITE_TAC[vADD_CLAUSES] ----> vDISCH_TAC ----> vBETA_TAC ---->
  vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vAP_TERM_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vCONJUNCT2) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST_ALL_TAC -| vMATCH_MP vLESS_ADD_1) ---->
  vREWRITE_TAC[vGSYM vADD1] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
  vREWRITE_TAC[vADD_SUB] ----> vREWRITE_TAC[vPOWDIFF; vREAL_ADD_SUB] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vREAL_MUL_SYM] ---->
  vAP_TERM_TAC ----> vMATCH_MP_TAC vSUM_SUBST ----> vX_GEN_TAC [%q {|q:num|} ] ---->
  vREWRITE_TAC[vADD_CLAUSES] ----> vSTRIP_TAC ----> vBETA_TAC ---->
  vAP_TERM_TAC ----> vAP_TERM_TAC ----> vCONV_TAC(vTOP_DEPTH_CONV num_CONV) ---->
  vREWRITE_TAC[vSUB_SUC; vSUB_0; vADD_SUB]);;

let%a vTERMDIFF_LEMMA3 = prove(
  [%q {|!z h n K. ~(h = &0) /\ abs(z) <= K /\ abs(z + h) <= K ==>
    abs(((((z + h) pow n) - (z pow n)) / h) - (&n * (z pow (n - 1))))
        <= &n * &(n - 1) * (K pow (n - 2)) * abs(h)|} ],
  let tac = vW((---->) (vMATCH_MP_TAC vREAL_LE_TRANS) -|
           vEXISTS_TAC -| rand -| concl -| vPART_MATCH (rand -| rator) vABS_SUM -|
           rand -| rator -| snd)  ----> vREWRITE_TAC[vABS_SUM] in
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN vASSUME_TAC) ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vTERMDIFF_LEMMA2 th]) ---->
  vREWRITE_TAC[vABS_MUL] ----> vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
  vFIRST_ASSUM(vASSUME_TAC -| vCONV_RULE(vREWR_CONV vABS_NZ)) ---->
  vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vI [vMATCH_MP vREAL_LE_LMUL_LOCAL th]) ---->
  tac ----> vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
  vMATCH_MP_TAC vSUM_BOUND ----> vX_GEN_TAC [%q {|p:num|} ] ---->
  vREWRITE_TAC[vADD_CLAUSES] ----> vDISCH_THEN vSTRIP_ASSUME_TAC ---->
  vBETA_TAC ----> vREWRITE_TAC[vABS_MUL] ---->
  vDISJ_CASES_THEN2 vSUBST1_TAC (vX_CHOOSE_THEN [%q {|r:num|} ] vSUBST_ALL_TAC)
  (vSPEC [%q {|n:num|} ] num_CASES) ++-->
   [vREWRITE_TAC[vSUB_0; sum; vABS_0; vREAL_MUL_RZERO; vREAL_LE_REFL];
    vALL_TAC] ---->
  vREWRITE_TAC[vSUC_SUB1; num_CONV [%q {|2|} ]; vSUB_SUC] ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vSUC_SUB1]) ---->
  vSUBGOAL_THEN [%q {|p < r:num|} ] vMP_TAC ++-->
   [vFIRST_ASSUM vMATCH_ACCEPT_TAC; vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST_ALL_TAC -| vMATCH_MP vLESS_ADD_1) ---->
  vREWRITE_TAC[vGSYM vADD1] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
  vREWRITE_TAC[vADD_SUB] ----> vREWRITE_TAC[vADD_CLAUSES; vSUC_SUB1; vADD_SUB] ---->
  vREWRITE_TAC[vPOW_ADD] ----> vGEN_REWRITE_TAC vRAND_CONV
   [vAC vREAL_MUL_AC
        [%q {|(a * b) * c = b * (c * a)|} ]] ---->
  vMATCH_MP_TAC vREAL_LE_MUL2V ----> vREWRITE_TAC[vABS_POS] ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vGSYM vPOW_ABS] ----> vMATCH_MP_TAC vPOW_LE ---->
    vASM_REWRITE_TAC[vABS_POS]; vALL_TAC] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|&(SUC d) * (K pow d)|} ] ---->
  vCONJ_TAC ++-->
   [vALL_TAC; vSUBGOAL_THEN [%q {|&0 <= K|} ] vMP_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|abs z|} ] ---->
      vASM_REWRITE_TAC[vABS_POS];
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|d:num|} ] -| vMATCH_MP vPOW_POS) ---->
      vDISCH_THEN(vDISJ_CASES_THEN vMP_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
       [vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_LE_RMUL_EQ th]) ---->
        vREWRITE_TAC[vREAL_LE; vLE_SUC] ---->
        vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC [%q {|SUC d|} ] ---->
        vREWRITE_TAC[vLE_SUC; vLE_ADD] ---->
        vMATCH_MP_TAC vLT_IMP_LE ----> vREWRITE_TAC[vLESS_SUC_REFL];
        vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
        vREWRITE_TAC[vREAL_MUL_RZERO; vREAL_LE_REFL]]]] ---->
  tac ----> vMATCH_MP_TAC vSUM_BOUND ----> vX_GEN_TAC [%q {|q:num|} ] ---->
  vREWRITE_TAC[vADD_CLAUSES] ----> vSTRIP_TAC ----> vBETA_TAC ---->
  vUNDISCH_TAC [%q {|q < (SUC d)|} ] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:num|} ] vMP_TAC -| vMATCH_MP vLESS_ADD_1) ---->
  vREWRITE_TAC[vGSYM vADD1; vADD_CLAUSES; vSUC_INJ] ---->
  vDISCH_THEN vSUBST_ALL_TAC ----> vREWRITE_TAC[vPOW_ADD] ---->
  vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB] ---->
  vREWRITE_TAC[vABS_MUL] ----> vMATCH_MP_TAC vREAL_LE_MUL2V ---->
  vREWRITE_TAC[vABS_POS; vGSYM vPOW_ABS] ---->
  vCONJ_TAC ----> vMATCH_MP_TAC vPOW_LE ----> vASM_REWRITE_TAC[vABS_POS]);;

let%a vTERMDIFF_LEMMA4 = prove(
  [%q {|!f K k. &0 < k /\
           (!h. &0 < abs(h) /\ abs(h) < k ==> abs(f h) <= K * abs(h))
        ==> (f tends_real_real &0)(&0)|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vREWRITE_TAC[vLIM; vREAL_SUB_RZERO] ---->
  vSUBGOAL_THEN [%q {|&0 <= K|} ] vMP_TAC ++-->
   [vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|k / &2|} ]) ---->
    vMP_TAC(vONCE_REWRITE_RULE[vGSYM vREAL_LT_HALF1] (vASSUME [%q {|&0 < k|} ])) ---->
    vDISCH_THEN(fun th -> vASSUME_TAC th ----> vMP_TAC th) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
    vDISCH_THEN(fun th -> vREWRITE_TAC[th; real_abs]) ---->
    vREWRITE_TAC[vGSYM real_abs] ---->
    vASM_REWRITE_TAC[vREAL_LT_HALF1; vREAL_LT_HALF2] ----> vDISCH_TAC ---->
    vMP_TAC(vGEN_ALL(vMATCH_MP vREAL_LE_RMUL_EQ (vASSUME [%q {|&0 < k / &2|} ]))) ---->
    vDISCH_THEN(fun th -> vGEN_REWRITE_TAC vI [vGSYM th]) ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|abs(f(k / &2))|} ] ---->
    vASM_REWRITE_TAC[vREAL_MUL_LZERO; vABS_POS]; vALL_TAC] ---->
  vDISCH_THEN(vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ++-->
   [vALL_TAC; vEXISTS_TAC [%q {|k:real|} ] ----> vREWRITE_TAC[vASSUME [%q {|&0 < k|} ]] ---->
    vGEN_TAC ----> vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vREAL_MUL_LZERO] ---->
    vDISCH_THEN(vMP_TAC -| vC vCONJ(vSPEC [%q {|(f:real->real) x|} ] vABS_POS)) ---->
    vREWRITE_TAC[vREAL_LE_ANTISYM] ----> vDISCH_THEN vSUBST1_TAC ---->
    vFIRST_ASSUM vACCEPT_TAC] ---->
  vSUBGOAL_THEN [%q {|&0 < (e / K) / &2|} ] vASSUME_TAC ++-->
   [vREWRITE_TAC[real_div] ---->
    vREPEAT(vMATCH_MP_TAC vREAL_LT_MUL ----> vCONJ_TAC) ---->
    vTRY(vMATCH_MP_TAC vREAL_INV_POS) ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vREAL_LT; num_CONV [%q {|2|} ]; vLT_0]; vALL_TAC] ---->
  vMP_TAC(vSPECL [[%q {|(e / K) / &2|} ]; [%q {|k:real|} ]] vREAL_DOWN2) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|h:real|} ] ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|K * abs(h)|} ] ----> vCONJ_TAC ++-->
   [vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|d:real|} ] ---->
    vASM_REWRITE_TAC[];
    vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|K * d|} ] ---->
    vASM_REWRITE_TAC[vMATCH_MP vREAL_LT_LMUL_EQ (vASSUME [%q {|&0 < K|} ])] ---->
    vONCE_REWRITE_TAC[vGSYM(vMATCH_MP vREAL_LT_RDIV (vASSUME [%q {|&0 < K|} ]))] ---->
    vREWRITE_TAC[real_div] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
      [%q {|(a * b) * c = (c * a) * b|} ]] ---->
    vASSUME_TAC(vGSYM(vMATCH_MP vREAL_LT_IMP_NE (vASSUME [%q {|&0 < K|} ]))) ---->
    vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV (vASSUME [%q {|~(K = &0)|} ])] ---->
    vREWRITE_TAC[vREAL_MUL_LID] ---->
    vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|(e / K) / &2|} ] ---->
    vASM_REWRITE_TAC[vGSYM real_div] ----> vREWRITE_TAC[vREAL_LT_HALF2] ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_LT_HALF1] ----> vASM_REWRITE_TAC[]]);;

let%a vTERMDIFF_LEMMA5 = prove(
  [%q {|!f g k. &0 < k /\
         summable(f) /\
         (!h. &0 < abs(h) /\ abs(h) < k ==> !n. abs(g(h) n) <= (f(n) * abs(h)))
             ==> ((\h. suminf(g h)) tends_real_real &0)(&0)|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vASSUME_TAC -| vMATCH_MP vSUMMABLE_SUM) vMP_TAC) ---->
  vASSUME_TAC((vGEN [%q {|h:real|} ] -| vSPEC [%q {|abs(h)|} ] -|
    vMATCH_MP vSER_CMUL) (vASSUME [%q {|f sums (suminf f)|} ])) ---->
  vRULE_ASSUM_TAC(vONCE_REWRITE_RULE[vREAL_MUL_SYM]) ---->
  vFIRST_ASSUM(vASSUME_TAC -| vGEN [%q {|h:real|} ] -|
    vMATCH_MP vSUM_UNIQ -| vSPEC [%q {|h:real|} ]) ----> vDISCH_TAC ---->
  vC vSUBGOAL_THEN vASSUME_TAC [%q {|!h. &0 < abs(h) /\ abs(h) < k ==>
    abs(suminf(g h)) <= (suminf(f) * abs(h))|} ] ++-->
   [vGEN_TAC ----> vDISCH_THEN(fun th -> vASSUME_TAC th ---->
      vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ----> vDISCH_TAC ---->
    vSUBGOAL_THEN [%q {|summable(\n. f(n) * abs(h))|} ] vASSUME_TAC ++-->
     [vMATCH_MP_TAC vSUM_SUMMABLE ---->
      vEXISTS_TAC [%q {|suminf(f) * abs(h)|} ] ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|summable(\n. abs(g(h:real)(n:num)))|} ] vASSUME_TAC ++-->
     [vMATCH_MP_TAC vSER_COMPAR ---->
      vEXISTS_TAC [%q {|\n:num. f(n) * abs(h)|} ] ----> vASM_REWRITE_TAC[] ---->
      vEXISTS_TAC [%q {|0|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
      vDISCH_THEN(vK vALL_TAC) ----> vBETA_TAC ----> vREWRITE_TAC[vABS_ABS] ---->
      vFIRST_ASSUM(vMATCH_MP_TAC -| vREWRITE_RULE[vRIGHT_IMP_FORALL_THM]) ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ---->
    vEXISTS_TAC [%q {|suminf(\n. abs(g(h:real)(n:num)))|} ] ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vSER_ABS ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vSER_LE ---->
    vREPEAT vCONJ_TAC ----> vTRY(vFIRST_ASSUM vACCEPT_TAC) ---->
    vGEN_TAC ----> vBETA_TAC ---->
    vFIRST_ASSUM(vMATCH_MP_TAC -| vREWRITE_RULE[vRIGHT_IMP_FORALL_THM]) ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vMATCH_MP_TAC vTERMDIFF_LEMMA4 ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|suminf(f)|} ]; [%q {|k:real|} ]] ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[]);;

let%a vTERMDIFF = prove(
  [%q {|!c K. summable(\n. c(n) * (K pow n)) /\
         summable(\n. (diffs c)(n) * (K pow n)) /\
         summable(\n. (diffs(diffs c))(n) * (K pow n)) /\
         abs(x) < abs(K)
        ==> ((\x. suminf (\n. c(n) * (x pow n))) diffl
             (suminf (\n. (diffs c)(n) * (x pow n))))(x)|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vREWRITE_TAC[diffl] ----> vBETA_TAC ---->
  vMATCH_MP_TAC vLIM_TRANSFORM ---->
  vEXISTS_TAC [%q {|\h. suminf(\n. ((c(n) * ((x + h) pow n)) -
                             (c(n) * (x pow n))) / h)|} ] ----> vCONJ_TAC ++-->
   [vBETA_TAC ----> vREWRITE_TAC[vLIM] ----> vBETA_TAC ---->
    vREWRITE_TAC[vREAL_SUB_RZERO] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
    vEXISTS_TAC [%q {|abs(K) - abs(x)|} ] ----> vREWRITE_TAC[vREAL_SUB_LT] ---->
    vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|h:real|} ] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vABS_CIRCLE) ---->
    vW(fun (asl,w) -> vSUBGOAL_THEN (mk_eq(rand(rator w),[%q {|&0|} ])) vSUBST1_TAC) ---->
    vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vABS_ZERO] ---->
    vREWRITE_TAC[vREAL_SUB_0] ----> vC vSUBGOAL_THEN vMP_TAC
      [%q {|(\n. (c n) * (x pow n)) sums
           (suminf(\n. (c n) * (x pow n))) /\
       (\n. (c n) * ((x + h) pow n)) sums
           (suminf(\n. (c n) * ((x + h) pow n)))|} ] ++-->
     [vCONJ_TAC ----> vMATCH_MP_TAC vSUMMABLE_SUM ---->
      vMATCH_MP_TAC vPOWSER_INSIDE ----> vEXISTS_TAC [%q {|K:real|} ] ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vONCE_REWRITE_TAC[vCONJ_SYM] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_SUB) ----> vBETA_TAC ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|h:real|} ] -| vMATCH_MP vSER_CDIV) ---->
    vBETA_TAC ----> vDISCH_THEN(vACCEPT_TAC -| vMATCH_MP vSUM_UNIQ); vALL_TAC] ---->
  vONCE_REWRITE_TAC[vLIM_NULL] ----> vBETA_TAC ---->
  vMATCH_MP_TAC vLIM_TRANSFORM ----> vEXISTS_TAC
   [%q {|\h. suminf (\n. c(n) *
    (((((x + h) pow n) - (x pow n)) / h) - (&n * (x pow (n - 1)))))|} ] ---->
  vBETA_TAC ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vLIM] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
    vEXISTS_TAC [%q {|abs(K) - abs(x)|} ] ----> vREWRITE_TAC[vREAL_SUB_LT] ---->
    vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|h:real|} ] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vABS_CIRCLE) ---->
    vW(fun (asl,w) -> vSUBGOAL_THEN (mk_eq(rand(rator w),[%q {|&0|} ])) vSUBST1_TAC) ---->
    vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vREAL_SUB_RZERO; vABS_ZERO] ---->
    vBETA_TAC ----> vREWRITE_TAC[vREAL_SUB_0] ---->
    vSUBGOAL_THEN [%q {|summable(\n. (diffs c)(n) * (x pow n))|} ] vMP_TAC ++-->
     [vMATCH_MP_TAC vPOWSER_INSIDE ----> vEXISTS_TAC [%q {|K:real|} ] ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vDISCH_THEN(fun th -> vASSUME_TAC th ---->
        vMP_TAC (vMATCH_MP vDIFFS_EQUIV th)) ---->
    vDISCH_THEN(fun th -> vSUBST1_TAC (vMATCH_MP vSUM_UNIQ th) ----> vMP_TAC th) ---->
    vRULE_ASSUM_TAC(vREWRITE_RULE[vREAL_SUB_RZERO]) ----> vC vSUBGOAL_THEN vMP_TAC
      [%q {|(\n. (c n) * (x pow n)) sums
           (suminf(\n. (c n) * (x pow n))) /\
       (\n. (c n) * ((x + h) pow n)) sums
           (suminf(\n. (c n) * ((x + h) pow n)))|} ] ++-->
     [vCONJ_TAC ----> vMATCH_MP_TAC vSUMMABLE_SUM ---->
      vMATCH_MP_TAC vPOWSER_INSIDE ----> vEXISTS_TAC [%q {|K:real|} ] ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vONCE_REWRITE_TAC[vCONJ_SYM] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_SUB) ----> vBETA_TAC ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|h:real|} ] -| vMATCH_MP vSER_CDIV) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUMMABLE_SUM -| vMATCH_MP vSUM_SUMMABLE) ---->
    vBETA_TAC ----> vDISCH_THEN(fun th -> vDISCH_THEN (vMP_TAC -|
      vMATCH_MP vSUMMABLE_SUM -| vMATCH_MP vSUM_SUMMABLE) ----> vMP_TAC th) ---->
    vDISCH_THEN(fun th1 -> vDISCH_THEN(fun th2 -> vMP_TAC(vCONJ th1 th2))) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_SUB) ----> vBETA_TAC ---->
    vDISCH_THEN(vSUBST1_TAC -| vMATCH_MP vSUM_UNIQ) ----> vAP_TERM_TAC ---->
    vABS_TAC ----> vREWRITE_TAC[real_div] ---->
    vREWRITE_TAC[vREAL_SUB_LDISTRIB; vREAL_SUB_RDISTRIB] ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_TERM_TAC ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ----> vMATCH_ACCEPT_TAC vREAL_MUL_SYM;
    vALL_TAC] ---->
  vMP_TAC(vSPECL [[%q {|abs(x)|} ]; [%q {|abs(K)|} ]] vREAL_MEAN) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|R:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL
   [[%q {|\n. abs(c n) * &n * &(n - 1) * (R pow (n - 2))|} ];
    [%q {|\h n. c(n) * (((((x + h) pow n) - (x pow n)) / h) -
                     (&n * (x pow (n - 1))))|} ];
    [%q {|R - abs(x)|} ]] vTERMDIFF_LEMMA5) ---->
  vBETA_TAC ----> vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vDISCH_THEN vMATCH_MP_TAC ----> vREPEAT vCONJ_TAC ++-->
   [vASM_REWRITE_TAC[vREAL_SUB_LT];

    vSUBGOAL_THEN [%q {|summable(\n. abs(diffs(diffs c) n) * (R pow n))|} ] vMP_TAC ++-->
     [vMATCH_MP_TAC vPOWSER_INSIDEA ---->
      vEXISTS_TAC [%q {|K:real|} ] ----> vASM_REWRITE_TAC[] ---->
      vSUBGOAL_THEN [%q {|abs(R) = R|} ] (fun th -> vASM_REWRITE_TAC[th]) ---->
      vREWRITE_TAC[vABS_REFL] ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
      vEXISTS_TAC [%q {|abs(x)|} ] ----> vREWRITE_TAC[vABS_POS] ---->
      vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vREWRITE_TAC[diffs] ----> vBETA_TAC ----> vREWRITE_TAC[vABS_MUL] ---->
    vREWRITE_TAC[vABS_N] ----> vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
    vC vSUBGOAL_THEN (fun th -> vONCE_REWRITE_TAC[vGSYM th])
      [%q {|!n. diffs(diffs (\n. abs(c n))) n * (R pow n) =
           &(SUC n) * &(SUC(SUC n)) * abs(c(SUC(SUC n))) * (R pow n)|} ] ++-->
     [vGEN_TAC ----> vREWRITE_TAC[diffs] ----> vBETA_TAC ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC]; vALL_TAC] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFFS_EQUIV) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUM_SUMMABLE) ---->
    vREWRITE_TAC[diffs] ----> vBETA_TAC ----> vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
    vSUBGOAL_THEN [%q {|(\n. &n * &(SUC n) * abs(c(SUC n)) * (R pow (n - 1))) =
           \n. diffs(\m. &(m - 1) * abs(c m) / R) n * (R pow n)|} ]
    vSUBST1_TAC ++-->
     [vREWRITE_TAC[diffs] ----> vBETA_TAC ----> vREWRITE_TAC[vSUC_SUB1] ---->
      vABS_TAC ---->
      vDISJ_CASES_THEN2 (vSUBST1_TAC) (vX_CHOOSE_THEN [%q {|m:num|} ] vSUBST1_TAC)
       (vSPEC [%q {|n:num|} ] num_CASES) ---->
      vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_MUL_RZERO; vSUC_SUB1] ---->
      vREWRITE_TAC[vADD1; vPOW_ADD] ----> vREWRITE_TAC[vGSYM vADD1; vPOW_1] ---->
      vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC; real_div] ---->
      vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
        [%q {|a * b * c * d * e * f = b * a * c * e * d * f|} ]] ---->
      vREPEAT vAP_TERM_TAC ----> vSUBGOAL_THEN [%q {|inv(R) * R = &1|} ] vSUBST1_TAC ++-->
       [vMATCH_MP_TAC vREAL_MUL_LINV ----> vREWRITE_TAC[vABS_NZ] ---->
        vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|abs(x)|} ] ---->
        vASM_REWRITE_TAC[vABS_POS] ----> vMATCH_MP_TAC vREAL_LTE_TRANS ---->
        vEXISTS_TAC [%q {|R:real|} ] ----> vASM_REWRITE_TAC[vABS_LE];
        vREWRITE_TAC[vREAL_MUL_RID]]; vALL_TAC] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFFS_EQUIV) ----> vBETA_TAC ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUM_SUMMABLE) ---->
    vMATCH_MP_TAC vEQ_IMP ----> vAP_TERM_TAC ---->
    vCONV_TAC(vX_FUN_EQ_CONV [%q {|n:num|} ]) ----> vBETA_TAC ----> vGEN_TAC ---->
    vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
    vGEN_REWRITE_TAC vRAND_CONV
     [vAC vREAL_MUL_AC
      [%q {|a * b * c * d = b * c * a * d|} ]] ---->
    vDISJ_CASES_THEN2 vSUBST1_TAC (vX_CHOOSE_THEN [%q {|m:num|} ] vSUBST1_TAC)
     (vSPEC [%q {|n:num|} ] num_CASES) ----> vREWRITE_TAC[vREAL_MUL_LZERO] ---->
    vREWRITE_TAC[num_CONV [%q {|2|} ]; vSUC_SUB1; vSUB_SUC] ----> vAP_TERM_TAC ---->
    vDISJ_CASES_THEN2 vSUBST1_TAC (vX_CHOOSE_THEN [%q {|n:num|} ] vSUBST1_TAC)
     (vSPEC [%q {|m:num|} ] num_CASES) ----> vREWRITE_TAC[vREAL_MUL_LZERO] ---->
    vREPEAT vAP_TERM_TAC ----> vREWRITE_TAC[vSUC_SUB1] ---->
    vREWRITE_TAC[vADD1; vPOW_ADD; vPOW_1] ---->
    vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
    vSUBGOAL_THEN [%q {|R * inv(R) = &1|} ]
    (fun th -> vREWRITE_TAC[th; vREAL_MUL_RID]) ---->
    vMATCH_MP_TAC vREAL_MUL_RINV ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|abs(x)|} ] ----> vASM_REWRITE_TAC[vABS_POS];

    vX_GEN_TAC [%q {|h:real|} ] ----> vDISCH_TAC ----> vX_GEN_TAC [%q {|n:num|} ] ---->
    vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vONCE_REWRITE_TAC[vABS_MUL] ---->
    vMATCH_MP_TAC vREAL_LE_LMUL_IMP ----> vREWRITE_TAC[vABS_POS] ---->
    vMATCH_MP_TAC vTERMDIFF_LEMMA3 ----> vASM_REWRITE_TAC[vABS_NZ] ---->
    vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|abs(x) + abs(h)|} ] ---->
      vREWRITE_TAC[vABS_TRIANGLE] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
      vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
      vASM_REWRITE_TAC[vGSYM vREAL_LT_SUB_LADD]]]);;

(* ------------------------------------------------------------------------- *)
(* I eventually decided to get rid of the pointless side-conditions.         *)
(* ------------------------------------------------------------------------- *)

let%a vSEQ_NPOW = prove
 ([%q {|!x. abs(x) < &1 ==> (\n. &n * x pow n) tends_num_real &0|} ],
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|!n. abs(x) / (&1 - abs(x)) < &n <=> &(SUC n) * abs(x) < &n|} ]
  vASSUME_TAC ++-->
   [vASM_SIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_SUB_LT] ---->
    vREWRITE_TAC[vGSYM vREAL_OF_NUM_SUC] ----> vREAL_ARITH_TAC; vALL_TAC] ---->
  vMP_TAC(vSPEC [%q {|abs(x) / (&1 - abs(x))|} ] vREAL_ARCH_SIMPLE) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:num|} ] vSTRIP_ASSUME_TAC) ---->
  vMATCH_MP_TAC vSER_ZERO ----> vMATCH_MP_TAC vSER_RATIO ---->
  vEXISTS_TAC [%q {|&(SUC(SUC N)) * abs(x) / &(SUC N)|} ] ---->
  vEXISTS_TAC [%q {|SUC N|} ] ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[real_div; vREAL_MUL_ASSOC] ----> vREWRITE_TAC[vGSYM real_div] ---->
    vSIMP_TAC[vREAL_MUL_LID;vREAL_LT_LDIV_EQ; vREAL_OF_NUM_LT; vLT_0] ---->
    vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vI [vGSYM th]) ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|&N|} ] ---->
    vASM_REWRITE_TAC[vREAL_OF_NUM_LT; vLT]; vALL_TAC] ---->
  vABBREV_TAC [%q {|m = SUC N|} ] ----> vGEN_TAC ----> vREWRITE_TAC[vGE] ----> vDISCH_TAC ---->
  vREWRITE_TAC[real_div; real_pow; vREAL_ABS_MUL; vGSYM vREAL_MUL_ASSOC] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vAC vREAL_MUL_AC
   [%q {|a * b * c * d * e = ((a * d) * c) * (b * e)|} ]] ---->
  vMATCH_MP_TAC vREAL_LE_RMUL ---->
  vSIMP_TAC[vREAL_ABS_POS; vREAL_LE_MUL] ---->
  vSUBGOAL_THEN [%q {|&0 < &m|} ] vASSUME_TAC ++-->
   [vREWRITE_TAC[vREAL_OF_NUM_LT] ----> vUNDISCH_TAC [%q {|m:num <= n|} ] ---->
    vEXPAND_TAC "m" ----> vARITH_TAC; vALL_TAC] ---->
  vASM_SIMP_TAC[vGSYM real_div; vREAL_LE_RDIV_EQ] ---->
  vUNDISCH_TAC [%q {|m:num <= n|} ] ----> vGEN_REWRITE_TAC vLAND_CONV [vLE_EXISTS] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC) ---->
  vREWRITE_TAC[vREAL_ABS_NUM; vREAL_OF_NUM_MUL; vREAL_OF_NUM_LE] ---->
  vREWRITE_TAC[vADD_CLAUSES; vMULT_CLAUSES] ----> vARITH_TAC);;

let%a vTERMDIFF_CONVERGES = prove
 ([%q {|!K. (!x. abs(x) < K ==> summable(\n. c(n) * x pow n))
       ==> !x. abs(x) < K ==> summable (\n. diffs c n * x pow n)|} ],
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC [%q {|x = &0|} ] ++-->
   [vREWRITE_TAC[summable] ---->
    vEXISTS_TAC [%q {|sum(0,1) (\n. diffs c n * x pow n)|} ] ---->
    vMATCH_MP_TAC vSER_0 ---->
    vASM_REWRITE_TAC[vREAL_ENTIRE; vREAL_POW_EQ_0] ---->
    vSIMP_TAC[vARITH_RULE [%q {|1 <= m <=> ~(m = 0)|} ]]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|?y. abs(x) < abs(y) /\ abs(y) < K|} ] vSTRIP_ASSUME_TAC ++-->
   [vEXISTS_TAC [%q {|(abs(x) + K) / &2|} ] ---->
    vSIMP_TAC[vREAL_ABS_DIV; vREAL_ABS_NUM; vREAL_LT_RDIV_EQ; vREAL_LT_LDIV_EQ;
             vREAL_OF_NUM_LT; vARITH] ---->
    vUNDISCH_TAC [%q {|abs(x) < K|} ] ----> vREAL_ARITH_TAC; vALL_TAC] ---->
  vREWRITE_TAC[diffs] ---->
  vSUBGOAL_THEN [%q {|summable (\n. (&n * c(n)) * x pow n)|} ] vMP_TAC ++-->
   [vALL_TAC;
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|1|} ] -| vMATCH_MP vSER_OFFSET) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|inv(x)|} ] -| vMATCH_MP vSER_CMUL) ---->
    vREWRITE_TAC[vGSYM vADD1; real_pow] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
     [%q {|a * (b * c) * d * e = (a * d) * (b * c) * e|} ]] ---->
    vASM_SIMP_TAC[vREAL_MUL_LINV; vREAL_MUL_LID] ---->
    vREWRITE_TAC[vSUM_SUMMABLE]] ---->
  vMATCH_MP_TAC vSER_COMPAR ----> vEXISTS_TAC [%q {|\n:num. abs(c n * y pow n)|} ] ---->
  vCONJ_TAC ++-->
   [vALL_TAC;
    vREWRITE_TAC[vREAL_ABS_MUL; vREAL_ABS_POW] ---->
    vMATCH_MP_TAC vPOWSER_INSIDEA ---->
    vEXISTS_TAC [%q {|(abs(y) + K) / &2|} ] ---->
    vSUBGOAL_THEN [%q {|abs(abs y) < abs((abs y + K) / &2) /\
                  abs((abs y + K) / &2) < K|} ]
     (fun th -> vASM_SIMP_TAC[th]) ---->
    vSIMP_TAC[vREAL_ABS_DIV; vREAL_ABS_NUM; vREAL_LT_RDIV_EQ; vREAL_LT_LDIV_EQ;
             vREAL_OF_NUM_LT; vARITH] ---->
    vUNDISCH_TAC [%q {|abs y < K|} ] ----> vREAL_ARITH_TAC] ---->
  vSUBGOAL_THEN [%q {|&0 < abs(y)|} ] vASSUME_TAC ++-->
   [vMAP_EVERY vUNDISCH_TAC [[%q {|abs x < abs y|} ]; [%q {|~(x = &0)|} ]] ---->
    vREAL_ARITH_TAC; vALL_TAC] ---->
  vMP_TAC(vSPEC [%q {|x / y|} ] vSEQ_NPOW) ---->
  vASM_SIMP_TAC[vREAL_MUL_LID; vREAL_LT_LDIV_EQ; vREAL_ABS_DIV] ---->
  vREWRITE_TAC[vSEQ] ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|&1|} ]) ---->
  vREWRITE_TAC[vREAL_OF_NUM_LT; vREAL_SUB_RZERO; vARITH] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vGEN_TAC ----> vMATCH_MP_TAC vMONO_FORALL ---->
  vGEN_TAC ----> vMATCH_MP_TAC(vTAUT [%q {|(b ==> c) ==> (a ==> b) ==> (a ==> c)|} ]) ---->
  vREWRITE_TAC[vREAL_ABS_DIV; vREAL_ABS_MUL; vREAL_ABS_POW; vREAL_ABS_NUM] ---->
  vREWRITE_TAC[vREAL_POW_DIV] ---->
  vREWRITE_TAC[real_div; vREAL_MUL_ASSOC; vREAL_POW_INV] ---->
  vREWRITE_TAC[vGSYM real_div] ---->
  vASM_SIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_POW_LT] ---->
  vREWRITE_TAC[vREAL_MUL_LID] ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC vLAND_CONV [vAC vREAL_MUL_AC [%q {|(a * b) * c = b * a * c|} ]] ---->
  vMATCH_MP_TAC vREAL_LE_LMUL ---->
  vASM_SIMP_TAC[vREAL_ABS_POS; vREAL_LT_IMP_LE]);;

let%a vTERMDIFF_STRONG = prove
 ([%q {|!c K x.
        summable(\n. c(n) * (K pow n)) /\ abs(x) < abs(K)
        ==> ((\x. suminf (\n. c(n) * (x pow n))) diffl
             (suminf (\n. (diffs c)(n) * (x pow n))))(x)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vTERMDIFF ---->
  vEXISTS_TAC [%q {|(abs(x) + abs(K)) / &2|} ] ---->
  vSUBGOAL_THEN [%q {|abs(x) < abs((abs(x) + abs(K)) / &2) /\
                abs((abs(x) + abs(K)) / &2) < abs(K)|} ]
  vSTRIP_ASSUME_TAC ++-->
   [vSIMP_TAC[vREAL_ABS_DIV; vREAL_ABS_NUM; vREAL_LT_RDIV_EQ;
             vREAL_LT_LDIV_EQ; vREAL_OF_NUM_LT; vARITH] ---->
    vUNDISCH_TAC [%q {|abs(x) < abs(K)|} ] ----> vREAL_ARITH_TAC; vALL_TAC] ---->
  vASM_REWRITE_TAC[vREAL_ABS_ABS] ----> vREPEAT vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSER_ACONV ---->
    vREWRITE_TAC[vREAL_ABS_MUL; vREAL_ABS_POW] ---->
    vMATCH_MP_TAC vPOWSER_INSIDEA ---->
    vEXISTS_TAC [%q {|K:real|} ] ----> vASM_REWRITE_TAC[vREAL_ABS_ABS];
    vSUBGOAL_THEN
     [%q {|!x. abs(x) < abs(K) ==> summable (\n. diffs c n * x pow n)|} ]
     (fun th -> vASM_SIMP_TAC[th]);
    vSUBGOAL_THEN
     [%q {|!x. abs(x) < abs(K) ==> summable (\n. diffs(diffs c) n * x pow n)|} ]
     (fun th -> vASM_SIMP_TAC[th]) ---->
    vMATCH_MP_TAC vTERMDIFF_CONVERGES] ---->
  vMATCH_MP_TAC vTERMDIFF_CONVERGES ---->
  vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC vSER_ACONV ---->
  vREWRITE_TAC[vREAL_ABS_MUL; vREAL_ABS_POW] ---->
  vMATCH_MP_TAC vPOWSER_INSIDEA ---->
  vEXISTS_TAC [%q {|K:real|} ] ----> vASM_REWRITE_TAC[vREAL_ABS_ABS]);;

(* ------------------------------------------------------------------------- *)
(* Term-by-term comparison of power series.                                  *)
(* ------------------------------------------------------------------------- *)

let%a vPOWSER_0 = prove
 ([%q {|!a. (\n. a n * (&0) pow n) sums a(0)|} ],
  vGEN_TAC ---->
  vSUBGOAL_THEN [%q {|a(0) = sum(0,1) (\n. a n * (&0) pow n)|} ] vSUBST1_TAC ++-->
   [vCONV_TAC(vONCE_DEPTH_CONV vREAL_SUM_CONV) ---->
    vREWRITE_TAC[real_pow; vREAL_MUL_RID]; vALL_TAC] ---->
  vMATCH_MP_TAC vSER_0 ----> vINDUCT_TAC ---->
  vREWRITE_TAC[real_pow; vREAL_MUL_LZERO; vREAL_MUL_RZERO; vARITH]);;

let%a vPOWSER_LIMIT_0 = prove
 ([%q {|!f a s. &0 < s /\
           (!x. abs(x) < s ==> (\n. a n * x pow n) sums (f x))
           ==> (f tends_real_real a(0))(&0)|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|a:num->real|} ]; [%q {|s / &2|} ]; [%q {|&0|} ]] vTERMDIFF_STRONG) ---->
  vW(vC vSUBGOAL_THEN (fun th -> vREWRITE_TAC[th]) -| funpow 2 lhand -| snd) ++-->
   [vASM_SIMP_TAC[vREAL_ABS_NUM; vREAL_ABS_DIV; vREAL_LT_DIV; vREAL_OF_NUM_LT;
                 vARITH; vREAL_ARITH [%q {|&0 < x ==> &0 < abs(x)|} ]] ---->
    vMATCH_MP_TAC vSUM_SUMMABLE ---->
    vEXISTS_TAC [%q {|(f:real->real) (s / &2)|} ] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_SIMP_TAC[vREAL_ABS_DIV; vREAL_ABS_NUM; vREAL_LT_LDIV_EQ; vREAL_OF_NUM_LT;
                 vARITH] ---->
    vUNDISCH_TAC [%q {|&0 < s|} ] ----> vREAL_ARITH_TAC; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_CONT) ----> vREWRITE_TAC[contl] ---->
  vSUBGOAL_THEN [%q {|suminf (\n. a n * &0 pow n) = a(0)|} ] vSUBST1_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSUM_UNIQ ---->
    vREWRITE_TAC[vPOWSER_0]; vALL_TAC] ---->
  vMATCH_MP_TAC(vONCE_REWRITE_RULE[vIMP_CONJ]
               vLIM_TRANSFORM) ---->
  vREWRITE_TAC[vREAL_ADD_LID; vLIM] ---->
  vREPEAT vSTRIP_TAC ----> vEXISTS_TAC [%q {|s:real|} ] ---->
  vASM_REWRITE_TAC[vREAL_SUB_RZERO] ---->
  vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|(a = b) /\ &0 < e ==> abs(a - b) < e|} ]) ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vSUM_UNIQ ----> vASM_SIMP_TAC[]);;

let%a vPOWSER_LIMIT_0_STRONG = prove
 ([%q {|!f a s.
        &0 < s /\
        (!x. &0 < abs(x) /\ abs(x) < s ==> (\n. a n * x pow n) sums (f x))
        ==> (f tends_real_real a(0))(&0)|} ],
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN
   [%q {|((\x. if x = &0 then a(0):real else f x) tends_real_real a(0))(&0)|} ]
  vMP_TAC ++-->
   [vMATCH_MP_TAC vPOWSER_LIMIT_0 ---->
    vEXISTS_TAC [%q {|s:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vX_GEN_TAC [%q {|x:real|} ] ----> vSTRIP_TAC ----> vASM_CASES_TAC [%q {|x = &0|} ] ---->
    vASM_SIMP_TAC[vGSYM vREAL_ABS_NZ] ----> vREWRITE_TAC[sums; vSEQ] ---->
    vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ----> vEXISTS_TAC [%q {|1|} ] ---->
    vINDUCT_TAC ----> vREWRITE_TAC[vARITH; vADD1] ----> vDISCH_TAC ---->
    vREWRITE_TAC[vGSYM(vONCE_REWRITE_RULE[vREAL_EQ_SUB_LADD] vSUM_OFFSET)] ---->
    vREWRITE_TAC[vREAL_POW_ADD; vREAL_POW_1; vREAL_MUL_RZERO; vSUM_CONST] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vREAL_SUM_CONV) ---->
    vREWRITE_TAC[real_pow; vREAL_MUL_RID] ---->
    vASM_REWRITE_TAC[vREAL_ADD_LID; vREAL_SUB_REFL; vREAL_ABS_NUM]; vALL_TAC] ---->
  vMATCH_MP_TAC vEQ_IMP ---->
  vMATCH_MP_TAC vLIM_EQUAL ----> vSIMP_TAC[]);;

let%a vPOWSER_EQUAL_0 = prove
 ([%q {|!f a b P.
        (!e. &0 < e ==> ?x. P x /\ &0 < abs x /\ abs(x) < e) /\
        (!x. &0 < abs(x) /\ P x
             ==> (\n. a n * x pow n) sums (f x) /\
                 (\n. b n * x pow n) sums (f x))
        ==> (a(0) = b(0))|} ],
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN
   [%q {|?s. &0 < s /\
        !x. abs(x) < s
            ==> summable (\n. a n * x pow n) /\ summable (\n. b n * x pow n)|} ]
  vMP_TAC ++-->
   [vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP vREAL_LT_01) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|abs(k)|} ] ----> vASM_REWRITE_TAC[] ---->
    vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vPOWSER_INSIDE ---->
    vEXISTS_TAC [%q {|k:real|} ] ---->
    vASM_REWRITE_TAC[summable] ---->
    vEXISTS_TAC [%q {|(f:real->real) k|} ] ----> vASM_SIMP_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[summable; vLEFT_AND_EXISTS_THM] ---->
  vREWRITE_TAC[vRIGHT_AND_EXISTS_THM; vRIGHT_IMP_EXISTS_THM] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:real|} ] vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vREWRITE_TAC[vSKOLEM_THM] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g:real->real|} ] vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|h:real->real|} ] vMP_TAC) ----> vDISCH_TAC ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|~(&0 < abs(x - y)) ==> (x = y)|} ]) ---->
  vABBREV_TAC [%q {|e = abs(a 0 - b 0)|} ] ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|g:real->real|} ]; [%q {|a:num->real|} ]; [%q {|s:real|} ]]
    vPOWSER_LIMIT_0_STRONG) ---->
  vASM_SIMP_TAC[vLIM] ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH; vREAL_SUB_RZERO] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d1:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|h:real->real|} ]; [%q {|b:num->real|} ]; [%q {|s:real|} ]]
    vPOWSER_LIMIT_0_STRONG) ---->
  vASM_SIMP_TAC[vLIM] ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH; vREAL_SUB_RZERO] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d2:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|d1:real|} ]; [%q {|d2:real|} ]] vREAL_DOWN2) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d0:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|d0:real|} ]; [%q {|s:real|} ]] vREAL_DOWN2) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vUNDISCH_TAC [%q {|!e. &0 < e ==> ?x. P x /\ &0 < abs x /\ abs x < e|} ] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|d:real|} ]) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|abs(a 0 - b 0) < e|} ] vMP_TAC ++-->
   [vALL_TAC; vASM_REWRITE_TAC[vREAL_LT_REFL]] ---->
  vMATCH_MP_TAC vREAL_LTE_TRANS ---->
  vEXISTS_TAC [%q {|e / &2 + e / &2|} ] ----> vCONJ_TAC ++-->
   [vALL_TAC;
    vSIMP_TAC[vGSYM vREAL_MUL_2; vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH_EQ] ---->
    vREWRITE_TAC[vREAL_LE_REFL]] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|!f g h. abs(g - a) < e2 /\ abs(h - b) < e2 /\ (g = f) /\ (h = f)
            ==> abs(a - b) < e2 + e2|} ]) ---->
  vMAP_EVERY vEXISTS_TAC
   [[%q {|(f:real->real) x|} ]; [%q {|(g:real->real) x|} ]; [%q {|(h:real->real) x|} ]] ---->
  vCONJ_TAC ++--> [vASM_MESON_TAC[vREAL_LT_TRANS]; vALL_TAC] ---->
  vCONJ_TAC ++--> [vASM_MESON_TAC[vREAL_LT_TRANS]; vALL_TAC] ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vEQ_TRANS ----> vEXISTS_TAC [%q {|suminf(\n. a n * x pow n)|} ] ---->
    vCONJ_TAC ++-->
     [vMATCH_MP_TAC vSUM_UNIQ;
      vMATCH_MP_TAC(vGSYM vSUM_UNIQ)] ---->
    vASM_SIMP_TAC[] ---->
    vSUBGOAL_THEN [%q {|abs(x) < s|} ] (fun th -> vASM_SIMP_TAC[th]) ---->
    vASM_MESON_TAC[vREAL_LT_TRANS];
    vMATCH_MP_TAC vEQ_TRANS ----> vEXISTS_TAC [%q {|suminf(\n. b n * x pow n)|} ] ---->
    vCONJ_TAC ++-->
     [vMATCH_MP_TAC vSUM_UNIQ;
      vMATCH_MP_TAC(vGSYM vSUM_UNIQ)] ---->
    vASM_SIMP_TAC[] ---->
    vSUBGOAL_THEN [%q {|abs(x) < s|} ] (fun th -> vASM_SIMP_TAC[th]) ---->
    vASM_MESON_TAC[vREAL_LT_TRANS]]);;

let%a vPOWSER_EQUAL = prove
 ([%q {|!f a b P.
        (!e. &0 < e ==> ?x. P x /\ &0 < abs x /\ abs(x) < e) /\
        (!x. P x ==> (\n. a n * x pow n) sums (f x) /\
                     (\n. b n * x pow n) sums (f x))
        ==> (a = b)|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vFUN_EQ_THM] ---->
  vGEN_REWRITE_TAC vI [vTAUT [%q {|p <=> ~ ~ p|} ]] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vNOT_FORALL_THM] ---->
  vONCE_REWRITE_TAC[num_WOP] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:num|} ] vMP_TAC) ----> vREWRITE_TAC[] ---->
  vREWRITE_TAC[vTAUT [%q {|~(~a /\ b) <=> b ==> a|} ]] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|(\m. a(m + n):real) 0 = (\m. b(m + n)) 0|} ] vMP_TAC ++-->
   [vALL_TAC; vREWRITE_TAC[vADD_CLAUSES]] ---->
  vMATCH_MP_TAC vPOWSER_EQUAL_0 ---->
  vEXISTS_TAC [%q {|\x. inv(x pow n) * (f(x) - sum(0,n) (\n. b n * x pow n))|} ] ---->
  vEXISTS_TAC [%q {|P:real->bool|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|x:real|} ] ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|!a m. a(m + n) * x pow m =
                      inv(x pow n) * a(m + n) * x pow (m + n)|} ]
   (fun th -> vGEN_REWRITE_TAC (vBINOP_CONV -| vLAND_CONV -| vONCE_DEPTH_CONV) [th])
  ++-->
   [vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_POW_ADD] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC [%q {|x' * a * b * x = (x * x') * a * b|} ]] ---->
    vASM_SIMP_TAC[vREAL_MUL_RINV; vREAL_POW_EQ_0;
                 vREAL_ARITH [%q {|(x = &0) <=> ~(&0 < abs x)|} ]] ---->
    vREWRITE_TAC[vREAL_MUL_LID]; vALL_TAC] ---->
  vCONJ_TAC ----> vMATCH_MP_TAC vSER_CMUL ++-->
   [vSUBGOAL_THEN [%q {|sum(0,n) (\n. b n * x pow n) = sum(0,n) (\n. a n * x pow n)|} ]
    vSUBST1_TAC ++-->
     [vMATCH_MP_TAC vSUM_EQ ----> vASM_SIMP_TAC[vADD_CLAUSES]; vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|f x = suminf (\n. a n * x pow n)|} ] vSUBST1_TAC ++-->
     [vMATCH_MP_TAC vSUM_UNIQ ----> vASM_SIMP_TAC[]; vALL_TAC] ---->
    vMP_TAC(vSPEC [%q {|\n. a n * x pow n|} ] vSER_OFFSET);
    vSUBGOAL_THEN [%q {|f x = suminf (\n. b n * x pow n)|} ] vSUBST1_TAC ++-->
     [vMATCH_MP_TAC vSUM_UNIQ ----> vASM_SIMP_TAC[]; vALL_TAC] ---->
    vMP_TAC(vSPEC [%q {|\n. b n * x pow n|} ] vSER_OFFSET)] ---->
  vREWRITE_TAC[] ---->
  vW(vC vSUBGOAL_THEN (fun th -> vSIMP_TAC[th]) -| funpow 2 lhand -| snd) ---->
  vMATCH_MP_TAC vSUM_SUMMABLE ---->
  vEXISTS_TAC [%q {|(f:real->real) x|} ] ----> vASM_SIMP_TAC[]);;

(* ======================================================================== *)
(* Definitions of the transcendental functions etc.                         *)
(* ======================================================================== *)

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* To avoid all those beta redexes vanishing without trace...                *)
(* ------------------------------------------------------------------------- *)

set_basic_rewrites (subtract' equals_thm (basic_rewrites())
   [vSPEC_ALL vBETA_THM]);;

(* ------------------------------------------------------------------------ *)
(* Some miscellaneous lemmas                                                *)
(* ------------------------------------------------------------------------ *)

let%a vMULT_DIV_2 = prove
 ([%q {|!n. (2 * n) DIV 2 = n|} ],
  vGEN_TAC ----> vMATCH_MP_TAC vDIV_MULT ---->
  vREWRITE_TAC[vARITH]);;

let%a vEVEN_DIV2 = prove
 ([%q {|!n. ~(EVEN n) ==> ((SUC n) DIV 2 = SUC((n - 1) DIV 2))|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vNOT_ODD; vODD_EXISTS] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:num|} ] vSUBST1_TAC) ---->
  vREWRITE_TAC[vSUC_SUB1] ----> vREWRITE_TAC[vADD1; vGSYM vADD_ASSOC] ---->
  vSUBST1_TAC(vEQT_ELIM(vNUM_REDUCE_CONV [%q {|1 + 1 = 2 * 1|} ])) ---->
  vREWRITE_TAC[vGSYM vLEFT_ADD_DISTRIB; vMULT_DIV_2]);;

(* ------------------------------------------------------------------------ *)
(* Now set up real numbers interface                                        *)
(* ------------------------------------------------------------------------ *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Another lost lemma.                                                       *)
(* ------------------------------------------------------------------------- *)

let%a vPOW_ZERO = prove(
  [%q {|!n x. (x pow n = &0) ==> (x = &0)|} ],
  vINDUCT_TAC ----> vGEN_TAC ----> vONCE_REWRITE_TAC[pow] ---->
  vREWRITE_TAC[vREAL_10; vREAL_ENTIRE] ---->
  vDISCH_THEN(vDISJ_CASES_THEN2 vACCEPT_TAC vASSUME_TAC) ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vFIRST_ASSUM vACCEPT_TAC);;

let%a vPOW_ZERO_EQ = prove(
  [%q {|!n x. (x pow (SUC n) = &0) <=> (x = &0)|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vPOW_ZERO] ---->
  vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vPOW_0]);;

let%a vPOW_LT = prove(
  [%q {|!n x y. &0 <= x /\ x < y ==> (x pow (SUC n)) < (y pow (SUC n))|} ],
  vREPEAT vSTRIP_TAC ----> vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vINDUCT_TAC ++-->
   [vASM_REWRITE_TAC[pow; vREAL_MUL_RID];
    vONCE_REWRITE_TAC[pow] ----> vMATCH_MP_TAC vREAL_LT_MUL2_ALT ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vPOW_POS ----> vASM_REWRITE_TAC[]]);;

let%a vPOW_EQ = prove(
  [%q {|!n x y. &0 <= x /\ &0 <= y /\ (x pow (SUC n) = y pow (SUC n))
        ==> (x = y)|} ],
  vREPEAT vSTRIP_TAC ----> vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC
    (vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vREAL_LT_TOTAL) ---->
  vASM_REWRITE_TAC[] ---->
  vUNDISCH_TAC [%q {|x pow (SUC n) = y pow (SUC n)|} ] ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_THEN(vK vALL_TAC) ++-->
   [vALL_TAC; vCONV_TAC(vRAND_CONV vSYM_CONV)] ---->
  vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
  vMATCH_MP_TAC vPOW_LT ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Basic differentiation theorems --- none yet.                              *)
(* ------------------------------------------------------------------------- *)

let diff_net = ref empty_net;;

let add_to_diff_net th =
  let t = lhand(rator(rand(concl th))) in
  let net = !diff_net in
  let net' = enter [] (t,vPART_MATCH (lhand -| rator -| rand) th) net in
  diff_net := net';;

(* ------------------------------------------------------------------------ *)
(* The three functions we define by series are exp, sin, cos                *)
(* ------------------------------------------------------------------------ *)

let exp = new_definition
  [%q {|exp(x) = suminf(\n. ((\n. inv(&(FACT n)))) n * (x pow n))|} ];;

let sin = new_definition
  [%q {|sin(x) = suminf(\n. ((\n. if EVEN n then &0 else
      ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n))|} ];;

let cos = new_definition
  [%q {|cos(x) = suminf(\n. ((\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n)
       else &0)) n * (x pow n))|} ];;

(* ------------------------------------------------------------------------ *)
(* Show the series for exp converges, using the ratio test                  *)
(* ------------------------------------------------------------------------ *)

let%a vREAL_EXP_CONVERGES = prove(
  [%q {|!x. (\n. ((\n. inv(&(FACT n)))) n * (x pow n)) sums exp(x)|} ],
  let fnz tm =
    (vGSYM -| vMATCH_MP vREAL_LT_IMP_NE -|
     vREWRITE_RULE[vGSYM vREAL_LT] -| vC vSPEC vFACT_LT) tm in
  vGEN_TAC ----> vREWRITE_TAC[exp] ----> vMATCH_MP_TAC vSUMMABLE_SUM ---->
  vMATCH_MP_TAC vSER_RATIO ---->
  vMP_TAC (vSPEC [%q {|&1|} ] vREAL_DOWN) ----> vREWRITE_TAC[vREAL_LT_01] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|c:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|c:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vMP_TAC(vSPEC [%q {|c:real|} ] vREAL_ARCH) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|abs(x)|} ]) ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|N:num|} ]) ----> vEXISTS_TAC [%q {|N:num|} ] ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vGE] ----> vDISCH_TAC ---->
  vBETA_TAC ---->
  vREWRITE_TAC[vADD1; vPOW_ADD; vABS_MUL; vREAL_MUL_ASSOC; vPOW_1] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vMATCH_MP_TAC vREAL_LE_RMUL_IMP ---->
  vREWRITE_TAC[vABS_POS] ----> vREWRITE_TAC[vGSYM vADD1; vFACT] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL; vMATCH_MP vREAL_INV_MUL_WEAK (vCONJ
   (vREWRITE_RULE[vGSYM vREAL_INJ] (vSPEC [%q {|n:num|} ] vNOT_SUC)) (fnz [%q {|n:num|} ]))] ---->
  vREWRITE_TAC[vABS_MUL; vREAL_MUL_ASSOC] ---->
  vMATCH_MP_TAC vREAL_LE_RMUL_IMP ----> vREWRITE_TAC[vABS_POS] ---->
  vMP_TAC(vSPEC [%q {|n:num|} ] vLT_0) ----> vREWRITE_TAC[vGSYM vREAL_LT] ---->
  vDISCH_THEN(vASSUME_TAC -| vGSYM -| vMATCH_MP vREAL_LT_IMP_NE) ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vABS_INV th]) ---->
  vREWRITE_TAC[vGSYM real_div] ----> vMATCH_MP_TAC vREAL_LE_LDIV ---->
  vASM_REWRITE_TAC[vGSYM vABS_NZ] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vREWRITE_RULE[vGSYM vABS_REFL; vGSYM vREAL_LE] vLE_0] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|&N * c|} ] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vFIRST_ASSUM vACCEPT_TAC;
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_LE_RMUL_EQ th]) ---->
    vREWRITE_TAC[vREAL_LE] ----> vMATCH_MP_TAC vLE_TRANS ---->
    vEXISTS_TAC [%q {|n:num|} ] ----> vASM_REWRITE_TAC[vLESS_EQ_SUC_REFL]]);;

(* ------------------------------------------------------------------------ *)
(* Show by the comparison test that sin and cos converge                    *)
(* ------------------------------------------------------------------------ *)

let%a vSIN_CONVERGES = prove(
  [%q {|!x. (\n. ((\n. if EVEN n then &0 else
  ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n)) sums
  sin(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[sin] ----> vMATCH_MP_TAC vSUMMABLE_SUM ---->
  vMATCH_MP_TAC vSER_COMPAR ---->
  vEXISTS_TAC [%q {|\n. ((\n. inv(&(FACT n)))) n * (abs(x) pow n)|} ] ---->
  vREWRITE_TAC[vMATCH_MP vSUM_SUMMABLE (vSPEC_ALL vREAL_EXP_CONVERGES)] ---->
  vEXISTS_TAC [%q {|0|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
  vDISCH_THEN(vK vALL_TAC) ----> vBETA_TAC ----> vCOND_CASES_TAC ---->
  vREWRITE_TAC[vABS_MUL; vPOW_ABS] ++-->
   [vREWRITE_TAC[vABS_0; vREAL_MUL_LZERO] ----> vMATCH_MP_TAC vREAL_LE_MUL ---->
    vREWRITE_TAC[vABS_POS];
    vREWRITE_TAC[real_div; vABS_MUL; vPOW_M1; vREAL_MUL_LID] ---->
    vMATCH_MP_TAC vREAL_LE_RMUL_IMP ----> vREWRITE_TAC[vABS_POS] ---->
    vMATCH_MP_TAC vREAL_EQ_IMP_LE ----> vREWRITE_TAC[vABS_REFL]] ---->
  vMAP_EVERY vMATCH_MP_TAC [vREAL_LT_IMP_LE; vREAL_INV_POS] ---->
  vREWRITE_TAC[vREAL_LT; vFACT_LT]);;

let%a vCOS_CONVERGES = prove(
  [%q {|!x. (\n. ((\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n) else &0)) n
    * (x pow n)) sums cos(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[cos] ----> vMATCH_MP_TAC vSUMMABLE_SUM ---->
  vMATCH_MP_TAC vSER_COMPAR ---->
  vEXISTS_TAC [%q {|\n. ((\n. inv(&(FACT n)))) n * (abs(x) pow n)|} ] ---->
  vREWRITE_TAC[vMATCH_MP vSUM_SUMMABLE (vSPEC_ALL vREAL_EXP_CONVERGES)] ---->
  vEXISTS_TAC [%q {|0|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
  vDISCH_THEN(vK vALL_TAC) ----> vBETA_TAC ----> vCOND_CASES_TAC ---->
  vREWRITE_TAC[vABS_MUL; vPOW_ABS] ++-->
   [vREWRITE_TAC[real_div; vABS_MUL; vPOW_M1; vREAL_MUL_LID] ---->
    vMATCH_MP_TAC vREAL_LE_RMUL_IMP ----> vREWRITE_TAC[vABS_POS] ---->
    vMATCH_MP_TAC vREAL_EQ_IMP_LE ----> vREWRITE_TAC[vABS_REFL];
    vREWRITE_TAC[vABS_0; vREAL_MUL_LZERO] ----> vMATCH_MP_TAC vREAL_LE_MUL ---->
    vREWRITE_TAC[vABS_POS]] ---->
  vMAP_EVERY vMATCH_MP_TAC [vREAL_LT_IMP_LE; vREAL_INV_POS] ---->
  vREWRITE_TAC[vREAL_LT; vFACT_LT]);;

(* ------------------------------------------------------------------------ *)
(* Show what the formal derivatives of these series are                     *)
(* ------------------------------------------------------------------------ *)

let%a vREAL_EXP_FDIFF = prove(
  [%q {|diffs (\n. inv(&(FACT n))) = (\n. inv(&(FACT n)))|} ],
  vREWRITE_TAC[diffs] ----> vBETA_TAC ---->
  vCONV_TAC(vX_FUN_EQ_CONV [%q {|n:num|} ]) ----> vGEN_TAC ----> vBETA_TAC ---->
  vREWRITE_TAC[vFACT; vGSYM vREAL_MUL] ---->
  vSUBGOAL_THEN [%q {|~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)|} ] vASSUME_TAC ++-->
   [vCONJ_TAC ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
    vREWRITE_TAC[vREAL_LT; vLT_0; vFACT_LT];
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_INV_MUL_WEAK th]) ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC; vREAL_EQ_RMUL] ----> vDISJ2_TAC ---->
    vMATCH_MP_TAC vREAL_MUL_RINV ----> vASM_REWRITE_TAC[]]);;

let%a vSIN_FDIFF = prove(
  [%q {|diffs (\n. if EVEN n then &0 else ((--(&1)) pow ((n - 1) DIV 2)) / &(FACT n))
   = (\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n) else &0)|} ],
  vREWRITE_TAC[diffs] ----> vBETA_TAC ---->
  vCONV_TAC(vX_FUN_EQ_CONV [%q {|n:num|} ]) ----> vGEN_TAC ----> vBETA_TAC ---->
  vCOND_CASES_TAC ----> vRULE_ASSUM_TAC(vREWRITE_RULE[vEVEN]) ---->
  vASM_REWRITE_TAC[vREAL_MUL_RZERO] ----> vREWRITE_TAC[vSUC_SUB1] ---->
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ----> vAP_TERM_TAC ---->
  vREWRITE_TAC[vFACT; vGSYM vREAL_MUL] ---->
  vSUBGOAL_THEN [%q {|~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)|} ] vASSUME_TAC ++-->
   [vCONJ_TAC ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
    vREWRITE_TAC[vREAL_LT; vLT_0; vFACT_LT];
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_INV_MUL_WEAK th]) ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC; vREAL_EQ_RMUL] ----> vDISJ2_TAC ---->
    vMATCH_MP_TAC vREAL_MUL_RINV ----> vASM_REWRITE_TAC[]]);;

let%a vCOS_FDIFF = prove(
  [%q {|diffs (\n. if EVEN n then ((--(&1)) pow (n DIV 2)) / &(FACT n) else &0) =
  (\n. --(((\n. if EVEN n then &0 else ((--(&1)) pow ((n - 1) DIV 2)) /
   &(FACT n))) n))|} ],
  vREWRITE_TAC[diffs] ----> vBETA_TAC ---->
  vCONV_TAC(vX_FUN_EQ_CONV [%q {|n:num|} ]) ----> vGEN_TAC ----> vBETA_TAC ---->
  vCOND_CASES_TAC ----> vRULE_ASSUM_TAC(vREWRITE_RULE[vEVEN]) ---->
  vASM_REWRITE_TAC[vREAL_MUL_RZERO; vREAL_NEG_0] ---->
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[real_div; vREAL_NEG_LMUL] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vBINOP_TAC ++-->
   [vPOP_ASSUM(vSUBST1_TAC -| vMATCH_MP vEVEN_DIV2) ---->
    vREWRITE_TAC[pow] ----> vREWRITE_TAC[vGSYM vREAL_NEG_MINUS1];
    vREWRITE_TAC[vFACT; vGSYM vREAL_MUL] ---->
    vSUBGOAL_THEN [%q {|~(&(SUC n) = &0) /\ ~(&(FACT n) = &0)|} ] vASSUME_TAC ++-->
     [vCONJ_TAC ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
      vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
      vREWRITE_TAC[vREAL_LT; vLT_0; vFACT_LT];
      vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_INV_MUL_WEAK th]) ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
      vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC; vREAL_EQ_RMUL] ----> vDISJ2_TAC ---->
      vMATCH_MP_TAC vREAL_MUL_RINV ----> vASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------ *)
(* Now at last we can get the derivatives of exp, sin and cos               *)
(* ------------------------------------------------------------------------ *)

let%a vSIN_NEGLEMMA = prove(
  [%q {|!x. --(sin x) = suminf (\n. --(((\n. if EVEN n then &0 else ((--(&1))
        pow ((n - 1) DIV 2)) / &(FACT n))) n * (x pow n)))|} ],
  vGEN_TAC ----> vMATCH_MP_TAC vSUM_UNIQ ---->
  vMP_TAC(vMATCH_MP vSER_NEG (vSPEC [%q {|x:real|} ] vSIN_CONVERGES)) ---->
  vBETA_TAC ----> vDISCH_THEN vACCEPT_TAC);;

let%a vDIFF_EXP = prove(
  [%q {|!x. (exp diffl exp(x))(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vHALF_MK_ABS exp] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vGSYM vREAL_EXP_FDIFF] ---->
  vCONV_TAC(vLAND_CONV vBETA_CONV) ---->
  vMATCH_MP_TAC vTERMDIFF ----> vEXISTS_TAC [%q {|abs(x) + &1|} ] ---->
  vREWRITE_TAC[vREAL_EXP_FDIFF; vMATCH_MP vSUM_SUMMABLE (vSPEC_ALL vREAL_EXP_CONVERGES)] ---->
  vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|abs(x) + &1|} ] ---->
  vREWRITE_TAC[vABS_LE; vREAL_LT_ADDR] ---->
  vREWRITE_TAC[vREAL_LT; num_CONV [%q {|1|} ]; vLT_0]);;

let%a vDIFF_SIN = prove(
  [%q {|!x. (sin diffl cos(x))(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vHALF_MK_ABS sin; cos] ---->
  vONCE_REWRITE_TAC[vGSYM vSIN_FDIFF] ---->
  vMATCH_MP_TAC vTERMDIFF ----> vEXISTS_TAC [%q {|abs(x) + &1|} ] ---->
  vREPEAT vCONJ_TAC ++-->
   [vREWRITE_TAC[vMATCH_MP vSUM_SUMMABLE (vSPEC_ALL vSIN_CONVERGES)];
    vREWRITE_TAC[vSIN_FDIFF; vMATCH_MP vSUM_SUMMABLE (vSPEC_ALL vCOS_CONVERGES)];
    vREWRITE_TAC[vSIN_FDIFF; vCOS_FDIFF] ----> vBETA_TAC ---->
    vMP_TAC(vSPEC [%q {|abs(x) + &1|} ] vSIN_CONVERGES) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_NEG) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUM_SUMMABLE) ----> vBETA_TAC ---->
    vREWRITE_TAC[vGSYM vREAL_NEG_LMUL];
    vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|abs(x) + &1|} ] ---->
    vREWRITE_TAC[vABS_LE; vREAL_LT_ADDR] ---->
    vREWRITE_TAC[vREAL_LT; num_CONV [%q {|1|} ]; vLT_0]]);;

let%a vDIFF_COS = prove(
  [%q {|!x. (cos diffl --(sin(x)))(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vHALF_MK_ABS cos; vSIN_NEGLEMMA] ---->
  vONCE_REWRITE_TAC[vREAL_NEG_LMUL] ---->
  vREWRITE_TAC[vGSYM(vCONV_RULE(vRAND_CONV vBETA_CONV)
    (vAP_THM vCOS_FDIFF [%q {|n:num|} ]))] ---->
  vMATCH_MP_TAC vTERMDIFF ----> vEXISTS_TAC [%q {|abs(x) + &1|} ] ---->
  vREPEAT vCONJ_TAC ++-->
   [vREWRITE_TAC[vMATCH_MP vSUM_SUMMABLE (vSPEC_ALL vCOS_CONVERGES)];
    vREWRITE_TAC[vCOS_FDIFF] ---->
    vMP_TAC(vSPEC [%q {|abs(x) + &1|} ] vSIN_CONVERGES) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_NEG) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUM_SUMMABLE) ----> vBETA_TAC ---->
    vREWRITE_TAC[vGSYM vREAL_NEG_LMUL];
    vREWRITE_TAC[vCOS_FDIFF; vDIFFS_NEG] ---->
    vMP_TAC vSIN_FDIFF ----> vBETA_TAC ---->
    vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
    vMP_TAC(vSPEC [%q {|abs(x) + &1|} ] vCOS_CONVERGES) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_NEG) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUM_SUMMABLE) ----> vBETA_TAC ---->
    vREWRITE_TAC[vGSYM vREAL_NEG_LMUL];
    vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|abs(x) + &1|} ] ---->
    vREWRITE_TAC[vABS_LE; vREAL_LT_ADDR] ---->
    vREWRITE_TAC[vREAL_LT; num_CONV [%q {|1|} ]; vLT_0]]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation conversion.                                               *)
(* ------------------------------------------------------------------------- *)

let vDIFF_CONV =
  let lookup_expr tm =
    tryfind (fun f -> f tm) (lookup tm (!diff_net)) in
  let v = [%q {|x:real|} ] and k = [%q {|k:real|} ] and diffl_tm = [%q {|(diffl)|} ] in
  let vDIFF_var = vSPEC v vDIFF_X
  and vDIFF_const = vSPECL [k;v] vDIFF_CONST in
  let uneta_CONV = vREWR_CONV (vGSYM vETA_AX) in
  let rec vDIFF_CONV tm =
    if not (is_abs tm) then
      let th0 = uneta_CONV tm in
      let th1 = vDIFF_CONV (rand(concl th0)) in
      vCONV_RULE (vRATOR_CONV(vLAND_CONV(vK(vSYM th0)))) th1 else
    let x,bod = dest_abs tm in
    if bod = x then vINST [x,v] vDIFF_var
    else if not(free_in x bod) then vINST [bod,k; x,v] vDIFF_const else
    let th = lookup_expr tm in
    let hyp = fst(dest_imp(concl th)) in
    let hyps = conjuncts hyp in
    let dhyps,sides = partition
      (fun t -> try funpow 3 rator t = diffl_tm
                with Failure _ -> false) hyps in
    let tha = vCONJ_ACI_RULE(mk_eq(hyp,list_mk_conj(dhyps@sides))) in
    let thb = vCONV_RULE (vLAND_CONV (vK tha)) th in
    let dths = map (vDIFF_CONV -| lhand -| rator) dhyps in
    vMATCH_MP thb (end_itlist vCONJ (dths @ map vASSUME sides)) in
  fun tm ->
    let xv = try bndvar tm with Failure _ -> v in
    vGEN xv (vDISCH_ALL(vDIFF_CONV tm));;

(* ------------------------------------------------------------------------- *)
(* Processed versions of composition theorems.                               *)
(* ------------------------------------------------------------------------- *)

let%a vDIFF_COMPOSITE = prove
 ([%q {|((f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl --(l / (f(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)) /\
   ((f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)) /\
   ((f diffl l)(x) ==> ((\x. --(f x)) diffl --l)(x)) /\
   ((g diffl m)(x) ==>
         ((\x. (g x) pow n) diffl ((&n * (g x) pow (n - 1)) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. exp(g x)) diffl (exp(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. sin(g x)) diffl (cos(g x) * m))(x)) /\
   ((g diffl m)(x) ==> ((\x. cos(g x)) diffl (--(sin(g x)) * m))(x))|} ],
  vREWRITE_TAC[vDIFF_INV; vDIFF_DIV; vDIFF_ADD; vDIFF_SUB; vDIFF_MUL; vDIFF_NEG] ---->
  vREPEAT vCONJ_TAC ----> vDISCH_TAC ---->
  vTRY(vMATCH_MP_TAC vDIFF_CHAIN ---->
  vASM_REWRITE_TAC[vDIFF_SIN; vDIFF_COS; vDIFF_EXP]) ---->
  vMATCH_MP_TAC(vBETA_RULE (vSPEC [%q {|\x. x pow n|} ] vDIFF_CHAIN)) ---->
  vASM_REWRITE_TAC[vDIFF_POW]);;

do_list add_to_diff_net (vCONJUNCTS vDIFF_COMPOSITE);;

(* ------------------------------------------------------------------------- *)
(* Tactic for goals "(f diffl l) x"                                          *)
(* ------------------------------------------------------------------------- *)

let vDIFF_TAC =
  vW(fun (asl,w) -> vMP_TAC(vSPEC(rand w) (vDIFF_CONV(lhand(rator w)))) ---->
                   vMATCH_MP_TAC vEQ_IMP ----> vAP_THM_TAC ----> vAP_TERM_TAC);;

(* ------------------------------------------------------------------------- *)
(* Prove differentiability terms.                                            *)
(* ------------------------------------------------------------------------- *)

let vDIFFERENTIABLE_RULE =
  let pth = prove
   ([%q {|(f diffl l) x ==> f differentiable x|} ], vMESON_TAC[differentiable]) in
  let match_pth = vMATCH_MP pth in
  fun tm ->
    let tb,y = dest_comb tm in
    let tm' = rand tb in
    match_pth (vSPEC y (vDIFF_CONV tm'));;

let vDIFFERENTIABLE_CONV = vEQT_INTRO -| vDIFFERENTIABLE_RULE;;

(* ------------------------------------------------------------------------- *)
(* Prove continuity via differentiability (weak but useful).                 *)
(* ------------------------------------------------------------------------- *)

let vCONTINUOUS_RULE =
  let pth = prove
   ([%q {|!f x. f differentiable x ==> f contl x|} ],
    vMESON_TAC[differentiable; vDIFF_CONT]) in
  let match_pth = vPART_MATCH rand pth in
  fun tm ->
   let th1 = match_pth tm in
   vMP th1 (vDIFFERENTIABLE_RULE(lhand(concl th1)));;

let vCONTINUOUS_CONV = vEQT_INTRO -| vCONTINUOUS_RULE;;

(* ------------------------------------------------------------------------ *)
(* Properties of the exponential function                                   *)
(* ------------------------------------------------------------------------ *)

let%a vREAL_EXP_0 = prove(
  [%q {|exp(&0) = &1|} ],
  vREWRITE_TAC[exp] ----> vCONV_TAC vSYM_CONV ---->
  vMATCH_MP_TAC vSUM_UNIQ ----> vBETA_TAC ---->
  vW(vMP_TAC -| vC vSPEC vSER_0 -| rand -| rator -| snd) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|1|} ]) ---->
  vREWRITE_TAC[num_CONV [%q {|1|} ]; sum] ---->
  vREWRITE_TAC[vADD_CLAUSES; vREAL_ADD_LID] ----> vBETA_TAC ---->
  vREWRITE_TAC[vFACT; pow; vREAL_MUL_RID; vREAL_INV1] ---->
  vREWRITE_TAC[vSYM(num_CONV [%q {|1|} ])] ----> vDISCH_THEN vMATCH_MP_TAC ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[num_CONV [%q {|1|} ]; vLE_SUC_LT] ---->
  vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC -| vMATCH_MP vLESS_ADD_1) ---->
  vREWRITE_TAC[vGSYM vADD1; vPOW_0; vREAL_MUL_RZERO; vADD_CLAUSES]);;

let%a vREAL_EXP_LE_X = prove(
  [%q {|!x. &0 <= x ==> (&1 + x) <= exp(x)|} ],
  vGEN_TAC ----> vDISCH_THEN(vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
   [vMP_TAC(vSPECL [[%q {|\n. ((\n. inv(&(FACT n)))) n * (x pow n)|} ]; [%q {|2|} ]]
     vSER_POS_LE) ---->
    vREWRITE_TAC[vMATCH_MP vSUM_SUMMABLE (vSPEC_ALL vREAL_EXP_CONVERGES)] ---->
    vREWRITE_TAC[vGSYM exp] ----> vBETA_TAC ---->
    vW(vC vSUBGOAL_THEN (fun t ->vREWRITE_TAC[t]) -|
    funpow 2 (fst -| dest_imp) -| snd) ++-->
     [vGEN_TAC ----> vDISCH_THEN(vK vALL_TAC) ---->
      vMATCH_MP_TAC vREAL_LE_MUL ----> vCONJ_TAC ++-->
       [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vMATCH_MP_TAC vREAL_INV_POS ---->
        vREWRITE_TAC[vREAL_LT; vFACT_LT];
        vMATCH_MP_TAC vPOW_POS ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
        vFIRST_ASSUM vACCEPT_TAC];
      vCONV_TAC(vTOP_DEPTH_CONV num_CONV) ----> vREWRITE_TAC[sum] ---->
      vBETA_TAC ----> vREWRITE_TAC[vADD_CLAUSES; vFACT; pow; vREAL_ADD_LID] ---->
      vREWRITE_TAC[vMULT_CLAUSES; vREAL_INV1; vREAL_MUL_LID; vADD_CLAUSES] ---->
      vREWRITE_TAC[vREAL_MUL_RID; vSYM(num_CONV [%q {|1|} ])]];
    vPOP_ASSUM(vSUBST1_TAC -| vSYM) ---->
    vREWRITE_TAC[vREAL_EXP_0; vREAL_ADD_RID; vREAL_LE_REFL]]);;

let%a vREAL_EXP_LT_1 = prove(
  [%q {|!x. &0 < x ==> &1 < exp(x)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LTE_TRANS ---->
  vEXISTS_TAC [%q {|&1 + x|} ] ----> vASM_REWRITE_TAC[vREAL_LT_ADDR] ---->
  vMATCH_MP_TAC vREAL_EXP_LE_X ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
  vPOP_ASSUM vACCEPT_TAC);;

let%a vREAL_EXP_ADD_MUL = prove(
  [%q {|!x y. exp(x + y) * exp(--x) = exp(y)|} ],
  vREPEAT vGEN_TAC ---->
  vCONV_TAC(vLAND_CONV(vX_BETA_CONV [%q {|x:real|} ])) ---->
  vSUBGOAL_THEN [%q {|exp(y) = (\x. exp(x + y) * exp(--x))(&0)|} ] vSUBST1_TAC ++-->
   [vBETA_TAC ----> vREWRITE_TAC[vREAL_ADD_LID; vREAL_NEG_0] ---->
    vREWRITE_TAC[vREAL_EXP_0; vREAL_MUL_RID];
    vMATCH_MP_TAC vDIFF_ISCONST_ALL ----> vX_GEN_TAC [%q {|x:real|} ] ---->
    vW(vMP_TAC -| vDIFF_CONV -| rand -| funpow 2 rator -| snd) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x:real|} ]) ---->
    vMATCH_MP_TAC vEQ_IMP ----> vAP_THM_TAC ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL] ---->
    vREWRITE_TAC[vGSYM real_sub; vREAL_SUB_0; vREAL_MUL_RID; vREAL_ADD_RID] ---->
    vMATCH_ACCEPT_TAC vREAL_MUL_SYM]);;

let%a vREAL_EXP_NEG_MUL = prove(
  [%q {|!x. exp(x) * exp(--x) = &1|} ],
  vGEN_TAC ----> vMP_TAC(vSPECL [[%q {|x:real|} ]; [%q {|&0|} ]] vREAL_EXP_ADD_MUL) ---->
  vREWRITE_TAC[vREAL_ADD_RID; vREAL_EXP_0]);;

let%a vREAL_EXP_NEG_MUL2 = prove(
  [%q {|!x. exp(--x) * exp(x) = &1|} ],
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vMATCH_ACCEPT_TAC vREAL_EXP_NEG_MUL);;

let%a vREAL_EXP_NEG = prove(
  [%q {|!x. exp(--x) = inv(exp(x))|} ],
  vGEN_TAC ----> vMATCH_MP_TAC vREAL_RINV_UNIQ ---->
  vMATCH_ACCEPT_TAC vREAL_EXP_NEG_MUL);;

let%a vREAL_EXP_ADD = prove(
  [%q {|!x y. exp(x + y) = exp(x) * exp(y)|} ],
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vREAL_EXP_ADD_MUL) ---->
  vDISCH_THEN(vMP_TAC -| vC vAP_THM [%q {|exp(x)|} ] -| vAP_TERM [%q {|(*)|} ]) ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
  vREWRITE_TAC[vONCE_REWRITE_RULE[vREAL_MUL_SYM] vREAL_EXP_NEG_MUL; vREAL_MUL_RID] ---->
  vDISCH_THEN vSUBST1_TAC ----> vMATCH_ACCEPT_TAC vREAL_MUL_SYM);;

let%a vREAL_EXP_POS_LE = prove(
  [%q {|!x. &0 <= exp(x)|} ],
  vGEN_TAC ---->
  vGEN_REWRITE_TAC (funpow 2 vRAND_CONV) [vGSYM vREAL_HALF_DOUBLE] ---->
  vREWRITE_TAC[vREAL_EXP_ADD] ----> vMATCH_ACCEPT_TAC vREAL_LE_SQUARE);;

let%a vREAL_EXP_NZ = prove(
  [%q {|!x. ~(exp(x) = &0)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vREAL_EXP_NEG_MUL) ---->
  vASM_REWRITE_TAC[vREAL_MUL_LZERO] ---->
  vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
  vMATCH_ACCEPT_TAC vREAL_10);;

let%a vREAL_EXP_POS_LT = prove(
  [%q {|!x. &0 < exp(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vREAL_LT_LE] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ---->
  vREWRITE_TAC[vREAL_EXP_POS_LE; vREAL_EXP_NZ]);;

let%a vREAL_EXP_N = prove(
  [%q {|!n x. exp(&n * x) = exp(x) pow n|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_EXP_0; pow] ---->
  vREWRITE_TAC[vADD1] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_ADD; vREAL_EXP_ADD; vREAL_RDISTRIB] ---->
  vGEN_TAC ----> vASM_REWRITE_TAC[vREAL_MUL_LID]);;

let%a vREAL_EXP_SUB = prove(
  [%q {|!x y. exp(x - y) = exp(x) / exp(y)|} ],
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[real_sub; real_div; vREAL_EXP_ADD; vREAL_EXP_NEG]);;

let%a vREAL_EXP_MONO_IMP = prove(
  [%q {|!x y. x < y ==> exp(x) < exp(y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -|
    vMATCH_MP vREAL_EXP_LT_1 -| vONCE_REWRITE_RULE[vGSYM vREAL_SUB_LT]) ---->
  vREWRITE_TAC[vREAL_EXP_SUB] ---->
  vSUBGOAL_THEN [%q {|&1 < exp(y) / exp(x) <=>
                 (&1 * exp(x)) < ((exp(y) / exp(x)) * exp(x))|} ] vSUBST1_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_LT_RMUL_EQ ---->
    vMATCH_ACCEPT_TAC vREAL_EXP_POS_LT;
    vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC; vREAL_EXP_NEG_MUL2;
                vGSYM vREAL_EXP_NEG] ---->
    vREWRITE_TAC[vREAL_MUL_LID; vREAL_MUL_RID]]);;

let%a vREAL_EXP_MONO_LT = prove(
  [%q {|!x y. exp(x) < exp(y) <=> x < y|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vREAL_NOT_LT] ---->
    vREWRITE_TAC[vREAL_LE_LT] ---->
    vDISCH_THEN(vDISJ_CASES_THEN2 vASSUME_TAC vSUBST1_TAC) ---->
    vREWRITE_TAC[] ----> vDISJ1_TAC ----> vMATCH_MP_TAC vREAL_EXP_MONO_IMP ---->
    vPOP_ASSUM vACCEPT_TAC;
    vMATCH_ACCEPT_TAC vREAL_EXP_MONO_IMP]);;

let%a vREAL_EXP_MONO_LE = prove(
  [%q {|!x y. exp(x) <= exp(y) <=> x <= y|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_NOT_LT] ---->
  vREWRITE_TAC[vREAL_EXP_MONO_LT]);;

let%a vREAL_EXP_INJ = prove(
  [%q {|!x y. (exp(x) = exp(y)) <=> (x = y)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
  vREWRITE_TAC[vREAL_EXP_MONO_LE]);;

let%a vREAL_EXP_TOTAL_LEMMA = prove(
  [%q {|!y. &1 <= y ==> ?x. &0 <= x /\ x <= y - &1 /\ (exp(x) = y)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vIVT ---->
  vASM_REWRITE_TAC[vREAL_EXP_0; vREAL_LE_SUB_LADD; vREAL_ADD_LID] ----> vCONJ_TAC ++-->
   [vRULE_ASSUM_TAC(vONCE_REWRITE_RULE[vGSYM vREAL_SUB_LE]) ---->
    vPOP_ASSUM(vMP_TAC -| vMATCH_MP vREAL_EXP_LE_X) ----> vREWRITE_TAC[vREAL_SUB_ADD2];
    vX_GEN_TAC [%q {|x:real|} ] ----> vDISCH_THEN(vK vALL_TAC) ---->
    vMATCH_MP_TAC vDIFF_CONT ----> vEXISTS_TAC [%q {|exp(x)|} ] ---->
    vMATCH_ACCEPT_TAC vDIFF_EXP]);;

let%a vREAL_EXP_TOTAL = prove(
  [%q {|!y. &0 < y ==> ?x. exp(x) = y|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vDISJ_CASES_TAC(vSPECL [[%q {|&1|} ]; [%q {|y:real|} ]] vREAL_LET_TOTAL) ++-->
   [vFIRST_ASSUM(vX_CHOOSE_TAC [%q {|x:real|} ] -| vMATCH_MP vREAL_EXP_TOTAL_LEMMA) ---->
    vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[];
    vMP_TAC(vSPEC [%q {|y:real|} ] vREAL_INV_LT1) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|x:real|} ] -| vMATCH_MP vREAL_EXP_TOTAL_LEMMA) ---->
    vEXISTS_TAC [%q {|--x|} ] ----> vASM_REWRITE_TAC[vREAL_EXP_NEG] ---->
    vMATCH_MP_TAC vREAL_INVINV ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vASM_REWRITE_TAC[]]);;

let%a vREAL_EXP_BOUND_LEMMA = prove
 ([%q {|!x. &0 <= x /\ x <= inv(&2) ==> exp(x) <= &1 + &2 * x|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|suminf (\n. x pow n)|} ] ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[exp; vBETA_THM] ----> vMATCH_MP_TAC vSER_LE ---->
    vREWRITE_TAC[summable; vBETA_THM] ----> vREPEAT vCONJ_TAC ++-->
     [vGEN_TAC ---->
      vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
      vMATCH_MP_TAC vREAL_LE_RMUL_IMP ----> vCONJ_TAC ++-->
       [vMATCH_MP_TAC vREAL_POW_LE ----> vASM_REWRITE_TAC[];
        vMATCH_MP_TAC vREAL_INV_LE_1 ---->
        vREWRITE_TAC[vREAL_OF_NUM_LE; num_CONV [%q {|1|} ]; vLE_SUC_LT] ---->
        vREWRITE_TAC[vFACT_LT]];
      vEXISTS_TAC [%q {|exp x|} ] ----> vREWRITE_TAC[vBETA_RULE vREAL_EXP_CONVERGES];
      vEXISTS_TAC [%q {|inv(&1 - x)|} ] ----> vMATCH_MP_TAC vGP ---->
      vASM_REWRITE_TAC[real_abs] ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|inv(&2)|} ] ---->
      vASM_REWRITE_TAC[] ----> vCONV_TAC vREAL_RAT_REDUCE_CONV];
    vSUBGOAL_THEN [%q {|suminf (\n. x pow n) = inv (&1 - x)|} ] vSUBST1_TAC ++-->
     [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSUM_UNIQ ---->
      vMATCH_MP_TAC vGP ---->
      vASM_REWRITE_TAC[real_abs] ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|inv(&2)|} ] ---->
      vASM_REWRITE_TAC[] ----> vCONV_TAC vREAL_RAT_REDUCE_CONV;
      vMATCH_MP_TAC vREAL_LE_LCANCEL_IMP ---->
      vEXISTS_TAC [%q {|&1 - x|} ] ---->
      vSUBGOAL_THEN [%q {|(&1 - x) * inv (&1 - x) = &1|} ] vSUBST1_TAC ++-->
       [vMATCH_MP_TAC vREAL_MUL_RINV ---->
        vREWRITE_TAC[vREAL_ARITH [%q {|(&1 - x = &0) <=> (x = &1)|} ]] ---->
        vDISCH_THEN vSUBST_ALL_TAC ---->
        vPOP_ASSUM vMP_TAC ----> vCONV_TAC vREAL_RAT_REDUCE_CONV;
        vCONJ_TAC ++-->
         [vMATCH_MP_TAC vREAL_LET_TRANS ---->
          vEXISTS_TAC [%q {|inv(&2) - x|} ] ---->
          vASM_REWRITE_TAC[vREAL_ARITH [%q {|&0 <= x - y <=> y <= x|} ]] ---->
          vASM_REWRITE_TAC[vREAL_ARITH [%q {|a - x < b - x <=> a < b|} ]] ---->
          vCONV_TAC vREAL_RAT_REDUCE_CONV;
          vREWRITE_TAC[vREAL_ADD_LDISTRIB; vREAL_SUB_RDISTRIB] ---->
          vREWRITE_TAC[vREAL_MUL_RID; vREAL_MUL_LID] ---->
          vREWRITE_TAC[vREAL_ARITH [%q {|&1 <= (&1 + &2 * x) - (x + x * &2 * x) <=>
                                  x * (&2 * x) <= x * &1|} ]] ---->
          vMATCH_MP_TAC vREAL_LE_LMUL_IMP ----> vASM_REWRITE_TAC[] ---->
          vMATCH_MP_TAC vREAL_LE_LCANCEL_IMP ----> vEXISTS_TAC [%q {|inv(&2)|} ] ---->
          vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
          vCONV_TAC vREAL_RAT_REDUCE_CONV ---->
          vASM_REWRITE_TAC[vREAL_MUL_LID; real_div]]]]]);;

(* ------------------------------------------------------------------------ *)
(* Properties of the logarithmic function                                   *)
(* ------------------------------------------------------------------------ *)

let ln = new_definition
  [%q {|ln x = @u. exp(u) = x|} ];;

let%a vLN_EXP = prove(
  [%q {|!x. ln(exp x) = x|} ],
  vGEN_TAC ----> vREWRITE_TAC[ln; vREAL_EXP_INJ] ---->
  vCONV_TAC vSYM_CONV ----> vCONV_TAC(vRAND_CONV(vONCE_DEPTH_CONV vSYM_CONV)) ---->
  vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ----> vMATCH_MP_TAC vSELECT_AX ---->
  vEXISTS_TAC [%q {|x:real|} ] ----> vREFL_TAC);;

let%a vREAL_EXP_LN = prove(
  [%q {|!x. (exp(ln x) = x) <=> &0 < x|} ],
  vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vMATCH_ACCEPT_TAC vREAL_EXP_POS_LT;
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|y:real|} ] vMP_TAC -| vMATCH_MP vREAL_EXP_TOTAL) ---->
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vREAL_EXP_INJ; vLN_EXP]]);;

let%a vEXP_LN = prove
 ([%q {|!x. &0 < x ==> exp(ln x) = x|} ],
  vREWRITE_TAC[vREAL_EXP_LN]);;

let%a vLN_MUL = prove(
  [%q {|!x y. &0 < x /\ &0 < y ==> (ln(x * y) = ln(x) + ln(y))|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_EXP_INJ] ---->
  vREWRITE_TAC[vREAL_EXP_ADD] ----> vSUBGOAL_THEN [%q {|&0 < x * y|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vREAL_LT_MUL ----> vASM_REWRITE_TAC[];
    vEVERY_ASSUM(fun th -> vREWRITE_TAC[vONCE_REWRITE_RULE[vGSYM vREAL_EXP_LN] th])]);;

let%a vLN_INJ = prove(
  [%q {|!x y. &0 < x /\ &0 < y ==> ((ln(x) = ln(y)) <=> (x = y))|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vEVERY_ASSUM(fun th -> vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV)
    [vSYM(vREWRITE_RULE[vGSYM vREAL_EXP_LN] th)]) ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_ACCEPT_TAC vREAL_EXP_INJ);;

let%a vLN_1 = prove(
  [%q {|ln(&1) = &0|} ],
  vONCE_REWRITE_TAC[vGSYM vREAL_EXP_INJ] ---->
  vREWRITE_TAC[vREAL_EXP_0; vREAL_EXP_LN; vREAL_LT_01]);;

let%a vLN_INV = prove(
  [%q {|!x. &0 < x ==> (ln(inv x) = --(ln x))|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vGSYM vREAL_RNEG_UNIQ] ---->
  vSUBGOAL_THEN [%q {|&0 < x /\ &0 < inv(x)|} ] vMP_TAC ++-->
   [vCONJ_TAC ----> vTRY(vMATCH_MP_TAC vREAL_INV_POS) ----> vASM_REWRITE_TAC[];
    vDISCH_THEN(fun th -> vREWRITE_TAC[vGSYM(vMATCH_MP vLN_MUL th)]) ---->
    vSUBGOAL_THEN [%q {|x * (inv x) = &1|} ] vSUBST1_TAC ++-->
     [vMATCH_MP_TAC vREAL_MUL_RINV ---->
      vPOP_ASSUM(vACCEPT_TAC -| vMATCH_MP vREAL_LT_IMP_NZ);
      vREWRITE_TAC[vLN_1]]]);;

let%a vLN_DIV = prove(
  [%q {|!x. &0 < x /\ &0 < y ==> (ln(x / y) = ln(x) - ln(y))|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|&0 < x /\ &0 < inv(y)|} ] vMP_TAC ++-->
   [vCONJ_TAC ----> vTRY(vMATCH_MP_TAC vREAL_INV_POS) ----> vASM_REWRITE_TAC[];
    vREWRITE_TAC[real_div] ---->
    vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vLN_MUL th]) ---->
    vREWRITE_TAC[vMATCH_MP vLN_INV (vASSUME [%q {|&0 < y|} ])] ---->
    vREWRITE_TAC[real_sub]]);;

let%a vLN_MONO_LT = prove(
  [%q {|!x y. &0 < x /\ &0 < y ==> (ln(x) < ln(y) <=> x < y)|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vEVERY_ASSUM(fun th -> vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV)
    [vSYM(vREWRITE_RULE[vGSYM vREAL_EXP_LN] th)]) ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_ACCEPT_TAC vREAL_EXP_MONO_LT);;

let%a vLN_MONO_LE = prove(
  [%q {|!x y. &0 < x /\ &0 < y ==> (ln(x) <= ln(y) <=> x <= y)|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vEVERY_ASSUM(fun th -> vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV)
    [vSYM(vREWRITE_RULE[vGSYM vREAL_EXP_LN] th)]) ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_ACCEPT_TAC vREAL_EXP_MONO_LE);;

let%a vLN_POW = prove(
  [%q {|!n x. &0 < x ==> (ln(x pow n) = &n * ln(x))|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vCHOOSE_THEN (vSUBST1_TAC -| vSYM) -| vMATCH_MP vREAL_EXP_TOTAL) ---->
  vREWRITE_TAC[vGSYM vREAL_EXP_N; vLN_EXP]);;

let%a vLN_LE = prove(
  [%q {|!x. &0 <= x ==> ln(&1 + x) <= x|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC vRAND_CONV  [vGSYM vLN_EXP] ---->
  vMP_TAC(vSPECL [[%q {|&1 + x|} ]; [%q {|exp(x)|} ]] vLN_MONO_LE) ---->
  vW(vC vSUBGOAL_THEN (fun t -> vREWRITE_TAC[t]) -| funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vREWRITE_TAC[vREAL_EXP_POS_LT] ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[vREAL_LT_ADDL; vREAL_LT_01];
    vDISCH_THEN vSUBST1_TAC ----> vMATCH_MP_TAC vREAL_EXP_LE_X ----> vASM_REWRITE_TAC[]]);;

let%a vLN_LT_X = prove(
  [%q {|!x. &0 < x ==> ln(x) < x|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LTE_TRANS ---->
  vEXISTS_TAC [%q {|ln(&1 + x)|} ] ----> vCONJ_TAC ++-->
   [vIMP_SUBST_TAC vLN_MONO_LT ---->
    vASM_REWRITE_TAC[vREAL_LT_ADDL; vREAL_LT_01] ---->
    vMATCH_MP_TAC vREAL_LT_ADD ----> vASM_REWRITE_TAC[vREAL_LT_01];
    vMATCH_MP_TAC vLN_LE ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
    vASM_REWRITE_TAC[]]);;

let%a vLN_POS = prove
 ([%q {|!x. &1 <= x ==> &0 <= ln(x)|} ],
  vREWRITE_TAC[vGSYM vLN_1] ---->
  vSIMP_TAC[vLN_MONO_LE; vARITH_RULE [%q {|&1 <= x ==> &0 < x|} ]; vREAL_LT_01]);;

let%a vLN_POS_LT = prove
 ([%q {|!x. &1 < x ==> &0 < ln(x)|} ],
  vREWRITE_TAC[vGSYM vLN_1] ---->
  vSIMP_TAC[vLN_MONO_LT; vARITH_RULE [%q {|&1 < x ==> &0 < x|} ]; vREAL_LT_01]);;

let%a vDIFF_LN = prove(
  [%q {|!x. &0 < x ==> (ln diffl (inv x))(x)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vASSUME_TAC -| vREWRITE_RULE[vGSYM vREAL_EXP_LN]) ---->
  vFIRST_ASSUM (fun th ->  vGEN_REWRITE_TAC vRAND_CONV  [vGSYM th]) ---->
  vMATCH_MP_TAC vDIFF_INVERSE_LT ---->
  vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_NZ) ---->
  vASM_REWRITE_TAC[vMATCH_MP vDIFF_CONT (vSPEC_ALL vDIFF_EXP)] ---->
  vMP_TAC(vSPEC [%q {|ln(x)|} ] vDIFF_EXP) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_TAC ----> vASM_REWRITE_TAC[vLN_EXP] ---->
  vEXISTS_TAC [%q {|&1|} ] ----> vMATCH_ACCEPT_TAC vREAL_LT_01);;

(* ------------------------------------------------------------------------ *)
(* Some properties of roots (easier via logarithms)                         *)
(* ------------------------------------------------------------------------ *)

let root = new_definition
  [%q {|root(n) x = @u. (&0 < x ==> &0 < u) /\ (u pow n = x)|} ];;

let%a vROOT_LT_LEMMA = prove(
  [%q {|!n x. &0 < x ==> (exp(ln(x) / &(SUC n)) pow (SUC n) = x)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[vGSYM vREAL_EXP_N] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
  vSUBGOAL_THEN [%q {|inv(&(SUC n)) * &(SUC n) = &1|} ] vSUBST1_TAC ++-->
   [vMATCH_MP_TAC vREAL_MUL_LINV ----> vREWRITE_TAC[vREAL_INJ; vNOT_SUC];
    vASM_REWRITE_TAC[vREAL_MUL_RID; vREAL_EXP_LN]]);;

let%a vROOT_LN = prove(
  [%q {|!x. &0 < x ==> !n. root(SUC n) x = exp(ln(x) / &(SUC n))|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ----> vREWRITE_TAC[root] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ----> vX_GEN_TAC [%q {|y:real|} ] ----> vBETA_TAC ---->
  vASM_REWRITE_TAC[] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vSUBST1_TAC -| vSYM)) ---->
    vSUBGOAL_THEN [%q {|!z. &0 < y /\ &0 < exp(z)|} ] vMP_TAC ++-->
     [vASM_REWRITE_TAC[vREAL_EXP_POS_LT]; vALL_TAC] ---->
    vDISCH_THEN(vMP_TAC -| vGEN_ALL -| vSYM -| vMATCH_MP vLN_INJ -| vSPEC_ALL) ---->
    vDISCH_THEN(fun th -> vGEN_REWRITE_TAC vI [th]) ---->
    vREWRITE_TAC[vLN_EXP] ---->
    vSUBGOAL_THEN [%q {|ln(y) * &(SUC n) = (ln(y pow(SUC n)) / &(SUC n)) * &(SUC n)|} ]
    vMP_TAC ++-->
     [vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
      vSUBGOAL_THEN [%q {|inv(&(SUC n)) * &(SUC n) = &1|} ] vSUBST1_TAC ++-->
       [vMATCH_MP_TAC vREAL_MUL_LINV ----> vREWRITE_TAC[vREAL_INJ; vNOT_SUC];
        vREWRITE_TAC[vREAL_MUL_RID] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
        vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vLN_POW ---->
        vASM_REWRITE_TAC[]];
      vREWRITE_TAC[vREAL_EQ_RMUL; vREAL_INJ; vNOT_SUC]];
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vREAL_EXP_POS_LT] ---->
    vMATCH_MP_TAC vROOT_LT_LEMMA ----> vASM_REWRITE_TAC[]]);;

let%a vROOT_0 = prove(
  [%q {|!n. root(SUC n) (&0) = &0|} ],
  vGEN_TAC ----> vREWRITE_TAC[root] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ----> vX_GEN_TAC [%q {|y:real|} ] ---->
  vBETA_TAC ----> vREWRITE_TAC[vREAL_LT_REFL] ----> vEQ_TAC ++-->
   [vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vINDUCT_TAC ----> vONCE_REWRITE_TAC[pow] ++-->
     [vREWRITE_TAC[pow; vREAL_MUL_RID];
      vREWRITE_TAC[vREAL_ENTIRE] ----> vDISCH_THEN vDISJ_CASES_TAC ---->
      vASM_REWRITE_TAC[] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vASM_REWRITE_TAC[]];
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[pow; vREAL_MUL_LZERO]]);;

let%a vROOT_1 = prove(
  [%q {|!n. root(SUC n) (&1) = &1|} ],
  vGEN_TAC ----> vREWRITE_TAC[vMATCH_MP vROOT_LN vREAL_LT_01] ---->
  vREWRITE_TAC[vLN_1; vREAL_DIV_LZERO; vREAL_EXP_0]);;

let%a vROOT_POW_POS = prove(
  [%q {|!n x. &0 <= x ==> ((root(SUC n) x) pow (SUC n) = x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_LE_LT] ---->
  vDISCH_THEN vDISJ_CASES_TAC ++-->
   [vFIRST_ASSUM(fun th -> vREWRITE_TAC
     [vMATCH_MP vROOT_LN th; vMATCH_MP vROOT_LT_LEMMA th]);
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vROOT_0] ---->
    vMATCH_ACCEPT_TAC vPOW_0]);;

let%a vPOW_ROOT_POS = prove(
  [%q {|!n x. &0 <= x ==> (root(SUC n)(x pow (SUC n)) = x)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[root] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vX_GEN_TAC [%q {|y:real|} ] ----> vBETA_TAC ----> vEQ_TAC ---->
  vDISCH_TAC ----> vASM_REWRITE_TAC[] ++-->
   [vDISJ_CASES_THEN vMP_TAC (vREWRITE_RULE[vREAL_LE_LT] (vASSUME [%q {|&0 <= x|} ])) ++-->
     [vDISCH_TAC ----> vFIRST_ASSUM(vUNDISCH_TAC -| check is_conj -| concl) ---->
      vFIRST_ASSUM(fun th ->  vREWRITE_TAC[vMATCH_MP vPOW_POS_LT th]) ---->
      vDISCH_TAC ----> vMATCH_MP_TAC vPOW_EQ ----> vEXISTS_TAC [%q {|n:num|} ] ---->
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
      vASM_REWRITE_TAC[];
      vDISCH_THEN(vSUBST_ALL_TAC -| vSYM) ---->
      vFIRST_ASSUM(vUNDISCH_TAC -| check is_conj -| concl) ---->
      vREWRITE_TAC[vPOW_0; vREAL_LT_REFL; vPOW_ZERO]];
    vASM_REWRITE_TAC[vREAL_LT_LE] ----> vCONV_TAC vCONTRAPOS_CONV ---->
    vREWRITE_TAC[] ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
    vREWRITE_TAC[vPOW_0]]);;

let%a vROOT_POS_POSITIVE = prove
 ([%q {|!x n. &0 <= x ==> &0 <= root(SUC n) x|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
   [vPOP_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vROOT_LN th]) ---->
    vREWRITE_TAC[vREAL_EXP_POS_LE];
    vPOP_ASSUM(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vROOT_0] ---->
    vREWRITE_TAC[vREAL_LE_REFL]]);;

let%a vROOT_POS_UNIQ = prove
 ([%q {|!n x y. &0 <= x /\ &0 <= y /\ (y pow (SUC n) = x)
           ==> (root (SUC n) x = y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC (vSUBST1_TAC -| vSYM)) ---->
  vASM_SIMP_TAC[vPOW_ROOT_POS]);;

let%a vROOT_MUL = prove
 ([%q {|!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x * y) = root(SUC n) x * root(SUC n) y)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vROOT_POS_UNIQ ---->
  vASM_SIMP_TAC[vREAL_POW_MUL; vROOT_POW_POS; vREAL_LE_MUL;
               vROOT_POS_POSITIVE]);;

let%a vROOT_INV = prove
 ([%q {|!n x. &0 <= x ==> (root(SUC n) (inv x) = inv(root(SUC n) x))|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vROOT_POS_UNIQ ---->
  vASM_SIMP_TAC[vREAL_LE_INV; vROOT_POS_POSITIVE; vREAL_POW_INV;
               vROOT_POW_POS]);;

let%a vROOT_DIV = prove
 ([%q {|!n x y. &0 <= x /\ &0 <= y
           ==> (root(SUC n) (x / y) = root(SUC n) x / root(SUC n) y)|} ],
  vSIMP_TAC[real_div; vROOT_MUL; vROOT_INV; vREAL_LE_INV]);;

let%a vROOT_MONO_LT = prove
 ([%q {|!x y. &0 <= x /\ x < y ==> root(SUC n) x < root(SUC n) y|} ],
  vREPEAT vSTRIP_TAC ----> vSUBGOAL_THEN [%q {|&0 <= y|} ] vASSUME_TAC ++-->
   [vASM_MESON_TAC[vREAL_LE_TRANS; vREAL_LT_IMP_LE]; vALL_TAC] ---->
  vUNDISCH_TAC [%q {|x < y|} ] ----> vCONV_TAC vCONTRAPOS_CONV ---->
  vREWRITE_TAC[vREAL_NOT_LT] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|(x = (root(SUC n) x) pow (SUC n)) /\
                (y = (root(SUC n) y) pow (SUC n))|} ]
   (vCONJUNCTS_THEN vSUBST1_TAC)
  ++--> [vASM_SIMP_TAC[vGSYM vROOT_POW_POS]; vALL_TAC] ---->
  vMATCH_MP_TAC vREAL_POW_LE2 ---->
  vASM_SIMP_TAC[vNOT_SUC; vROOT_POS_POSITIVE]);;

let%a vROOT_MONO_LE = prove
 ([%q {|!x y. &0 <= x /\ x <= y ==> root(SUC n) x <= root(SUC n) y|} ],
  vMESON_TAC[vROOT_MONO_LT; vREAL_LE_LT]);;

let%a vROOT_MONO_LT_EQ = prove
 ([%q {|!x y. &0 <= x /\ &0 <= y ==> (root(SUC n) x < root(SUC n) y <=> x < y)|} ],
  vMESON_TAC[vROOT_MONO_LT; vREAL_NOT_LT; vROOT_MONO_LE]);;

let%a vROOT_MONO_LE_EQ = prove
 ([%q {|!x y. &0 <= x /\ &0 <= y ==> (root(SUC n) x <= root(SUC n) y <=> x <= y)|} ],
  vMESON_TAC[vROOT_MONO_LT; vREAL_NOT_LT; vROOT_MONO_LE]);;

let%a vROOT_INJ = prove
 ([%q {|!x y. &0 <= x /\ &0 <= y ==> ((root(SUC n) x = root(SUC n) y) <=> (x = y))|} ],
  vSIMP_TAC[vGSYM vREAL_LE_ANTISYM; vROOT_MONO_LE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Special case of square roots, a few theorems not already present.         *)
(* ------------------------------------------------------------------------- *)

let%a vSQRT_EVEN_POW2 = prove
 ([%q {|!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))|} ],
  vGEN_TAC ----> vREWRITE_TAC[vEVEN_MOD] ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vSQRT_UNIQUE ---->
  vSIMP_TAC[vREAL_POW_LE; vREAL_POS; vREAL_POW_POW] ---->
  vAP_TERM_TAC ---->
  vGEN_REWRITE_TAC vRAND_CONV [vMATCH_MP vDIVISION (vARITH_RULE [%q {|~(2 = 0)|} ])] ---->
  vASM_REWRITE_TAC[vADD_CLAUSES]);;

let%a vREAL_DIV_SQRT = prove
 ([%q {|!x. &0 <= x ==> x / sqrt(x) = sqrt(x)|} ],
  vGEN_TAC ----> vASM_CASES_TAC [%q {|x = &0|} ] ++-->
   [vASM_REWRITE_TAC[vSQRT_0; real_div; vREAL_MUL_LZERO]; vALL_TAC] ---->
  vDISCH_TAC ----> vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSQRT_UNIQUE ---->
  vASM_SIMP_TAC[vSQRT_POS_LE; vREAL_LE_DIV] ---->
  vREWRITE_TAC[real_div; vREAL_POW_MUL; vREAL_POW_INV] ---->
  vASM_SIMP_TAC[vSQRT_POW_2] ---->
  vREWRITE_TAC[vREAL_POW_2; vGSYM vREAL_MUL_ASSOC] ---->
  vASM_SIMP_TAC[vREAL_MUL_RINV; vREAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Derivative of sqrt (could do the other roots with a bit more care).       *)
(* ------------------------------------------------------------------------- *)

let%a vDIFF_SQRT = prove
 ([%q {|!x. &0 < x ==> (sqrt diffl inv(&2 * sqrt(x))) x|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|\x. x pow 2|} ]; [%q {|sqrt|} ]; [%q {|&2 * sqrt(x)|} ]; [%q {|sqrt(x)|} ]; [%q {|sqrt(x)|} ]]
        vDIFF_INVERSE_LT) ---->
  vASM_SIMP_TAC[vSQRT_POW_2; vREAL_LT_IMP_LE; vBETA_THM] ---->
  vDISCH_THEN vMATCH_MP_TAC ---->
  vASM_SIMP_TAC[vSQRT_POS_LT; vREAL_LT_IMP_NZ; vREAL_ENTIRE] ---->
  vREWRITE_TAC[vREAL_OF_NUM_EQ; vARITH_EQ] ----> vREPEAT vCONJ_TAC ++-->
   [vASM_MESON_TAC[vPOW_2_SQRT; vREAL_ARITH [%q {|abs(x - y) < y ==> &0 <= x|} ]];
    vREPEAT vSTRIP_TAC ----> vCONV_TAC vCONTINUOUS_CONV;
    vDIFF_TAC ----> vREWRITE_TAC[vARITH; vREAL_POW_1; vREAL_MUL_RID]]);;

let vDIFF_SQRT_COMPOSITE = prove
 ([%q {|!g m x. (g diffl m)(x) /\ &0 < g x
           ==> ((\x. sqrt(g x)) diffl (inv(&2 * sqrt(g x)) * m))(x)|} ],
  vSIMP_TAC[vDIFF_CHAIN; vDIFF_SQRT]) in
add_to_diff_net (vSPEC_ALL vDIFF_SQRT_COMPOSITE);;

(* ------------------------------------------------------------------------ *)
(* Basic properties of the trig functions                                   *)
(* ------------------------------------------------------------------------ *)

let%a vSIN_0 = prove(
  [%q {|sin(&0) = &0|} ],
  vREWRITE_TAC[sin] ----> vCONV_TAC vSYM_CONV ---->
  vMATCH_MP_TAC vSUM_UNIQ ----> vBETA_TAC ---->
  vW(vMP_TAC -| vC vSPEC vSER_0 -| rand -| rator -| snd) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|0|} ]) ----> vREWRITE_TAC[vLE_0] ---->
  vBETA_TAC ---->
  vREWRITE_TAC[sum] ----> vDISCH_THEN vMATCH_MP_TAC ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vREAL_MUL_LZERO] ---->
  vMP_TAC(vSPEC [%q {|n:num|} ] vODD_EXISTS) ----> vASM_REWRITE_TAC[vGSYM vNOT_EVEN] ---->
  vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC) ---->
  vREWRITE_TAC[vGSYM vADD1; vPOW_0; vREAL_MUL_RZERO]);;

let%a vCOS_0 = prove(
  [%q {|cos(&0) = &1|} ],
  vREWRITE_TAC[cos] ----> vCONV_TAC vSYM_CONV ---->
  vMATCH_MP_TAC vSUM_UNIQ ----> vBETA_TAC ---->
  vW(vMP_TAC -| vC vSPEC vSER_0 -| rand -| rator -| snd) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|1|} ]) ---->
  vREWRITE_TAC[num_CONV [%q {|1|} ]; sum; vADD_CLAUSES] ----> vBETA_TAC ---->
  vREWRITE_TAC[vEVEN; pow; vFACT] ---->
  vREWRITE_TAC[vREAL_ADD_LID; vREAL_MUL_RID] ---->
  vSUBGOAL_THEN [%q {|0 DIV 2 = 0|} ] vSUBST1_TAC ++-->
   [vMATCH_MP_TAC vDIV_UNIQ ----> vEXISTS_TAC [%q {|0|} ] ---->
    vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES] ---->
    vREWRITE_TAC[num_CONV [%q {|2|} ]; vLT_0];
    vREWRITE_TAC[pow]] ---->
  vSUBGOAL_THEN [%q {|&1 / &1 = &(SUC 0)|} ] vSUBST1_TAC ++-->
   [vREWRITE_TAC[vSYM(num_CONV [%q {|1|} ])] ----> vMATCH_MP_TAC vREAL_DIV_REFL ---->
    vMATCH_ACCEPT_TAC vREAL_10;
    vDISCH_THEN vMATCH_MP_TAC] ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vLE_SUC_LT] ---->
  vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC -| vMATCH_MP vLESS_ADD_1) ---->
  vREWRITE_TAC[vGSYM vADD1; vPOW_0; vREAL_MUL_RZERO; vADD_CLAUSES]);;

let%a vSIN_CIRCLE = prove(
  [%q {|!x. (sin(x) pow 2) + (cos(x) pow 2) = &1|} ],
  vGEN_TAC ----> vCONV_TAC(vLAND_CONV(vX_BETA_CONV [%q {|x:real|} ])) ---->
  vSUBGOAL_THEN [%q {|&1 = (\x.(sin(x) pow 2) + (cos(x) pow 2))(&0)|} ] vSUBST1_TAC ++-->
   [vBETA_TAC ----> vREWRITE_TAC[vSIN_0; vCOS_0] ---->
    vREWRITE_TAC[num_CONV [%q {|2|} ]; vPOW_0] ---->
    vREWRITE_TAC[pow; vPOW_1] ----> vREWRITE_TAC[vREAL_ADD_LID; vREAL_MUL_LID];
    vMATCH_MP_TAC vDIFF_ISCONST_ALL ----> vX_GEN_TAC [%q {|x:real|} ] ---->
    vW(vMP_TAC -| vDIFF_CONV -| rand -| funpow 2 rator -| snd) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x:real|} ]) ---->
    vMATCH_MP_TAC vEQ_IMP ----> vAP_THM_TAC ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL] ---->
    vREWRITE_TAC[vGSYM real_sub; vREAL_SUB_0] ---->
    vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC; vREAL_MUL_RID] ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[num_CONV [%q {|2|} ]; vSUC_SUB1] ---->
    vREWRITE_TAC[vPOW_1] ----> vMATCH_ACCEPT_TAC vREAL_MUL_SYM]);;

let%a vSIN_BOUND = prove(
  [%q {|!x. abs(sin x) <= &1|} ],
  vGEN_TAC ----> vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
  vPURE_ONCE_REWRITE_TAC[vREAL_NOT_LE] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT1_POW2) ---->
  vREWRITE_TAC[vREAL_POW2_ABS] ---->
  vDISCH_THEN(vMP_TAC -| vONCE_REWRITE_RULE[vGSYM vREAL_SUB_LT]) ---->
  vDISCH_THEN(vMP_TAC -| vC vCONJ(vSPEC [%q {|cos(x)|} ] vREAL_LE_SQUARE)) ---->
  vREWRITE_TAC[vGSYM vPOW_2] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LTE_ADD) ---->
  vREWRITE_TAC[real_sub; vGSYM vREAL_ADD_ASSOC] ---->
  vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
    [%q {|a + b + c = (a + c) + b|} ]] ---->
  vREWRITE_TAC[vSIN_CIRCLE; vREAL_ADD_RINV; vREAL_LT_REFL]);;

let%a vSIN_BOUNDS = prove(
  [%q {|!x. --(&1) <= sin(x) /\ sin(x) <= &1|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vABS_BOUNDS; vSIN_BOUND]);;

let%a vCOS_BOUND = prove(
  [%q {|!x. abs(cos x) <= &1|} ],
  vGEN_TAC ----> vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
  vPURE_ONCE_REWRITE_TAC[vREAL_NOT_LE] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT1_POW2) ---->
  vREWRITE_TAC[vREAL_POW2_ABS] ---->
  vDISCH_THEN(vMP_TAC -| vONCE_REWRITE_RULE[vGSYM vREAL_SUB_LT]) ---->
  vDISCH_THEN(vMP_TAC -| vCONJ(vSPEC [%q {|sin(x)|} ] vREAL_LE_SQUARE)) ---->
  vREWRITE_TAC[vGSYM vPOW_2] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LET_ADD) ---->
  vREWRITE_TAC[real_sub; vREAL_ADD_ASSOC; vSIN_CIRCLE;
    vREAL_ADD_ASSOC; vSIN_CIRCLE; vREAL_ADD_RINV; vREAL_LT_REFL]);;

let%a vCOS_BOUNDS = prove(
  [%q {|!x. --(&1) <= cos(x) /\ cos(x) <= &1|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vABS_BOUNDS; vCOS_BOUND]);;

let%a vSIN_COS_ADD = prove(
  [%q {|!x y. ((sin(x + y) - ((sin(x) * cos(y)) + (cos(x) * sin(y)))) pow 2) +
         ((cos(x + y) - ((cos(x) * cos(y)) - (sin(x) * sin(y)))) pow 2) = &0|} ],
  vREPEAT vGEN_TAC ---->
  vCONV_TAC(vLAND_CONV(vX_BETA_CONV [%q {|x:real|} ])) ---->
  vW(vC vSUBGOAL_THEN (vSUBST1_TAC -| vSYM) -| subst[[%q {|&0|} ],[%q {|x:real|} ]] -| snd) ++-->
   [vBETA_TAC ----> vREWRITE_TAC[vSIN_0; vCOS_0] ---->
    vREWRITE_TAC[vREAL_ADD_LID; vREAL_MUL_LZERO; vREAL_MUL_LID] ---->
    vREWRITE_TAC[vREAL_SUB_RZERO; vREAL_SUB_REFL] ---->
    vREWRITE_TAC[num_CONV [%q {|2|} ]; vPOW_0; vREAL_ADD_LID];
    vMATCH_MP_TAC vDIFF_ISCONST_ALL ----> vGEN_TAC ---->
    vW(vMP_TAC -| vDIFF_CONV -| rand -| funpow 2 rator -| snd) ---->
    vNUM_REDUCE_TAC ----> vREWRITE_TAC[vPOW_1] ---->
    vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_RID; vREAL_MUL_RID] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x:real|} ]) ---->
    vMATCH_MP_TAC vEQ_IMP ----> vAP_THM_TAC ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[vGSYM vREAL_NEG_LMUL] ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_EQ_SUB_LADD] ---->
    vREWRITE_TAC[vREAL_SUB_LZERO; vGSYM vREAL_MUL_ASSOC] ---->
    vREWRITE_TAC[vREAL_NEG_RMUL] ----> vAP_TERM_TAC ---->
    vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ----> vBINOP_TAC ++-->
     [vREWRITE_TAC[real_sub; vREAL_NEG_ADD; vREAL_NEG_NEG; vREAL_NEG_RMUL];
      vREWRITE_TAC[vGSYM vREAL_NEG_RMUL; vGSYM real_sub]]]);;

let%a vSIN_COS_NEG = prove(
  [%q {|!x. ((sin(--x) + (sin x)) pow 2) +
       ((cos(--x) - (cos x)) pow 2) = &0|} ],
  vGEN_TAC ----> vCONV_TAC(vLAND_CONV(vX_BETA_CONV [%q {|x:real|} ])) ---->
  vW(vC vSUBGOAL_THEN (vSUBST1_TAC -| vSYM) -| subst[[%q {|&0|} ],[%q {|x:real|} ]] -| snd) ++-->
   [vBETA_TAC ----> vREWRITE_TAC[vSIN_0; vCOS_0; vREAL_NEG_0] ---->
    vREWRITE_TAC[vREAL_ADD_LID; vREAL_SUB_REFL] ---->
    vREWRITE_TAC[num_CONV [%q {|2|} ]; vPOW_0; vREAL_ADD_LID];
    vMATCH_MP_TAC vDIFF_ISCONST_ALL ----> vGEN_TAC ---->
    vW(vMP_TAC -| vDIFF_CONV -| rand -| funpow 2 rator -| snd) ---->
    vNUM_REDUCE_TAC ----> vREWRITE_TAC[vPOW_1] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x:real|} ]) ---->
    vMATCH_MP_TAC vEQ_IMP ----> vAP_THM_TAC ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[vGSYM vREAL_NEG_RMUL] ---->
    vREWRITE_TAC[vREAL_MUL_RID; real_sub; vREAL_NEG_NEG; vGSYM vREAL_MUL_ASSOC] ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_EQ_SUB_LADD] ---->
    vREWRITE_TAC[vREAL_SUB_LZERO; vREAL_NEG_RMUL] ----> vAP_TERM_TAC ---->
    vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
    vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vREAL_NEG_RMUL] ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vREAL_NEG_ADD; vREAL_NEG_NEG]]);;

let%a vSIN_ADD = prove(
  [%q {|!x y. sin(x + y) = (sin(x) * cos(y)) + (cos(x) * sin(y))|} ],
  vREPEAT vGEN_TAC ----> vMP_TAC(vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vSIN_COS_ADD) ---->
  vREWRITE_TAC[vPOW_2; vREAL_SUMSQ] ----> vREWRITE_TAC[vREAL_SUB_0] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[th]));;

let%a vCOS_ADD = prove(
  [%q {|!x y. cos(x + y) = (cos(x) * cos(y)) - (sin(x) * sin(y))|} ],
  vREPEAT vGEN_TAC ----> vMP_TAC(vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vSIN_COS_ADD) ---->
  vREWRITE_TAC[vPOW_2; vREAL_SUMSQ] ----> vREWRITE_TAC[vREAL_SUB_0] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[th]));;

let%a vSIN_NEG = prove(
  [%q {|!x. sin(--x) = --(sin(x))|} ],
  vGEN_TAC ----> vMP_TAC(vSPEC [%q {|x:real|} ] vSIN_COS_NEG) ---->
  vREWRITE_TAC[vPOW_2; vREAL_SUMSQ] ----> vREWRITE_TAC[vREAL_LNEG_UNIQ] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[th]));;

let%a vCOS_NEG = prove(
  [%q {|!x. cos(--x) = cos(x)|} ],
  vGEN_TAC ----> vMP_TAC(vSPEC [%q {|x:real|} ] vSIN_COS_NEG) ---->
  vREWRITE_TAC[vPOW_2; vREAL_SUMSQ] ----> vREWRITE_TAC[vREAL_SUB_0] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[th]));;

let%a vSIN_DOUBLE = prove(
  [%q {|!x. sin(&2 * x) = &2 * sin(x) * cos(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_DOUBLE; vSIN_ADD] ---->
  vAP_TERM_TAC ----> vMATCH_ACCEPT_TAC vREAL_MUL_SYM);;

let%a vCOS_DOUBLE = prove(
  [%q {|!x. cos(&2 * x) = (cos(x) pow 2) - (sin(x) pow 2)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_DOUBLE; vCOS_ADD; vPOW_2]);;

let%a vCOS_ABS = prove
 ([%q {|!x. cos(abs x) = cos(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_abs] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vCOS_NEG]);;

(* ------------------------------------------------------------------------ *)
(* Show that there's a least positive x with cos(x) = 0; hence define pi    *)
(* ------------------------------------------------------------------------ *)

let%a vSIN_PAIRED = prove(
  [%q {|!x. (\n. (((--(&1)) pow n) / &(FACT((2 * n) + 1)))
         * (x pow ((2 * n) + 1))) sums (sin x)|} ],
  vGEN_TAC ----> vMP_TAC(vSPEC [%q {|x:real|} ] vSIN_CONVERGES) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUM_SUMMABLE) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_PAIR) ----> vREWRITE_TAC[vGSYM sin] ---->
  vBETA_TAC ----> vREWRITE_TAC[vSUM_2] ----> vBETA_TAC ---->
  vREWRITE_TAC[vGSYM vADD1; vEVEN_DOUBLE;
              vREWRITE_RULE[vGSYM vNOT_EVEN] vODD_DOUBLE] ---->
  vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_LID; vSUC_SUB1; vMULT_DIV_2]);;

let%a vSIN_POS = prove(
  [%q {|!x. &0 < x /\ x < &2 ==> &0 < sin(x)|} ],
  vGEN_TAC ----> vSTRIP_TAC ----> vMP_TAC(vSPEC [%q {|x:real|} ] vSIN_PAIRED) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUM_SUMMABLE) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_PAIR) ---->
  vREWRITE_TAC[vSYM(vMATCH_MP vSUM_UNIQ (vSPEC [%q {|x:real|} ] vSIN_PAIRED))] ---->
  vREWRITE_TAC[vSUM_2] ----> vBETA_TAC ----> vREWRITE_TAC[vGSYM vADD1] ---->
  vREWRITE_TAC[pow; vGSYM vREAL_NEG_MINUS1; vPOW_MINUS1] ---->
  vREWRITE_TAC[real_div; vGSYM vREAL_NEG_LMUL; vGSYM real_sub] ---->
  vREWRITE_TAC[vREAL_MUL_LID] ----> vREWRITE_TAC[vADD1] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP vSUM_UNIQ) ---->
  vW(vC vSUBGOAL_THEN vSUBST1_TAC -| curry mk_eq [%q {|&0|} ] -| curry mk_comb [%q {|sum(0,0)|} ] -|
  funpow 2 rand -| snd) ++--> [vREWRITE_TAC[sum]; vALL_TAC] ---->
  vMATCH_MP_TAC vSER_POS_LT ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vSUM_SUMMABLE th]) ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_THEN(vK vALL_TAC) ----> vBETA_TAC ---->
  vREWRITE_TAC[vGSYM vADD1; vMULT_CLAUSES] ---->
  vREWRITE_TAC[num_CONV [%q {|2|} ]; vADD_CLAUSES; pow; vFACT; vGSYM vREAL_MUL] ---->
  vREWRITE_TAC[vSYM(num_CONV [%q {|2|} ])] ---->
  vREWRITE_TAC[num_CONV [%q {|1|} ]; vADD_CLAUSES; pow; vFACT; vGSYM vREAL_MUL] ---->
  vREWRITE_TAC[vREAL_SUB_LT] ----> vONCE_REWRITE_TAC[vGSYM pow] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vMATCH_MP_TAC vREAL_LT_RMUL_IMP ----> vCONJ_TAC ++-->
   [vALL_TAC; vMATCH_MP_TAC vPOW_POS_LT ----> vASM_REWRITE_TAC[]] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC; vGSYM vPOW_2] ---->
  vSUBGOAL_THEN [%q {|!n. &0 < &(SUC n)|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vREWRITE_TAC[vREAL_LT; vLT_0]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!n. &0 < &(FACT n)|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vREWRITE_TAC[vREAL_LT; vFACT_LT]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!n. ~(&(SUC n) = &0)|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vREWRITE_TAC[vREAL_INJ; vNOT_SUC]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!n. ~(&(FACT n) = &0)|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
    vREWRITE_TAC[vREAL_LT; vFACT_LT]; vALL_TAC] ---->
  vREPEAT(vIMP_SUBST_TAC vREAL_INV_MUL_WEAK ----> vASM_REWRITE_TAC[vREAL_ENTIRE]) ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
    [%q {|a * b * c * d * e = (a * b * e) * (c * d)|} ]] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
  vMATCH_MP_TAC vREAL_LT_RMUL_IMP ----> vCONJ_TAC ++-->
   [vALL_TAC; vMATCH_MP_TAC vREAL_LT_MUL ----> vCONJ_TAC ---->
    vMATCH_MP_TAC vREAL_INV_POS ----> vASM_REWRITE_TAC[]] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vIMP_SUBST_TAC ((vCONV_RULE(vRAND_CONV vSYM_CONV) -| vSPEC_ALL) vREAL_INV_MUL_WEAK) ---->
  vASM_REWRITE_TAC[vREAL_ENTIRE] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vGSYM real_div] ----> vMATCH_MP_TAC vREAL_LT_1 ---->
  vREWRITE_TAC[vPOW_2] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LE_MUL ----> vCONJ_TAC;
    vMATCH_MP_TAC vREAL_LT_MUL2_ALT ----> vREPEAT vCONJ_TAC] ---->
  vTRY(vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[] ----> vNO_TAC) ++-->
   [vW((---->) (vMATCH_MP_TAC vREAL_LT_TRANS) -| vEXISTS_TAC -|
      curry mk_comb [%q {|&|} ] -| funpow 3 rand -| snd) ---->
    vREWRITE_TAC[vREAL_LT; vLESS_SUC_REFL]; vALL_TAC] ---->
  vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|&2|} ] ---->
  vASM_REWRITE_TAC[] ----> vCONV_TAC(vREDEPTH_CONV num_CONV) ---->
  vREWRITE_TAC[vREAL_LE; vLE_SUC; vLE_0]);;

let%a vCOS_PAIRED = prove(
  [%q {|!x. (\n. (((--(&1)) pow n) / &(FACT(2 * n)))
         * (x pow (2 * n))) sums (cos x)|} ],
  vGEN_TAC ----> vMP_TAC(vSPEC [%q {|x:real|} ] vCOS_CONVERGES) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUM_SUMMABLE) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_PAIR) ----> vREWRITE_TAC[vGSYM cos] ---->
  vBETA_TAC ----> vREWRITE_TAC[vSUM_2] ----> vBETA_TAC ---->
  vREWRITE_TAC[vGSYM vADD1; vEVEN_DOUBLE;
              vREWRITE_RULE[vGSYM vNOT_EVEN] vODD_DOUBLE] ---->
  vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_RID; vMULT_DIV_2]);;

let%a vCOS_2 = prove(
  [%q {|cos(&2) < &0|} ],
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_NEG_LT0] ----> vMP_TAC(vSPEC [%q {|&2|} ] vCOS_PAIRED) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_NEG) ----> vBETA_TAC ---->
  vDISCH_TAC ----> vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP vSUM_UNIQ) ---->
  vMATCH_MP_TAC vREAL_LT_TRANS ---->
  vEXISTS_TAC [%q {|sum(0,3) (\n. --((((--(&1)) pow n) / &(FACT(2 * n)))
                * (&2 pow (2 * n))))|} ] ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[num_CONV [%q {|3|} ]; sum; vSUM_2] ----> vBETA_TAC ---->
    vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; pow; vFACT] ---->
    vREWRITE_TAC[vREAL_MUL_RID; vPOW_1; vPOW_2; vGSYM vREAL_NEG_RMUL] ---->
    vIMP_SUBST_TAC vREAL_DIV_REFL ----> vREWRITE_TAC[vREAL_NEG_NEG; vREAL_10] ---->
    vNUM_REDUCE_TAC ----> vREWRITE_TAC[num_CONV [%q {|4|} ]; num_CONV [%q {|3|} ]; vFACT; pow] ---->
    vREWRITE_TAC[vSYM(num_CONV [%q {|4|} ]); vSYM(num_CONV [%q {|3|} ])] ---->
    vREWRITE_TAC[num_CONV [%q {|2|} ]; num_CONV [%q {|1|} ]; vFACT; pow] ---->
    vREWRITE_TAC[vSYM(num_CONV [%q {|1|} ]); vSYM(num_CONV [%q {|2|} ])] ---->
    vREWRITE_TAC[vREAL_MUL] ----> vNUM_REDUCE_TAC ---->
    vREWRITE_TAC[real_div; vREAL_NEG_LMUL; vREAL_NEG_NEG; vREAL_MUL_LID] ---->
    vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vREAL_ADD_ASSOC] ---->
    vREWRITE_TAC[vGSYM real_sub; vREAL_SUB_LT] ---->
    vSUBGOAL_THEN [%q {|inv(&2) * &4 = &1 + &1|} ] vSUBST1_TAC ++-->
     [vMATCH_MP_TAC vREAL_EQ_LMUL_IMP ----> vEXISTS_TAC [%q {|&2|} ] ---->
      vREWRITE_TAC[vREAL_INJ] ----> vNUM_REDUCE_TAC ---->
      vREWRITE_TAC[vREAL_ADD; vREAL_MUL] ----> vNUM_REDUCE_TAC ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
      vSUBGOAL_THEN [%q {|&2 * inv(&2) = &1|} ] vSUBST1_TAC ---->
      vREWRITE_TAC[vREAL_MUL_LID] ----> vMATCH_MP_TAC vREAL_MUL_RINV ---->
      vREWRITE_TAC[vREAL_INJ] ----> vNUM_REDUCE_TAC;
      vREWRITE_TAC[vREAL_MUL_LID; vREAL_ADD_ASSOC] ---->
      vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID] ---->
      vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vGSYM real_div] ---->
      vMATCH_MP_TAC vREAL_LT_1 ----> vREWRITE_TAC[vREAL_LE; vREAL_LT] ---->
      vNUM_REDUCE_TAC]; vALL_TAC] ---->
  vMATCH_MP_TAC vSER_POS_LT_PAIR ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vSUM_SUMMABLE th]) ---->
  vX_GEN_TAC [%q {|d:num|} ] ----> vBETA_TAC ---->
  vREWRITE_TAC[vPOW_ADD; vPOW_MINUS1; vREAL_MUL_RID] ---->
  vREWRITE_TAC[num_CONV [%q {|3|} ]; pow] ----> vREWRITE_TAC[vSYM(num_CONV [%q {|3|} ])] ---->
  vREWRITE_TAC[vPOW_2; vPOW_1] ---->
  vREWRITE_TAC[vGSYM vREAL_NEG_MINUS1; vREAL_NEG_NEG] ---->
  vREWRITE_TAC[real_div; vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL] ---->
  vREWRITE_TAC[vREAL_MUL_LID; vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vGSYM real_sub; vREAL_SUB_LT] ---->
  vREWRITE_TAC[vGSYM vADD1; vADD_CLAUSES; vMULT_CLAUSES] ---->
  vREWRITE_TAC[vPOW_ADD; vREAL_MUL_ASSOC] ---->
  vMATCH_MP_TAC vREAL_LT_RMUL_IMP ----> vCONJ_TAC ++-->
   [vALL_TAC;
    vREWRITE_TAC[num_CONV [%q {|2|} ]; vMULT_CLAUSES] ---->
    vREWRITE_TAC[num_CONV [%q {|3|} ]; vADD_CLAUSES] ---->
    vMATCH_MP_TAC vPOW_POS_LT ----> vREWRITE_TAC[vREAL_LT] ---->
    vNUM_REDUCE_TAC] ---->
  vREWRITE_TAC[num_CONV [%q {|2|} ]; vADD_CLAUSES; vFACT] ---->
  vREWRITE_TAC[vSYM(num_CONV [%q {|2|} ])] ---->
  vREWRITE_TAC[num_CONV [%q {|1|} ]; vADD_CLAUSES; vFACT] ---->
  vREWRITE_TAC[vSYM(num_CONV [%q {|1|} ])] ---->
  vSUBGOAL_THEN [%q {|!n. &0 < &(SUC n)|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vREWRITE_TAC[vREAL_LT; vLT_0]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!n. &0 < &(FACT n)|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vREWRITE_TAC[vREAL_LT; vFACT_LT]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!n. ~(&(SUC n) = &0)|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vREWRITE_TAC[vREAL_INJ; vNOT_SUC]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!n. ~(&(FACT n) = &0)|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
    vREWRITE_TAC[vREAL_LT; vFACT_LT]; vALL_TAC] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL] ---->
  vREPEAT(vIMP_SUBST_TAC vREAL_INV_MUL_WEAK ----> vASM_REWRITE_TAC[vREAL_ENTIRE]) ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
    [%q {|a * b * c * d = (a * b * d) * c|} ]] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
  vMATCH_MP_TAC vREAL_LT_RMUL_IMP ----> vCONJ_TAC ++-->
   [vALL_TAC;
    vMATCH_MP_TAC vREAL_INV_POS ----> vREWRITE_TAC[vREAL_LT; vFACT_LT]] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vIMP_SUBST_TAC ((vCONV_RULE(vRAND_CONV vSYM_CONV) -| vSPEC_ALL) vREAL_INV_MUL_WEAK) ---->
  vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vGSYM real_div] ----> vMATCH_MP_TAC vREAL_LT_1 ---->
  vREWRITE_TAC[vPOW_2; vREAL_MUL; vREAL_LE; vREAL_LT] ----> vNUM_REDUCE_TAC ---->
  vREWRITE_TAC[num_CONV [%q {|4|} ]; num_CONV [%q {|3|} ]; vMULT_CLAUSES; vADD_CLAUSES] ---->
  vREWRITE_TAC[vLT_SUC] ---->
  vREWRITE_TAC[num_CONV [%q {|2|} ]; vADD_CLAUSES; vMULT_CLAUSES] ---->
  vREWRITE_TAC[num_CONV [%q {|1|} ]; vLT_SUC; vLT_0]);;

let%a vCOS_ISZERO = prove(
  [%q {|?!x. &0 <= x /\ x <= &2 /\ (cos x = &0)|} ],
  vREWRITE_TAC[vEXISTS_UNIQUE_DEF] ----> vBETA_TAC ---->
  vW(vC vSUBGOAL_THEN vASSUME_TAC -| hd -| conjuncts -| snd) ++-->
   [vMATCH_MP_TAC vIVT2 ----> vREPEAT vCONJ_TAC ++-->
     [vREWRITE_TAC[vREAL_LE; vLE_0];
      vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vACCEPT_TAC vCOS_2;
      vREWRITE_TAC[vCOS_0; vREAL_LE_01];
      vX_GEN_TAC [%q {|x:real|} ] ----> vDISCH_THEN(vK vALL_TAC) ---->
      vMATCH_MP_TAC vDIFF_CONT ----> vEXISTS_TAC [%q {|--(sin x)|} ] ---->
      vREWRITE_TAC[vDIFF_COS]];
    vASM_REWRITE_TAC[] ----> vBETA_TAC ---->
    vMAP_EVERY vX_GEN_TAC [[%q {|x1:real|} ]; [%q {|x2:real|} ]] ---->
    vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
    vPURE_REWRITE_TAC[vNOT_IMP] ----> vREWRITE_TAC[] ----> vSTRIP_TAC ---->
    vMP_TAC(vSPECL [[%q {|x1:real|} ]; [%q {|x2:real|} ]] vREAL_LT_TOTAL) ---->
    vSUBGOAL_THEN [%q {|(!x. cos differentiable x) /\
                  (!x. cos contl x)|} ] vSTRIP_ASSUME_TAC ++-->
     [vCONJ_TAC ----> vGEN_TAC ++-->
       [vREWRITE_TAC[differentiable]; vMATCH_MP_TAC vDIFF_CONT] ---->
      vEXISTS_TAC [%q {|--(sin x)|} ] ----> vREWRITE_TAC[vDIFF_COS]; vALL_TAC] ---->
    vASM_REWRITE_TAC[] ----> vDISCH_THEN vDISJ_CASES_TAC ++-->
     [vMP_TAC(vSPECL [[%q {|cos|} ]; [%q {|x1:real|} ]; [%q {|x2:real|} ]] vROLLE);
      vMP_TAC(vSPECL [[%q {|cos|} ]; [%q {|x2:real|} ]; [%q {|x1:real|} ]] vROLLE)] ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vMP_TAC) ----> vREWRITE_TAC[vCONJ_ASSOC] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vSTRIP_ASSUME_TAC vMP_TAC) ---->
    vDISCH_THEN(vMP_TAC -| vCONJ(vSPEC [%q {|x:real|} ] vDIFF_COS)) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_UNIQ) ---->
    vREWRITE_TAC[vREAL_NEG_EQ0] ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
    vMATCH_MP_TAC vSIN_POS ++-->
     [vCONJ_TAC ++-->
       [vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x1:real|} ] ---->
        vASM_REWRITE_TAC[];
        vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|x2:real|} ] ---->
        vASM_REWRITE_TAC[]];
      vCONJ_TAC ++-->
       [vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x2:real|} ] ---->
        vASM_REWRITE_TAC[];
        vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|x1:real|} ] ---->
        vASM_REWRITE_TAC[]]]]);;

let pi = new_definition
  [%q {|pi = &2 * @x. &0 <= x /\ x <= &2 /\ (cos x = &0)|} ];;

(* ------------------------------------------------------------------------ *)
(* Periodicity and related properties of the trig functions                 *)
(* ------------------------------------------------------------------------ *)

let%a vPI2 = prove(
  [%q {|pi / &2 = @x. &0 <= x /\ x <= &2 /\ (cos(x) = &0)|} ],
  vREWRITE_TAC[pi; real_div] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
    [%q {|(a * b) * c = (c * a) * b|} ]] ---->
  vIMP_SUBST_TAC vREAL_MUL_LINV ----> vREWRITE_TAC[vREAL_INJ] ---->
  vNUM_REDUCE_TAC ----> vREWRITE_TAC[vREAL_MUL_LID]);;

let%a vCOS_PI2 = prove(
  [%q {|cos(pi / &2) = &0|} ],
  vMP_TAC(vSELECT_RULE (vEXISTENCE vCOS_ISZERO)) ---->
  vREWRITE_TAC[vGSYM vPI2] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[th]));;

let%a vPI2_BOUNDS = prove(
  [%q {|&0 < (pi / &2) /\ (pi / &2) < &2|} ],
  vMP_TAC(vSELECT_RULE (vEXISTENCE vCOS_ISZERO)) ---->
  vREWRITE_TAC[vGSYM vPI2] ----> vDISCH_TAC ---->
  vASM_REWRITE_TAC[vREAL_LT_LE] ----> vCONJ_TAC ++-->
   [vDISCH_TAC ----> vMP_TAC vCOS_0 ----> vASM_REWRITE_TAC[] ---->
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vGSYM vREAL_10];
    vDISCH_TAC ----> vMP_TAC vCOS_PI2 ----> vFIRST_ASSUM vSUBST1_TAC ---->
    vREWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
    vMATCH_ACCEPT_TAC vCOS_2]);;

let%a vPI_POS = prove(
  [%q {|&0 < pi|} ],
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_HALF_DOUBLE] ---->
  vMATCH_MP_TAC vREAL_LT_ADD ----> vREWRITE_TAC[vPI2_BOUNDS]);;

let%a vSIN_PI2 = prove(
  [%q {|sin(pi / &2) = &1|} ],
  vMP_TAC(vSPEC [%q {|pi / &2|} ] vSIN_CIRCLE) ---->
  vREWRITE_TAC[vCOS_PI2; vPOW_2; vREAL_MUL_LZERO; vREAL_ADD_RID] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vREAL_MUL_LID] ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_SUB_0] ---->
  vREWRITE_TAC[vGSYM vREAL_DIFFSQ; vREAL_ENTIRE] ---->
  vDISCH_THEN vDISJ_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM vMP_TAC ----> vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_THEN(vK vALL_TAC) ---->
  vREWRITE_TAC[vREAL_LNEG_UNIQ] ----> vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|(--)|} ]) ---->
  vREWRITE_TAC[vREAL_NEG_NEG] ----> vDISCH_TAC ---->
  vMP_TAC vREAL_LT_01 ----> vPOP_ASSUM(vSUBST1_TAC -| vSYM) ---->
  vREWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_GT ---->
  vREWRITE_TAC[vREAL_NEG_LT0] ----> vMATCH_MP_TAC vSIN_POS ---->
  vREWRITE_TAC[vPI2_BOUNDS]);;

let%a vCOS_PI = prove(
  [%q {|cos(pi) = --(&1)|} ],
  vMP_TAC(vSPECL [[%q {|pi / &2|} ]; [%q {|pi / &2|} ]] vCOS_ADD) ---->
  vREWRITE_TAC[vSIN_PI2; vCOS_PI2; vREAL_MUL_LZERO; vREAL_MUL_LID] ---->
  vREWRITE_TAC[vREAL_SUB_LZERO] ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vAP_TERM_TAC ----> vREWRITE_TAC[vREAL_DOUBLE] ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_LMUL ---->
  vREWRITE_TAC[vREAL_INJ] ----> vNUM_REDUCE_TAC);;

let%a vSIN_PI = prove(
  [%q {|sin(pi) = &0|} ],
  vMP_TAC(vSPECL [[%q {|pi / &2|} ]; [%q {|pi / &2|} ]] vSIN_ADD) ---->
  vREWRITE_TAC[vCOS_PI2; vREAL_MUL_LZERO; vREAL_MUL_RZERO; vREAL_ADD_LID] ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vAP_TERM_TAC ---->
  vREWRITE_TAC[vREAL_DOUBLE] ----> vCONV_TAC vSYM_CONV ---->
  vMATCH_MP_TAC vREAL_DIV_LMUL ---->
  vREWRITE_TAC[vREAL_INJ] ----> vNUM_REDUCE_TAC);;

let%a vSIN_COS = prove(
  [%q {|!x. sin(x) = cos((pi / &2) - x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_sub; vCOS_ADD] ---->
  vREWRITE_TAC[vSIN_PI2; vCOS_PI2; vREAL_MUL_LZERO] ---->
  vREWRITE_TAC[vREAL_ADD_LID; vREAL_MUL_LID] ---->
  vREWRITE_TAC[vSIN_NEG; vREAL_NEG_NEG]);;

let%a vCOS_SIN = prove(
  [%q {|!x. cos(x) = sin((pi / &2) - x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_sub; vSIN_ADD] ---->
  vREWRITE_TAC[vSIN_PI2; vCOS_PI2; vREAL_MUL_LZERO] ---->
  vREWRITE_TAC[vREAL_MUL_LID; vREAL_ADD_RID] ---->
  vREWRITE_TAC[vCOS_NEG]);;

let%a vSIN_PERIODIC_PI = prove(
  [%q {|!x. sin(x + pi) = --(sin(x))|} ],
  vGEN_TAC ----> vREWRITE_TAC[vSIN_ADD; vSIN_PI; vCOS_PI] ---->
  vREWRITE_TAC[vREAL_MUL_RZERO; vREAL_ADD_RID; vGSYM vREAL_NEG_RMUL] ---->
  vREWRITE_TAC[vREAL_MUL_RID]);;

let%a vCOS_PERIODIC_PI = prove(
  [%q {|!x. cos(x + pi) = --(cos(x))|} ],
  vGEN_TAC ----> vREWRITE_TAC[vCOS_ADD; vSIN_PI; vCOS_PI] ---->
  vREWRITE_TAC[vREAL_MUL_RZERO; vREAL_SUB_RZERO; vGSYM vREAL_NEG_RMUL] ---->
  vREWRITE_TAC[vREAL_MUL_RID]);;

let%a vSIN_PERIODIC = prove(
  [%q {|!x. sin(x + (&2 * pi)) = sin(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_DOUBLE; vREAL_ADD_ASSOC] ---->
  vREWRITE_TAC[vSIN_PERIODIC_PI; vREAL_NEG_NEG]);;

let%a vCOS_PERIODIC = prove(
  [%q {|!x. cos(x + (&2 * pi)) = cos(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_DOUBLE; vREAL_ADD_ASSOC] ---->
  vREWRITE_TAC[vCOS_PERIODIC_PI; vREAL_NEG_NEG]);;

let%a vCOS_NPI = prove(
  [%q {|!n. cos(&n * pi) = --(&1) pow n|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[vREAL_MUL_LZERO; vCOS_0; pow] ---->
  vREWRITE_TAC[vADD1; vGSYM vREAL_ADD; vREAL_RDISTRIB; vCOS_ADD] ---->
  vREWRITE_TAC[vREAL_MUL_LID; vSIN_PI; vREAL_MUL_RZERO; vREAL_SUB_RZERO] ---->
  vASM_REWRITE_TAC[vCOS_PI] ---->
  vMATCH_ACCEPT_TAC vREAL_MUL_SYM);;

let%a vSIN_NPI = prove(
  [%q {|!n. sin(&n * pi) = &0|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[vREAL_MUL_LZERO; vSIN_0; pow] ---->
  vREWRITE_TAC[vADD1; vGSYM vREAL_ADD; vREAL_RDISTRIB; vSIN_ADD] ---->
  vREWRITE_TAC[vREAL_MUL_LID; vSIN_PI; vREAL_MUL_RZERO; vREAL_ADD_RID] ---->
  vASM_REWRITE_TAC[vREAL_MUL_LZERO]);;

let%a vSIN_POS_PI2 = prove(
  [%q {|!x. &0 < x /\ x < pi / &2 ==> &0 < sin(x)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vSIN_POS ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_TRANS ---->
  vEXISTS_TAC [%q {|pi / &2|} ] ----> vASM_REWRITE_TAC[vPI2_BOUNDS]);;

let%a vCOS_POS_PI2 = prove(
  [%q {|!x. &0 < x /\ x < pi / &2 ==> &0 < cos(x)|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
  vPURE_REWRITE_TAC[vREAL_NOT_LT] ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|cos|} ]; [%q {|&0|} ]; [%q {|x:real|} ]; [%q {|&0|} ]] vIVT2) ---->
  vASM_REWRITE_TAC[vCOS_0; vREAL_LE_01; vNOT_IMP] ----> vREPEAT vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
    vX_GEN_TAC [%q {|z:real|} ] ----> vDISCH_THEN(vK vALL_TAC) ---->
    vMATCH_MP_TAC vDIFF_CONT ----> vEXISTS_TAC [%q {|--(sin z)|} ] ---->
    vREWRITE_TAC[vDIFF_COS];
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|z:real|} ]) ---->
    vMP_TAC(vCONJUNCT2 (vCONV_RULE vEXISTS_UNIQUE_CONV vCOS_ISZERO)) ---->
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|z:real|} ]; [%q {|pi / &2|} ]]) ---->
    vASM_REWRITE_TAC[vCOS_PI2] ----> vREWRITE_TAC[vNOT_IMP] ---->
    vREPEAT vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
      vEXISTS_TAC [%q {|pi / &2|} ] ----> vASM_REWRITE_TAC[] ----> vCONJ_TAC;
      vALL_TAC;
      vALL_TAC;
      vDISCH_THEN vSUBST_ALL_TAC ----> vUNDISCH_TAC [%q {|x < pi / &2|} ] ---->
      vASM_REWRITE_TAC[vREAL_NOT_LT]] ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[vPI2_BOUNDS]]);;

let%a vCOS_POS_PI = prove(
  [%q {|!x. --(pi / &2) < x /\ x < pi / &2 ==> &0 < cos(x)|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC
        (vSPECL [[%q {|x:real|} ]; [%q {|&0|} ]] vREAL_LT_TOTAL) ++-->
   [vASM_REWRITE_TAC[vCOS_0; vREAL_LT_01];
    vONCE_REWRITE_TAC[vGSYM vCOS_NEG] ----> vMATCH_MP_TAC vCOS_POS_PI2 ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_NEG_LT0] ----> vASM_REWRITE_TAC[vREAL_NEG_NEG] ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_LT_NEG2] ----> vASM_REWRITE_TAC[vREAL_NEG_NEG];
    vMATCH_MP_TAC vCOS_POS_PI2 ----> vASM_REWRITE_TAC[]]);;

let%a vSIN_POS_PI = prove(
  [%q {|!x. &0 < x /\ x < pi ==> &0 < sin(x)|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vREWRITE_TAC[vSIN_COS] ----> vONCE_REWRITE_TAC[vGSYM vCOS_NEG] ---->
  vREWRITE_TAC[vREAL_NEG_SUB] ---->
  vMATCH_MP_TAC vCOS_POS_PI ---->
  vREWRITE_TAC[vREAL_LT_SUB_LADD; vREAL_LT_SUB_RADD] ---->
  vASM_REWRITE_TAC[vREAL_HALF_DOUBLE; vREAL_ADD_LINV]);;

let%a vSIN_POS_PI_LE = prove
 ([%q {|!x. &0 <= x /\ x <= pi ==> &0 <= sin(x)|} ],
  vREWRITE_TAC[vREAL_LE_LT] ---->
  vMESON_TAC[vSIN_POS_PI; vSIN_PI; vSIN_0; vREAL_LE_REFL]);;

let%a vCOS_TOTAL = prove(
  [%q {|!y. --(&1) <= y /\ y <= &1 ==> ?!x. &0 <= x /\ x <= pi /\ (cos(x) = y)|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vCONV_TAC vEXISTS_UNIQUE_CONV ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vIVT2 ----> vASM_REWRITE_TAC[vCOS_0; vCOS_PI] ---->
    vREWRITE_TAC[vMATCH_MP vREAL_LT_IMP_LE vPI_POS] ---->
    vGEN_TAC ----> vDISCH_THEN(vK vALL_TAC) ---->
    vMATCH_MP_TAC vDIFF_CONT ----> vEXISTS_TAC [%q {|--(sin x)|} ] ---->
    vREWRITE_TAC[vDIFF_COS];
    vMAP_EVERY vX_GEN_TAC [[%q {|x1:real|} ]; [%q {|x2:real|} ]] ----> vSTRIP_TAC ---->
    vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC
         (vSPECL [[%q {|x1:real|} ]; [%q {|x2:real|} ]] vREAL_LT_TOTAL) ++-->
     [vFIRST_ASSUM vACCEPT_TAC;
      vMP_TAC(vSPECL [[%q {|cos|} ]; [%q {|x1:real|} ]; [%q {|x2:real|} ]] vROLLE);
      vMP_TAC(vSPECL [[%q {|cos|} ]; [%q {|x2:real|} ]; [%q {|x1:real|} ]] vROLLE)]] ---->
  vASM_REWRITE_TAC[] ---->
  (vW(vC vSUBGOAL_THEN (fun t -> vREWRITE_TAC[t]) -| funpow 2
                    (fst -| dest_imp) -| snd) ++-->
    [vCONJ_TAC ----> vX_GEN_TAC [%q {|x:real|} ] ----> vDISCH_THEN(vK vALL_TAC) ---->
     vTRY(vMATCH_MP_TAC vDIFF_CONT) ----> vREWRITE_TAC[differentiable] ---->
     vEXISTS_TAC [%q {|--(sin x)|} ] ----> vREWRITE_TAC[vDIFF_COS]; vALL_TAC]) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vSTRIP_ASSUME_TAC) ---->
  vUNDISCH_TAC [%q {|(cos diffl &0)(x)|} ] ---->
  vDISCH_THEN(vMP_TAC -| vCONJ (vSPEC [%q {|x:real|} ] vDIFF_COS)) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_UNIQ) ---->
  vREWRITE_TAC[vREAL_NEG_EQ0] ----> vDISCH_TAC ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vSIN_POS_PI) ---->
  vASM_REWRITE_TAC[vREAL_LT_REFL] ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_THEN(vK vALL_TAC) ---->
  vREWRITE_TAC[] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x1:real|} ];
    vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|x2:real|} ];
    vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x2:real|} ];
    vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|x1:real|} ]] ---->
  vASM_REWRITE_TAC[]);;

let%a vSIN_TOTAL = prove(
  [%q {|!y. --(&1) <= y /\ y <= &1 ==>
        ?!x.  --(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|!x. --(pi / &2) <= x /\ x <= pi / &2 /\ (sin(x) = y) <=>
    &0 <= (x + pi / &2) /\ (x + pi / &2) <= pi /\ (cos(x + pi / &2) = --y)|} ]
  (fun th -> vREWRITE_TAC[th]) ++-->
   [vGEN_TAC ----> vREWRITE_TAC[vCOS_ADD; vSIN_PI2; vCOS_PI2] ---->
    vREWRITE_TAC[vREAL_MUL_RZERO; vREAL_MUL_RZERO; vREAL_MUL_RID] ---->
    vREWRITE_TAC[vREAL_SUB_LZERO] ---->
    vREWRITE_TAC[vGSYM vREAL_LE_SUB_RADD; vGSYM vREAL_LE_SUB_LADD] ---->
    vREWRITE_TAC[vREAL_SUB_LZERO] ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vREAL_EQ_NEG] ----> vAP_THM_TAC ---->
    vREPEAT vAP_TERM_TAC ---->
    vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vGSYM vREAL_HALF_DOUBLE] ---->
    vREWRITE_TAC[vREAL_ADD_SUB]; vALL_TAC] ---->
  vMP_TAC(vSPEC [%q {|--y|} ] vCOS_TOTAL) ----> vASM_REWRITE_TAC[vREAL_LE_NEG2] ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_LE_NEG2] ----> vASM_REWRITE_TAC[vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_LE_NEG2] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vEXISTS_UNIQUE_CONV) ---->
  vDISCH_THEN((---->) vCONJ_TAC -| vMP_TAC) ++-->
   [vDISCH_THEN(vX_CHOOSE_TAC [%q {|x:real|} ] -| vCONJUNCT1) ---->
    vEXISTS_TAC [%q {|x - pi / &2|} ] ----> vASM_REWRITE_TAC[vREAL_SUB_ADD];
    vPOP_ASSUM(vK vALL_TAC) ----> vDISCH_THEN(vASSUME_TAC -| vCONJUNCT2) ---->
    vREPEAT vGEN_TAC ---->
    vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
    vREWRITE_TAC[vREAL_EQ_RADD]]);;

let%a vCOS_ZERO_LEMMA = prove(
  [%q {|!x. &0 <= x /\ (cos(x) = &0) ==>
      ?n. ~EVEN n /\ (x = &n * (pi / &2))|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] (vMATCH_MP vREAL_ARCH_LEAST vPI_POS)) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:num|} ] vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|&0 <= x - &n * pi /\ (x - &n * pi) <= pi /\
                (cos(x - &n * pi) = &0)|} ] vASSUME_TAC ++-->
   [vASM_REWRITE_TAC[vREAL_SUB_LE] ---->
    vREWRITE_TAC[vREAL_LE_SUB_RADD] ---->
    vREWRITE_TAC[real_sub; vCOS_ADD; vSIN_NEG; vCOS_NEG; vSIN_NPI; vCOS_NPI] ---->
    vASM_REWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_LID] ---->
    vREWRITE_TAC[vREAL_NEG_RMUL; vREAL_NEG_NEG; vREAL_MUL_RZERO] ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vUNDISCH_TAC [%q {|x < &(SUC n) * pi|} ] ---->
    vREWRITE_TAC[vADD1] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
    vREWRITE_TAC[vGSYM vREAL_ADD; vREAL_RDISTRIB; vREAL_MUL_LID];
    vMP_TAC(vSPEC [%q {|&0|} ] vCOS_TOTAL) ---->
    vREWRITE_TAC[vREAL_LE_01; vREAL_NEG_LE0] ---->
    vDISCH_THEN(vMP_TAC -| vCONV_RULE vEXISTS_UNIQUE_CONV) ---->
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|x - &n * pi|} ]; [%q {|pi / &2|} ]] -| vCONJUNCT2) ---->
    vASM_REWRITE_TAC[vCOS_PI2] ---->
    vW(vC vSUBGOAL_THEN vMP_TAC -| funpow 2 (fst -| dest_imp) -| snd) ++-->
     [vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vMP_TAC vPI2_BOUNDS ---->
      vREWRITE_TAC[vREAL_LT_HALF1; vREAL_LT_HALF2] ----> vDISCH_TAC ---->
      vASM_REWRITE_TAC[];
      vDISCH_THEN(fun th -> vREWRITE_TAC[th])] ---->
    vREWRITE_TAC[vREAL_EQ_SUB_RADD] ----> vDISCH_TAC ---->
    vEXISTS_TAC [%q {|SUC(2 * n)|} ] ---->
    vREWRITE_TAC[vGSYM vNOT_ODD; vODD_DOUBLE] ---->
    vREWRITE_TAC[vADD1; vGSYM vREAL_ADD; vGSYM vREAL_MUL] ---->
    vREWRITE_TAC[vREAL_RDISTRIB; vREAL_MUL_LID] ---->
    vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vASM_REWRITE_TAC[] ---->
    vAP_TERM_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_RMUL ---->
    vREWRITE_TAC[vREAL_INJ] ----> vNUM_REDUCE_TAC]);;

let%a vSIN_ZERO_LEMMA = prove(
  [%q {|!x. &0 <= x /\ (sin(x) = &0) ==>
        ?n. EVEN n /\ (x = &n * (pi / &2))|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC(vSPEC [%q {|x + pi / &2|} ] vCOS_ZERO_LEMMA) ---->
  vW(vC vSUBGOAL_THEN vMP_TAC -| funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
      vASM_REWRITE_TAC[vREAL_LE_ADDR] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
      vREWRITE_TAC[vPI2_BOUNDS];
      vASM_REWRITE_TAC[vCOS_ADD; vCOS_PI2; vREAL_MUL_LZERO; vREAL_MUL_RZERO] ---->
      vMATCH_ACCEPT_TAC vREAL_SUB_REFL];
    vDISCH_THEN(fun th -> vREWRITE_TAC[th])] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:num|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPEC [%q {|n:num|} ] vODD_EXISTS) ----> vASM_REWRITE_TAC[vGSYM vNOT_EVEN] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:num|} ] vSUBST_ALL_TAC) ---->
  vEXISTS_TAC [%q {|2 * m|} ] ----> vREWRITE_TAC[vEVEN_DOUBLE] ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vGSYM vREAL_EQ_SUB_LADD]) ---->
  vFIRST_ASSUM vSUBST1_TAC ---->
  vREWRITE_TAC[vADD1; vGSYM vREAL_ADD; vREAL_RDISTRIB; vREAL_MUL_LID] ---->
  vREWRITE_TAC[vONCE_REWRITE_RULE[vREAL_ADD_SYM] vREAL_ADD_SUB]);;

let%a vCOS_ZERO = prove(
  [%q {|!x. (cos(x) = &0) <=> (?n. ~EVEN n /\ (x = &n * (pi / &2))) \/
                         (?n. ~EVEN n /\ (x = --(&n * (pi / &2))))|} ],
  vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vDISJ_CASES_TAC (vSPECL [[%q {|&0|} ]; [%q {|x:real|} ]] vREAL_LE_TOTAL) ++-->
     [vDISJ1_TAC ----> vMATCH_MP_TAC vCOS_ZERO_LEMMA ----> vASM_REWRITE_TAC[];
      vDISJ2_TAC ----> vREWRITE_TAC[vGSYM vREAL_NEG_EQ] ---->
      vMATCH_MP_TAC vCOS_ZERO_LEMMA ----> vASM_REWRITE_TAC[vCOS_NEG] ---->
      vONCE_REWRITE_TAC[vGSYM vREAL_LE_NEG2] ---->
      vASM_REWRITE_TAC[vREAL_NEG_NEG; vREAL_NEG_0]];
    vDISCH_THEN(vDISJ_CASES_THEN (vX_CHOOSE_TAC [%q {|n:num|} ])) ---->
    vASM_REWRITE_TAC[vCOS_NEG] ----> vMP_TAC(vSPEC [%q {|n:num|} ] vODD_EXISTS) ---->
    vASM_REWRITE_TAC[vGSYM vNOT_EVEN] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:num|} ] vSUBST1_TAC) ---->
    vREWRITE_TAC[vADD1] ----> vSPEC_TAC([%q {|m:num|} ],[%q {|m:num|} ]) ----> vINDUCT_TAC ---->
    vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vREAL_MUL_LID; vCOS_PI2] ---->
    vREWRITE_TAC[vGSYM vADD_ASSOC] ----> vONCE_REWRITE_TAC[vGSYM vREAL_ADD] ---->
    vREWRITE_TAC[vREAL_RDISTRIB] ----> vREWRITE_TAC[vCOS_ADD] ---->
    vREWRITE_TAC[vGSYM vREAL_DOUBLE; vREAL_HALF_DOUBLE] ---->
    vASM_REWRITE_TAC[vCOS_PI; vSIN_PI; vREAL_MUL_LZERO; vREAL_MUL_RZERO] ---->
    vREWRITE_TAC[vREAL_SUB_RZERO]]);;

let%a vSIN_ZERO = prove(
  [%q {|!x. (sin(x) = &0) <=> (?n. EVEN n /\ (x = &n * (pi / &2))) \/
                         (?n. EVEN n /\ (x = --(&n * (pi / &2))))|} ],
  vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vDISJ_CASES_TAC (vSPECL [[%q {|&0|} ]; [%q {|x:real|} ]] vREAL_LE_TOTAL) ++-->
     [vDISJ1_TAC ----> vMATCH_MP_TAC vSIN_ZERO_LEMMA ----> vASM_REWRITE_TAC[];
      vDISJ2_TAC ----> vREWRITE_TAC[vGSYM vREAL_NEG_EQ] ---->
      vMATCH_MP_TAC vSIN_ZERO_LEMMA ---->
      vASM_REWRITE_TAC[vSIN_NEG; vREAL_NEG_0; vREAL_NEG_GE0]];
    vDISCH_THEN(vDISJ_CASES_THEN (vX_CHOOSE_TAC [%q {|n:num|} ])) ---->
    vASM_REWRITE_TAC[vSIN_NEG; vREAL_NEG_EQ0] ---->
    vMP_TAC(vSPEC [%q {|n:num|} ] vEVEN_EXISTS) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:num|} ] vSUBST1_TAC) ---->
    vREWRITE_TAC[vGSYM vREAL_MUL] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
      [%q {|(a * b) * c = b * (a * c)|} ]] ---->
    vREWRITE_TAC[vGSYM vREAL_DOUBLE; vREAL_HALF_DOUBLE; vSIN_NPI]]);;

let%a vSIN_ZERO_PI = prove
 ([%q {|!x. (sin(x) = &0) <=> (?n. x = &n * pi) \/ (?n. x = --(&n * pi))|} ],
  vGEN_TAC ----> vREWRITE_TAC[vSIN_ZERO; vEVEN_EXISTS] ---->
  vREWRITE_TAC[vLEFT_AND_EXISTS_THM] ---->
  vONCE_REWRITE_TAC[vSWAP_EXISTS_THM] ---->
  vREWRITE_TAC[vUNWIND_THM2] ----> vONCE_REWRITE_TAC[vMULT_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_OF_NUM_MUL] ---->
  vSIMP_TAC[vGSYM vREAL_MUL_ASSOC; vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH]);;

let%a vCOS_ONE_2PI = prove
 ([%q {|!x. (cos(x) = &1) <=> (?n. x = &n * &2 * pi) \/ (?n. x = --(&n * &2 * pi))|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vALL_TAC;
    vSTRIP_TAC ----> vASM_REWRITE_TAC[vCOS_NEG] ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC; vREAL_OF_NUM_MUL; vCOS_NPI] ---->
    vREWRITE_TAC[vREAL_POW_NEG; vEVEN_MULT; vARITH_EVEN; vREAL_POW_ONE]] ---->
  vDISCH_TAC ----> vMP_TAC(vSPEC [%q {|x:real|} ] vSIN_CIRCLE) ---->
  vASM_REWRITE_TAC[vREAL_POW_2; vREAL_MUL_LZERO] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|(x + &1 * &1 = &1) <=> (x = &0)|} ]] ---->
  vREWRITE_TAC[vREAL_ENTIRE] ----> vREWRITE_TAC[vSIN_ZERO_PI] ---->
  vMATCH_MP_TAC(vTAUT [%q {|(a ==> a') /\ (b ==> b') ==> (a \/ b ==> a' \/ b')|} ]) ---->
  vSIMP_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vCONJ_TAC ----> vX_GEN_TAC [%q {|m:num|} ] ----> vDISCH_THEN vSUBST_ALL_TAC ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vREAL_EQ_NEG2; vCOS_NEG] ---->
  vREWRITE_TAC[vCOS_NPI; vREAL_POW_NEG; vREAL_POW_ONE] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC; vREAL_EQ_MUL_RCANCEL] ---->
  vSIMP_TAC[vPI_POS; vREAL_LT_IMP_NZ] ---->
  vREWRITE_TAC[vREAL_OF_NUM_EQ; vREAL_OF_NUM_MUL] ---->
  vONCE_REWRITE_TAC[vMULT_SYM] ----> vREWRITE_TAC[vGSYM vEVEN_EXISTS] ---->
  vCOND_CASES_TAC ----> vCONV_TAC vREAL_RAT_REDUCE_CONV ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Tangent                                                                  *)
(* ------------------------------------------------------------------------ *)

let tan = new_definition
  [%q {|tan(x) = sin(x) / cos(x)|} ];;

let%a vTAN_0 = prove(
  [%q {|tan(&0) = &0|} ],
  vREWRITE_TAC[tan; vSIN_0; vREAL_DIV_LZERO]);;

let%a vTAN_PI = prove(
  [%q {|tan(pi) = &0|} ],
  vREWRITE_TAC[tan; vSIN_PI; vREAL_DIV_LZERO]);;

let%a vTAN_NPI = prove(
  [%q {|!n. tan(&n * pi) = &0|} ],
  vGEN_TAC ----> vREWRITE_TAC[tan; vSIN_NPI; vREAL_DIV_LZERO]);;

let%a vTAN_NEG = prove(
  [%q {|!x. tan(--x) = --(tan x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[tan; vSIN_NEG; vCOS_NEG] ---->
  vREWRITE_TAC[real_div; vREAL_NEG_LMUL]);;

let%a vTAN_PERIODIC = prove(
  [%q {|!x. tan(x + &2 * pi) = tan(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[tan; vSIN_PERIODIC; vCOS_PERIODIC]);;

let%a vTAN_PERIODIC_PI = prove
 ([%q {|!x. tan(x + pi) = tan(x)|} ],
  vREWRITE_TAC[tan; vSIN_PERIODIC_PI; vCOS_PERIODIC_PI;
      real_div; vREAL_INV_NEG; vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG]);;

let%a vTAN_PERIODIC_NPI = prove
 ([%q {|!x n. tan(x + &n * pi) = tan(x)|} ],
  vGEN_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_RID] ---->
  vREWRITE_TAC[vGSYM vREAL_OF_NUM_SUC; vREAL_ADD_RDISTRIB; vREAL_MUL_LID] ---->
  vASM_REWRITE_TAC[vREAL_ADD_ASSOC; vTAN_PERIODIC_PI]);;

let%a vTAN_ADD = prove(
  [%q {|!x y. ~(cos(x) = &0) /\ ~(cos(y) = &0) /\ ~(cos(x + y) = &0) ==>
           (tan(x + y) = (tan(x) + tan(y)) / (&1 - tan(x) * tan(y)))|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ----> vREWRITE_TAC[tan] ---->
  vMP_TAC(vSPECL [[%q {|cos(x) * cos(y)|} ];
                [%q {|&1 - (sin(x) / cos(x)) * (sin(y) / cos(y))|} ]]
         vREAL_DIV_MUL2) ----> vASM_REWRITE_TAC[vREAL_ENTIRE] ---->
  vW(vC vSUBGOAL_THEN vMP_TAC -| funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|(*) (cos(x) * cos(y))|} ]) ---->
    vREWRITE_TAC[real_div; vREAL_SUB_LDISTRIB; vGSYM vREAL_MUL_ASSOC] ---->
    vREWRITE_TAC[vREAL_MUL_RID; vREAL_MUL_RZERO] ---->
    vUNDISCH_TAC [%q {|~(cos(x + y) = &0)|} ] ---->
    vMATCH_MP_TAC vEQ_IMP ---->
    vAP_TERM_TAC ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vCOS_ADD] ----> vAP_TERM_TAC;
    vDISCH_THEN(fun th -> vDISCH_THEN(vMP_TAC -| vC vMATCH_MP th)) ---->
    vDISCH_THEN(fun th -> vONCE_REWRITE_TAC[th]) ----> vBINOP_TAC ++-->
     [vREWRITE_TAC[real_div; vREAL_LDISTRIB; vGSYM vREAL_MUL_ASSOC] ---->
      vREWRITE_TAC[vSIN_ADD] ----> vBINOP_TAC ++-->
       [vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
          [%q {|a * b * c * d = (d * a) * (c * b)|} ]] ---->
        vIMP_SUBST_TAC vREAL_MUL_LINV ----> vASM_REWRITE_TAC[vREAL_MUL_LID];
        vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
          [%q {|a * b * c * d = (d * b) * (a * c)|} ]] ---->
        vIMP_SUBST_TAC vREAL_MUL_LINV ----> vASM_REWRITE_TAC[vREAL_MUL_LID]];
      vREWRITE_TAC[vCOS_ADD; vREAL_SUB_LDISTRIB; vREAL_MUL_RID] ---->
      vAP_TERM_TAC ----> vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC]]] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
    [%q {|a * b * c * d * e * f = (f * b) * (d * a) * (c * e)|} ]] ---->
  vREPEAT(vIMP_SUBST_TAC vREAL_MUL_LINV ----> vASM_REWRITE_TAC[]) ---->
  vREWRITE_TAC[vREAL_MUL_LID]);;

let%a vTAN_DOUBLE = prove(
  [%q {|!x. ~(cos(x) = &0) /\ ~(cos(&2 * x) = &0) ==>
            (tan(&2 * x) = (&2 * tan(x)) / (&1 - (tan(x) pow 2)))|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|x:real|} ]; [%q {|x:real|} ]] vTAN_ADD) ---->
  vASM_REWRITE_TAC[vREAL_DOUBLE; vPOW_2]);;

let%a vTAN_POS_PI2 = prove(
  [%q {|!x. &0 < x /\ x < pi / &2 ==> &0 < tan(x)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[tan; real_div] ---->
  vMATCH_MP_TAC vREAL_LT_MUL ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSIN_POS_PI2;
    vMATCH_MP_TAC vREAL_INV_POS ----> vMATCH_MP_TAC vCOS_POS_PI2] ---->
  vASM_REWRITE_TAC[]);;

let%a vDIFF_TAN = prove(
  [%q {|!x. ~(cos(x) = &0) ==> (tan diffl inv(cos(x) pow 2))(x)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vMP_TAC(vDIFF_CONV [%q {|\x. sin(x) / cos(x)|} ]) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x:real|} ]) ----> vASM_REWRITE_TAC[vREAL_MUL_RID] ---->
  vREWRITE_TAC[vGSYM tan; vGSYM vREAL_NEG_LMUL; vREAL_NEG_NEG; real_sub] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vREWRITE_TAC[vGSYM vPOW_2; vSIN_CIRCLE; vGSYM vREAL_INV_1OVER]);;

let vDIFF_TAN_COMPOSITE = prove
 ([%q {|(g diffl m)(x) /\ ~(cos(g x) = &0)
   ==> ((\x. tan(g x)) diffl (inv(cos(g x) pow 2) * m))(x)|} ],
  vASM_SIMP_TAC[vDIFF_CHAIN; vDIFF_TAN]) in
add_to_diff_net vDIFF_TAN_COMPOSITE;;

let%a vTAN_TOTAL_LEMMA = prove(
  [%q {|!y. &0 < y ==> ?x. &0 < x /\ x < pi / &2 /\ y < tan(x)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|((\x. cos(x) / sin(x)) tends_real_real &0)(pi / &2)|} ]
  vMP_TAC ++-->
   [vSUBST1_TAC(vSYM(vSPEC [%q {|&1|} ] vREAL_DIV_LZERO)) ---->
    vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ----> vMATCH_MP_TAC vLIM_DIV ---->
    vREWRITE_TAC[vREAL_10] ----> vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ---->
    vSUBST1_TAC(vSYM vCOS_PI2) ----> vSUBST1_TAC(vSYM vSIN_PI2) ---->
    vREWRITE_TAC[vGSYM vCONTL_LIM] ----> vCONJ_TAC ----> vMATCH_MP_TAC vDIFF_CONT ++-->
     [vEXISTS_TAC [%q {|--(sin(pi / &2))|} ];
      vEXISTS_TAC [%q {|cos(pi / &2)|} ]] ---->
    vREWRITE_TAC[vDIFF_SIN; vDIFF_COS]; vALL_TAC] ---->
  vREWRITE_TAC[vLIM] ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|inv(y)|} ]) ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_INV_POS th]) ---->
  vBETA_TAC ----> vREWRITE_TAC[vREAL_SUB_RZERO] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|d:real|} ]; [%q {|pi / &2|} ]] vREAL_DOWN2) ---->
  vASM_REWRITE_TAC[vPI2_BOUNDS] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|(pi / &2) - e|} ] ----> vASM_REWRITE_TAC[vREAL_SUB_LT] ---->
  vCONJ_TAC ++-->
   [vREWRITE_TAC[real_sub; vGSYM vREAL_NOT_LE; vREAL_LE_ADDR; vREAL_NEG_GE0] ---->
    vASM_REWRITE_TAC[vREAL_NOT_LE]; vALL_TAC] ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|(pi / &2) - e|} ]) ---->
  vREWRITE_TAC[vREAL_SUB_SUB; vABS_NEG] ---->
  vSUBGOAL_THEN [%q {|abs(e) = e|} ] (fun th -> vASM_REWRITE_TAC[th]) ++-->
   [vREWRITE_TAC[vABS_REFL] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
    vFIRST_ASSUM vACCEPT_TAC; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|&0 < cos((pi / &2) - e) / sin((pi / &2) - e)|} ]
  vMP_TAC ++-->
   [vONCE_REWRITE_TAC[real_div] ---->
    vMATCH_MP_TAC vREAL_LT_MUL ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vCOS_POS_PI2;
      vMATCH_MP_TAC vREAL_INV_POS ----> vMATCH_MP_TAC vSIN_POS_PI2] ---->
    vASM_REWRITE_TAC[vREAL_SUB_LT] ---->
    vREWRITE_TAC[vGSYM vREAL_NOT_LE; real_sub; vREAL_LE_ADDR; vREAL_NEG_GE0] ---->
    vASM_REWRITE_TAC[vREAL_NOT_LE]; vALL_TAC] ---->
  vDISCH_THEN(fun th -> vASSUME_TAC th ----> vMP_TAC(vMATCH_MP vREAL_LT_IMP_NZ th)) ---->
  vREWRITE_TAC[vABS_NZ; vIMP_IMP] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_INV2) ----> vREWRITE_TAC[tan] ---->
  vMATCH_MP_TAC vEQ_IMP ----> vBINOP_TAC ++-->
   [vMATCH_MP_TAC vREAL_INVINV ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
    vFIRST_ASSUM vACCEPT_TAC; vALL_TAC] ---->
  vMP_TAC(vASSUME [%q {|&0 < cos((pi / &2) - e) / sin((pi / &2) - e)|} ]) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
  vREWRITE_TAC[vGSYM vABS_REFL] ----> vDISCH_THEN vSUBST1_TAC ---->
  vREWRITE_TAC[real_div] ----> vIMP_SUBST_TAC vREAL_INV_MUL_WEAK ++-->
   [vREWRITE_TAC[vGSYM vDE_MORGAN_THM; vGSYM vREAL_ENTIRE; vGSYM real_div] ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NZ ----> vFIRST_ASSUM vACCEPT_TAC;
    vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ----> vAP_TERM_TAC ---->
    vMATCH_MP_TAC vREAL_INVINV ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
    vMATCH_MP_TAC vSIN_POS_PI2 ----> vREWRITE_TAC[vREAL_SUB_LT; vGSYM real_div] ---->
    vREWRITE_TAC[vGSYM vREAL_NOT_LE; real_sub; vREAL_LE_ADDR; vREAL_NEG_GE0] ---->
    vASM_REWRITE_TAC[vREAL_NOT_LE]]);;

let%a vTAN_TOTAL_POS = prove(
  [%q {|!y. &0 <= y ==> ?x. &0 <= x /\ x < pi / &2 /\ (tan(x) = y)|} ],
  vGEN_TAC ----> vDISCH_THEN(vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
   [vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vTAN_TOTAL_LEMMA) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vSTRIP_ASSUME_TAC) ---->
    vMP_TAC(vSPECL [[%q {|tan|} ]; [%q {|&0|} ]; [%q {|x:real|} ]; [%q {|y:real|} ]] vIVT) ---->
    vW(vC vSUBGOAL_THEN (fun th -> vDISCH_THEN(vMP_TAC -| vC vMATCH_MP th)) -|
         funpow 2 (fst -| dest_imp) -| snd) ++-->
     [vREPEAT vCONJ_TAC ----> vTRY(vMATCH_MP_TAC vREAL_LT_IMP_LE) ---->
      vASM_REWRITE_TAC[vTAN_0] ----> vX_GEN_TAC [%q {|z:real|} ] ----> vSTRIP_TAC ---->
      vMATCH_MP_TAC vDIFF_CONT ----> vEXISTS_TAC [%q {|inv(cos(z) pow 2)|} ] ---->
      vMATCH_MP_TAC vDIFF_TAN ----> vUNDISCH_TAC [%q {|&0 <= z|} ] ---->
      vREWRITE_TAC[vREAL_LE_LT] ----> vDISCH_THEN(vDISJ_CASES_THEN vMP_TAC) ++-->
       [vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
        vMATCH_MP_TAC vCOS_POS_PI2 ----> vASM_REWRITE_TAC[] ---->
        vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
        vASM_REWRITE_TAC[];
        vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vCOS_0; vREAL_10]];
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vSTRIP_ASSUME_TAC) ---->
      vEXISTS_TAC [%q {|z:real|} ] ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
      vASM_REWRITE_TAC[]];
    vPOP_ASSUM(vSUBST1_TAC -| vSYM) ----> vEXISTS_TAC [%q {|&0|} ] ---->
    vREWRITE_TAC[vTAN_0; vREAL_LE_REFL; vPI2_BOUNDS]]);;

let%a vTAN_TOTAL = prove(
  [%q {|!y. ?!x. --(pi / &2) < x /\ x < (pi / &2) /\ (tan(x) = y)|} ],
  vGEN_TAC ----> vCONV_TAC vEXISTS_UNIQUE_CONV ----> vCONJ_TAC ++-->
   [vDISJ_CASES_TAC(vSPEC [%q {|y:real|} ] vREAL_LE_NEGTOTAL) ---->
    vPOP_ASSUM(vX_CHOOSE_TAC [%q {|x:real|} ] -| vMATCH_MP vTAN_TOTAL_POS) ++-->
     [vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|&0|} ] ---->
      vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vGSYM vREAL_LT_NEG2] ---->
      vREWRITE_TAC[vREAL_NEG_NEG; vREAL_NEG_0; vPI2_BOUNDS];
      vEXISTS_TAC [%q {|--x|} ] ----> vASM_REWRITE_TAC[vREAL_LT_NEG2] ---->
      vASM_REWRITE_TAC[vTAN_NEG; vREAL_NEG_EQ; vREAL_NEG_NEG] ---->
      vONCE_REWRITE_TAC[vGSYM vREAL_LT_NEG2] ---->
      vREWRITE_TAC[vREAL_LT_NEG2] ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
      vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[vREAL_LE_NEGL]];
    vMAP_EVERY vX_GEN_TAC [[%q {|x1:real|} ]; [%q {|x2:real|} ]] ---->
    vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC
         (vSPECL [[%q {|x1:real|} ]; [%q {|x2:real|} ]] vREAL_LT_TOTAL) ++-->
     [vDISCH_THEN(vK vALL_TAC) ----> vPOP_ASSUM vACCEPT_TAC;
      vALL_TAC;
      vPOP_ASSUM vMP_TAC ----> vSPEC_TAC([%q {|x1:real|} ],[%q {|z1:real|} ]) ---->
      vSPEC_TAC([%q {|x2:real|} ],[%q {|z2:real|} ]) ---->
      vMAP_EVERY vX_GEN_TAC [[%q {|x1:real|} ]; [%q {|x2:real|} ]] ----> vDISCH_TAC ---->
      vCONV_TAC(vRAND_CONV vSYM_CONV) ----> vONCE_REWRITE_TAC[vCONJ_SYM]] ---->
    (vSTRIP_TAC ----> vMP_TAC(vSPECL [[%q {|tan|} ]; [%q {|x1:real|} ]; [%q {|x2:real|} ]] vROLLE) ---->
     vASM_REWRITE_TAC[] ----> vCONV_TAC vCONTRAPOS_CONV ---->
     vDISCH_THEN(vK vALL_TAC) ----> vREWRITE_TAC[vNOT_IMP] ---->
     vREPEAT vCONJ_TAC ++-->
      [vX_GEN_TAC [%q {|x:real|} ] ----> vSTRIP_TAC ----> vMATCH_MP_TAC vDIFF_CONT ---->
       vEXISTS_TAC [%q {|inv(cos(x) pow 2)|} ] ----> vMATCH_MP_TAC vDIFF_TAN;
       vX_GEN_TAC [%q {|x:real|} ] ---->
       vDISCH_THEN(vCONJUNCTS_THEN (vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_LE)) ---->
       vREWRITE_TAC[differentiable] ----> vEXISTS_TAC [%q {|inv(cos(x) pow 2)|} ] ---->
       vMATCH_MP_TAC vDIFF_TAN;
       vREWRITE_TAC[vCONJ_ASSOC] ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ]
         (vCONJUNCTS_THEN2 (vCONJUNCTS_THEN (vASSUME_TAC -| vMATCH_MP
          vREAL_LT_IMP_LE)) vASSUME_TAC)) ---->
       vMP_TAC(vSPEC [%q {|x:real|} ] vDIFF_TAN) ---->
       vSUBGOAL_THEN [%q {|~(cos(x) = &0)|} ] vASSUME_TAC ++-->
        [vALL_TAC;
         vASM_REWRITE_TAC[] ---->
         vDISCH_THEN(vMP_TAC -| vC vCONJ (vASSUME [%q {|(tan diffl &0)(x)|} ])) ---->
         vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_UNIQ) ----> vREWRITE_TAC[] ---->
         vMATCH_MP_TAC vREAL_INV_NZ ----> vMATCH_MP_TAC vPOW_NZ ---->
         vASM_REWRITE_TAC[]]] ---->
     (vMATCH_MP_TAC vREAL_LT_IMP_NZ ----> vMATCH_MP_TAC vCOS_POS_PI ---->
      vCONJ_TAC ++-->
       [vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|x1:real|} ];
        vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x2:real|} ]] ---->
     vASM_REWRITE_TAC[]))]);;

let%a vPI2_PI4 = prove
 ([%q {|pi / &2 = &2 * pi / &4|} ],
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
  vCONV_TAC vREAL_RAT_REDUCE_CONV);;

let%a vTAN_PI4 = prove
 ([%q {|tan(pi / &4) = &1|} ],
  vREWRITE_TAC[tan; vCOS_SIN; real_div; vGSYM vREAL_SUB_LDISTRIB] ---->
  vCONV_TAC vREAL_RAT_REDUCE_CONV ----> vMATCH_MP_TAC vREAL_MUL_RINV ---->
  vREWRITE_TAC[vSIN_ZERO] ---->
  vREWRITE_TAC[real_div; vGSYM vREAL_MUL_LNEG] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC [%q {|a * b * c = b * a * c|} ]] ---->
  vSIMP_TAC[vREAL_MUL_LID; vREAL_EQ_MUL_LCANCEL; vPI_POS; vREAL_LT_IMP_NZ] ---->
  vSIMP_TAC[vGSYM real_div; vREAL_EQ_RDIV_EQ; vREAL_OF_NUM_LT; vARITH] ---->
  vCONV_TAC vREAL_RAT_REDUCE_CONV ---->
  vSIMP_TAC[vREAL_EQ_LDIV_EQ; vREAL_OF_NUM_LT; vARITH] ---->
  vREWRITE_TAC[vREAL_MUL_LNEG; vREAL_OF_NUM_MUL; vREAL_OF_NUM_EQ] ---->
  vSIMP_TAC[vREAL_ARITH [%q {|&0 <= x ==> ~(&1 = --x)|} ]; vREAL_POS] ---->
  vSTRIP_TAC ----> vFIRST_ASSUM(vMP_TAC -| vAP_TERM [%q {|EVEN|} ]) ---->
  vREWRITE_TAC[vEVEN_MULT; vARITH_EVEN]);;

let%a vTAN_COT = prove
 ([%q {|!x. tan(pi / &2 - x) = inv(tan x)|} ],
  vREWRITE_TAC[tan; vGSYM vSIN_COS; vGSYM vCOS_SIN; vREAL_INV_DIV]);;

let%a vTAN_BOUND_PI2 = prove
 ([%q {|!x. abs(x) < pi / &4 ==> abs(tan x) < &1|} ],
  vREPEAT vGEN_TAC ---->
  vSUBGOAL_THEN
   [%q {|!x. &0 < x /\ x < pi / &4 ==> &0 < tan(x) /\ tan(x) < &1|} ]
  vASSUME_TAC ++-->
   [vREPEAT vSTRIP_TAC ++-->
     [vASM_SIMP_TAC[tan; vREAL_LT_DIV; vSIN_POS_PI2; vCOS_POS_PI2; vPI2_PI4;
                   vREAL_ARITH [%q {|&0 < x /\ x < a ==> x < &2 * a|} ]];
      vALL_TAC] ---->
    vMP_TAC(vSPECL [[%q {|tan|} ]; [%q {|\x. inv(cos(x) pow 2)|} ];
                  [%q {|x:real|} ]; [%q {|pi / &4|} ]] vMVT_ALT) ---->
    vW(vC vSUBGOAL_THEN (fun th -> vREWRITE_TAC[th]) -| funpow 2 lhand -| snd) ++-->
     [vASM_REWRITE_TAC[vBETA_THM] ----> vX_GEN_TAC [%q {|z:real|} ] ----> vSTRIP_TAC ---->
      vMATCH_MP_TAC vDIFF_TAN ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
      vMATCH_MP_TAC vCOS_POS_PI2 ----> vREWRITE_TAC[vPI2_PI4] ---->
      vMAP_EVERY vUNDISCH_TAC [[%q {|x <= z|} ]; [%q {|z <= pi / &4|} ]; [%q {|&0 < x|} ]] ---->
      vREAL_ARITH_TAC;
      vALL_TAC] ---->
    vSIMP_TAC[vTAN_PI4; vREAL_ARITH [%q {|x < &1 <=> &0 < &1 - x|} ];
             vLEFT_IMP_EXISTS_THM] ---->
    vX_GEN_TAC [%q {|z:real|} ] ----> vREPEAT vSTRIP_TAC ---->
    vMATCH_MP_TAC vREAL_LT_MUL ----> vASM_REWRITE_TAC[vREAL_SUB_LT] ---->
    vREWRITE_TAC[vREAL_LT_INV_EQ; vBETA_THM] ---->
    vMATCH_MP_TAC vREAL_POW_LT ----> vMATCH_MP_TAC vCOS_POS_PI2 ---->
    vREWRITE_TAC[vPI2_PI4] ---->
    vMAP_EVERY vUNDISCH_TAC [[%q {|x < z|} ]; [%q {|z < pi / &4|} ]; [%q {|&0 < x|} ]] ---->
    vREAL_ARITH_TAC; vALL_TAC] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [real_abs] ---->
  vREWRITE_TAC[vREAL_LE_LT] ---->
  vASM_CASES_TAC [%q {|x = &0|} ] ---->
  vASM_REWRITE_TAC[vTAN_0; vREAL_ABS_NUM; vREAL_LT_01] ---->
  vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vREAL_ARITH [%q {|&0 < x /\ x < &1 ==> abs(x) < &1|} ]] ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_ABS_NEG] ----> vREWRITE_TAC[vGSYM vTAN_NEG] ---->
  vASM_SIMP_TAC[vREAL_ARITH [%q {|&0 < x /\ x < &1 ==> abs(x) < &1|} ];
               vREAL_ARITH [%q {|~(x = &0) /\ ~(&0 < x) ==> &0 < --x|} ]]);;

let%a vTAN_ABS_GE_X = prove
 ([%q {|!x. abs(x) < pi / &2 ==> abs(x) <= abs(tan x)|} ],
  vSUBGOAL_THEN [%q {|!y. &0 < y /\ y < pi / &2 ==> y <= tan(y)|} ] vASSUME_TAC ++-->
   [vALL_TAC;
    vGEN_TAC ---->
    vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC (vSPEC [%q {|x:real|} ] vREAL_LT_NEGTOTAL) ---->
    vASM_REWRITE_TAC[vTAN_0; vREAL_ABS_0; vREAL_LE_REFL] ++-->
     [vALL_TAC;
      vONCE_REWRITE_TAC[vGSYM vREAL_ABS_NEG] ----> vREWRITE_TAC[vGSYM vTAN_NEG]] ---->
    vMATCH_MP_TAC(vREAL_ARITH
     [%q {|&0 < x /\ (x < p ==> x <= tx)
      ==> abs(x) < p ==> abs(x) <= abs(tx)|} ]) ----> vASM_SIMP_TAC[]] ---->
  vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|tan|} ]; [%q {|\x. inv(cos(x) pow 2)|} ]; [%q {|&0|} ]; [%q {|y:real|} ]] vMVT_ALT) ---->
  vASM_REWRITE_TAC[vTAN_0; vREAL_SUB_RZERO] ---->
  vMATCH_MP_TAC(vTAUT [%q {|a /\ (b ==> c) ==> (a ==> b) ==> c|} ]) ----> vCONJ_TAC ++-->
   [vREPEAT vSTRIP_TAC ----> vBETA_TAC ----> vMATCH_MP_TAC vDIFF_TAN ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NZ ----> vMATCH_MP_TAC vCOS_POS_PI ---->
    vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ----> vREAL_ARITH_TAC;
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vSTRIP_ASSUME_TAC) ---->
    vASM_REWRITE_TAC[vBETA_THM] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_RID] ---->
    vMATCH_MP_TAC vREAL_LE_LMUL ----> vASM_SIMP_TAC[vREAL_LT_IMP_LE] ---->
    vMATCH_MP_TAC vREAL_INV_1_LE ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_POW_LT;
      vMATCH_MP_TAC vREAL_POW_1_LE ----> vREWRITE_TAC[vCOS_BOUNDS] ---->
      vMATCH_MP_TAC vREAL_LT_IMP_LE] ---->
    vMATCH_MP_TAC vCOS_POS_PI ---->
    vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ----> vREAL_ARITH_TAC]);;

(* ------------------------------------------------------------------------ *)
(* Inverse trig functions                                                   *)
(* ------------------------------------------------------------------------ *)

let asn = new_definition
  [%q {|asn(y) = @x. --(pi / &2) <= x /\ x <= pi / &2 /\ (sin x = y)|} ];;

let acs = new_definition
  [%q {|acs(y) = @x. &0 <= x /\ x <= pi /\ (cos x = y)|} ];;

let atn = new_definition
  [%q {|atn(y) = @x. --(pi / &2) < x /\ x < pi / &2 /\ (tan x = y)|} ];;

let%a vASN = prove(
  [%q {|!y. --(&1) <= y /\ y <= &1 ==>
     --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2 /\ (sin(asn y) = y)|} ],
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vSIN_TOTAL) ---->
  vDISCH_THEN(vMP_TAC -| vCONJUNCT1 -| vCONV_RULE vEXISTS_UNIQUE_CONV) ---->
  vDISCH_THEN(vMP_TAC -| vSELECT_RULE) ----> vREWRITE_TAC[vGSYM asn]);;

let%a vASN_SIN = prove(
  [%q {|!y. --(&1) <= y /\ y <= &1 ==> (sin(asn(y)) = y)|} ],
  vGEN_TAC ----> vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vASN th]));;

let%a vASN_BOUNDS = prove(
  [%q {|!y. --(&1) <= y /\ y <= &1 ==> --(pi / &2) <= asn(y) /\ asn(y) <= pi / &2|} ],
  vGEN_TAC ----> vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vASN th]));;

let%a vASN_BOUNDS_LT = prove(
  [%q {|!y. --(&1) < y /\ y < &1 ==> --(pi / &2) < asn(y) /\ asn(y) < pi / &2|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vEVERY_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
  vMP_TAC(vSPEC [%q {|y:real|} ] vASN_BOUNDS) ----> vASM_REWRITE_TAC[] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[vREAL_LT_LE] ---->
  vCONJ_TAC ----> vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|sin|} ]) ---->
  vIMP_SUBST_TAC vASN_SIN ----> vASM_REWRITE_TAC[vSIN_NEG; vSIN_PI2] ---->
  vDISCH_THEN((---->) (vPOP_ASSUM_LIST (vMP_TAC -| end_itlist vCONJ)) -|
    vASSUME_TAC) ----> vASM_REWRITE_TAC[vREAL_LT_REFL]);;

let%a vSIN_ASN = prove(
  [%q {|!x. --(pi / &2) <= x /\ x <= pi / &2 ==> (asn(sin(x)) = x)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC(vMATCH_MP vSIN_TOTAL (vSPEC [%q {|x:real|} ] vSIN_BOUNDS)) ---->
  vDISCH_THEN(vMATCH_MP_TAC -| vCONJUNCT2 -| vCONV_RULE vEXISTS_UNIQUE_CONV) ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vASN ---->
  vMATCH_ACCEPT_TAC vSIN_BOUNDS);;

let%a vACS = prove(
  [%q {|!y. --(&1) <= y /\ y <= &1 ==>
     &0 <= acs(y) /\ acs(y) <= pi  /\ (cos(acs y) = y)|} ],
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vCOS_TOTAL) ---->
  vDISCH_THEN(vMP_TAC -| vCONJUNCT1 -| vCONV_RULE vEXISTS_UNIQUE_CONV) ---->
  vDISCH_THEN(vMP_TAC -| vSELECT_RULE) ----> vREWRITE_TAC[vGSYM acs]);;

let%a vACS_COS = prove(
  [%q {|!y. --(&1) <= y /\ y <= &1 ==> (cos(acs(y)) = y)|} ],
  vGEN_TAC ----> vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vACS th]));;

let%a vACS_BOUNDS = prove(
  [%q {|!y. --(&1) <= y /\ y <= &1 ==> &0 <= acs(y) /\ acs(y) <= pi|} ],
  vGEN_TAC ----> vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vACS th]));;

let%a vACS_BOUNDS_LT = prove(
  [%q {|!y. --(&1) < y /\ y < &1 ==> &0 < acs(y) /\ acs(y) < pi|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vEVERY_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
  vMP_TAC(vSPEC [%q {|y:real|} ] vACS_BOUNDS) ----> vASM_REWRITE_TAC[] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[vREAL_LT_LE] ---->
  vCONJ_TAC ----> vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|cos|} ]) ---->
  vIMP_SUBST_TAC vACS_COS ----> vASM_REWRITE_TAC[vCOS_0; vCOS_PI] ---->
  vDISCH_THEN((---->) (vPOP_ASSUM_LIST (vMP_TAC -| end_itlist vCONJ)) -|
    vASSUME_TAC) ----> vASM_REWRITE_TAC[vREAL_LT_REFL]);;

let%a vCOS_ACS = prove(
  [%q {|!x. &0 <= x /\ x <= pi ==> (acs(cos(x)) = x)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC(vMATCH_MP vCOS_TOTAL (vSPEC [%q {|x:real|} ] vCOS_BOUNDS)) ---->
  vDISCH_THEN(vMATCH_MP_TAC -| vCONJUNCT2 -| vCONV_RULE vEXISTS_UNIQUE_CONV) ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vACS ---->
  vMATCH_ACCEPT_TAC vCOS_BOUNDS);;

let%a vATN = prove(
  [%q {|!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2) /\ (tan(atn y) = y)|} ],
  vGEN_TAC ----> vMP_TAC(vSPEC [%q {|y:real|} ] vTAN_TOTAL) ---->
  vDISCH_THEN(vMP_TAC -| vCONJUNCT1 -| vCONV_RULE vEXISTS_UNIQUE_CONV) ---->
  vDISCH_THEN(vMP_TAC -| vSELECT_RULE) ----> vREWRITE_TAC[vGSYM atn]);;

let%a vATN_TAN = prove(
  [%q {|!y. tan(atn y) = y|} ],
  vREWRITE_TAC[vATN]);;

let%a vATN_BOUNDS = prove(
  [%q {|!y. --(pi / &2) < atn(y) /\ atn(y) < (pi / &2)|} ],
  vREWRITE_TAC[vATN]);;

let%a vTAN_ATN = prove(
  [%q {|!x. --(pi / &2) < x /\ x < (pi / &2) ==> (atn(tan(x)) = x)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vMP_TAC(vSPEC [%q {|tan(x)|} ] vTAN_TOTAL) ---->
  vDISCH_THEN(vMATCH_MP_TAC -| vCONJUNCT2 -| vCONV_RULE vEXISTS_UNIQUE_CONV) ---->
  vASM_REWRITE_TAC[vATN]);;

let%a vATN_0 = prove
 ([%q {|atn(&0) = &0|} ],
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vSYM vTAN_0] ---->
  vMATCH_MP_TAC vTAN_ATN ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|&0 < a ==> --a < &0 /\ &0 < a|} ]) ---->
  vSIMP_TAC[vREAL_LT_DIV; vPI_POS; vREAL_OF_NUM_LT; vARITH]);;

let%a vATN_1 = prove
 ([%q {|atn(&1) = pi / &4|} ],
  vMP_TAC(vAP_TERM [%q {|atn|} ] vTAN_PI4) ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vMATCH_MP_TAC vTAN_ATN ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|&0 < a /\ a < b ==> --b < a /\ a < b|} ]) ---->
  vSIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH; vPI_POS] ---->
  vSIMP_TAC[real_div; vREAL_LT_LMUL_EQ; vPI_POS] ---->
  vCONV_TAC vREAL_RAT_REDUCE_CONV);;

let%a vATN_NEG = prove
 ([%q {|!x. atn(--x) = --(atn x)|} ],
  vGEN_TAC ----> vMP_TAC(vSPEC [%q {|atn(x)|} ] vTAN_NEG) ---->
  vREWRITE_TAC[vATN_TAN] ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vMATCH_MP_TAC vTAN_ATN ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|--a < x /\ x < a ==> --a < --x /\ --x < a|} ]) ---->
  vREWRITE_TAC[vATN_BOUNDS]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation of arctan.                                                *)
(* ------------------------------------------------------------------------- *)

let%a vCOS_ATN_NZ = prove(
  [%q {|!x. ~(cos(atn(x)) = &0)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vCOS_ZERO; vDE_MORGAN_THM] ----> vCONJ_TAC ---->
  vCONV_TAC vNOT_EXISTS_CONV ----> vX_GEN_TAC [%q {|n:num|} ] ---->
  vSTRUCT_CASES_TAC(vSPEC [%q {|n:num|} ] num_CASES) ---->
  vREWRITE_TAC[vEVEN; vDE_MORGAN_THM] ----> vDISJ2_TAC ---->
  vDISCH_TAC ----> vMP_TAC(vSPEC [%q {|x:real|} ] vATN_BOUNDS) ---->
  vASM_REWRITE_TAC[vDE_MORGAN_THM] ++-->
   [vDISJ2_TAC; vDISJ1_TAC ----> vREWRITE_TAC[vREAL_LT_NEG2]] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV)  [vGSYM vREAL_MUL_LID] ---->
  vREWRITE_TAC[vMATCH_MP vREAL_LT_RMUL_EQ (vCONJUNCT1 vPI2_BOUNDS)] ---->
  vREWRITE_TAC[vADD1; vGSYM vREAL_ADD; vREAL_NOT_LT] ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vREWRITE_TAC[vREAL_LE_ADDR; vREAL_LE; vLE_0]);;

let%a vTAN_SEC = prove(
  [%q {|!x. ~(cos(x) = &0) ==> (&1 + (tan(x) pow 2) = inv(cos x) pow 2)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[tan] ---->
  vFIRST_ASSUM(fun th ->  vONCE_REWRITE_TAC[vGSYM
   (vMATCH_MP vREAL_DIV_REFL (vSPEC [%q {|2|} ] (vMATCH_MP vPOW_NZ th)))]) ---->
  vREWRITE_TAC[real_div; vPOW_MUL] ---->
  vPOP_ASSUM(fun th ->  vREWRITE_TAC[vMATCH_MP vPOW_INV th]) ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_RDISTRIB; vSIN_CIRCLE; vREAL_MUL_LID]);;

let%a vDIFF_ATN = prove(
  [%q {|!x. (atn diffl (inv(&1 + (x pow 2))))(x)|} ],
  vGEN_TAC ---->
  vSUBGOAL_THEN [%q {|(atn diffl (inv(&1 + (x pow 2))))(tan(atn x))|} ]
  vMP_TAC ++--> [vMATCH_MP_TAC vDIFF_INVERSE_LT; vREWRITE_TAC[vATN_TAN]] ---->
  vSUBGOAL_THEN
    [%q {|?d. &0 < d /\
         !z. abs(z - atn(x)) < d ==>  (--(pi / (& 2))) < z /\ z < (pi / (& 2))|} ]
  (vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ++-->
   [vONCE_REWRITE_TAC[vABS_SUB] ----> vMATCH_MP_TAC vINTERVAL_LEMMA_LT ---->
    vMATCH_ACCEPT_TAC vATN_BOUNDS;
    vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vREPEAT vSTRIP_TAC ++-->
     [vMATCH_MP_TAC vTAN_ATN ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vASM_REWRITE_TAC[];
      vMATCH_MP_TAC vDIFF_CONT ----> vEXISTS_TAC [%q {|inv(cos(z) pow 2)|} ] ---->
      vMATCH_MP_TAC vDIFF_TAN ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
      vMATCH_MP_TAC vCOS_POS_PI ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vASM_REWRITE_TAC[];
      vASSUME_TAC(vSPEC [%q {|x:real|} ] vCOS_ATN_NZ) ---->
      vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vDIFF_TAN) ---->
      vFIRST_ASSUM(vASSUME_TAC -| vSYM -| vMATCH_MP vTAN_SEC) ---->
      vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vPOW_INV) ---->
      vASM_REWRITE_TAC[vATN_TAN];
      vUNDISCH_TAC [%q {|&1 + (x pow 2) = &0|} ] ----> vREWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
      vMATCH_MP_TAC vREAL_LTE_ADD ---->
      vREWRITE_TAC[vREAL_LT_01; vREAL_LE_SQUARE; vPOW_2]]]);;

let vDIFF_ATN_COMPOSITE = prove
 ([%q {|(g diffl m)(x) ==> ((\x. atn(g x)) diffl (inv(&1 + (g x) pow 2) * m))(x)|} ],
  vASM_SIMP_TAC[vDIFF_CHAIN; vDIFF_ATN]) in
add_to_diff_net vDIFF_ATN_COMPOSITE;;

(* ------------------------------------------------------------------------- *)
(* A few more lemmas about arctan.                                           *)
(* ------------------------------------------------------------------------- *)

let%a vATN_MONO_LT = prove
 ([%q {|!x y. x < y ==> atn(x) < atn(y)|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|atn|} ]; [%q {|\x. inv(&1 + x pow 2)|} ]; [%q {|x:real|} ]; [%q {|y:real|} ]]
               vMVT_ALT) ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[vDIFF_ATN] ----> vSTRIP_TAC ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vREAL_ARITH
    [%q {|(l - r = d) ==> l < d + e ==> r < e|} ])) ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|a < b + a <=> &0 < b|} ]] ---->
  vMATCH_MP_TAC vREAL_LT_MUL ---->
  vASM_REWRITE_TAC[vREAL_LT_SUB_LADD; vREAL_ADD_LID] ---->
  vREWRITE_TAC[vREAL_LT_INV_EQ] ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|&0 <= x ==> &0 < &1 + x|} ]) ---->
  vREWRITE_TAC[vREAL_POW_2; vREAL_LE_SQUARE]);;

let%a vATN_MONO_LT_EQ = prove
 ([%q {|!x y. atn(x) < atn(y) <=> x < y|} ],
  vMESON_TAC[vREAL_NOT_LE; vREAL_LE_LT; vATN_MONO_LT]);;

let%a vATN_MONO_LE_EQ = prove
 ([%q {|!x y. atn(x) <= atn(y) <=> x <= y|} ],
  vREWRITE_TAC[vGSYM vREAL_NOT_LT; vATN_MONO_LT_EQ]);;

let%a vATN_INJ = prove
 ([%q {|!x y. (atn x = atn y) <=> (x = y)|} ],
  vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM; vATN_MONO_LE_EQ]);;

let%a vATN_POS_LT = prove
 ([%q {|&0 < atn(x) <=> &0 < x|} ],
  vMESON_TAC[vATN_0; vATN_MONO_LT_EQ]);;

let%a vATN_POS_LE = prove
 ([%q {|&0 <= atn(x) <=> &0 <= x|} ],
  vMESON_TAC[vATN_0; vATN_MONO_LE_EQ]);;

let%a vATN_LT_PI4_POS = prove
 ([%q {|!x. x < &1 ==> atn(x) < pi / &4|} ],
  vSIMP_TAC[vGSYM vATN_1; vATN_MONO_LT]);;

let%a vATN_LT_PI4_NEG = prove
 ([%q {|!x. --(&1) < x ==> --(pi / &4) < atn(x)|} ],
  vSIMP_TAC[vGSYM vATN_1; vGSYM vATN_NEG; vATN_MONO_LT]);;

let%a vATN_LT_PI4 = prove
 ([%q {|!x. abs(x) < &1 ==> abs(atn x) < pi / &4|} ],
  vGEN_TAC ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|(&0 < x ==> &0 < y) /\
    (x < &0 ==> y < &0) /\
    ((x = &0) ==> (y = &0)) /\
    (x < a ==> y < b) /\
    (--a < x ==> --b < y)
    ==> abs(x) < a ==> abs(y) < b|} ]) ---->
  vSIMP_TAC[vATN_LT_PI4_POS; vATN_LT_PI4_NEG; vATN_0] ----> vCONJ_TAC ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vGSYM vATN_0] ---->
  vSIMP_TAC[vATN_MONO_LT]);;

let%a vATN_LE_PI4 = prove
 ([%q {|!x. abs(x) <= &1 ==> abs(atn x) <= pi / &4|} ],
  vREWRITE_TAC[vREAL_LE_LT] ----> vREPEAT vSTRIP_TAC ---->
  vASM_SIMP_TAC[vATN_LT_PI4] ----> vDISJ2_TAC ---->
  vFIRST_ASSUM(vDISJ_CASES_THEN vSUBST1_TAC -| vMATCH_MP
    (vREAL_ARITH [%q {|(abs(x) = a) ==> (x = a) \/ (x = --a)|} ])) ---->
  vASM_REWRITE_TAC[vATN_1; vATN_NEG] ---->
  vREWRITE_TAC[vREAL_ABS_DIV; vREAL_ABS_NUM; vREAL_ABS_NEG] ---->
  vSIMP_TAC[real_abs; vREAL_LT_IMP_LE; vPI_POS]);;

(* ------------------------------------------------------------------------- *)
(* Differentiation of arcsin.                                                *)
(* ------------------------------------------------------------------------- *)

let%a vCOS_SIN_SQRT = prove(
  [%q {|!x. &0 <= cos(x) ==> (cos(x) = sqrt(&1 - (sin(x) pow 2)))|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC (vONCE_REWRITE_RULE[vREAL_ADD_SYM] (vSPEC [%q {|x:real|} ] vSIN_CIRCLE)) ---->
  vREWRITE_TAC[vGSYM vREAL_EQ_SUB_LADD] ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSQRT_UNIQUE ---->
  vASM_REWRITE_TAC[]);;

let%a vCOS_ASN_NZ = prove(
  [%q {|!x. --(&1) < x /\ x < &1 ==> ~(cos(asn(x)) = &0)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vSTRIP_ASSUME_TAC -| vMATCH_MP vASN_BOUNDS_LT) ---->
  vREWRITE_TAC[vCOS_ZERO; vDE_MORGAN_THM] ---->
  vCONJ_TAC ----> vCONV_TAC vNOT_EXISTS_CONV ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vSTRUCT_CASES_TAC(vSPEC [%q {|n:num|} ] num_CASES) ---->
  vREWRITE_TAC[vEVEN] ----> vSTRIP_TAC ++-->
   [vUNDISCH_TAC [%q {|asn(x) < (pi / &2)|} ] ----> vASM_REWRITE_TAC[];
    vUNDISCH_TAC [%q {|--(pi / &2) < asn(x)|} ] ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vREAL_LT_NEG2]] ---->
  vREWRITE_TAC[vADD1; vGSYM vREAL_ADD; vREAL_RDISTRIB; vREAL_MUL_LID] ---->
  vREWRITE_TAC[vGSYM vREAL_NOT_LE; vREAL_LE_ADDL] ---->
  vMATCH_MP_TAC vREAL_LE_MUL ----> vREWRITE_TAC[vREAL_LE; vLE_0] ---->
  vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vREWRITE_TAC[vPI2_BOUNDS]);;

let%a vDIFF_ASN_COS = prove(
  [%q {|!x. --(&1) < x /\ x < &1 ==> (asn diffl (inv(cos(asn x))))(x)|} ],
  vREPEAT vSTRIP_TAC ---->
  vEVERY_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vASN_SIN) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_TAC ---->
  vFIRST_ASSUM(fun th ->  vGEN_REWRITE_TAC vRAND_CONV  [vGSYM th]) ---->
  vMATCH_MP_TAC vDIFF_INVERSE_LT ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vASN_BOUNDS_LT) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(fun th ->  vSTRIP_ASSUME_TAC th ---->
    vMP_TAC(vMATCH_MP vINTERVAL_LEMMA_LT th)) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vDISCH_THEN(vASSUME_TAC -| vONCE_REWRITE_RULE[vABS_SUB]) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vREPEAT vSTRIP_TAC ++-->
   [vMATCH_MP_TAC vSIN_ASN ---->
    vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|z:real|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC ----> vCONJ_TAC ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
    vMATCH_MP_TAC vDIFF_CONT ----> vEXISTS_TAC [%q {|cos(z)|} ] ---->
    vREWRITE_TAC[vDIFF_SIN];
    vREWRITE_TAC[vDIFF_SIN];
    vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[] ----> vMATCH_MP_TAC vCOS_ASN_NZ ---->
    vASM_REWRITE_TAC[]]);;

let%a vDIFF_ASN = prove(
  [%q {|!x. --(&1) < x /\ x < &1 ==> (asn diffl (inv(sqrt(&1 - (x pow 2)))))(x)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vDIFF_ASN_COS) ---->
  vMATCH_MP_TAC vEQ_IMP ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vAP_TERM_TAC ---->
  vSUBGOAL_THEN [%q {|sin(asn x) = x|} ] vMP_TAC ++-->
   [vMATCH_MP_TAC vASN_SIN ----> vCONJ_TAC ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
    vDISCH_THEN(fun th ->  vGEN_REWRITE_TAC
      (vRAND_CONV -| vONCE_DEPTH_CONV)  [vGSYM th]) ---->
    vMATCH_MP_TAC vCOS_SIN_SQRT ---->
    vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vASN_BOUNDS_LT) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vMATCH_MP_TAC vCOS_POS_PI ---->
    vASM_REWRITE_TAC[]]);;

let vDIFF_ASN_COMPOSITE = prove
 ([%q {|(g diffl m)(x) /\ -- &1 < g(x) /\ g(x) < &1
   ==> ((\x. asn(g x)) diffl (inv(sqrt (&1 - g(x) pow 2)) * m))(x)|} ],
  vASM_SIMP_TAC[vDIFF_CHAIN; vDIFF_ASN]) in
add_to_diff_net vDIFF_ASN_COMPOSITE;;

(* ------------------------------------------------------------------------- *)
(* Differentiation of arccos.                                                *)
(* ------------------------------------------------------------------------- *)

let%a vSIN_COS_SQRT = prove(
  [%q {|!x. &0 <= sin(x) ==> (sin(x) = sqrt(&1 - (cos(x) pow 2)))|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC (vSPEC [%q {|x:real|} ] vSIN_CIRCLE) ---->
  vREWRITE_TAC[vGSYM vREAL_EQ_SUB_LADD] ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSQRT_UNIQUE ---->
  vASM_REWRITE_TAC[]);;

let%a vSIN_ACS_NZ = prove(
  [%q {|!x. --(&1) < x /\ x < &1 ==> ~(sin(acs(x)) = &0)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vSTRIP_ASSUME_TAC -| vMATCH_MP vACS_BOUNDS_LT) ---->
  vREWRITE_TAC[vSIN_ZERO; vREAL_NEG_EQ0] ---->
  vREWRITE_TAC[vDE_MORGAN_THM] ---->
  vCONJ_TAC ----> vCONV_TAC vNOT_EXISTS_CONV ---->
  (vINDUCT_TAC ++-->
    [vREWRITE_TAC[vREAL_MUL_LZERO; vEVEN; vREAL_NEG_0] ---->
     vDISCH_THEN vSUBST_ALL_TAC ---->
     vRULE_ASSUM_TAC(vREWRITE_RULE[vREAL_LT_REFL]) ---->
     vCONTR_TAC(vASSUME [%q {|F|} ]); vALL_TAC] ---->
   vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vREWRITE_TAC[vEVEN] ---->
   vINDUCT_TAC ----> vREWRITE_TAC[vEVEN] ----> vSTRIP_TAC) ++-->
    [vUNDISCH_TAC [%q {|acs(x) < pi|} ] ---->
     vASM_REWRITE_TAC[vADD1; vGSYM vREAL_ADD; vREAL_RDISTRIB] ---->
     vREWRITE_TAC[vREAL_MUL_LID; vGSYM vREAL_ADD_ASSOC] ---->
     vREWRITE_TAC[vREAL_HALF_DOUBLE] ---->
     vREWRITE_TAC[vGSYM vREAL_NOT_LE; vREAL_LE_ADDL] ---->
     vMATCH_MP_TAC vREAL_LE_MUL ---->
     vREWRITE_TAC[vREAL_LE; vLE_0] ---->
     vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vREWRITE_TAC[vPI2_BOUNDS];
     vUNDISCH_TAC [%q {|&0 < acs(x)|} ] ----> vASM_REWRITE_TAC[] ---->
     vREWRITE_TAC[vREAL_NOT_LT] ----> vONCE_REWRITE_TAC[vGSYM vREAL_LE_NEG2] ---->
     vREWRITE_TAC[vREAL_NEG_NEG; vREAL_NEG_LMUL; vREAL_NEG_0] ---->
     vMATCH_MP_TAC vREAL_LE_MUL ----> vREWRITE_TAC[vREAL_LE; vLE_0] ---->
     vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vREWRITE_TAC[vPI2_BOUNDS]]);;

let%a vDIFF_ACS_SIN = prove(
  [%q {|!x. --(&1) < x /\ x < &1 ==> (acs diffl (inv(--(sin(acs x)))))(x)|} ],
  vREPEAT vSTRIP_TAC ---->
  vEVERY_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vACS_COS) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_TAC ---->
  vFIRST_ASSUM(fun th ->  vGEN_REWRITE_TAC vRAND_CONV  [vGSYM th]) ---->
  vMATCH_MP_TAC vDIFF_INVERSE_LT ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vACS_BOUNDS_LT) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(fun th ->  vSTRIP_ASSUME_TAC th ---->
    vMP_TAC(vMATCH_MP vINTERVAL_LEMMA_LT th)) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vDISCH_THEN(vASSUME_TAC -| vONCE_REWRITE_RULE[vABS_SUB]) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vREPEAT vSTRIP_TAC ++-->
   [vMATCH_MP_TAC vCOS_ACS ---->
    vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|z:real|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC ----> vCONJ_TAC ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
    vMATCH_MP_TAC vDIFF_CONT ----> vEXISTS_TAC [%q {|--(sin(z))|} ] ---->
    vREWRITE_TAC[vDIFF_COS];
    vREWRITE_TAC[vDIFF_COS];
    vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[] ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_EQ_NEG] ---->
    vREWRITE_TAC[vREAL_NEG_NEG; vREAL_NEG_0] ---->
    vMATCH_MP_TAC vSIN_ACS_NZ ----> vASM_REWRITE_TAC[]]);;

let%a vDIFF_ACS = prove(
  [%q {|!x. --(&1) < x /\ x < &1 ==> (acs diffl --(inv(sqrt(&1 - (x pow 2)))))(x)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vDIFF_ACS_SIN) ---->
  vMATCH_MP_TAC vEQ_IMP ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vIMP_SUBST_TAC (vGSYM vREAL_NEG_INV) ++-->
   [vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vSIN_ACS_NZ ----> vASM_REWRITE_TAC[];
    vREPEAT vAP_TERM_TAC] ---->
  vSUBGOAL_THEN [%q {|cos(acs x) = x|} ] vMP_TAC ++-->
   [vMATCH_MP_TAC vACS_COS ----> vCONJ_TAC ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
    vDISCH_THEN(fun th ->  vGEN_REWRITE_TAC
      (vRAND_CONV -| vONCE_DEPTH_CONV)  [vGSYM th]) ---->
    vMATCH_MP_TAC vSIN_COS_SQRT ---->
    vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vACS_BOUNDS_LT) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vMATCH_MP_TAC vSIN_POS_PI ---->
    vASM_REWRITE_TAC[]]);;

let vDIFF_ACS_COMPOSITE = prove
 ([%q {|(g diffl m)(x) /\ -- &1 < g(x) /\ g(x) < &1
   ==> ((\x. acs(g x)) diffl (--inv(sqrt(&1 - g(x) pow 2)) * m))(x)|} ],
  vASM_SIMP_TAC[vDIFF_CHAIN; vDIFF_ACS]) in
add_to_diff_net vDIFF_ACS_COMPOSITE;;

(* ------------------------------------------------------------------------- *)
(* Back to normal service!                                                   *)
(* ------------------------------------------------------------------------- *)

extend_basic_rewrites [vBETA_THM];;

(* ------------------------------------------------------------------------- *)
(* A kind of inverse to SIN_CIRCLE                                           *)
(* ------------------------------------------------------------------------- *)

let%a vCIRCLE_SINCOS = prove
 ([%q {|!x y. (x pow 2 + y pow 2 = &1) ==> ?t. (x = cos(t)) /\ (y = sin(t))|} ],
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|abs(x) <= &1 /\ abs(y) <= &1|} ] vSTRIP_ASSUME_TAC ++-->
   [vMATCH_MP_TAC(vREAL_ARITH
     [%q {|(&1 < x ==> &1 < x pow 2) /\ (&1 < y ==> &1 < y pow 2) /\
      &0 <= x pow 2 /\ &0 <= y pow 2 /\ x pow 2 + y pow 2 <= &1
      ==> x <= &1 /\ y <= &1|} ]) ---->
    vASM_REWRITE_TAC[vREAL_POW2_ABS; vREAL_LE_REFL] ---->
    vREWRITE_TAC[vREAL_POW_2; vREAL_LE_SQUARE] ---->
    vREWRITE_TAC[vGSYM vREAL_POW_2] ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_POW2_ABS] ----> vREWRITE_TAC[vREAL_POW_2] ---->
    vCONJ_TAC ----> vDISCH_TAC ---->
    vSUBST1_TAC(vSYM(vREAL_RAT_REDUCE_CONV [%q {|&1 * &1|} ])) ---->
    vMATCH_MP_TAC vREAL_LT_MUL2 ----> vASM_REWRITE_TAC[vREAL_POS];
    vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|&0 <= sin(acs x)|} ] vMP_TAC ++-->
   [vMATCH_MP_TAC vSIN_POS_PI_LE ---->
    vMATCH_MP_TAC vACS_BOUNDS ---->
    vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ----> vREAL_ARITH_TAC;
    vALL_TAC] ---->
  vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vSIN_COS_SQRT) ---->
  vSUBGOAL_THEN [%q {|abs(y) = sqrt(&1 - x pow 2)|} ] vASSUME_TAC ++-->
   [vREWRITE_TAC[vGSYM vPOW_2_SQRT_ABS] ----> vAP_TERM_TAC ---->
    vUNDISCH_TAC [%q {|x pow 2 + y pow 2 = &1|} ] ----> vREAL_ARITH_TAC;
    vALL_TAC] ---->
  vASM_CASES_TAC [%q {|&0 <= y|} ] ++-->
   [vEXISTS_TAC [%q {|acs x|} ]; vEXISTS_TAC [%q {|--(acs x)|} ]] ---->
  vASM_SIMP_TAC[vCOS_NEG; vSIN_NEG; vACS_COS; vREAL_ARITH
   [%q {|abs(x) <= &1 ==> --(&1) <= x /\ x <= &1|} ]]
  ++-->
   [vMATCH_MP_TAC(vREAL_ARITH [%q {|&0 <= y /\ (abs(y) = x) ==> (y = x)|} ]);
    vMATCH_MP_TAC(vREAL_ARITH [%q {|~(&0 <= y) /\ (abs(y) = x) ==> (y = --x)|} ])] ---->
  vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let%a vACS_MONO_LT = prove
 ([%q {|!x y. --(&1) < x /\ x < y /\ y < &1 ==> acs(y) < acs(x)|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|acs|} ]; [%q {|\x. --inv(sqrt(&1 - x pow 2))|} ]; [%q {|x:real|} ]; [%q {|y:real|} ]]
               vMVT_ALT) ---->
  vANTS_TAC ++-->
   [vREPEAT vSTRIP_TAC ----> vASM_SIMP_TAC[] ---->
    vMATCH_MP_TAC vDIFF_ACS ---->
    vASM_MESON_TAC[vREAL_LET_TRANS; vREAL_LTE_TRANS];
    vREWRITE_TAC[vREAL_EQ_SUB_RADD]] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vSTRIP_ASSUME_TAC) ---->
  vASM_REWRITE_TAC[vREAL_ARITH [%q {|a * --c + x < x <=> &0 < a * c|} ]] ---->
  vMATCH_MP_TAC vREAL_LT_MUL ----> vASM_REWRITE_TAC[vREAL_SUB_LT] ---->
  vMATCH_MP_TAC vREAL_LT_INV ----> vMATCH_MP_TAC vSQRT_POS_LT ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_POW2_ABS] ----> vREWRITE_TAC[vREAL_POW_2] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|&0 < &1 - z * z <=> z * z < &1 * &1|} ]] ---->
  vMATCH_MP_TAC vREAL_LT_MUL2 ----> vREWRITE_TAC[vREAL_ABS_POS] ---->
  vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ----> vREAL_ARITH_TAC);;

(* ======================================================================== *)
(* Formalization of Kurzweil-Henstock gauge integral                        *)
(* ======================================================================== *)

let vLE_MATCH_TAC th (asl,w) =
  let thi = vPART_MATCH (rand -| rator) th (rand(rator w)) in
  let tm = rand(concl thi) in
  (vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC tm ----> vCONJ_TAC ++-->
    [vMATCH_ACCEPT_TAC th; vALL_TAC]) (asl,w);;

(* ------------------------------------------------------------------------ *)
(* Some miscellaneous lemmas                                                *)
(* ------------------------------------------------------------------------ *)

let%a vLESS_SUC_EQ = prove(
  [%q {|!m n. m < SUC n <=> m <= n|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vCONJUNCT2 vLT; vLE_LT] ---->
  vEQ_TAC ----> vDISCH_THEN(vDISJ_CASES_THEN(fun th -> vREWRITE_TAC[th])));;

let%a vLESS_1 = prove(
  [%q {|!n. n < 1 <=> (n = 0)|} ],
  vREWRITE_TAC[num_CONV [%q {|1|} ]; vLESS_SUC_EQ; vCONJUNCT1 vLE]);;

(* ------------------------------------------------------------------------ *)
(* Divisions and tagged divisions etc.                                      *)
(* ------------------------------------------------------------------------ *)

let division = new_definition
  [%q {|division(a,b) D <=>
     (D 0 = a) /\
     (?N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = b)))|} ];;

let dsize = new_definition
  [%q {|dsize D =
      @N. (!n. n < N ==> D(n) < D(SUC n)) /\
          (!n. n >= N ==> (D(n) = D(N)))|} ];;

let tdiv = new_definition
  [%q {|tdiv(a,b) (D,p) <=>
     division(a,b) D /\
     (!n. D(n) <= p(n) /\ p(n) <= D(SUC n))|} ];;

(* ------------------------------------------------------------------------ *)
(* Gauges and gauge-fine divisions                                          *)
(* ------------------------------------------------------------------------ *)

let gauge = new_definition
  [%q {|gauge(E) (g:real->real) <=> !x. E x ==> &0 < g(x)|} ];;

let fine = new_definition
  [%q {|fine(g:real->real) (D,p) <=>
     !n. n < (dsize D) ==> (D(SUC n) - D(n)) < g(p(n))|} ];;

(* ------------------------------------------------------------------------ *)
(* Riemann sum                                                              *)
(* ------------------------------------------------------------------------ *)

let rsum = new_definition
  [%q {|rsum (D,(p:num->real)) f =
        sum(0,dsize(D))(\n. f(p n) * (D(SUC n) - D(n)))|} ];;

(* ------------------------------------------------------------------------ *)
(* Gauge integrability (definite)                                           *)
(* ------------------------------------------------------------------------ *)

let defint = new_definition
  [%q {|defint(a,b) f k <=>
     !e. &0 < e ==>
        ?g. gauge(\x. a <= x /\ x <= b) g /\
            !D p. tdiv(a,b) (D,p) /\ fine(g)(D,p) ==>
                abs(rsum(D,p) f - k) < e|} ];;

(* ------------------------------------------------------------------------ *)
(* Useful lemmas about the size of `trivial` divisions etc.                 *)
(* ------------------------------------------------------------------------ *)

let%a vDIVISION_0 = prove(
  [%q {|!a b. (a = b) ==> (dsize(\n. if (n = 0) then a else b) = 0)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN vSUBST_ALL_TAC ----> vREWRITE_TAC[vCOND_ID] ---->
  vREWRITE_TAC[dsize] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_LT_REFL; vNOT_LT] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vSPEC [%q {|0|} ]) ----> vREWRITE_TAC[vCONJUNCT1 vLE];
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vLE_0]]);;

let%a vDIVISION_1 = prove(
  [%q {|!a b. a < b ==> (dsize(\n. if (n = 0) then a else b) = 1)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[dsize] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ----> vX_GEN_TAC [%q {|n:num|} ] ----> vBETA_TAC ---->
  vREWRITE_TAC[vNOT_SUC] ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vMATCH_MP_TAC vLESS_EQUAL_ANTISYM ----> vCONJ_TAC ++-->
     [vPOP_ASSUM(vMP_TAC -| vSPEC [%q {|1|} ] -| vCONJUNCT1) ---->
      vREWRITE_TAC[vARITH] ---->
      vREWRITE_TAC[vREAL_LT_REFL; vNOT_LT];
      vPOP_ASSUM(vMP_TAC -| vSPEC [%q {|2|} ] -| vCONJUNCT2) ---->
      vREWRITE_TAC[num_CONV [%q {|2|} ]; vGE] ---->
      vCONV_TAC vCONTRAPOS_CONV ---->
      vREWRITE_TAC[num_CONV [%q {|1|} ]; vNOT_SUC_LESS_EQ; vCONJUNCT1 vLE] ---->
      vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vNOT_SUC; vNOT_IMP] ---->
      vREWRITE_TAC[vLE_0] ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
      vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vPOP_ASSUM vACCEPT_TAC];
    vDISCH_THEN vSUBST1_TAC ----> vCONJ_TAC ++-->
     [vGEN_TAC ----> vREWRITE_TAC[num_CONV [%q {|1|} ]; vCONJUNCT2 vLT; vNOT_LESS_0] ---->
      vDISCH_THEN vSUBST1_TAC ----> vASM_REWRITE_TAC[];
      vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vGE; num_CONV [%q {|1|} ]] ---->
      vASM_CASES_TAC [%q {|n = 0|} ] ---->
      vASM_REWRITE_TAC[vCONJUNCT1 vLE; vGSYM vNOT_SUC; vNOT_SUC]]]);;

let%a vDIVISION_SINGLE = prove(
  [%q {|!a b. a <= b ==> division(a,b)(\n. if (n = 0) then a else b)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[division] ---->
  vBETA_TAC ----> vREWRITE_TAC[] ---->
  vPOP_ASSUM(vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
   [vEXISTS_TAC [%q {|1|} ] ----> vCONJ_TAC ----> vX_GEN_TAC [%q {|n:num|} ] ++-->
     [vREWRITE_TAC[vLESS_1] ----> vDISCH_THEN vSUBST1_TAC ---->
      vASM_REWRITE_TAC[vNOT_SUC];
      vREWRITE_TAC[vGE] ---->
      vCOND_CASES_TAC ----> vASM_REWRITE_TAC[num_CONV [%q {|1|} ]] ---->
      vREWRITE_TAC[vGSYM vNOT_LT; vLESS_SUC_REFL]];
    vEXISTS_TAC [%q {|0|} ] ----> vREWRITE_TAC[vNOT_LESS_0] ---->
    vASM_REWRITE_TAC[vCOND_ID]]);;

let%a vDIVISION_LHS = prove(
  [%q {|!D a b. division(a,b) D ==> (D(0) = a)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[division] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[th]));;

let%a vDIVISION_THM = prove(
  [%q {|!D a b. division(a,b) D <=>
        (D(0) = a) /\
        (!n. n < (dsize D) ==> D(n) < D(SUC n)) /\
        (!n. n >= (dsize D) ==> (D(n) = b))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[division] ---->
  vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ++-->
   [vALL_TAC; vEXISTS_TAC [%q {|dsize D|} ] ----> vASM_REWRITE_TAC[]] ---->
  vPOP_ASSUM(vX_CHOOSE_THEN [%q {|N:num|} ] vSTRIP_ASSUME_TAC -| vCONJUNCT2) ---->
  vSUBGOAL_THEN [%q {|dsize D = N|} ] (fun th -> vASM_REWRITE_TAC[th]) ---->
  vREWRITE_TAC[dsize] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vX_GEN_TAC [%q {|M:num|} ] ----> vBETA_TAC ----> vEQ_TAC ++-->
   [vALL_TAC; vDISCH_THEN vSUBST1_TAC ----> vASM_REWRITE_TAC[] ---->
    vMP_TAC(vSPEC [%q {|N:num|} ] (vASSUME [%q {|!n:num. n >= N ==> (D n :real = b)|} ])) ---->
    vDISCH_THEN(vMP_TAC -| vREWRITE_RULE[vGE; vLE_REFL]) ---->
    vDISCH_THEN vSUBST1_TAC ----> vFIRST_ASSUM vMATCH_ACCEPT_TAC] ---->
  vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC
   (vSPECL [[%q {|M:num|} ]; [%q {|N:num|} ]] vLESS_LESS_CASES) ---->
  vASM_REWRITE_TAC[] ++-->
   [vDISCH_THEN(vMP_TAC -| vSPEC [%q {|SUC M|} ] -| vCONJUNCT2) ---->
    vREWRITE_TAC[vGE; vLESS_EQ_SUC_REFL] ----> vDISCH_TAC ---->
    vUNDISCH_TAC [%q {|!n. n < N ==> (D n) < (D(SUC n))|} ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|M:num|} ]) ----> vASM_REWRITE_TAC[vREAL_LT_REFL];
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|N:num|} ] -| vCONJUNCT1) ----> vASM_REWRITE_TAC[] ---->
    vUNDISCH_TAC [%q {|!n:num. n >= N ==> (D n :real = b)|} ] ---->
    vDISCH_THEN(fun th -> vMP_TAC(vSPEC [%q {|N:num|} ] th) ---->
    vMP_TAC(vSPEC [%q {|SUC N|} ] th)) ---->
    vREWRITE_TAC[vGE; vLESS_EQ_SUC_REFL; vLE_REFL] ---->
    vDISCH_THEN vSUBST1_TAC ----> vDISCH_THEN vSUBST1_TAC ---->
    vREWRITE_TAC[vREAL_LT_REFL]]);;

let%a vDIVISION_RHS = prove(
  [%q {|!D a b. division(a,b) D ==> (D(dsize D) = b)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vDIVISION_THM] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|dsize D|} ] -| last -| vCONJUNCTS) ---->
  vREWRITE_TAC[vGE; vLE_REFL]);;

let%a vDIVISION_LT_GEN = prove(
  [%q {|!D a b m n. division(a,b) D /\
               m < n /\
               n <= (dsize D) ==> D(m) < D(n)|} ],
  vREPEAT vSTRIP_TAC ----> vUNDISCH_TAC [%q {|m:num < n|} ] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vMP_TAC -| vMATCH_MP vLESS_ADD_1) ---->
  vREWRITE_TAC[vGSYM vADD1] ----> vDISCH_THEN vSUBST_ALL_TAC ---->
  vUNDISCH_TAC [%q {|(m + (SUC d)) <= (dsize D)|} ] ---->
  vSPEC_TAC([%q {|d:num|} ],[%q {|d:num|} ]) ----> vINDUCT_TAC ++-->
   [vREWRITE_TAC[vADD_CLAUSES] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vOR_LESS) ---->
    vRULE_ASSUM_TAC(vREWRITE_RULE[vDIVISION_THM]) ---->
    vASM_REWRITE_TAC[];
    vREWRITE_TAC[vADD_CLAUSES] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vOR_LESS) ---->
    vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LT_TRANS ---->
    vEXISTS_TAC [%q {|D(m + (SUC d)):real|} ] ----> vCONJ_TAC ++-->
     [vFIRST_ASSUM vMATCH_MP_TAC ----> vREWRITE_TAC[vADD_CLAUSES] ---->
      vMATCH_MP_TAC vLT_IMP_LE ----> vASM_REWRITE_TAC[];
      vREWRITE_TAC[vADD_CLAUSES] ---->
      vFIRST_ASSUM(vMATCH_MP_TAC -| el 1 -|
        vCONJUNCTS -| vREWRITE_RULE[vDIVISION_THM]) ---->
      vASM_REWRITE_TAC[]]]);;

let%a vDIVISION_LT = prove(
  [%q {|!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(0) < D(SUC n)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vDIVISION_THM] ----> vSTRIP_TAC ---->
  vINDUCT_TAC ----> vDISCH_THEN(fun th -> vASSUME_TAC th ---->
      vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|D(SUC n):real|} ] ---->
  vASM_REWRITE_TAC[] ----> vUNDISCH_TAC [%q {|D(0):real = a|} ] ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|SUC n|} ] ---->
  vASM_REWRITE_TAC[vLESS_SUC_REFL]);;

let%a vDIVISION_LE = prove(
  [%q {|!D a b. division(a,b) D ==> a <= b|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vDIVISION_LT) ---->
  vPOP_ASSUM(vSTRIP_ASSUME_TAC -| vREWRITE_RULE[vDIVISION_THM]) ---->
  vUNDISCH_TAC [%q {|D(0):real = a|} ] ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vUNDISCH_TAC [%q {|!n. n >= (dsize D) ==> (D n = b)|} ] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|dsize D|} ]) ---->
  vREWRITE_TAC[vGE; vLE_REFL] ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|PRE(dsize D)|} ]) ---->
  vSTRUCT_CASES_TAC(vSPEC [%q {|dsize D|} ] num_CASES) ---->
  vASM_REWRITE_TAC[vPRE; vREAL_LE_REFL; vLESS_SUC_REFL; vREAL_LT_IMP_LE]);;

let%a vDIVISION_GT = prove(
  [%q {|!D a b. division(a,b) D ==> !n. n < (dsize D) ==> D(n) < D(dsize D)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDIVISION_LT_GEN ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|a:real|} ]; [%q {|b:real|} ]] ---->
  vASM_REWRITE_TAC[vLE_REFL]);;

let%a vDIVISION_EQ = prove(
  [%q {|!D a b. division(a,b) D ==> ((a = b) <=> (dsize D = 0))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vDIVISION_LT) ---->
  vPOP_ASSUM(vSTRIP_ASSUME_TAC -| vREWRITE_RULE[vDIVISION_THM]) ---->
  vUNDISCH_TAC [%q {|D(0):real = a|} ] ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vUNDISCH_TAC [%q {|!n. n >= (dsize D) ==> (D n = b)|} ] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|dsize D|} ]) ---->
  vREWRITE_TAC[vGE; vLE_REFL] ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|PRE(dsize D)|} ]) ---->
  vSTRUCT_CASES_TAC(vSPEC [%q {|dsize D|} ] num_CASES) ---->
  vASM_REWRITE_TAC[vPRE; vNOT_SUC; vLESS_SUC_REFL; vREAL_LT_IMP_NE]);;

let%a vDIVISION_LBOUND = prove(
  [%q {|!D a b r. division(a,b) D ==> a <= D(r)|} ],
  vREWRITE_TAC[vDIVISION_THM; vRIGHT_FORALL_IMP_THM] ---->
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vREAL_LE_REFL] ---->
  vDISJ_CASES_TAC(vSPECL [[%q {|SUC r|} ]; [%q {|dsize D|} ]] vLTE_CASES) ++-->
   [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|(D:num->real) r|} ] ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
    vFIRST_ASSUM vMATCH_MP_TAC ---->
    vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|SUC r|} ] ---->
    vASM_REWRITE_TAC[vLESS_SUC_REFL];
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|b:real|} ] ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vDIVISION_LE ---->
      vEXISTS_TAC [%q {|D:num->real|} ] ----> vASM_REWRITE_TAC[vDIVISION_THM];
      vMATCH_MP_TAC vREAL_EQ_IMP_LE ----> vCONV_TAC vSYM_CONV ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[vGE]]]);;

let%a vDIVISION_LBOUND_LT = prove(
  [%q {|!D a b n. division(a,b) D /\ ~(dsize D = 0) ==> a < D(SUC n)|} ],
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ----> vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vSYM -| vMATCH_MP vDIVISION_LHS) ---->
  vDISJ_CASES_TAC(vSPECL [[%q {|dsize D|} ]; [%q {|SUC n|} ]] vLTE_CASES) ++-->
   [vFIRST_ASSUM(vMP_TAC -| el 2 -| vCONJUNCTS -| vREWRITE_RULE[vDIVISION_THM]) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|SUC n|} ]) ----> vREWRITE_TAC[vGE] ---->
    vIMP_RES_THEN vASSUME_TAC vLT_IMP_LE ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN vSUBST1_TAC ---->
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM -| vMATCH_MP vDIVISION_RHS) ---->
    vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vDIVISION_GT) ---->
    vASM_REWRITE_TAC[vGSYM vNOT_LE; vCONJUNCT1 vLE];
    vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vDIVISION_LT) ---->
    vMATCH_MP_TAC vOR_LESS ----> vASM_REWRITE_TAC[]]);;

let%a vDIVISION_UBOUND = prove(
  [%q {|!D a b r. division(a,b) D ==> D(r) <= b|} ],
  vREWRITE_TAC[vDIVISION_THM] ----> vREPEAT vSTRIP_TAC ---->
  vDISJ_CASES_TAC(vSPECL [[%q {|r:num|} ]; [%q {|dsize D|} ]] vLTE_CASES) ++-->
   [vALL_TAC;
    vMATCH_MP_TAC vREAL_EQ_IMP_LE ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[vGE]] ---->
  vSUBGOAL_THEN [%q {|!r. D((dsize D) - r) <= b|} ] vMP_TAC ++-->
   [vALL_TAC;
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|(dsize D) - r|} ]) ---->
    vMATCH_MP_TAC vEQ_IMP ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ----> vAP_TERM_TAC ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vSUB_SUB
      (vMATCH_MP vLT_IMP_LE th)]) ---->
    vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB]] ---->
  vUNDISCH_TAC [%q {|r < (dsize D)|} ] ----> vDISCH_THEN(vK vALL_TAC) ---->
  vINDUCT_TAC ++-->
   [vREWRITE_TAC[vSUB_0] ----> vMATCH_MP_TAC vREAL_EQ_IMP_LE ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vREWRITE_TAC[vGE; vLE_REFL];
    vALL_TAC] ---->
  vDISJ_CASES_TAC(vSPECL [[%q {|r:num|} ]; [%q {|dsize D|} ]] vLTE_CASES) ++-->
   [vALL_TAC;
    vSUBGOAL_THEN [%q {|(dsize D) - (SUC r) = 0|} ] vSUBST1_TAC ++-->
     [vREWRITE_TAC[vSUB_EQ_0] ----> vMATCH_MP_TAC vLE_TRANS ---->
      vEXISTS_TAC [%q {|r:num|} ] ----> vASM_REWRITE_TAC[vLESS_EQ_SUC_REFL];
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vDIVISION_LE ---->
      vEXISTS_TAC [%q {|D:num->real|} ] ----> vASM_REWRITE_TAC[vDIVISION_THM]]] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|D((dsize D) - r):real|} ] ----> vASM_REWRITE_TAC[] ---->
  vSUBGOAL_THEN [%q {|(dsize D) - r = SUC((dsize D) - (SUC r))|} ]
  vSUBST1_TAC ++-->
   [vALL_TAC;
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vMATCH_MP_TAC vLESS_CASES_IMP ---->
    vREWRITE_TAC[vNOT_LT; vLE_LT; vSUB_LESS_EQ] ---->
    vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vREWRITE_TAC[vSUB_EQ_EQ_0; vNOT_SUC] ---->
    vDISCH_THEN vSUBST_ALL_TAC ---->
    vUNDISCH_TAC [%q {|r < 0|} ] ----> vREWRITE_TAC[vNOT_LESS_0]] ---->
  vMP_TAC(vSPECL [[%q {|dsize D|} ]; [%q {|SUC r|} ]] (vCONJUNCT2 vSUB_OLD)) ---->
  vCOND_CASES_TAC ++-->
   [vREWRITE_TAC[vSUB_EQ_0; vLE_SUC] ---->
    vASM_REWRITE_TAC[vGSYM vNOT_LT];
    vDISCH_THEN (vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vSUB_SUC]]);;

let%a vDIVISION_UBOUND_LT = prove(
  [%q {|!D a b n. division(a,b) D /\
             n < dsize D ==> D(n) < b|} ],
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vSYM -| vMATCH_MP vDIVISION_RHS) ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vDIVISION_GT) ---->
  vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Divisions of adjacent intervals can be combined into one                 *)
(* ------------------------------------------------------------------------ *)

let%a vDIVISION_APPEND_LEMMA1 = prove(
  [%q {|!a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
        (!n. n < ((dsize D1) + (dsize D2)) ==>
                (\n. if (n < (dsize D1)) then  D1(n) else
                     D2(n - (dsize D1)))(n) <
   (\n. if (n < (dsize D1)) then  D1(n) else D2(n - (dsize D1)))(SUC n)) /\
        (!n. n >= ((dsize D1) + (dsize D2)) ==>
               ((\n. if (n < (dsize D1)) then  D1(n) else
   D2(n - (dsize D1)))(n) = (\n. if (n < (dsize D1)) then  D1(n) else
   D2(n - (dsize D1)))((dsize D1) + (dsize D2))))|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ----> vCONJ_TAC ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_TAC ----> vBETA_TAC ++-->
   [vASM_CASES_TAC [%q {|(SUC n) < (dsize D1)|} ] ----> vASM_REWRITE_TAC[] ++-->
     [vSUBGOAL_THEN [%q {|n < (dsize D1)|} ] vASSUME_TAC ---->
      vASM_REWRITE_TAC[] ++-->
       [vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|SUC n|} ] ---->
        vASM_REWRITE_TAC[vLESS_SUC_REFL];
        vUNDISCH_TAC [%q {|division(a,b) D1|} ] ----> vREWRITE_TAC[vDIVISION_THM] ---->
        vSTRIP_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
        vFIRST_ASSUM vACCEPT_TAC];
      vASM_CASES_TAC [%q {|n < (dsize D1)|} ] ----> vASM_REWRITE_TAC[] ++-->
       [vRULE_ASSUM_TAC(vREWRITE_RULE[vNOT_LT]) ---->
        vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|b:real|} ] ---->
        vCONJ_TAC ++-->
         [vMATCH_MP_TAC vDIVISION_UBOUND_LT ---->
          vEXISTS_TAC [%q {|a:real|} ] ----> vASM_REWRITE_TAC[];
          vMATCH_MP_TAC vDIVISION_LBOUND ---->
          vEXISTS_TAC [%q {|c:real|} ] ----> vASM_REWRITE_TAC[]];
        vUNDISCH_TAC [%q {|~(n < (dsize D1))|} ] ---->
        vREWRITE_TAC[vNOT_LT] ---->
        vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST_ALL_TAC -|
          vREWRITE_RULE[vLE_EXISTS]) ---->
        vREWRITE_TAC[vSUB_OLD; vGSYM vNOT_LE; vLE_ADD] ---->
        vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB] ---->
        vFIRST_ASSUM(vMATCH_MP_TAC -| el 1 -| vCONJUNCTS -|
          vREWRITE_RULE[vDIVISION_THM]) ---->
        vUNDISCH_TAC [%q {|((dsize D1) + d) <
                     ((dsize D1) + (dsize D2))|} ] ---->
        vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vLT_ADD_RCANCEL]]];
    vREWRITE_TAC[vGSYM vNOT_LE; vLE_ADD] ---->
    vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB] ---->
    vREWRITE_TAC[vNOT_LE] ----> vCOND_CASES_TAC ---->
    vUNDISCH_TAC [%q {|n >= ((dsize D1) + (dsize D2))|} ] ++-->
     [vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_TAC ---->
      vREWRITE_TAC[vGE; vNOT_LE] ---->
      vMATCH_MP_TAC vLTE_TRANS ----> vEXISTS_TAC [%q {|dsize D1|} ] ---->
      vASM_REWRITE_TAC[vLE_ADD];
      vREWRITE_TAC[vGE; vLE_EXISTS] ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST_ALL_TAC) ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
      vREWRITE_TAC[vADD_SUB] ---->
      vFIRST_ASSUM(vCHANGED_TAC -|
       (vSUBST1_TAC -| vMATCH_MP vDIVISION_RHS)) ---->
      vFIRST_ASSUM(vMATCH_MP_TAC -| el 2 -| vCONJUNCTS -|
        vREWRITE_RULE[vDIVISION_THM]) ---->
      vREWRITE_TAC[vGE; vLE_ADD]]]);;

let%a vDIVISION_APPEND_LEMMA2 = prove(
  [%q {|!a b c D1 D2. division(a,b) D1 /\ division(b,c) D2 ==>
                   (dsize(\n. if (n < (dsize D1)) then  D1(n) else
       D2(n - (dsize D1))) = dsize(D1) + dsize(D2))|} ],
  vREPEAT vSTRIP_TAC ----> vGEN_REWRITE_TAC vLAND_CONV [dsize] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vX_GEN_TAC [%q {|N:num|} ] ----> vBETA_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN((---->) (vMATCH_MP_TAC vLESS_EQUAL_ANTISYM) -| vMP_TAC) ---->
    vCONV_TAC vCONTRAPOS_CONV ---->
    vREWRITE_TAC[vDE_MORGAN_THM; vNOT_LE] ---->
    vDISCH_THEN vDISJ_CASES_TAC ++-->
     [vDISJ1_TAC ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|dsize(D1) + dsize(D2)|} ]) ---->
      vASM_REWRITE_TAC[] ---->
      vREWRITE_TAC[vGSYM vNOT_LE; vLE_ADD] ---->
      vSUBGOAL_THEN [%q {|!x y. x <= SUC(x + y)|} ] vASSUME_TAC ++-->
       [vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
        vEXISTS_TAC [%q {|x + y:num|} ] ---->
        vREWRITE_TAC[vLE_ADD; vLESS_EQ_SUC_REFL]; vALL_TAC] ---->
      vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vSUB_OLD; vGSYM vNOT_LE] ---->
      vREWRITE_TAC[vLE_ADD] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
      vREWRITE_TAC[vADD_SUB] ---->
      vMP_TAC(vASSUME [%q {|division(b,c) D2|} ]) ----> vREWRITE_TAC[vDIVISION_THM] ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|SUC(dsize D2)|} ] -| el 2 -| vCONJUNCTS) ---->
      vREWRITE_TAC[vGE; vLESS_EQ_SUC_REFL] ---->
      vDISCH_THEN vSUBST1_TAC ---->
      vFIRST_ASSUM(vCHANGED_TAC -| vSUBST1_TAC -| vMATCH_MP vDIVISION_RHS) ---->
      vREWRITE_TAC[vREAL_LT_REFL];
      vDISJ2_TAC ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|dsize(D1) + dsize(D2)|} ]) ---->
      vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vLT_IMP_LE) ---->
      vASM_REWRITE_TAC[vGE] ---->
      vREWRITE_TAC[vGSYM vNOT_LE; vLE_ADD] ---->
      vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB] ---->
      vCOND_CASES_TAC ++-->
       [vSUBGOAL_THEN [%q {|D1(N:num) < D2(dsize D2)|} ] vMP_TAC ++-->
         [vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|b:real|} ] ---->
          vCONJ_TAC ++-->
           [vMATCH_MP_TAC vDIVISION_UBOUND_LT ----> vEXISTS_TAC [%q {|a:real|} ] ---->
            vASM_REWRITE_TAC[vGSYM vNOT_LE];
            vMATCH_MP_TAC vDIVISION_LBOUND ---->
            vEXISTS_TAC [%q {|c:real|} ] ----> vASM_REWRITE_TAC[]];
          vCONV_TAC vCONTRAPOS_CONV ----> vASM_REWRITE_TAC[] ---->
          vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vREAL_LT_REFL]];
        vRULE_ASSUM_TAC(vREWRITE_RULE[]) ---->
        vSUBGOAL_THEN [%q {|D2(N - (dsize D1)) < D2(dsize D2)|} ] vMP_TAC ++-->
         [vMATCH_MP_TAC vDIVISION_LT_GEN ---->
          vMAP_EVERY vEXISTS_TAC [[%q {|b:real|} ]; [%q {|c:real|} ]] ---->
          vASM_REWRITE_TAC[vLE_REFL] ---->
          vREWRITE_TAC[vGSYM vNOT_LE] ---->
          vREWRITE_TAC[vSUB_LEFT_LESS_EQ; vDE_MORGAN_THM] ---->
          vONCE_REWRITE_TAC[vADD_SYM] ----> vASM_REWRITE_TAC[vNOT_LE] ---->
          vUNDISCH_TAC [%q {|dsize(D1) <= N|} ] ---->
          vREWRITE_TAC[vLE_EXISTS] ---->
          vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST_ALL_TAC) ---->
          vRULE_ASSUM_TAC(vONCE_REWRITE_RULE[vADD_SYM]) ---->
          vRULE_ASSUM_TAC(vREWRITE_RULE[vLT_ADD_RCANCEL]) ---->
          vMATCH_MP_TAC vLET_TRANS ----> vEXISTS_TAC [%q {|d:num|} ] ---->
          vASM_REWRITE_TAC[vLE_0];
          vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[] ---->
          vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vREAL_LT_REFL]]]];
  vDISCH_THEN vSUBST1_TAC ----> vCONJ_TAC ++-->
   [vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_TAC ---->
    vASM_CASES_TAC [%q {|(SUC n) < (dsize(D1))|} ] ---->
    vASM_REWRITE_TAC[] ++-->
     [vSUBGOAL_THEN [%q {|n < (dsize(D1))|} ] vASSUME_TAC ++-->
       [vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|SUC n|} ] ---->
        vASM_REWRITE_TAC[vLESS_SUC_REFL]; vALL_TAC] ---->
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vDIVISION_LT_GEN ---->
      vMAP_EVERY vEXISTS_TAC [[%q {|a:real|} ]; [%q {|b:real|} ]] ---->
      vASM_REWRITE_TAC[vLESS_SUC_REFL] ---->
      vMATCH_MP_TAC vLT_IMP_LE ----> vASM_REWRITE_TAC[];
      vCOND_CASES_TAC ++-->
       [vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|b:real|} ] ---->
        vCONJ_TAC ++-->
         [vMATCH_MP_TAC vDIVISION_UBOUND_LT ----> vEXISTS_TAC [%q {|a:real|} ] ---->
          vASM_REWRITE_TAC[];
          vFIRST_ASSUM(vMATCH_ACCEPT_TAC -| vMATCH_MP vDIVISION_LBOUND)];
        vMATCH_MP_TAC vDIVISION_LT_GEN ---->
        vMAP_EVERY vEXISTS_TAC [[%q {|b:real|} ]; [%q {|c:real|} ]] ---->
        vASM_REWRITE_TAC[] ---->
        vCONJ_TAC ++--> [vASM_REWRITE_TAC[vSUB_OLD; vLESS_SUC_REFL]; vALL_TAC] ---->
        vREWRITE_TAC[vREWRITE_RULE[vGE] vSUB_LEFT_GREATER_EQ] ---->
        vONCE_REWRITE_TAC[vADD_SYM] ----> vASM_REWRITE_TAC[vLE_SUC_LT]]];
    vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vGE] ----> vDISCH_TAC ---->
    vREWRITE_TAC[vGSYM vNOT_LE; vLE_ADD] ---->
    vSUBGOAL_THEN [%q {|(dsize D1) <= n|} ] vASSUME_TAC ++-->
     [vMATCH_MP_TAC vLE_TRANS ---->
      vEXISTS_TAC [%q {|dsize D1 + dsize D2|} ] ---->
      vASM_REWRITE_TAC[vLE_ADD];
      vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
      vREWRITE_TAC[vADD_SUB] ---->
      vFIRST_ASSUM(vCHANGED_TAC -| vSUBST1_TAC -| vMATCH_MP vDIVISION_RHS) ---->
      vFIRST_ASSUM(vMATCH_MP_TAC -| el 2 -|
        vCONJUNCTS -| vREWRITE_RULE[vDIVISION_THM]) ---->
      vREWRITE_TAC[vGE; vSUB_LEFT_LESS_EQ] ---->
      vONCE_REWRITE_TAC[vADD_SYM] ----> vASM_REWRITE_TAC[]]]]);;

let%a vDIVISION_APPEND_EXPLICIT = prove
 ([%q {|!a b c g d1 p1 d2 p2.
        tdiv(a,b) (d1,p1) /\
        fine g (d1,p1) /\
        tdiv(b,c) (d2,p2) /\
        fine g (d2,p2)
        ==> tdiv(a,c)
              ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            fine g ((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
               (\n. if n < dsize d1
                    then p1(n) else p2(n - (dsize d1)))) /\
            !f. rsum((\n. if n < dsize d1 then  d1(n) else d2(n - (dsize d1))),
                     (\n. if n < dsize d1
                          then p1(n) else p2(n - (dsize d1)))) f =
                rsum(d1,p1) f + rsum(d2,p2) f|} ],
  vMAP_EVERY vX_GEN_TAC
   [[%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|c:real|} ]; [%q {|g:real->real|} ];
    [%q {|D1:num->real|} ]; [%q {|p1:num->real|} ]; [%q {|D2:num->real|} ]; [%q {|p2:num->real|} ]] ---->
  vSTRIP_TAC ----> vREWRITE_TAC[vCONJ_ASSOC] ----> vCONJ_TAC ++-->
   [vALL_TAC;
    vGEN_TAC ----> vREWRITE_TAC[rsum] ---->
    vMP_TAC(vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|c:real|} ];
                  [%q {|D1:num->real|} ]; [%q {|D2:num->real|} ]] vDIVISION_APPEND_LEMMA2) ---->
    vANTS_TAC ++--> [vASM_MESON_TAC[tdiv]; vALL_TAC] ---->
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vGSYM vSUM_SPLIT] ---->
    vREWRITE_TAC[vSUM_REINDEX] ----> vBINOP_TAC ----> vMATCH_MP_TAC vSUM_EQ ---->
    vSIMP_TAC[vADD_CLAUSES; vARITH_RULE [%q {|~(r + d < d:num)|} ];
             vARITH_RULE [%q {|~(SUC(r + d) < d)|} ]; vADD_SUB;
             vARITH_RULE [%q {|SUC(r + d) - d = SUC r|} ]] ---->
    vX_GEN_TAC [%q {|k:num|} ] ----> vSTRIP_TAC ----> vAP_TERM_TAC ---->
    vASM_SIMP_TAC[vARITH_RULE [%q {|k < n ==> (SUC k < n <=> ~(n = SUC k))|} ]] ---->
    vASM_CASES_TAC [%q {|dsize D1 = SUC k|} ] ----> vASM_REWRITE_TAC[vSUB_REFL] ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vASM_MESON_TAC[tdiv; vDIVISION_LHS; vDIVISION_RHS]] ---->
  vDISJ_CASES_TAC(vGSYM (vSPEC [%q {|dsize(D1)|} ] vLESS_0_CASES)) ++-->
   [vASM_REWRITE_TAC[vNOT_LESS_0; vSUB_0] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ---->
    vSUBGOAL_THEN [%q {|a:real = b|} ] (fun th -> vASM_REWRITE_TAC[th]) ---->
    vMP_TAC(vSPECL [[%q {|D1:num->real|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]] vDIVISION_EQ) ---->
    vRULE_ASSUM_TAC(vREWRITE_RULE[tdiv]) ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vCONJ_TAC ++-->
   [vALL_TAC;
    vREWRITE_TAC[fine] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
    vRULE_ASSUM_TAC(vREWRITE_RULE[tdiv]) ---->
    vMP_TAC(vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|c:real|} ];
                  [%q {|D1:num->real|} ]; [%q {|D2:num->real|} ]] vDIVISION_APPEND_LEMMA2) ---->
    vASM_REWRITE_TAC[] ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ----> vBETA_TAC ---->
    vDISCH_TAC ----> vASM_CASES_TAC [%q {|(SUC n) < (dsize D1)|} ] ---->
    vASM_REWRITE_TAC[] ++-->
     [vSUBGOAL_THEN [%q {|n < (dsize D1)|} ] vASSUME_TAC ++-->
       [vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|SUC n|} ] ---->
        vASM_REWRITE_TAC[vLESS_SUC_REFL]; vALL_TAC] ---->
      vASM_REWRITE_TAC[] ---->
      vFIRST_ASSUM(vMATCH_MP_TAC -| vREWRITE_RULE[fine]) ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vASM_CASES_TAC [%q {|n < (dsize D1)|} ] ----> vASM_REWRITE_TAC[] ++-->
     [vSUBGOAL_THEN [%q {|SUC n = dsize D1|} ] vASSUME_TAC ++-->
       [vMATCH_MP_TAC vLESS_EQUAL_ANTISYM ---->
        vASM_REWRITE_TAC[vGSYM vNOT_LT] ---->
        vREWRITE_TAC[vNOT_LT] ----> vMATCH_MP_TAC vLESS_OR ---->
        vASM_REWRITE_TAC[];
        vASM_REWRITE_TAC[vSUB_REFL] ---->
        vFIRST_ASSUM(vCHANGED_TAC -| vSUBST1_TAC -| vMATCH_MP vDIVISION_LHS -|
          vCONJUNCT1) ---->
        vFIRST_ASSUM(vCHANGED_TAC -| vSUBST1_TAC -| vSYM -|
          vMATCH_MP vDIVISION_RHS -|  vCONJUNCT1) ---->
        vSUBST1_TAC(vSYM(vASSUME [%q {|SUC n = dsize D1|} ])) ---->
        vFIRST_ASSUM(vMATCH_MP_TAC -| vREWRITE_RULE[fine]) ---->
        vASM_REWRITE_TAC[]];
      vASM_REWRITE_TAC[vSUB_OLD] ----> vUNDISCH_TAC [%q {|~(n < (dsize D1))|} ] ---->
      vREWRITE_TAC[vLE_EXISTS; vNOT_LT] ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST_ALL_TAC) ---->
      vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB] ---->
      vFIRST_ASSUM(vMATCH_MP_TAC -| vREWRITE_RULE[fine]) ---->
      vRULE_ASSUM_TAC(vONCE_REWRITE_RULE[vADD_SYM]) ---->
      vRULE_ASSUM_TAC(vREWRITE_RULE[vLT_ADD_RCANCEL]) ---->
      vFIRST_ASSUM vACCEPT_TAC]] ---->
  vREWRITE_TAC[tdiv] ----> vBETA_TAC ----> vCONJ_TAC ++-->
   [vRULE_ASSUM_TAC(vREWRITE_RULE[tdiv]) ---->
    vREWRITE_TAC[vDIVISION_THM] ----> vCONJ_TAC ++-->
     [vBETA_TAC ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vDIVISION_LHS ----> vEXISTS_TAC [%q {|b:real|} ] ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|c = (\n. if (n < (dsize D1)) then  D1(n) else D2(n -
                  (dsize D1))) (dsize(D1) + dsize(D2))|} ] vSUBST1_TAC ++-->
     [vBETA_TAC ----> vREWRITE_TAC[vGSYM vNOT_LE; vLE_ADD] ---->
      vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB] ---->
      vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vDIVISION_RHS ---->
      vEXISTS_TAC [%q {|b:real|} ] ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vMP_TAC(vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|c:real|} ];
                 [%q {|D1:num->real|} ]; [%q {|D2:num->real|} ]] vDIVISION_APPEND_LEMMA2) ---->
    vASM_REWRITE_TAC[] ----> vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
    vMATCH_MP_TAC (vBETA_RULE vDIVISION_APPEND_LEMMA1) ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|c:real|} ]] ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vRULE_ASSUM_TAC(vREWRITE_RULE[tdiv]) ---->
  vASM_CASES_TAC [%q {|(SUC n) < (dsize D1)|} ] ----> vASM_REWRITE_TAC[] ++-->
   [vSUBGOAL_THEN [%q {|n < (dsize D1)|} ] vASSUME_TAC ++-->
     [vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|SUC n|} ] ---->
      vASM_REWRITE_TAC[vLESS_SUC_REFL]; vALL_TAC] ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ++-->
   [vASM_REWRITE_TAC[vSUB_OLD] ---->
    vFIRST_ASSUM(vCHANGED_TAC -| vSUBST1_TAC -| vMATCH_MP vDIVISION_LHS -|
      vCONJUNCT1) ---->
    vFIRST_ASSUM(vCHANGED_TAC -| vSUBST1_TAC -| vSYM -|
      vMATCH_MP vDIVISION_RHS -|  vCONJUNCT1) ---->
    vSUBGOAL_THEN [%q {|dsize D1 = SUC n|} ] (fun th -> vASM_REWRITE_TAC[th]) ---->
    vMATCH_MP_TAC vLESS_EQUAL_ANTISYM ---->
    vASM_REWRITE_TAC[vGSYM vNOT_LT] ----> vREWRITE_TAC[vNOT_LT] ---->
    vMATCH_MP_TAC vLESS_OR ----> vASM_REWRITE_TAC[];
    vASM_REWRITE_TAC[vSUB_OLD]]);;

let%a vDIVISION_APPEND_STRONG = prove
 ([%q {|!a b c D1 p1 D2 p2.
        tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1) /\
        tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)
        ==> ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p) /\
                  !f. rsum(D,p) f = rsum(D1,p1) f + rsum(D2,p2) f|} ],
  vREPEAT vSTRIP_TAC ----> vMAP_EVERY vEXISTS_TAC
   [[%q {|\n. if n < dsize D1 then D1(n):real else D2(n - (dsize D1))|} ];
    [%q {|\n. if n < dsize D1 then p1(n):real else p2(n - (dsize D1))|} ]] ---->
  vMATCH_MP_TAC vDIVISION_APPEND_EXPLICIT ----> vASM_MESON_TAC[]);;

let%a vDIVISION_APPEND = prove(
  [%q {|!a b c.
      (?D1 p1. tdiv(a,b) (D1,p1) /\ fine(g) (D1,p1)) /\
      (?D2 p2. tdiv(b,c) (D2,p2) /\ fine(g) (D2,p2)) ==>
        ?D p. tdiv(a,c) (D,p) /\ fine(g) (D,p)|} ],
  vMESON_TAC[vDIVISION_APPEND_STRONG]);;

(* ------------------------------------------------------------------------ *)
(* We can always find a division which is fine wrt any gauge                *)
(* ------------------------------------------------------------------------ *)

let%a vDIVISION_EXISTS = prove(
  [%q {|!a b g. a <= b /\ gauge(\x. a <= x /\ x <= b) g ==>
        ?D p. tdiv(a,b) (D,p) /\ fine(g) (D,p)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  (vMP_TAC -| vC vSPEC vBOLZANO_LEMMA)
    [%q {|\(u,v). a <= u /\ v <= b ==> ?D p. tdiv(u,v) (D,p) /\ fine(g) (D,p)|} ] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ---->
  vW(vC vSUBGOAL_THEN (fun t ->vREWRITE_TAC[t]) -|
  funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vCONJ_TAC;
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ]]) ---->
    vREWRITE_TAC[vREAL_LE_REFL]]
  ++-->
   [vMAP_EVERY vX_GEN_TAC [[%q {|u:real|} ]; [%q {|v:real|} ]; [%q {|w:real|} ]] ---->
    vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDIVISION_APPEND ---->
    vEXISTS_TAC [%q {|v:real|} ] ----> vCONJ_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|w:real|} ];
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|u:real|} ]] ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vX_GEN_TAC [%q {|x:real|} ] ----> vASM_CASES_TAC [%q {|a <= x /\ x <= b|} ] ++-->
   [vALL_TAC;
    vEXISTS_TAC [%q {|&1|} ] ----> vREWRITE_TAC[vREAL_LT_01] ---->
    vMAP_EVERY vX_GEN_TAC [[%q {|w:real|} ]; [%q {|y:real|} ]] ----> vSTRIP_TAC ---->
    vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_THEN(vK vALL_TAC) ---->
    vFIRST_ASSUM(vUNDISCH_TAC -| check is_neg -| concl) ---->
    vREWRITE_TAC[vDE_MORGAN_THM; vREAL_NOT_LE] ---->
    vDISCH_THEN vDISJ_CASES_TAC ++-->
     [vDISJ1_TAC ----> vMATCH_MP_TAC vREAL_LET_TRANS;
      vDISJ2_TAC ----> vMATCH_MP_TAC vREAL_LTE_TRANS] ---->
    vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[]] ---->
  vUNDISCH_TAC [%q {|gauge(\x. a <= x /\ x <= b) g|} ] ---->
  vREWRITE_TAC[gauge] ----> vBETA_TAC ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP th)) ---->
  vEXISTS_TAC [%q {|(g:real->real) x|} ] ----> vASM_REWRITE_TAC[] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|w:real|} ]; [%q {|y:real|} ]] ----> vREPEAT vSTRIP_TAC ---->
  vEXISTS_TAC [%q {|\n. if (n = 0) then (w:real) else y|} ] ---->
  vEXISTS_TAC [%q {|\n. if (n = 0) then (x:real) else y|} ] ---->
  vSUBGOAL_THEN [%q {|w <= y|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vCONJ_TAC ++-->
   [vREWRITE_TAC[tdiv] ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vDIVISION_SINGLE ----> vFIRST_ASSUM vACCEPT_TAC;
      vX_GEN_TAC [%q {|n:num|} ] ----> vBETA_TAC ----> vREWRITE_TAC[vNOT_SUC] ---->
      vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_LE_REFL]];
    vREWRITE_TAC[fine] ----> vBETA_TAC ----> vREWRITE_TAC[vNOT_SUC] ---->
    vX_GEN_TAC [%q {|n:num|} ] ---->
    vDISJ_CASES_THEN vMP_TAC (vREWRITE_RULE[vREAL_LE_LT] (vASSUME [%q {|w <= y|} ])) ++-->
     [vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vDIVISION_1) ---->
      vASM_REWRITE_TAC[num_CONV [%q {|1|} ]; vCONJUNCT2 vLT; vNOT_LESS_0] ---->
      vDISCH_THEN vSUBST1_TAC ----> vASM_REWRITE_TAC[];
      vDISCH_THEN(vSUBST1_TAC -| vMATCH_MP vDIVISION_0) ---->
      vREWRITE_TAC[vNOT_LESS_0]]]);;

(* ------------------------------------------------------------------------ *)
(* Lemmas about combining gauges                                            *)
(* ------------------------------------------------------------------------ *)

let%a vGAUGE_MIN = prove(
  [%q {|!E g1 g2. gauge(E) g1 /\ gauge(E) g2 ==>
        gauge(E) (\x. if g1(x) < g2(x) then g1(x) else g2(x))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[gauge] ----> vSTRIP_TAC ---->
  vX_GEN_TAC [%q {|x:real|} ] ----> vBETA_TAC ----> vDISCH_TAC ---->
  vCOND_CASES_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vFIRST_ASSUM vACCEPT_TAC);;

let%a vFINE_MIN = prove(
  [%q {|!g1 g2 D p. fine (\x. if g1(x) < g2(x) then g1(x) else g2(x)) (D,p) ==>
        fine(g1) (D,p) /\ fine(g2) (D,p)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[fine] ---->
  vBETA_TAC ----> vDISCH_TAC ----> vCONJ_TAC ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[] ----> vDISCH_TAC ++-->
   [vRULE_ASSUM_TAC(vREWRITE_RULE[vREAL_NOT_LT]) ---->
    vMATCH_MP_TAC vREAL_LTE_TRANS;
    vMATCH_MP_TAC vREAL_LT_TRANS] ---->
  vFIRST_ASSUM(fun th -> vEXISTS_TAC(rand(concl th)) ---->
                   vASM_REWRITE_TAC[] ----> vNO_TAC));;

(* ------------------------------------------------------------------------ *)
(* The integral is unique if it exists                                      *)
(* ------------------------------------------------------------------------ *)

let%a vDINT_UNIQ = prove(
  [%q {|!a b f k1 k2. a <= b /\ defint(a,b) f k1 /\ defint(a,b) f k2 ==> (k1 = k2)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_SUB_0] ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vONCE_REWRITE_TAC[vABS_NZ] ----> vDISCH_TAC ---->
  vREWRITE_TAC[defint] ---->
  vDISCH_THEN(vCONJUNCTS_THEN(vMP_TAC -| vSPEC [%q {|abs(k1 - k2) / &2|} ])) ---->
  vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g1:real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g2:real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|\x. a <= x /\ x <= b|} ];
                [%q {|g1:real->real|} ]; [%q {|g2:real->real|} ]] vGAUGE_MIN) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ];
         [%q {|\x:real. if g1(x) < g2(x) then g1(x) else g2(x)|} ]] vDIVISION_EXISTS) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|D:num->real|} ] (vX_CHOOSE_THEN [%q {|p:num->real|} ]
    vSTRIP_ASSUME_TAC)) ---->
  vFIRST_ASSUM(vSTRIP_ASSUME_TAC -| vMATCH_MP vFINE_MIN) ---->
  vREPEAT(vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|D:num->real|} ]; [%q {|p:num->real|} ]]) ---->
    vASM_REWRITE_TAC[] ----> vDISCH_TAC) ---->
  vSUBGOAL_THEN [%q {|abs((rsum(D,p) f - k2) - (rsum(D,p) f - k1)) < abs(k1 - k2)|} ]
  vMP_TAC ++-->
   [vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|abs(rsum(D,p) f - k2) + abs(rsum(D,p) f - k1)|} ] ---->
    vCONJ_TAC ++-->
     [vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [real_sub] ---->
      vGEN_REWRITE_TAC (funpow 2 vRAND_CONV) [vGSYM vABS_NEG] ---->
      vMATCH_ACCEPT_TAC vABS_TRIANGLE;
      vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_HALF_DOUBLE] ---->
      vMATCH_MP_TAC vREAL_LT_ADD2 ----> vASM_REWRITE_TAC[]];
    vREWRITE_TAC[real_sub; vREAL_NEG_ADD; vREAL_NEG_SUB] ---->
    vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
      [%q {|(a + b) + (c + d) = (d + a) + (c + b)|} ]] ---->
    vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID; vREAL_LT_REFL]]);;

(* ------------------------------------------------------------------------ *)
(* Integral over a null interval is 0                                       *)
(* ------------------------------------------------------------------------ *)

let%a vINTEGRAL_NULL = prove(
  [%q {|!f a. defint(a,a) f (&0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[defint] ----> vGEN_TAC ---->
  vDISCH_TAC ----> vEXISTS_TAC [%q {|\x:real. &1|} ] ---->
  vREWRITE_TAC[gauge; vREAL_LT_01] ----> vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[tdiv] ----> vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vDIVISION_EQ) ---->
  vREWRITE_TAC[rsum] ----> vDISCH_THEN vSUBST1_TAC ---->
  vASM_REWRITE_TAC[sum; vREAL_SUB_REFL; vABS_0]);;

(* ------------------------------------------------------------------------ *)
(* Fundamental theorem of calculus (Part I)                                 *)
(* ------------------------------------------------------------------------ *)

let%a vSTRADDLE_LEMMA = prove(
  [%q {|!f f' a b e. (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\ &0 < e
    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
            !x u v. a <= u /\ u <= x /\ x <= v /\ v <= b /\ (v - u) < g(x)
                ==> abs((f(v) - f(u)) - (f'(x) * (v - u))) <= e * (v - u)|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[gauge] ----> vBETA_TAC ---->
  vSUBGOAL_THEN
   [%q {|!x. a <= x /\ x <= b ==>
        ?d. &0 < d /\
          !u v. u <= x /\ x <= v /\ (v - u) < d ==>
            abs((f(v) - f(u)) - (f'(x) * (v - u))) <= e * (v - u)|} ] vMP_TAC ++-->
   [vALL_TAC;
    vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vK vALL_TAC) ---->
    vDISCH_THEN(vMP_TAC -| vCONV_RULE
      ((vONCE_DEPTH_CONV vRIGHT_IMP_EXISTS_CONV) +---> vOLD_SKOLEM_CONV)) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|g:real->real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|g:real->real|} ] ----> vCONJ_TAC ++-->
     [vGEN_TAC ---->
      vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
      vDISCH_THEN(fun th -> vREWRITE_TAC[th]);
      vREPEAT vSTRIP_TAC ---->
      vC vSUBGOAL_THEN (fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th))
      [%q {|a <= x /\ x <= b|} ] ++-->
       [vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ++-->
         [vEXISTS_TAC [%q {|u:real|} ]; vEXISTS_TAC [%q {|v:real|} ]] ---->
        vASM_REWRITE_TAC[];
        vDISCH_THEN(vMATCH_MP_TAC -| vCONJUNCT2) ----> vASM_REWRITE_TAC[]]]] ---->
  vX_GEN_TAC [%q {|x:real|} ] ---->
  vDISCH_THEN(fun th -> vSTRIP_ASSUME_TAC th ---->
    vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vMP_TAC -| vC vMATCH_MP th)) ---->
  vREWRITE_TAC[diffl; vLIM] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
  vBETA_TAC ----> vREWRITE_TAC[vREAL_SUB_RZERO] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|!z. abs(z - x) < d ==>
        abs((f(z) - f(x)) - (f'(x) * (z - x))) <= (e / &2) * abs(z - x)|} ]
  vASSUME_TAC ++-->
   [vGEN_TAC ----> vASM_CASES_TAC [%q {|&0 < abs(z - x)|} ] ++-->
     [vALL_TAC;
      vUNDISCH_TAC [%q {|~(&0 < abs(z - x))|} ] ---->
      vREWRITE_TAC[vGSYM vABS_NZ; vREAL_SUB_0] ---->
      vDISCH_THEN vSUBST1_TAC ---->
      vREWRITE_TAC[vREAL_SUB_REFL; vREAL_MUL_RZERO; vABS_0; vREAL_LE_REFL]] ---->
    vDISCH_THEN(vMP_TAC -| vCONJ (vASSUME [%q {|&0 < abs(z - x)|} ])) ---->
    vDISCH_THEN((---->) (vMATCH_MP_TAC vREAL_LT_IMP_LE) -| vMP_TAC) ---->
    vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
    vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vLAND_CONV
      [vGSYM(vMATCH_MP vREAL_LT_RMUL_EQ th)]) ---->
    vMATCH_MP_TAC vEQ_IMP ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vGSYM vABS_MUL] ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vREAL_SUB_RDISTRIB] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vREAL_SUB_ADD2] ----> vMATCH_MP_TAC vREAL_DIV_RMUL ---->
    vASM_REWRITE_TAC[vABS_NZ]; vALL_TAC] ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|u <= v|} ] (vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
   [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
    vASM_REWRITE_TAC[];
    vALL_TAC;
    vASM_REWRITE_TAC[vREAL_SUB_REFL; vREAL_MUL_RZERO; vABS_0; vREAL_LE_REFL]] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|abs((f(v) - f(x)) - (f'(x) * (v - x))) +
              abs((f(x) - f(u)) - (f'(x) * (x - u)))|} ] ---->
  vCONJ_TAC ++-->
   [vMP_TAC(vSPECL[[%q {|(f(v) - f(x)) - (f'(x) * (v - x))|} ];
                 [%q {|(f(x) - f(u)) - (f'(x) * (x - u))|} ]] vABS_TRIANGLE) ---->
    vMATCH_MP_TAC vEQ_IMP ---->
    vAP_THM_TAC ----> vREPEAT vAP_TERM_TAC ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_ADD2_SUB2] ---->
    vREWRITE_TAC[vREAL_SUB_LDISTRIB] ---->
    vSUBGOAL_THEN [%q {|!a b c. (a - b) + (b - c) = (a - c)|} ]
      (fun th -> vREWRITE_TAC[th]) ---->
    vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub] ---->
    vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
      [%q {|(a + b) + (c + d) = (b + c) + (a + d)|} ]] ---->
    vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID]; vALL_TAC] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_HALF_DOUBLE] ---->
  vMATCH_MP_TAC vREAL_LE_ADD2 ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LE_TRANS ---->
    vEXISTS_TAC [%q {|(e / &2) * abs(v - x)|} ] ----> vCONJ_TAC ++-->
     [vFIRST_ASSUM vMATCH_MP_TAC ---->
      vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|v - u|} ] ---->
      vASM_REWRITE_TAC[] ----> vREWRITE_TAC[real_sub; vREAL_LE_LADD] ---->
      vASM_REWRITE_TAC[vREAL_LE_NEG2];
      vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ----> vREWRITE_TAC[real_div] ---->
      vGEN_REWRITE_TAC vLAND_CONV
       [vAC vREAL_MUL_AC [%q {|(a * b) * c = (a * c) * b|} ]] ---->
      vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC;
        vMATCH_MP vREAL_LE_LMUL_LOCAL (vASSUME [%q {|&0 < e|} ])] ---->
      vSUBGOAL_THEN [%q {|!x y. (x * inv(&2)) <= (y * inv(&2)) <=> x <= y|} ]
      (fun th -> vASM_REWRITE_TAC[th; real_sub; vREAL_LE_LADD; vREAL_LE_NEG2]) ---->
      vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vREAL_LE_RMUL_EQ ---->
      vMATCH_MP_TAC vREAL_INV_POS ---->
      vREWRITE_TAC[vREAL_LT; num_CONV [%q {|2|} ]; vLT_0]];
    vMATCH_MP_TAC vREAL_LE_TRANS ---->
    vEXISTS_TAC [%q {|(e / &2) * abs(x - u)|} ] ----> vCONJ_TAC ++-->
     [vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [real_sub] ---->
      vONCE_REWRITE_TAC[vGSYM vABS_NEG] ---->
      vREWRITE_TAC[vREAL_NEG_ADD; vREAL_NEG_SUB] ---->
      vONCE_REWRITE_TAC[vREAL_NEG_RMUL] ---->
      vREWRITE_TAC[vREAL_NEG_SUB] ----> vREWRITE_TAC[vGSYM real_sub] ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vONCE_REWRITE_TAC[vABS_SUB] ---->
      vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|v - u|} ] ---->
      vASM_REWRITE_TAC[] ----> vASM_REWRITE_TAC[real_sub; vREAL_LE_RADD];
      vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ----> vREWRITE_TAC[real_div] ---->
      vGEN_REWRITE_TAC vLAND_CONV
       [vAC vREAL_MUL_AC [%q {|(a * b) * c = (a * c) * b|} ]] ---->
      vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC;
        vMATCH_MP vREAL_LE_LMUL_LOCAL (vASSUME [%q {|&0 < e|} ])] ---->
      vSUBGOAL_THEN [%q {|!x y. (x * inv(&2)) <= (y * inv(&2)) <=> x <= y|} ]
      (fun th -> vASM_REWRITE_TAC[th; real_sub; vREAL_LE_RADD; vREAL_LE_NEG2]) ---->
      vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vREAL_LE_RMUL_EQ ---->
      vMATCH_MP_TAC vREAL_INV_POS ---->
      vREWRITE_TAC[vREAL_LT; num_CONV [%q {|2|} ]; vLT_0]]]);;

let%a vFTC1 = prove(
  [%q {|!f f' a b. a <= b /\ (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x))
        ==> defint(a,b) f' (f(b) - f(a))|} ],
  vREPEAT vSTRIP_TAC ---->
  vUNDISCH_TAC [%q {|a <= b|} ] ----> vREWRITE_TAC[vREAL_LE_LT] ---->
  vDISCH_THEN vDISJ_CASES_TAC ++-->
   [vALL_TAC; vASM_REWRITE_TAC[vREAL_SUB_REFL; vINTEGRAL_NULL]] ---->
  vREWRITE_TAC[defint] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN
    [%q {|!e. &0 < e ==>
      ?g. gauge(\x. a <= x /\ x <= b)g /\
          (!D p.
            tdiv(a,b)(D,p) /\ fine g(D,p) ==>
            (abs((rsum(D,p)f') - ((f b) - (f a)))) <= e)|} ]
  vMP_TAC ++-->
   [vALL_TAC;
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ----> vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|g:real->real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|g:real->real|} ] ----> vASM_REWRITE_TAC[] ---->
    vREPEAT vGEN_TAC ---->
    vDISCH_THEN(fun th -> vFIRST_ASSUM(vASSUME_TAC -| vC vMATCH_MP th)) ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|e / &2|} ] ---->
    vASM_REWRITE_TAC[vREAL_LT_HALF2]] ---->
  vUNDISCH_TAC [%q {|&0 < e|} ] ----> vDISCH_THEN(vK vALL_TAC) ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|f':real->real|} ];
    [%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|e / (b - a)|} ]] vSTRADDLE_LEMMA) ---->
  vASM_REWRITE_TAC[] ---->
  vSUBGOAL_THEN [%q {|&0 < e / (b - a)|} ] (fun th -> vREWRITE_TAC[th]) ++-->
   [vREWRITE_TAC[real_div] ----> vMATCH_MP_TAC vREAL_LT_MUL ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_INV_POS ---->
    vASM_REWRITE_TAC[vREAL_SUB_LT]; vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g:real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|g:real->real|} ] ----> vASM_REWRITE_TAC[] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|D:num->real|} ]; [%q {|p:num->real|} ]] ---->
  vREWRITE_TAC[tdiv] ----> vSTRIP_TAC ----> vREWRITE_TAC[rsum] ---->
  vSUBGOAL_THEN [%q {|f(b) - f(a) = sum(0,dsize D)(\n. f(D(SUC n)) - f(D(n)))|} ]
  vSUBST1_TAC ++-->
   [vMP_TAC(vSPECL [[%q {|\n:num. (f:real->real)(D(n))|} ]; [%q {|0|} ]; [%q {|dsize D|} ]]
      vSUM_CANCEL) ----> vBETA_TAC ----> vDISCH_THEN vSUBST1_TAC ---->
    vASM_REWRITE_TAC[vADD_CLAUSES] ---->
    vMAP_EVERY (vIMP_RES_THEN vSUBST1_TAC) [vDIVISION_LHS; vDIVISION_RHS] ---->
    vREFL_TAC; vALL_TAC] ---->
  vONCE_REWRITE_TAC[vABS_SUB] ----> vREWRITE_TAC[vGSYM vSUM_SUB] ----> vBETA_TAC ---->
  vLE_MATCH_TAC vABS_SUM ----> vBETA_TAC ---->
  vSUBGOAL_THEN [%q {|e = sum(0,dsize D)(\n. (e / (b - a)) * (D(SUC n) - D(n)))|} ]
  vSUBST1_TAC ++-->
   [vONCE_REWRITE_TAC[vSYM(vBETA_CONV [%q {|(\n. (D(SUC n) - D(n))) n|} ])] ---->
    vASM_REWRITE_TAC[vSUM_CMUL; vSUM_CANCEL; vADD_CLAUSES] ---->
    vMAP_EVERY (vIMP_RES_THEN vSUBST1_TAC) [vDIVISION_LHS; vDIVISION_RHS] ---->
    vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_RMUL ---->
    vREWRITE_TAC[vREAL_SUB_0] ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vFIRST_ASSUM vACCEPT_TAC; vALL_TAC] ---->
  vMATCH_MP_TAC vSUM_LE ----> vX_GEN_TAC [%q {|r:num|} ] ---->
  vREWRITE_TAC[vADD_CLAUSES] ----> vSTRIP_TAC ----> vBETA_TAC ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ----> vREPEAT vCONJ_TAC ++-->
   [vIMP_RES_THEN (fun th -> vREWRITE_TAC[th]) vDIVISION_LBOUND;
    vIMP_RES_THEN (fun th -> vREWRITE_TAC[th]) vDIVISION_UBOUND;
    vUNDISCH_TAC [%q {|fine(g)(D,p)|} ] ----> vREWRITE_TAC[fine] ---->
    vDISCH_THEN vMATCH_MP_TAC ----> vFIRST_ASSUM vACCEPT_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Definition of integral and integrability.                                 *)
(* ------------------------------------------------------------------------- *)

let integrable = new_definition
 [%q {|integrable(a,b) f = ?i. defint(a,b) f i|} ];;

let integral = new_definition
 [%q {|integral(a,b) f = @i. defint(a,b) f i|} ];;

let%a vINTEGRABLE_DEFINT = prove
 ([%q {|!f a b. integrable(a,b) f ==> defint(a,b) f (integral(a,b) f)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[integrable; integral] ---->
  vCONV_TAC(vRAND_CONV vSELECT_CONV) ----> vREWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Other more or less trivial lemmas.                                        *)
(* ------------------------------------------------------------------------- *)

let%a vDIVISION_BOUNDS = prove
 ([%q {|!d a b. division(a,b) d ==> !n. a <= d(n) /\ d(n) <= b|} ],
  vMESON_TAC[vDIVISION_UBOUND; vDIVISION_LBOUND]);;

let%a vTDIV_BOUNDS = prove
 ([%q {|!d p a b. tdiv(a,b) (d,p)
             ==> !n. a <= d(n) /\ d(n) <= b /\ a <= p(n) /\ p(n) <= b|} ],
  vREWRITE_TAC[tdiv] ----> vASM_MESON_TAC[vDIVISION_BOUNDS; vREAL_LE_TRANS]);;

let%a vTDIV_LE = prove
 ([%q {|!d p a b. tdiv(a,b) (d,p) ==> a <= b|} ],
  vMESON_TAC[tdiv; vDIVISION_LE]);;

let%a vDEFINT_WRONG = prove
 ([%q {|!a b f i. b < a ==> defint(a,b) f i|} ],
  vREWRITE_TAC[defint; gauge] ----> vREPEAT vSTRIP_TAC ---->
  vEXISTS_TAC [%q {|\x:real. &0|} ] ---->
  vASM_SIMP_TAC[vREAL_ARITH [%q {|b < a ==> (a <= x /\ x <= b <=> F)|} ]] ---->
  vASM_MESON_TAC[vREAL_NOT_LE; vTDIV_LE]);;

let%a vDEFINT_INTEGRAL = prove
 ([%q {|!f a b i. a <= b /\ defint(a,b) f i ==> integral(a,b) f = i|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[integral] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ----> vASM_MESON_TAC[vDINT_UNIQ]);;

(* ------------------------------------------------------------------------- *)
(* Linearity.                                                                *)
(* ------------------------------------------------------------------------- *)

let%a vDEFINT_CONST = prove
 ([%q {|!a b c. defint(a,b) (\x. c) (c * (b - a))|} ],
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vSPECL [[%q {|\x. c * x|} ]; [%q {|\x:real. c:real|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]] vFTC1) ---->
  vDISJ_CASES_TAC(vREAL_ARITH [%q {|b < a \/ a <= b|} ]) ---->
  vASM_SIMP_TAC[vDEFINT_WRONG; vREAL_SUB_LDISTRIB] ---->
  vDISCH_THEN vMATCH_MP_TAC ----> vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] (vDIFF_CONV [%q {|\x. c * x|} ])) ---->
  vREWRITE_TAC[vREAL_MUL_LID; vREAL_MUL_LZERO; vREAL_ADD_LID]);;

let%a vDEFINT_0 = prove
 ([%q {|!a b. defint(a,b) (\x. &0) (&0)|} ],
  vMP_TAC vDEFINT_CONST ----> vREPEAT(vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|&0|} ]) ----> vREWRITE_TAC[vREAL_MUL_LZERO]);;

let%a vDEFINT_NEG = prove
 ([%q {|!f a b i. defint(a,b) f i ==> defint(a,b) (\x. --f x) (--i)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[defint] ---->
  vREWRITE_TAC[rsum; vREAL_MUL_LNEG; vSUM_NEG] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|abs(--x - --y) = abs(x - y)|} ]]);;

let%a vDEFINT_CMUL = prove
 ([%q {|!f a b c i. defint(a,b) f i ==> defint(a,b) (\x. c * f x) (c * i)|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|c = &0|} ] ++-->
   [vMP_TAC(vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|c:real|} ]] vDEFINT_CONST) ---->
    vASM_SIMP_TAC[vREAL_MUL_LZERO];
    vALL_TAC] ---->
  vREWRITE_TAC[defint] ----> vDISCH_TAC ----> vX_GEN_TAC [%q {|e:real|} ] ---->
  vDISCH_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|e / abs c|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vGSYM vREAL_ABS_NZ] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vGEN_TAC ---->
  vREWRITE_TAC[rsum; vSUM_CMUL; vGSYM vREAL_MUL_ASSOC] ---->
  vASM_SIMP_TAC[vGSYM vREAL_SUB_LDISTRIB; vREAL_ABS_MUL] ---->
  vASM_SIMP_TAC[vREAL_LT_RDIV_EQ; vGSYM vREAL_ABS_NZ; vREAL_MUL_SYM]);;

let%a vDEFINT_ADD = prove
 ([%q {|!f g a b i j.
        defint(a,b) f i /\ defint(a,b) g j
        ==> defint(a,b) (\x. f x + g x) (i + j)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[defint] ---->
  vSTRIP_TAC ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vREPEAT(vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|e / &2|} ])) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g1:real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g2:real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|\x:real. if g1(x) < g2(x) then g1(x) else g2(x)|} ] ---->
  vASM_SIMP_TAC[vGAUGE_MIN; rsum] ----> vREPEAT vSTRIP_TAC ---->
  vREWRITE_TAC[vREAL_ADD_RDISTRIB; vSUM_ADD] ----> vREWRITE_TAC[vGSYM rsum] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|abs(x - i) < e / &2 /\ abs(y - j) < e / &2
    ==> abs((x + y) - (i + j)) < e|} ]) ---->
  vASM_MESON_TAC[vFINE_MIN]);;

let%a vDEFINT_SUB = prove
 ([%q {|!f g a b i j.
        defint(a,b) f i /\ defint(a,b) g j
        ==> defint(a,b) (\x. f x - g x) (i - j)|} ],
  vSIMP_TAC[real_sub; vDEFINT_ADD; vDEFINT_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Ordering properties of integral.                                          *)
(* ------------------------------------------------------------------------- *)

let%a vINTEGRAL_LE = prove
 ([%q {|!f g a b i j.
        a <= b /\ integrable(a,b) f /\ integrable(a,b) g /\
        (!x. a <= x /\ x <= b ==> f(x) <= g(x))
        ==> integral(a,b) f <= integral(a,b) g|} ],
  vREPEAT vSTRIP_TAC ---->
  vREPEAT(vFIRST_X_ASSUM(vASSUME_TAC -| vMATCH_MP vINTEGRABLE_DEFINT)) ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|~(&0 < x - y) ==> x <= y|} ]) ---->
  vABBREV_TAC [%q {|e = integral(a,b) f - integral(a,b) g|} ] ----> vDISCH_TAC ---->
  vREPEAT(vFIRST_X_ASSUM(vMP_TAC -|
    vSPEC [%q {|e / &2|} ] -| vGEN_REWRITE_RULE vI [defint])) ---->
  vASM_REWRITE_TAC[vREAL_ARITH [%q {|&0 < e / &2 <=> &0 < e|} ]] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g1:real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g2:real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ];
                [%q {|\x:real. if g1(x) < g2(x) then g1(x) else g2(x)|} ]]
               vDIVISION_EXISTS) ---->
  vASM_SIMP_TAC[vGAUGE_MIN; vNOT_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|D:num->real|} ]; [%q {|p:num->real|} ]] ----> vSTRIP_TAC ---->
  vREPEAT(vFIRST_X_ASSUM(vMP_TAC -| vSPECL [[%q {|D:num->real|} ]; [%q {|p:num->real|} ]])) ---->
  vREPEAT(vFIRST_X_ASSUM(vMP_TAC -| vSPECL [[%q {|D:num->real|} ]; [%q {|p:num->real|} ]])) ---->
  vFIRST_ASSUM(fun th -> vASM_REWRITE_TAC[vMATCH_MP vFINE_MIN th]) ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|ih - ig = e /\ &0 < e /\ sh <= sg
    ==> abs(sg - ig) < e / &2 ==> ~(abs(sh - ih) < e / &2)|} ]) ---->
  vASM_REWRITE_TAC[] ----> vREWRITE_TAC[rsum] ----> vMATCH_MP_TAC vSUM_LE ---->
  vX_GEN_TAC [%q {|r:num|} ] ----> vREWRITE_TAC[vADD_CLAUSES] ----> vSTRIP_TAC ---->
  vMATCH_MP_TAC vREAL_LE_RMUL ----> vREWRITE_TAC[vREAL_SUB_LE] ---->
  vASM_MESON_TAC[vTDIV_BOUNDS; vREAL_LT_IMP_LE; vDIVISION_THM; tdiv]);;

let%a vDEFINT_LE = prove
 ([%q {|!f g a b i j. a <= b /\ defint(a,b) f i /\ defint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> f(x) <= g(x))
                 ==> i <= j|} ],
  vREPEAT vGEN_TAC ----> vMP_TAC(vSPEC_ALL vINTEGRAL_LE) ---->
  vMESON_TAC[integrable; vDEFINT_INTEGRAL]);;

let%a vDEFINT_TRIANGLE = prove
 ([%q {|!f a b i j. a <= b /\ defint(a,b) f i /\ defint(a,b) (\x. abs(f x)) j
               ==> abs(i) <= j|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC(vREAL_ARITH
   [%q {|--a <= b /\ b <= a ==> abs(b) <= a|} ]) ---->
  vCONJ_TAC ----> vMATCH_MP_TAC vDEFINT_LE ++-->
   [vMAP_EVERY vEXISTS_TAC [[%q {|\x:real. --abs(f x)|} ]; [%q {|f:real->real|} ]];
    vMAP_EVERY vEXISTS_TAC [[%q {|f:real->real|} ]; [%q {|\x:real. abs(f x)|} ]]] ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|a:real|} ]; [%q {|b:real|} ]] ---->
  vASM_SIMP_TAC[vDEFINT_NEG] ----> vREAL_ARITH_TAC);;

let%a vDEFINT_EQ = prove
 ([%q {|!f g a b i j. a <= b /\ defint(a,b) f i /\ defint(a,b) g j /\
                 (!x. a <= x /\ x <= b ==> f(x) = g(x))
                 ==> i = j|} ],
  vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ----> vMESON_TAC[vDEFINT_LE]);;

let%a vINTEGRAL_EQ = prove
 ([%q {|!f g a b i. defint(a,b) f i /\
               (!x. a <= x /\ x <= b ==> f(x) = g(x))
               ==> defint(a,b) g i|} ],
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC [%q {|a <= b|} ] ++-->
   [vALL_TAC; vASM_MESON_TAC[vREAL_NOT_LE; vDEFINT_WRONG]] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [defint]) ---->
  vREWRITE_TAC[defint] ----> vMATCH_MP_TAC vMONO_FORALL ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vASM_CASES_TAC [%q {|&0 < e|} ] ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|d:real->real|} ] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vMONO_FORALL ----> vX_GEN_TAC [%q {|D:num->real|} ] ---->
  vMATCH_MP_TAC vMONO_FORALL ----> vX_GEN_TAC [%q {|p:num->real|} ] ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|x = y ==> abs(x - i) < e ==> abs(y - i) < e|} ]) ---->
  vREWRITE_TAC[rsum] ----> vMATCH_MP_TAC vSUM_EQ ---->
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vFIRST_X_ASSUM vMATCH_MP_TAC ---->
  vASM_MESON_TAC[tdiv; vDIVISION_LBOUND; vDIVISION_UBOUND; vDIVISION_THM;
                vREAL_LE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Integration by parts.                                                     *)
(* ------------------------------------------------------------------------- *)

let%a vINTEGRATION_BY_PARTS = prove
 ([%q {|!f g f' g' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        (!x. a <= x /\ x <= b ==> (g diffl g'(x))(x))
        ==> defint(a,b) (\x. f'(x) * g(x) + f(x) * g'(x))
                        (f(b) * g(b) - f(a) * g(a))|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vFTC1 ----> vASM_REWRITE_TAC[] ---->
  vONCE_REWRITE_TAC[vREAL_ARITH [%q {|a + b * c = a + c * b|} ]] ---->
  vASM_SIMP_TAC[vDIFF_MUL]);;

(* ------------------------------------------------------------------------- *)
(* Various simple lemmas about divisions.                                    *)
(* ------------------------------------------------------------------------- *)

let%a vDIVISION_LE_SUC = prove
 ([%q {|!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)|} ],
  vREWRITE_TAC[vDIVISION_THM; vGE] ---->
  vMESON_TAC[vLET_CASES; vLE; vREAL_LE_REFL; vREAL_LT_IMP_LE]);;

let%a vDIVISION_MONO_LE = prove
 ([%q {|!d a b. division(a,b) d ==> !m n. m <= n ==> d(m) <= d(n)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vDIVISION_LE_SUC) ---->
  vSIMP_TAC[vLE_EXISTS; vLEFT_IMP_EXISTS_THM] ---->
  vGEN_TAC ----> vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vREWRITE_TAC[vLEFT_FORALL_IMP_THM; vEXISTS_REFL] ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vADD_CLAUSES; vREAL_LE_REFL] ---->
  vASM_MESON_TAC[vREAL_LE_TRANS]);;

let%a vDIVISION_MONO_LE_SUC = prove
 ([%q {|!d a b. division(a,b) d ==> !n. d(n) <= d(SUC n)|} ],
  vMESON_TAC[vDIVISION_MONO_LE; vLE; vLE_REFL]);;

let%a vDIVISION_INTERMEDIATE = prove
 ([%q {|!d a b c. division(a,b) d /\ a <= c /\ c <= b
             ==> ?n. n <= dsize d /\ d(n) <= c /\ c <= d(SUC n)|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|\n. n <= dsize d /\ (d:num->real)(n) <= c|} ] num_MAX) ---->
  vDISCH_THEN(vMP_TAC -| fst -| vEQ_IMP_RULE) ----> vANTS_TAC ++-->
   [vASM_MESON_TAC[vLE_0; vDIVISION_THM]; vALL_TAC] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|n:num|} ] ----> vSIMP_TAC[] ---->
  vSTRIP_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|SUC n|} ]) ---->
  vREWRITE_TAC[vARITH_RULE [%q {|~(SUC n <= n)|} ]] ---->
  vONCE_REWRITE_TAC[vGSYM vCONTRAPOS_THM] ----> vREWRITE_TAC[vREAL_NOT_LE] ---->
  vDISCH_TAC ----> vASM_SIMP_TAC[vREAL_LT_IMP_LE; vLE_SUC_LT; vLT_LE] ---->
  vDISCH_THEN vSUBST_ALL_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|SUC(dsize d)|} ] -| repeat vCONJUNCT2) ---->
  vREWRITE_TAC[vGE; vLE; vLE_REFL] ---->
  vASM_REAL_ARITH_TAC);;

let%a vDIVISION_DSIZE_LE = prove
 ([%q {|!a b d n. division(a,b) d /\ d(SUC n) = d(n) ==> dsize d <= n|} ],
  vREWRITE_TAC[vDIVISION_THM] ----> vMESON_TAC[vREAL_LT_REFL; vNOT_LT]);;

let%a vDIVISION_DSIZE_GE = prove
 ([%q {|!a b d n. division(a,b) d /\ d(n) < d(SUC n) ==> SUC n <= dsize d|} ],
  vREWRITE_TAC[vDIVISION_THM; vLE_SUC_LT; vGE] ---->
  vMESON_TAC[vREAL_LT_REFL; vLE; vNOT_LT]);;

let%a vDIVISION_DSIZE_EQ = prove
 ([%q {|!a b d n. division(a,b) d /\ d(n) < d(SUC n) /\ d(SUC(SUC n)) = d(SUC n)
           ==> dsize d = SUC n|} ],
  vREWRITE_TAC[vGSYM vLE_ANTISYM] ---->
  vMESON_TAC[vDIVISION_DSIZE_LE; vDIVISION_DSIZE_GE]);;

let%a vDIVISION_DSIZE_EQ_ALT = prove
 ([%q {|!a b d n. division(a,b) d /\ d(SUC n) = d(n) /\
             (!i. i < n ==> d(i) < d(SUC i))
             ==> dsize d = n|} ],
  vREPLICATE_TAC 3 vGEN_TAC ----> vINDUCT_TAC ++-->
   [vMESON_TAC[vARITH_RULE [%q {|d <= 0 ==> d = 0|} ]; vDIVISION_DSIZE_LE]; vALL_TAC] ---->
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vLE_ANTISYM] ---->
  vASM_MESON_TAC[vDIVISION_DSIZE_LE; vDIVISION_DSIZE_GE; vLT]);;

(* ------------------------------------------------------------------------- *)
(* Combination of adjacent intervals (quite painful in the details).         *)
(* ------------------------------------------------------------------------- *)

let%a vDEFINT_COMBINE = prove
 ([%q {|!f a b c i j. a <= b /\ b <= c /\ defint(a,b) f i /\ defint(b,c) f j
                 ==> defint(a,c) f (i + j)|} ],
  vREPEAT vGEN_TAC ---->
  vREPLICATE_TAC 2 (vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vMP_TAC(vASSUME [%q {|a <= b|} ]) ----> vREWRITE_TAC[vREAL_LE_LT] ---->
  vASM_CASES_TAC [%q {|a:real = b|} ] ----> vASM_REWRITE_TAC[] ++-->
   [vASM_MESON_TAC[vINTEGRAL_NULL; vDINT_UNIQ; vREAL_LE_TRANS; vREAL_ADD_LID];
    vDISCH_TAC] ---->
  vMP_TAC(vASSUME [%q {|b <= c|} ]) ----> vREWRITE_TAC[vREAL_LE_LT] ---->
  vASM_CASES_TAC [%q {|b:real = c|} ] ----> vASM_REWRITE_TAC[] ++-->
   [vASM_MESON_TAC[vINTEGRAL_NULL; vDINT_UNIQ; vREAL_LE_TRANS; vREAL_ADD_RID];
    vDISCH_TAC] ---->
  vREWRITE_TAC[defint; vAND_FORALL_THM] ---->
  vDISCH_THEN(fun th -> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ----> vMP_TAC th) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2
   (vX_CHOOSE_THEN [%q {|g1:real->real|} ] vSTRIP_ASSUME_TAC)
   (vX_CHOOSE_THEN [%q {|g2:real->real|} ] vSTRIP_ASSUME_TAC)) ---->
  vEXISTS_TAC
   [%q {|\x. if x < b then min (g1 x) (b - x)
        else if b < x then min (g2 x) (x - b)
        else min (g1 x) (g2 x)|} ] ---->
  vCONJ_TAC ++-->
   [vREPEAT(vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [gauge])) ---->
    vREWRITE_TAC[gauge] ----> vREPEAT vSTRIP_TAC ---->
    vREPEAT vCOND_CASES_TAC ----> vASM_SIMP_TAC[vREAL_LT_MIN; vREAL_SUB_LT] ---->
    vTRY vCONJ_TAC ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
    vASM_REAL_ARITH_TAC;
    vALL_TAC] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]] ---->
  vREWRITE_TAC[tdiv; rsum] ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|d:num->real|} ]; [%q {|a:real|} ]; [%q {|c:real|} ]; [%q {|b:real|} ]]
               vDIVISION_INTERMEDIATE) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:num|} ]
   (vCONJUNCTS_THEN2 vMP_TAC vSTRIP_ASSUME_TAC)) ----> vREWRITE_TAC[vLE_EXISTS] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|n:num|} ]) ----> vASM_REWRITE_TAC[] ---->
  vASM_CASES_TAC [%q {|n = 0|} ] ++-->
   [vFIRST_X_ASSUM vSUBST_ALL_TAC ---->
    vRULE_ASSUM_TAC(vREWRITE_RULE[vADD_CLAUSES]) ---->
    vFIRST_X_ASSUM(vSUBST_ALL_TAC -| vSYM) ---->
    vASM_MESON_TAC[vDIVISION_THM; vGE; vLE_REFL; vREAL_NOT_LT];
    vALL_TAC] ---->
  vREWRITE_TAC[vGSYM vSUM_SPLIT; vADD_CLAUSES] ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP (vARITH_RULE
   [%q {|~(n = 0) ==> n = 1 + PRE n|} ])) ---->
  vREWRITE_TAC[vGSYM vSUM_SPLIT; vSUM_1] ---->
  vSUBGOAL_THEN [%q {|(p:num->real) m = b|} ] vASSUME_TAC ++-->
   [vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|m:num|} ] -| vGEN_REWRITE_RULE vI [fine]) ---->
    vASM_REWRITE_TAC[vARITH_RULE [%q {|m < m + n <=> ~(n = 0)|} ]] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|m:num|} ]) ---->
    vMAP_EVERY vUNDISCH_TAC [[%q {|(d:num->real) m <= b|} ]; [%q {|b:real <= d(SUC m)|} ]] ---->
    vREAL_ARITH_TAC;
    vALL_TAC] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|!b. abs((s1 + x * (b - a)) - i) < e / &2 /\
        abs((s2 + x * (c - b)) - j) < e / &2
        ==> abs((s1 + x * (c - a) + s2) - (i + j)) < e|} ]) ---->
  vEXISTS_TAC [%q {|b:real|} ] ----> vCONJ_TAC ++-->
   [vUNDISCH_TAC
     [%q {|!D p. tdiv(a,b) (D,p) /\ fine g1 (D,p)
            ==> abs(rsum(D,p) f - i) < e / &2|} ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|\i. if i <= m then (d:num->real)(i) else b|} ]) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|\i. if i <= m then (p:num->real)(i) else b|} ]) ---->
    vMATCH_MP_TAC(vTAUT [%q {|a /\ (a ==> b) /\ (a /\ c ==> d)
                       ==> (a /\ b ==> c) ==> d|} ]) ---->
    vCONJ_TAC ++-->
     [vREWRITE_TAC[tdiv; division] ----> vREPEAT vCONJ_TAC ++-->
       [vASM_MESON_TAC[division; vLE_0];
        vALL_TAC;
        vX_GEN_TAC [%q {|k:num|} ] ---->
        vREWRITE_TAC[vARITH_RULE [%q {|SUC n <= m <=> n <= m /\ ~(m = n)|} ]] ---->
        vASM_CASES_TAC [%q {|k:num = m|} ] ---->
        vASM_REWRITE_TAC[vLE_REFL; vREAL_LE_REFL] ---->
        vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_LE_REFL]] ---->
      vASM_CASES_TAC [%q {|(d:num->real) m = b|} ] ++-->
       [vEXISTS_TAC [%q {|m:num|} ] ---->
        vSIMP_TAC[vARITH_RULE [%q {|n < m ==> n <= m /\ SUC n <= m|} ]] ---->
        vSIMP_TAC[vARITH_RULE [%q {|n >= m ==> (n <= m <=> m = n:num)|} ]] ---->
        vCONJ_TAC ++--> [vALL_TAC; vASM_MESON_TAC[]] ---->
        vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
        vASM_REWRITE_TAC[] ---->
        vMESON_TAC[vARITH_RULE [%q {|i:num < m ==> i < m + n|} ]];
        vALL_TAC] ---->
      vEXISTS_TAC [%q {|SUC m|} ] ---->
      vSIMP_TAC[vARITH_RULE [%q {|n >= SUC m ==> ~(n <= m)|} ]] ---->
      vSIMP_TAC[vARITH_RULE [%q {|n < SUC m ==> n <= m|} ]] ---->
      vSIMP_TAC[vARITH_RULE [%q {|n < SUC m ==> (SUC n <= m <=> ~(m = n))|} ]] ---->
      vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
      vASM_REWRITE_TAC[] ---->
      vASM_MESON_TAC[vARITH_RULE [%q {|k < SUC m /\ ~(n = 0) ==> k < m + n|} ];
                    vREAL_LT_LE];
      vALL_TAC] ---->
    vCONJ_TAC ++-->
     [vREWRITE_TAC[tdiv; fine] ----> vSTRIP_TAC ----> vX_GEN_TAC [%q {|k:num|} ] ---->
      vREWRITE_TAC[vARITH_RULE [%q {|SUC n <= m <=> n <= m /\ ~(m = n)|} ]] ---->
      vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|k:num|} ] -| vGEN_REWRITE_RULE vI [fine]) ---->
      vMATCH_MP_TAC vMONO_IMP ----> vASM_CASES_TAC [%q {|k:num = m|} ] ++-->
       [vASM_REWRITE_TAC[vLE_REFL; vREAL_LT_REFL] ---->
        vASM_REWRITE_TAC[vARITH_RULE [%q {|m < m + n <=> ~(n = 0)|} ]] ---->
        vMAP_EVERY vUNDISCH_TAC [[%q {|d(m:num) <= b|} ]; [%q {|b <= d(SUC m)|} ]] ---->
        vREAL_ARITH_TAC;
        vALL_TAC] ---->
      vASM_CASES_TAC [%q {|k:num <= m|} ] ----> vASM_REWRITE_TAC[] ++-->
       [vASM_SIMP_TAC[vARITH_RULE [%q {|k <= m /\ ~(n = 0) ==> k < m + n|} ]] ---->
        vSUBGOAL_THEN [%q {|(p:num->real) k <= b|} ] vMP_TAC ++-->
         [vALL_TAC; vREAL_ARITH_TAC] ---->
        vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|(d:num->real) m|} ] ---->
        vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
        vEXISTS_TAC [%q {|(d:num->real) (SUC k)|} ] ----> vASM_REWRITE_TAC[] ---->
        vASM_MESON_TAC[vDIVISION_MONO_LE; vARITH_RULE
         [%q {|k <= m /\ ~(k = m) ==> SUC k <= m|} ]];
        vALL_TAC] ---->
      vCONJ_TAC ++-->
       [vMATCH_MP_TAC(vARITH_RULE
         [%q {|d:num <= SUC m /\ ~(n = 0) ==> k < d ==> k < m + n|} ]) ---->
        vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vDIVISION_DSIZE_LE ---->
        vMAP_EVERY vEXISTS_TAC [[%q {|a:real|} ]; [%q {|b:real|} ]] ----> vASM_REWRITE_TAC[] ---->
        vARITH_TAC;
        vALL_TAC] ---->
      vUNDISCH_TAC [%q {|gauge (\x. a <= x /\ x <= b) g1|} ] ---->
      vASM_REWRITE_TAC[vREAL_SUB_REFL; gauge; vREAL_LE_REFL] ---->
      vDISCH_THEN(fun th -> vDISCH_THEN(vK vALL_TAC) ----> vMP_TAC th) ---->
      vASM_MESON_TAC[vREAL_LE_REFL];
      vALL_TAC] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vMATCH_MP_TAC(vREAL_ARITH
     [%q {|x = y ==> abs(x - i) < e ==> abs(y - i) < e|} ]) ---->
    vREWRITE_TAC[rsum] ----> vASM_CASES_TAC [%q {|(d:num->real) m = b|} ] ++-->
     [vSUBGOAL_THEN [%q {|dsize (\i. if i <= m then d i else b) = m|} ] vASSUME_TAC ++-->
       [vALL_TAC;
        vASM_REWRITE_TAC[vREAL_SUB_REFL; vREAL_MUL_RZERO; vREAL_ADD_RID] ---->
        vMATCH_MP_TAC vSUM_EQ ---->
        vSIMP_TAC[vADD_CLAUSES; vLT_IMP_LE; vLE_SUC_LT]] ---->
      vMATCH_MP_TAC vDIVISION_DSIZE_EQ_ALT ---->
      vMAP_EVERY vEXISTS_TAC [[%q {|a:real|} ]; [%q {|b:real|} ]] ---->
      vCONJ_TAC ++--> [vASM_MESON_TAC[tdiv]; vALL_TAC] ---->
      vASM_REWRITE_TAC[vLE_REFL; vARITH_RULE [%q {|~(SUC m <= m)|} ]] ---->
      vSIMP_TAC[vLT_IMP_LE; vLE_SUC_LT] ---->
      vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
      vASM_REWRITE_TAC[] ----> vMESON_TAC[vARITH_RULE [%q {|i < m:num ==> i < m + n|} ]];
      vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|dsize (\i. if i <= m then d i else b) = SUC m|} ]
    vASSUME_TAC ++-->
     [vALL_TAC;
      vASM_REWRITE_TAC[sum; vADD_CLAUSES; vLE_REFL;
                      vARITH_RULE [%q {|~(SUC m <= m)|} ]] ---->
      vAP_THM_TAC ----> vAP_TERM_TAC ----> vMATCH_MP_TAC vSUM_EQ ---->
      vSIMP_TAC[vADD_CLAUSES; vLT_IMP_LE; vLE_SUC_LT]] ---->
    vMATCH_MP_TAC vDIVISION_DSIZE_EQ ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|a:real|} ]; [%q {|b:real|} ]] ---->
    vCONJ_TAC ++--> [vASM_MESON_TAC[tdiv]; vALL_TAC] ---->
    vASM_REWRITE_TAC[vLE_REFL; vARITH_RULE [%q {|~(SUC m <= m)|} ]] ---->
    vREWRITE_TAC[vARITH_RULE [%q {|~(SUC(SUC m) <= m)|} ]] ---->
    vASM_REWRITE_TAC[vREAL_LT_LE];
    vALL_TAC] ---->
  vASM_CASES_TAC [%q {|d(SUC m):real = b|} ] ----> vASM_REWRITE_TAC[] ++-->
   [vASM_REWRITE_TAC[vREAL_SUB_REFL; vREAL_MUL_RZERO; vREAL_ADD_RID] ---->
    vUNDISCH_TAC
     [%q {|!D p. tdiv(b,c) (D,p) /\ fine g2 (D,p)
            ==> abs(rsum(D,p) f - j) < e / &2|} ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|\i. (d:num->real) (i + SUC m)|} ]) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|\i. (p:num->real) (i + SUC m)|} ]) ---->
    vMATCH_MP_TAC(vTAUT [%q {|a /\ (a ==> b /\ (b /\ c ==> d))
                       ==> (a /\ b ==> c) ==> d|} ]) ---->
    vCONJ_TAC ++-->
     [vASM_REWRITE_TAC[tdiv; division; vADD_CLAUSES] ----> vEXISTS_TAC [%q {|PRE n|} ] ---->
      vFIRST_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
      vASM_MESON_TAC[vARITH_RULE
                     [%q {|~(n = 0) /\ k < PRE n ==> SUC(k + m) < m + n|} ];
                    vARITH_RULE
                     [%q {|~(n = 0) /\ k >= PRE n ==> SUC(k + m) >= m + n|} ]];
      vDISCH_TAC] ---->
    vSUBGOAL_THEN [%q {|dsize(\i. d (i + SUC m)) = PRE n|} ] vASSUME_TAC ++-->
     [vMATCH_MP_TAC vDIVISION_DSIZE_EQ_ALT ---->
      vMAP_EVERY vEXISTS_TAC [[%q {|b:real|} ]; [%q {|c:real|} ]] ---->
      vCONJ_TAC ++--> [vASM_MESON_TAC[tdiv]; vALL_TAC] ---->
      vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
      vDISCH_THEN(vMP_TAC -| vCONJUNCT2) ----> vASM_REWRITE_TAC[vADD_CLAUSES] ---->
      vGEN_REWRITE_TAC vRAND_CONV [vCONJ_SYM] ---->
      vMATCH_MP_TAC vMONO_AND ----> vCONJ_TAC ++-->
       [vALL_TAC;
        vASM_MESON_TAC[vARITH_RULE [%q {|SUC(PRE n + m) >= m + n /\
                                  SUC(SUC(PRE n + m)) >= m + n|} ]]] ---->
      vDISCH_THEN(fun th -> vX_GEN_TAC [%q {|k:num|} ] ----> vDISCH_TAC ---->
                           vMATCH_MP_TAC th) ---->
      vUNDISCH_TAC [%q {|k < PRE n|} ] ----> vARITH_TAC;
      vALL_TAC] ---->
    vCONJ_TAC ++-->
     [vASM_REWRITE_TAC[fine] ----> vX_GEN_TAC [%q {|k:num|} ] ----> vDISCH_TAC ---->
      vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [fine]) ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|k + SUC m|} ]) ---->
      vASM_REWRITE_TAC[vADD_CLAUSES] ----> vANTS_TAC ++-->
       [vUNDISCH_TAC [%q {|k < PRE n|} ] ----> vARITH_TAC; vALL_TAC] ---->
      vMATCH_MP_TAC(vREAL_ARITH [%q {|b <= a ==> x < b ==> x < a|} ]) ---->
      vSUBGOAL_THEN [%q {|~(p(SUC (k + m)) < b)|} ]
        (fun th -> vREWRITE_TAC[th] ----> vREAL_ARITH_TAC) ---->
      vREWRITE_TAC[vREAL_NOT_LT] ---->
      vFIRST_ASSUM(vMP_TAC -| vCONJUNCT1 -| vSPEC [%q {|SUC(k + m)|} ]) ---->
      vUNDISCH_TAC [%q {|b <= d (SUC m)|} ] ---->
      vFIRST_X_ASSUM(vMP_TAC -| vMATCH_MP vDIVISION_MONO_LE) ---->
      vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|SUC m|} ]; [%q {|k + SUC m|} ]]) ---->
      vANTS_TAC ++--> [vARITH_TAC; vALL_TAC] ---->
      vREWRITE_TAC[vADD_CLAUSES] ----> vREAL_ARITH_TAC;
      vALL_TAC] ---->
     vASM_REWRITE_TAC[rsum] ---->
     vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
     vSUBST1_TAC(vARITH_RULE [%q {|m + 1 = 0 + SUC m|} ]) ---->
     vREWRITE_TAC[vSUM_REINDEX] ---->
     vMATCH_MP_TAC(vREAL_ARITH
      [%q {|x = y ==> abs(x - i) < e ==> abs(y - i) < e|} ]) ---->
     vMATCH_MP_TAC vSUM_EQ ----> vREWRITE_TAC[vADD_CLAUSES];
     vALL_TAC] ---->
  vUNDISCH_TAC
   [%q {|!D p. tdiv(b,c) (D,p) /\ fine g2 (D,p)
          ==> abs(rsum(D,p) f - j) < e / &2|} ] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|\i. if i = 0 then b:real else d(i + m)|} ]) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|\i. if i = 0 then b:real else p(i + m)|} ]) ---->
  vMATCH_MP_TAC(vTAUT [%q {|a /\ (a ==> b /\ (b /\ c ==> d))
                     ==> (a /\ b ==> c) ==> d|} ]) ---->
  vCONJ_TAC ++-->
   [vASM_REWRITE_TAC[tdiv; division; vADD_CLAUSES] ----> vCONJ_TAC ++-->
     [vALL_TAC;
      vGEN_TAC ----> vREWRITE_TAC[vNOT_SUC] ---->
      vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_LE_REFL] ---->
      vFIRST_X_ASSUM(vMP_TAC -| vCONJUNCT2 -| vSPEC [%q {|m:num|} ]) ---->
      vASM_REWRITE_TAC[vADD_CLAUSES]] ---->
    vEXISTS_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vNOT_SUC] ---->
    vFIRST_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
    vDISCH_THEN(vMP_TAC -| vCONJUNCT2) ----> vMATCH_MP_TAC vMONO_AND ---->
    vASM_REWRITE_TAC[] ----> vCONJ_TAC ----> vDISCH_THEN(fun th ->
      vX_GEN_TAC [%q {|k:num|} ] ----> vMP_TAC(vSPEC [%q {|k + m:num|} ] th))
    ++--> [vALL_TAC; vUNDISCH_TAC [%q {|~(n = 0)|} ] ----> vARITH_TAC] ---->
    vASM_CASES_TAC [%q {|k:num < n|} ] ---->
    vASM_REWRITE_TAC[vARITH_RULE [%q {|k + m:num < m + n <=> k < n|} ]] ---->
    vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES] ---->
    vASM_REWRITE_TAC[vREAL_LT_LE];
    vDISCH_TAC] ---->
  vSUBGOAL_THEN [%q {|dsize(\i. if i = 0 then b else d (i + m)) = n|} ] vASSUME_TAC
  ++-->
   [vMATCH_MP_TAC vDIVISION_DSIZE_EQ_ALT ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|b:real|} ]; [%q {|c:real|} ]] ---->
    vCONJ_TAC ++--> [vASM_MESON_TAC[tdiv]; vALL_TAC] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
    vDISCH_THEN(vMP_TAC -| vCONJUNCT2) ----> vASM_REWRITE_TAC[vADD_CLAUSES] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vCONJ_SYM] ----> vREWRITE_TAC[vNOT_SUC] ---->
    vMATCH_MP_TAC vMONO_AND ----> vCONJ_TAC ++-->
     [vALL_TAC; vMESON_TAC[vGE; vADD_SYM; vLE_REFL; vLE]] ---->
    vDISCH_THEN(fun th ->
      vX_GEN_TAC [%q {|k:num|} ] ----> vMP_TAC(vSPEC [%q {|k + m:num|} ] th)) ---->
    vASM_CASES_TAC [%q {|k:num < n|} ] ---->
    vASM_REWRITE_TAC[vARITH_RULE [%q {|k + m:num < m + n <=> k < n|} ]] ---->
    vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES] ---->
    vASM_REWRITE_TAC[vREAL_LT_LE];
    vALL_TAC] ---->
  vCONJ_TAC ++-->
   [vASM_REWRITE_TAC[fine] ----> vX_GEN_TAC [%q {|k:num|} ] ----> vDISCH_TAC ---->
    vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [fine]) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|k + m:num|} ]) ---->
    vASM_REWRITE_TAC[vADD_CLAUSES; vNOT_SUC;
                    vARITH_RULE [%q {|k + m < m + n <=> k:num < n|} ]] ---->
    vASM_CASES_TAC [%q {|k = 0|} ] ----> vASM_REWRITE_TAC[] ++-->
     [vASM_REWRITE_TAC[vADD_CLAUSES; vREAL_LT_REFL] ---->
      vMAP_EVERY vUNDISCH_TAC [[%q {|(d:num->real) m <= b|} ]; [%q {|b <= d (SUC m)|} ]] ---->
      vREAL_ARITH_TAC;
      vALL_TAC] ---->
    vMATCH_MP_TAC(vREAL_ARITH [%q {|b <= a ==> x < b ==> x < a|} ]) ---->
    vSUBGOAL_THEN [%q {|~((p:num->real) (k + m) < b)|} ]
     (fun th -> vREWRITE_TAC[th] ----> vREAL_ARITH_TAC) ---->
    vREWRITE_TAC[vREAL_NOT_LT] ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|d(SUC m):real|} ] ---->
    vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|(d:num->real)(k + m)|} ] ---->
    vASM_REWRITE_TAC[] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vMATCH_MP vDIVISION_MONO_LE) ---->
    vDISCH_THEN vMATCH_MP_TAC ----> vUNDISCH_TAC [%q {|~(k = 0)|} ] ----> vARITH_TAC;
    vALL_TAC] ---->
  vASM_REWRITE_TAC[rsum] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|x = y ==> abs(x - i) < e ==> abs(y - i) < e|} ]) ---->
  vSUBGOAL_THEN [%q {|n = 1 + PRE n|} ]
   (fun th -> vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV -| vRAND_CONV) [th])
  ++--> [vUNDISCH_TAC [%q {|~(n = 0)|} ] ----> vARITH_TAC; vALL_TAC] ---->
  vREWRITE_TAC[vGSYM vSUM_SPLIT; vSUM_1; vNOT_SUC; vADD_CLAUSES] ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|a = b ==> x + a = b + x|} ]) ---->
  vSUBST1_TAC(vARITH_RULE [%q {|1 = 0 + 1|} ]) ---->
  vSUBST1_TAC(vARITH_RULE [%q {|m + 0 + 1 = 0 + m + 1|} ]) ---->
  vONCE_REWRITE_TAC[vSUM_REINDEX] ----> vMATCH_MP_TAC vSUM_EQ ---->
  vREWRITE_TAC[vADD_CLAUSES; vADD_EQ_0; vARITH] ----> vREWRITE_TAC[vADD_AC]);;

(* ------------------------------------------------------------------------- *)
(* Pointwise perturbation and spike functions.                               *)
(* ------------------------------------------------------------------------- *)

let%a vDEFINT_DELTA_LEFT = prove
 ([%q {|!a b. defint(a,b) (\x. if x = a then &1 else &0) (&0)|} ],
  vREPEAT vGEN_TAC ----> vDISJ_CASES_TAC(vREAL_ARITH [%q {|b < a \/ a <= b|} ]) ---->
  vASM_SIMP_TAC[vDEFINT_WRONG] ----> vREWRITE_TAC[defint] ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ----> vEXISTS_TAC [%q {|(\x. e):real->real|} ] ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH;
               gauge; fine; rsum; tdiv; vREAL_SUB_RZERO] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]] ----> vSTRIP_TAC ---->
  vASM_CASES_TAC [%q {|dsize d = 0|} ] ----> vASM_REWRITE_TAC[sum; vREAL_ABS_NUM] ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP
   (vARITH_RULE [%q {|~(n = 0) ==> n = 1 + PRE n|} ])) ---->
  vREWRITE_TAC[vGSYM vSUM_SPLIT; vSUM_1; vADD_CLAUSES] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|(&0 <= x /\ x < e) /\ y = &0 ==> abs(x + y) < e|} ]) ---->
  vCONJ_TAC ++-->
   [vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_MUL_LZERO; vREAL_LE_REFL] ---->
    vREWRITE_TAC[vREAL_MUL_LID; vREAL_SUB_LE] ---->
    vASM_MESON_TAC[vDIVISION_THM; vLE_0; vLT_NZ];
    vALL_TAC] ---->
  vMATCH_MP_TAC vSUM_EQ_0 ----> vX_GEN_TAC [%q {|r:num|} ] ---->
  vSTRIP_TAC ----> vREWRITE_TAC[] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_MUL_LZERO] ---->
  vFIRST_ASSUM(vMP_TAC -| vSPECL [[%q {|1|} ]; [%q {|r:num|} ]] -| vMATCH_MP vDIVISION_MONO_LE) ---->
  vASM_REWRITE_TAC[] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vMP_TAC -| vCONJUNCT1)) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|0|} ]) ----> vASM_REWRITE_TAC[vARITH; vLT_NZ] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vCONJUNCT1 -| vSPEC [%q {|r:num|} ]) ---->
  vASM_REWRITE_TAC[] ----> vREAL_ARITH_TAC);;

let%a vDEFINT_DELTA_RIGHT = prove
 ([%q {|!a b. defint(a,b) (\x. if x = b then &1 else &0) (&0)|} ],
  vREPEAT vGEN_TAC ----> vDISJ_CASES_TAC(vREAL_ARITH [%q {|b < a \/ a <= b|} ]) ---->
  vASM_SIMP_TAC[vDEFINT_WRONG] ----> vREWRITE_TAC[defint] ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ----> vEXISTS_TAC [%q {|(\x. e):real->real|} ] ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH;
               gauge; fine; rsum; tdiv; vREAL_SUB_RZERO] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]] ----> vSTRIP_TAC ---->
  vASM_CASES_TAC [%q {|dsize d = 0|} ] ----> vASM_REWRITE_TAC[sum; vREAL_ABS_NUM] ---->
  vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP
   (vARITH_RULE [%q {|~(n = 0) ==> n = PRE n + 1|} ])) ---->
  vABBREV_TAC [%q {|m = PRE(dsize d)|} ] ---->
  vASM_REWRITE_TAC[vGSYM vSUM_SPLIT; vSUM_1; vADD_CLAUSES] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|(&0 <= x /\ x < e) /\ y = &0 ==> abs(y + x) < e|} ]) ---->
  vCONJ_TAC ++-->
   [vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_MUL_LZERO; vREAL_LE_REFL] ---->
    vREWRITE_TAC[vREAL_MUL_LID; vREAL_SUB_LE] ---->
    vASM_MESON_TAC[vDIVISION_THM; vARITH_RULE [%q {|m < m + 1|} ]; vREAL_LT_IMP_LE];
    vALL_TAC] ---->
  vMATCH_MP_TAC vSUM_EQ_0 ----> vX_GEN_TAC [%q {|r:num|} ] ---->
  vREWRITE_TAC[vADD_CLAUSES] ----> vSTRIP_TAC ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_MUL_LZERO] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vCONJUNCT2 -| vSPEC [%q {|r:num|} ]) ---->
  vFIRST_ASSUM(vMP_TAC -| vSPECL [[%q {|SUC r|} ]; [%q {|m:num|} ]] -|
    vMATCH_MP vDIVISION_MONO_LE) ---->
  vASM_REWRITE_TAC[vLE_SUC_LT] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vCONJUNCT2 -| vGEN_REWRITE_RULE vI [vDIVISION_THM]) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2
   (vMP_TAC -| vSPEC [%q {|m:num|} ]) (vMP_TAC -| vSPEC [%q {|m + 1|} ])) ---->
  vASM_REWRITE_TAC[vGE; vLE_REFL; vARITH_RULE [%q {|x < x + 1|} ]] ---->
  vREWRITE_TAC[vADD1] ----> vREAL_ARITH_TAC);;

let%a vDEFINT_DELTA = prove
 ([%q {|!a b c. defint(a,b) (\x. if x = c then &1 else &0) (&0)|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|a <= b|} ] ++-->
   [vALL_TAC; vASM_MESON_TAC[vREAL_NOT_LE; vDEFINT_WRONG]] ---->
  vASM_CASES_TAC [%q {|a <= c /\ c <= b|} ] ++-->
   [vALL_TAC;
    vMATCH_MP_TAC vINTEGRAL_EQ ----> vEXISTS_TAC [%q {|\x:real. &0|} ] ---->
    vASM_REWRITE_TAC[vDEFINT_0] ----> vASM_MESON_TAC[]] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_ADD_LID] ---->
  vMATCH_MP_TAC vDEFINT_COMBINE ----> vEXISTS_TAC [%q {|c:real|} ] ---->
  vASM_REWRITE_TAC[vDEFINT_DELTA_LEFT; vDEFINT_DELTA_RIGHT]);;

let%a vDEFINT_POINT_SPIKE = prove
 ([%q {|!f g a b c i.
        (!x. a <= x /\ x <= b /\ ~(x = c) ==> (f x = g x)) /\ defint(a,b) f i
        ==> defint(a,b) g i|} ],
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC [%q {|a <= b|} ] ++-->
   [vALL_TAC; vASM_MESON_TAC[vREAL_NOT_LE; vDEFINT_WRONG]] ---->
  vMATCH_MP_TAC vINTEGRAL_EQ ---->
  vEXISTS_TAC [%q {|\x:real. f(x) + (g c - f c) * (if x = c then &1 else &0)|} ] ---->
  vASM_REWRITE_TAC[] ----> vCONJ_TAC ++-->
   [vSUBST1_TAC(vREAL_ARITH [%q {|i = i + ((g:real->real) c - f c) * &0|} ]) ---->
    vMATCH_MP_TAC vDEFINT_ADD ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vDEFINT_CMUL ----> vREWRITE_TAC[vDEFINT_DELTA];
    vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
    vASM_SIMP_TAC[vREAL_MUL_RZERO; vREAL_ADD_RID] ---->
    vREAL_ARITH_TAC]);;

let%a vDEFINT_FINITE_SPIKE = prove
 ([%q {|!f g a b s i.
        FINITE s /\
        (!x. a <= x /\ x <= b /\ ~(x IN s) ==> (f x = g x)) /\
        defint(a,b) f i
        ==> defint(a,b) g i|} ],
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vTAUT [%q {|a /\ b /\ c ==> d <=> c ==> a ==> b ==> d|} ]] ---->
  vDISCH_TAC ----> vMAP_EVERY (fun t -> vSPEC_TAC(t,t))
   [[%q {|g:real->real|} ]; [%q {|s:real->bool|} ]] ---->
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vNOT_IN_EMPTY] ---->
  vCONJ_TAC ++--> [vASM_MESON_TAC[vINTEGRAL_EQ]; vALL_TAC] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|c:real|} ]; [%q {|s:real->bool|} ]] ----> vSTRIP_TAC ---->
  vX_GEN_TAC [%q {|g:real->real|} ] ----> vREWRITE_TAC[vIN_INSERT; vDE_MORGAN_THM] ---->
  vDISCH_TAC ----> vMATCH_MP_TAC vDEFINT_POINT_SPIKE ---->
  vEXISTS_TAC [%q {|\x. if x = c then (f:real->real) x else g x|} ] ---->
  vEXISTS_TAC [%q {|c:real|} ] ----> vSIMP_TAC[] ---->
  vFIRST_X_ASSUM vMATCH_MP_TAC ----> vASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Cauchy-type integrability criterion.                                      *)
(* ------------------------------------------------------------------------- *)

let%a vGAUGE_MIN_FINITE = prove
 ([%q {|!s gs n. (!m:num. m <= n ==> gauge s (gs m))
            ==> ?g. gauge s g /\
                    !d p. fine g (d,p) ==> !m. m <= n ==> fine (gs m) (d,p)|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[vLE] ++-->
   [vMESON_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[vTAUT [%q {|a \/ b ==> c <=> (a ==> c) /\ (b ==> c)|} ]] ---->
  vSIMP_TAC[vFORALL_AND_THM; vLEFT_FORALL_IMP_THM; vEXISTS_REFL] ---->
  vSTRIP_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| check (is_imp -| concl)) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|gm:real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|\x:real. if gm x < gs(SUC n) x then gm x else gs(SUC n) x|} ] ---->
  vASM_SIMP_TAC[vGAUGE_MIN; vETA_AX] ----> vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vFINE_MIN) ----> vASM_SIMP_TAC[vETA_AX]);;

let%a vINTEGRABLE_CAUCHY = prove
 ([%q {|!f a b. integrable(a,b) f <=>
           !e. &0 < e
               ==> ?g. gauge (\x. a <= x /\ x <= b) g /\
                       !d1 p1 d2 p2.
                            tdiv (a,b) (d1,p1) /\ fine g (d1,p1) /\
                            tdiv (a,b) (d2,p2) /\ fine g (d2,p2)
                            ==> abs (rsum(d1,p1) f - rsum(d2,p2) f) < e|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[integrable] ----> vEQ_TAC ++-->
   [vREWRITE_TAC[defint] ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|i:real|} ]) ---->
    vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
    vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
    vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|g:real->real|} ] ---->
    vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
    vMAP_EVERY vX_GEN_TAC
     [[%q {|d1:num->real|} ]; [%q {|p1:num->real|} ]; [%q {|d2:num->real|} ]; [%q {|p2:num->real|} ]] ---->
    vSTRIP_TAC ----> vFIRST_X_ASSUM(fun th ->
      vMP_TAC(vSPECL [[%q {|d1:num->real|} ]; [%q {|p1:num->real|} ]] th) ---->
      vMP_TAC(vSPECL [[%q {|d2:num->real|} ]; [%q {|p2:num->real|} ]] th)) ---->
    vASM_REWRITE_TAC[] ----> vREAL_ARITH_TAC;
    vALL_TAC] ---->
  vDISCH_TAC ----> vDISJ_CASES_TAC(vREAL_ARITH [%q {|b < a \/ a <= b|} ]) ++-->
   [vASM_MESON_TAC[vDEFINT_WRONG]; vALL_TAC] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN [%q {|n:num|} ] -| vSPEC [%q {|&1 / &2 pow n|} ]) ---->
  vSIMP_TAC[vREAL_LT_DIV; vREAL_POW_LT; vREAL_OF_NUM_LT; vARITH] ---->
  vREWRITE_TAC[vFORALL_AND_THM; vSKOLEM_THM] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g:num->real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vGEN [%q {|n:num|} ]
   (vSPECL [[%q {|\x. a <= x /\ x <= b|} ]; [%q {|g:num->real->real|} ]; [%q {|n:num|} ]]
          vGAUGE_MIN_FINITE)) ---->
  vASM_REWRITE_TAC[vSKOLEM_THM; vFORALL_AND_THM] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|G:num->real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vGEN [%q {|n:num|} ]
    (vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|(G:num->real->real) n|} ]] vDIVISION_EXISTS)) ---->
  vASM_REWRITE_TAC[vSKOLEM_THM; vLEFT_IMP_EXISTS_THM; vFORALL_AND_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|d:num->num->real|} ]; [%q {|p:num->num->real|} ]] ---->
  vSTRIP_TAC ----> vSUBGOAL_THEN [%q {|cauchy (\n. rsum(d n,p n) f)|} ] vMP_TAC ++-->
   [vREWRITE_TAC[cauchy] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
    vMP_TAC(vSPEC [%q {|&1 / e|} ] vREAL_ARCH_POW2) ----> vMATCH_MP_TAC vMONO_EXISTS ---->
    vX_GEN_TAC [%q {|N:num|} ] ----> vASM_SIMP_TAC[vREAL_LT_LDIV_EQ] ----> vDISCH_TAC ---->
    vREWRITE_TAC[vGE] ----> vMAP_EVERY vX_GEN_TAC [[%q {|m:num|} ]; [%q {|n:num|} ]] ---->
    vSTRIP_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPECL
     [[%q {|N:num|} ]; [%q {|(d:num->num->real) m|} ]; [%q {|(p:num->num->real) m|} ];
      [%q {|(d:num->num->real) n|} ]; [%q {|(p:num->num->real) n|} ]]) ---->
    vANTS_TAC ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
    vMATCH_MP_TAC(vREAL_ARITH [%q {|d < e ==> x < d ==> x < e|} ]) ---->
    vASM_SIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_POW_LT; vREAL_OF_NUM_LT; vARITH] ---->
    vASM_MESON_TAC[vREAL_MUL_SYM];
    vALL_TAC] ---->
  vREWRITE_TAC[vSEQ_CAUCHY; convergent; vSEQ; defint] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|i:real|} ] ----> vSTRIP_TAC ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N1:num|} ] vMP_TAC) ---->
  vX_CHOOSE_TAC [%q {|N2:num|} ] (vSPEC [%q {|&2 / e|} ] vREAL_ARCH_POW2) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|N1 + N2:num|} ]) ----> vREWRITE_TAC[vGE; vLE_ADD] ---->
  vDISCH_TAC ----> vEXISTS_TAC [%q {|(G:num->real->real)(N1 + N2)|} ] ---->
  vASM_REWRITE_TAC[] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|dx:num->real|} ]; [%q {|px:num->real|} ]] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL
   [[%q {|N1 + N2:num|} ]; [%q {|dx:num->real|} ]; [%q {|px:num->real|} ];
    [%q {|(d:num->num->real)(N1 + N2)|} ]; [%q {|(p:num->num->real)(N1 + N2)|} ]]) ---->
  vANTS_TAC ++--> [vASM_MESON_TAC[vLE_REFL]; vALL_TAC] ---->
  vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vREAL_ARITH
   [%q {|abs(s1 - i) < e / &2
    ==> d < e / &2
        ==> abs(s2 - s1) < d ==> abs(s2 - i) < e|} ])) ---->
  vREWRITE_TAC[real_div; vREAL_MUL_LID] ----> vREWRITE_TAC[vGSYM real_div] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_INV_DIV] ---->
  vMATCH_MP_TAC vREAL_LT_INV2 ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|&2 pow N2|} ] ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_POW_MONO ---->
  vREWRITE_TAC[vREAL_OF_NUM_LE] ----> vARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Limit theorem.                                                            *)
(* ------------------------------------------------------------------------- *)

let%a vSUM_DIFFS = prove
 ([%q {|!m n. sum(m,n) (\i. d(SUC i) - d(i)) = d(m + n) - d m|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[sum; vADD_CLAUSES; vREAL_SUB_REFL] ----> vREAL_ARITH_TAC);;

let%a vRSUM_BOUND = prove
 ([%q {|!a b d p e f.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x) <= e)
        ==> abs(rsum(d,p) f) <= e * (b - a)|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[rsum] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|sum(0,dsize d) (\i. abs(f(p i :real) * (d(SUC i) - d i)))|} ] ---->
  vREWRITE_TAC[vSUM_ABS_LE] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|sum(0,dsize d) (\i. e * abs(d(SUC i) - d(i)))|} ] ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSUM_LE ----> vREWRITE_TAC[vADD_CLAUSES; vREAL_ABS_MUL] ---->
    vX_GEN_TAC [%q {|r:num|} ] ----> vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_RMUL ---->
    vREWRITE_TAC[vREAL_ABS_POS] ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
    vASM_MESON_TAC[tdiv; vDIVISION_UBOUND; vDIVISION_LBOUND; vREAL_LE_TRANS];
    vALL_TAC] ---->
  vREWRITE_TAC[vSUM_CMUL] ----> vMATCH_MP_TAC vREAL_LE_LMUL ----> vCONJ_TAC ++-->
   [vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|a:real|} ]) ---->
    vASM_MESON_TAC[vREAL_LE_REFL; vREAL_ABS_POS; vREAL_LE_TRANS; vDIVISION_LE;
                  tdiv];
    vALL_TAC] ---->
  vFIRST_X_ASSUM(vCONJUNCTS_THEN vASSUME_TAC -| vREWRITE_RULE[tdiv]) ---->
  vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vDIVISION_MONO_LE_SUC) ---->
  vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE; vSUM_DIFFS; vADD_CLAUSES] ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|a <= d0 /\ d1 <= b ==> d1 - d0 <= b - a|} ]) ---->
  vASM_MESON_TAC[vDIVISION_LBOUND; vDIVISION_UBOUND]);;

let%a vRSUM_DIFF_BOUND = prove
 ([%q {|!a b d p e f g.
        tdiv(a,b) (d,p) /\
        (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e)
        ==> abs(rsum (d,p) f - rsum (d,p) g) <= e * (b - a)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vRSUM_BOUND) ---->
  vREWRITE_TAC[rsum; vSUM_SUB; vREAL_SUB_RDISTRIB]);;

let%a vINTEGRABLE_LIMIT = prove
 ([%q {|!f a b. (!e. &0 < e
                ==> ?g. (!x. a <= x /\ x <= b ==> abs(f x - g x) <= e) /\
                        integrable(a,b) g)
           ==> integrable(a,b) f|} ],
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC [%q {|a <= b|} ] ++-->
   [vALL_TAC; vASM_MESON_TAC[vREAL_NOT_LE; vDEFINT_WRONG; integrable]] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN [%q {|n:num|} ] -| vSPEC [%q {|&1 / &2 pow n|} ]) ---->
  vSIMP_TAC[vREAL_LT_DIV; vREAL_POW_LT; vREAL_OF_NUM_LT; vARITH] ---->
  vREWRITE_TAC[vFORALL_AND_THM; vSKOLEM_THM; integrable] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g:num->real->real|} ] (vCONJUNCTS_THEN2
   vASSUME_TAC (vX_CHOOSE_TAC [%q {|i:num->real|} ]))) ---->
  vSUBGOAL_THEN [%q {|cauchy i|} ] vMP_TAC ++-->
   [vREWRITE_TAC[cauchy] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
    vMP_TAC(vSPEC [%q {|(&4 * (b - a)) / e|} ] vREAL_ARCH_POW2) ---->
    vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|N:num|} ] ----> vDISCH_TAC ---->
    vMAP_EVERY vX_GEN_TAC [[%q {|m:num|} ]; [%q {|n:num|} ]] ----> vREWRITE_TAC[vGE] ---->
    vSTRIP_TAC ---->
    vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vBINDER_CONV [defint]) ---->
    vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &4|} ]) ---->
    vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
    vDISCH_THEN(fun th -> vMP_TAC(vSPEC [%q {|m:num|} ] th) ---->
      vMP_TAC(vSPEC [%q {|n:num|} ] th)) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|gn:real->real|} ] vSTRIP_ASSUME_TAC) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|gm:real->real|} ] vSTRIP_ASSUME_TAC) ---->
    vMP_TAC(vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ];
                  [%q {|\x:real. if gm x < gn x then gm x else gn x|} ]]
                 vDIVISION_EXISTS) ---->
    vASM_SIMP_TAC[vGAUGE_MIN; vLEFT_IMP_EXISTS_THM] ---->
    vMAP_EVERY vX_GEN_TAC [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]] ---->
    vSTRIP_TAC ---->
    vFIRST_X_ASSUM(vCONJUNCTS_THEN vASSUME_TAC -| vMATCH_MP vFINE_MIN) ---->
    vREPEAT(vFIRST_X_ASSUM(vMP_TAC -| vSPECL [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]])) ---->
    vASM_REWRITE_TAC[] ---->
    vSUBGOAL_THEN [%q {|abs(rsum(d,p) (g(m:num)) - rsum(d,p) (g n)) <= e / &2|} ]
     (fun th -> vMP_TAC th ----> vREAL_ARITH_TAC) ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|&2 / &2 pow N * (b - a)|} ] ---->
    vCONJ_TAC ++-->
     [vMATCH_MP_TAC vRSUM_DIFF_BOUND ----> vASM_REWRITE_TAC[] ---->
      vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC(vREAL_ARITH
       [%q {|!f. abs(f - gm) <= inv(k) /\ abs(f - gn) <= inv(k)
            ==> abs(gm - gn) <= &2 / k|} ]) ---->
      vEXISTS_TAC [%q {|(f:real->real) x|} ] ----> vCONJ_TAC ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ++-->
       [vEXISTS_TAC [%q {|&1 / &2 pow m|} ]; vEXISTS_TAC [%q {|&1 / &2 pow n|} ]] ---->
      vASM_SIMP_TAC[] ----> vREWRITE_TAC[real_div; vREAL_MUL_LID] ---->
      vMATCH_MP_TAC vREAL_LE_INV2 ---->
      vASM_SIMP_TAC[vREAL_POW_LT; vREAL_POW_MONO; vREAL_OF_NUM_LE;
                   vREAL_OF_NUM_LT; vARITH];
      vALL_TAC] ---->
    vREWRITE_TAC[vREAL_ARITH [%q {|&2 / n * x <= e / &2 <=> (&4 * x) / n <= e|} ]] ---->
    vSIMP_TAC[vREAL_LE_LDIV_EQ; vREAL_POW_LT; vREAL_OF_NUM_LT; vARITH] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
    vASM_SIMP_TAC[vGSYM vREAL_LE_LDIV_EQ; vREAL_LT_IMP_LE];
    vALL_TAC] ---->
  vREWRITE_TAC[vSEQ_CAUCHY; convergent] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|s:real|} ] ----> vDISCH_TAC ---->
  vREWRITE_TAC[defint] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|e / &3|} ] -| vGEN_REWRITE_RULE vI [vSEQ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH; vGE] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|N1:num|} ]) ---->
  vMP_TAC(vSPEC [%q {|(&3 * (b - a)) / e|} ] vREAL_ARCH_POW2) ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|N2:num|} ]) ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vBINDER_CONV [defint]) ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|N1 + N2:num|} ]; [%q {|e / &3|} ]]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vMATCH_MP_TAC vMONO_EXISTS ---->
  vX_GEN_TAC [%q {|g:real->real|} ] ----> vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]]) ---->
  vASM_REWRITE_TAC[] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vC vMATCH_MP (vARITH_RULE [%q {|N1:num <= N1 + N2|} ])) ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|abs(sf - sg) <= e / &3
    ==> abs(i - s) < e / &3 ==> abs(sg - i) < e / &3 ==> abs(sf - s) < e|} ]) ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|&1 / &2 pow (N1 + N2) * (b - a)|} ] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vRSUM_DIFF_BOUND ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|&1 / n * x <= e / &3 <=> (&3 * x) / n <= e|} ]] ---->
  vSIMP_TAC[vREAL_LE_LDIV_EQ; vREAL_POW_LT; vREAL_OF_NUM_LT; vARITH] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
  vASM_SIMP_TAC[vGSYM vREAL_LE_LDIV_EQ; vREAL_LT_IMP_LE] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|&2 pow N2|} ] ---->
  vASM_SIMP_TAC[vREAL_LT_IMP_LE; vREAL_POW_MONO; vREAL_OF_NUM_LE; vARITH;
               vARITH_RULE [%q {|N2 <= N1 + N2:num|} ]]);;

(* ------------------------------------------------------------------------- *)
(* Hence continuous functions are integrable.                                *)
(* ------------------------------------------------------------------------- *)

let%a vINTEGRABLE_CONST = prove
 ([%q {|!a b c. integrable(a,b) (\x. c)|} ],
  vREWRITE_TAC[integrable] ----> vMESON_TAC[vDEFINT_CONST]);;

let%a vINTEGRABLE_COMBINE = prove
 ([%q {|!f a b c. a <= b /\ b <= c /\ integrable(a,b) f /\ integrable(b,c) f
         ==> integrable(a,c) f|} ],
  vREWRITE_TAC[integrable] ----> vMESON_TAC[vDEFINT_COMBINE]);;

let%a vINTEGRABLE_POINT_SPIKE = prove
 ([%q {|!f g a b c.
         (!x. a <= x /\ x <= b /\ ~(x = c) ==> f x = g x) /\ integrable(a,b) f
         ==> integrable(a,b) g|} ],
  vREWRITE_TAC[integrable] ----> vMESON_TAC[vDEFINT_POINT_SPIKE]);;

let%a vINTEGRABLE_CONTINUOUS = prove
 ([%q {|!f a b. (!x. a <= x /\ x <= b ==> f contl x) ==> integrable(a,b) f|} ],
  vREPEAT vSTRIP_TAC ----> vDISJ_CASES_TAC(vREAL_ARITH [%q {|b < a \/ a <= b|} ]) ++-->
   [vASM_MESON_TAC[integrable; vDEFINT_WRONG]; vALL_TAC] ---->
  vMATCH_MP_TAC vINTEGRABLE_LIMIT ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]] vCONT_UNIFORM) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e:real|} ]) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vUNDISCH_TAC [%q {|a <= b|} ] ----> vMAP_EVERY (fun t -> vSPEC_TAC(t,t))
   [[%q {|b:real|} ]; [%q {|a:real|} ]] ---->
  vMATCH_MP_TAC vBOLZANO_LEMMA_ALT ----> vCONJ_TAC ++-->
   [vMAP_EVERY vX_GEN_TAC [[%q {|u:real|} ]; [%q {|v:real|} ]; [%q {|w:real|} ]] ---->
    vREPLICATE_TAC 2 (vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
    vDISCH_THEN(fun th -> vDISCH_TAC ----> vMP_TAC th) ---->
    vMATCH_MP_TAC(vTAUT
      [%q {|(a /\ b) /\ (c /\ d ==> e) ==> (a ==> c) /\ (b ==> d) ==> e|} ]) ---->
    vCONJ_TAC ++--> [vASM_MESON_TAC[vREAL_LE_TRANS]; vALL_TAC] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC [%q {|g:real->real|} ])
                               (vX_CHOOSE_TAC [%q {|h:real->real|} ])) ---->
    vEXISTS_TAC [%q {|\x. if x <= v then g(x):real else h(x)|} ] ---->
    vREWRITE_TAC[] ----> vCONJ_TAC ++-->
     [vASM_MESON_TAC[vREAL_LE_TOTAL]; vALL_TAC] ---->
    vMATCH_MP_TAC vINTEGRABLE_COMBINE ----> vEXISTS_TAC [%q {|v:real|} ] ---->
    vASM_REWRITE_TAC[] ----> vCONJ_TAC ---->
    vMATCH_MP_TAC vINTEGRABLE_POINT_SPIKE ++-->
     [vEXISTS_TAC [%q {|g:real->real|} ]; vEXISTS_TAC [%q {|h:real->real|} ]] ---->
    vEXISTS_TAC [%q {|v:real|} ] ----> vASM_REWRITE_TAC[] ----> vSIMP_TAC[] ---->
    vASM_MESON_TAC[vREAL_ARITH [%q {|b <= x /\ x <= c /\ ~(x = b) ==> ~(x <= b)|} ]];
    vALL_TAC] ---->
  vX_GEN_TAC [%q {|x:real|} ] ----> vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|u:real|} ]; [%q {|v:real|} ]] ----> vREPEAT vSTRIP_TAC ---->
  vEXISTS_TAC [%q {|\x:real. (f:real->real) u|} ] ---->
  vASM_REWRITE_TAC[vINTEGRABLE_CONST] ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
  vFIRST_X_ASSUM vMATCH_MP_TAC ---->
  vASM_REAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integrability on a subinterval.                                           *)
(* ------------------------------------------------------------------------- *)

let%a vINTEGRABLE_SPLIT_SIDES = prove
 ([%q {|!f a b c.
        a <= c /\ c <= b /\ integrable(a,b) f
        ==> ?i. !e. &0 < e
                    ==> ?g. gauge(\x. a <= x /\ x <= b) g /\
                            !d1 p1 d2 p2. tdiv(a,c) (d1,p1) /\
                                          fine g (d1,p1) /\
                                          tdiv(c,b) (d2,p2) /\
                                          fine g (d2,p2)
                                          ==> abs((rsum(d1,p1) f +
                                                   rsum(d2,p2) f) - i) < e|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[integrable; defint] ---->
  vREPEAT(vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|i:real|} ] ---->
  vMATCH_MP_TAC vMONO_FORALL ----> vX_GEN_TAC [%q {|e:real|} ] ---->
  vASM_CASES_TAC [%q {|&0 < e|} ] ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|g:real->real|} ] ---->
  vASM_MESON_TAC[vDIVISION_APPEND_STRONG]);;

let%a vINTEGRABLE_SUBINTERVAL_LEFT = prove
 ([%q {|!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(a,c) f|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vX_CHOOSE_TAC [%q {|i:real|} ] -| vMATCH_MP vINTEGRABLE_SPLIT_SIDES) ---->
  vREWRITE_TAC[vINTEGRABLE_CAUCHY] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vSIMP_TAC[vASSUME [%q {|&0 < e|} ]; vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|g:real->real|} ] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vCONJ_TAC ++-->
   [vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [gauge]) ---->
    vREWRITE_TAC[gauge] ----> vASM_MESON_TAC[vREAL_LE_TRANS];
    vALL_TAC] ---->
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|c:real|} ]; [%q {|b:real|} ]; [%q {|g:real->real|} ]] vDIVISION_EXISTS) ---->
  vANTS_TAC ++-->
   [vASM_REWRITE_TAC[] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [gauge]) ---->
    vREWRITE_TAC[gauge] ----> vASM_MESON_TAC[vREAL_LE_TRANS];
    vALL_TAC] ---->
  vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(fun th ->
   vMP_TAC(vSPECL [[%q {|d1:num->real|} ]; [%q {|p1:num->real|} ]] th) ---->
   vMP_TAC(vSPECL [[%q {|d2:num->real|} ]; [%q {|p2:num->real|} ]] th)) ---->
  vREWRITE_TAC[vIMP_IMP; vAND_FORALL_THM] ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]]) ---->
  vASM_REWRITE_TAC[] ----> vREAL_ARITH_TAC);;

let%a vINTEGRABLE_SUBINTERVAL_RIGHT = prove
 ([%q {|!f a b c. a <= c /\ c <= b /\ integrable(a,b) f ==> integrable(c,b) f|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vX_CHOOSE_TAC [%q {|i:real|} ] -| vMATCH_MP vINTEGRABLE_SPLIT_SIDES) ---->
  vREWRITE_TAC[vINTEGRABLE_CAUCHY] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vSIMP_TAC[vASSUME [%q {|&0 < e|} ]; vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|g:real->real|} ] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vCONJ_TAC ++-->
   [vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [gauge]) ---->
    vREWRITE_TAC[gauge] ----> vASM_MESON_TAC[vREAL_LE_TRANS];
    vALL_TAC] ---->
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|a:real|} ]; [%q {|c:real|} ]; [%q {|g:real->real|} ]] vDIVISION_EXISTS) ---->
  vANTS_TAC ++-->
   [vASM_REWRITE_TAC[] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [gauge]) ---->
    vREWRITE_TAC[gauge] ----> vASM_MESON_TAC[vREAL_LE_TRANS];
    vALL_TAC] ---->
  vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [[%q {|d:num->real|} ]; [%q {|p:num->real|} ]]) ---->
  vDISCH_THEN(fun th ->
   vMP_TAC(vSPECL [[%q {|d1:num->real|} ]; [%q {|p1:num->real|} ]] th) ---->
   vMP_TAC(vSPECL [[%q {|d2:num->real|} ]; [%q {|p2:num->real|} ]] th)) ---->
  vASM_REWRITE_TAC[] ----> vREAL_ARITH_TAC);;

let%a vINTEGRABLE_SUBINTERVAL = prove
 ([%q {|!f a b c d. a <= c /\ c <= d /\ d <= b /\ integrable(a,b) f
               ==> integrable(c,d) f|} ],
  vMESON_TAC[vINTEGRABLE_SUBINTERVAL_LEFT; vINTEGRABLE_SUBINTERVAL_RIGHT;
            vREAL_LE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Basic integrability rule for everywhere-differentiable function.          *)
(* ------------------------------------------------------------------------- *)

let vINTEGRABLE_RULE =
  let pth = prove
   ([%q {|(!x. f contl x) ==> integrable(a,b) f|} ],
    vMESON_TAC[vINTEGRABLE_CONTINUOUS]) in
  let match_pth = vPART_MATCH rand pth
  and forsimp = vGEN_REWRITE_RULE vLAND_CONV [vFORALL_SIMP] in
  fun tm ->
    let th1 = match_pth tm in
    let th2 = vCONV_RULE (vLAND_CONV(vBINDER_CONV vCONTINUOUS_CONV)) th1 in
    vMP (forsimp th2) vTRUTH;;

let vINTEGRABLE_CONV = vEQT_INTRO -| vINTEGRABLE_RULE;;

(* ------------------------------------------------------------------------- *)
(* More basic lemmas about integration.                                      *)
(* ------------------------------------------------------------------------- *)

let%a vINTEGRAL_CONST = prove
 ([%q {|!a b c. a <= b ==> integral(a,b) (\x. c) = c * (b - a)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDEFINT_INTEGRAL ---->
  vASM_SIMP_TAC[vDEFINT_CONST]);;

let%a vINTEGRAL_CMUL = prove
 ([%q {|!f c a b. a <= b /\ integrable(a,b) f
             ==> integral(a,b) (\x. c * f(x)) = c * integral(a,b) f|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDEFINT_INTEGRAL ---->
  vASM_SIMP_TAC[vDEFINT_CMUL; vINTEGRABLE_DEFINT]);;

let%a vINTEGRAL_ADD = prove
 ([%q {|!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> integral(a,b) (\x. f(x) + g(x)) =
                 integral(a,b) f + integral(a,b) g|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDEFINT_INTEGRAL ---->
  vASM_SIMP_TAC[vDEFINT_ADD; vINTEGRABLE_DEFINT]);;

let%a vINTEGRAL_SUB = prove
 ([%q {|!f g a b. a <= b /\ integrable(a,b) f /\ integrable(a,b) g
             ==> integral(a,b) (\x. f(x) - g(x)) =
                 integral(a,b) f - integral(a,b) g|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDEFINT_INTEGRAL ---->
  vASM_SIMP_TAC[vDEFINT_SUB; vINTEGRABLE_DEFINT]);;

let%a vINTEGRAL_BY_PARTS = prove
 ([%q {|!f g f' g' a b.
         a <= b /\
         (!x. a <= x /\ x <= b ==> (f diffl f' x) x) /\
         (!x. a <= x /\ x <= b ==> (g diffl g' x) x) /\
         integrable(a,b) (\x. f' x * g x) /\
         integrable(a,b) (\x. f x * g' x)
         ==> integral(a,b) (\x. f x * g' x) =
             (f b * g b - f a * g a) - integral(a,b) (\x. f' x * g x)|} ],
  vMP_TAC vINTEGRATION_BY_PARTS ---->
  vREPEAT(vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC) ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN(vMP_TAC -| vCONJ (vASSUME [%q {|a <= b|} ])) ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM -| vMATCH_MP vDEFINT_INTEGRAL) ---->
  vASM_SIMP_TAC[vINTEGRAL_ADD] ----> vREAL_ARITH_TAC);;

(* ------------------------------------------------------------------------ *)
(* SYM_CANON_CONV - Canonicalizes single application of symmetric operator  *)
(* Rewrites `so as to make fn true`, e.g. fn = (<<) or fn = (=) `1` o fst   *)
(* ------------------------------------------------------------------------ *)

let vSYM_CANON_CONV sym fn =
  vREWR_CONV sym -| check
   (not -| fn -| ((snd -| dest_comb) $-$ vI) -| dest_comb);;

(* ----------------------------------------------------------- *)
(* EXT_CONV `!x. f x = g x` = |- (!x. f x = g x) <=> (f = g)   *)
(* ----------------------------------------------------------- *)

let vEXT_CONV =  vSYM -| uncurry vX_FUN_EQ_CONV -|
      (vI $-$ (mk_eq -| (rator $-$ rator) -| dest_eq)) -| dest_forall;;

(* ------------------------------------------------------------------------ *)
(* Mclaurin's theorem with Lagrange form of remainder                       *)
(* We could weaken the hypotheses slightly, but it's not worth it           *)
(* ------------------------------------------------------------------------ *)

let%a vMCLAURIN = prove(
  [%q {|!f diff h n.
    &0 < h /\
    0 < n /\
    (diff(0) = f) /\
    (!m t. m < n /\ &0 <= t /\ t <= h ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. &0 < t /\ t < h /\
        (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)) +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vUNDISCH_TAC [%q {|0 < n|} ] ---->
  vDISJ_CASES_THEN2 vSUBST_ALL_TAC (vX_CHOOSE_THEN [%q {|r:num|} ] vMP_TAC)
   (vSPEC [%q {|n:num|} ] num_CASES) ----> vREWRITE_TAC[vLT_REFL] ---->
  vDISCH_THEN(vASSUME_TAC -| vSYM) ----> vDISCH_THEN(vK vALL_TAC) ---->
  vSUBGOAL_THEN [%q {|?B. f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m))
                  + (B * ((h pow n) / &(FACT n)))|} ] vMP_TAC ++-->
   [vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_EQ_SUB_RADD] ---->
    vEXISTS_TAC [%q {|(f(h) - sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)))
        * &(FACT n) / (h pow n)|} ] ----> vREWRITE_TAC[real_div] ---->
    vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
    vGEN_REWRITE_TAC (vRATOR_CONV -| vRAND_CONV) [vGSYM vREAL_MUL_RID] ---->
    vAP_TERM_TAC ----> vCONV_TAC vSYM_CONV ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
      [%q {|a * b * c * d = (d * a) * (b * c)|} ]] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ----> vBINOP_TAC ---->
    vMATCH_MP_TAC vREAL_MUL_LINV ++-->
     [vMATCH_MP_TAC vREAL_LT_IMP_NZ ----> vREWRITE_TAC[vREAL_LT; vFACT_LT];
      vMATCH_MP_TAC vPOW_NZ ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
      vASM_REWRITE_TAC[]]; vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|B:real|} ] (vASSUME_TAC -| vSYM)) ---->
  vABBREV_TAC [%q {|g = \t. f(t) -
                      (sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (t pow m)) +
                       (B * ((t pow n) / &(FACT n))))|} ] ---->
  vSUBGOAL_THEN [%q {|(g(&0) = &0) /\ (g(h) = &0)|} ] vASSUME_TAC ++-->
   [vEXPAND_TAC "g" ----> vBETA_TAC ----> vASM_REWRITE_TAC[vREAL_SUB_REFL] ---->
    vEXPAND_TAC "n" ----> vREWRITE_TAC[vPOW_0; vREAL_DIV_LZERO] ---->
    vREWRITE_TAC[vREAL_MUL_RZERO; vREAL_ADD_RID] ----> vREWRITE_TAC[vREAL_SUB_0] ---->
    vMP_TAC(vGEN [%q {|j:num->real|} ]
     (vSPECL [[%q {|j:num->real|} ]; [%q {|r:num|} ]; [%q {|1|} ]] vSUM_OFFSET)) ---->
    vREWRITE_TAC[vADD1; vREAL_EQ_SUB_LADD] ---->
    vDISCH_THEN(fun th -> vREWRITE_TAC[vGSYM th]) ----> vBETA_TAC ---->
    vREWRITE_TAC[vSUM_1] ----> vBETA_TAC ----> vREWRITE_TAC[pow; vFACT] ---->
    vASM_REWRITE_TAC[real_div; vREAL_INV1; vREAL_MUL_RID] ---->
    vCONV_TAC vSYM_CONV ----> vREWRITE_TAC[vREAL_ADD_LID_UNIQ] ---->
    vREWRITE_TAC[vGSYM vADD1; vPOW_0; vREAL_MUL_RZERO; vSUM_0]; vALL_TAC] ---->
  vABBREV_TAC [%q {|difg = \m t. diff(m) t -
      (sum(0,n - m)(\p. (diff(m + p)(&0) / &(FACT p)) * (t pow p))
       + (B * ((t pow (n - m)) / &(FACT(n - m)))))|} ] ---->
  vSUBGOAL_THEN [%q {|difg(0):real->real = g|} ] vASSUME_TAC ++-->
   [vEXPAND_TAC "difg" ----> vBETA_TAC ----> vEXPAND_TAC "g" ---->
    vCONV_TAC vFUN_EQ_CONV ----> vGEN_TAC ----> vBETA_TAC ---->
    vASM_REWRITE_TAC[vADD_CLAUSES; vSUB_0]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|(!m t. m < n /\ (& 0) <= t /\ t <= h ==>
                   (difg(m) diffl difg(SUC m)(t))(t))|} ] vASSUME_TAC ++-->
   [vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vEXPAND_TAC "difg" ----> vBETA_TAC ---->
    vCONV_TAC((funpow 2 vRATOR_CONV -| vRAND_CONV) vHABS_CONV) ---->
    vMATCH_MP_TAC vDIFF_SUB ----> vCONJ_TAC ++-->
     [vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vCONV_TAC((funpow 2 vRATOR_CONV -| vRAND_CONV) vHABS_CONV) ---->
    vMATCH_MP_TAC vDIFF_ADD ----> vCONJ_TAC ++-->
     [vALL_TAC;
      vW(vMP_TAC -| vDIFF_CONV -| rand -| funpow 2 rator -| snd) ---->
      vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_MUL_RID; vREAL_ADD_LID] ---->
      vREWRITE_TAC[vREAL_FACT_NZ; vREAL_SUB_RZERO] ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|t:real|} ]) ---->
      vMATCH_MP_TAC vEQ_IMP ---->
      vAP_THM_TAC ----> vCONV_TAC(vONCE_DEPTH_CONV(vALPHA_CONV [%q {|t:real|} ])) ---->
      vAP_TERM_TAC ----> vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
      vAP_THM_TAC ----> vAP_TERM_TAC ----> vREWRITE_TAC[real_div] ---->
      vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC; vPOW_2] ---->
      vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
        [%q {|a * b * c * d = b * (a * (d * c))|} ]] ---->
      vFIRST_ASSUM(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC -|
        vMATCH_MP vLESS_ADD_1 -| vCONJUNCT1) ---->
      vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB] ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC] ---->
      vREWRITE_TAC[vONCE_REWRITE_RULE[vADD_SYM] (vGSYM vADD1)] ---->
      vREWRITE_TAC[vADD_SUB] ----> vAP_TERM_TAC ---->
      vIMP_SUBST_TAC vREAL_INV_MUL_WEAK ----> vREWRITE_TAC[vREAL_FACT_NZ] ---->
      vREWRITE_TAC[vGSYM vADD1; vFACT; vGSYM vREAL_MUL] ---->
      vREPEAT(vIMP_SUBST_TAC vREAL_INV_MUL_WEAK ---->
             vREWRITE_TAC[vREAL_FACT_NZ; vREAL_INJ; vNOT_SUC]) ---->
      vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
      vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
       [%q {|a * b * c * d * e * f * g = (b * a) * (d * f) * (c * g) * e|} ]] ---->
      vREPEAT(vIMP_SUBST_TAC vREAL_MUL_LINV ----> vREWRITE_TAC[vREAL_FACT_NZ] ---->
             vREWRITE_TAC[vREAL_INJ; vNOT_SUC]) ---->
      vREWRITE_TAC[vREAL_MUL_LID]] ---->
    vFIRST_ASSUM(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC -|
        vMATCH_MP vLESS_ADD_1 -| vCONJUNCT1) ---->
    vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB] ---->
    vREWRITE_TAC[vGSYM vADD_ASSOC] ---->
    vREWRITE_TAC[vONCE_REWRITE_RULE[vADD_SYM] (vGSYM vADD1)] ---->
    vREWRITE_TAC[vADD_SUB] ---->
    vREWRITE_TAC[vGSYM(vREWRITE_RULE[vREAL_EQ_SUB_LADD] vSUM_OFFSET)] ---->
    vBETA_TAC ----> vREWRITE_TAC[vSUM_1] ----> vBETA_TAC ---->
    vCONV_TAC (funpow 2 vRATOR_CONV (vRAND_CONV vHABS_CONV)) ---->
    vGEN_REWRITE_TAC (vRATOR_CONV -| vRAND_CONV) [vGSYM vREAL_ADD_RID] ---->
    vMATCH_MP_TAC vDIFF_ADD ----> vREWRITE_TAC[pow; vDIFF_CONST] ---->
    (vMP_TAC -| vC vSPECL vDIFF_SUM)
     [[%q {|\p x. (diff((p + 1) + m)(&0) / &(FACT(p + 1)))
                * (x pow (p + 1))|} ];
      [%q {|\p x. (diff(p + (SUC m))(&0) / &(FACT p)) * (x pow p)|} ];
      [%q {|0|} ]; [%q {|d:num|} ]; [%q {|t:real|} ]] ----> vBETA_TAC ---->
    vDISCH_THEN vMATCH_MP_TAC ----> vREWRITE_TAC[vADD_CLAUSES] ---->
    vX_GEN_TAC [%q {|k:num|} ] ----> vSTRIP_TAC ---->
    vW(vMP_TAC -| vDIFF_CONV -| rand -| funpow 2 rator -| snd) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|t:real|} ]) ---->
    vMATCH_MP_TAC vEQ_IMP ---->
    vCONV_TAC(vONCE_DEPTH_CONV(vALPHA_CONV [%q {|z:real|} ])) ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_LID; vREAL_MUL_RID] ---->
    vREWRITE_TAC[vGSYM vADD1; vADD_CLAUSES; real_div; vGSYM vREAL_MUL_ASSOC] ---->
    vREWRITE_TAC[vSUC_SUB1] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC [%q {|a * b * c * d = c * (a * d) * b|} ]] ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ---->
    vAP_TERM_TAC ---->
    vSUBGOAL_THEN [%q {|&(SUC k) = inv(inv(&(SUC k)))|} ] vSUBST1_TAC ++-->
     [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_INVINV ---->
      vREWRITE_TAC[vREAL_INJ; vNOT_SUC]; vALL_TAC] ---->
    vIMP_SUBST_TAC(vGSYM vREAL_INV_MUL_WEAK) ++-->
     [vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ----> vREWRITE_TAC[vREAL_FACT_NZ] ---->
      vMATCH_MP_TAC vREAL_LT_IMP_NZ ----> vMATCH_MP_TAC vREAL_INV_POS ---->
      vREWRITE_TAC[vREAL_LT; vLT_0]; vALL_TAC] ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[vFACT; vGSYM vREAL_MUL; vREAL_MUL_ASSOC] ---->
    vIMP_SUBST_TAC vREAL_MUL_LINV ----> vREWRITE_TAC[vREAL_MUL_LID] ---->
    vREWRITE_TAC[vREAL_INJ; vNOT_SUC]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!m. m < n ==>
        ?t. &0 < t /\ t < h /\ (difg(SUC m)(t) = &0)|} ] vMP_TAC ++-->
   [vALL_TAC;
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|r:num|} ]) ----> vEXPAND_TAC "n" ---->
    vREWRITE_TAC[vLESS_SUC_REFL] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|t:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vUNDISCH_TAC [%q {|difg(SUC r)(t:real) = &0|} ] ----> vEXPAND_TAC "difg" ---->
    vASM_REWRITE_TAC[vSUB_REFL; sum; pow; vFACT] ---->
    vREWRITE_TAC[vREAL_SUB_0; vREAL_ADD_LID; real_div] ---->
    vREWRITE_TAC[vREAL_INV1; vREAL_MUL_RID] ----> vDISCH_THEN vSUBST1_TAC ---->
    vGEN_REWRITE_TAC (funpow 2 vRAND_CONV)
     [vAC vREAL_MUL_AC
      [%q {|(a * b) * c = a * (c * b)|} ]] ---->
    vASM_REWRITE_TAC[vGSYM real_div]] ---->
  vSUBGOAL_THEN [%q {|!m:num. m < n ==> (difg(m)(&0) = &0)|} ] vASSUME_TAC ++-->
   [vX_GEN_TAC [%q {|m:num|} ] ----> vEXPAND_TAC "difg" ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC -| vMATCH_MP vLESS_ADD_1) ---->
    vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vADD_SUB] ---->
    vMP_TAC(vGEN [%q {|j:num->real|} ]
     (vSPECL [[%q {|j:num->real|} ]; [%q {|d:num|} ]; [%q {|1|} ]] vSUM_OFFSET)) ---->
    vREWRITE_TAC[vADD1; vREAL_EQ_SUB_LADD] ---->
    vDISCH_THEN(fun th -> vREWRITE_TAC[vGSYM th]) ----> vBETA_TAC ---->
    vREWRITE_TAC[vSUM_1] ----> vBETA_TAC ---->
    vREWRITE_TAC[vFACT; pow; vREAL_INV1; vADD_CLAUSES; real_div; vREAL_MUL_RID] ---->
    vREWRITE_TAC[vGSYM vADD1; vPOW_0; vREAL_MUL_RZERO; vSUM_0; vREAL_ADD_LID] ---->
    vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_MUL_RZERO; vREAL_ADD_RID] ---->
    vREWRITE_TAC[vREAL_SUB_REFL]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!m:num. m < n ==> ?t. &0 < t /\ t < h /\
                        (difg(m) diffl &0)(t)|} ] vMP_TAC ++-->
   [vALL_TAC;
    vDISCH_THEN(fun th -> vGEN_TAC ---->
      vDISCH_THEN(fun t -> vASSUME_TAC t ----> vMP_TAC(vMATCH_MP th t))) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|t:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vDIFF_UNIQ ----> vEXISTS_TAC [%q {|difg(m:num):real->real|} ] ---->
    vEXISTS_TAC [%q {|t:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
    vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
    vFIRST_ASSUM vACCEPT_TAC] ---->
  vINDUCT_TAC ++-->
   [vDISCH_TAC ----> vMATCH_MP_TAC vROLLE ----> vASM_REWRITE_TAC[] ---->
    vSUBGOAL_THEN [%q {|!t. &0 <= t /\ t <= h ==> g differentiable t|} ] vMP_TAC ++-->
     [vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[differentiable] ---->
      vEXISTS_TAC [%q {|difg(SUC 0)(t:real):real|} ] ---->
      vSUBST1_TAC(vSYM(vASSUME [%q {|difg(0):real->real = g|} ])) ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vDISCH_TAC ----> vCONJ_TAC ++-->
     [vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vDIFF_CONT ---->
      vREWRITE_TAC[vGSYM differentiable] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vASM_REWRITE_TAC[];
      vGEN_TAC ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]];
    vDISCH_TAC ---->
    vSUBGOAL_THEN [%q {|m < n:num|} ]
    (fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ++-->
     [vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|SUC m|} ] ---->
      vASM_REWRITE_TAC[vLESS_SUC_REFL]; vALL_TAC] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|t0:real|} ] vSTRIP_ASSUME_TAC) ---->
    vSUBGOAL_THEN [%q {|?t. (& 0) < t /\ t < t0 /\ ((difg(SUC m)) diffl (& 0))t|} ]
    vMP_TAC ++-->
     [vMATCH_MP_TAC vROLLE ----> vASM_REWRITE_TAC[] ----> vCONJ_TAC ++-->
       [vSUBGOAL_THEN [%q {|difg(SUC m)(&0) = &0|} ] vSUBST1_TAC ++-->
         [vFIRST_ASSUM vMATCH_MP_TAC ----> vFIRST_ASSUM vACCEPT_TAC;
          vMATCH_MP_TAC vDIFF_UNIQ ----> vEXISTS_TAC [%q {|difg(m:num):real->real|} ] ---->
          vEXISTS_TAC [%q {|t0:real|} ] ----> vASM_REWRITE_TAC[] ---->
          vFIRST_ASSUM vMATCH_MP_TAC ----> vREPEAT vCONJ_TAC ++-->
           [vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|SUC m|} ] ---->
            vASM_REWRITE_TAC[vLESS_SUC_REFL];
            vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
            vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]]]; vALL_TAC] ---->
      vSUBGOAL_THEN [%q {|!t. &0 <= t /\ t <= t0 ==>
                       difg(SUC m) differentiable t|} ] vASSUME_TAC ++-->
       [vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[differentiable] ---->
        vEXISTS_TAC [%q {|difg(SUC(SUC m))(t:real):real|} ] ---->
        vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
        vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|t0:real|} ] ---->
        vASM_REWRITE_TAC[] ---->
        vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
      vCONJ_TAC ++-->
       [vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vDIFF_CONT ---->
        vREWRITE_TAC[vGSYM differentiable] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
        vASM_REWRITE_TAC[];
        vGEN_TAC ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
        vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]];
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ] vSTRIP_ASSUME_TAC) ---->
      vEXISTS_TAC [%q {|t:real|} ] ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|t0:real|} ] ---->
      vASM_REWRITE_TAC[]]]);;

let%a vMCLAURIN_NEG = prove
 ([%q {|!f diff h n.
    h < &0 /\
    0 < n /\
    (diff(0) = f) /\
    (!m t. m < n /\ h <= t /\ t <= &0 ==>
           (diff(m) diffl diff(SUC m)(t))(t)) ==>
   (?t. h < t /\ t < &0 /\
        (f(h) = sum(0,n)(\m. (diff(m)(&0) / &(FACT m)) * (h pow m)) +
                ((diff(n)(t) / &(FACT n)) * (h pow n))))|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|\x. (f(--x):real)|} ];
                [%q {|\n x. ((--(&1)) pow n) * (diff:num->real->real)(n)(--x)|} ];
                [%q {|--h|} ]; [%q {|n:num|} ]] vMCLAURIN) ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[vREAL_NEG_GT0; pow; vREAL_MUL_LID] ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_LE_NEG2] ---->
  vREWRITE_TAC[vREAL_NEG_NEG; vREAL_NEG_0] ---->
  vONCE_REWRITE_TAC[vAC vCONJ_ACI [%q {|a /\ b /\ c <=> a /\ c /\ b|} ]] ---->
  vW(vC vSUBGOAL_THEN (fun t -> vREWRITE_TAC[t]) -|
  funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vREPEAT vGEN_TAC ---->
    vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
    vDISCH_THEN(vMP_TAC -| vC vCONJ (vSPEC [%q {|t:real|} ] (vDIFF_CONV [%q {|\x. --x|} ]))) ---->
    vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_CHAIN) ---->
    vDISCH_THEN(vMP_TAC -| vGEN_ALL -| vMATCH_MP vDIFF_CMUL) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|(--(&1)) pow m|} ]) ----> vBETA_TAC ---->
    vMATCH_MP_TAC vEQ_IMP ---->
    vCONV_TAC(vONCE_DEPTH_CONV(vALPHA_CONV [%q {|z:real|} ])) ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vCONV_TAC(vAC vREAL_MUL_AC);
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ] vSTRIP_ASSUME_TAC)] ---->
  vEXISTS_TAC [%q {|--t|} ] ----> vONCE_REWRITE_TAC[vGSYM vREAL_LT_NEG2] ---->
  vASM_REWRITE_TAC[vREAL_NEG_NEG; vREAL_NEG_0] ---->
  vBINOP_TAC ++-->
   [vMATCH_MP_TAC vSUM_EQ ---->
    vX_GEN_TAC [%q {|m:num|} ] ----> vREWRITE_TAC[vADD_CLAUSES] ---->
    vDISCH_THEN(vASSUME_TAC -| vCONJUNCT2) ----> vBETA_TAC; vALL_TAC] ---->
  vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
    [%q {|a * b * c * d = (b * c) * (a * d)|} ]] ---->
  vREWRITE_TAC[vGSYM vPOW_MUL; vGSYM vREAL_NEG_MINUS1; vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* More convenient "bidirectional" version.                                  *)
(* ------------------------------------------------------------------------- *)

let%a vMCLAURIN_BI_LE = prove
 ([%q {|!f diff x n.
        (diff 0 = f) /\
        (!m t. m < n /\ abs(t) <= abs(x) ==> (diff m diffl diff (SUC m) t) t)
        ==> ?t. abs(t) <= abs(x) /\
                (f x = sum (0,n) (\m. diff m (&0) / &(FACT m) * x pow m) +
                       diff n t / &(FACT n) * x pow n)|} ],
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC [%q {|n = 0|} ] ++-->
   [vASM_REWRITE_TAC[sum; real_pow; vFACT; vREAL_DIV_1; vREAL_MUL_RID;
                    vREAL_ADD_LID] ---->
    vEXISTS_TAC [%q {|x:real|} ] ----> vREWRITE_TAC[vREAL_LE_REFL]; vALL_TAC] ---->
  vASM_CASES_TAC [%q {|x = &0|} ] ++-->
   [vEXISTS_TAC [%q {|&0|} ] ----> vASM_REWRITE_TAC[vREAL_LE_REFL] ---->
    vUNDISCH_TAC [%q {|~(n = 0)|} ] ----> vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ---->
    vINDUCT_TAC ----> vASM_REWRITE_TAC[vNOT_SUC] ---->
    vREWRITE_TAC[vADD1] ---->
    vREWRITE_TAC[vREWRITE_RULE[vREAL_EQ_SUB_RADD] (vGSYM vSUM_OFFSET)] ---->
    vREWRITE_TAC[vREAL_POW_ADD; vREAL_POW_1; vREAL_MUL_RZERO; vSUM_0] ---->
    vREWRITE_TAC[vREAL_ADD_RID; vREAL_ADD_LID] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vREAL_SUM_CONV) ---->
    vASM_REWRITE_TAC[real_pow; vFACT; vREAL_MUL_RID; vREAL_DIV_1]; vALL_TAC] ---->
  vFIRST_ASSUM(vDISJ_CASES_TAC -| vMATCH_MP (vREAL_ARITH
   [%q {|~(x = &0) ==> &0 < x \/ x < &0|} ]))
  ++-->
   [vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|diff:num->real->real|} ]; [%q {|x:real|} ]; [%q {|n:num|} ]]
                 vMCLAURIN) ---->
    vASM_SIMP_TAC[vREAL_ARITH [%q {|&0 <= t /\ t <= x ==> abs(t) <= abs(x)|} ]] ---->
    vASM_REWRITE_TAC[vLT_NZ] ----> vMATCH_MP_TAC vMONO_EXISTS ---->
    vSIMP_TAC[vREAL_ARITH [%q {|&0 < t /\ t < x ==> abs(t) <= abs(x)|} ]];
    vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|diff:num->real->real|} ]; [%q {|x:real|} ]; [%q {|n:num|} ]]
                 vMCLAURIN_NEG) ---->
    vASM_SIMP_TAC[vREAL_ARITH [%q {|x <= t /\ t <= &0 ==> abs(t) <= abs(x)|} ]] ---->
    vASM_REWRITE_TAC[vLT_NZ] ----> vMATCH_MP_TAC vMONO_EXISTS ---->
    vSIMP_TAC[vREAL_ARITH [%q {|x < t /\ t < &0 ==> abs(t) <= abs(x)|} ]]]);;

(* ------------------------------------------------------------------------- *)
(* Simple strong form if a function is differentiable everywhere.            *)
(* ------------------------------------------------------------------------- *)

let%a vMCLAURIN_ALL_LT = prove
 ([%q {|!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ~(x = &0) /\ 0 < n
            ==> ?t. &0 < abs(t) /\ abs(t) < abs(x) /\
                    (f(x) = sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) +
                            (diff n t / &(FACT n)) * x pow n)|} ],
  vREPEAT vSTRIP_TAC ---->
  vREPEAT_TCL vDISJ_CASES_THEN vMP_TAC
   (vSPECL [[%q {|x:real|} ]; [%q {|&0|} ]] vREAL_LT_TOTAL) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ++-->
   [vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|diff:num->real->real|} ];
                  [%q {|x:real|} ]; [%q {|n:num|} ]] vMCLAURIN_NEG) ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|t:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vUNDISCH_TAC [%q {|t < &0|} ] ----> vUNDISCH_TAC [%q {|x < t|} ] ----> vREAL_ARITH_TAC;
    vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|diff:num->real->real|} ];
                  [%q {|x:real|} ]; [%q {|n:num|} ]] vMCLAURIN) ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|t:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vUNDISCH_TAC [%q {|&0 < t|} ] ----> vUNDISCH_TAC [%q {|t < x|} ] ----> vREAL_ARITH_TAC]);;

let%a vMCLAURIN_ZERO = prove
 ([%q {|!diff n x. (x = &0) /\ 0 < n ==>
       (sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) = diff 0 (&0))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vSUBST1_TAC vMP_TAC) ---->
  vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vINDUCT_TAC ----> vREWRITE_TAC[vLT_REFL] ---->
  vREWRITE_TAC[vLT] ---->
  vDISCH_THEN(vDISJ_CASES_THEN2 (vSUBST1_TAC -| vSYM) vMP_TAC) ++-->
   [vREWRITE_TAC[sum; vADD_CLAUSES; vFACT; real_pow; real_div; vREAL_INV_1] ---->
    vREWRITE_TAC[vREAL_ADD_LID; vREAL_MUL_RID];
    vREWRITE_TAC[sum] ---->
    vDISCH_THEN(fun th -> vASSUME_TAC th ----> vANTE_RES_THEN vSUBST1_TAC th) ---->
    vUNDISCH_TAC [%q {|0 < n|} ] ----> vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ---->
    vINDUCT_TAC ----> vREWRITE_TAC[vLT_REFL] ---->
    vREWRITE_TAC[vADD_CLAUSES; real_pow; vREAL_MUL_LZERO; vREAL_MUL_RZERO] ---->
    vREWRITE_TAC[vREAL_ADD_RID]]);;

let%a vMCLAURIN_ALL_LE = prove
 ([%q {|!f diff.
      (diff 0 = f) /\
      (!m x. ((diff m) diffl (diff(SUC m) x)) x)
      ==> !x n. ?t. abs(t) <= abs(x) /\
                    (f(x) = sum(0,n)(\m. (diff m (&0) / &(FACT m)) * x pow m) +
                            (diff n t / &(FACT n)) * x pow n)|} ],
  vREPEAT vSTRIP_TAC ---->
  vDISJ_CASES_THEN vMP_TAC(vSPECL [[%q {|n:num|} ]; [%q {|0|} ]] vLET_CASES) ++-->
   [vREWRITE_TAC[vLE] ----> vDISCH_THEN vSUBST1_TAC ---->
    vASM_REWRITE_TAC[sum; vREAL_ADD_LID; vFACT] ----> vEXISTS_TAC [%q {|x:real|} ] ---->
    vREWRITE_TAC[vREAL_LE_REFL; real_pow; vREAL_MUL_RID; vREAL_DIV_1];
    vDISCH_TAC ----> vASM_CASES_TAC [%q {|x = &0|} ] ++-->
     [vMP_TAC(vSPEC_ALL vMCLAURIN_ZERO) ----> vASM_REWRITE_TAC[] ---->
      vDISCH_THEN vSUBST1_TAC ----> vEXISTS_TAC [%q {|&0|} ] ---->
      vREWRITE_TAC[vREAL_LE_REFL] ---->
      vSUBGOAL_THEN [%q {|&0 pow n = &0|} ] vSUBST1_TAC ++-->
       [vASM_REWRITE_TAC[vREAL_POW_EQ_0; vGSYM (vCONJUNCT1 vLE); vNOT_LE];
        vREWRITE_TAC[vREAL_ADD_RID; vREAL_MUL_RZERO]];
      vMP_TAC(vSPEC_ALL vMCLAURIN_ALL_LT) ----> vASM_REWRITE_TAC[] ---->
      vDISCH_THEN(vMP_TAC -| vSPEC_ALL) ----> vASM_REWRITE_TAC[] ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ] vSTRIP_ASSUME_TAC) ---->
      vEXISTS_TAC [%q {|t:real|} ] ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]]]);;

(* ------------------------------------------------------------------------- *)
(* Version for exp.                                                          *)
(* ------------------------------------------------------------------------- *)

let%a vMCLAURIN_EXP_LEMMA = prove
 ([%q {|((\n:num. exp) 0 = exp) /\
   (!m x. (((\n:num. exp) m) diffl ((\n:num. exp) (SUC m) x)) x)|} ],
  vREWRITE_TAC[vDIFF_EXP]);;

let%a vMCLAURIN_EXP_LT = prove
 ([%q {|!x n. ~(x = &0) /\ 0 < n
         ==> ?t. &0 < abs(t) /\
                 abs(t) < abs(x) /\
                 (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                           (exp(t) / &(FACT n)) * x pow n)|} ],
  vMP_TAC (vMATCH_MP vMCLAURIN_ALL_LT vMCLAURIN_EXP_LEMMA) ---->
  vREWRITE_TAC[vREAL_EXP_0; real_div; vREAL_MUL_AC; vREAL_MUL_LID; vREAL_MUL_RID]);;

let%a vMCLAURIN_EXP_LE = prove
 ([%q {|!x n. ?t. abs(t) <= abs(x) /\
             (exp(x) = sum(0,n)(\m. x pow m / &(FACT m)) +
                       (exp(t) / &(FACT n)) * x pow n)|} ],
  vMP_TAC (vMATCH_MP vMCLAURIN_ALL_LE vMCLAURIN_EXP_LEMMA) ---->
  vREWRITE_TAC[vREAL_EXP_0; real_div; vREAL_MUL_AC; vREAL_MUL_LID; vREAL_MUL_RID]);;

(* ------------------------------------------------------------------------- *)
(* Version for ln(1 +/- x).                                                  *)
(* ------------------------------------------------------------------------- *)

let vDIFF_LN_COMPOSITE = prove
 ([%q {|!g m x. (g diffl m)(x) /\ &0 < g x
           ==> ((\x. ln(g x)) diffl (inv(g x) * m))(x)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDIFF_CHAIN ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vDIFF_LN ---->
  vASM_REWRITE_TAC[]) in
add_to_diff_net (vSPEC_ALL vDIFF_LN_COMPOSITE);;

let%a vMCLAURIN_LN_POS = prove
 ([%q {|!x n.
     &0 < x /\ 0 < n
     ==> ?t. &0 < t /\
             t < x /\
             (ln(&1 + x) = sum(0,n)
                           (\m. --(&1) pow (SUC m) * (x pow m) / &m) +
               --(&1) pow (SUC n) * x pow n / (&n * (&1 + t) pow n))|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|\x. ln(&1 + x)|} ] vMCLAURIN) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC
    [%q {|\n x. if n = 0 then ln(&1 + x)
           else --(&1) pow (SUC n) *
                &(FACT(PRE n)) * inv((&1 + x) pow n)|} ]) ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|x:real|} ]; [%q {|n:num|} ]]) ---->
  vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vNOT_SUC; vREAL_ADD_RID; vREAL_POW_ONE] ---->
  vREWRITE_TAC[vLN_1; vREAL_INV_1; vREAL_MUL_RID] ---->
  vSUBGOAL_THEN [%q {|~(n = 0)|} ] vASSUME_TAC ++-->
   [vUNDISCH_TAC [%q {|0 < n|} ] ----> vARITH_TAC; vASM_REWRITE_TAC[]] ---->
  vSUBGOAL_THEN [%q {|!p. ~(p = 0) ==> (&(FACT(PRE p)) / &(FACT p) = inv(&p))|} ]
  vASSUME_TAC ++-->
   [vINDUCT_TAC ----> vREWRITE_TAC[vNOT_SUC; vPRE] ---->
    vREWRITE_TAC[real_div; vFACT; vGSYM vREAL_OF_NUM_MUL] ---->
    vREWRITE_TAC[vREAL_INV_MUL] ---->
    vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_RID] ---->
    vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
    vAP_TERM_TAC ----> vMATCH_MP_TAC vREAL_MUL_LINV ---->
    vREWRITE_TAC[vREAL_OF_NUM_EQ] ---->
    vMP_TAC(vSPEC [%q {|p:num|} ] vFACT_LT) ----> vARITH_TAC; vALL_TAC] ---->
  vSUBGOAL_THEN
   [%q {|!p. (if p = 0 then &0 else --(&1) pow (SUC p) * &(FACT (PRE p))) /
        &(FACT p) = --(&1) pow (SUC p) * inv(&p)|} ]
  (fun th -> vREWRITE_TAC[th]) ++-->
   [vINDUCT_TAC ++-->
     [vREWRITE_TAC[vREAL_INV_0; real_div; vREAL_MUL_LZERO; vREAL_MUL_RZERO];
      vREWRITE_TAC[vNOT_SUC] ---->
      vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
      vAP_TERM_TAC ----> vREWRITE_TAC[vGSYM real_div] ---->
      vFIRST_ASSUM vMATCH_MP_TAC ---->
      vREWRITE_TAC[vNOT_SUC]]; vALL_TAC] ---->
  vSUBGOAL_THEN
    [%q {|!t. (--(&1) pow (SUC n) * &(FACT(PRE n)) * inv ((&1 + t) pow n)) /
         &(FACT n) * x pow n = --(&1) pow (SUC n) *
                               x pow n / (&n * (&1 + t) pow n)|} ]
  (fun th -> vREWRITE_TAC[th]) ++-->
   [vGEN_TAC ----> vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vREAL_MUL_SYM] ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vREAL_INV_MUL] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vREAL_MUL_SYM] ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vGSYM real_div] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[real_div; vREAL_MUL_AC] ---->
  vDISCH_THEN vMATCH_MP_TAC ---->
  vX_GEN_TAC [%q {|m:num|} ] ----> vX_GEN_TAC [%q {|u:real|} ] ----> vSTRIP_TAC ---->
  vASM_CASES_TAC [%q {|m = 0|} ] ----> vASM_REWRITE_TAC[] ++-->
   [vW(vMP_TAC -| vSPEC [%q {|u:real|} ] -| vDIFF_CONV -| lhand -| rator -| snd) ---->
    vREWRITE_TAC[vPRE; real_pow; vREAL_ADD_LID; vREAL_MUL_RID] ---->
    vREWRITE_TAC[vREAL_MUL_RNEG; vREAL_MUL_LNEG; vREAL_MUL_RID] ---->
    vREWRITE_TAC[vFACT; vREAL_MUL_RID; vREAL_NEG_NEG] ---->
    vDISCH_THEN vMATCH_MP_TAC ----> vUNDISCH_TAC [%q {|&0 <= u|} ] ----> vREAL_ARITH_TAC;
    vW(vMP_TAC -| vSPEC [%q {|u:real|} ] -| vDIFF_CONV -| lhand -| rator -| snd) ---->
    vSUBGOAL_THEN [%q {|~((&1 + u) pow m = &0)|} ] (fun th -> vREWRITE_TAC[th]) ++-->
     [vREWRITE_TAC[vREAL_POW_EQ_0] ----> vASM_REWRITE_TAC[] ---->
      vUNDISCH_TAC [%q {|&0 <= u|} ] ----> vREAL_ARITH_TAC;
      vMATCH_MP_TAC vEQ_IMP ---->
      vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_RID] ---->
      vREWRITE_TAC[vREAL_ADD_LID; vREAL_MUL_RID] ---->
      vREWRITE_TAC[real_div; real_pow; vREAL_MUL_LNEG; vREAL_MUL_RNEG] ---->
      vREWRITE_TAC[vREAL_NEG_NEG; vREAL_MUL_RID; vREAL_MUL_LID] ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vUNDISCH_TAC [%q {|~(m = 0)|} ] ----> vSPEC_TAC([%q {|m:num|} ],[%q {|p:num|} ]) ---->
      vINDUCT_TAC ----> vREWRITE_TAC[vNOT_SUC] ---->
      vREWRITE_TAC[vSUC_SUB1; vPRE] ----> vREWRITE_TAC[vFACT] ---->
      vREWRITE_TAC[vGSYM vREAL_OF_NUM_MUL] ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
      vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vAP_TERM_TAC ---->
      vREWRITE_TAC[real_pow; vREAL_POW_2] ----> vREWRITE_TAC[vREAL_INV_MUL] ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
      vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vMATCH_MP_TAC vREAL_MUL_LINV ---->
      vREWRITE_TAC[vREAL_POW_EQ_0] ----> vASM_REWRITE_TAC[] ---->
      vREWRITE_TAC[vDE_MORGAN_THM] ----> vDISJ1_TAC ---->
      vUNDISCH_TAC [%q {|&0 <= u|} ] ----> vREAL_ARITH_TAC]]);;

let%a vMCLAURIN_LN_NEG = prove
 ([%q {|!x n. &0 < x /\ x < &1 /\ 0 < n
         ==> ?t. &0 < t /\
                 t < x /\
                 (--(ln(&1 - x)) = sum(0,n) (\m. (x pow m) / &m) +
                                    x pow n / (&n * (&1 - t) pow n))|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|\x. --(ln(&1 - x))|} ] vMCLAURIN) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC
    [%q {|\n x. if n = 0 then --(ln(&1 - x))
           else &(FACT(PRE n)) * inv((&1 - x) pow n)|} ]) ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|x:real|} ]; [%q {|n:num|} ]]) ---->
  vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vREAL_SUB_RZERO] ---->
  vREWRITE_TAC[vNOT_SUC; vLN_1; vREAL_POW_ONE] ---->
  vSUBGOAL_THEN [%q {|~(n = 0)|} ] vASSUME_TAC ++-->
   [vUNDISCH_TAC [%q {|0 < n|} ] ----> vARITH_TAC; vASM_REWRITE_TAC[]] ---->
  vREWRITE_TAC[vREAL_INV_1; vREAL_MUL_RID; vREAL_MUL_LID] ---->
  vSUBGOAL_THEN [%q {|!p. ~(p = 0) ==> (&(FACT(PRE p)) / &(FACT p) = inv(&p))|} ]
  vASSUME_TAC ++-->
   [vINDUCT_TAC ----> vREWRITE_TAC[vNOT_SUC; vPRE] ---->
    vREWRITE_TAC[real_div; vFACT; vGSYM vREAL_OF_NUM_MUL] ---->
    vREWRITE_TAC[vREAL_INV_MUL] ---->
    vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_RID] ---->
    vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
    vAP_TERM_TAC ----> vMATCH_MP_TAC vREAL_MUL_LINV ---->
    vREWRITE_TAC[vREAL_OF_NUM_EQ] ---->
    vMP_TAC(vSPEC [%q {|p:num|} ] vFACT_LT) ----> vARITH_TAC; vALL_TAC] ---->
  vREWRITE_TAC[vREAL_NEG_0] ---->
  vSUBGOAL_THEN [%q {|!p. (if p = 0 then &0 else &(FACT (PRE p))) / &(FACT p) =
                    inv(&p)|} ]
  (fun th -> vREWRITE_TAC[th]) ++-->
   [vINDUCT_TAC ++-->
     [vREWRITE_TAC[vREAL_INV_0; real_div; vREAL_MUL_LZERO];
      vREWRITE_TAC[vNOT_SUC] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vREWRITE_TAC[vNOT_SUC]]; vALL_TAC] ---->
  vSUBGOAL_THEN
    [%q {|!t. (&(FACT(PRE n)) * inv ((&1 - t) pow n)) / &(FACT n) * x pow n
         = x pow n / (&n * (&1 - t) pow n)|} ]
  (fun th -> vREWRITE_TAC[th]) ++-->
   [vGEN_TAC ----> vREWRITE_TAC[real_div; vREAL_MUL_ASSOC] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vREAL_MUL_SYM] ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vREAL_INV_MUL] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vREAL_MUL_SYM] ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vGSYM real_div] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[real_div; vREAL_MUL_AC] ---->
  vDISCH_THEN vMATCH_MP_TAC ---->
  vX_GEN_TAC [%q {|m:num|} ] ----> vX_GEN_TAC [%q {|u:real|} ] ----> vSTRIP_TAC ---->
  vASM_CASES_TAC [%q {|m = 0|} ] ----> vASM_REWRITE_TAC[] ++-->
   [vW(vMP_TAC -| vSPEC [%q {|u:real|} ] -| vDIFF_CONV -| lhand -| rator -| snd) ---->
    vREWRITE_TAC[vPRE; pow; vFACT; vREAL_SUB_LZERO] ---->
    vREWRITE_TAC[vREAL_MUL_RNEG; vREAL_NEG_NEG; vREAL_MUL_RID] ---->
    vDISCH_THEN vMATCH_MP_TAC ---->
    vUNDISCH_TAC [%q {|x < &1|} ] ----> vUNDISCH_TAC [%q {|u:real <= x|} ] ---->
    vREAL_ARITH_TAC;
    vW(vMP_TAC -| vSPEC [%q {|u:real|} ] -| vDIFF_CONV -| lhand -| rator -| snd) ---->
    vSUBGOAL_THEN [%q {|~((&1 - u) pow m = &0)|} ] (fun th -> vREWRITE_TAC[th]) ++-->
     [vREWRITE_TAC[vREAL_POW_EQ_0] ----> vASM_REWRITE_TAC[] ---->
      vUNDISCH_TAC [%q {|x < &1|} ] ----> vUNDISCH_TAC [%q {|u:real <= x|} ] ---->
      vREAL_ARITH_TAC;
      vMATCH_MP_TAC vEQ_IMP ---->
      vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vREWRITE_TAC[vREAL_SUB_LZERO; real_div; vPRE] ---->
      vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_RID] ---->
      vREWRITE_TAC
       [vREAL_MUL_RNEG; vREAL_MUL_LNEG; vREAL_NEG_NEG; vREAL_MUL_RID] ---->
      vUNDISCH_TAC [%q {|~(m = 0)|} ] ----> vSPEC_TAC([%q {|m:num|} ],[%q {|p:num|} ]) ---->
      vINDUCT_TAC ----> vREWRITE_TAC[vNOT_SUC] ---->
      vREWRITE_TAC[vSUC_SUB1; vPRE] ----> vREWRITE_TAC[vFACT] ---->
      vREWRITE_TAC[vGSYM vREAL_OF_NUM_MUL] ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
      vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vAP_TERM_TAC ---->
      vREWRITE_TAC[real_pow; vREAL_POW_2] ----> vREWRITE_TAC[vREAL_INV_MUL] ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
      vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vMATCH_MP_TAC vREAL_MUL_LINV ---->
      vREWRITE_TAC[vREAL_POW_EQ_0] ----> vASM_REWRITE_TAC[] ---->
      vUNDISCH_TAC [%q {|x < &1|} ] ----> vUNDISCH_TAC [%q {|u:real <= x|} ] ---->
      vREAL_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Versions for sin and cos.                                                 *)
(* ------------------------------------------------------------------------- *)

let%a vMCLAURIN_SIN = prove
 ([%q {|!x n. abs(sin x -
             sum(0,n) (\m. (if EVEN m then &0
                            else -- &1 pow ((m - 1) DIV 2) / &(FACT m)) *
                            x pow m))
         <= inv(&(FACT n)) * abs(x) pow n|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|sin|} ]; [%q {|\n x. if n MOD 4 = 0 then sin(x)
                              else if n MOD 4 = 1 then cos(x)
                              else if n MOD 4 = 2 then --sin(x)
                              else --cos(x)|} ]] vMCLAURIN_ALL_LE) ---->
  vW(vC vSUBGOAL_THEN (fun th -> vREWRITE_TAC[th]) -| funpow 2 lhand -| snd) ++-->
   [vCONJ_TAC ++-->
     [vSIMP_TAC[vMOD_0; vARITH_EQ; vEQT_INTRO(vSPEC_ALL vETA_AX)]; vALL_TAC] ---->
    vX_GEN_TAC [%q {|m:num|} ] ----> vX_GEN_TAC [%q {|y:real|} ] ----> vREWRITE_TAC[] ---->
    vMP_TAC(vSPECL [[%q {|m:num|} ]; [%q {|4|} ]] vDIVISION) ---->
    vREWRITE_TAC[vARITH_EQ] ----> vABBREV_TAC [%q {|d = m MOD 4|} ] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vSUBST1_TAC vMP_TAC) ---->
    vREWRITE_TAC[vADD1; vGSYM vADD_ASSOC; vMOD_MULT_ADD] ---->
    vSPEC_TAC([%q {|d:num|} ],[%q {|d:num|} ]) ----> vCONV_TAC vEXPAND_CASES_CONV ---->
    vCONV_TAC vNUM_REDUCE_CONV ----> vREWRITE_TAC[] ---->
    vREPEAT vCONJ_TAC ---->
    vW(vMP_TAC -| vDIFF_CONV -| lhand -| rator -| snd) ---->
    vSIMP_TAC[vREAL_MUL_RID; vREAL_NEG_NEG]; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|x:real|} ]; [%q {|n:num|} ]]) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ]
    (vCONJUNCTS_THEN2 vASSUME_TAC vSUBST1_TAC)) ---->
  vMATCH_MP_TAC(vREAL_ARITH
    [%q {|(x = y) /\ abs(u) <= v ==> abs((x + u) - y) <= v|} ]) ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSUM_EQ ----> vX_GEN_TAC [%q {|r:num|} ] ----> vSTRIP_TAC ---->
    vREWRITE_TAC[vSIN_0; vCOS_0; vREAL_NEG_0] ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vMP_TAC(vSPECL [[%q {|r:num|} ]; [%q {|4|} ]] vDIVISION) ----> vREWRITE_TAC[vARITH_EQ] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
    vDISCH_THEN(fun th -> vGEN_REWRITE_TAC
      (vRAND_CONV -| vONCE_DEPTH_CONV) [th] ---->
      vMP_TAC(vSYM th)) ---->
    vREWRITE_TAC[vEVEN_ADD; vEVEN_MULT; vARITH_EVEN] ---->
    vUNDISCH_TAC [%q {|r MOD 4 < 4|} ] ---->
    vSPEC_TAC([%q {|r MOD 4|} ],[%q {|d:num|} ]) ----> vCONV_TAC vEXPAND_CASES_CONV ---->
    vCONV_TAC vNUM_REDUCE_CONV ----> vREWRITE_TAC[] ---->
    vREWRITE_TAC[real_div; vREAL_MUL_LZERO] ---->
    vSIMP_TAC[vARITH_RULE [%q {|(x + 1) - 1 = x|} ];
             vARITH_RULE [%q {|(x + 3) - 1 = x + 2|} ];
             vARITH_RULE [%q {|x * 4 + 2 = 2 * (2 * x + 1)|} ];
             vARITH_RULE [%q {|x * 4 = 2 * 2 * x|} ]] ---->
    vSIMP_TAC[vDIV_MULT; vARITH_EQ] ---->
    vREWRITE_TAC[vREAL_POW_NEG; vEVEN_ADD; vEVEN_MULT; vARITH_EVEN; vREAL_POW_ONE];
    vALL_TAC] ---->
  vREWRITE_TAC[vREAL_ABS_MUL; vREAL_INV_MUL] ---->
  vMATCH_MP_TAC vREAL_LE_MUL2 ----> vREWRITE_TAC[vREAL_ABS_POS] ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[real_div; vREAL_ABS_MUL] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
    vREWRITE_TAC[vREAL_ABS_INV; vREAL_ABS_NUM] ---->
    vMATCH_MP_TAC vREAL_LE_RMUL ---->
    vSIMP_TAC[vREAL_LE_INV_EQ; vREAL_POS] ---->
    vREPEAT vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_ABS_NEG; vSIN_BOUND; vCOS_BOUND];
    vALL_TAC] ---->
  vREWRITE_TAC[vREAL_ABS_POW; vREAL_LE_REFL]);;

let%a vMCLAURIN_COS = prove
 ([%q {|!x n. abs(cos x -
                   sum(0,n) (\m. (if EVEN m
                                  then -- &1 pow (m DIV 2) / &(FACT m)
                                  else &0) * x pow m))
               <= inv(&(FACT n)) * abs(x) pow n|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|cos|} ]; [%q {|\n x. if n MOD 4 = 0 then cos(x)
                              else if n MOD 4 = 1 then --sin(x)
                              else if n MOD 4 = 2 then --cos(x)
                              else sin(x)|} ]] vMCLAURIN_ALL_LE) ---->
  vW(vC vSUBGOAL_THEN (fun th -> vREWRITE_TAC[th]) -| funpow 2 lhand -| snd) ++-->
   [vCONJ_TAC ++-->
     [vSIMP_TAC[vMOD_0; vARITH_EQ; vEQT_INTRO(vSPEC_ALL vETA_AX)]; vALL_TAC] ---->
    vX_GEN_TAC [%q {|m:num|} ] ----> vX_GEN_TAC [%q {|y:real|} ] ----> vREWRITE_TAC[] ---->
    vMP_TAC(vSPECL [[%q {|m:num|} ]; [%q {|4|} ]] vDIVISION) ---->
    vREWRITE_TAC[vARITH_EQ] ----> vABBREV_TAC [%q {|d = m MOD 4|} ] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vSUBST1_TAC vMP_TAC) ---->
    vREWRITE_TAC[vADD1; vGSYM vADD_ASSOC; vMOD_MULT_ADD] ---->
    vSPEC_TAC([%q {|d:num|} ],[%q {|d:num|} ]) ----> vCONV_TAC vEXPAND_CASES_CONV ---->
    vCONV_TAC vNUM_REDUCE_CONV ----> vREWRITE_TAC[] ---->
    vREPEAT vCONJ_TAC ---->
    vW(vMP_TAC -| vDIFF_CONV -| lhand -| rator -| snd) ---->
    vSIMP_TAC[vREAL_MUL_RID; vREAL_NEG_NEG]; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|x:real|} ]; [%q {|n:num|} ]]) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ]
    (vCONJUNCTS_THEN2 vASSUME_TAC vSUBST1_TAC)) ---->
  vMATCH_MP_TAC(vREAL_ARITH
    [%q {|(x = y) /\ abs(u) <= v ==> abs((x + u) - y) <= v|} ]) ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSUM_EQ ----> vX_GEN_TAC [%q {|r:num|} ] ----> vSTRIP_TAC ---->
    vREWRITE_TAC[vSIN_0; vCOS_0; vREAL_NEG_0] ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vMP_TAC(vSPECL [[%q {|r:num|} ]; [%q {|4|} ]] vDIVISION) ----> vREWRITE_TAC[vARITH_EQ] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
    vDISCH_THEN(fun th -> vGEN_REWRITE_TAC
      (vRAND_CONV -| vONCE_DEPTH_CONV) [th] ---->
      vMP_TAC(vSYM th)) ---->
    vREWRITE_TAC[vEVEN_ADD; vEVEN_MULT; vARITH_EVEN] ---->
    vUNDISCH_TAC [%q {|r MOD 4 < 4|} ] ---->
    vSPEC_TAC([%q {|r MOD 4|} ],[%q {|d:num|} ]) ----> vCONV_TAC vEXPAND_CASES_CONV ---->
    vCONV_TAC vNUM_REDUCE_CONV ----> vREWRITE_TAC[] ---->
    vREWRITE_TAC[real_div; vREAL_MUL_LZERO] ---->
    vREWRITE_TAC[vARITH_RULE [%q {|x * 4 + 2 = 2 * (2 * x + 1)|} ];
                vARITH_RULE [%q {|x * 4 + 0 = 2 * 2 * x|} ]] ---->
    vSIMP_TAC[vDIV_MULT; vARITH_EQ] ---->
    vREWRITE_TAC[vREAL_POW_NEG; vEVEN_ADD; vEVEN_MULT; vARITH_EVEN; vREAL_POW_ONE];
    vALL_TAC] ---->
  vREWRITE_TAC[vREAL_ABS_MUL; vREAL_ABS_DIV; vREAL_MUL_ASSOC; vREAL_ABS_POW] ---->
  vMATCH_MP_TAC vREAL_LE_RMUL ----> vSIMP_TAC[vREAL_POW_LE; vREAL_ABS_POS] ---->
  vREWRITE_TAC[real_div; vREAL_ABS_NUM] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
  vMATCH_MP_TAC vREAL_LE_RMUL ----> vREWRITE_TAC[vREAL_LE_INV_EQ; vREAL_POS] ---->
  vREPEAT vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_ABS_NEG; vSIN_BOUND; vCOS_BOUND]);;

(* ------------------------------------------------------------------------- *)
(* Taylor series for atan; needs a bit more preparation.                     *)
(* ------------------------------------------------------------------------- *)

let%a vREAL_ATN_POWSER_SUMMABLE = prove
 ([%q {|!x. abs(x) < &1
       ==> summable (\n. (if EVEN n then &0
                          else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSER_COMPAR ---->
  vEXISTS_TAC [%q {|\n. abs(x) pow n|} ] ----> vCONJ_TAC ++-->
   [vEXISTS_TAC [%q {|0|} ] ----> vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[] ---->
    vCOND_CASES_TAC ---->
    vSIMP_TAC[vREAL_POW_LE; vREAL_MUL_LZERO; vREAL_ABS_POS; vREAL_ABS_NUM] ---->
    vREWRITE_TAC[vREAL_ABS_MUL; vREAL_ABS_DIV; vREAL_ABS_NEG; vREAL_ABS_POW] ---->
    vREWRITE_TAC[vREAL_ABS_NUM; vREAL_POW_ONE; vREAL_MUL_LID] ---->
    vREWRITE_TAC[real_div; vREAL_MUL_LID] ---->
    vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vGSYM real_div] ---->
    vMATCH_MP_TAC vREAL_LE_LDIV ---->
    vCONJ_TAC ++--> [vASM_MESON_TAC[vREAL_OF_NUM_LT; vEVEN; vLT_NZ]; vALL_TAC] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_RID] ---->
    vMATCH_MP_TAC vREAL_LE_LMUL ---->
    vSIMP_TAC[vREAL_POW_LE; vREAL_ABS_POS] ---->
    vASM_MESON_TAC[vREAL_OF_NUM_LE; vEVEN; vARITH_RULE [%q {|1 <= n <=> ~(n = 0)|} ]];
    vALL_TAC] ---->
  vREWRITE_TAC[summable] ----> vEXISTS_TAC [%q {|inv(&1 - abs x)|} ] ---->
  vMATCH_MP_TAC vGP ----> vASM_REWRITE_TAC[vREAL_ABS_ABS]);;

let%a vREAL_ATN_POWSER_DIFFS_SUMMABLE = prove
 ([%q {|!x. abs(x) < &1
       ==> summable (\n. diffs (\n. (if EVEN n then &0
                                     else --(&1) pow ((n - 1) DIV 2) / &n)) n *
                         x pow n)|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[diffs] ---->
  vMATCH_MP_TAC vSER_COMPAR ---->
  vEXISTS_TAC [%q {|\n. abs(x) pow n|} ] ----> vCONJ_TAC ++-->
   [vEXISTS_TAC [%q {|0|} ] ----> vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[] ---->
    vCOND_CASES_TAC ---->
    vSIMP_TAC[vREAL_POW_LE; vREAL_MUL_LZERO; vREAL_MUL_RZERO;
             vREAL_ABS_POS; vREAL_ABS_NUM] ---->
    vSIMP_TAC[vREAL_MUL_ASSOC; vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vNOT_SUC] ---->
    vREWRITE_TAC[vREAL_ABS_MUL; vREAL_ABS_DIV; vREAL_ABS_NEG; vREAL_ABS_POW] ---->
    vREWRITE_TAC[vREAL_ABS_NUM; vREAL_POW_ONE; vREAL_MUL_LID; vREAL_LE_REFL];
    vALL_TAC] ---->
  vREWRITE_TAC[summable] ----> vEXISTS_TAC [%q {|inv(&1 - abs x)|} ] ---->
  vMATCH_MP_TAC vGP ----> vASM_REWRITE_TAC[vREAL_ABS_ABS]);;

let%a vREAL_ATN_POWSER_DIFFS_SUM = prove
 ([%q {|!x. abs(x) < &1
       ==> (\n. diffs (\n. (if EVEN n then &0
                            else --(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)
           sums (inv(&1 + x pow 2))|} ],
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vREAL_ATN_POWSER_DIFFS_SUMMABLE) ---->
  vDISCH_THEN(fun th -> vMP_TAC(vMATCH_MP vSUMMABLE_SUM th) ---->
                       vMP_TAC(vMATCH_MP vSER_PAIR th)) ---->
  vSUBGOAL_THEN
   [%q {|(\n. sum (2 * n,2) (\n. diffs
      (\n. (if EVEN n then &0
            else --(&1) pow ((n - 1) DIV 2) / &n)) n * x pow n)) =
    (\n. --(x pow 2) pow n)|} ]
  vSUBST1_TAC ++-->
   [vABS_TAC ---->
    vCONV_TAC(vLAND_CONV(vLAND_CONV(vRAND_CONV(vTOP_DEPTH_CONV num_CONV)))) ---->
    vREWRITE_TAC[sum; diffs; vADD_CLAUSES; vEVEN_MULT; vARITH_EVEN; vEVEN] ---->
    vREWRITE_TAC[vREAL_ADD_LID; vREAL_ADD_RID; vREAL_MUL_LZERO;
                vREAL_MUL_RZERO] ---->
    vSIMP_TAC[vARITH_RULE [%q {|SUC n - 1 = n|} ]; vDIV_MULT; vARITH_EQ] ---->
    vSIMP_TAC[vREAL_MUL_ASSOC; vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vNOT_SUC] ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_POW_POW] ---->
    vREWRITE_TAC[vGSYM vREAL_POW_MUL] ---->
    vREWRITE_TAC[vREAL_MUL_LNEG; vREAL_MUL_LID]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|(\n. --(x pow 2) pow n) sums inv (&1 + x pow 2)|} ] vMP_TAC ++-->
   [vONCE_REWRITE_TAC[vREAL_ARITH [%q {|&1 + x = &1 - (--x)|} ]] ---->
    vMATCH_MP_TAC vGP ---->
    vREWRITE_TAC[vREAL_ABS_NEG; vREAL_ABS_POW] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
    vASM_SIMP_TAC[vREAL_POW_2; vREAL_LT_MUL2; vREAL_ABS_POS]; vALL_TAC] ---->
  vMESON_TAC[vSUM_UNIQ]);;

let%a vREAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE = prove
 ([%q {|!x. abs(x) < &1
       ==> summable
             (\n. diffs (diffs
                 (\n. (if EVEN n then &0
                       else --(&1) pow ((n - 1) DIV 2) / &n))) n * x pow n)|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[diffs] ---->
  vMATCH_MP_TAC vSER_COMPAR ---->
  vEXISTS_TAC [%q {|\n. &(SUC n) * abs(x) pow n|} ] ----> vCONJ_TAC ++-->
   [vEXISTS_TAC [%q {|0|} ] ----> vREPEAT vSTRIP_TAC ---->
    vREWRITE_TAC[vREAL_ABS_NUM; vREAL_ABS_MUL; vGSYM vREAL_MUL_ASSOC] ---->
    vMATCH_MP_TAC vREAL_LE_LMUL ----> vREWRITE_TAC[vREAL_POS] ---->
    vCOND_CASES_TAC ---->
    vSIMP_TAC[vREAL_POW_LE; vREAL_MUL_LZERO; vREAL_MUL_RZERO;
             vREAL_ABS_POS; vREAL_ABS_NUM] ---->
    vREWRITE_TAC[vREAL_ABS_DIV; vREAL_ABS_NUM; vREAL_MUL_ASSOC] ---->
    vSIMP_TAC[vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vNOT_SUC] ---->
    vREWRITE_TAC[vREAL_ABS_POW; vREAL_ABS_NEG; vREAL_POW_ONE; vREAL_MUL_LID;
                vREAL_ABS_NUM; vREAL_LE_REFL]; vALL_TAC] ---->
  vMATCH_MP_TAC vSER_RATIO ---->
  vSUBGOAL_THEN [%q {|?c. abs(x) < c /\ c < &1|} ] vSTRIP_ASSUME_TAC ++-->
   [vEXISTS_TAC [%q {|(&1 + abs(x)) / &2|} ] ---->
    vSIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_LT_RDIV_EQ; vREAL_OF_NUM_LT; vARITH] ---->
    vUNDISCH_TAC [%q {|abs(x) < &1|} ] ----> vREAL_ARITH_TAC; vALL_TAC] ---->
  vEXISTS_TAC [%q {|c:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vSUBGOAL_THEN [%q {|?N. !n. n >= N ==> &(SUC(SUC n)) * abs(x) <= &(SUC n) * c|} ]
  vSTRIP_ASSUME_TAC ++-->
   [vALL_TAC;
    vEXISTS_TAC [%q {|N:num|} ] ----> vREPEAT vSTRIP_TAC ---->
    vREWRITE_TAC[real_pow; vREAL_ABS_MUL; vREAL_MUL_ASSOC] ---->
    vMATCH_MP_TAC vREAL_LE_RMUL ----> vREWRITE_TAC[vREAL_ABS_POS] ---->
    vREWRITE_TAC[vREAL_ABS_NUM; vREAL_ABS_ABS] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ----> vASM_SIMP_TAC[]] ---->
  vASM_CASES_TAC [%q {|x = &0|} ] ++-->
   [vASM_REWRITE_TAC[vREAL_ABS_NUM; vREAL_MUL_RZERO] ---->
    vEXISTS_TAC [%q {|0|} ] ----> vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_MUL ---->
    vREWRITE_TAC[vREAL_POS] ----> vUNDISCH_TAC [%q {|abs(x) < c|} ] ----> vREAL_ARITH_TAC;
    vALL_TAC] ---->
  vASM_SIMP_TAC[vGSYM vREAL_LE_RDIV_EQ; vGSYM vREAL_ABS_NZ] ---->
  vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
  vREWRITE_TAC[vGSYM real_div] ---->
  vREWRITE_TAC[vADD1; vGSYM vREAL_OF_NUM_ADD] ---->
  vONCE_REWRITE_TAC[vREAL_ARITH [%q {|x + &1 <= y <=> &1 <= y - x * &1|} ]] ---->
  vREWRITE_TAC[vGSYM vREAL_SUB_LDISTRIB] ---->
  vSUBGOAL_THEN [%q {|?N. &1 <= &N * (c / abs x - &1)|} ] vSTRIP_ASSUME_TAC ++-->
   [vALL_TAC;
    vEXISTS_TAC [%q {|N:num|} ] ----> vREWRITE_TAC[vGE] ----> vREPEAT vSTRIP_TAC ---->
    vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vREAL_ARITH
     [%q {|&1 <= x ==> x <= y ==> &1 <= y|} ])) ---->
    vMATCH_MP_TAC vREAL_LE_RMUL ---->
    vASM_SIMP_TAC[vREAL_ARITH [%q {|a <= b ==> a <= b + &1|} ];
                 vREAL_OF_NUM_LE; vREAL_LE_RADD] ---->
    vREWRITE_TAC[vREAL_LE_SUB_LADD; vREAL_ADD_LID] ---->
    vASM_SIMP_TAC[vREAL_LE_RDIV_EQ; vGSYM vREAL_ABS_NZ; vREAL_MUL_LID;
                 vREAL_LT_IMP_LE]] ---->
  vASM_SIMP_TAC[vGSYM vREAL_LE_LDIV_EQ; vREAL_LT_SUB_LADD; vREAL_ADD_LID;
               vREAL_LT_RDIV_EQ; vGSYM vREAL_ABS_NZ; vREAL_MUL_LID;
               vREAL_ARCH_SIMPLE]);;

let%a vREAL_ATN_POWSER_DIFFL = prove
 ([%q {|!x. abs(x) < &1
       ==> ((\x. suminf (\n. (if EVEN n then &0
                              else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n))
            diffl (inv(&1 + x pow 2))) x|} ],
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vREAL_ATN_POWSER_DIFFS_SUM) ---->
  vDISCH_THEN(vSUBST1_TAC -| vMATCH_MP vSUM_UNIQ) ---->
  vMATCH_MP_TAC vTERMDIFF ---->
  vSUBGOAL_THEN [%q {|?K. abs(x) < abs(K) /\ abs(K) < &1|} ] vSTRIP_ASSUME_TAC ++-->
   [vEXISTS_TAC [%q {|(&1 + abs(x)) / &2|} ] ---->
    vSIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_ABS_DIV; vREAL_ABS_NUM;
             vREAL_LT_RDIV_EQ; vREAL_OF_NUM_LT; vARITH] ---->
    vUNDISCH_TAC [%q {|abs(x) < &1|} ] ----> vREAL_ARITH_TAC; vALL_TAC] ---->
  vEXISTS_TAC [%q {|K:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vASM_SIMP_TAC[vREAL_ATN_POWSER_SUMMABLE; vREAL_ATN_POWSER_DIFFS_SUMMABLE;
               vREAL_ATN_POWSER_DIFFS_DIFFS_SUMMABLE]);;

let%a vREAL_ATN_POWSER = prove
 ([%q {|!x. abs(x) < &1
       ==> (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n)
           sums (atn x)|} ],
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vREAL_ATN_POWSER_SUMMABLE) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUMMABLE_SUM) ---->
  vSUBGOAL_THEN
   [%q {|suminf (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n) = atn(x)|} ]
   (fun th -> vREWRITE_TAC[th]) ---->
  vONCE_REWRITE_TAC[vREAL_ARITH [%q {|(a = b) <=> (a - b = &0)|} ]] ---->
  vSUBGOAL_THEN
   [%q {|suminf (\n. (if EVEN n then &0
                 else --(&1) pow ((n - 1) DIV 2) / &n) * &0 pow n) -
    atn(&0) = &0|} ]
  vMP_TAC ++-->
   [vMATCH_MP_TAC(vREAL_ARITH [%q {|(a = &0) /\ (b = &0) ==> (a - b = &0)|} ]) ---->
    vCONJ_TAC ++-->
     [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSUM_UNIQ ---->
      vMP_TAC(vSPEC [%q {|&0|} ] vGP) ---->
      vREWRITE_TAC[vREAL_ABS_NUM; vREAL_OF_NUM_LT; vARITH] ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|&0|} ] -| vMATCH_MP vSER_CMUL) ---->
      vREWRITE_TAC[vREAL_MUL_LZERO] ---->
      vMATCH_MP_TAC vEQ_IMP ---->
      vAP_THM_TAC ----> vAP_TERM_TAC ----> vABS_TAC ---->
      vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_MUL_LZERO] ---->
      vCONV_TAC vSYM_CONV ---->
      vREWRITE_TAC[vREAL_ENTIRE; vREAL_POW_EQ_0] ----> vASM_MESON_TAC[vEVEN];
      vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vTAN_0] ---->
      vMATCH_MP_TAC vTAN_ATN ---->
      vSIMP_TAC[vPI2_BOUNDS; vREAL_ARITH [%q {|&0 < x ==> --x < &0|} ]]];
    vALL_TAC] ---->
  vASM_CASES_TAC [%q {|x = &0|} ] ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(fun th -> vGEN_REWRITE_TAC vRAND_CONV [vSYM th]) ---->
  vMP_TAC(vSPEC [%q {|\x. suminf (\n. (if EVEN n then &0

                       else --(&1) pow ((n - 1) DIV 2) / &n) * x pow n) -
          atn x|} ] vDIFF_ISCONST_END_SIMPLE) ---->
  vFIRST_ASSUM(vDISJ_CASES_TAC -| vMATCH_MP (vREAL_ARITH
    [%q {|~(x = &0) ==> &0 < x \/ x < &0|} ]))
  ++-->
   [vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|&0|} ]; [%q {|x:real|} ]]);
    vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|x:real|} ]; [%q {|&0|} ]])] ---->
  (vREWRITE_TAC[] ----> vDISCH_THEN vMATCH_MP_TAC ---->
   vASM_REWRITE_TAC[] ---->
   vX_GEN_TAC [%q {|u:real|} ] ----> vREPEAT vSTRIP_TAC ---->
   vSUBGOAL_THEN [%q {|abs(u) < &1|} ] (vMP_TAC -| vMATCH_MP vREAL_ATN_POWSER_DIFFL) ++-->
    [vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ----> vREAL_ARITH_TAC;
     vALL_TAC] ---->
   vDISCH_THEN(vMP_TAC -| vC vCONJ (vSPEC [%q {|u:real|} ] vDIFF_ATN)) ---->
   vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_SUB) ---->
   vREWRITE_TAC[vREAL_SUB_REFL]));;

let%a vMCLAURIN_ATN = prove
 ([%q {|!x n. abs(x) < &1
           ==> abs(atn x -
                   sum(0,n) (\m. (if EVEN m then &0
                                  else --(&1) pow ((m - 1) DIV 2) / &m) *
                                  x pow m))
               <= abs(x) pow n / (&1 - abs x)|} ],
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vREAL_ATN_POWSER) ---->
  vDISCH_THEN(fun th -> vASSUME_TAC(vSYM(vMATCH_MP vSUM_UNIQ th)) ---->
                       vMP_TAC(vMATCH_MP vSUM_SUMMABLE th)) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_OFFSET) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|n:num|} ]) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUM_UNIQ) ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|abs(r) <= e ==> (f - s = r) ==> abs(f - s) <= e|} ]) ---->
  vSUBGOAL_THEN
   [%q {|(\m. abs(x) pow (m + n)) sums (abs(x) pow n) * inv(&1 - abs(x))|} ]
  vASSUME_TAC ++-->
   [vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vGP -| vMATCH_MP (vREAL_ARITH
      [%q {|abs(x) < &1 ==> abs(abs x) < &1|} ])) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|abs(x) pow n|} ] -| vMATCH_MP vSER_CMUL) ---->
    vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vGSYM vREAL_POW_ADD];
    vALL_TAC] ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP vSUM_UNIQ -| vREWRITE_RULE[vGSYM real_div]) ---->
  vSUBGOAL_THEN
   [%q {|!m. abs((if EVEN (m + n) then &0
             else --(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
             x pow (m + n))
        <= abs(x) pow (m + n)|} ]
  vASSUME_TAC ++-->
   [vGEN_TAC ----> vCOND_CASES_TAC ---->
    vSIMP_TAC[vREAL_MUL_LZERO; vREAL_ABS_NUM; vREAL_POW_LE; vREAL_ABS_POS] ---->
    vREWRITE_TAC[vREAL_ABS_MUL; vREAL_ABS_DIV; vREAL_ABS_POW; vREAL_ABS_NEG] ---->
    vREWRITE_TAC[vREAL_ABS_NUM; vREAL_POW_ONE; vREAL_MUL_LID] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
    vMATCH_MP_TAC vREAL_LE_RMUL ----> vSIMP_TAC[vREAL_POW_LE; vREAL_ABS_POS] ---->
    vREWRITE_TAC[real_div; vREAL_MUL_LID] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_INV_1] ---->
    vMATCH_MP_TAC vREAL_LE_INV2 ----> vCONV_TAC vREAL_RAT_REDUCE_CONV ---->
    vREWRITE_TAC[vREAL_OF_NUM_LE; vARITH_RULE [%q {|1 <= n <=> ~(n = 0)|} ]] ---->
    vASM_MESON_TAC[vEVEN]; vALL_TAC] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC
   [%q {|suminf (\m. abs((if EVEN (m + n) then &0
                     else --(&1) pow (((m + n) - 1) DIV 2) / &(m + n)) *
                    x pow (m + n)))|} ] ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSER_ABS ----> vMATCH_MP_TAC vSER_COMPARA ---->
    vEXISTS_TAC [%q {|\m. abs(x) pow (m + n)|} ] ---->
    vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[vSUM_SUMMABLE]; vALL_TAC] ---->
  vMATCH_MP_TAC vSER_LE ----> vASM_REWRITE_TAC[] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSER_COMPARA ---->
    vEXISTS_TAC [%q {|\m. abs(x) pow (m + n)|} ] ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vASM_MESON_TAC[vSUM_SUMMABLE]);;
