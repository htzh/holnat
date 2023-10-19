[@@@warning "-33-27-8"]
open Hol.All
open Hol.Accept
include Complex_transc (* hack to keep exp for poly_exp on *)
;;
(* ========================================================================= *)
(* Properties of complex polynomials (not canonically represented).          *)
(* ========================================================================= *)

prioritize_complex();;

parse_as_infix("++",(16,"right"));;
parse_as_infix("**",(20,"right"));;
parse_as_infix("##",(20,"right"));;
parse_as_infix("divides",(14,"right"));;
parse_as_infix("exp",(22,"right"));;

do_list override_interface
  ["++",[%q {|poly_add:complex list->complex list->complex list|} ];
   "**",[%q {|poly_mul:complex list->complex list->complex list|} ];
   "##",[%q {|poly_cmul:complex->complex list->complex list|} ];
   "neg",[%q {|poly_neg:complex list->complex list|} ];
   "divides",[%q {|poly_divides:complex list->complex list->bool|} ];
   "exp",[%q {|poly_exp:complex list -> num -> complex list|} ];
   "diff",[%q {|poly_diff:complex list->complex list|} ]];;

let vSIMPLE_COMPLEX_ARITH tm = prove(tm,vSIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Polynomials.                                                              *)
(* ------------------------------------------------------------------------- *)

let poly = new_recursive_definition list_RECURSION
  [%q {|(poly [] x = Cx(&0)) /\
   (poly (CONS h t) x = h + x * poly t x)|} ];;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on polynomials.                                     *)
(* ------------------------------------------------------------------------- *)

let poly_add = new_recursive_definition list_RECURSION
  [%q {|([] ++ l2 = l2) /\
   ((CONS h t) ++ l2 =
        (if l2 = [] then CONS h t
                    else CONS (h + HD l2) (t ++ TL l2)))|} ];;

let poly_cmul = new_recursive_definition list_RECURSION
  [%q {|(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))|} ];;

let poly_neg = new_definition
  [%q {|neg = (##) (--(Cx(&1)))|} ];;

let poly_mul = new_recursive_definition list_RECURSION
  [%q {|([] ** l2 = []) /\
   ((CONS h t) ** l2 =
        if t = [] then h ## l2
        else (h ## l2) ++ CONS (Cx(&0)) (t ** l2))|} ];;

let poly_exp = new_recursive_definition num_RECURSION
  [%q {|(p exp 0 = [Cx(&1)]) /\
   (p exp (SUC n) = p ** p exp n)|} ];;

(* ------------------------------------------------------------------------- *)
(* Useful clausifications.                                                   *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_ADD_CLAUSES = prove
 ([%q {|([] ++ p2 = p2) /\
   (p1 ++ [] = p1) /\
   ((CONS h1 t1) ++ (CONS h2 t2) = CONS (h1 + h2) (t1 ++ t2))|} ],
  vREWRITE_TAC[poly_add; vNOT_CONS_NIL; vHD; vTL] ---->
  vSPEC_TAC([%q {|p1:complex list|} ],[%q {|p1:complex list|} ]) ---->
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[poly_add]);;

let%a vPOLY_CMUL_CLAUSES = prove
 ([%q {|(c ## [] = []) /\
   (c ## (CONS h t) = CONS (c * h) (c ## t))|} ],
  vREWRITE_TAC[poly_cmul]);;

let%a vPOLY_NEG_CLAUSES = prove
 ([%q {|(neg [] = []) /\
   (neg (CONS h t) = CONS (--h) (neg t))|} ],
  vREWRITE_TAC[poly_neg; vPOLY_CMUL_CLAUSES;
              vCOMPLEX_MUL_LNEG; vCOMPLEX_MUL_LID]);;

let%a vPOLY_MUL_CLAUSES = prove
 ([%q {|([] ** p2 = []) /\
   ([h1] ** p2 = h1 ## p2) /\
   ((CONS h1 (CONS k1 t1)) ** p2 =
        h1 ## p2 ++ CONS (Cx(&0)) (CONS k1 t1 ** p2))|} ],
  vREWRITE_TAC[poly_mul; vNOT_CONS_NIL]);;

(* ------------------------------------------------------------------------- *)
(* Various natural consequences of syntactic definitions.                    *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_ADD = prove
 ([%q {|!p1 p2 x. poly (p1 ++ p2) x = poly p1 x + poly p2 x|} ],
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[poly_add; poly; vCOMPLEX_ADD_LID] ---->
  vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vNOT_CONS_NIL; vHD; vTL; poly; vCOMPLEX_ADD_RID] ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_CMUL = prove
 ([%q {|!p c x. poly (c ## p) x = c * poly p x|} ],
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[poly; poly_cmul] ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_NEG = prove
 ([%q {|!p x. poly (neg p) x = --(poly p x)|} ],
  vREWRITE_TAC[poly_neg; vPOLY_CMUL] ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_MUL = prove
 ([%q {|!x p1 p2. poly (p1 ** p2) x = poly p1 x * poly p2 x|} ],
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[poly_mul; poly; vCOMPLEX_MUL_LZERO; vPOLY_CMUL; vPOLY_ADD] ---->
  vSPEC_TAC([%q {|h:complex|} ],[%q {|h:complex|} ]) ---->
  vSPEC_TAC([%q {|t:complex list|} ],[%q {|t:complex list|} ]) ---->
  vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[poly_mul; vPOLY_CMUL; vPOLY_ADD; poly; vPOLY_CMUL;
    vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID; vNOT_CONS_NIL] ---->
  vASM_REWRITE_TAC[vPOLY_ADD; vPOLY_CMUL; poly] ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_EXP = prove
 ([%q {|!p n x. poly (p exp n) x = (poly p x) pow n|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[poly_exp; complex_pow; vPOLY_MUL] ---->
  vREWRITE_TAC[poly] ----> vSIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Lemmas.                                                                   *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_ADD_RZERO = prove
 ([%q {|!p. poly (p ++ []) = poly p|} ],
  vREWRITE_TAC[vFUN_EQ_THM; vPOLY_ADD; poly; vCOMPLEX_ADD_RID]);;

let%a vPOLY_MUL_ASSOC = prove
 ([%q {|!p q r. poly (p ** (q ** r)) = poly ((p ** q) ** r)|} ],
  vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; vCOMPLEX_MUL_ASSOC]);;

let%a vPOLY_EXP_ADD = prove
 ([%q {|!d n p. poly(p exp (n + d)) = poly(p exp n ** p exp d)|} ],
  vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL] ---->
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vPOLY_MUL; vADD_CLAUSES; poly_exp; poly] ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Key property that f(a) = 0 ==> (x - a) divides p(x). Very delicate!       *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_LINEAR_REM = prove
 ([%q {|!t h. ?q r. CONS h t = [r] ++ [--a; Cx(&1)] ** q|} ],
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[] ++-->
   [vGEN_TAC ----> vEXISTS_TAC [%q {|[]:complex list|} ] ---->
    vEXISTS_TAC [%q {|h:complex|} ] ---->
    vREWRITE_TAC[poly_add; poly_mul; poly_cmul; vNOT_CONS_NIL] ---->
    vREWRITE_TAC[vHD; vTL; vCOMPLEX_ADD_RID];
    vX_GEN_TAC [%q {|k:complex|} ] ---->
    vPOP_ASSUM(vSTRIP_ASSUME_TAC -| vSPEC [%q {|h:complex|} ]) ---->
    vEXISTS_TAC [%q {|CONS (r:complex) q|} ] ----> vEXISTS_TAC [%q {|r * a + k|} ] ---->
    vASM_REWRITE_TAC[vPOLY_ADD_CLAUSES; vPOLY_MUL_CLAUSES; poly_cmul] ---->
    vREWRITE_TAC[vCONS_11] ----> vCONJ_TAC ++-->
     [vSIMPLE_COMPLEX_ARITH_TAC; vALL_TAC] ---->
    vSPEC_TAC([%q {|q:complex list|} ],[%q {|q:complex list|} ]) ---->
    vLIST_INDUCT_TAC ---->
    vREWRITE_TAC[vPOLY_ADD_CLAUSES; vPOLY_MUL_CLAUSES; poly_cmul] ---->
    vREWRITE_TAC[vCOMPLEX_ADD_RID; vCOMPLEX_MUL_LID] ---->
    vREWRITE_TAC[vCOMPLEX_ADD_AC]]);;

let%a vPOLY_LINEAR_DIVIDES = prove
 ([%q {|!a p. (poly p a = Cx(&0)) <=> (p = []) \/ ?q. p = [--a; Cx(&1)] ** q|} ],
  vGEN_TAC ----> vLIST_INDUCT_TAC ++-->
   [vREWRITE_TAC[poly]; vALL_TAC] ---->
  vEQ_TAC ----> vSTRIP_TAC ++-->
   [vDISJ2_TAC ----> vSTRIP_ASSUME_TAC(vSPEC_ALL vPOLY_LINEAR_REM) ---->
    vEXISTS_TAC [%q {|q:complex list|} ] ----> vASM_REWRITE_TAC[] ---->
    vSUBGOAL_THEN [%q {|r = Cx(&0)|} ] vSUBST_ALL_TAC ++-->
     [vUNDISCH_TAC [%q {|poly (CONS h t) a = Cx(&0)|} ] ---->
      vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vPOLY_ADD; vPOLY_MUL] ---->
      vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID;
                  vCOMPLEX_MUL_RID] ---->
      vREWRITE_TAC[vCOMPLEX_ADD_LINV] ----> vSIMPLE_COMPLEX_ARITH_TAC;
      vREWRITE_TAC[poly_mul] ----> vREWRITE_TAC[vNOT_CONS_NIL] ---->
      vSPEC_TAC([%q {|q:complex list|} ],[%q {|q:complex list|} ]) ----> vLIST_INDUCT_TAC ++-->
       [vREWRITE_TAC[poly_cmul; poly_add; vNOT_CONS_NIL;
                    vHD; vTL; vCOMPLEX_ADD_LID];
        vREWRITE_TAC[poly_cmul; poly_add; vNOT_CONS_NIL;
                    vHD; vTL; vCOMPLEX_ADD_LID]]];
    vASM_REWRITE_TAC[] ----> vREWRITE_TAC[poly];
    vASM_REWRITE_TAC[] ----> vREWRITE_TAC[poly] ---->
    vREWRITE_TAC[vPOLY_MUL] ----> vREWRITE_TAC[poly] ---->
    vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID; vCOMPLEX_MUL_RID] ---->
    vREWRITE_TAC[vCOMPLEX_ADD_LINV] ----> vSIMPLE_COMPLEX_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Thanks to the finesse of the above, we can use length rather than degree. *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_LENGTH_MUL = prove
 ([%q {|!q. LENGTH([--a; Cx(&1)] ** q) = SUC(LENGTH q)|} ],
  let lemma = prove
   ([%q {|!p h k a. LENGTH (k ## p ++ CONS h (a ## p)) = SUC(LENGTH p)|} ],
    vLIST_INDUCT_TAC ---->
    vASM_REWRITE_TAC[poly_cmul; vPOLY_ADD_CLAUSES; vLENGTH]) in
  vREWRITE_TAC[poly_mul; vNOT_CONS_NIL; lemma]);;

(* ------------------------------------------------------------------------- *)
(* Thus a nontrivial polynomial of degree n has no more than n roots.        *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_ROOTS_INDEX_LEMMA = prove
 ([%q {|!n. !p. ~(poly p = poly []) /\ (LENGTH p = n)
           ==> ?i. !x. (poly p x = Cx(&0)) ==> ?m. m <= n /\ (x = i m)|} ],
  vINDUCT_TAC ++-->
   [vREWRITE_TAC[vLENGTH_EQ_NIL] ----> vMESON_TAC[];
    vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC [%q {|?a. poly p a = Cx(&0)|} ] ++-->
     [vUNDISCH_TAC [%q {|?a. poly p a = Cx(&0)|} ] ---->
      vDISCH_THEN(vCHOOSE_THEN vMP_TAC) ---->
      vGEN_REWRITE_TAC vLAND_CONV [vPOLY_LINEAR_DIVIDES] ---->
      vDISCH_THEN(vDISJ_CASES_THEN vMP_TAC) ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|q:complex list|} ] vSUBST_ALL_TAC) ---->
      vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
      vUNDISCH_TAC [%q {|~(poly ([-- a; Cx(&1)] ** q) = poly [])|} ] ---->
      vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vPOLY_LENGTH_MUL; vSUC_INJ] ---->
      vDISCH_TAC ----> vASM_CASES_TAC [%q {|poly q = poly []|} ] ++-->
       [vASM_REWRITE_TAC[vPOLY_MUL; poly; vCOMPLEX_MUL_RZERO; vFUN_EQ_THM];
        vDISCH_THEN(vK vALL_TAC)] ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|q:complex list|} ]) ----> vASM_REWRITE_TAC[] ---->
      vDISCH_THEN(vX_CHOOSE_TAC [%q {|i:num->complex|} ]) ---->
      vEXISTS_TAC [%q {|\m. if m = SUC n then a:complex else i m|} ] ---->
      vREWRITE_TAC[vPOLY_MUL; vLE; vCOMPLEX_ENTIRE] ---->
      vX_GEN_TAC [%q {|x:complex|} ] ----> vDISCH_THEN(vDISJ_CASES_THEN vMP_TAC) ++-->
       [vDISCH_THEN(fun th -> vEXISTS_TAC [%q {|SUC n|} ] ----> vMP_TAC th) ---->
        vREWRITE_TAC[poly] ----> vSIMPLE_COMPLEX_ARITH_TAC;
        vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
        vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:num|} ] vSTRIP_ASSUME_TAC) ---->
        vEXISTS_TAC [%q {|m:num|} ] ----> vASM_REWRITE_TAC[] ---->
        vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
        vUNDISCH_TAC [%q {|m:num <= n|} ] ----> vASM_REWRITE_TAC[] ----> vARITH_TAC];
      vUNDISCH_TAC [%q {|~(?a. poly p a = Cx(&0))|} ] ---->
      vREWRITE_TAC[vNOT_EXISTS_THM] ----> vDISCH_TAC ----> vASM_REWRITE_TAC[]]]);;

let%a vPOLY_ROOTS_INDEX_LENGTH = prove
 ([%q {|!p. ~(poly p = poly [])
       ==> ?i. !x. (poly p(x) = Cx(&0)) ==> ?n. n <= LENGTH p /\ (x = i n)|} ],
  vMESON_TAC[vPOLY_ROOTS_INDEX_LEMMA]);;

let%a vPOLY_ROOTS_FINITE_LEMMA = prove
 ([%q {|!p. ~(poly p = poly [])
       ==> ?N i. !x. (poly p(x) = Cx(&0)) ==> ?n:num. n < N /\ (x = i n)|} ],
  vMESON_TAC[vPOLY_ROOTS_INDEX_LENGTH; vLT_SUC_LE]);;

let%a vFINITE_LEMMA = prove
 ([%q {|!i N P. (!x. P x ==> ?n:num. n < N /\ (x = i n))
           ==> ?a. !x. P x ==> norm(x) < a|} ],
  vGEN_TAC ----> vONCE_REWRITE_TAC[vRIGHT_IMP_EXISTS_THM] ----> vINDUCT_TAC ++-->
   [vREWRITE_TAC[vLT] ----> vMESON_TAC[]; vALL_TAC] ---->
  vX_GEN_TAC [%q {|P:complex->bool|} ] ---->
  vPOP_ASSUM(vMP_TAC -| vSPEC [%q {|\z. P z /\ ~(z = (i:num->complex) N)|} ]) ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|a:real|} ]) ---->
  vEXISTS_TAC [%q {|abs(a) + norm(i(N:num)) + &1|} ] ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vLT] ---->
  vSUBGOAL_THEN [%q {|(!x. norm(x) < abs(a) + norm(x) + &1) /\
                (!x y. norm(x) < a ==> norm(x) < abs(a) + norm(y) + &1)|} ]
   (fun th -> vMP_TAC th ----> vMESON_TAC[]) ---->
  vCONJ_TAC ++--> [vREAL_ARITH_TAC; vALL_TAC] ---->
  vREPEAT vGEN_TAC ----> vMP_TAC(vSPEC [%q {|y:complex|} ] vCOMPLEX_NORM_POS) ---->
  vREAL_ARITH_TAC);;

let%a vPOLY_ROOTS_FINITE = prove
 ([%q {|!p. ~(poly p = poly []) <=>
       ?N i. !x. (poly p(x) = Cx(&0)) ==> ?n:num. n < N /\ (x = i n)|} ],
  vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vPOLY_ROOTS_FINITE_LEMMA] ---->
  vREWRITE_TAC[vFUN_EQ_THM; vLEFT_IMP_EXISTS_THM; vNOT_FORALL_THM; poly] ---->
  vMP_TAC(vGENL [[%q {|i:num->complex|} ]; [%q {|N:num|} ]]
   (vSPECL [[%q {|i:num->complex|} ]; [%q {|N:num|} ]; [%q {|\x. poly p x = Cx(&0)|} ]]
         vFINITE_LEMMA)) ---->
  vREWRITE_TAC[] ----> vMESON_TAC[vREAL_ARITH [%q {|~(abs(x) < x)|} ]; vCOMPLEX_NORM_CX]);;

(* ------------------------------------------------------------------------- *)
(* Hence get entirety and cancellation for polynomials.                      *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_ENTIRE_LEMMA = prove
 ([%q {|!p q. ~(poly p = poly []) /\ ~(poly q = poly [])
         ==> ~(poly (p ** q) = poly [])|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vPOLY_ROOTS_FINITE] ---->
  vDISCH_THEN(vCONJUNCTS_THEN vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N2:num|} ] (vX_CHOOSE_TAC [%q {|i2:num->complex|} ])) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N1:num|} ] (vX_CHOOSE_TAC [%q {|i1:num->complex|} ])) ---->
  vEXISTS_TAC [%q {|N1 + N2:num|} ] ---->
  vEXISTS_TAC [%q {|\n:num. if n < N1 then i1(n):complex else i2(n - N1)|} ] ---->
  vX_GEN_TAC [%q {|x:complex|} ] ----> vREWRITE_TAC[vCOMPLEX_ENTIRE; vPOLY_MUL] ---->
  vDISCH_THEN(vDISJ_CASES_THEN (vANTE_RES_THEN (vX_CHOOSE_TAC [%q {|n:num|} ]))) ++-->
   [vEXISTS_TAC [%q {|n:num|} ] ----> vASM_REWRITE_TAC[] ---->
    vFIRST_ASSUM(vMP_TAC -| vCONJUNCT1) ----> vARITH_TAC;
    vEXISTS_TAC [%q {|N1 + n:num|} ] ----> vASM_REWRITE_TAC[vLT_ADD_LCANCEL] ---->
    vREWRITE_TAC[vARITH_RULE [%q {|~(m + n < m:num)|} ]] ---->
    vAP_TERM_TAC ----> vARITH_TAC]);;

let%a vPOLY_ENTIRE = prove
 ([%q {|!p q. (poly (p ** q) = poly []) <=>
         (poly p = poly []) \/ (poly q = poly [])|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vMESON_TAC[vPOLY_ENTIRE_LEMMA];
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL] ---->
    vSTRIP_TAC ---->
    vASM_REWRITE_TAC[vCOMPLEX_MUL_RZERO; vCOMPLEX_MUL_LZERO; poly]]);;

let%a vPOLY_MUL_LCANCEL = prove
 ([%q {|!p q r. (poly (p ** q) = poly (p ** r)) <=>
           (poly p = poly []) \/ (poly q = poly r)|} ],
  let lemma1 = prove
   ([%q {|!p q. (poly (p ++ neg q) = poly []) <=> (poly p = poly q)|} ],
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_ADD; vPOLY_NEG; poly] ---->
    vREWRITE_TAC[vSIMPLE_COMPLEX_ARITH [%q {|(p + --q = Cx(&0)) <=> (p = q)|} ]]) in
  let lemma2 = prove
   ([%q {|!p q r. poly (p ** q ++ neg(p ** r)) = poly (p ** (q ++ neg(r)))|} ],
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_ADD; vPOLY_NEG; vPOLY_MUL] ---->
    vSIMPLE_COMPLEX_ARITH_TAC) in
  vONCE_REWRITE_TAC[vGSYM lemma1] ---->
  vREWRITE_TAC[lemma2; vPOLY_ENTIRE] ---->
  vREWRITE_TAC[lemma1]);;

let%a vPOLY_EXP_EQ_0 = prove
 ([%q {|!p n. (poly (p exp n) = poly []) <=> (poly p = poly []) /\ ~(n = 0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vFUN_EQ_THM; poly] ---->
  vREWRITE_TAC[vLEFT_AND_FORALL_THM] ----> vAP_TERM_TAC ----> vABS_TAC ---->
  vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vINDUCT_TAC ---->
  vREWRITE_TAC[poly_exp; poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID;
    vCX_INJ; vREAL_OF_NUM_EQ; vARITH; vNOT_SUC] ---->
  vASM_REWRITE_TAC[vPOLY_MUL; poly; vCOMPLEX_ENTIRE] ---->
  vCONV_TAC vTAUT);;

let%a vPOLY_PRIME_EQ_0 = prove
 ([%q {|!a. ~(poly [a ; Cx(&1)] = poly [])|} ],
  vGEN_TAC ----> vREWRITE_TAC[vFUN_EQ_THM; poly] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|Cx(&1) - a|} ]) ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_EXP_PRIME_EQ_0 = prove
 ([%q {|!a n. ~(poly ([a ; Cx(&1)] exp n) = poly [])|} ],
  vMESON_TAC[vPOLY_EXP_EQ_0; vPOLY_PRIME_EQ_0]);;

(* ------------------------------------------------------------------------- *)
(* Can also prove a more "constructive" notion of polynomial being trivial.  *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_ZERO_LEMMA = prove
 ([%q {|!h t. (poly (CONS h t) = poly []) ==> (h = Cx(&0)) /\ (poly t = poly [])|} ],
  let lemma = vREWRITE_RULE[vFUN_EQ_THM; poly] vPOLY_ROOTS_FINITE in
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vFUN_EQ_THM; poly] ---->
  vASM_CASES_TAC [%q {|h = Cx(&0)|} ] ----> vASM_REWRITE_TAC[] ++-->
   [vREWRITE_TAC[vCOMPLEX_ADD_LID];
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|Cx(&0)|} ]) ---->
    vPOP_ASSUM vMP_TAC ----> vSIMPLE_COMPLEX_ARITH_TAC] ---->
  vCONV_TAC vCONTRAPOS_CONV ---->
  vDISCH_THEN(vMP_TAC -| vREWRITE_RULE[lemma]) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:num|} ] (vX_CHOOSE_TAC [%q {|i:num->complex|} ])) ---->
  vMP_TAC(vSPECL
    [[%q {|i:num->complex|} ]; [%q {|N:num|} ]; [%q {|\x. poly t x = Cx(&0)|} ]] vFINITE_LEMMA) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|a:real|} ]) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|Cx(abs(a) + &1)|} ]) ---->
  vREWRITE_TAC[vCOMPLEX_ENTIRE; vDE_MORGAN_THM] ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vCX_INJ] ----> vREAL_ARITH_TAC;
    vDISCH_THEN(vMP_TAC -| vMATCH_MP
     (vASSUME [%q {|!x. (poly t x = Cx(&0)) ==> norm(x) < a|} ])) ---->
    vREWRITE_TAC[vCOMPLEX_NORM_CX] ----> vREAL_ARITH_TAC]);;

let%a vPOLY_ZERO = prove
 ([%q {|!p. (poly p = poly []) <=> ALL (\c. c = Cx(&0)) p|} ],
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vMATCH_MP vPOLY_ZERO_LEMMA) ----> vASM_REWRITE_TAC[];
    vPOP_ASSUM(vSUBST1_TAC -| vSYM) ----> vSTRIP_TAC ---->
    vASM_REWRITE_TAC[vFUN_EQ_THM; poly] ----> vSIMPLE_COMPLEX_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Basics of divisibility.                                                   *)
(* ------------------------------------------------------------------------- *)

let divides = new_definition
  [%q {|p1 divides p2 <=> ?q. poly p2 = poly (p1 ** q)|} ];;

let%a vPOLY_PRIMES = prove
 ([%q {|!a p q. [a; Cx(&1)] divides (p ** q) <=>
           [a; Cx(&1)] divides p \/ [a; Cx(&1)] divides q|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[divides; vPOLY_MUL; vFUN_EQ_THM; poly] ---->
  vREWRITE_TAC[vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_RID; vCOMPLEX_MUL_RID] ---->
  vEQ_TAC ++-->
   [vDISCH_THEN(vX_CHOOSE_THEN [%q {|r:complex list|} ] (vMP_TAC -| vSPEC [%q {|--a|} ])) ---->
    vREWRITE_TAC[vCOMPLEX_ENTIRE; vGSYM complex_sub;
                vCOMPLEX_SUB_REFL; vCOMPLEX_MUL_LZERO] ---->
    vDISCH_THEN vDISJ_CASES_TAC ++--> [vDISJ1_TAC; vDISJ2_TAC] ---->
    (vPOP_ASSUM(vMP_TAC -| vREWRITE_RULE[vPOLY_LINEAR_DIVIDES]) ---->
     vREWRITE_TAC[vCOMPLEX_NEG_NEG] ---->
     vDISCH_THEN(vDISJ_CASES_THEN2 vSUBST_ALL_TAC
        (vX_CHOOSE_THEN [%q {|s:complex list|} ] vSUBST_ALL_TAC)) ++-->
      [vEXISTS_TAC [%q {|[]:complex list|} ] ----> vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO];
       vEXISTS_TAC [%q {|s:complex list|} ] ----> vGEN_TAC ---->
       vREWRITE_TAC[vPOLY_MUL; poly] ----> vSIMPLE_COMPLEX_ARITH_TAC]);
    vDISCH_THEN(vDISJ_CASES_THEN(vX_CHOOSE_TAC [%q {|s:complex list|} ])) ---->
    vASM_REWRITE_TAC[] ++-->
     [vEXISTS_TAC [%q {|s ** q|} ]; vEXISTS_TAC [%q {|p ** s|} ]] ---->
    vGEN_TAC ----> vREWRITE_TAC[vPOLY_MUL] ----> vSIMPLE_COMPLEX_ARITH_TAC]);;

let%a vPOLY_DIVIDES_REFL = prove
 ([%q {|!p. p divides p|} ],
  vGEN_TAC ----> vREWRITE_TAC[divides] ----> vEXISTS_TAC [%q {|[Cx(&1)]|} ] ---->
  vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; poly] ----> vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_DIVIDES_TRANS = prove
 ([%q {|!p q r. p divides q /\ q divides r ==> p divides r|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[divides] ---->
  vDISCH_THEN(vCONJUNCTS_THEN vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:complex list|} ] vASSUME_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:complex list|} ] vASSUME_TAC) ---->
  vEXISTS_TAC [%q {|t ** s|} ] ---->
  vASM_REWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; vCOMPLEX_MUL_ASSOC]);;

let%a vPOLY_DIVIDES_EXP = prove
 ([%q {|!p m n. m <= n ==> (p exp m) divides (p exp n)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLE_EXISTS] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC) ---->
  vSPEC_TAC([%q {|d:num|} ],[%q {|d:num|} ]) ----> vINDUCT_TAC ---->
  vREWRITE_TAC[vADD_CLAUSES; vPOLY_DIVIDES_REFL] ---->
  vMATCH_MP_TAC vPOLY_DIVIDES_TRANS ---->
  vEXISTS_TAC [%q {|p exp (m + d)|} ] ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[divides] ----> vEXISTS_TAC [%q {|p:complex list|} ] ---->
  vREWRITE_TAC[poly_exp; vFUN_EQ_THM; vPOLY_MUL] ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_EXP_DIVIDES = prove
 ([%q {|!p q m n. (p exp n) divides q /\ m <= n ==> (p exp m) divides q|} ],
  vMESON_TAC[vPOLY_DIVIDES_TRANS; vPOLY_DIVIDES_EXP]);;

let%a vPOLY_DIVIDES_ADD = prove
 ([%q {|!p q r. p divides q /\ p divides r ==> p divides (q ++ r)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[divides] ---->
  vDISCH_THEN(vCONJUNCTS_THEN vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:complex list|} ] vASSUME_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:complex list|} ] vASSUME_TAC) ---->
  vEXISTS_TAC [%q {|t ++ s|} ] ---->
  vASM_REWRITE_TAC[vFUN_EQ_THM; vPOLY_ADD; vPOLY_MUL] ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_DIVIDES_SUB = prove
 ([%q {|!p q r. p divides q /\ p divides (q ++ r) ==> p divides r|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[divides] ---->
  vDISCH_THEN(vCONJUNCTS_THEN vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:complex list|} ] vASSUME_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:complex list|} ] vASSUME_TAC) ---->
  vEXISTS_TAC [%q {|s ++ neg(t)|} ] ---->
  vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ---->
  vREWRITE_TAC[vFUN_EQ_THM; vPOLY_ADD; vPOLY_MUL; vPOLY_NEG] ---->
  vDISCH_THEN(vSTRIP_ASSUME_TAC -| vGSYM) ---->
  vREWRITE_TAC[vCOMPLEX_ADD_LDISTRIB; vCOMPLEX_MUL_RNEG] ---->
  vASM_REWRITE_TAC[] ----> vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_DIVIDES_SUB2 = prove
 ([%q {|!p q r. p divides r /\ p divides (q ++ r) ==> p divides q|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vPOLY_DIVIDES_SUB ---->
  vEXISTS_TAC [%q {|r:complex list|} ] ----> vASM_REWRITE_TAC[] ---->
  vUNDISCH_TAC [%q {|p divides (q ++ r)|} ] ---->
  vREWRITE_TAC[divides; vPOLY_ADD; vFUN_EQ_THM; vPOLY_MUL] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|s:complex list|} ]) ---->
  vEXISTS_TAC [%q {|s:complex list|} ] ---->
  vX_GEN_TAC [%q {|x:complex|} ] ----> vPOP_ASSUM(vMP_TAC -| vSPEC [%q {|x:complex|} ]) ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vPOLY_DIVIDES_ZERO = prove
 ([%q {|!p q. (poly p = poly []) ==> q divides p|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[divides] ---->
  vEXISTS_TAC [%q {|[]:complex list|} ] ---->
  vASM_REWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; poly; vCOMPLEX_MUL_RZERO]);;

(* ------------------------------------------------------------------------- *)
(* At last, we can consider the order of a root.                             *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_ORDER_EXISTS = prove
 ([%q {|!a d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
             ==> ?n. ([--a; Cx(&1)] exp n) divides p /\
                     ~(([--a; Cx(&1)] exp (SUC n)) divides p)|} ],
  vGEN_TAC ---->
  (vSTRIP_ASSUME_TAC -| prove_recursive_functions_exist num_RECURSION)
    [%q {|(!p q. mulexp 0 p q = q) /\
     (!p q n. mulexp (SUC n) p q = p ** (mulexp n p q))|} ] ---->
  vSUBGOAL_THEN
   [%q {|!d. !p. (LENGTH p = d) /\ ~(poly p = poly [])
           ==> ?n q. (p = mulexp (n:num) [--a; Cx(&1)] q) /\
                     ~(poly q a = Cx(&0))|} ]
  vMP_TAC ++-->
   [vINDUCT_TAC ++-->
     [vREWRITE_TAC[vLENGTH_EQ_NIL] ----> vMESON_TAC[]; vALL_TAC] ---->
    vX_GEN_TAC [%q {|p:complex list|} ] ---->
    vASM_CASES_TAC [%q {|poly p a = Cx(&0)|} ] ++-->
     [vSTRIP_TAC ----> vUNDISCH_TAC [%q {|poly p a = Cx(&0)|} ] ---->
      vDISCH_THEN(vMP_TAC -| vREWRITE_RULE[vPOLY_LINEAR_DIVIDES]) ---->
      vDISCH_THEN(vDISJ_CASES_THEN vMP_TAC) ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|q:complex list|} ] vSUBST_ALL_TAC) ---->
      vUNDISCH_TAC
       [%q {|!p. (LENGTH p = d) /\ ~(poly p = poly [])
            ==> ?n q. (p = mulexp (n:num) [--a; Cx(&1)] q) /\
                      ~(poly q a = Cx(&0))|} ] ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|q:complex list|} ]) ---->
      vRULE_ASSUM_TAC(vREWRITE_RULE[vPOLY_LENGTH_MUL; vPOLY_ENTIRE;
        vDE_MORGAN_THM; vSUC_INJ]) ---->
      vASM_REWRITE_TAC[] ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:num|} ]
       (vX_CHOOSE_THEN [%q {|s:complex list|} ] vSTRIP_ASSUME_TAC)) ---->
      vEXISTS_TAC [%q {|SUC n|} ] ----> vEXISTS_TAC [%q {|s:complex list|} ] ---->
      vASM_REWRITE_TAC[];
      vSTRIP_TAC ----> vEXISTS_TAC [%q {|0|} ] ----> vEXISTS_TAC [%q {|p:complex list|} ] ---->
      vASM_REWRITE_TAC[]];
    vDISCH_TAC ----> vREPEAT vGEN_TAC ---->
    vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:num|} ]
       (vX_CHOOSE_THEN [%q {|s:complex list|} ] vSTRIP_ASSUME_TAC)) ---->
    vEXISTS_TAC [%q {|n:num|} ] ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[divides] ----> vCONJ_TAC ++-->
     [vEXISTS_TAC [%q {|s:complex list|} ] ---->
      vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vINDUCT_TAC ---->
      vASM_REWRITE_TAC[poly_exp; vFUN_EQ_THM; vPOLY_MUL; poly] ---->
      vSIMPLE_COMPLEX_ARITH_TAC;
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|r:complex list|} ] vMP_TAC) ---->
      vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vINDUCT_TAC ---->
      vASM_REWRITE_TAC[] ++-->
       [vUNDISCH_TAC [%q {|~(poly s a = Cx(&0))|} ] ----> vCONV_TAC vCONTRAPOS_CONV ---->
        vREWRITE_TAC[] ----> vDISCH_THEN vSUBST1_TAC ---->
        vREWRITE_TAC[poly; poly_exp; vPOLY_MUL] ----> vSIMPLE_COMPLEX_ARITH_TAC;
        vREWRITE_TAC[] ----> vONCE_ASM_REWRITE_TAC[] ---->
        vONCE_REWRITE_TAC[poly_exp] ---->
        vREWRITE_TAC[vGSYM vPOLY_MUL_ASSOC; vPOLY_MUL_LCANCEL] ---->
        vREWRITE_TAC[vDE_MORGAN_THM] ----> vCONJ_TAC ++-->
         [vREWRITE_TAC[vFUN_EQ_THM] ---->
          vDISCH_THEN(vMP_TAC -| vSPEC [%q {|a + Cx(&1)|} ]) ---->
          vREWRITE_TAC[poly] ----> vSIMPLE_COMPLEX_ARITH_TAC;
          vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ----> vREWRITE_TAC[]]]]]);;

let%a vPOLY_ORDER = prove
 ([%q {|!p a. ~(poly p = poly [])
         ==> ?!n. ([--a; Cx(&1)] exp n) divides p /\
                      ~(([--a; Cx(&1)] exp (SUC n)) divides p)|} ],
  vMESON_TAC[vPOLY_ORDER_EXISTS; vPOLY_EXP_DIVIDES; vLE_SUC_LT; vLT_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Definition of order.                                                      *)
(* ------------------------------------------------------------------------- *)

let order = new_definition
  [%q {|order a p = @n. ([--a; Cx(&1)] exp n) divides p /\
                   ~(([--a; Cx(&1)] exp (SUC n)) divides p)|} ];;

let%a vORDER = prove
 ([%q {|!p a n. ([--a; Cx(&1)] exp n) divides p /\
           ~(([--a; Cx(&1)] exp (SUC n)) divides p) <=>
           (n = order a p) /\
           ~(poly p = poly [])|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[order] ---->
  vEQ_TAC ----> vSTRIP_TAC ++-->
   [vSUBGOAL_THEN [%q {|~(poly p = poly [])|} ] vASSUME_TAC ++-->
     [vFIRST_ASSUM(vUNDISCH_TAC -| check is_neg -| concl) ---->
      vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[divides] ---->
      vDISCH_THEN vSUBST1_TAC ----> vEXISTS_TAC [%q {|[]:complex list|} ] ---->
      vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; poly; vCOMPLEX_MUL_RZERO];
      vASM_REWRITE_TAC[] ----> vCONV_TAC vSYM_CONV ---->
      vMATCH_MP_TAC vSELECT_UNIQUE ----> vREWRITE_TAC[]];
    vONCE_ASM_REWRITE_TAC[] ----> vCONV_TAC vSELECT_CONV] ---->
  vASM_MESON_TAC[vPOLY_ORDER]);;

let%a vORDER_THM = prove
 ([%q {|!p a. ~(poly p = poly [])
         ==> ([--a; Cx(&1)] exp (order a p)) divides p /\
             ~(([--a; Cx(&1)] exp (SUC(order a p))) divides p)|} ],
  vMESON_TAC[vORDER]);;

let%a vORDER_UNIQUE = prove
 ([%q {|!p a n. ~(poly p = poly []) /\
           ([--a; Cx(&1)] exp n) divides p /\
           ~(([--a; Cx(&1)] exp (SUC n)) divides p)
           ==> (n = order a p)|} ],
  vMESON_TAC[vORDER]);;

let%a vORDER_POLY = prove
 ([%q {|!p q a. (poly p = poly q) ==> (order a p = order a q)|} ],
  vREPEAT vSTRIP_TAC ---->
  vASM_REWRITE_TAC[order; divides; vFUN_EQ_THM; vPOLY_MUL]);;

let%a vORDER_ROOT = prove
 ([%q {|!p a. (poly p a = Cx(&0)) <=> (poly p = poly []) \/ ~(order a p = 0)|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|poly p = poly []|} ] ---->
  vASM_REWRITE_TAC[poly] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vREWRITE_RULE[vPOLY_LINEAR_DIVIDES]) ---->
    vASM_CASES_TAC [%q {|p:complex list = []|} ] ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|q:complex list|} ] vSUBST_ALL_TAC) ----> vDISCH_TAC ---->
    vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|a:complex|} ] -| vMATCH_MP vORDER_THM) ---->
    vASM_REWRITE_TAC[poly_exp; vDE_MORGAN_THM] ----> vDISJ2_TAC ---->
    vREWRITE_TAC[divides] ----> vEXISTS_TAC [%q {|q:complex list|} ] ---->
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; poly] ----> vSIMPLE_COMPLEX_ARITH_TAC;
    vDISCH_TAC ---->
    vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|a:complex|} ] -| vMATCH_MP vORDER_THM) ---->
    vUNDISCH_TAC [%q {|~(order a p = 0)|} ] ---->
    vSPEC_TAC([%q {|order a p|} ],[%q {|n:num|} ]) ---->
    vINDUCT_TAC ----> vASM_REWRITE_TAC[poly_exp; vNOT_SUC] ---->
    vDISCH_THEN(vMP_TAC -| vCONJUNCT1) ----> vREWRITE_TAC[divides] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:complex list|} ] vSUBST1_TAC) ---->
    vREWRITE_TAC[vPOLY_MUL; poly] ----> vSIMPLE_COMPLEX_ARITH_TAC]);;

let%a vORDER_DIVIDES = prove
 ([%q {|!p a n. ([--a; Cx(&1)] exp n) divides p <=>
           (poly p = poly []) \/ n <= order a p|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|poly p = poly []|} ] ---->
  vASM_REWRITE_TAC[] ++-->
   [vASM_REWRITE_TAC[divides] ----> vEXISTS_TAC [%q {|[]:complex list|} ] ---->
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; poly; vCOMPLEX_MUL_RZERO];
    vASM_MESON_TAC[vORDER_THM; vPOLY_EXP_DIVIDES; vNOT_LE; vLE_SUC_LT]]);;

let%a vORDER_DECOMP = prove
 ([%q {|!p a. ~(poly p = poly [])
         ==> ?q. (poly p = poly (([--a; Cx(&1)] exp (order a p)) ** q)) /\
                 ~([--a; Cx(&1)] divides q)|} ],
  vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vORDER_THM) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC -| vSPEC [%q {|a:complex|} ]) ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|q:complex list|} ] -| vREWRITE_RULE[divides]) ---->
  vEXISTS_TAC [%q {|q:complex list|} ] ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|r: complex list|} ] -| vREWRITE_RULE[divides]) ---->
  vUNDISCH_TAC [%q {|~([-- a; Cx(&1)] exp SUC (order a p) divides p)|} ] ---->
  vASM_REWRITE_TAC[] ----> vREWRITE_TAC[divides] ---->
  vEXISTS_TAC [%q {|r:complex list|} ] ---->
  vASM_REWRITE_TAC[vPOLY_MUL; vFUN_EQ_THM; poly_exp] ---->
  vSIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Important composition properties of orders.                               *)
(* ------------------------------------------------------------------------- *)

let%a vORDER_MUL = prove
 ([%q {|!a p q. ~(poly (p ** q) = poly []) ==>
           (order a (p ** q) = order a p + order a q)|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(fun th -> vASSUME_TAC th ----> vMP_TAC th) ---->
  vREWRITE_TAC[vPOLY_ENTIRE; vDE_MORGAN_THM] ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|(order a p + order a q = order a (p ** q)) /\
                ~(poly (p ** q) = poly [])|} ]
  vMP_TAC ++--> [vALL_TAC; vMESON_TAC[]] ---->
  vREWRITE_TAC[vGSYM vORDER] ----> vCONJ_TAC ++-->
   [vMP_TAC(vCONJUNCT1 (vSPEC [%q {|a:complex|} ]
      (vMATCH_MP vORDER_THM (vASSUME [%q {|~(poly p = poly [])|} ])))) ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|r: complex list|} ] -| vREWRITE_RULE[divides]) ---->
    vMP_TAC(vCONJUNCT1 (vSPEC [%q {|a:complex|} ]
      (vMATCH_MP vORDER_THM (vASSUME [%q {|~(poly q = poly [])|} ])))) ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|s: complex list|} ] -| vREWRITE_RULE[divides]) ---->
    vREWRITE_TAC[divides; vFUN_EQ_THM] ----> vEXISTS_TAC [%q {|s ** r|} ] ---->
    vASM_REWRITE_TAC[vPOLY_MUL; vPOLY_EXP_ADD] ----> vSIMPLE_COMPLEX_ARITH_TAC;
    vX_CHOOSE_THEN [%q {|r: complex list|} ] vSTRIP_ASSUME_TAC
    (vSPEC [%q {|a:complex|} ] (vMATCH_MP vORDER_DECOMP
       (vASSUME [%q {|~(poly p = poly [])|} ]))) ---->
    vX_CHOOSE_THEN [%q {|s: complex list|} ] vSTRIP_ASSUME_TAC
    (vSPEC [%q {|a:complex|} ] (vMATCH_MP vORDER_DECOMP
       (vASSUME [%q {|~(poly q = poly [])|} ]))) ---->
    vASM_REWRITE_TAC[divides; vFUN_EQ_THM; vPOLY_EXP_ADD; vPOLY_MUL; poly_exp] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:complex list|} ] vSTRIP_ASSUME_TAC) ---->
    vSUBGOAL_THEN [%q {|[--a; Cx(&1)] divides (r ** s)|} ] vMP_TAC ++-->
     [vALL_TAC; vASM_REWRITE_TAC[vPOLY_PRIMES]] ---->
    vREWRITE_TAC[divides] ----> vEXISTS_TAC [%q {|t:complex list|} ] ---->
    vSUBGOAL_THEN [%q {|poly ([-- a; Cx(&1)] exp (order a p) ** r ** s) =
                  poly ([-- a; Cx(&1)] exp (order a p) **
                       ([-- a; Cx(&1)] ** t))|} ]
    vMP_TAC ++-->
     [vALL_TAC; vMESON_TAC[vPOLY_MUL_LCANCEL; vPOLY_EXP_PRIME_EQ_0]] ---->
    vSUBGOAL_THEN [%q {|poly ([-- a; Cx(&1)] exp (order a q) **
                        [-- a; Cx(&1)] exp (order a p) ** r ** s) =
                  poly ([-- a; Cx(&1)] exp (order a q) **
                        [-- a; Cx(&1)] exp (order a p) **
                        [-- a; Cx(&1)] ** t)|} ]
    vMP_TAC ++-->
     [vALL_TAC; vMESON_TAC[vPOLY_MUL_LCANCEL; vPOLY_EXP_PRIME_EQ_0]] ---->
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; vPOLY_ADD] ---->
    vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vREWRITE_TAC[vCOMPLEX_MUL_AC]]);;

(* ------------------------------------------------------------------------- *)
(* Normalization of a polynomial.                                            *)
(* ------------------------------------------------------------------------- *)

let normalize = new_recursive_definition list_RECURSION
  [%q {|(normalize [] = []) /\
   (normalize (CONS h t) =
        if normalize t = [] then if h = Cx(&0) then [] else [h]
        else CONS h (normalize t))|} ];;

let%a vPOLY_NORMALIZE = prove
 ([%q {|!p. poly (normalize p) = poly p|} ],
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[normalize; poly] ---->
  vASM_CASES_TAC [%q {|h = Cx(&0)|} ] ----> vASM_REWRITE_TAC[] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[poly; vFUN_EQ_THM] ---->
  vUNDISCH_TAC [%q {|poly (normalize t) = poly t|} ] ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vASM_REWRITE_TAC[poly] ---->
  vREWRITE_TAC[vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_LID]);;

let%a vLENGTH_NORMALIZE_LE = prove
 ([%q {|!p. LENGTH(normalize p) <= LENGTH p|} ],
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vLENGTH; normalize; vLE_REFL] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vLENGTH; vLE_SUC] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vLENGTH] ----> vARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* The degree of a polynomial.                                               *)
(* ------------------------------------------------------------------------- *)

let degree = new_definition
  [%q {|degree p = PRE(LENGTH(normalize p))|} ];;

let%a vDEGREE_ZERO = prove
 ([%q {|!p. (poly p = poly []) ==> (degree p = 0)|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[degree] ---->
  vSUBGOAL_THEN [%q {|normalize p = []|} ] vSUBST1_TAC ++-->
   [vPOP_ASSUM vMP_TAC ----> vSPEC_TAC([%q {|p:complex list|} ],[%q {|p:complex list|} ]) ---->
    vREWRITE_TAC[vPOLY_ZERO] ---->
    vLIST_INDUCT_TAC ----> vREWRITE_TAC[normalize; vALL] ---->
    vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
    vSUBGOAL_THEN [%q {|normalize t = []|} ] (fun th -> vREWRITE_TAC[th]) ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
    vREWRITE_TAC[vLENGTH; vPRE]]);;

(* ------------------------------------------------------------------------- *)
(* Show that the degree is welldefined.                                      *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_CONS_EQ = prove
 ([%q {|(poly (CONS h1 t1) = poly (CONS h2 t2)) <=>
   (h1 = h2) /\ (poly t1 = poly t2)|} ],
  vREWRITE_TAC[vFUN_EQ_THM] ----> vEQ_TAC ++--> [vALL_TAC; vSIMP_TAC[poly]] ---->
  vONCE_REWRITE_TAC[vSIMPLE_COMPLEX_ARITH [%q {|(a = b) <=> (a + --b = Cx(&0))|} ]] ---->
  vREWRITE_TAC[vGSYM vPOLY_NEG; vGSYM vPOLY_ADD] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|poly (CONS h1 t1 ++ neg(CONS h2 t2)) = poly []|} ] vMP_TAC ++-->
   [vASM_REWRITE_TAC[poly; vFUN_EQ_THM]; vALL_TAC] ---->
  vREWRITE_TAC[poly_neg; poly_cmul; poly_add; vNOT_CONS_NIL; vHD; vTL] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vPOLY_ZERO_LEMMA) ---->
  vSIMP_TAC[poly; vCOMPLEX_MUL_LNEG; vCOMPLEX_MUL_LID]);;

let%a vPOLY_NORMALIZE_ZERO = prove
 ([%q {|!p. (poly p = poly []) <=> (normalize p = [])|} ],
  vREWRITE_TAC[vPOLY_ZERO] ---->
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vALL; normalize] ---->
  vASM_CASES_TAC [%q {|normalize t = []|} ] ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vNOT_CONS_NIL] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vNOT_CONS_NIL]);;

let%a vPOLY_NORMALIZE_EQ_LEMMA = prove
 ([%q {|!p q. (poly p = poly q) ==> (normalize p = normalize q)|} ],
  vLIST_INDUCT_TAC ++-->
   [vMESON_TAC[vPOLY_NORMALIZE_ZERO]; vALL_TAC] ---->
  vLIST_INDUCT_TAC ++-->
   [vMESON_TAC[vPOLY_NORMALIZE_ZERO]; vALL_TAC] ---->
  vREWRITE_TAC[vPOLY_CONS_EQ] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[normalize] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|t':complex list|} ]) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN vSUBST1_TAC ----> vREFL_TAC);;

let%a vPOLY_NORMALIZE_EQ = prove
 ([%q {|!p q. (poly p = poly q) <=> (normalize p = normalize q)|} ],
  vMESON_TAC[vPOLY_NORMALIZE_EQ_LEMMA; vPOLY_NORMALIZE]);;

let%a vDEGREE_WELLDEF = prove
 ([%q {|!p q. (poly p = poly q) ==> (degree p = degree q)|} ],
  vSIMP_TAC[degree; vPOLY_NORMALIZE_EQ]);;

(* ------------------------------------------------------------------------- *)
(* Degree of a product with a power of linear terms.                         *)
(* ------------------------------------------------------------------------- *)

let%a vNORMALIZE_EQ = prove
 ([%q {|!p. ~(LAST p = Cx(&0)) ==> (normalize p = p)|} ],
  vMATCH_MP_TAC list_INDUCT ----> vREWRITE_TAC[vNOT_CONS_NIL] ---->
  vREWRITE_TAC[normalize; vLAST] ----> vREPEAT vGEN_TAC ---->
  vREPEAT(vCOND_CASES_TAC ----> vASM_SIMP_TAC[normalize]));;

let%a vNORMAL_DEGREE = prove
 ([%q {|!p. ~(LAST p = Cx(&0)) ==> (degree p = LENGTH p - 1)|} ],
  vSIMP_TAC[degree; vNORMALIZE_EQ] ----> vREPEAT vSTRIP_TAC ----> vARITH_TAC);;

let%a vLAST_LINEAR_MUL_LEMMA = prove
 ([%q {|!p a b x.
     LAST(a ## p ++ CONS x (b ## p)) = if p = [] then x else b * LAST(p)|} ],
  vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[poly_cmul; poly_add; vLAST; vHD; vTL; vNOT_CONS_NIL] ---->
  vREPEAT vGEN_TAC ---->
  vSUBGOAL_THEN [%q {|~(a ## t ++ CONS (b * h) (b ## t) = [])|} ]
  vASSUME_TAC ++-->
   [vSPEC_TAC([%q {|t:complex list|} ],[%q {|t:complex list|} ]) ---->
    vLIST_INDUCT_TAC ----> vREWRITE_TAC[poly_cmul; poly_add; vNOT_CONS_NIL];
    vALL_TAC] ---->
  vASM_REWRITE_TAC[] ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[]);;

let%a vLAST_LINEAR_MUL = prove
 ([%q {|!p. ~(p = []) ==> (LAST([a; Cx(&1)] ** p) = LAST p)|} ],
  vSIMP_TAC[poly_mul; vNOT_CONS_NIL; vLAST_LINEAR_MUL_LEMMA; vCOMPLEX_MUL_LID]);;

let%a vNORMAL_NORMALIZE = prove
 ([%q {|!p. ~(normalize p = []) ==> ~(LAST(normalize p) = Cx(&0))|} ],
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[normalize] ---->
  vPOP_ASSUM vMP_TAC ----> vASM_CASES_TAC [%q {|normalize t = []|} ] ---->
  vASM_REWRITE_TAC[vLAST; vNOT_CONS_NIL] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vLAST]);;

let%a vLINEAR_MUL_DEGREE = prove
 ([%q {|!p a. ~(poly p = poly []) ==> (degree([a; Cx(&1)] ** p) = degree(p) + 1)|} ],
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|degree([a; Cx(&1)] ** normalize p) = degree(normalize p) + 1|} ]
  vMP_TAC ++-->
   [vFIRST_ASSUM(vASSUME_TAC -|
      vGEN_REWRITE_RULE vRAND_CONV [vPOLY_NORMALIZE_ZERO]) ---->
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vNORMAL_NORMALIZE) ---->
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vLAST_LINEAR_MUL) ---->
    vSIMP_TAC[vNORMAL_DEGREE] ----> vREPEAT vSTRIP_TAC ---->
    vSUBST1_TAC(vSYM(vSPEC [%q {|a:complex|} ] vCOMPLEX_NEG_NEG)) ---->
    vREWRITE_TAC[vPOLY_LENGTH_MUL] ---->
    vUNDISCH_TAC [%q {|~(normalize p = [])|} ] ---->
    vSPEC_TAC([%q {|normalize p|} ],[%q {|p:complex list|} ]) ---->
    vLIST_INDUCT_TAC ----> vREWRITE_TAC[vNOT_CONS_NIL; vLENGTH] ----> vARITH_TAC;
    vMATCH_MP_TAC vEQ_IMP ----> vBINOP_TAC ---->
    vTRY(vAP_THM_TAC ----> vAP_TERM_TAC) ----> vMATCH_MP_TAC vDEGREE_WELLDEF ---->
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; vPOLY_NORMALIZE]]);;

let%a vLINEAR_POW_MUL_DEGREE = prove
 ([%q {|!n a p. degree([a; Cx(&1)] exp n ** p) =
                if poly p = poly [] then 0 else degree p + n|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[poly_exp] ++-->
   [vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ++-->
     [vMATCH_MP_TAC vEQ_TRANS ----> vEXISTS_TAC [%q {|degree(p)|} ] ----> vCONJ_TAC ++-->
       [vMATCH_MP_TAC vDEGREE_WELLDEF ---->
        vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; poly; vCOMPLEX_MUL_RZERO;
                    vCOMPLEX_ADD_RID; vCOMPLEX_MUL_LID];
        vMATCH_MP_TAC vEQ_TRANS ----> vEXISTS_TAC [%q {|degree []|} ] ----> vCONJ_TAC ++-->
         [vMATCH_MP_TAC vDEGREE_WELLDEF ----> vASM_REWRITE_TAC[];
          vREWRITE_TAC[degree; vLENGTH; normalize; vARITH]]];
      vREWRITE_TAC[vADD_CLAUSES] ----> vMATCH_MP_TAC vDEGREE_WELLDEF ---->
      vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; poly; vCOMPLEX_MUL_RZERO;
                  vCOMPLEX_ADD_RID; vCOMPLEX_MUL_LID]];
    vALL_TAC] ---->
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC [%q {|degree([a; Cx (&1)] exp n ** ([a; Cx (&1)] ** p))|} ] ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vDEGREE_WELLDEF ---->
    vREWRITE_TAC[vFUN_EQ_THM; vPOLY_MUL; vCOMPLEX_MUL_AC]; vALL_TAC] ---->
  vASM_REWRITE_TAC[vPOLY_ENTIRE] ---->
  vASM_CASES_TAC [%q {|poly p = poly []|} ] ----> vASM_REWRITE_TAC[] ---->
  vASM_SIMP_TAC[vLINEAR_MUL_DEGREE] ---->
  vSUBGOAL_THEN [%q {|~(poly [a; Cx (&1)] = poly [])|} ]
   (fun th -> vREWRITE_TAC[th] ----> vARITH_TAC) ---->
  vREWRITE_TAC[vPOLY_NORMALIZE_EQ] ---->
  vREWRITE_TAC[normalize; vCX_INJ; vREAL_OF_NUM_EQ; vARITH; vNOT_CONS_NIL]);;

(* ------------------------------------------------------------------------- *)
(* Show that the order of a root (or nonroot!) is bounded by degree.         *)
(* ------------------------------------------------------------------------- *)

let%a vORDER_DEGREE = prove
 ([%q {|!a p. ~(poly p = poly []) ==> order a p <= degree p|} ],
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|a:complex|} ] -| vMATCH_MP vORDER_THM) ---->
  vDISCH_THEN(vMP_TAC -| vREWRITE_RULE[divides] -| vCONJUNCT1) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|q:complex list|} ] vASSUME_TAC) ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vMATCH_MP vDEGREE_WELLDEF) ---->
  vASM_REWRITE_TAC[vLINEAR_POW_MUL_DEGREE] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vFUN_EQ_THM]) ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vPOLY_MUL] ++-->
   [vUNDISCH_TAC [%q {|~(poly p = poly [])|} ] ---->
    vSIMP_TAC[vFUN_EQ_THM; vPOLY_MUL; poly; vCOMPLEX_MUL_RZERO];
    vDISCH_TAC ----> vARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Tidier versions of finiteness of roots.                                   *)
(* ------------------------------------------------------------------------- *)

let%a vPOLY_ROOTS_FINITE_SET = prove
 ([%q {|!p. ~(poly p = poly []) ==> FINITE { x | poly p x = Cx(&0)}|} ],
  vGEN_TAC ----> vREWRITE_TAC[vPOLY_ROOTS_FINITE] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:num|} ] vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|i:num->complex|} ] vASSUME_TAC) ---->
  vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC [%q {|{x:complex | ?n:num. n < N /\ (x = i n)}|} ] ---->
  vCONJ_TAC ++-->
   [vSPEC_TAC([%q {|N:num|} ],[%q {|N:num|} ]) ----> vPOP_ASSUM_LIST(vK vALL_TAC) ---->
    vINDUCT_TAC ++-->
     [vSUBGOAL_THEN [%q {|{x:complex | ?n. n < 0 /\ (x = i n)} = {}|} ]
      (fun th -> vREWRITE_TAC[th; vFINITE_RULES]) ---->
      vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vNOT_IN_EMPTY; vLT];
      vSUBGOAL_THEN [%q {|{x:complex | ?n. n < SUC N /\ (x = i n)} =
                    (i N) INSERT {x:complex | ?n. n < N /\ (x = i n)}|} ]
      vSUBST1_TAC ++-->
       [vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vIN_INSERT; vLT] ----> vMESON_TAC[];
        vMATCH_MP_TAC(vCONJUNCT2 vFINITE_RULES) ----> vASM_REWRITE_TAC[]]];
    vASM_REWRITE_TAC[vSUBSET; vIN_ELIM_THM]]);;

(* ------------------------------------------------------------------------- *)
(* Conversions to perform operations if coefficients are rational constants. *)
(* ------------------------------------------------------------------------- *)

let vCOMPLEX_RAT_MUL_CONV =
  vGEN_REWRITE_CONV vI [vGSYM vCX_MUL] +---> vRAND_CONV vREAL_RAT_MUL_CONV;;

let vCOMPLEX_RAT_ADD_CONV =
  vGEN_REWRITE_CONV vI [vGSYM vCX_ADD] +---> vRAND_CONV vREAL_RAT_ADD_CONV;;

let vCOMPLEX_RAT_EQ_CONV =
  vGEN_REWRITE_CONV vI [vCX_INJ] +---> vREAL_RAT_EQ_CONV;;

let vPOLY_CMUL_CONV =
  let cmul_conv0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 poly_cmul]
  and cmul_conv1 = vGEN_REWRITE_CONV vI [vCONJUNCT2 poly_cmul] in
  let rec vPOLY_CMUL_CONV tm =
   (cmul_conv0 ||-->
    (cmul_conv1 +--->
     vLAND_CONV vCOMPLEX_RAT_MUL_CONV +--->
     vRAND_CONV vPOLY_CMUL_CONV)) tm in
  vPOLY_CMUL_CONV;;

let vPOLY_ADD_CONV =
  let add_conv0 = vGEN_REWRITE_CONV vI (butlast (vCONJUNCTS vPOLY_ADD_CLAUSES))
  and add_conv1 = vGEN_REWRITE_CONV vI [last (vCONJUNCTS vPOLY_ADD_CLAUSES)] in
  let rec vPOLY_ADD_CONV tm =
   (add_conv0 ||-->
    (add_conv1 +--->
     vLAND_CONV vCOMPLEX_RAT_ADD_CONV +--->
     vRAND_CONV vPOLY_ADD_CONV)) tm in
  vPOLY_ADD_CONV;;

let vPOLY_MUL_CONV =
  let mul_conv0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 vPOLY_MUL_CLAUSES]
  and mul_conv1 = vGEN_REWRITE_CONV vI [vCONJUNCT1(vCONJUNCT2 vPOLY_MUL_CLAUSES)]
  and mul_conv2 = vGEN_REWRITE_CONV vI [vCONJUNCT2(vCONJUNCT2 vPOLY_MUL_CLAUSES)] in
  let rec vPOLY_MUL_CONV tm =
   (mul_conv0 ||-->
    (mul_conv1 +---> vPOLY_CMUL_CONV) ||-->
    (mul_conv2 +--->
     vLAND_CONV vPOLY_CMUL_CONV +--->
     vRAND_CONV(vRAND_CONV vPOLY_MUL_CONV) +--->
     vPOLY_ADD_CONV)) tm in
  vPOLY_MUL_CONV;;

let vPOLY_NORMALIZE_CONV =
  let pth = prove
   ([%q {|normalize (CONS h t) =
      (\n. if n = [] then if h = Cx(&0) then [] else [h] else CONS h n)
      (normalize t)|} ],
    vREWRITE_TAC[normalize]) in
  let norm_conv0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 normalize]
  and norm_conv1 = vGEN_REWRITE_CONV vI [pth]
  and norm_conv2 = vGEN_REWRITE_CONV vDEPTH_CONV
   [vCOND_CLAUSES; vNOT_CONS_NIL; vEQT_INTRO(vSPEC_ALL vEQ_REFL)] in
  let rec vPOLY_NORMALIZE_CONV tm =
   (norm_conv0 ||-->
    (norm_conv1 +--->
     vRAND_CONV vPOLY_NORMALIZE_CONV +--->
     vBETA_CONV +--->
     vRATOR_CONV(vRAND_CONV(vRATOR_CONV(vLAND_CONV vCOMPLEX_RAT_EQ_CONV))) +--->
     norm_conv2)) tm in
  vPOLY_NORMALIZE_CONV;;

(* ------------------------------------------------------------------------- *)
(* Now we're finished with polynomials...                                    *)
(* ------------------------------------------------------------------------- *)

(************** keep this for now

do_list reduce_interface
 ["divides",`poly_divides:complex list->complex list->bool`;
  "exp",`poly_exp:complex list -> num -> complex list`;
  "diff",`poly_diff:complex list->complex list`];;

unparse_as_infix "exp";;

 ****************)
