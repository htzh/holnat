[@@@warning "-33-27-8"]
open Hol.All
open Hol.Accept
;;
(* ========================================================================= *)
(* The integer/rational-valued reals, and the "floor" and "frac" functions.  *)
(* ========================================================================= *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Closure theorems and other lemmas for the integer-valued reals.           *)
(* ------------------------------------------------------------------------- *)

let%a vINTEGER_CASES = prove
 ([%q {|integer x <=> (?n. x = &n) \/ (?n. x = -- &n)|} ],
  vREWRITE_TAC[is_int; vOR_EXISTS_THM]);;

let%a vREAL_ABS_INTEGER_LEMMA = prove
 ([%q {|!x. integer(x) /\ ~(x = &0) ==> &1 <= abs(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[integer] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vONCE_REWRITE_TAC[vREAL_ARITH [%q {|(x = &0) <=> (abs(x) = &0)|} ]] ---->
  vPOP_ASSUM(vCHOOSE_THEN vSUBST1_TAC) ---->
  vREWRITE_TAC[vREAL_OF_NUM_EQ; vREAL_OF_NUM_LE] ----> vARITH_TAC);;

let%a vINTEGER_CLOSED = prove
 ([%q {|(!n. integer(&n)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(x + y)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(x - y)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(x * y)) /\
   (!x r. integer(x) ==> integer(x pow r)) /\
   (!x. integer(x) ==> integer(--x)) /\
   (!x. integer(x) ==> integer(abs x)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(max x y)) /\
   (!x y. integer(x) /\ integer(y) ==> integer(min x y))|} ],
  vREWRITE_TAC[integer] ---->
  vMATCH_MP_TAC(vTAUT
   [%q {|g /\ h /\ x /\ c /\ d /\ e /\ f /\ (a /\ e ==> b) /\ a
    ==> x /\ a /\ b /\ c /\ d /\ e /\ f /\ g /\ h|} ]) ---->
  vREPEAT vCONJ_TAC ++-->
   [vREWRITE_TAC[real_max] ----> vMESON_TAC[];
    vREWRITE_TAC[real_min] ----> vMESON_TAC[];
    vREWRITE_TAC[vREAL_ABS_NUM] ----> vMESON_TAC[];
    vREWRITE_TAC[vREAL_ABS_MUL] ----> vMESON_TAC[vREAL_OF_NUM_MUL];
    vREWRITE_TAC[vREAL_ABS_POW] ----> vMESON_TAC[vREAL_OF_NUM_POW];
    vREWRITE_TAC[vREAL_ABS_NEG]; vREWRITE_TAC[vREAL_ABS_ABS];
    vREWRITE_TAC[real_sub] ----> vMESON_TAC[]; vALL_TAC] ---->
  vSIMP_TAC[vREAL_ARITH [%q {|&0 <= a ==> ((abs(x) = a) <=> (x = a) \/ (x = --a))|} ];
           vREAL_POS] ---->
  vREPEAT vSTRIP_TAC ---->
  vASM_REWRITE_TAC[vGSYM vREAL_NEG_ADD; vREAL_OF_NUM_ADD] ++-->
   [vMESON_TAC[]; vALL_TAC; vALL_TAC; vMESON_TAC[]] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|(--a + b = c) <=> (a + c = b)|} ];
              vREAL_ARITH [%q {|(a + --b = c) <=> (b + c = a)|} ]] ---->
  vREWRITE_TAC[vREAL_OF_NUM_ADD; vREAL_OF_NUM_EQ] ---->
  vMESON_TAC[vLE_EXISTS; vADD_SYM; vLE_CASES]);;

let%a vINTEGER_ADD = prove
 ([%q {|!x y. integer(x) /\ integer(y) ==> integer(x + y)|} ],
  vREWRITE_TAC[vINTEGER_CLOSED]);;

let%a vINTEGER_SUB = prove
 ([%q {|!x y. integer(x) /\ integer(y) ==> integer(x - y)|} ],
  vREWRITE_TAC[vINTEGER_CLOSED]);;

let%a vINTEGER_MUL = prove
 ([%q {|!x y. integer(x) /\ integer(y) ==> integer(x * y)|} ],
  vREWRITE_TAC[vINTEGER_CLOSED]);;

let%a vINTEGER_POW = prove
 ([%q {|!x n. integer(x) ==> integer(x pow n)|} ],
  vREWRITE_TAC[vINTEGER_CLOSED]);;

let%a vREAL_LE_INTEGERS = prove
 ([%q {|!x y. integer(x) /\ integer(y) ==> (x <= y <=> (x = y) \/ x + &1 <= y)|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|y - x|} ] vREAL_ABS_INTEGER_LEMMA) ---->
  vASM_SIMP_TAC[vINTEGER_CLOSED] ----> vREAL_ARITH_TAC);;

let%a vREAL_LE_CASES_INTEGERS = prove
 ([%q {|!x y. integer(x) /\ integer(y) ==> x <= y \/ y + &1 <= x|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|y - x|} ] vREAL_ABS_INTEGER_LEMMA) ---->
  vASM_SIMP_TAC[vINTEGER_CLOSED] ----> vREAL_ARITH_TAC);;

let%a vREAL_LE_REVERSE_INTEGERS = prove
 ([%q {|!x y. integer(x) /\ integer(y) /\ ~(y + &1 <= x) ==> x <= y|} ],
  vMESON_TAC[vREAL_LE_CASES_INTEGERS]);;

let%a vREAL_LT_INTEGERS = prove
 ([%q {|!x y. integer(x) /\ integer(y) ==> (x < y <=> x + &1 <= y)|} ],
  vMESON_TAC[vREAL_NOT_LT; vREAL_LE_CASES_INTEGERS;
            vREAL_ARITH [%q {|x + &1 <= y ==> x < y|} ]]);;

let%a vREAL_EQ_INTEGERS = prove
 ([%q {|!x y. integer x /\ integer y ==> (x = y <=> abs(x - y) < &1)|} ],
  vREWRITE_TAC[vREAL_ARITH [%q {|x = y <=> ~(x < y \/ y < x)|} ]] ---->
  vSIMP_TAC[vREAL_LT_INTEGERS] ----> vREAL_ARITH_TAC);;

let%a vREAL_EQ_INTEGERS_IMP = prove
 ([%q {|!x y. integer x /\ integer y /\ abs(x - y) < &1 ==> x = y|} ],
  vSIMP_TAC[vREAL_EQ_INTEGERS]);;

let%a vINTEGER_NEG = prove
 ([%q {|!x. integer(--x) <=> integer(x)|} ],
  vMESON_TAC[vINTEGER_CLOSED; vREAL_NEG_NEG]);;

let%a vINTEGER_ABS = prove
 ([%q {|!x. integer(abs x) <=> integer(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_abs] ----> vCOND_CASES_TAC ---->
  vREWRITE_TAC[vINTEGER_NEG]);;

let%a vINTEGER_POS = prove
 ([%q {|!x. &0 <= x ==> (integer(x) <=> ?n. x = &n)|} ],
  vSIMP_TAC[integer; real_abs]);;

let%a vNONNEGATIVE_INTEGER = prove
 ([%q {|!x. integer x /\ &0 <= x <=> ?n. x = &n|} ],
  vMESON_TAC[vINTEGER_POS; vINTEGER_CLOSED; vREAL_POS]);;

let%a vNONPOSITIVE_INTEGER = prove
 ([%q {|!x. integer x /\ x <= &0 <=> ?n. x = -- &n|} ],
  vGEN_TAC ----> vREWRITE_TAC[is_int] ---->
  vREWRITE_TAC[vLEFT_AND_EXISTS_THM; vREAL_ARITH [%q {|a + b = &0 <=> a = --b|} ]] ---->
  vAP_TERM_TAC ----> vABS_TAC ----> vREAL_ARITH_TAC);;

let%a vNONPOSITIVE_INTEGER_ALT = prove
 ([%q {|!x. integer x /\ x <= &0 <=> ?n. x + &n = &0|} ],
  vGEN_TAC ----> vREWRITE_TAC[vNONPOSITIVE_INTEGER] ---->
  vAP_TERM_TAC ----> vABS_TAC ----> vREAL_ARITH_TAC);;

let%a vINTEGER_ADD_EQ = prove
 ([%q {|(!x y. integer(x) ==> (integer(x + y) <=> integer(y))) /\
   (!x y. integer(y) ==> (integer(x + y) <=> integer(x)))|} ],
  vMESON_TAC[vREAL_ADD_SUB; vREAL_ADD_SYM; vINTEGER_CLOSED]);;

let%a vINTEGER_SUB_EQ = prove
 ([%q {|(!x y. integer(x) ==> (integer(x - y) <=> integer(y))) /\
   (!x y. integer(y) ==> (integer(x - y) <=> integer(x)))|} ],
  vMESON_TAC[vREAL_SUB_ADD; vREAL_NEG_SUB; vINTEGER_CLOSED]);;

let%a vFORALL_INTEGER = prove
 ([%q {|!P. (!n. P(&n)) /\ (!x. P x ==> P(--x)) ==> !x. integer x ==> P x|} ],
  vMESON_TAC[vINTEGER_CASES]);;

let%a vINTEGER_SUM = prove
 ([%q {|!f:A->real s. (!x. x IN s ==> integer(f x)) ==> integer(sum s f)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_CLOSED ---->
  vASM_REWRITE_TAC[vINTEGER_CLOSED]);;

let%a vINTEGER_ABS_MUL_EQ_1 = prove
 ([%q {|!x y. integer x /\ integer y
         ==> (abs(x * y) = &1 <=> abs x = &1 /\ abs y = &1)|} ],
  vREWRITE_TAC[integer] ---->
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[vREAL_ABS_MUL] ---->
  vREWRITE_TAC[vREAL_OF_NUM_EQ; vREAL_OF_NUM_MUL; vMULT_EQ_1]);;

let%a vINTEGER_DIV = prove
 ([%q {|!m n. integer(&m / &n) <=> n = 0 \/ n divides m|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|n = 0|} ] ++-->
   [vASM_REWRITE_TAC[real_div; vREAL_INV_0; vREAL_MUL_RZERO; vINTEGER_CLOSED];
    vASM_SIMP_TAC[vINTEGER_POS; vREAL_POS; vREAL_LE_DIV; divides] ---->
    vASM_SIMP_TAC[vREAL_OF_NUM_EQ; vREAL_FIELD
     [%q {|~(n = &0) ==> (x / n = y <=> x = n * y)|} ]] ---->
    vREWRITE_TAC[vREAL_OF_NUM_MUL; vREAL_OF_NUM_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Similar theorems for rational-valued reals.                               *)
(* ------------------------------------------------------------------------- *)

let rational = new_definition
 [%q {|rational x <=> ?m n. integer m /\ integer n /\ ~(n = &0) /\ x = m / n|} ];;

let%a vRATIONAL_INTEGER = prove
 ([%q {|!x. integer x ==> rational x|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[rational] ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|x:real|} ]; [%q {|&1|} ]] ---->
  vASM_SIMP_TAC[vINTEGER_CLOSED] ----> vCONV_TAC vREAL_FIELD);;

let%a vRATIONAL_NUM = prove
 ([%q {|!n. rational(&n)|} ],
  vSIMP_TAC[vRATIONAL_INTEGER; vINTEGER_CLOSED]);;

let%a vRATIONAL_NEG = prove
 ([%q {|!x. rational(x) ==> rational(--x)|} ],
  vREWRITE_TAC[rational; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|x:real|} ]; [%q {|m:real|} ]; [%q {|n:real|} ]] ---->
  vSTRIP_TAC ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|--m:real|} ]; [%q {|n:real|} ]] ---->
  vASM_SIMP_TAC[vINTEGER_CLOSED] ----> vCONV_TAC vREAL_FIELD);;

let%a vRATIONAL_ABS = prove
 ([%q {|!x. rational(x) ==> rational(abs x)|} ],
  vREWRITE_TAC[real_abs] ----> vMESON_TAC[vRATIONAL_NEG]);;

let%a vRATIONAL_INV = prove
 ([%q {|!x. rational(x) ==> rational(inv x)|} ],
  vGEN_TAC ----> vASM_CASES_TAC [%q {|x = &0|} ] ---->
  vASM_SIMP_TAC[vREAL_INV_0; vRATIONAL_NUM] ---->
  vREWRITE_TAC[rational; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|m:real|} ]; [%q {|n:real|} ]] ----> vSTRIP_TAC ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|n:real|} ]; [%q {|m:real|} ]] ---->
  vASM_SIMP_TAC[vINTEGER_CLOSED] ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ----> vCONV_TAC vREAL_FIELD);;

let%a vRATIONAL_ADD = prove
 ([%q {|!x y. rational(x) /\ rational(y) ==> rational(x + y)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[rational; vLEFT_AND_EXISTS_THM] ---->
  vREWRITE_TAC[vRIGHT_AND_EXISTS_THM; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|m1:real|} ]; [%q {|n1:real|} ]; [%q {|m2:real|} ]; [%q {|n2:real|} ]] ---->
  vSTRIP_TAC ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|m1 * n2 + m2 * n1:real|} ]; [%q {|n1 * n2:real|} ]] ---->
  vASM_SIMP_TAC[vINTEGER_CLOSED] ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ----> vCONV_TAC vREAL_FIELD);;

let%a vRATIONAL_SUB = prove
 ([%q {|!x y. rational(x) /\ rational(y) ==> rational(x - y)|} ],
  vSIMP_TAC[real_sub; vRATIONAL_NEG; vRATIONAL_ADD]);;

let%a vRATIONAL_MUL = prove
 ([%q {|!x y. rational(x) /\ rational(y) ==> rational(x * y)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[rational; vLEFT_AND_EXISTS_THM] ---->
  vREWRITE_TAC[vRIGHT_AND_EXISTS_THM; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|m1:real|} ]; [%q {|n1:real|} ]; [%q {|m2:real|} ]; [%q {|n2:real|} ]] ---->
  vSTRIP_TAC ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|m1 * m2:real|} ]; [%q {|n1 * n2:real|} ]] ---->
  vASM_SIMP_TAC[vINTEGER_CLOSED] ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ----> vCONV_TAC vREAL_FIELD);;

let%a vRATIONAL_DIV = prove
 ([%q {|!x y. rational(x) /\ rational(y) ==> rational(x / y)|} ],
  vSIMP_TAC[real_div; vRATIONAL_INV; vRATIONAL_MUL]);;

let%a vRATIONAL_POW = prove
 ([%q {|!x n. rational(x) ==> rational(x pow n)|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_SIMP_TAC[real_pow; vRATIONAL_NUM; vRATIONAL_MUL]);;

let%a vRATIONAL_CLOSED = prove
 ([%q {|(!n. rational(&n)) /\
   (!x. integer x ==> rational x) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x + y)) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x - y)) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x * y)) /\
   (!x y. rational(x) /\ rational(y) ==> rational(x / y)) /\
   (!x r. rational(x) ==> rational(x pow r)) /\
   (!x. rational(x) ==> rational(--x)) /\
   (!x. rational(x) ==> rational(inv x)) /\
   (!x. rational(x) ==> rational(abs x))|} ],
  vSIMP_TAC[vRATIONAL_NUM; vRATIONAL_NEG; vRATIONAL_ABS; vRATIONAL_INV;
           vRATIONAL_ADD; vRATIONAL_SUB; vRATIONAL_MUL; vRATIONAL_DIV;
           vRATIONAL_POW; vRATIONAL_INTEGER]);;

let%a vRATIONAL_NEG_EQ = prove
 ([%q {|!x. rational(--x) <=> rational x|} ],
  vMESON_TAC[vREAL_NEG_NEG; vRATIONAL_NEG]);;

let%a vRATIONAL_ABS_EQ = prove
 ([%q {|!x. rational(abs x) <=> rational x|} ],
  vREWRITE_TAC[real_abs] ----> vMESON_TAC[vRATIONAL_NEG_EQ; vRATIONAL_NUM]);;

let%a vRATIONAL_INV_EQ = prove
 ([%q {|!x. rational(inv x) <=> rational x|} ],
  vMESON_TAC[vREAL_INV_INV; vRATIONAL_INV]);;

let%a vRATIONAL_SUM = prove
 ([%q {|!s x. (!i. i IN s ==> rational(x i)) ==> rational(sum s x)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_CLOSED ---->
  vASM_SIMP_TAC[vRATIONAL_CLOSED]);;

let%a vRATIONAL_ALT = prove
 ([%q {|!x. rational(x) <=> ?p q. ~(q = 0) /\ abs x = &p / &q|} ],
  vGEN_TAC ----> vREWRITE_TAC[rational] ----> vEQ_TAC ++-->
   [vREWRITE_TAC[integer] ----> vSTRIP_TAC ----> vASM_REWRITE_TAC[vREAL_ABS_DIV] ---->
    vASM_MESON_TAC[vREAL_OF_NUM_EQ; vREAL_ABS_ZERO];
    vSTRIP_TAC ----> vFIRST_X_ASSUM(vDISJ_CASES_THEN vSUBST1_TAC -| vMATCH_MP
     (vREAL_ARITH [%q {|abs(x:real) = a ==> x = a \/ x = --a|} ])) ---->
    vASM_REWRITE_TAC[real_div; vGSYM vREAL_MUL_LNEG] ---->
    vREWRITE_TAC[vGSYM real_div] ---->
    vASM_MESON_TAC[vINTEGER_CLOSED; vREAL_OF_NUM_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* The floor and frac functions.                                             *)
(* ------------------------------------------------------------------------- *)

let%a vREAL_TRUNCATE_POS = prove
 ([%q {|!x. &0 <= x ==> ?n r. &0 <= r /\ r < &1 /\ (x = &n + r)|} ],
  vREPEAT vSTRIP_TAC ----> vMP_TAC(vSPEC [%q {|x:real|} ] vREAL_ARCH_SIMPLE) ---->
  vGEN_REWRITE_TAC vLAND_CONV [num_WOP] ---->
  vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vLT_SUC_LE; vCONJUNCT1 vLT] ++-->
   [vDISCH_TAC ----> vMAP_EVERY vEXISTS_TAC [[%q {|0|} ]; [%q {|&0|} ]] ----> vASM_REAL_ARITH_TAC;
    vPOP_ASSUM_LIST(vK vALL_TAC)] ---->
  vREWRITE_TAC[vGSYM vREAL_OF_NUM_SUC] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vMP_TAC -| vSPEC [%q {|n:num|} ])) ---->
  vREWRITE_TAC[vLE_REFL; vREAL_NOT_LE] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vDISJ_CASES_THEN vSTRIP_ASSUME_TAC -| vREWRITE_RULE[vREAL_LE_LT])
  ++-->
   [vMAP_EVERY vEXISTS_TAC [[%q {|n:num|} ]; [%q {|x - &n|} ]] ----> vASM_REAL_ARITH_TAC;
    vMAP_EVERY vEXISTS_TAC [[%q {|SUC n|} ]; [%q {|x - &(SUC n)|} ]] ---->
    vREWRITE_TAC[vREAL_ADD_SUB; vGSYM vREAL_OF_NUM_SUC] ----> vASM_REAL_ARITH_TAC]);;

let%a vREAL_TRUNCATE = prove
 ([%q {|!x. ?n r. integer(n) /\ &0 <= r /\ r < &1 /\ (x = n + r)|} ],
  vGEN_TAC ----> vDISJ_CASES_TAC(vSPECL [[%q {|x:real|} ]; [%q {|&0|} ]] vREAL_LE_TOTAL) ++-->
   [vMP_TAC(vSPEC [%q {|--x|} ] vREAL_ARCH_SIMPLE) ---->
    vREWRITE_TAC[vREAL_ARITH [%q {|--a <= b <=> &0 <= a + b|} ]] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:num|} ]
     (vMP_TAC -| vMATCH_MP vREAL_TRUNCATE_POS)) ---->
    vREWRITE_TAC[vREAL_ARITH [%q {|(a + b = c + d) <=> (a = (c - b) + d)|} ]];
    vALL_TAC] ---->
  vASM_MESON_TAC[integer; vINTEGER_CLOSED; vREAL_TRUNCATE_POS]);;

let vFLOOR_FRAC =
    new_specification ["floor"; "frac"]
       (vREWRITE_RULE[vSKOLEM_THM] vREAL_TRUNCATE);;

(* ------------------------------------------------------------------------- *)
(* Useful lemmas about floor and frac.                                       *)
(* ------------------------------------------------------------------------- *)

let%a vFLOOR_UNIQUE = prove
 ([%q {|!x a. integer(a) /\ a <= x /\ x < a + &1 <=> (floor x = a)|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vSTRIP_TAC ----> vSTRIP_ASSUME_TAC(vSPEC [%q {|x:real|} ] vFLOOR_FRAC) ---->
    vSUBGOAL_THEN [%q {|abs(floor x - a) < &1|} ] vMP_TAC ++-->
     [vASM_REAL_ARITH_TAC; vALL_TAC] ---->
    vONCE_REWRITE_TAC[vGSYM vCONTRAPOS_THM] ---->
    vDISCH_TAC ----> vREWRITE_TAC[vREAL_NOT_LT] ---->
    vMATCH_MP_TAC vREAL_ABS_INTEGER_LEMMA ----> vCONJ_TAC ++-->
     [vASM_MESON_TAC[vINTEGER_CLOSED]; vASM_REAL_ARITH_TAC];
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
    vMP_TAC(vSPEC [%q {|x:real|} ] vFLOOR_FRAC) ---->
    vSIMP_TAC[] ----> vREAL_ARITH_TAC]);;

let%a vFLOOR_EQ_0 = prove
 ([%q {|!x. (floor x = &0) <=> &0 <= x /\ x < &1|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vFLOOR_UNIQUE] ---->
  vREWRITE_TAC[vINTEGER_CLOSED; vREAL_ADD_LID]);;

let%a vFLOOR = prove
 ([%q {|!x. integer(floor x) /\ floor(x) <= x /\ x < floor(x) + &1|} ],
  vGEN_TAC ----> vMP_TAC(vSPEC [%q {|x:real|} ] vFLOOR_FRAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vASM_REWRITE_TAC[] ----> vREAL_ARITH_TAC);;

let%a vFLOOR_DOUBLE = prove
 ([%q {|!u. &2 * floor(u) <= floor(&2 * u) /\ floor(&2 * u) <= &2 * floor(u) + &1|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_REVERSE_INTEGERS ---->
  vSIMP_TAC[vINTEGER_CLOSED; vFLOOR] ---->
  vMP_TAC(vSPEC [%q {|u:real|} ] vFLOOR) ----> vMP_TAC(vSPEC [%q {|&2 * u|} ] vFLOOR) ---->
  vREAL_ARITH_TAC);;

let%a vFRAC_FLOOR = prove
 ([%q {|!x. frac(x) = x - floor(x)|} ],
  vMP_TAC vFLOOR_FRAC ----> vMATCH_MP_TAC vMONO_FORALL ----> vREAL_ARITH_TAC);;

let%a vFLOOR_NUM = prove
 ([%q {|!n. floor(&n) = &n|} ],
  vREWRITE_TAC[vGSYM vFLOOR_UNIQUE; vINTEGER_CLOSED] ----> vREAL_ARITH_TAC);;

let%a vREAL_LE_FLOOR = prove
 ([%q {|!x n. integer(n) ==> (n <= floor x <=> n <= x)|} ],
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ++-->
   [vASM_MESON_TAC[vFLOOR; vREAL_LE_TRANS]; vALL_TAC] ---->
  vREWRITE_TAC[vGSYM vREAL_NOT_LT] ----> vASM_SIMP_TAC[vREAL_LT_INTEGERS; vFLOOR] ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vFLOOR) ----> vREAL_ARITH_TAC);;

let%a vREAL_FLOOR_LE = prove
 ([%q {|!x n. integer n ==> (floor x <= n <=> x - &1 < n)|} ],
  vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vREAL_ARITH [%q {|x <= y <=> x + &1 <= y + &1|} ]] ---->
  vASM_SIMP_TAC[vGSYM vREAL_LT_INTEGERS; vFLOOR; vINTEGER_CLOSED] ---->
  vONCE_REWRITE_TAC[vTAUT [%q {|(p <=> q) <=> (~p <=> ~q)|} ]] ---->
  vASM_SIMP_TAC[vREAL_NOT_LT; vREAL_LE_FLOOR; vINTEGER_CLOSED] ---->
  vREAL_ARITH_TAC);;

let%a vREAL_FLOOR_LT = prove
 ([%q {|!x n. integer n ==> (floor x < n <=> x < n)|} ],
  vSIMP_TAC[vGSYM vREAL_NOT_LE; vREAL_LE_FLOOR]);;

let%a vREAL_LT_FLOOR = prove
 ([%q {|!x n. integer n ==> (n < floor x <=> n <= x - &1)|} ],
  vSIMP_TAC[vGSYM vREAL_NOT_LE; vREAL_FLOOR_LE]);;

let%a vFLOOR_POS = prove
 ([%q {|!x. &0 <= x ==> ?n. floor(x) = &n|} ],
  vREPEAT vSTRIP_TAC ----> vMP_TAC(vCONJUNCT1(vSPEC [%q {|x:real|} ] vFLOOR)) ---->
  vREWRITE_TAC[integer] ---->
  vASM_SIMP_TAC[real_abs; vREAL_LE_FLOOR; vFLOOR; vINTEGER_CLOSED]);;

let%a vFLOOR_DIV_DIV = prove
 ([%q {|!m n. ~(m = 0) ==> floor(&n / &m) = &(n DIV m)|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vFLOOR_UNIQUE; vINTEGER_CLOSED] ---->
  vASM_SIMP_TAC[vREAL_LE_RDIV_EQ; vREAL_LT_LDIV_EQ; vREAL_OF_NUM_LT;
               vREAL_OF_NUM_LE; vREAL_OF_NUM_MUL; vREAL_OF_NUM_ADD; vLT_NZ] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|n:num|} ] -| vMATCH_MP vDIVISION) ----> vARITH_TAC);;

let%a vFLOOR_MONO = prove
 ([%q {|!x y. x <= y ==> floor x <= floor y|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_NOT_LT] ---->
  vSIMP_TAC[vFLOOR; vREAL_LT_INTEGERS] ---->
  vMAP_EVERY (vMP_TAC -| vC vSPEC vFLOOR) [[%q {|x:real|} ]; [%q {|y:real|} ]] ----> vREAL_ARITH_TAC);;

let%a vREAL_FLOOR_EQ = prove
 ([%q {|!x. floor x = x <=> integer x|} ],
  vREWRITE_TAC[vGSYM vFLOOR_UNIQUE; vREAL_LE_REFL; vREAL_ARITH [%q {|x < x + &1|} ]]);;

let%a vREAL_FLOOR_LT_REFL = prove
 ([%q {|!x. floor x < x <=> ~(integer x)|} ],
  vMESON_TAC[vREAL_LT_LE; vREAL_FLOOR_EQ; vFLOOR]);;

let%a vREAL_FRAC_EQ_0 = prove
 ([%q {|!x. frac x = &0 <=> integer x|} ],
  vREWRITE_TAC[vFRAC_FLOOR; vREAL_SUB_0] ----> vMESON_TAC[vREAL_FLOOR_EQ]);;

let%a vREAL_FRAC_POS_LT = prove
 ([%q {|!x. &0 < frac x <=> ~(integer x)|} ],
  vREWRITE_TAC[vFRAC_FLOOR; vREAL_SUB_LT; vREAL_FLOOR_LT_REFL]);;

let%a vFRAC_NUM = prove
 ([%q {|!n. frac(&n) = &0|} ],
  vREWRITE_TAC[vREAL_FRAC_EQ_0; vINTEGER_CLOSED]);;

let%a vREAL_FLOOR_REFL = prove
 ([%q {|!x. integer x ==> floor x = x|} ],
  vREWRITE_TAC[vREAL_FLOOR_EQ]);;

let%a vREAL_FRAC_ZERO = prove
 ([%q {|!x. integer x ==> frac x = &0|} ],
  vREWRITE_TAC[vREAL_FRAC_EQ_0]);;

let%a vREAL_FLOOR_ADD = prove
 ([%q {|!x y. floor(x + y) = if frac x + frac y < &1 then floor(x) + floor(y)
                        else (floor(x) + floor(y)) + &1|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vFLOOR_UNIQUE] ---->
  vCONJ_TAC ++--> [vASM_MESON_TAC[vINTEGER_CLOSED; vFLOOR]; vALL_TAC] ---->
  vMAP_EVERY (vMP_TAC -| vC vSPEC vFLOOR_FRAC)[[%q {|x:real|} ]; [%q {|y:real|} ]; [%q {|x + y:real|} ]] ---->
  vREAL_ARITH_TAC);;

let%a vREAL_FLOOR_TRIANGLE = prove
 ([%q {|!x y. floor(x) + floor(y) <= floor(x + y) /\
         floor(x + y) <= (floor x + floor y) + &1|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_FLOOR_ADD] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ----> vREAL_ARITH_TAC);;

let%a vREAL_FLOOR_NEG = prove
 ([%q {|!x. floor(--x) = if integer x then --x else --(floor x + &1)|} ],
  vGEN_TAC ----> vCOND_CASES_TAC ----> vREWRITE_TAC[vGSYM vFLOOR_UNIQUE] ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vFLOOR) ---->
  vMP_TAC(vSPEC [%q {|x:real|} ] vREAL_FLOOR_EQ) ---->
  vASM_SIMP_TAC[vINTEGER_CLOSED] ----> vREAL_ARITH_TAC);;

let%a vREAL_FRAC_ADD = prove
 ([%q {|!x y. frac(x + y) = if frac x + frac y < &1 then frac(x) + frac(y)
                       else (frac(x) + frac(y)) - &1|} ],
  vREWRITE_TAC[vFRAC_FLOOR; vREAL_FLOOR_ADD] ----> vREAL_ARITH_TAC);;

let%a vFLOOR_POS_LE = prove
 ([%q {|!x. &0 <= floor x <=> &0 <= x|} ],
  vSIMP_TAC[vREAL_LE_FLOOR; vINTEGER_CLOSED]);;

let%a vFRAC_UNIQUE = prove
 ([%q {|!x a. integer(x - a) /\ &0 <= a /\ a < &1 <=> frac x = a|} ],
  vREWRITE_TAC[vFRAC_FLOOR; vREAL_ARITH [%q {|x - f:real = a <=> f = x - a|} ]] ---->
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vFLOOR_UNIQUE] ---->
  vAP_TERM_TAC ----> vREAL_ARITH_TAC);;

let%a vREAL_FRAC_EQ = prove
 ([%q {|!x. frac x = x <=> &0 <= x /\ x < &1|} ],
  vREWRITE_TAC[vGSYM vFRAC_UNIQUE; vREAL_SUB_REFL; vINTEGER_CLOSED]);;

let%a vINTEGER_ROUND = prove
 ([%q {|!x. ?n. integer n /\ abs(x - n) <= &1 / &2|} ],
  vGEN_TAC ----> vMATCH_MP_TAC(vMESON[] [%q {|!a. P a \/ P(a + &1) ==> ?x. P x|} ]) ---->
  vEXISTS_TAC [%q {|floor x|} ] ----> vMP_TAC(vISPEC [%q {|x:real|} ] vFLOOR) ---->
  vSIMP_TAC[vINTEGER_CLOSED] ----> vREAL_ARITH_TAC);;

let%a vFRAC_DIV_MOD = prove
 ([%q {|!m n. ~(n = 0) ==> frac(&m / &n) = &(m MOD n) / &n|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vFRAC_UNIQUE] ---->
  vASM_SIMP_TAC[vREAL_LE_DIV; vREAL_POS; vREAL_LT_LDIV_EQ; vREAL_OF_NUM_LT; vLE_1;
               vREAL_ARITH [%q {|x / a - y / a:real = (x - y) / a|} ]] ---->
  vMP_TAC(vSPECL [[%q {|m:num|} ]; [%q {|n:num|} ]] vDIVISION) ---->
  vASM_SIMP_TAC[vREAL_OF_NUM_LT; vREAL_MUL_LID] ---->
  vDISCH_THEN(fun th ->
    vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV -| vLAND_CONV -| vRAND_CONV)
                    [vCONJUNCT1 th]) ---->
  vSIMP_TAC[vREAL_OF_NUM_SUB; vONCE_REWRITE_RULE[vADD_SYM] vLE_ADD; vADD_SUB] ---->
  vASM_SIMP_TAC[vGSYM vREAL_OF_NUM_MUL; vREAL_OF_NUM_EQ; vINTEGER_CLOSED;
               vREAL_FIELD [%q {|~(n:real = &0) ==> (x * n) / n = x|} ]]);;

let%a vFRAC_NEG = prove
 ([%q {|!x. frac(--x) = if integer x then &0 else &1 - frac x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vFRAC_FLOOR; vREAL_FLOOR_NEG] ---->
  vCOND_CASES_TAC ----> vREAL_ARITH_TAC);;

let%a vREAL_FLOOR_FLOOR_DIV = prove
 ([%q {|!x n. floor(floor x / &n) = floor(x / &n)|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|n = 0|} ] ---->
  vASM_REWRITE_TAC[real_div; vREAL_INV_0; vREAL_MUL_RZERO] ---->
  vREWRITE_TAC[vGSYM real_div; vGSYM vFLOOR_UNIQUE; vFLOOR] ---->
  vASM_SIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_LE_RDIV_EQ; vREAL_OF_NUM_LT; vLE_1] ---->
  vSIMP_TAC[vREAL_FLOOR_LT; vREAL_LE_FLOOR; vFLOOR; vINTEGER_CLOSED] ---->
  vASM_SIMP_TAC[vGSYM vREAL_LT_LDIV_EQ; vGSYM vREAL_LE_RDIV_EQ;
               vREAL_OF_NUM_LT; vLE_1; vFLOOR]);;

(* ------------------------------------------------------------------------- *)
(* Assertions that there are integers between well-spaced reals.             *)
(* ------------------------------------------------------------------------- *)

let%a vINTEGER_EXISTS_BETWEEN_ALT = prove
 ([%q {|!x y. x + &1 <= y ==> ?n. integer n /\ x < n /\ n <= y|} ],
  vREPEAT vSTRIP_TAC ----> vEXISTS_TAC [%q {|floor y|} ] ---->
  vMP_TAC(vSPEC [%q {|y:real|} ] vFLOOR) ----> vSIMP_TAC[] ----> vASM_REAL_ARITH_TAC);;

let%a vINTEGER_EXISTS_BETWEEN_LT = prove
 ([%q {|!x y. x + &1 < y ==> ?n. integer n /\ x < n /\ n < y|} ],
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC [%q {|integer y|} ] ++-->
   [vEXISTS_TAC [%q {|y - &1:real|} ] ---->
    vASM_SIMP_TAC[vINTEGER_CLOSED] ----> vASM_REAL_ARITH_TAC;
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vINTEGER_EXISTS_BETWEEN_ALT -|
      vMATCH_MP vREAL_LT_IMP_LE) ---->
    vMATCH_MP_TAC vMONO_EXISTS ----> vREPEAT vSTRIP_TAC ---->
    vASM_REWRITE_TAC[vREAL_LT_LE] ----> vASM_MESON_TAC[]]);;

let%a vINTEGER_EXISTS_BETWEEN = prove
 ([%q {|!x y. x + &1 <= y ==> ?n. integer n /\ x <= n /\ n < y|} ],
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC [%q {|integer y|} ] ++-->
   [vEXISTS_TAC [%q {|y - &1:real|} ] ---->
    vASM_SIMP_TAC[vINTEGER_CLOSED] ----> vASM_REAL_ARITH_TAC;
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vINTEGER_EXISTS_BETWEEN_ALT) ---->
    vMATCH_MP_TAC vMONO_EXISTS ----> vREPEAT vSTRIP_TAC ---->
    vASM_REWRITE_TAC[vREAL_LT_LE] ++--> [vASM_REAL_ARITH_TAC; vASM_MESON_TAC[]]]);;

let%a vINTEGER_EXISTS_BETWEEN_ABS = prove
 ([%q {|!x y. &1 <= abs(x - y)
         ==> ?n. integer n /\ (x <= n /\ n < y \/ y <= n /\ n < x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_abs] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ----> vDISCH_TAC ++-->
   [vMP_TAC(vISPECL [[%q {|y:real|} ]; [%q {|x:real|} ]] vINTEGER_EXISTS_BETWEEN);
    vMP_TAC(vISPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vINTEGER_EXISTS_BETWEEN)] ---->
  (vANTS_TAC ++--> [vASM_REAL_ARITH_TAC; vMATCH_MP_TAC vMONO_EXISTS]) ---->
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[]);;

let%a vINTEGER_EXISTS_BETWEEN_ABS_LT = prove
 ([%q {|!x y. &1 < abs(x - y)
         ==> ?n. integer n /\ (x < n /\ n < y \/ y < n /\ n < x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_abs] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ----> vDISCH_TAC ++-->
   [vMP_TAC(vISPECL [[%q {|y:real|} ]; [%q {|x:real|} ]] vINTEGER_EXISTS_BETWEEN_LT);
    vMP_TAC(vISPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vINTEGER_EXISTS_BETWEEN_LT)] ---->
  (vANTS_TAC ++--> [vASM_REAL_ARITH_TAC; vMATCH_MP_TAC vMONO_EXISTS]) ---->
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More trivial theorems about real_of_int.                                  *)
(* ------------------------------------------------------------------------- *)

let%a vREAL_OF_INT_OF_REAL = prove
 ([%q {|!x. integer(x) ==> real_of_int(int_of_real x) = x|} ],
  vSIMP_TAC[int_rep]);;

let%a vIMAGE_REAL_OF_INT_UNIV = prove
 ([%q {|IMAGE real_of_int (:int) = integer|} ],
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vIN_UNIV] ---->
  vREWRITE_TAC[vIN] ----> vMESON_TAC[int_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Finiteness of bounded set of integers.                                    *)
(* ------------------------------------------------------------------------- *)

let%a vHAS_SIZE_INTSEG_NUM = prove
 ([%q {|!m n. {x | integer(x) /\ &m <= x /\ x <= &n} HAS_SIZE ((n + 1) - m)|} ],
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|{x | integer(x) /\ &m <= x /\ x <= &n} =
                IMAGE real_of_num (m..n)|} ]
  vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vIN_ELIM_THM] ---->
    vX_GEN_TAC [%q {|x:real|} ] ----> vASM_CASES_TAC [%q {|?k. x = &k|} ] ++-->
     [vFIRST_X_ASSUM(vCHOOSE_THEN vSUBST_ALL_TAC) ---->
      vREWRITE_TAC[vREAL_OF_NUM_LE; vINTEGER_CLOSED; vREAL_OF_NUM_EQ] ---->
      vREWRITE_TAC[vUNWIND_THM1; vIN_NUMSEG];
      vASM_MESON_TAC[vINTEGER_POS; vREAL_ARITH [%q {|&n <= x ==> &0 <= x|} ]]];
    vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ----> vREWRITE_TAC[vHAS_SIZE_NUMSEG] ---->
    vSIMP_TAC[vREAL_OF_NUM_EQ]]);;

let%a vFINITE_INTSEG = prove
 ([%q {|!a b. FINITE {x | integer(x) /\ a <= x /\ x <= b}|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|max (abs a) (abs b)|} ] vREAL_ARCH_SIMPLE) ---->
  vREWRITE_TAC[vREAL_MAX_LE; vLEFT_IMP_EXISTS_THM] ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vSTRIP_TAC ---->
  vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC [%q {|{x | integer(x) /\ abs(x) <= &n}|} ] ----> vCONJ_TAC ++-->
   [vALL_TAC; vSIMP_TAC[vSUBSET; vIN_ELIM_THM] ----> vASM_REAL_ARITH_TAC] ---->
  vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC [%q {|IMAGE (\x. &x) (0..n) UNION IMAGE (\x. --(&x)) (0..n)|} ] ---->
  vASM_SIMP_TAC[vFINITE_UNION; vFINITE_IMAGE; vFINITE_NUMSEG] ---->
  vREWRITE_TAC[vINTEGER_CASES; vSUBSET; vIN_ELIM_THM] ---->
  vREPEAT vSTRIP_TAC ----> vFIRST_X_ASSUM vSUBST_ALL_TAC ---->
  vREWRITE_TAC[vIN_UNION; vIN_IMAGE; vREAL_OF_NUM_EQ; vREAL_EQ_NEG2] ---->
  vREWRITE_TAC[vUNWIND_THM1; vIN_NUMSEG] ---->
  vREWRITE_TAC[vGSYM vREAL_OF_NUM_LE] ---->
  vASM_REAL_ARITH_TAC);;

let%a vHAS_SIZE_INTSEG_INT = prove
 ([%q {|!a b. integer a /\ integer b
         ==> {x | integer(x) /\ a <= x /\ x <= b} HAS_SIZE
             if b < a then 0 else num_of_int(int_of_real(b - a + &1))|} ],
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN
   [%q {|{x | integer(x) /\ a <= x /\ x <= b} =
    IMAGE (\n. a + &n) {n | &n <= b - a}|} ]
  vSUBST1_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSURJECTIVE_IMAGE_EQ ---->
    vASM_SIMP_TAC[vIN_ELIM_THM; vINTEGER_CLOSED] ---->
    vCONJ_TAC ++--> [vALL_TAC; vREAL_ARITH_TAC] ---->
    vX_GEN_TAC [%q {|c:real|} ] ----> vSTRIP_TAC ---->
    vONCE_REWRITE_TAC[vREAL_ARITH [%q {|a + x:real = y <=> y - a = x|} ]] ---->
    vASM_SIMP_TAC[vGSYM vINTEGER_POS; vREAL_SUB_LE; vINTEGER_CLOSED];
    vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ---->

    vSIMP_TAC[vREAL_EQ_ADD_LCANCEL; vREAL_OF_NUM_EQ] ---->
    vCOND_CASES_TAC ++-->
     [vASM_SIMP_TAC[vREAL_ARITH [%q {|b < a ==> ~(&n <= b - a)|} ]] ---->
      vREWRITE_TAC[vHAS_SIZE_0; vEMPTY_GSPEC];
      vSUBGOAL_THEN [%q {|?m. b - a = &m|} ] (vCHOOSE_THEN vSUBST1_TAC) ++-->
       [vASM_MESON_TAC[vINTEGER_POS; vINTEGER_CLOSED; vREAL_NOT_LT; vREAL_SUB_LE];
        vREWRITE_TAC[vREAL_OF_NUM_ADD; vREAL_OF_NUM_LE; vGSYM int_of_num;
                    vNUM_OF_INT_OF_NUM; vHAS_SIZE_NUMSEG_LE]]]]);;

let%a vCARD_INTSEG_INT = prove
 ([%q {|!a b. integer a /\ integer b
         ==> CARD {x | integer(x) /\ a <= x /\ x <= b} =
             if b < a then 0 else num_of_int(int_of_real(b - a + &1))|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vHAS_SIZE_INTSEG_INT) ---->
  vSIMP_TAC[vHAS_SIZE]);;

let%a vREAL_CARD_INTSEG_INT = prove
 ([%q {|!a b. integer a /\ integer b
         ==> &(CARD {x | integer(x) /\ a <= x /\ x <= b}) =
             if b < a then &0 else b - a + &1|} ],
  vREPEAT vSTRIP_TAC ----> vASM_SIMP_TAC[vCARD_INTSEG_INT] ---->
  vCOND_CASES_TAC ----> vASM_SIMP_TAC[vREAL_OF_INT_OF_REAL] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vGSYM int_of_num_th] ---->
  vW(vMP_TAC -| vPART_MATCH (lhs -| rand) vINT_OF_NUM_OF_INT -|
    rand -| lhand -| snd) ---->
  vANTS_TAC ++-->
   [vASM_SIMP_TAC[int_le; int_of_num_th; vREAL_OF_INT_OF_REAL;
                 vINTEGER_CLOSED] ----> vASM_REAL_ARITH_TAC;
    vDISCH_THEN vSUBST1_TAC ----> vMATCH_MP_TAC vREAL_OF_INT_OF_REAL ---->
    vASM_SIMP_TAC[vINTEGER_CLOSED]]);;

(* ------------------------------------------------------------------------- *)
(* Yet set of all integers or rationals is infinite.                         *)
(* ------------------------------------------------------------------------- *)

let%a vINFINITE_INTEGER = prove
 ([%q {|INFINITE integer|} ],
  vSUBGOAL_THEN [%q {|INFINITE(IMAGE real_of_num (:num))|} ] vMP_TAC ++-->
   [vSIMP_TAC[vINFINITE_IMAGE_INJ; vREAL_OF_NUM_EQ; num_INFINITE]; vALL_TAC] ---->
  vREWRITE_TAC[vINFINITE; vCONTRAPOS_THM] ---->
  vMATCH_MP_TAC(vREWRITE_RULE[vIMP_CONJ_ALT] vFINITE_SUBSET) ---->
  vREWRITE_TAC[vSUBSET; vFORALL_IN_IMAGE; vIN_UNIV] ---->
  vREWRITE_TAC[vIN; vINTEGER_CLOSED]);;

let%a vINFINITE_RATIONAL = prove
 ([%q {|INFINITE rational|} ],
  vMP_TAC vINFINITE_INTEGER ---->
  vREWRITE_TAC[vINFINITE; vCONTRAPOS_THM] ---->
  vMATCH_MP_TAC(vREWRITE_RULE[vIMP_CONJ_ALT] vFINITE_SUBSET) ---->
  vREWRITE_TAC[vSUBSET; vIN; vRATIONAL_INTEGER]);;

(* ------------------------------------------------------------------------- *)
(* Arbitrarily good rational approximations.                                 *)
(* ------------------------------------------------------------------------- *)

let%a vPADIC_RATIONAL_APPROXIMATION_STRADDLE = prove
 ([%q {|!p x e. &0 < e /\ &1 < p
           ==> ?n q r. integer q /\ integer r /\
                       q / p pow n < x /\ x < r / p pow n /\
                       abs(q / p pow n - r / p pow n) < e|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [[%q {|p:real|} ]; [%q {|&2 / e:real|} ]] vREAL_ARCH_POW) ---->
  vASM_SIMP_TAC[vREAL_LT_LDIV_EQ] ----> vMATCH_MP_TAC vMONO_EXISTS ---->
  vX_GEN_TAC [%q {|n:num|} ] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vREAL_MUL_SYM] ---->
  vASM_SIMP_TAC[vGSYM vREAL_LT_LDIV_EQ; vREAL_POW_LT;
               vREAL_ARITH [%q {|&1 < p ==> &0 < p|} ]] ---->
  vDISCH_TAC ----> vMAP_EVERY vEXISTS_TAC
   [[%q {|floor(p pow n * x) - &1|} ]; [%q {|floor(p pow n * x) + &1|} ]] ---->
  vREWRITE_TAC[vREAL_ARITH
   [%q {|abs((x - &1) / p - (x + &1) / p) = abs(&2 / p)|} ]] ---->
  vASM_SIMP_TAC[vFLOOR; vINTEGER_CLOSED; vREAL_LT_LDIV_EQ; vREAL_LT_RDIV_EQ;
               vREAL_POW_LT; vREAL_ARITH [%q {|&1 < p ==> &0 < p|} ]] ---->
  vREWRITE_TAC[vREAL_ABS_DIV; vREAL_ABS_POW; vREAL_ABS_NUM] ---->
  vASM_SIMP_TAC[vREAL_ARITH [%q {|&1 < p ==> abs p = p|} ]] ---->
  vMP_TAC(vISPEC [%q {|p pow n * x:real|} ] vFLOOR) ----> vREAL_ARITH_TAC);;

let vPADIC_RATIONAL_APPROXIMATION_STRADDLE_POS,
    vPADIC_RATIONAL_APPROXIMATION_STRADDLE_POS_LE = (vCONJ_PAIR -| prove)
 ([%q {|(!p x e. &0 < e /\ &1 < p /\ &0 < x
            ==> ?n q r. &q / p pow n < x /\ x < &r / p pow n /\
                        abs(&q / p pow n - &r / p pow n) < e) /\
   (!p x e. &0 < e /\ &1 < p /\ &0 <= x
           ==> ?n q r. &q / p pow n <= x /\ x < &r / p pow n /\
                       abs(&q / p pow n - &r / p pow n) < e)|} ],
  vREPEAT vSTRIP_TAC ---->
 (vSUBGOAL_THEN [%q {|&0 < p /\ &0 <= p|} ] vSTRIP_ASSUME_TAC ++-->
   [vASM_REAL_ARITH_TAC; vALL_TAC] ---->
  vMP_TAC(vISPECL [[%q {|p:real|} ]; [%q {|x:real|} ]; [%q {|e:real|} ]]
    vPADIC_RATIONAL_APPROXIMATION_STRADDLE) ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|n:num|} ] ---->
  vASM_SIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_LT_RDIV_EQ; vREAL_POW_LT;
               vREAL_LE_LDIV_EQ; vREAL_LE_RDIV_EQ; vLEFT_IMP_EXISTS_THM] ---->
  vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|q:real|} ]; [%q {|r:real|} ]] ----> vSTRIP_TAC ---->
  vMP_TAC(vISPEC [%q {|r:real|} ] integer) ---->
  vMP_TAC(vISPEC [%q {|max q (&0)|} ] integer) ---->
  vASM_SIMP_TAC[vINTEGER_CLOSED] ---->
  vREWRITE_TAC[vIMP_IMP; vLEFT_AND_EXISTS_THM] ---->
  vREWRITE_TAC[vRIGHT_AND_EXISTS_THM] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|a:num|} ] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|b:num|} ] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|abs(max q (&0)) = max q (&0)|} ]] ---->
  vSUBGOAL_THEN [%q {|&0 < r|} ] vASSUME_TAC ++-->
   [vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vREAL_ARITH
     [%q {|a < r ==> &0 <= a ==> &0 < r|} ])) ---->
    vMATCH_MP_TAC vREAL_LE_MUL ----> vASM_SIMP_TAC[vREAL_LT_IMP_LE] ---->
    vMATCH_MP_TAC vREAL_POW_LE ----> vASM_REAL_ARITH_TAC;
    vASM_SIMP_TAC[vREAL_ARITH [%q {|&0 < r ==> abs r = r|} ]]] ---->
  vDISCH_THEN(vCONJUNCTS_THEN (vSUBST1_TAC -| vSYM)) ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|max q (&0) = if &0 <= q then q else &0|} ]] ---->
  vCOND_CASES_TAC ----> vASM_SIMP_TAC[vREAL_LT_IMP_LE] ---->
  vASM_SIMP_TAC[vREAL_LE_MUL; vREAL_LT_MUL; vREAL_POW_LE; vREAL_POW_LT] ---->
  vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vREAL_ARITH
   [%q {|abs(q - r) < e ==> &0 < --q /\ z = &0 /\ &0 < r
    ==> abs(z - r) < e|} ])) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_POW_LT] ---->
  vREWRITE_TAC[real_div; vREAL_MUL_LZERO; vGSYM vREAL_MUL_LNEG] ---->
  vMATCH_MP_TAC vREAL_LT_MUL ---->
  vASM_SIMP_TAC[vREAL_LT_INV_EQ; vREAL_POW_LT] ----> vASM_REAL_ARITH_TAC));;

let%a vRATIONAL_APPROXIMATION = prove
 ([%q {|!x e. &0 < e ==> ?r. rational r /\ abs(r - x) < e|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [[%q {|&2:real|} ]; [%q {|x:real|} ]; [%q {|e:real|} ]]
    vPADIC_RATIONAL_APPROXIMATION_STRADDLE) ---->
  vANTS_TAC ++--> [vASM_REAL_ARITH_TAC; vREWRITE_TAC[vLEFT_IMP_EXISTS_THM]] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|n:num|} ]; [%q {|q:real|} ]; [%q {|r:real|} ]] ---->
  vSTRIP_TAC ----> vEXISTS_TAC [%q {|q / &2 pow n|} ] ---->
  vASM_SIMP_TAC[vRATIONAL_CLOSED] ----> vASM_REAL_ARITH_TAC);;

let%a vRATIONAL_BETWEEN = prove
 ([%q {|!a b. a < b ==> ?q. rational q /\ a < q /\ q < b|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|(a + b) / &2|} ]; [%q {|(b - a) / &4|} ]] vRATIONAL_APPROXIMATION) ---->
  vANTS_TAC ++--> [vALL_TAC; vMATCH_MP_TAC vMONO_EXISTS ----> vSIMP_TAC[]] ---->
  vASM_REAL_ARITH_TAC);;

let%a vRATIONAL_BETWEEN_EQ = prove
 ([%q {|!a b. (?q. rational q /\ a < q /\ q < b) <=> a < b|} ],
  vMESON_TAC[vRATIONAL_BETWEEN; vREAL_LT_TRANS]);;

let%a vRATIONAL_APPROXIMATION_STRADDLE = prove
 ([%q {|!x e. &0 < e
         ==> ?a b. rational a /\ rational b /\
                   a < x /\ x < b /\ abs(b - a) < e|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [[%q {|x - e / &4|} ]; [%q {|e / &4|} ]] vRATIONAL_APPROXIMATION) ---->
  vANTS_TAC ++-->
   [vASM_REAL_ARITH_TAC;
    vMATCH_MP_TAC vMONO_EXISTS ----> vGEN_TAC ----> vSTRIP_TAC] ---->
  vMP_TAC(vISPECL [[%q {|x + e / &4|} ]; [%q {|e / &4|} ]] vRATIONAL_APPROXIMATION) ---->
  vANTS_TAC ++-->
   [vASM_REAL_ARITH_TAC;
    vMATCH_MP_TAC vMONO_EXISTS ----> vGEN_TAC ----> vSTRIP_TAC] ---->
  vASM_REWRITE_TAC[] ----> vASM_REAL_ARITH_TAC);;

let%a vRATIONAL_APPROXIMATION_ABOVE = prove
 ([%q {|!x e. &0 < e ==> ?q. rational q /\ x < q /\ q < x + e|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|x:real|} ]; [%q {|e:real|} ]] vRATIONAL_APPROXIMATION_STRADDLE) ---->
  vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vSWAP_EXISTS_THM] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vREPEAT vSTRIP_TAC ---->
  vASM_REWRITE_TAC[] ----> vASM_REAL_ARITH_TAC);;

let%a vRATIONAL_APPROXIMATION_BELOW = prove
 ([%q {|!x e. &0 < e ==> ?q. rational q /\ x - e < q /\ q < x|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|x:real|} ]; [%q {|e:real|} ]] vRATIONAL_APPROXIMATION_STRADDLE) ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vMONO_EXISTS ----> vREPEAT vSTRIP_TAC ---->
  vASM_REWRITE_TAC[] ----> vASM_REAL_ARITH_TAC);;

let%a vINFINITE_RATIONAL_IN_RANGE = prove
 ([%q {|!a b. a < b ==> INFINITE {q | rational q /\ a < q /\ q < b}|} ],
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN
   [%q {|?q. (!n. rational(q n) /\ a < q n /\ q n < b) /\ (!n. q(SUC n) < q n)|} ]
  vSTRIP_ASSUME_TAC ++-->
   [vMATCH_MP_TAC vDEPENDENT_CHOICE ---->
    vREWRITE_TAC[vGSYM vCONJ_ASSOC; vGSYM vREAL_LT_MIN] ---->
    vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vRATIONAL_BETWEEN ---->
    vASM_REWRITE_TAC[vREAL_LT_MIN];
    vMATCH_MP_TAC vINFINITE_SUPERSET ---->
    vEXISTS_TAC [%q {|IMAGE (q:num->real) (:num)|} ] ---->
    vCONJ_TAC ++--> [vALL_TAC; vASM vSET_TAC[]] ---->
    vMATCH_MP_TAC vINFINITE_IMAGE ----> vREWRITE_TAC[num_INFINITE; vIN_UNIV] ---->
    vSUBGOAL_THEN [%q {|!m n. m < n ==> (q:num->real) n < q m|} ]
     (fun th -> vMESON_TAC[vLT_CASES; th; vREAL_LT_REFL]) ---->
    vMATCH_MP_TAC vTRANSITIVE_STEPWISE_LT ---->
    vASM_MESON_TAC[vREAL_LT_TRANS]]);;

(* ------------------------------------------------------------------------- *)
(* Converting a congruence over N or Z into a real equivalent.               *)
(* ------------------------------------------------------------------------- *)

let%a vREAL_CONGRUENCE = prove
 ([%q {|!a b n. (a == b) (mod n) <=>
           if n = 0 then &a:real = &b
           else integer((&a - &b) / &n)|} ],
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_OF_NUM_EQ] ++-->
   [vCONV_TAC vNUMBER_RULE; vALL_TAC] ---->
  vREWRITE_TAC[vGSYM vIMAGE_REAL_OF_INT_UNIV] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vIN] ---->
  vREWRITE_TAC[vIN_IMAGE; vIN_UNIV] ---->
  vASM_SIMP_TAC[vREAL_OF_NUM_EQ; vREAL_FIELD
   [%q {|~(n:real = &0) ==> (x / n = y <=> n * y = x)|} ]] ---->
  vREWRITE_TAC[vGSYM int_of_num_th] ---->
  vREWRITE_TAC[vGSYM int_sub_th; vGSYM int_mul_th; vGSYM int_eq] ---->
  vREWRITE_TAC[num_congruent; int_congruent] ----> vMESON_TAC[]);;

let%a vREAL_INT_CONGRUENCE = prove
 ([%q {|!a b n. (a == b) (mod n) <=>
           if n = &0 then real_of_int a = real_of_int b
           else integer((real_of_int a - real_of_int b) / real_of_int n)|} ],
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vGSYM int_eq] ++-->
   [vCONV_TAC vINTEGER_RULE; vALL_TAC] ---->
  vREWRITE_TAC[vGSYM vIMAGE_REAL_OF_INT_UNIV] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vIN] ---->
  vREWRITE_TAC[vIN_IMAGE; vIN_UNIV] ---->
  vASM_SIMP_TAC[vGSYM int_of_num_th; vGSYM int_eq;  vREAL_FIELD
   [%q {|~(n:real = &0) ==> (x / n = y <=> n * y = x)|} ]] ---->
  vREWRITE_TAC[vGSYM int_mul_th; vGSYM int_sub_th; vGSYM int_eq] ---->
  vCONV_TAC vINTEGER_RULE);;

(* ------------------------------------------------------------------------- *)
(* A simple tactic to try and prove that a real expression is integral.      *)
(* ------------------------------------------------------------------------- *)

let (vREAL_INTEGER_TAC:tactic) =
  let base = vMATCH_ACCEPT_TAC(vCONJUNCT1 vINTEGER_CLOSED) |--->
             vMATCH_ACCEPT_TAC vINTEGER_REAL_OF_INT
  and step =
    vMAP_FIRST vMATCH_MP_TAC (vCONJUNCTS(vCONJUNCT2 vINTEGER_CLOSED)) ---->
    vTRY vCONJ_TAC in
  let tac = vREPEAT step ----> base in
  fun (asl,w) ->
   (match w with
     Comb(Const("integer",_),t) ->
      (tac |--->
       (vCONV_TAC(vRAND_CONV vREAL_POLY_CONV) ----> tac)) (asl,w)
    | _ -> failwith "REAL_INTEGER_TAC: Goal not of expected form");;
