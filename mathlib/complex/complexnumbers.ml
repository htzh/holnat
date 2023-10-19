[@@@warning "-33-32-27-26-8"]
open Hol.All
open Hol.Accept
open Analysis
open Transc
open Floor
;;
(* ========================================================================= *)
(* Basic definitions and properties of complex numbers.                      *)
(* ========================================================================= *)

prioritize_real();;

(* ------------------------------------------------------------------------- *)
(* Definition of complex number type.                                        *)
(* ------------------------------------------------------------------------- *)

let complex_tybij_raw =
  new_type_definition "complex" ("complex","coords")
   (prove([%q {|?x:real#real. T|} ],vREWRITE_TAC[]));;

let complex_tybij = vREWRITE_RULE [] complex_tybij_raw;;

(* ------------------------------------------------------------------------- *)
(* Real and imaginary parts of a number.                                     *)
(* ------------------------------------------------------------------------- *)

let vRE_DEF = new_definition
  [%q {|Re(z) = FST(coords(z))|} ];;

let vIM_DEF = new_definition
  [%q {|Im(z) = SND(coords(z))|} ];;

(* ------------------------------------------------------------------------- *)
(* Set up overloading.                                                       *)
(* ------------------------------------------------------------------------- *)

do_list overload_interface
 ["+",[%q {|complex_add:complex->complex->complex|} ];
  "-",[%q {|complex_sub:complex->complex->complex|} ];
  "*",[%q {|complex_mul:complex->complex->complex|} ];
  "/",[%q {|complex_div:complex->complex->complex|} ];
  "--",[%q {|complex_neg:complex->complex|} ];
  "pow",[%q {|complex_pow:complex->num->complex|} ];
  "inv",[%q {|complex_inv:complex->complex|} ]];;

let prioritize_complex() = prioritize_overload(mk_type("complex",[]));;

(* ------------------------------------------------------------------------- *)
(* Complex absolute value (modulus).                                         *)
(* ------------------------------------------------------------------------- *)

make_overloadable "norm" [%q {|:A->real|} ];;
overload_interface("norm",[%q {|complex_norm:complex->real|} ]);;

let complex_norm = new_definition
  [%q {|norm(z) = sqrt(Re(z) pow 2 + Im(z) pow 2)|} ];;

(* ------------------------------------------------------------------------- *)
(* Imaginary unit (too inconvenient to use "i"!)                             *)
(* ------------------------------------------------------------------------- *)

let ii = new_definition
  [%q {|ii = complex(&0,&1)|} ];;

(* ------------------------------------------------------------------------- *)
(* Injection from reals.                                                     *)
(* ------------------------------------------------------------------------- *)

let vCX_DEF = new_definition
  [%q {|Cx(a) = complex(a,&0)|} ];;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations.                                                    *)
(* ------------------------------------------------------------------------- *)

let complex_neg = new_definition
  [%q {|--z = complex(--(Re(z)),--(Im(z)))|} ];;

let complex_add = new_definition
  [%q {|w + z = complex(Re(w) + Re(z),Im(w) + Im(z))|} ];;

let complex_sub = new_definition
  [%q {|w - z = w + --z|} ];;

let complex_mul = new_definition
  [%q {|w * z = complex(Re(w) * Re(z) - Im(w) * Im(z),
                   Re(w) * Im(z) + Im(w) * Re(z))|} ];;

let complex_inv = new_definition
  [%q {|inv(z) = complex(Re(z) / (Re(z) pow 2 + Im(z) pow 2),
                    --(Im(z)) / (Re(z) pow 2 + Im(z) pow 2))|} ];;

let complex_div = new_definition
  [%q {|w / z = w * inv(z)|} ];;

let complex_pow = new_recursive_definition num_RECURSION
  [%q {|(x pow 0 = Cx(&1)) /\
   (!n. x pow (SUC n) = x * x pow n)|} ];;

(* ------------------------------------------------------------------------- *)
(* Various handy rewrites.                                                   *)
(* ------------------------------------------------------------------------- *)

let%a vRE = prove
 ([%q {|(Re(complex(x,y)) = x)|} ],
  vREWRITE_TAC[vRE_DEF; complex_tybij]);;

let%a vIM = prove
 ([%q {|Im(complex(x,y)) = y|} ],
  vREWRITE_TAC[vIM_DEF; complex_tybij]);;

let%a vCOMPLEX = prove
 ([%q {|complex(Re(z),Im(z)) = z|} ],
  vREWRITE_TAC[vIM_DEF; vRE_DEF; complex_tybij]);;

let%a vCOMPLEX_EQ = prove
 ([%q {|!w z. (w = z) <=> (Re(w) = Re(z)) /\ (Im(w) = Im(z))|} ],
  vREWRITE_TAC[vRE_DEF; vIM_DEF; vGSYM vPAIR_EQ] ----> vMESON_TAC[complex_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Crude tactic to automate very simple algebraic equivalences.              *)
(* ------------------------------------------------------------------------- *)

let vSIMPLE_COMPLEX_ARITH_TAC =
  vREWRITE_TAC[vCOMPLEX_EQ; vRE; vIM; vCX_DEF;
              complex_add; complex_neg; complex_sub; complex_mul] ---->
  vREAL_ARITH_TAC;;

let%a vSIMPLE_COMPLEX_ARITH tm = prove(tm,vSIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Basic algebraic properties that can be proved automatically by this.      *)
(* ------------------------------------------------------------------------- *)

let%a vCOMPLEX_ADD_SYM = prove
 ([%q {|!x y. x + y = y + x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_ASSOC = prove
 ([%q {|!x y z. x + y + z = (x + y) + z|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_LID = prove
 ([%q {|!x. Cx(&0) + x = x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_LINV = prove
 ([%q {|!x. --x + x = Cx(&0)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_SYM = prove
 ([%q {|!x y. x * y = y * x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_ASSOC = prove
 ([%q {|!x y z. x * y * z = (x * y) * z|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_LID = prove
 ([%q {|!x. Cx(&1) * x = x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_LDISTRIB = prove
 ([%q {|!x y z. x * (y + z) = x * y + x * z|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_AC = prove
 ([%q {|(m + n = n + m) /\ ((m + n) + p = m + n + p) /\ (m + n + p = n + m + p)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_AC = prove
 ([%q {|(m * n = n * m) /\ ((m * n) * p = m * n * p) /\ (m * n * p = n * m * p)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_RID = prove
 ([%q {|!x. x + Cx(&0) = x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_RID = prove
 ([%q {|!x. x * Cx(&1) = x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_RINV = prove
 ([%q {|!x. x + --x = Cx(&0)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_RDISTRIB = prove
 ([%q {|!x y z. (x + y) * z = x * z + y * z|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_EQ_ADD_LCANCEL = prove
 ([%q {|!x y z. (x + y = x + z) <=> (y = z)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_EQ_ADD_RCANCEL = prove
 ([%q {|!x y z. (x + z = y + z) <=> (x = y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_RZERO = prove
 ([%q {|!x. x * Cx(&0) = Cx(&0)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_LZERO = prove
 ([%q {|!x. Cx(&0) * x = Cx(&0)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_NEG = prove
 ([%q {|!x. --(--x) = x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_RNEG = prove
 ([%q {|!x y. x * --y = --(x * y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_LNEG = prove
 ([%q {|!x y. --x * y = --(x * y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_ADD = prove
 ([%q {|!x y. --(x + y) = --x + --y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_0 = prove
 ([%q {|--Cx(&0) = Cx(&0)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_EQ_ADD_LCANCEL_0 = prove
 ([%q {|!x y. (x + y = x) <=> (y = Cx(&0))|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_EQ_ADD_RCANCEL_0 = prove
 ([%q {|!x y. (x + y = y) <=> (x = Cx(&0))|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_LNEG_UNIQ = prove
 ([%q {|!x y. (x + y = Cx(&0)) <=> (x = --y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_RNEG_UNIQ = prove
 ([%q {|!x y. (x + y = Cx(&0)) <=> (y = --x)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_LMUL = prove
 ([%q {|!x y. --(x * y) = --x * y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_RMUL = prove
 ([%q {|!x y. --(x * y) = x * --y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_MUL2 = prove
 ([%q {|!x y. --x * --y = x * y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_ADD = prove
 ([%q {|!x y. x - y + y = x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_ADD2 = prove
 ([%q {|!x y. y + x - y = x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_REFL = prove
 ([%q {|!x. x - x = Cx(&0)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_0 = prove
 ([%q {|!x y. (x - y = Cx(&0)) <=> (x = y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_EQ_0 = prove
 ([%q {|!x. (--x = Cx(&0)) <=> (x = Cx(&0))|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_SUB = prove
 ([%q {|!x y. --(x - y) = y - x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_SUB = prove
 ([%q {|!x y. (x + y) - x = y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_EQ = prove
 ([%q {|!x y. (--x = y) <=> (x = --y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_NEG_MINUS1 = prove
 ([%q {|!x. --x = --Cx(&1) * x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_SUB = prove
 ([%q {|!x y. x - y - x = --y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD2_SUB2 = prove
 ([%q {|!a b c d. (a + b) - (c + d) = a - c + b - d|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_LZERO = prove
 ([%q {|!x. Cx(&0) - x = --x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_RZERO = prove
 ([%q {|!x. x - Cx(&0) = x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_LNEG = prove
 ([%q {|!x y. --x - y = --(x + y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_RNEG = prove
 ([%q {|!x y. x - --y = x + y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_NEG2 = prove
 ([%q {|!x y. --x - --y = y - x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_TRIANGLE = prove
 ([%q {|!a b c. a - b + b - c = a - c|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_EQ_SUB_LADD = prove
 ([%q {|!x y z. (x = y - z) <=> (x + z = y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_EQ_SUB_RADD = prove
 ([%q {|!x y z. (x - y = z) <=> (x = z + y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_SUB2 = prove
 ([%q {|!x y. x - (x - y) = y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_ADD_SUB2 = prove
 ([%q {|!x y. x - (x + y) = --y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_DIFFSQ = prove
 ([%q {|!x y. (x + y) * (x - y) = x * x - y * y|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_EQ_NEG2 = prove
 ([%q {|!x y. (--x = --y) <=> (x = y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_LDISTRIB = prove
 ([%q {|!x y z. x * (y - z) = x * y - x * z|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_SUB_RDISTRIB = prove
 ([%q {|!x y z. (x - y) * z = x * z - y * z|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let%a vCOMPLEX_MUL_2 = prove
 ([%q {|!x. &2 * x = x + x|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Homomorphic embedding properties for Cx mapping.                          *)
(* ------------------------------------------------------------------------- *)

let%a vCX_INJ = prove
 ([%q {|!x y. (Cx(x) = Cx(y)) <=> (x = y)|} ],
  vREWRITE_TAC[vCX_DEF; vCOMPLEX_EQ; vRE; vIM]);;

let%a vCX_NEG = prove
 ([%q {|!x. Cx(--x) = --(Cx(x))|} ],
  vREWRITE_TAC[vCX_DEF; complex_neg; vRE; vIM; vREAL_NEG_0]);;

let%a vCX_INV = prove
 ([%q {|!x. Cx(inv x) = inv(Cx x)|} ],
  vGEN_TAC ---->
  vREWRITE_TAC[vCX_DEF; complex_inv; vRE; vIM] ---->
  vREWRITE_TAC[real_div; vREAL_NEG_0; vREAL_MUL_LZERO] ---->
  vREWRITE_TAC[vCOMPLEX_EQ; vREAL_POW_2; vREAL_MUL_RZERO; vRE; vIM] ---->
  vREWRITE_TAC[vREAL_ADD_RID; vREAL_INV_MUL] ---->
  vASM_CASES_TAC [%q {|x = &0|} ] ---->
  vASM_REWRITE_TAC[vREAL_INV_0; vREAL_MUL_LZERO] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_LID] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vASM_MESON_TAC[vREAL_MUL_RINV]);;

let%a vCX_ADD = prove
 ([%q {|!x y. Cx(x + y) = Cx(x) + Cx(y)|} ],
  vREWRITE_TAC[vCX_DEF; complex_add; vRE; vIM; vREAL_ADD_LID]);;

let%a vCX_SUB = prove
 ([%q {|!x y. Cx(x - y) = Cx(x) - Cx(y)|} ],
  vREWRITE_TAC[complex_sub; real_sub; vCX_ADD; vCX_NEG]);;

let%a vCX_MUL = prove
 ([%q {|!x y. Cx(x * y) = Cx(x) * Cx(y)|} ],
  vREWRITE_TAC[vCX_DEF; complex_mul; vRE; vIM; vREAL_MUL_LZERO; vREAL_MUL_RZERO] ---->
  vREWRITE_TAC[vREAL_SUB_RZERO; vREAL_ADD_RID]);;

let%a vCX_DIV = prove
 ([%q {|!x y. Cx(x / y) = Cx(x) / Cx(y)|} ],
  vREWRITE_TAC[complex_div; real_div; vCX_MUL; vCX_INV]);;

let%a vCX_POW = prove
 ([%q {|!x n. Cx(x pow n) = Cx(x) pow n|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[complex_pow; real_pow; vCX_MUL]);;

let%a vCX_ABS = prove
 ([%q {|!x. Cx(abs x) = Cx(norm(Cx(x)))|} ],
  vREWRITE_TAC[vCX_DEF; complex_norm; vCOMPLEX_EQ; vRE; vIM] ---->
  vREWRITE_TAC[vREAL_POW_2; vREAL_MUL_LZERO; vREAL_ADD_RID] ---->
  vREWRITE_TAC[vGSYM vREAL_POW_2; vPOW_2_SQRT_ABS]);;

let%a vCOMPLEX_NORM_CX = prove
 ([%q {|!x. norm(Cx(x)) = abs(x)|} ],
  vREWRITE_TAC[vGSYM vCX_INJ; vCX_ABS]);;

(* ------------------------------------------------------------------------- *)
(* A convenient lemma that we need a few times below.                        *)
(* ------------------------------------------------------------------------- *)

let%a vCOMPLEX_ENTIRE = prove
 ([%q {|!x y. (x * y = Cx(&0)) <=> (x = Cx(&0)) \/ (y = Cx(&0))|} ],
  vREWRITE_TAC[vCOMPLEX_EQ; complex_mul; vRE; vIM; vCX_DEF; vGSYM vREAL_SOS_EQ_0] ---->
  vCONV_TAC vREAL_RING);;

(* ------------------------------------------------------------------------- *)
(* Powers.                                                                   *)
(* ------------------------------------------------------------------------- *)

let%a vCOMPLEX_POW_ADD = prove
 ([%q {|!x m n. x pow (m + n) = x pow m * x pow n|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vADD_CLAUSES; complex_pow;
                  vCOMPLEX_MUL_LID; vCOMPLEX_MUL_ASSOC]);;

let%a vCOMPLEX_POW_POW = prove
 ([%q {|!x m n. (x pow m) pow n = x pow (m * n)|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[complex_pow; vMULT_CLAUSES; vCOMPLEX_POW_ADD]);;

let%a vCOMPLEX_POW_1 = prove
 ([%q {|!x. x pow 1 = x|} ],
  vREWRITE_TAC[num_CONV [%q {|1|} ]] ----> vREWRITE_TAC[complex_pow; vCOMPLEX_MUL_RID]);;

let%a vCOMPLEX_POW_2 = prove
 ([%q {|!x. x pow 2 = x * x|} ],
  vREWRITE_TAC[num_CONV [%q {|2|} ]] ----> vREWRITE_TAC[complex_pow; vCOMPLEX_POW_1]);;

let%a vCOMPLEX_POW_NEG = prove
 ([%q {|!x n. (--x) pow n = if EVEN n then x pow n else --(x pow n)|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[complex_pow; vEVEN] ---->
  vASM_CASES_TAC [%q {|EVEN n|} ] ---->
  vASM_REWRITE_TAC[vCOMPLEX_MUL_RNEG; vCOMPLEX_MUL_LNEG; vCOMPLEX_NEG_NEG]);;

let%a vCOMPLEX_POW_ONE = prove
 ([%q {|!n. Cx(&1) pow n = Cx(&1)|} ],
  vINDUCT_TAC ----> vASM_REWRITE_TAC[complex_pow; vCOMPLEX_MUL_LID]);;

let%a vCOMPLEX_POW_MUL = prove
 ([%q {|!x y n. (x * y) pow n = (x pow n) * (y pow n)|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[complex_pow; vCOMPLEX_MUL_LID; vCOMPLEX_MUL_AC]);;

let%a vCOMPLEX_POW_II_2 = prove
 ([%q {|ii pow 2 = --Cx(&1)|} ],
  vREWRITE_TAC[ii; vCOMPLEX_POW_2; complex_mul; vCX_DEF; vRE; vIM; complex_neg] ---->
  vCONV_TAC vREAL_RAT_REDUCE_CONV);;

let%a vCOMPLEX_POW_EQ_0 = prove
 ([%q {|!x n. (x pow n = Cx(&0)) <=> (x = Cx(&0)) /\ ~(n = 0)|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vNOT_SUC; complex_pow; vCOMPLEX_ENTIRE] ++-->
   [vSIMPLE_COMPLEX_ARITH_TAC; vCONV_TAC vTAUT]);;

(* ------------------------------------------------------------------------- *)
(* Norms (aka "moduli").                                                     *)
(* ------------------------------------------------------------------------- *)

let%a vCOMPLEX_NORM_CX = prove
 ([%q {|!x. norm(Cx x) = abs(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[complex_norm; vCX_DEF; vRE; vIM] ---->
  vREWRITE_TAC[vREAL_POW_2; vREAL_MUL_LZERO; vREAL_ADD_RID] ---->
  vREWRITE_TAC[vGSYM vREAL_POW_2; vPOW_2_SQRT_ABS]);;

let%a vCOMPLEX_NORM_POS = prove
 ([%q {|!z. &0 <= norm(z)|} ],
  vSIMP_TAC[complex_norm; vSQRT_POS_LE; vREAL_POW_2;
           vREAL_LE_SQUARE; vREAL_LE_ADD]);;

let%a vCOMPLEX_ABS_NORM = prove
 ([%q {|!z. abs(norm z) = norm z|} ],
  vREWRITE_TAC[real_abs; vCOMPLEX_NORM_POS]);;

let%a vCOMPLEX_NORM_ZERO = prove
 ([%q {|!z. (norm z = &0) <=> (z = Cx(&0))|} ],
  vGEN_TAC ----> vREWRITE_TAC[complex_norm] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vSQRT_0] ---->
  vSIMP_TAC[vREAL_POW_2; vREAL_LE_SQUARE; vREAL_LE_ADD; vREAL_POS; vSQRT_INJ] ---->
  vREWRITE_TAC[vCOMPLEX_EQ; vRE; vIM; vCX_DEF] ---->
  vSIMP_TAC[vREAL_LE_SQUARE; vREAL_ARITH
   [%q {|&0 <= x /\ &0 <= y ==> ((x + y = &0) <=> (x = &0) /\ (y = &0))|} ]] ---->
  vREWRITE_TAC[vREAL_ENTIRE]);;

let%a vCOMPLEX_NORM_NUM = prove
 ([%q {|norm(Cx(&n)) = &n|} ],
  vREWRITE_TAC[vCOMPLEX_NORM_CX; vREAL_ABS_NUM]);;

let%a vCOMPLEX_NORM_0 = prove
 ([%q {|norm(Cx(&0)) = &0|} ],
  vMESON_TAC[vCOMPLEX_NORM_ZERO]);;

let%a vCOMPLEX_NORM_NZ = prove
 ([%q {|!z. &0 < norm(z) <=> ~(z = Cx(&0))|} ],
  vMESON_TAC[vCOMPLEX_NORM_ZERO; vCOMPLEX_ABS_NORM; vREAL_ABS_NZ]);;

let%a vCOMPLEX_NORM_NEG = prove
 ([%q {|!z. norm(--z) = norm(z)|} ],
  vREWRITE_TAC[complex_neg; complex_norm; vREAL_POW_2; vRE; vIM] ---->
  vGEN_TAC ----> vAP_TERM_TAC ----> vREAL_ARITH_TAC);;

let%a vCOMPLEX_NORM_MUL = prove
 ([%q {|!w z. norm(w * z) = norm(w) * norm(z)|} ],
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[complex_norm; complex_mul; vRE; vIM] ---->
  vSIMP_TAC[vGSYM vSQRT_MUL; vREAL_POW_2; vREAL_LE_ADD; vREAL_LE_SQUARE] ---->
  vAP_TERM_TAC ----> vREAL_ARITH_TAC);;

let%a vCOMPLEX_NORM_POW = prove
 ([%q {|!z n. norm(z pow n) = norm(z) pow n|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[complex_pow; real_pow; vCOMPLEX_NORM_NUM; vCOMPLEX_NORM_MUL]);;

let%a vCOMPLEX_NORM_INV = prove
 ([%q {|!z. norm(inv z) = inv(norm z)|} ],
  vGEN_TAC ----> vREWRITE_TAC[complex_norm; complex_inv; vRE; vIM] ---->
  vREWRITE_TAC[vREAL_POW_2; real_div] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|(r * d) * r * d + (--i * d) * --i * d =
                          (r * r + i * i) * d * d:real|} ]] ---->
  vASM_CASES_TAC [%q {|Re z * Re z + Im z * Im z = &0|} ] ++-->
   [vASM_REWRITE_TAC[vREAL_INV_0; vSQRT_0; vREAL_MUL_LZERO]; vALL_TAC] ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_MUL_RINV_UNIQ ---->
  vSIMP_TAC[vGSYM vSQRT_MUL; vREAL_LE_MUL; vREAL_LE_INV_EQ; vREAL_LE_ADD;
           vREAL_LE_SQUARE] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
   [%q {|a * a * b * b:real = (a * b) * (a * b)|} ]] ---->
  vASM_SIMP_TAC[vREAL_MUL_RINV; vREAL_MUL_LID; vSQRT_1]);;

let%a vCOMPLEX_NORM_DIV = prove
 ([%q {|!w z. norm(w / z) = norm(w) / norm(z)|} ],
  vREWRITE_TAC[complex_div; real_div; vCOMPLEX_NORM_INV; vCOMPLEX_NORM_MUL]);;

let%a vCOMPLEX_NORM_TRIANGLE = prove
 ([%q {|!w z. norm(w + z) <= norm(w) + norm(z)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[complex_norm; complex_add; vRE; vIM] ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|&0 <= y /\ abs(x) <= abs(y) ==> x <= y|} ]) ---->
  vSIMP_TAC[vSQRT_POS_LE; vREAL_POW_2; vREAL_LE_ADD; vREAL_LE_SQUARE;
           vREAL_LE_SQUARE_ABS; vSQRT_POW_2] ---->
  vGEN_REWRITE_TAC vRAND_CONV[vREAL_ARITH
    [%q {|(a + b) * (a + b) = a * a + b * b + &2 * a * b|} ]] ---->
  vREWRITE_TAC[vGSYM vREAL_POW_2] ---->
  vSIMP_TAC[vSQRT_POW_2; vREAL_POW_2; vREAL_LE_ADD; vREAL_LE_SQUARE] ---->
  vREWRITE_TAC[vREAL_ARITH
   [%q {|(rw + rz) * (rw + rz) + (iw + iz) * (iw + iz) <=
    (rw * rw + iw * iw) + (rz * rz + iz * iz) + &2 * other <=>
    rw * rz + iw * iz <= other|} ]] ---->
  vSIMP_TAC[vGSYM vSQRT_MUL; vREAL_POW_2; vREAL_LE_ADD; vREAL_LE_SQUARE] ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|&0 <= y /\ abs(x) <= abs(y) ==> x <= y|} ]) ---->
  vSIMP_TAC[vSQRT_POS_LE; vREAL_POW_2; vREAL_LE_ADD; vREAL_LE_SQUARE;
           vREAL_LE_SQUARE_ABS; vSQRT_POW_2; vREAL_LE_MUL] ---->
  vREWRITE_TAC[vREAL_ARITH
   [%q {|(rw * rz + iw * iz) * (rw * rz + iw * iz) <=
    (rw * rw + iw * iw) * (rz * rz + iz * iz) <=>
    &0 <= (rw * iz - rz * iw) * (rw * iz - rz * iw)|} ]] ---->
  vREWRITE_TAC[vREAL_LE_SQUARE]);;

let%a vCOMPLEX_NORM_TRIANGLE_SUB = prove
 ([%q {|!w z. norm(w) <= norm(w + z) + norm(z)|} ],
  vMESON_TAC[vCOMPLEX_NORM_TRIANGLE; vCOMPLEX_NORM_NEG; vCOMPLEX_ADD_ASSOC;
            vCOMPLEX_ADD_RINV; vCOMPLEX_ADD_RID]);;

let%a vCOMPLEX_NORM_ABS_NORM = prove
 ([%q {|!w z. abs(norm w - norm z) <= norm(w - z)|} ],
  vREPEAT vGEN_TAC ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|a - b <= x /\ b - a <= x ==> abs(a - b) <= x:real|} ]) ---->
  vMESON_TAC[vCOMPLEX_NEG_SUB; vCOMPLEX_NORM_NEG; vREAL_LE_SUB_RADD; complex_sub;
            vCOMPLEX_NORM_TRIANGLE_SUB]);;

(* ------------------------------------------------------------------------- *)
(* Complex conjugate.                                                        *)
(* ------------------------------------------------------------------------- *)

let cnj = new_definition
  [%q {|cnj(z) = complex(Re(z),--(Im(z)))|} ];;

(* ------------------------------------------------------------------------- *)
(* Conjugation is an automorphism.                                           *)
(* ------------------------------------------------------------------------- *)

let%a vCNJ_INJ = prove
 ([%q {|!w z. (cnj(w) = cnj(z)) <=> (w = z)|} ],
  vREWRITE_TAC[cnj; vCOMPLEX_EQ; vRE; vIM; vREAL_EQ_NEG2]);;

let%a vCNJ_CNJ = prove
 ([%q {|!z. cnj(cnj z) = z|} ],
  vREWRITE_TAC[cnj; vCOMPLEX_EQ; vRE; vIM; vREAL_NEG_NEG]);;

let%a vCNJ_CX = prove
 ([%q {|!x. cnj(Cx x) = Cx x|} ],
  vREWRITE_TAC[cnj; vCOMPLEX_EQ; vCX_DEF; vREAL_NEG_0; vRE; vIM]);;

let%a vCOMPLEX_NORM_CNJ = prove
 ([%q {|!z. norm(cnj z) = norm(z)|} ],
  vREWRITE_TAC[complex_norm; cnj; vREAL_POW_2] ---->
  vREWRITE_TAC[vREAL_MUL_LNEG; vREAL_MUL_RNEG; vRE; vIM; vREAL_NEG_NEG]);;

let%a vCNJ_NEG = prove
 ([%q {|!z. cnj(--z) = --(cnj z)|} ],
  vREWRITE_TAC[cnj; complex_neg; vCOMPLEX_EQ; vRE; vIM]);;

let%a vCNJ_INV = prove
 ([%q {|!z. cnj(inv z) = inv(cnj z)|} ],
  vREWRITE_TAC[cnj; complex_inv; vCOMPLEX_EQ; vRE; vIM] ---->
  vREWRITE_TAC[real_div; vREAL_NEG_NEG; vREAL_POW_2;
              vREAL_MUL_LNEG; vREAL_MUL_RNEG]);;

let%a vCNJ_ADD = prove
 ([%q {|!w z. cnj(w + z) = cnj(w) + cnj(z)|} ],
  vREWRITE_TAC[cnj; complex_add; vCOMPLEX_EQ; vRE; vIM] ---->
  vREWRITE_TAC[vREAL_NEG_ADD; vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG]);;

let%a vCNJ_SUB = prove
 ([%q {|!w z. cnj(w - z) = cnj(w) - cnj(z)|} ],
  vREWRITE_TAC[complex_sub; vCNJ_ADD; vCNJ_NEG]);;

let%a vCNJ_MUL = prove
 ([%q {|!w z. cnj(w * z) = cnj(w) * cnj(z)|} ],
  vREWRITE_TAC[cnj; complex_mul; vCOMPLEX_EQ; vRE; vIM] ---->
  vREWRITE_TAC[vREAL_NEG_ADD; vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG]);;

let%a vCNJ_DIV = prove
 ([%q {|!w z. cnj(w / z) = cnj(w) / cnj(z)|} ],
  vREWRITE_TAC[complex_div; vCNJ_MUL; vCNJ_INV]);;

let%a vCNJ_POW = prove
 ([%q {|!z n. cnj(z pow n) = cnj(z) pow n|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[complex_pow; vCNJ_MUL; vCNJ_CX]);;

(* ------------------------------------------------------------------------- *)
(* Conversion of (complex-type) rational constant to ML rational number.     *)
(* ------------------------------------------------------------------------- *)

let is_complex_const =
  let cx_tm = [%q {|Cx|} ] in
  fun tm ->
    is_comb tm &&
    let l,r = dest_comb tm in l = cx_tm && is_ratconst r;;

let dest_complex_const =
  let cx_tm = [%q {|Cx|} ] in
  fun tm ->
    let l,r = dest_comb tm in
    if l = cx_tm then rat_of_term r
    else failwith "dest_complex_const";;

let mk_complex_const =
  let cx_tm = [%q {|Cx|} ] in
  fun r ->
    mk_comb(cx_tm,term_of_rat r);;

(* ------------------------------------------------------------------------- *)
(* Conversions to perform operations if coefficients are rational constants. *)
(* ------------------------------------------------------------------------- *)

let vCOMPLEX_RAT_MUL_CONV =
  vGEN_REWRITE_CONV vI [vGSYM vCX_MUL] +---> vRAND_CONV vREAL_RAT_MUL_CONV;;

let vCOMPLEX_RAT_ADD_CONV =
  vGEN_REWRITE_CONV vI [vGSYM vCX_ADD] +---> vRAND_CONV vREAL_RAT_ADD_CONV;;

let vCOMPLEX_RAT_EQ_CONV =
  vGEN_REWRITE_CONV vI [vCX_INJ] +---> vREAL_RAT_EQ_CONV;;

let vCOMPLEX_RAT_POW_CONV =
  let x_tm = [%q {|x:real|} ]
  and n_tm = [%q {|n:num|} ] in
  let pth = vSYM(vSPECL [x_tm; n_tm] vCX_POW) in
  fun tm ->
    let lop,r = dest_comb tm in
    let op,bod = dest_comb lop in
    let th1 = vINST [rand bod,x_tm; r,n_tm] pth in
    let tm1,tm2 = dest_comb(concl th1) in
    if rand tm1 <> tm then failwith "COMPLEX_RAT_POW_CONV" else
    let tm3,tm4 = dest_comb tm2 in
    vTRANS th1 (vAP_TERM tm3 (vREAL_RAT_REDUCE_CONV tm4));;

(* ------------------------------------------------------------------------- *)
(* Instantiate polynomial normalizer.                                        *)
(* ------------------------------------------------------------------------- *)

let vCOMPLEX_POLY_CLAUSES = prove
 ([%q {|(!x y z. x + (y + z) = (x + y) + z) /\
   (!x y. x + y = y + x) /\
   (!x. Cx(&0) + x = x) /\
   (!x y z. x * (y * z) = (x * y) * z) /\
   (!x y. x * y = y * x) /\
   (!x. Cx(&1) * x = x) /\
   (!x. Cx(&0) * x = Cx(&0)) /\
   (!x y z. x * (y + z) = x * y + x * z) /\
   (!x. x pow 0 = Cx(&1)) /\
   (!x n. x pow (SUC n) = x * x pow n)|} ],
  vREWRITE_TAC[complex_pow] ----> vSIMPLE_COMPLEX_ARITH_TAC)
and vCOMPLEX_POLY_NEG_CLAUSES = prove
 ([%q {|(!x. --x = Cx(-- &1) * x) /\
   (!x y. x - y = x + Cx(-- &1) * y)|} ],
  vSIMPLE_COMPLEX_ARITH_TAC);;

let vCOMPLEX_POLY_NEG_CONV,vCOMPLEX_POLY_ADD_CONV,vCOMPLEX_POLY_SUB_CONV,
    vCOMPLEX_POLY_MUL_CONV,vCOMPLEX_POLY_POW_CONV,vCOMPLEX_POLY_CONV =
  vSEMIRING_NORMALIZERS_CONV vCOMPLEX_POLY_CLAUSES vCOMPLEX_POLY_NEG_CLAUSES
   (is_complex_const,
    vCOMPLEX_RAT_ADD_CONV,vCOMPLEX_RAT_MUL_CONV,vCOMPLEX_RAT_POW_CONV)
   (<);;

let vCOMPLEX_RAT_INV_CONV =
  vGEN_REWRITE_CONV vI [vGSYM vCX_INV] +---> vRAND_CONV vREAL_RAT_INV_CONV;;

let vCOMPLEX_POLY_CONV =
  let neg_tm = [%q {|(--):complex->complex|} ]
  and inv_tm = [%q {|inv:complex->complex|} ]
  and add_tm = [%q {|(+):complex->complex->complex|} ]
  and sub_tm = [%q {|(-):complex->complex->complex|} ]
  and mul_tm = [%q {|(*):complex->complex->complex|} ]
  and div_tm = [%q {|(/):complex->complex->complex|} ]
  and pow_tm = [%q {|(pow):complex->num->complex|} ]
  and div_conv = vREWR_CONV complex_div in
  let rec vCOMPLEX_POLY_CONV tm =
    if not(is_comb tm) || is_complex_const tm then vREFL tm else
    let lop,r = dest_comb tm in
    if lop = neg_tm then
      let th1 = vAP_TERM lop (vCOMPLEX_POLY_CONV r) in
      vTRANS th1 (vCOMPLEX_POLY_NEG_CONV (rand(concl th1)))
    else if lop = inv_tm then
      let th1 = vAP_TERM lop (vCOMPLEX_POLY_CONV r) in
      vTRANS th1 (vTRY_CONV vCOMPLEX_RAT_INV_CONV (rand(concl th1)))
    else if not(is_comb lop) then vREFL tm else
    let op,l = dest_comb lop in
    if op = pow_tm then
      let th1 = vAP_THM (vAP_TERM op (vCOMPLEX_POLY_CONV l)) r in
      vTRANS th1 (vTRY_CONV vCOMPLEX_POLY_POW_CONV (rand(concl th1)))
    else if op = add_tm || op = mul_tm || op = sub_tm then
      let th1 = vMK_COMB(vAP_TERM op (vCOMPLEX_POLY_CONV l),
                        vCOMPLEX_POLY_CONV r) in
      let fn = if op = add_tm then vCOMPLEX_POLY_ADD_CONV
               else if op = mul_tm then vCOMPLEX_POLY_MUL_CONV
               else vCOMPLEX_POLY_SUB_CONV in
      vTRANS th1 (fn (rand(concl th1)))
    else if op = div_tm then
      let th1 = div_conv tm in
      vTRANS th1 (vCOMPLEX_POLY_CONV (rand(concl th1)))
    else vREFL tm in
  vCOMPLEX_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Complex number version of usual ring procedure.                           *)
(* ------------------------------------------------------------------------- *)

let%a vCOMPLEX_MUL_LINV = prove
 ([%q {|!z. ~(z = Cx(&0)) ==> (inv(z) * z = Cx(&1))|} ],
  vREWRITE_TAC[complex_mul; complex_inv; vRE; vIM; vCOMPLEX_EQ; vCX_DEF] ---->
  vREWRITE_TAC[vGSYM vREAL_SOS_EQ_0] ----> vCONV_TAC vREAL_FIELD);;

let%a vCOMPLEX_MUL_RINV = prove
 ([%q {|!z. ~(z = Cx(&0)) ==> (z * inv(z) = Cx(&1))|} ],
  vONCE_REWRITE_TAC[vCOMPLEX_MUL_SYM] ----> vREWRITE_TAC[vCOMPLEX_MUL_LINV]);;

let vCOMPLEX_RING,complex_ideal_cofactors =
  let ring_pow_tm = [%q {|(pow):complex->num->complex|} ]
  and vCOMPLEX_INTEGRAL = prove
   ([%q {|(!x. Cx(&0) * x = Cx(&0)) /\
     (!x y z. (x + y = x + z) <=> (y = z)) /\
     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \/ (y = z))|} ],
    vREWRITE_TAC[vCOMPLEX_ENTIRE; vSIMPLE_COMPLEX_ARITH
     [%q {|(w * y + x * z = w * z + x * y) <=>
      (w - x) * (y - z) = Cx(&0)|} ]] ---->
    vSIMPLE_COMPLEX_ARITH_TAC)
  and vCOMPLEX_RABINOWITSCH = prove
   ([%q {|!x y:complex. ~(x = y) <=> ?z. (x - y) * z = Cx(&1)|} ],
    vREPEAT vGEN_TAC ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vCOMPLEX_SUB_0] ---->
    vMESON_TAC[vCOMPLEX_MUL_RINV; vCOMPLEX_MUL_LZERO;
              vSIMPLE_COMPLEX_ARITH [%q {|~(Cx(&1) = Cx(&0))|} ]])
  and init = vALL_CONV in
  let pure,ideal =
    vRING_AND_IDEAL_CONV
        (dest_complex_const,mk_complex_const,vCOMPLEX_RAT_EQ_CONV,
         [%q {|(--):complex->complex|} ],[%q {|(+):complex->complex->complex|} ],
         [%q {|(-):complex->complex->complex|} ],[%q {|(inv):complex->complex|} ],
         [%q {|(*):complex->complex->complex|} ],[%q {|(/):complex->complex->complex|} ],
         [%q {|(pow):complex->num->complex|} ],
         vCOMPLEX_INTEGRAL,vCOMPLEX_RABINOWITSCH,vCOMPLEX_POLY_CONV) in
  (fun tm -> let th = init tm in vEQ_MP (vSYM th) (pure(rand(concl th)))),
  ideal;;

(* ------------------------------------------------------------------------- *)
(* Most basic properties of inverses.                                        *)
(* ------------------------------------------------------------------------- *)

let%a vCOMPLEX_INV_0 = prove
 ([%q {|inv(Cx(&0)) = Cx(&0)|} ],
  vREWRITE_TAC[complex_inv; vCX_DEF; vRE; vIM; real_div; vREAL_MUL_LZERO;
              vREAL_NEG_0]);;

let%a vCOMPLEX_INV_MUL = prove
 ([%q {|!w z. inv(w * z) = inv(w) * inv(z)|} ],
  vREPEAT vGEN_TAC ---->
  vMAP_EVERY vASM_CASES_TAC [[%q {|w = Cx(&0)|} ]; [%q {|z = Cx(&0)|} ]] ---->
  vASM_REWRITE_TAC[vCOMPLEX_INV_0; vCOMPLEX_MUL_LZERO; vCOMPLEX_MUL_RZERO] ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ---->
  vREWRITE_TAC[complex_mul; complex_inv; vRE; vIM; vCOMPLEX_EQ; vCX_DEF] ---->
  vREWRITE_TAC[vGSYM vREAL_SOS_EQ_0] ----> vCONV_TAC vREAL_FIELD);;

let%a vCOMPLEX_INV_1 = prove
 ([%q {|inv(Cx(&1)) = Cx(&1)|} ],
  vREWRITE_TAC[complex_inv; vCX_DEF; vRE; vIM] ---->
  vCONV_TAC vREAL_RAT_REDUCE_CONV ----> vREWRITE_TAC[vREAL_DIV_1]);;

let%a vCOMPLEX_POW_INV = prove
 ([%q {|!x n. (inv x) pow n = inv(x pow n)|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[complex_pow; vCOMPLEX_INV_1; vCOMPLEX_INV_MUL]);;

let%a vCOMPLEX_INV_INV = prove
 ([%q {|!x:complex. inv(inv x) = x|} ],
  vGEN_TAC ----> vASM_CASES_TAC [%q {|x = Cx(&0)|} ] ---->
  vASM_REWRITE_TAC[vCOMPLEX_INV_0] ---->
  vPOP_ASSUM vMP_TAC ---->
  vMAP_EVERY (fun t -> vMP_TAC(vSPEC t vCOMPLEX_MUL_RINV))
   [[%q {|x:complex|} ]; [%q {|inv(x):complex|} ]] ---->
  vCONV_TAC vCOMPLEX_RING);;

(* ------------------------------------------------------------------------- *)
(* And also field procedure.                                                 *)
(* ------------------------------------------------------------------------- *)

let vCOMPLEX_FIELD =
  let prenex_conv =
    vTOP_DEPTH_CONV vBETA_CONV +--->
    vPURE_REWRITE_CONV[vFORALL_SIMP; vEXISTS_SIMP; complex_div;
                      vCOMPLEX_INV_INV; vCOMPLEX_INV_MUL; vGSYM vREAL_POW_INV] +--->
    vNNFC_CONV +---> vDEPTH_BINOP_CONV [%q {|(/\)|} ] vCONDS_CELIM_CONV +--->
    vPRENEX_CONV
  and setup_conv = vNNF_CONV +---> vWEAK_CNF_CONV +---> vCONJ_CANON_CONV
  and is_inv =
    let inv_tm = [%q {|inv:complex->complex|} ]
    and is_div = is_binop [%q {|(/):complex->complex->complex|} ] in
    fun tm -> (is_div tm || (is_comb tm && rator tm = inv_tm)) &&
              not(is_complex_const(rand tm))
  and lemma_inv = vMESON[vCOMPLEX_MUL_RINV]
    [%q {|!x. x = Cx(&0) \/ x * inv(x) = Cx(&1)|} ]
  and dcases = vMATCH_MP(vTAUT [%q {|(p \/ q) /\ (r \/ s) ==> (p \/ r) \/ q /\ s|} ]) in
  let cases_rule th1 th2 = dcases (vCONJ th1 th2) in
  let vBASIC_COMPLEX_FIELD tm =
    let is_freeinv t = is_inv t && free_in t tm in
    let itms = setify(map rand (find_terms is_freeinv tm)) in
    let dth = if itms = [] then vTRUTH
              else end_itlist cases_rule (map (vC vSPEC lemma_inv) itms) in
    let tm' = mk_imp(concl dth,tm) in
    let th1 = setup_conv tm' in
    let ths = map vCOMPLEX_RING (conjuncts(rand(concl th1))) in
    let th2 = vEQ_MP (vSYM th1) (end_itlist vCONJ ths) in
    vMP (vEQ_MP (vSYM th1) (end_itlist vCONJ ths)) dth in
  fun tm ->
    let th0 = prenex_conv tm in
    let tm0 = rand(concl th0) in
    let avs,bod = strip_forall tm0 in
    let th1 = setup_conv bod in
    let ths = map vBASIC_COMPLEX_FIELD (conjuncts(rand(concl th1))) in
    vEQ_MP (vSYM th0) (vGENL avs (vEQ_MP (vSYM th1) (end_itlist vCONJ ths)));;

(* ------------------------------------------------------------------------- *)
(* Properties of inverses, divisions are now mostly automatic.               *)
(* ------------------------------------------------------------------------- *)

let%a vCOMPLEX_POW_DIV = prove
 ([%q {|!x y n. (x / y) pow n = (x pow n) / (y pow n)|} ],
  vREWRITE_TAC[complex_div; vCOMPLEX_POW_MUL; vCOMPLEX_POW_INV]);;

let%a vCOMPLEX_DIV_REFL = prove
 ([%q {|!x. ~(x = Cx(&0)) ==> (x / x = Cx(&1))|} ],
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vCOMPLEX_EQ_MUL_LCANCEL = prove
 ([%q {|!x y z. (x * y = x * z) <=> (x = Cx(&0)) \/ (y = z)|} ],
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vCOMPLEX_EQ_MUL_RCANCEL = prove
 ([%q {|!x y z. (x * z = y * z) <=> (x = y) \/ (z = Cx(&0))|} ],
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vCOMPLEX_MUL_RINV_UNIQ = prove
 ([%q {|!w z. w * z = Cx(&1) ==> inv w = z|} ],
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vCOMPLEX_MUL_LINV_UNIQ = prove
 ([%q {|!w z. w * z = Cx(&1) ==> inv z = w|} ],
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vCOMPLEX_DIV_LMUL = prove
 ([%q {|!w z. ~(z = Cx(&0)) ==> z * w / z = w|} ],
  vCONV_TAC vCOMPLEX_FIELD);;

let%a vCOMPLEX_DIV_RMUL = prove
 ([%q {|!w z. ~(z = Cx(&0)) ==> w / z * z = w|} ],
  vCONV_TAC vCOMPLEX_FIELD);;
