(* ========================================================================= *)
(* More basic properties of the reals.                                       *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*              (c) Copyright, Valentina Bruno 2010                          *)
(* ========================================================================= *)

open Lib
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
open Calc_int
open Realarith

(* ------------------------------------------------------------------------- *)
(* Additional commutativity properties of the inclusion map.                 *)
(* ------------------------------------------------------------------------- *)

let vREAL_OF_NUM_LT = try Cache.lookup_thm "REAL_OF_NUM_LT" with _ ->  prove
 ((parse_term "!m n. &m < &n <=> m < n"),
  vREWRITE_TAC[real_lt; vGSYM vNOT_LE; vREAL_OF_NUM_LE]);;

let vREAL_OF_NUM_GE = try Cache.lookup_thm "REAL_OF_NUM_GE" with _ ->  prove
 ((parse_term "!m n. &m >= &n <=> m >= n"),
  vREWRITE_TAC[vGE; real_ge; vREAL_OF_NUM_LE]);;

let vREAL_OF_NUM_GT = try Cache.lookup_thm "REAL_OF_NUM_GT" with _ ->  prove
 ((parse_term "!m n. &m > &n <=> m > n"),
  vREWRITE_TAC[vGT; real_gt; vREAL_OF_NUM_LT]);;

let vREAL_OF_NUM_MAX = try Cache.lookup_thm "REAL_OF_NUM_MAX" with _ ->  prove
 ((parse_term "!m n. max (&m) (&n) = &(MAX m n)"),
  vREWRITE_TAC[vREAL_OF_NUM_LE; vMAX; real_max; vGSYM vCOND_RAND]);;

let vREAL_OF_NUM_MIN = try Cache.lookup_thm "REAL_OF_NUM_MIN" with _ ->  prove
 ((parse_term "!m n. min (&m) (&n) = &(MIN m n)"),
  vREWRITE_TAC[vREAL_OF_NUM_LE; vMIN; real_min; vGSYM vCOND_RAND]);;

let vREAL_OF_NUM_SUC = try Cache.lookup_thm "REAL_OF_NUM_SUC" with _ ->  prove
 ((parse_term "!n. &n + &1 = &(SUC n)"),
  vREWRITE_TAC[vADD1; vREAL_OF_NUM_ADD]);;

let vREAL_OF_NUM_SUB = try Cache.lookup_thm "REAL_OF_NUM_SUB" with _ ->  prove
 ((parse_term "!m n. m <= n ==> (&n - &m = &(n - m))"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLE_EXISTS] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[vADD_SUB2] ---->
  vREWRITE_TAC[vGSYM vREAL_OF_NUM_ADD] ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vREWRITE_TAC[real_sub; vGSYM vREAL_ADD_ASSOC] ---->
  vMESON_TAC[vREAL_ADD_LINV; vREAL_ADD_SYM; vREAL_ADD_LID]);;

let vREAL_OF_NUM_SUB_CASES = try Cache.lookup_thm "REAL_OF_NUM_SUB_CASES" with _ ->  prove
 ((parse_term "!m n. &m - &n = if n <= m then &(m - n) else -- &(n - m)"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_SIMP_TAC[vREAL_OF_NUM_SUB] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_NEG_SUB] ----> vAP_TERM_TAC ---->
  vMATCH_MP_TAC vREAL_OF_NUM_SUB ----> vASM_MESON_TAC[vLE_CASES]);;

let vREAL_OF_NUM_CLAUSES = try Cache.lookup_thm "REAL_OF_NUM_CLAUSES" with _ ->  prove
 ((parse_term "(!m n. &m:real = &n <=> m = n) /\\\n   (!m n. &m:real >= &n <=> m >= n) /\\\n   (!m n. &m:real > &n <=> m > n) /\\\n   (!m n. &m:real <= &n <=> m <= n) /\\\n   (!m n. &m:real < &n <=> m < n) /\\\n   (!m n. max (&m) (&n):real = &(MAX m n)) /\\\n   (!m n. min (&m) (&n):real = &(MIN m n)) /\\\n   (!m n. &m + &n:real = &(m + n)) /\\\n   (!m n. &m * &n:real = &(m * n)) /\\\n   (!x n. (&x:real) pow n = &(x EXP n))"),
  vREWRITE_TAC[vREAL_OF_NUM_EQ; vREAL_OF_NUM_GE; vREAL_OF_NUM_GT;
              vREAL_OF_NUM_LE; vREAL_OF_NUM_LT; vREAL_OF_NUM_MAX;
              vREAL_OF_NUM_MIN; vREAL_OF_NUM_ADD; vREAL_OF_NUM_MUL;
              vREAL_OF_NUM_POW]);;

(* ------------------------------------------------------------------------- *)
(* A few theorems we need to prove explicitly for later.                     *)
(* ------------------------------------------------------------------------- *)

let vREAL_MUL_AC = try Cache.lookup_thm "REAL_MUL_AC" with _ ->  prove
 ((parse_term "(m * n = n * m) /\\\n   ((m * n) * p = m * (n * p)) /\\\n   (m * (n * p) = n * (m * p))"),
  vREWRITE_TAC[vREAL_MUL_ASSOC; vEQT_INTRO(vSPEC_ALL vREAL_MUL_SYM)] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vMATCH_ACCEPT_TAC vREAL_MUL_SYM);;

let vREAL_ADD_RDISTRIB = try Cache.lookup_thm "REAL_ADD_RDISTRIB" with _ ->  prove
 ((parse_term "!x y z. (x + y) * z = x * z + y * z"),
  vMESON_TAC[vREAL_MUL_SYM; vREAL_ADD_LDISTRIB]);;

let vREAL_LT_LADD_IMP = try Cache.lookup_thm "REAL_LT_LADD_IMP" with _ ->  prove
 ((parse_term "!x y z. y < z ==> x + y < x + z"),
  vREPEAT vGEN_TAC ----> vCONV_TAC vCONTRAPOS_CONV ---->
  vREWRITE_TAC[real_lt] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LE_LADD_IMP) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "--x")) ---->
  vREWRITE_TAC[vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_LID]);;

let vREAL_LT_MUL = try Cache.lookup_thm "REAL_LT_MUL" with _ ->  prove
 ((parse_term "!x y. &0 < x /\\ &0 < y ==> &0 < x * y"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_LT_LE] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[vREAL_ENTIRE] ---->
  vMATCH_MP_TAC vREAL_LE_MUL ----> vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tactic version of REAL_ARITH.                                             *)
(* ------------------------------------------------------------------------- *)

let vREAL_ARITH_TAC = vCONV_TAC vREAL_ARITH;;

(* ------------------------------------------------------------------------- *)
(* Prove all the linear theorems we can blow away automatically.             *)
(* ------------------------------------------------------------------------- *)

let vREAL_EQ_ADD_LCANCEL_0 = try Cache.lookup_thm "REAL_EQ_ADD_LCANCEL_0" with _ ->  prove
 ((parse_term "!x y. (x + y = x) <=> (y = &0)"),
  vREAL_ARITH_TAC);;

let vREAL_EQ_ADD_RCANCEL_0 = try Cache.lookup_thm "REAL_EQ_ADD_RCANCEL_0" with _ ->  prove
 ((parse_term "!x y. (x + y = y) <=> (x = &0)"),
  vREAL_ARITH_TAC);;

let vREAL_LNEG_UNIQ = try Cache.lookup_thm "REAL_LNEG_UNIQ" with _ ->  prove
 ((parse_term "!x y. (x + y = &0) <=> (x = --y)"),
  vREAL_ARITH_TAC);;

let vREAL_RNEG_UNIQ = try Cache.lookup_thm "REAL_RNEG_UNIQ" with _ ->  prove
 ((parse_term "!x y. (x + y = &0) <=> (y = --x)"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_LMUL = try Cache.lookup_thm "REAL_NEG_LMUL" with _ ->  prove
 ((parse_term "!x y. --(x * y) = (--x) * y"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_RMUL = try Cache.lookup_thm "REAL_NEG_RMUL" with _ ->  prove
 ((parse_term "!x y. --(x * y) = x * (--y)"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_MUL2 = try Cache.lookup_thm "REAL_NEG_MUL2" with _ ->  prove
 ((parse_term "!x y. (--x) * (--y) = x * y"),
  vREAL_ARITH_TAC);;

let vREAL_LT_LADD = try Cache.lookup_thm "REAL_LT_LADD" with _ ->  prove
 ((parse_term "!x y z. (x + y) < (x + z) <=> y < z"),
  vREAL_ARITH_TAC);;

let vREAL_LT_RADD = try Cache.lookup_thm "REAL_LT_RADD" with _ ->  prove
 ((parse_term "!x y z. (x + z) < (y + z) <=> x < y"),
  vREAL_ARITH_TAC);;

let vREAL_LT_ANTISYM = try Cache.lookup_thm "REAL_LT_ANTISYM" with _ ->  prove
 ((parse_term "!x y. ~(x < y /\\ y < x)"),
  vREAL_ARITH_TAC);;

let vREAL_LT_GT = try Cache.lookup_thm "REAL_LT_GT" with _ ->  prove
 ((parse_term "!x y. x < y ==> ~(y < x)"),
  vREAL_ARITH_TAC);;

let vREAL_NOT_EQ = try Cache.lookup_thm "REAL_NOT_EQ" with _ ->  prove
 ((parse_term "!x y. ~(x = y) <=> x < y \\/ y < x"),
  vREAL_ARITH_TAC);;

let vREAL_NOT_LE = try Cache.lookup_thm "REAL_NOT_LE" with _ ->  prove
 ((parse_term "!x y. ~(x <= y) <=> y < x"),
  vREAL_ARITH_TAC);;

let vREAL_LET_ANTISYM = try Cache.lookup_thm "REAL_LET_ANTISYM" with _ ->  prove
 ((parse_term "!x y. ~(x <= y /\\ y < x)"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_LT0 = try Cache.lookup_thm "REAL_NEG_LT0" with _ ->  prove
 ((parse_term "!x. (--x) < &0 <=> &0 < x"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_GT0 = try Cache.lookup_thm "REAL_NEG_GT0" with _ ->  prove
 ((parse_term "!x. &0 < (--x) <=> x < &0"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_LE0 = try Cache.lookup_thm "REAL_NEG_LE0" with _ ->  prove
 ((parse_term "!x. (--x) <= &0 <=> &0 <= x"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_GE0 = try Cache.lookup_thm "REAL_NEG_GE0" with _ ->  prove
 ((parse_term "!x. &0 <= (--x) <=> x <= &0"),
  vREAL_ARITH_TAC);;

let vREAL_LT_TOTAL = try Cache.lookup_thm "REAL_LT_TOTAL" with _ ->  prove
 ((parse_term "!x y. (x = y) \\/ x < y \\/ y < x"),
  vREAL_ARITH_TAC);;

let vREAL_LT_NEGTOTAL = try Cache.lookup_thm "REAL_LT_NEGTOTAL" with _ ->  prove
 ((parse_term "!x. (x = &0) \\/ (&0 < x) \\/ (&0 < --x)"),
  vREAL_ARITH_TAC);;

let vREAL_LE_01 = try Cache.lookup_thm "REAL_LE_01" with _ ->  prove
 ((parse_term "&0 <= &1"),
  vREAL_ARITH_TAC);;

let vREAL_LT_01 = try Cache.lookup_thm "REAL_LT_01" with _ ->  prove
 ((parse_term "&0 < &1"),
  vREAL_ARITH_TAC);;

let vREAL_LE_LADD = try Cache.lookup_thm "REAL_LE_LADD" with _ ->  prove
 ((parse_term "!x y z. (x + y) <= (x + z) <=> y <= z"),
  vREAL_ARITH_TAC);;

let vREAL_LE_RADD = try Cache.lookup_thm "REAL_LE_RADD" with _ ->  prove
 ((parse_term "!x y z. (x + z) <= (y + z) <=> x <= y"),
  vREAL_ARITH_TAC);;

let vREAL_LT_ADD2 = try Cache.lookup_thm "REAL_LT_ADD2" with _ ->  prove
 ((parse_term "!w x y z. w < x /\\ y < z ==> (w + y) < (x + z)"),
  vREAL_ARITH_TAC);;

let vREAL_LE_ADD2 = try Cache.lookup_thm "REAL_LE_ADD2" with _ ->  prove
 ((parse_term "!w x y z. w <= x /\\ y <= z ==> (w + y) <= (x + z)"),
  vREAL_ARITH_TAC);;

let vREAL_LT_LNEG = try Cache.lookup_thm "REAL_LT_LNEG" with _ ->  prove
 ((parse_term "!x y. --x < y <=> &0 < x + y"),
  vREWRITE_TAC[real_lt; vREAL_LE_RNEG; vREAL_ADD_AC]);;

let vREAL_LT_RNEG = try Cache.lookup_thm "REAL_LT_RNEG" with _ ->  prove
 ((parse_term "!x y. x < --y <=> x + y < &0"),
  vREWRITE_TAC[real_lt; vREAL_LE_LNEG; vREAL_ADD_AC]);;

let vREAL_LT_ADDNEG = try Cache.lookup_thm "REAL_LT_ADDNEG" with _ ->  prove
 ((parse_term "!x y z. y < (x + (--z)) <=> (y + z) < x"),
  vREAL_ARITH_TAC);;

let vREAL_LT_ADDNEG2 = try Cache.lookup_thm "REAL_LT_ADDNEG2" with _ ->  prove
 ((parse_term "!x y z. (x + (--y)) < z <=> x < (z + y)"),
  vREAL_ARITH_TAC);;

let vREAL_LT_ADD1 = try Cache.lookup_thm "REAL_LT_ADD1" with _ ->  prove
 ((parse_term "!x y. x <= y ==> x < (y + &1)"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_ADD = try Cache.lookup_thm "REAL_SUB_ADD" with _ ->  prove
 ((parse_term "!x y. (x - y) + y = x"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_ADD2 = try Cache.lookup_thm "REAL_SUB_ADD2" with _ ->  prove
 ((parse_term "!x y. y + (x - y) = x"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_REFL = try Cache.lookup_thm "REAL_SUB_REFL" with _ ->  prove
 ((parse_term "!x. x - x = &0"),
  vREAL_ARITH_TAC);;

let vREAL_LE_DOUBLE = try Cache.lookup_thm "REAL_LE_DOUBLE" with _ ->  prove
 ((parse_term "!x. &0 <= x + x <=> &0 <= x"),
  vREAL_ARITH_TAC);;

let vREAL_LE_NEGL = try Cache.lookup_thm "REAL_LE_NEGL" with _ ->  prove
 ((parse_term "!x. (--x <= x) <=> (&0 <= x)"),
  vREAL_ARITH_TAC);;

let vREAL_LE_NEGR = try Cache.lookup_thm "REAL_LE_NEGR" with _ ->  prove
 ((parse_term "!x. (x <= --x) <=> (x <= &0)"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_EQ_0 = try Cache.lookup_thm "REAL_NEG_EQ_0" with _ ->  prove
 ((parse_term "!x. (--x = &0) <=> (x = &0)"),
  vREAL_ARITH_TAC);;

let vREAL_ADD_SUB = try Cache.lookup_thm "REAL_ADD_SUB" with _ ->  prove
 ((parse_term "!x y. (x + y) - x = y"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_EQ = try Cache.lookup_thm "REAL_NEG_EQ" with _ ->  prove
 ((parse_term "!x y. (--x = y) <=> (x = --y)"),
  vREAL_ARITH_TAC);;

let vREAL_NEG_MINUS1 = try Cache.lookup_thm "REAL_NEG_MINUS1" with _ ->  prove
 ((parse_term "!x. --x = (--(&1)) * x"),
  vREAL_ARITH_TAC);;

let vREAL_LT_IMP_NE = try Cache.lookup_thm "REAL_LT_IMP_NE" with _ ->  prove
 ((parse_term "!x y. x < y ==> ~(x = y)"),
  vREAL_ARITH_TAC);;

let vREAL_LE_ADDR = try Cache.lookup_thm "REAL_LE_ADDR" with _ ->  prove
 ((parse_term "!x y. x <= x + y <=> &0 <= y"),
  vREAL_ARITH_TAC);;

let vREAL_LE_ADDL = try Cache.lookup_thm "REAL_LE_ADDL" with _ ->  prove
 ((parse_term "!x y. y <= x + y <=> &0 <= x"),
  vREAL_ARITH_TAC);;

let vREAL_LT_ADDR = try Cache.lookup_thm "REAL_LT_ADDR" with _ ->  prove
 ((parse_term "!x y. x < x + y <=> &0 < y"),
  vREAL_ARITH_TAC);;

let vREAL_LT_ADDL = try Cache.lookup_thm "REAL_LT_ADDL" with _ ->  prove
 ((parse_term "!x y. y < x + y <=> &0 < x"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_SUB = try Cache.lookup_thm "REAL_SUB_SUB" with _ ->  prove
 ((parse_term "!x y. (x - y) - x = --y"),
  vREAL_ARITH_TAC);;

let vREAL_LT_ADD_SUB = try Cache.lookup_thm "REAL_LT_ADD_SUB" with _ ->  prove
 ((parse_term "!x y z. (x + y) < z <=> x < (z - y)"),
  vREAL_ARITH_TAC);;

let vREAL_LT_SUB_RADD = try Cache.lookup_thm "REAL_LT_SUB_RADD" with _ ->  prove
 ((parse_term "!x y z. (x - y) < z <=> x < z + y"),
  vREAL_ARITH_TAC);;

let vREAL_LT_SUB_LADD = try Cache.lookup_thm "REAL_LT_SUB_LADD" with _ ->  prove
 ((parse_term "!x y z. x < (y - z) <=> (x + z) < y"),
  vREAL_ARITH_TAC);;

let vREAL_LE_SUB_LADD = try Cache.lookup_thm "REAL_LE_SUB_LADD" with _ ->  prove
 ((parse_term "!x y z. x <= (y - z) <=> (x + z) <= y"),
  vREAL_ARITH_TAC);;

let vREAL_LE_SUB_RADD = try Cache.lookup_thm "REAL_LE_SUB_RADD" with _ ->  prove
 ((parse_term "!x y z. (x - y) <= z <=> x <= z + y"),
  vREAL_ARITH_TAC);;

let vREAL_ADD2_SUB2 = try Cache.lookup_thm "REAL_ADD2_SUB2" with _ ->  prove
 ((parse_term "!a b c d. (a + b) - (c + d) = (a - c) + (b - d)"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_LZERO = try Cache.lookup_thm "REAL_SUB_LZERO" with _ ->  prove
 ((parse_term "!x. &0 - x = --x"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_RZERO = try Cache.lookup_thm "REAL_SUB_RZERO" with _ ->  prove
 ((parse_term "!x. x - &0 = x"),
  vREAL_ARITH_TAC);;

let vREAL_LET_ADD2 = try Cache.lookup_thm "REAL_LET_ADD2" with _ ->  prove
 ((parse_term "!w x y z. w <= x /\\ y < z ==> (w + y) < (x + z)"),
  vREAL_ARITH_TAC);;

let vREAL_LTE_ADD2 = try Cache.lookup_thm "REAL_LTE_ADD2" with _ ->  prove
 ((parse_term "!w x y z. w < x /\\ y <= z ==> w + y < x + z"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_LNEG = try Cache.lookup_thm "REAL_SUB_LNEG" with _ ->  prove
 ((parse_term "!x y. (--x) - y = --(x + y)"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_RNEG = try Cache.lookup_thm "REAL_SUB_RNEG" with _ ->  prove
 ((parse_term "!x y. x - (--y) = x + y"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_NEG2 = try Cache.lookup_thm "REAL_SUB_NEG2" with _ ->  prove
 ((parse_term "!x y. (--x) - (--y) = y - x"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_TRIANGLE = try Cache.lookup_thm "REAL_SUB_TRIANGLE" with _ ->  prove
 ((parse_term "!a b c. (a - b) + (b - c) = a - c"),
  vREAL_ARITH_TAC);;

let vREAL_EQ_SUB_LADD = try Cache.lookup_thm "REAL_EQ_SUB_LADD" with _ ->  prove
 ((parse_term "!x y z. (x = y - z) <=> (x + z = y)"),
  vREAL_ARITH_TAC);;

let vREAL_EQ_SUB_RADD = try Cache.lookup_thm "REAL_EQ_SUB_RADD" with _ ->  prove
 ((parse_term "!x y z. (x - y = z) <=> (x = z + y)"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_SUB2 = try Cache.lookup_thm "REAL_SUB_SUB2" with _ ->  prove
 ((parse_term "!x y. x - (x - y) = y"),
  vREAL_ARITH_TAC);;

let vREAL_ADD_SUB2 = try Cache.lookup_thm "REAL_ADD_SUB2" with _ ->  prove
 ((parse_term "!x y. x - (x + y) = --y"),
  vREAL_ARITH_TAC);;

let vREAL_EQ_IMP_LE = try Cache.lookup_thm "REAL_EQ_IMP_LE" with _ ->  prove
 ((parse_term "!x y. (x = y) ==> x <= y"),
  vREAL_ARITH_TAC);;

let vREAL_LT_IMP_NZ = try Cache.lookup_thm "REAL_LT_IMP_NZ" with _ ->  prove
 ((parse_term "!x. &0 < x ==> ~(x = &0)"),
  vREAL_ARITH_TAC);;

let vREAL_DIFFSQ = try Cache.lookup_thm "REAL_DIFFSQ" with _ ->  prove
 ((parse_term "!x y. (x + y) * (x - y) = (x * x) - (y * y)"),
  vREAL_ARITH_TAC);;

let vREAL_EQ_NEG2 = try Cache.lookup_thm "REAL_EQ_NEG2" with _ ->  prove
 ((parse_term "!x y. (--x = --y) <=> (x = y)"),
  vREAL_ARITH_TAC);;

let vREAL_LT_NEG2 = try Cache.lookup_thm "REAL_LT_NEG2" with _ ->  prove
 ((parse_term "!x y. --x < --y <=> y < x"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_LDISTRIB = try Cache.lookup_thm "REAL_SUB_LDISTRIB" with _ ->  prove
 ((parse_term "!x y z. x * (y - z) = x * y - x * z"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_RDISTRIB = try Cache.lookup_thm "REAL_SUB_RDISTRIB" with _ ->  prove
 ((parse_term "!x y z. (x - y) * z = x * z - y * z"),
  vREAL_ARITH_TAC);;

let vREAL_OF_NUM_MOD = try Cache.lookup_thm "REAL_OF_NUM_MOD" with _ ->  prove
 ((parse_term "!m n. &(m MOD n):real = &m - &(m DIV n) * &n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_EQ_SUB_LADD] ---->
  vREWRITE_TAC[vREAL_OF_NUM_CLAUSES] ---->
  vMESON_TAC[vDIVISION_SIMP; vADD_SYM]);;

(* ------------------------------------------------------------------------- *)
(* Theorems about "abs".                                                     *)
(* ------------------------------------------------------------------------- *)

let vREAL_ABS_ZERO = try Cache.lookup_thm "REAL_ABS_ZERO" with _ ->  prove
 ((parse_term "!x. (abs(x) = &0) <=> (x = &0)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_0 = try Cache.lookup_thm "REAL_ABS_0" with _ ->  prove
 ((parse_term "abs(&0) = &0"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_1 = try Cache.lookup_thm "REAL_ABS_1" with _ ->  prove
 ((parse_term "abs(&1) = &1"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_TRIANGLE = try Cache.lookup_thm "REAL_ABS_TRIANGLE" with _ ->  prove
 ((parse_term "!x y. abs(x + y) <= abs(x) + abs(y)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_TRIANGLE_LE = try Cache.lookup_thm "REAL_ABS_TRIANGLE_LE" with _ ->  prove
 ((parse_term "!x y z.abs(x) + abs(y - x) <= z ==> abs(y) <= z"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_TRIANGLE_LT = try Cache.lookup_thm "REAL_ABS_TRIANGLE_LT" with _ ->  prove
 ((parse_term "!x y z.abs(x) + abs(y - x) < z ==> abs(y) < z"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_POS = try Cache.lookup_thm "REAL_ABS_POS" with _ ->  prove
 ((parse_term "!x. &0 <= abs(x)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_SUB = try Cache.lookup_thm "REAL_ABS_SUB" with _ ->  prove
 ((parse_term "!x y. abs(x - y) = abs(y - x)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_NZ = try Cache.lookup_thm "REAL_ABS_NZ" with _ ->  prove
 ((parse_term "!x. ~(x = &0) <=> &0 < abs(x)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_ABS = try Cache.lookup_thm "REAL_ABS_ABS" with _ ->  prove
 ((parse_term "!x. abs(abs(x)) = abs(x)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_LE = try Cache.lookup_thm "REAL_ABS_LE" with _ ->  prove
 ((parse_term "!x. x <= abs(x)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_REFL = try Cache.lookup_thm "REAL_ABS_REFL" with _ ->  prove
 ((parse_term "!x. (abs(x) = x) <=> &0 <= x"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_BETWEEN = try Cache.lookup_thm "REAL_ABS_BETWEEN" with _ ->  prove
 ((parse_term "!x y d. &0 < d /\\ ((x - d) < y) /\\ (y < (x + d)) <=> abs(y - x) < d"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_BOUND = try Cache.lookup_thm "REAL_ABS_BOUND" with _ ->  prove
 ((parse_term "!x y d. abs(x - y) < d ==> y < (x + d)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_STILLNZ = try Cache.lookup_thm "REAL_ABS_STILLNZ" with _ ->  prove
 ((parse_term "!x y. abs(x - y) < abs(y) ==> ~(x = &0)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_CASES = try Cache.lookup_thm "REAL_ABS_CASES" with _ ->  prove
 ((parse_term "!x. (x = &0) \\/ &0 < abs(x)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_BETWEEN1 = try Cache.lookup_thm "REAL_ABS_BETWEEN1" with _ ->  prove
 ((parse_term "!x y z. x < z /\\ (abs(y - x)) < (z - x) ==> y < z"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_SIGN = try Cache.lookup_thm "REAL_ABS_SIGN" with _ ->  prove
 ((parse_term "!x y. abs(x - y) < y ==> &0 < x"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_SIGN2 = try Cache.lookup_thm "REAL_ABS_SIGN2" with _ ->  prove
 ((parse_term "!x y. abs(x - y) < --y ==> x < &0"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_CIRCLE = try Cache.lookup_thm "REAL_ABS_CIRCLE" with _ ->  prove
 ((parse_term "!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)"),
  vREAL_ARITH_TAC);;

let vREAL_SUB_ABS = try Cache.lookup_thm "REAL_SUB_ABS" with _ ->  prove
 ((parse_term "!x y. (abs(x) - abs(y)) <= abs(x - y)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_SUB_ABS = try Cache.lookup_thm "REAL_ABS_SUB_ABS" with _ ->  prove
 ((parse_term "!x y. abs(abs(x) - abs(y)) <= abs(x - y)"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_BETWEEN2 = try Cache.lookup_thm "REAL_ABS_BETWEEN2" with _ ->  prove
 ((parse_term "!x0 x y0 y. x0 < y0 /\\ &2 * abs(x - x0) < (y0 - x0) /\\\n                          &2 * abs(y - y0) < (y0 - x0)\n        ==> x < y"),
  vREAL_ARITH_TAC);;

let vREAL_ABS_BOUNDS = try Cache.lookup_thm "REAL_ABS_BOUNDS" with _ ->  prove
 ((parse_term "!x k. abs(x) <= k <=> --k <= x /\\ x <= k"),
  vREAL_ARITH_TAC);;

let vREAL_BOUNDS_LE = try Cache.lookup_thm "REAL_BOUNDS_LE" with _ ->  prove
 ((parse_term "!x k. --k <= x /\\ x <= k <=> abs(x) <= k"),
  vREAL_ARITH_TAC);;

let vREAL_BOUNDS_LT = try Cache.lookup_thm "REAL_BOUNDS_LT" with _ ->  prove
 ((parse_term "!x k. --k < x /\\ x < k <=> abs(x) < k"),
  vREAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Theorems about max and min.                                               *)
(* ------------------------------------------------------------------------- *)

let vREAL_MIN_MAX = try Cache.lookup_thm "REAL_MIN_MAX" with _ ->  prove
 ((parse_term "!x y. min x y = --(max (--x) (--y))"),
  vREAL_ARITH_TAC);;

let vREAL_MAX_MIN = try Cache.lookup_thm "REAL_MAX_MIN" with _ ->  prove
 ((parse_term "!x y. max x y = --(min (--x) (--y))"),
  vREAL_ARITH_TAC);;

let vREAL_MAX_MAX = try Cache.lookup_thm "REAL_MAX_MAX" with _ ->  prove
 ((parse_term "!x y. x <= max x y /\\ y <= max x y"),
  vREAL_ARITH_TAC);;

let vREAL_MIN_MIN = try Cache.lookup_thm "REAL_MIN_MIN" with _ ->  prove
 ((parse_term "!x y. min x y <= x /\\ min x y <= y"),
  vREAL_ARITH_TAC);;

let vREAL_MAX_SYM = try Cache.lookup_thm "REAL_MAX_SYM" with _ ->  prove
 ((parse_term "!x y. max x y = max y x"),
  vREAL_ARITH_TAC);;

let vREAL_MIN_SYM = try Cache.lookup_thm "REAL_MIN_SYM" with _ ->  prove
 ((parse_term "!x y. min x y = min y x"),
  vREAL_ARITH_TAC);;

let vREAL_LE_MAX = try Cache.lookup_thm "REAL_LE_MAX" with _ ->  prove
 ((parse_term "!x y z. z <= max x y <=> z <= x \\/ z <= y"),
  vREAL_ARITH_TAC);;

let vREAL_LE_MIN = try Cache.lookup_thm "REAL_LE_MIN" with _ ->  prove
 ((parse_term "!x y z. z <= min x y <=> z <= x /\\ z <= y"),
  vREAL_ARITH_TAC);;

let vREAL_LT_MAX = try Cache.lookup_thm "REAL_LT_MAX" with _ ->  prove
 ((parse_term "!x y z. z < max x y <=> z < x \\/ z < y"),
  vREAL_ARITH_TAC);;

let vREAL_LT_MIN = try Cache.lookup_thm "REAL_LT_MIN" with _ ->  prove
 ((parse_term "!x y z. z < min x y <=> z < x /\\ z < y"),
  vREAL_ARITH_TAC);;

let vREAL_MAX_LE = try Cache.lookup_thm "REAL_MAX_LE" with _ ->  prove
 ((parse_term "!x y z. max x y <= z <=> x <= z /\\ y <= z"),
  vREAL_ARITH_TAC);;

let vREAL_MIN_LE = try Cache.lookup_thm "REAL_MIN_LE" with _ ->  prove
 ((parse_term "!x y z. min x y <= z <=> x <= z \\/ y <= z"),
  vREAL_ARITH_TAC);;

let vREAL_MAX_LT = try Cache.lookup_thm "REAL_MAX_LT" with _ ->  prove
 ((parse_term "!x y z. max x y < z <=> x < z /\\ y < z"),
  vREAL_ARITH_TAC);;

let vREAL_MIN_LT = try Cache.lookup_thm "REAL_MIN_LT" with _ ->  prove
 ((parse_term "!x y z. min x y < z <=> x < z \\/ y < z"),
  vREAL_ARITH_TAC);;

let vREAL_MAX_ASSOC = try Cache.lookup_thm "REAL_MAX_ASSOC" with _ ->  prove
 ((parse_term "!x y z. max x (max y z) = max (max x y) z"),
  vREAL_ARITH_TAC);;

let vREAL_MIN_ASSOC = try Cache.lookup_thm "REAL_MIN_ASSOC" with _ ->  prove
 ((parse_term "!x y z. min x (min y z) = min (min x y) z"),
  vREAL_ARITH_TAC);;

let vREAL_MAX_ACI = try Cache.lookup_thm "REAL_MAX_ACI" with _ ->  prove
 ((parse_term "(max x y = max y x) /\\\n   (max (max x y) z = max x (max y z)) /\\\n   (max x (max y z) = max y (max x z)) /\\\n   (max x x = x) /\\\n   (max x (max x y) = max x y)"),
  vREAL_ARITH_TAC);;

let vREAL_MIN_ACI = try Cache.lookup_thm "REAL_MIN_ACI" with _ ->  prove
 ((parse_term "(min x y = min y x) /\\\n   (min (min x y) z = min x (min y z)) /\\\n   (min x (min y z) = min y (min x z)) /\\\n   (min x x = x) /\\\n   (min x (min x y) = min x y)"),
  vREAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* To simplify backchaining, just as in the natural number case.             *)
(* ------------------------------------------------------------------------- *)

let vREAL_LE_IMP =
  let pth = vPURE_ONCE_REWRITE_RULE[vIMP_CONJ] vREAL_LE_TRANS in
  fun th -> vGEN_ALL(vMATCH_MP pth (vSPEC_ALL th));;

let vREAL_LET_IMP =
  let pth = vPURE_ONCE_REWRITE_RULE[vIMP_CONJ] vREAL_LET_TRANS in
  fun th -> vGEN_ALL(vMATCH_MP pth (vSPEC_ALL th));;

(* ------------------------------------------------------------------------- *)
(* Now a bit of nonlinear stuff.                                             *)
(* ------------------------------------------------------------------------- *)

let vREAL_ABS_MUL = try Cache.lookup_thm "REAL_ABS_MUL" with _ ->  prove
 ((parse_term "!x y. abs(x * y) = abs(x) * abs(y)"),
  vREPEAT vGEN_TAC ---->
  vDISJ_CASES_TAC (vSPEC (parse_term "x:real") vREAL_LE_NEGTOTAL) ++-->
   [vALL_TAC;
    vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vGSYM vREAL_ABS_NEG]] ---->
  (vDISJ_CASES_TAC (vSPEC (parse_term "y:real") vREAL_LE_NEGTOTAL) ++-->
    [vALL_TAC;
     vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vGSYM vREAL_ABS_NEG]]) ---->
  vASSUM_LIST(vMP_TAC -| vMATCH_MP vREAL_LE_MUL -| end_itlist vCONJ -| rev) ---->
  vREWRITE_TAC[vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG] ----> vDISCH_TAC ++-->
   [vALL_TAC;
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_ABS_NEG];
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_ABS_NEG];
    vALL_TAC] ---->
  vASM_REWRITE_TAC[real_abs; vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG]);;

let vREAL_POW_LE = try Cache.lookup_thm "REAL_POW_LE" with _ ->  prove
 ((parse_term "!x n. &0 <= x ==> &0 <= x pow n"),
  vREPEAT vSTRIP_TAC ----> vSPEC_TAC((parse_term "n:num"),(parse_term "n:num")) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[real_pow; vREAL_POS] ---->
  vMATCH_MP_TAC vREAL_LE_MUL ----> vASM_REWRITE_TAC[]);;

let vREAL_POW_LT = try Cache.lookup_thm "REAL_POW_LT" with _ ->  prove
 ((parse_term "!x n. &0 < x ==> &0 < x pow n"),
  vREPEAT vSTRIP_TAC ----> vSPEC_TAC((parse_term "n:num"),(parse_term "n:num")) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[real_pow; vREAL_LT_01] ---->
  vMATCH_MP_TAC vREAL_LT_MUL ----> vASM_REWRITE_TAC[]);;

let vREAL_ABS_POW = try Cache.lookup_thm "REAL_ABS_POW" with _ ->  prove
 ((parse_term "!x n. abs(x pow n) = abs(x) pow n"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[real_pow; vREAL_ABS_NUM; vREAL_ABS_MUL]);;

let vREAL_LE_LMUL = try Cache.lookup_thm "REAL_LE_LMUL" with _ ->  prove
 ((parse_term "!x y z. &0 <= x /\\ y <= z ==> x * y <= x * z"),
  vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "x <= y <=> &0 <= y - x")] ---->
  vREWRITE_TAC[vGSYM vREAL_SUB_LDISTRIB; vREAL_SUB_RZERO; vREAL_LE_MUL]);;

let vREAL_LE_RMUL = try Cache.lookup_thm "REAL_LE_RMUL" with _ ->  prove
 ((parse_term "!x y z. x <= y /\\ &0 <= z ==> x * z <= y * z"),
  vMESON_TAC[vREAL_MUL_SYM; vREAL_LE_LMUL]);;

let vREAL_LT_LMUL = try Cache.lookup_thm "REAL_LT_LMUL" with _ ->  prove
 ((parse_term "!x y z. &0 < x /\\ y < z ==> x * y < x * z"),
  vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "x < y <=> &0 < y - x")] ---->
  vREWRITE_TAC[vGSYM vREAL_SUB_LDISTRIB; vREAL_SUB_RZERO; vREAL_LT_MUL]);;

let vREAL_LT_RMUL = try Cache.lookup_thm "REAL_LT_RMUL" with _ ->  prove
 ((parse_term "!x y z. x < y /\\ &0 < z ==> x * z < y * z"),
  vMESON_TAC[vREAL_MUL_SYM; vREAL_LT_LMUL]);;

let vREAL_EQ_MUL_LCANCEL = try Cache.lookup_thm "REAL_EQ_MUL_LCANCEL" with _ ->  prove
 ((parse_term "!x y z. (x * y = x * z) <=> (x = &0) \\/ (y = z)"),
  vREPEAT vGEN_TAC ---->
  vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "(x = y) <=> (x - y = &0)")] ---->
  vREWRITE_TAC[vGSYM vREAL_SUB_LDISTRIB; vREAL_ENTIRE; vREAL_SUB_RZERO]);;

let vREAL_EQ_MUL_RCANCEL = try Cache.lookup_thm "REAL_EQ_MUL_RCANCEL" with _ ->  prove
 ((parse_term "!x y z. (x * z = y * z) <=> (x = y) \\/ (z = &0)"),
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vREAL_EQ_MUL_LCANCEL] ---->
  vMESON_TAC[]);;

let vREAL_MUL_LINV_UNIQ = try Cache.lookup_thm "REAL_MUL_LINV_UNIQ" with _ ->  prove
 ((parse_term "!x y. (x * y = &1) ==> (inv(y) = x)"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "y = &0") ---->
  vASM_REWRITE_TAC[vREAL_MUL_RZERO; vREAL_OF_NUM_EQ; vARITH_EQ] ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vSYM -| vMATCH_MP vREAL_MUL_LINV) ---->
  vASM_REWRITE_TAC[vREAL_EQ_MUL_RCANCEL] ---->
  vDISCH_THEN(vACCEPT_TAC -| vSYM));;

let vREAL_MUL_RINV_UNIQ = try Cache.lookup_thm "REAL_MUL_RINV_UNIQ" with _ ->  prove
 ((parse_term "!x y. (x * y = &1) ==> (inv(x) = y)"),
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_MUL_LINV_UNIQ);;

let vREAL_INV_INV = try Cache.lookup_thm "REAL_INV_INV" with _ ->  prove
 ((parse_term "!x. inv(inv x) = x"),
  vGEN_TAC ----> vASM_CASES_TAC (parse_term "x = &0") ---->
  vASM_REWRITE_TAC[vREAL_INV_0] ---->
  vMATCH_MP_TAC vREAL_MUL_RINV_UNIQ ---->
  vMATCH_MP_TAC vREAL_MUL_LINV ---->
  vASM_REWRITE_TAC[]);;

let vREAL_EQ_INV2 = try Cache.lookup_thm "REAL_EQ_INV2" with _ ->  prove
 ((parse_term "!x y. inv(x) = inv(y) <=> x = y"),
  vMESON_TAC[vREAL_INV_INV]);;

let vREAL_INV_EQ_0 = try Cache.lookup_thm "REAL_INV_EQ_0" with _ ->  prove
 ((parse_term "!x. inv(x) = &0 <=> x = &0"),
  vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[vREAL_INV_0] ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_INV_INV] ----> vASM_REWRITE_TAC[vREAL_INV_0]);;

let vREAL_LT_INV = try Cache.lookup_thm "REAL_LT_INV" with _ ->  prove
 ((parse_term "!x. &0 < x ==> &0 < inv(x)"),
  vGEN_TAC ---->
  vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC (vSPEC (parse_term "inv(x)") vREAL_LT_NEGTOTAL) ---->
  vASM_REWRITE_TAC[] ++-->
   [vRULE_ASSUM_TAC(vREWRITE_RULE[vREAL_INV_EQ_0]) ----> vASM_REWRITE_TAC[];
    vDISCH_TAC ----> vSUBGOAL_THEN (parse_term "&0 < --(inv x) * x") vMP_TAC ++-->
     [vMATCH_MP_TAC vREAL_LT_MUL ----> vASM_REWRITE_TAC[];
      vREWRITE_TAC[vREAL_MUL_LNEG]]] ---->
  vSUBGOAL_THEN (parse_term "inv(x) * x = &1") vSUBST1_TAC ++-->
   [vMATCH_MP_TAC vREAL_MUL_LINV ---->
    vUNDISCH_TAC (parse_term "&0 < x") ----> vREAL_ARITH_TAC;
    vREWRITE_TAC[vREAL_LT_RNEG; vREAL_ADD_LID; vREAL_OF_NUM_LT; vARITH]]);;

let vREAL_LT_INV_EQ = try Cache.lookup_thm "REAL_LT_INV_EQ" with _ ->  prove
 ((parse_term "!x. &0 < inv x <=> &0 < x"),
  vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[vREAL_LT_INV] ---->
  vGEN_REWRITE_TAC (funpow 2 vRAND_CONV) [vGSYM vREAL_INV_INV] ---->
  vREWRITE_TAC[vREAL_LT_INV]);;

let vREAL_INV_NEG = try Cache.lookup_thm "REAL_INV_NEG" with _ ->  prove
 ((parse_term "!x. inv(--x) = --(inv x)"),
  vGEN_TAC ----> vASM_CASES_TAC (parse_term "x = &0") ---->
  vASM_REWRITE_TAC[vREAL_NEG_0; vREAL_INV_0] ---->
  vMATCH_MP_TAC vREAL_MUL_LINV_UNIQ ---->
  vREWRITE_TAC[vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG] ---->
  vMATCH_MP_TAC vREAL_MUL_LINV ----> vASM_REWRITE_TAC[]);;

let vREAL_LE_INV_EQ = try Cache.lookup_thm "REAL_LE_INV_EQ" with _ ->  prove
 ((parse_term "!x. &0 <= inv x <=> &0 <= x"),
  vREWRITE_TAC[vREAL_LE_LT; vREAL_LT_INV_EQ; vREAL_INV_EQ_0] ---->
  vMESON_TAC[vREAL_INV_EQ_0]);;

let vREAL_LE_INV = try Cache.lookup_thm "REAL_LE_INV" with _ ->  prove
 ((parse_term "!x. &0 <= x ==> &0 <= inv(x)"),
  vREWRITE_TAC[vREAL_LE_INV_EQ]);;

let vREAL_MUL_RINV = try Cache.lookup_thm "REAL_MUL_RINV" with _ ->  prove
 ((parse_term "!x. ~(x = &0) ==> (x * inv(x) = &1)"),
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vREAL_MUL_LINV]);;

let vREAL_INV_1 = try Cache.lookup_thm "REAL_INV_1" with _ ->  prove
 ((parse_term "inv(&1) = &1"),
  vMATCH_MP_TAC vREAL_MUL_RINV_UNIQ ---->
  vREWRITE_TAC[vREAL_MUL_LID]);;

let vREAL_INV_EQ_1 = try Cache.lookup_thm "REAL_INV_EQ_1" with _ ->  prove
 ((parse_term "!x. inv(x) = &1 <=> x = &1"),
  vMESON_TAC[vREAL_INV_INV; vREAL_INV_1]);;

let vREAL_DIV_1 = try Cache.lookup_thm "REAL_DIV_1" with _ ->  prove
 ((parse_term "!x. x / &1 = x"),
  vREWRITE_TAC[real_div; vREAL_INV_1; vREAL_MUL_RID]);;

let vREAL_DIV_REFL = try Cache.lookup_thm "REAL_DIV_REFL" with _ ->  prove
 ((parse_term "!x. ~(x = &0) ==> (x / x = &1)"),
  vGEN_TAC ----> vREWRITE_TAC[real_div; vREAL_MUL_RINV]);;

let vREAL_DIV_RMUL = try Cache.lookup_thm "REAL_DIV_RMUL" with _ ->  prove
 ((parse_term "!x y. ~(y = &0) ==> ((x / y) * y = x)"),
  vSIMP_TAC[real_div; vGSYM vREAL_MUL_ASSOC; vREAL_MUL_LINV; vREAL_MUL_RID]);;

let vREAL_DIV_LMUL = try Cache.lookup_thm "REAL_DIV_LMUL" with _ ->  prove
 ((parse_term "!x y. ~(y = &0) ==> (y * (x / y) = x)"),
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vREAL_DIV_RMUL]);;

let vREAL_DIV_EQ_1 = try Cache.lookup_thm "REAL_DIV_EQ_1" with _ ->  prove
 ((parse_term "!x y:real. x / y = &1 <=> x = y /\\ ~(x = &0) /\\ ~(y = &0)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_div] ---->
  vASM_CASES_TAC (parse_term "x = &0") ----> vASM_REWRITE_TAC[vREAL_MUL_LZERO] ---->
  vASM_CASES_TAC (parse_term "y = &0") ----> vASM_REWRITE_TAC[vREAL_INV_0; vREAL_MUL_RZERO] ---->
  vREWRITE_TAC[vREAL_OF_NUM_EQ; vARITH] ---->
  vEQ_TAC ----> vASM_SIMP_TAC[vGSYM real_div; vREAL_DIV_REFL] ---->
  vDISCH_THEN(vMP_TAC -| vAP_TERM (parse_term "( * ) (y:real)")) ---->
  vASM_SIMP_TAC[vREAL_DIV_LMUL; vREAL_MUL_RID]);;

let vREAL_ABS_INV = try Cache.lookup_thm "REAL_ABS_INV" with _ ->  prove
 ((parse_term "!x. abs(inv x) = inv(abs x)"),
  vGEN_TAC ----> vCONV_TAC vSYM_CONV ---->
  vASM_CASES_TAC (parse_term "x = &0") ----> vASM_REWRITE_TAC[vREAL_INV_0; vREAL_ABS_0] ---->
  vMATCH_MP_TAC vREAL_MUL_RINV_UNIQ ---->
  vREWRITE_TAC[vGSYM vREAL_ABS_MUL] ---->
  vPOP_ASSUM(vSUBST1_TAC -| vMATCH_MP vREAL_MUL_RINV) ---->
  vREWRITE_TAC[vREAL_ABS_1]);;

let vREAL_ABS_DIV = try Cache.lookup_thm "REAL_ABS_DIV" with _ ->  prove
 ((parse_term "!x y. abs(x / y) = abs(x) / abs(y)"),
  vREWRITE_TAC[real_div; vREAL_ABS_INV; vREAL_ABS_MUL]);;

let vREAL_INV_MUL = try Cache.lookup_thm "REAL_INV_MUL" with _ ->  prove
 ((parse_term "!x y. inv(x * y) = inv(x) * inv(y)"),
  vREPEAT vGEN_TAC ---->
  vMAP_EVERY vASM_CASES_TAC [(parse_term "x = &0"); (parse_term "y = &0")] ---->
  vASM_REWRITE_TAC[vREAL_INV_0; vREAL_MUL_LZERO; vREAL_MUL_RZERO] ---->
  vMATCH_MP_TAC vREAL_MUL_LINV_UNIQ ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC (parse_term "(a * b) * (c * d) = (a * c) * (b * d)")] ---->
  vEVERY_ASSUM(vSUBST1_TAC -| vMATCH_MP vREAL_MUL_LINV) ---->
  vREWRITE_TAC[vREAL_MUL_LID]);;

let vREAL_INV_DIV = try Cache.lookup_thm "REAL_INV_DIV" with _ ->  prove
 ((parse_term "!x y. inv(x / y) = y / x"),
  vREWRITE_TAC[real_div; vREAL_INV_INV; vREAL_INV_MUL] ---->
  vMATCH_ACCEPT_TAC vREAL_MUL_SYM);;

let vREAL_POW_MUL = try Cache.lookup_thm "REAL_POW_MUL" with _ ->  prove
 ((parse_term "!x y n. (x * y) pow n = (x pow n) * (y pow n)"),
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[real_pow; vREAL_MUL_LID; vREAL_MUL_AC]);;

let vREAL_POW_INV = try Cache.lookup_thm "REAL_POW_INV" with _ ->  prove
 ((parse_term "!x n. (inv x) pow n = inv(x pow n)"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[real_pow; vREAL_INV_1; vREAL_INV_MUL]);;

let vREAL_INV_POW = try Cache.lookup_thm "REAL_INV_POW" with _ ->  prove
 ((parse_term "!x n. inv(x pow n) = (inv x) pow n"),
  vREWRITE_TAC[vREAL_POW_INV]);;

let vREAL_POW_DIV = try Cache.lookup_thm "REAL_POW_DIV" with _ ->  prove
 ((parse_term "!x y n. (x / y) pow n = (x pow n) / (y pow n)"),
  vREWRITE_TAC[real_div; vREAL_POW_MUL; vREAL_POW_INV]);;

let vREAL_DIV_EQ_0 = try Cache.lookup_thm "REAL_DIV_EQ_0" with _ ->  prove
 ((parse_term "!x y. x / y = &0 <=> x = &0 \\/ y = &0"),
  vREWRITE_TAC[real_div; vREAL_INV_EQ_0; vREAL_ENTIRE]);;

let vREAL_POW_ADD = try Cache.lookup_thm "REAL_POW_ADD" with _ ->  prove
 ((parse_term "!x m n. x pow (m + n) = x pow m * x pow n"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vADD_CLAUSES; real_pow; vREAL_MUL_LID; vREAL_MUL_ASSOC]);;

let vREAL_POW_NZ = try Cache.lookup_thm "REAL_POW_NZ" with _ ->  prove
 ((parse_term "!x n. ~(x = &0) ==> ~(x pow n = &0)"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[real_pow; vREAL_OF_NUM_EQ; vARITH] ---->
  vASM_MESON_TAC[vREAL_ENTIRE]);;

let vREAL_POW_SUB = try Cache.lookup_thm "REAL_POW_SUB" with _ ->  prove
 ((parse_term "!x m n. ~(x = &0) /\\ m <= n ==> (x pow (n - m) = x pow n / x pow m)"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vREWRITE_TAC[vLE_EXISTS] ---->
  vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC) ---->
  vREWRITE_TAC[vADD_SUB2] ----> vREWRITE_TAC[vREAL_POW_ADD] ---->
  vREWRITE_TAC[real_div] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_LID] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_MUL_LINV ---->
  vMATCH_MP_TAC vREAL_POW_NZ ----> vASM_REWRITE_TAC[]);;

let vREAL_LT_LCANCEL_IMP = try Cache.lookup_thm "REAL_LT_LCANCEL_IMP" with _ ->  prove
 ((parse_term "!x y z. &0 < x /\\ x * y < x * z ==> y < z"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(fun th -> vASSUME_TAC(vCONJUNCT1 th) ----> vMP_TAC th) ----> vDISCH_THEN
   (vMP_TAC -| uncurry vCONJ -| (vMATCH_MP vREAL_LT_INV $-$ vI) -| vCONJ_PAIR) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_LMUL) ---->
  vPOP_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_MUL_LINV -| vMATCH_MP vREAL_LT_IMP_NZ) ---->
  vASM_REWRITE_TAC[vREAL_MUL_ASSOC; vREAL_MUL_LID]);;

let vREAL_LT_RCANCEL_IMP = try Cache.lookup_thm "REAL_LT_RCANCEL_IMP" with _ ->  prove
 ((parse_term "!x y z. &0 < z /\\ x * z < y * z ==> x < y"),
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vREAL_LT_LCANCEL_IMP]);;

let vREAL_LE_LCANCEL_IMP = try Cache.lookup_thm "REAL_LE_LCANCEL_IMP" with _ ->  prove
 ((parse_term "!x y z. &0 < x /\\ x * y <= x * z ==> y <= z"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_LE_LT; vREAL_EQ_MUL_LCANCEL] ---->
  vASM_CASES_TAC (parse_term "x = &0") ----> vASM_REWRITE_TAC[vREAL_LT_REFL] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[] ----> vDISJ1_TAC ---->
  vMATCH_MP_TAC vREAL_LT_LCANCEL_IMP ---->
  vEXISTS_TAC (parse_term "x:real") ----> vASM_REWRITE_TAC[]);;

let vREAL_LE_RCANCEL_IMP = try Cache.lookup_thm "REAL_LE_RCANCEL_IMP" with _ ->  prove
 ((parse_term "!x y z. &0 < z /\\ x * z <= y * z ==> x <= y"),
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vREAL_LE_LCANCEL_IMP]);;

let vREAL_LE_RMUL_EQ = try Cache.lookup_thm "REAL_LE_RMUL_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (x * z <= y * z <=> x <= y)"),
  vMESON_TAC[vREAL_LE_RMUL; vREAL_LE_RCANCEL_IMP; vREAL_LT_IMP_LE]);;

let vREAL_LE_LMUL_EQ = try Cache.lookup_thm "REAL_LE_LMUL_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (z * x <= z * y <=> x <= y)"),
  vMESON_TAC[vREAL_LE_RMUL_EQ; vREAL_MUL_SYM]);;

let vREAL_LT_RMUL_EQ = try Cache.lookup_thm "REAL_LT_RMUL_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (x * z < y * z <=> x < y)"),
  vSIMP_TAC[vGSYM vREAL_NOT_LE; vREAL_LE_RMUL_EQ]);;

let vREAL_LT_LMUL_EQ = try Cache.lookup_thm "REAL_LT_LMUL_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (z * x < z * y <=> x < y)"),
  vSIMP_TAC[vGSYM vREAL_NOT_LE; vREAL_LE_LMUL_EQ]);;

let vREAL_LE_MUL_EQ = try Cache.lookup_thm "REAL_LE_MUL_EQ" with _ ->  prove
 ((parse_term "(!x y. &0 < x ==> (&0 <= x * y <=> &0 <= y)) /\\\n   (!x y. &0 < y ==> (&0 <= x * y <=> &0 <= x))"),
  vMESON_TAC[vREAL_LE_LMUL_EQ; vREAL_LE_RMUL_EQ; vREAL_MUL_LZERO; vREAL_MUL_RZERO]);;

let vREAL_LT_MUL_EQ = try Cache.lookup_thm "REAL_LT_MUL_EQ" with _ ->  prove
 ((parse_term "(!x y. &0 < x ==> (&0 < x * y <=> &0 < y)) /\\\n   (!x y. &0 < y ==> (&0 < x * y <=> &0 < x))"),
  vMESON_TAC[vREAL_LT_LMUL_EQ; vREAL_LT_RMUL_EQ; vREAL_MUL_LZERO; vREAL_MUL_RZERO]);;

let vREAL_MUL_POS_LT = try Cache.lookup_thm "REAL_MUL_POS_LT" with _ ->  prove
 ((parse_term "!x y. &0 < x * y <=> &0 < x /\\ &0 < y \\/ x < &0 /\\ y < &0"),
  vREPEAT vSTRIP_TAC ---->
  vSTRIP_ASSUME_TAC(vSPEC (parse_term "x:real") vREAL_LT_NEGTOTAL) ---->
  vSTRIP_ASSUME_TAC(vSPEC (parse_term "y:real") vREAL_LT_NEGTOTAL) ---->
  vASM_REWRITE_TAC[vREAL_MUL_LZERO; vREAL_MUL_RZERO; vREAL_LT_REFL] ---->
  vASSUM_LIST(vMP_TAC -| vMATCH_MP vREAL_LT_MUL -| end_itlist vCONJ) ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC);;

let vREAL_MUL_POS_LE = try Cache.lookup_thm "REAL_MUL_POS_LE" with _ ->  prove
 ((parse_term "!x y. &0 <= x * y <=>\n         x = &0 \\/ y = &0 \\/ &0 < x /\\ &0 < y \\/ x < &0 /\\ y < &0"),
  vREWRITE_TAC[vREAL_ARITH (parse_term "&0 <= x <=> x = &0 \\/ &0 < x")] ---->
  vREWRITE_TAC[vREAL_MUL_POS_LT; vREAL_ENTIRE] ----> vREAL_ARITH_TAC);;

let vREAL_LE_RDIV_EQ = try Cache.lookup_thm "REAL_LE_RDIV_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (x <= y / z <=> x * z <= y)"),
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(fun th ->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM(vMATCH_MP vREAL_LE_RMUL_EQ th)]) ---->
  vASM_SIMP_TAC[real_div; vGSYM vREAL_MUL_ASSOC; vREAL_MUL_LINV;
               vREAL_MUL_RID; vREAL_LT_IMP_NZ]);;

let vREAL_LE_LDIV_EQ = try Cache.lookup_thm "REAL_LE_LDIV_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (x / z <= y <=> x <= y * z)"),
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(fun th ->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM(vMATCH_MP vREAL_LE_RMUL_EQ th)]) ---->
  vASM_SIMP_TAC[real_div; vGSYM vREAL_MUL_ASSOC; vREAL_MUL_LINV;
               vREAL_MUL_RID; vREAL_LT_IMP_NZ]);;

let vREAL_LT_RDIV_EQ = try Cache.lookup_thm "REAL_LT_RDIV_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (x < y / z <=> x * z < y)"),
  vSIMP_TAC[vGSYM vREAL_NOT_LE; vREAL_LE_LDIV_EQ]);;

let vREAL_LT_LDIV_EQ = try Cache.lookup_thm "REAL_LT_LDIV_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (x / z < y <=> x < y * z)"),
  vSIMP_TAC[vGSYM vREAL_NOT_LE; vREAL_LE_RDIV_EQ]);;

let vREAL_EQ_RDIV_EQ = try Cache.lookup_thm "REAL_EQ_RDIV_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> ((x = y / z) <=> (x * z = y))"),
  vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
  vSIMP_TAC[vREAL_LE_RDIV_EQ; vREAL_LE_LDIV_EQ]);;

let vREAL_EQ_LDIV_EQ = try Cache.lookup_thm "REAL_EQ_LDIV_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> ((x / z = y) <=> (x = y * z))"),
  vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
  vSIMP_TAC[vREAL_LE_RDIV_EQ; vREAL_LE_LDIV_EQ]);;

let vREAL_LT_DIV2_EQ = try Cache.lookup_thm "REAL_LT_DIV2_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (x / z < y / z <=> x < y)"),
  vSIMP_TAC[real_div; vREAL_LT_RMUL_EQ; vREAL_LT_INV_EQ]);;

let vREAL_LE_DIV2_EQ = try Cache.lookup_thm "REAL_LE_DIV2_EQ" with _ ->  prove
 ((parse_term "!x y z. &0 < z ==> (x / z <= y / z <=> x <= y)"),
  vSIMP_TAC[real_div; vREAL_LE_RMUL_EQ; vREAL_LT_INV_EQ]);;

let vREAL_MUL_2 = try Cache.lookup_thm "REAL_MUL_2" with _ ->  prove
 ((parse_term "!x. &2 * x = x + x"),
  vREAL_ARITH_TAC);;

let vREAL_POW_EQ_0 = try Cache.lookup_thm "REAL_POW_EQ_0" with _ ->  prove
 ((parse_term "!x n. (x pow n = &0) <=> (x = &0) /\\ ~(n = 0)"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vNOT_SUC; real_pow; vREAL_ENTIRE] ++-->
   [vREAL_ARITH_TAC;
    vCONV_TAC vTAUT]);;

let vREAL_LE_MUL2 = try Cache.lookup_thm "REAL_LE_MUL2" with _ ->  prove
 ((parse_term "!w x y z. &0 <= w /\\ w <= x /\\ &0 <= y /\\ y <= z\n             ==> w * y <= x * z"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC (parse_term "w * z") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LE_LMUL; vMATCH_MP_TAC vREAL_LE_RMUL] ---->
  vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "y:real") ---->
  vASM_REWRITE_TAC[]);;

let vREAL_LT_MUL2 = try Cache.lookup_thm "REAL_LT_MUL2" with _ ->  prove
 ((parse_term "!w x y z. &0 <= w /\\ w < x /\\ &0 <= y /\\ y < z\n             ==> w * y < x * z"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC (parse_term "w * z") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LE_LMUL; vMATCH_MP_TAC vREAL_LT_RMUL] ---->
  vASM_REWRITE_TAC[] ++-->
   [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
    vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC (parse_term "y:real") ---->
    vASM_REWRITE_TAC[]]);;

let vREAL_LT_SQUARE = try Cache.lookup_thm "REAL_LT_SQUARE" with _ ->  prove
 ((parse_term "!x. (&0 < x * x) <=> ~(x = &0)"),
  vGEN_TAC ----> vREWRITE_TAC[vREAL_LT_LE; vREAL_LE_SQUARE] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vEQ_SYM_EQ] ---->
  vREWRITE_TAC[vREAL_ENTIRE]);;

let vREAL_POW_1 = try Cache.lookup_thm "REAL_POW_1" with _ ->  prove
 ((parse_term "!x. x pow 1 = x"),
  vREWRITE_TAC[num_CONV (parse_term "1")] ---->
  vREWRITE_TAC[real_pow; vREAL_MUL_RID]);;

let vREAL_POW_ONE = try Cache.lookup_thm "REAL_POW_ONE" with _ ->  prove
 ((parse_term "!n. &1 pow n = &1"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[real_pow; vREAL_MUL_LID]);;

let vREAL_LT_INV2 = try Cache.lookup_thm "REAL_LT_INV2" with _ ->  prove
 ((parse_term "!x y. &0 < x /\\ x < y ==> inv(y) < inv(x)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LT_RCANCEL_IMP ---->
  vEXISTS_TAC (parse_term "x * y") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LT_MUL ---->
    vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ----> vREAL_ARITH_TAC;
    vSUBGOAL_THEN (parse_term "(inv x * x = &1) /\\ (inv y * y = &1)") vASSUME_TAC ++-->
     [vCONJ_TAC ----> vMATCH_MP_TAC vREAL_MUL_LINV ---->
      vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ----> vREAL_ARITH_TAC;
      vASM_REWRITE_TAC[vREAL_MUL_ASSOC; vREAL_MUL_LID] ---->
      vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV) [vREAL_MUL_SYM] ---->
      vASM_REWRITE_TAC[vGSYM vREAL_MUL_ASSOC; vREAL_MUL_RID]]]);;

let vREAL_LE_INV2 = try Cache.lookup_thm "REAL_LE_INV2" with _ ->  prove
 ((parse_term "!x y. &0 < x /\\ x <= y ==> inv(y) <= inv(x)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_LE_LT] ---->
  vASM_CASES_TAC (parse_term "x:real = y") ----> vASM_REWRITE_TAC[] ---->
  vSTRIP_TAC ----> vDISJ1_TAC ----> vMATCH_MP_TAC vREAL_LT_INV2 ---->
  vASM_REWRITE_TAC[]);;

let vREAL_LT_LINV = try Cache.lookup_thm "REAL_LT_LINV" with _ ->  prove
 ((parse_term "!x y. &0 < y /\\ inv y < x ==> inv x < y"),
  vREPEAT vSTRIP_TAC ----> vMP_TAC (vSPEC (parse_term "y:real") vREAL_LT_INV) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vMP_TAC (vSPECL [(parse_term "(inv y:real)"); (parse_term "x:real")] vREAL_LT_INV2) ---->
  vASM_REWRITE_TAC[vREAL_INV_INV]);;

let vREAL_LT_RINV = try Cache.lookup_thm "REAL_LT_RINV" with _ ->  prove
 ((parse_term "!x y. &0 < x /\\ x < inv y ==> y < inv x"),
  vREPEAT vSTRIP_TAC ----> vMP_TAC (vSPEC (parse_term "x:real") vREAL_LT_INV) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vMP_TAC (vSPECL [(parse_term "x:real"); (parse_term "inv y:real")] vREAL_LT_INV2) ---->
  vASM_REWRITE_TAC[vREAL_INV_INV]);;

let vREAL_LE_LINV = try Cache.lookup_thm "REAL_LE_LINV" with _ ->  prove
 ((parse_term "!x y. &0 < y /\\ inv y <= x ==> inv x <= y"),
  vREPEAT vSTRIP_TAC ----> vMP_TAC (vSPEC (parse_term "y:real") vREAL_LT_INV) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vMP_TAC (vSPECL [(parse_term "(inv y:real)"); (parse_term "x:real")] vREAL_LE_INV2) ---->
  vASM_REWRITE_TAC[vREAL_INV_INV]);;

let vREAL_LE_RINV = try Cache.lookup_thm "REAL_LE_RINV" with _ ->  prove
 ((parse_term "!x y. &0 < x /\\ x <= inv y ==> y <= inv x"),
  vREPEAT vSTRIP_TAC ----> vMP_TAC (vSPEC (parse_term "x:real") vREAL_LT_INV) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vMP_TAC (vSPECL [(parse_term "x:real"); (parse_term "inv y:real")] vREAL_LE_INV2) ---->
  vASM_REWRITE_TAC[vREAL_INV_INV]);;

let vREAL_INV_LE_1 = try Cache.lookup_thm "REAL_INV_LE_1" with _ ->  prove
 ((parse_term "!x. &1 <= x ==> inv(x) <= &1"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_INV_1] ---->
  vMATCH_MP_TAC vREAL_LE_INV2 ----> vASM_REWRITE_TAC[vREAL_LT_01]);;

let vREAL_INV_1_LE = try Cache.lookup_thm "REAL_INV_1_LE" with _ ->  prove
 ((parse_term "!x. &0 < x /\\ x <= &1 ==> &1 <= inv(x)"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_INV_1] ---->
  vMATCH_MP_TAC vREAL_LE_INV2 ----> vASM_REWRITE_TAC[vREAL_LT_01]);;

let vREAL_INV_LT_1 = try Cache.lookup_thm "REAL_INV_LT_1" with _ ->  prove
 ((parse_term "!x. &1 < x ==> inv(x) < &1"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_INV_1] ---->
  vMATCH_MP_TAC vREAL_LT_INV2 ----> vASM_REWRITE_TAC[vREAL_LT_01]);;

let vREAL_INV_1_LT = try Cache.lookup_thm "REAL_INV_1_LT" with _ ->  prove
 ((parse_term "!x. &0 < x /\\ x < &1 ==> &1 < inv(x)"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_INV_1] ---->
  vMATCH_MP_TAC vREAL_LT_INV2 ----> vASM_REWRITE_TAC[vREAL_LT_01]);;

let vREAL_SUB_INV = try Cache.lookup_thm "REAL_SUB_INV" with _ ->  prove
 ((parse_term "!x y. ~(x = &0) /\\ ~(y = &0) ==> (inv(x) - inv(y) = (y - x) / (x * y))"),
  vREWRITE_TAC[real_div; vREAL_SUB_RDISTRIB; vREAL_INV_MUL] ---->
  vSIMP_TAC[vREAL_MUL_ASSOC; vREAL_MUL_RINV; vREAL_MUL_LID] ---->
  vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vREWRITE_TAC[vGSYM real_div] ---->
  vSIMP_TAC[vREAL_DIV_LMUL]);;

let vREAL_DOWN = try Cache.lookup_thm "REAL_DOWN" with _ ->  prove
 ((parse_term "!d. &0 < d ==> ?e. &0 < e /\\ e < d"),
  vGEN_TAC ----> vDISCH_TAC ----> vEXISTS_TAC (parse_term "d / &2") ---->
  vASSUME_TAC(vREAL_ARITH (parse_term "&0 < &2")) ---->
  vASSUME_TAC(vMATCH_MP vREAL_MUL_LINV (vREAL_ARITH (parse_term "~(&2 = &0)"))) ---->
  vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LT_RCANCEL_IMP ----> vEXISTS_TAC (parse_term "&2") ---->
  vASM_REWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC; vREAL_MUL_RID] ---->
  vUNDISCH_TAC (parse_term "&0 < d") ----> vREAL_ARITH_TAC);;

let vREAL_DOWN2 = try Cache.lookup_thm "REAL_DOWN2" with _ ->  prove
 ((parse_term "!d1 d2. &0 < d1 /\\ &0 < d2 ==> ?e. &0 < e /\\ e < d1 /\\ e < d2"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vDISJ_CASES_TAC(vSPECL [(parse_term "d1:real"); (parse_term "d2:real")] vREAL_LE_TOTAL) ++-->
   [vMP_TAC(vSPEC (parse_term "d1:real") vREAL_DOWN);
    vMP_TAC(vSPEC (parse_term "d2:real") vREAL_DOWN)] ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "e:real") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "e:real") ---->
  vPOP_ASSUM_LIST(vMP_TAC -| end_itlist vCONJ) ---->
  vREAL_ARITH_TAC);;

let vREAL_POW_LE2 = try Cache.lookup_thm "REAL_POW_LE2" with _ ->  prove
 ((parse_term "!n x y. &0 <= x /\\ x <= y ==> x pow n <= y pow n"),
  vINDUCT_TAC ----> vREWRITE_TAC[real_pow; vREAL_LE_REFL] ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_MUL2 ---->
  vASM_REWRITE_TAC[] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_POW_LE ----> vASM_REWRITE_TAC[];
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]);;

let vREAL_POW_LE_1 = try Cache.lookup_thm "REAL_POW_LE_1" with _ ->  prove
 ((parse_term "!n x. &1 <= x ==> &1 <= x pow n"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [(parse_term "n:num"); (parse_term "&1"); (parse_term "x:real")] vREAL_POW_LE2) ---->
  vASM_REWRITE_TAC[vREAL_POW_ONE; vREAL_POS]);;

let vREAL_POW_1_LE = try Cache.lookup_thm "REAL_POW_1_LE" with _ ->  prove
 ((parse_term "!n x. &0 <= x /\\ x <= &1 ==> x pow n <= &1"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [(parse_term "n:num"); (parse_term "x:real"); (parse_term "&1")] vREAL_POW_LE2) ---->
  vASM_REWRITE_TAC[vREAL_POW_ONE]);;

let vREAL_POW_MONO = try Cache.lookup_thm "REAL_POW_MONO" with _ ->  prove
 ((parse_term "!m n x. &1 <= x /\\ m <= n ==> x pow m <= x pow n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLE_EXISTS] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:num") vSUBST1_TAC) ---->
  vREWRITE_TAC[vREAL_POW_ADD] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_RID] ---->
  vMATCH_MP_TAC vREAL_LE_LMUL ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "&1") ---->
    vREWRITE_TAC[vREAL_OF_NUM_LE; vARITH] ---->
    vMATCH_MP_TAC vREAL_POW_LE_1 ----> vASM_REWRITE_TAC[];
    vMATCH_MP_TAC vREAL_POW_LE_1 ----> vASM_REWRITE_TAC[]]);;

let vREAL_POW_LT2 = try Cache.lookup_thm "REAL_POW_LT2" with _ ->  prove
 ((parse_term "!n x y. ~(n = 0) /\\ &0 <= x /\\ x < y ==> x pow n < y pow n"),
  vINDUCT_TAC ----> vREWRITE_TAC[vNOT_SUC; real_pow] ----> vREPEAT vSTRIP_TAC ---->
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[real_pow; vREAL_MUL_RID] ---->
  vMATCH_MP_TAC vREAL_LT_MUL2 ----> vASM_REWRITE_TAC[] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_POW_LE ----> vASM_REWRITE_TAC[];
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]);;

let vREAL_POW_LT_1 = try Cache.lookup_thm "REAL_POW_LT_1" with _ ->  prove
 ((parse_term "!n x. ~(n = 0) /\\ &1 < x ==> &1 < x pow n"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [(parse_term "n:num"); (parse_term "&1"); (parse_term "x:real")] vREAL_POW_LT2) ---->
  vASM_REWRITE_TAC[vREAL_POW_ONE; vREAL_POS]);;

let vREAL_POW_1_LT = try Cache.lookup_thm "REAL_POW_1_LT" with _ ->  prove
 ((parse_term "!n x. ~(n = 0) /\\ &0 <= x /\\ x < &1 ==> x pow n < &1"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [(parse_term "n:num"); (parse_term "x:real"); (parse_term "&1")] vREAL_POW_LT2) ---->
  vASM_REWRITE_TAC[vREAL_POW_ONE]);;

let vREAL_POW_MONO_LT = try Cache.lookup_thm "REAL_POW_MONO_LT" with _ ->  prove
 ((parse_term "!m n x. &1 < x /\\ m < n ==> x pow m < x pow n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLT_EXISTS] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vCHOOSE_THEN vSUBST_ALL_TAC) ---->
  vREWRITE_TAC[vREAL_POW_ADD] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_RID] ---->
  vMATCH_MP_TAC vREAL_LT_LMUL ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_POW_LT ---->
    vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC (parse_term "&1") ---->
    vASM_REWRITE_TAC[vREAL_OF_NUM_LT; vARITH];
    vSPEC_TAC((parse_term "d:num"),(parse_term "d:num")) ---->
    vINDUCT_TAC ----> vONCE_REWRITE_TAC[real_pow] ++-->
     [vASM_REWRITE_TAC[real_pow; vREAL_MUL_RID]; vALL_TAC] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_LID] ---->
    vMATCH_MP_TAC vREAL_LT_MUL2 ---->
    vASM_REWRITE_TAC[vREAL_OF_NUM_LE; vARITH]]);;

let vREAL_POW_POW = try Cache.lookup_thm "REAL_POW_POW" with _ ->  prove
 ((parse_term "!x m n. (x pow m) pow n = x pow (m * n)"),
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[real_pow; vMULT_CLAUSES; vREAL_POW_ADD]);;

let vREAL_EQ_RCANCEL_IMP = try Cache.lookup_thm "REAL_EQ_RCANCEL_IMP" with _ ->  prove
 ((parse_term "!x y z. ~(z = &0) /\\ (x * z = y * z) ==> (x = y)"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_SUB_0] ---->
  vREWRITE_TAC[vREAL_SUB_RZERO; vGSYM vREAL_SUB_RDISTRIB; vREAL_ENTIRE] ---->
  vCONV_TAC vTAUT);;

let vREAL_EQ_LCANCEL_IMP = try Cache.lookup_thm "REAL_EQ_LCANCEL_IMP" with _ ->  prove
 ((parse_term "!x y z. ~(z = &0) /\\ (z * x = z * y) ==> (x = y)"),
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vMATCH_ACCEPT_TAC vREAL_EQ_RCANCEL_IMP);;

let vREAL_LT_DIV = try Cache.lookup_thm "REAL_LT_DIV" with _ ->  prove
 ((parse_term "!x y. &0 < x /\\ &0 < y ==> &0 < x / y"),
  vSIMP_TAC[vREAL_LT_MUL; vREAL_LT_INV_EQ; real_div]);;

let vREAL_LE_DIV = try Cache.lookup_thm "REAL_LE_DIV" with _ ->  prove
 ((parse_term "!x y. &0 <= x /\\ &0 <= y ==> &0 <= x / y"),
  vSIMP_TAC[vREAL_LE_MUL; vREAL_LE_INV_EQ; real_div]);;

let vREAL_DIV_POW2 = try Cache.lookup_thm "REAL_DIV_POW2" with _ ->  prove
 ((parse_term "!x m n. ~(x = &0)\n           ==> (x pow m / x pow n = if n <= m then x pow (m - n)\n                                    else inv(x pow (n - m)))"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
  vASM_SIMP_TAC[vREAL_POW_SUB] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_INV_INV] ---->
  vAP_TERM_TAC ----> vREWRITE_TAC[vREAL_INV_DIV] ---->
  vUNDISCH_TAC (parse_term "~(n:num <= m)") ----> vREWRITE_TAC[vNOT_LE] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vLT_IMP_LE) ---->
  vASM_SIMP_TAC[vREAL_POW_SUB]);;

let vREAL_DIV_POW2_ALT = try Cache.lookup_thm "REAL_DIV_POW2_ALT" with _ ->  prove
 ((parse_term "!x m n. ~(x = &0)\n           ==> (x pow m / x pow n = if n < m then x pow (m - n)\n                                    else inv(x pow (n - m)))"),
  vREPEAT vSTRIP_TAC ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_INV_INV] ---->
  vONCE_REWRITE_TAC[vREAL_INV_DIV] ---->
  vASM_SIMP_TAC[vGSYM vNOT_LE; vREAL_DIV_POW2] ---->
  vASM_CASES_TAC (parse_term "m <= n:num") ---->
  vASM_REWRITE_TAC[vREAL_INV_INV]);;

let vREAL_LT_POW2 = try Cache.lookup_thm "REAL_LT_POW2" with _ ->  prove
 ((parse_term "!n. &0 < &2 pow n"),
  vSIMP_TAC[vREAL_POW_LT; vREAL_OF_NUM_LT; vARITH]);;

let vREAL_LE_POW2 = try Cache.lookup_thm "REAL_LE_POW2" with _ ->  prove
 ((parse_term "!n. &1 <= &2 pow n"),
  vGEN_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "&2 pow 0") ---->
  vSIMP_TAC[vREAL_POW_MONO; vLE_0; vREAL_OF_NUM_LE; vARITH] ---->
  vREWRITE_TAC[real_pow; vREAL_LE_REFL]);;

let vREAL_POW2_ABS = try Cache.lookup_thm "REAL_POW2_ABS" with _ ->  prove
 ((parse_term "!x. abs(x) pow 2 = x pow 2"),
  vGEN_TAC ----> vREWRITE_TAC[real_abs] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_POW_NEG; vARITH_EVEN]);;

let vREAL_LE_SQUARE_ABS = try Cache.lookup_thm "REAL_LE_SQUARE_ABS" with _ ->  prove
 ((parse_term "!x y. abs(x) <= abs(y) <=> x pow 2 <= y pow 2"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_POW2_ABS] ---->
  vMESON_TAC[vREAL_POW_LE2; vREAL_ABS_POS; vNUM_EQ_CONV (parse_term "2 = 0");
            vREAL_POW_LT2; vREAL_NOT_LE]);;

let vREAL_LT_SQUARE_ABS = try Cache.lookup_thm "REAL_LT_SQUARE_ABS" with _ ->  prove
 ((parse_term "!x y. abs(x) < abs(y) <=> x pow 2 < y pow 2"),
  vREWRITE_TAC[vGSYM vREAL_NOT_LE; vREAL_LE_SQUARE_ABS]);;

let vREAL_EQ_SQUARE_ABS = try Cache.lookup_thm "REAL_EQ_SQUARE_ABS" with _ ->  prove
 ((parse_term "!x y. abs x = abs y <=> x pow 2 = y pow 2"),
  vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_LE_SQUARE_ABS]);;

let vREAL_LE_POW_2 = try Cache.lookup_thm "REAL_LE_POW_2" with _ ->  prove
 ((parse_term "!x. &0 <= x pow 2"),
  vREWRITE_TAC[vREAL_POW_2; vREAL_LE_SQUARE]);;

let vREAL_LT_POW_2 = try Cache.lookup_thm "REAL_LT_POW_2" with _ ->  prove
 ((parse_term "!x. &0 < x pow 2 <=> ~(x = &0)"),
  vREWRITE_TAC[vREAL_LE_POW_2; vREAL_ARITH (parse_term "&0 < x <=> &0 <= x /\\ ~(x = &0)")] ---->
  vREWRITE_TAC[vREAL_POW_EQ_0; vARITH]);;

let vREAL_SOS_EQ_0 = try Cache.lookup_thm "REAL_SOS_EQ_0" with _ ->  prove
 ((parse_term "!x y. x pow 2 + y pow 2 = &0 <=> x = &0 /\\ y = &0"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ---->
  vSIMP_TAC[vREAL_POW_2; vREAL_MUL_LZERO; vREAL_ADD_LID] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP (vREAL_ARITH
   (parse_term "x + y = &0 ==> &0 <= x /\\ &0 <= y ==> x = &0 /\\ y = &0"))) ---->
  vREWRITE_TAC[vREAL_LE_SQUARE; vREAL_ENTIRE]);;

let vREAL_POW_ZERO = try Cache.lookup_thm "REAL_POW_ZERO" with _ ->  prove
 ((parse_term "!n. &0 pow n = if n = 0 then &1 else &0"),
  vINDUCT_TAC ----> vREWRITE_TAC[real_pow; vNOT_SUC; vREAL_MUL_LZERO]);;

let vREAL_POW_MONO_INV = try Cache.lookup_thm "REAL_POW_MONO_INV" with _ ->  prove
 ((parse_term "!m n x. &0 <= x /\\ x <= &1 /\\ n <= m ==> x pow m <= x pow n"),
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "x = &0") ++-->
   [vASM_REWRITE_TAC[vREAL_POW_ZERO] ---->
    vREPEAT(vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_POS; vREAL_LE_REFL]) ---->
    vUNDISCH_TAC (parse_term "n:num <= m") ----> vASM_REWRITE_TAC[vLE];
    vGEN_REWRITE_TAC vBINOP_CONV [vGSYM vREAL_INV_INV] ---->
    vMATCH_MP_TAC vREAL_LE_INV2 ----> vREWRITE_TAC[vGSYM vREAL_POW_INV] ---->
    vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_POW_LT ----> vREWRITE_TAC[vREAL_LT_INV_EQ];
      vMATCH_MP_TAC vREAL_POW_MONO ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_INV_1_LE] ---->
    vASM_REWRITE_TAC[vREAL_LT_LE]]);;

let vREAL_POW_LE2_REV = try Cache.lookup_thm "REAL_POW_LE2_REV" with _ ->  prove
 ((parse_term "!n x y. ~(n = 0) /\\ &0 <= y /\\ x pow n <= y pow n ==> x <= y"),
  vMESON_TAC[vREAL_POW_LT2; vREAL_NOT_LE]);;

let vREAL_POW_LT2_REV = try Cache.lookup_thm "REAL_POW_LT2_REV" with _ ->  prove
 ((parse_term "!n x y. &0 <= y /\\ x pow n < y pow n ==> x < y"),
  vMESON_TAC[vREAL_POW_LE2; vREAL_NOT_LE]);;

let vREAL_POW_EQ = try Cache.lookup_thm "REAL_POW_EQ" with _ ->  prove
 ((parse_term "!n x y. ~(n = 0) /\\ &0 <= x /\\ &0 <= y /\\ x pow n = y pow n ==> x = y"),
  vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ----> vMESON_TAC[vREAL_POW_LE2_REV]);;

let vREAL_POW_EQ_ABS = try Cache.lookup_thm "REAL_POW_EQ_ABS" with _ ->  prove
 ((parse_term "!n x y. ~(n = 0) /\\ x pow n = y pow n ==> abs x = abs y"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_POW_EQ ----> vEXISTS_TAC (parse_term "n:num") ---->
  vASM_REWRITE_TAC[vREAL_ABS_POS; vGSYM vREAL_ABS_POW]);;

let vREAL_POW_EQ_1_IMP = try Cache.lookup_thm "REAL_POW_EQ_1_IMP" with _ ->  prove
 ((parse_term "!x n. ~(n = 0) /\\ x pow n = &1 ==> abs(x) = &1"),
  vREPEAT vSTRIP_TAC ----> vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_ABS_NUM] ---->
  vMATCH_MP_TAC vREAL_POW_EQ_ABS ----> vEXISTS_TAC (parse_term "n:num") ---->
  vASM_REWRITE_TAC[vREAL_POW_ONE]);;

let vREAL_POW_EQ_1 = try Cache.lookup_thm "REAL_POW_EQ_1" with _ ->  prove
 ((parse_term "!x n. x pow n = &1 <=> abs(x) = &1 /\\ (x < &0 ==> EVEN(n)) \\/ n = 0"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[real_pow] ---->
  vASM_CASES_TAC (parse_term "abs(x) = &1") ++-->
   [vALL_TAC; vASM_MESON_TAC[vREAL_POW_EQ_1_IMP]] ---->
  vASM_REWRITE_TAC[] ---->
  vFIRST_X_ASSUM(vDISJ_CASES_THEN vSUBST1_TAC -| vMATCH_MP (vREAL_ARITH
   (parse_term "abs x = a ==> x = a \\/ x = --a"))) ---->
  vASM_REWRITE_TAC[vREAL_POW_NEG; vREAL_POW_ONE] ---->
  vREPEAT vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ----> vREAL_ARITH_TAC);;

let vREAL_POW_LT2_ODD = try Cache.lookup_thm "REAL_POW_LT2_ODD" with _ ->  prove
 ((parse_term "!n x y. x < y /\\ ODD n ==> x pow n < y pow n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vARITH] ----> vSTRIP_TAC ---->
  vDISJ_CASES_TAC(vSPEC (parse_term "y:real") vREAL_LE_NEGTOTAL) ++-->
   [vDISJ_CASES_TAC(vREAL_ARITH (parse_term "&0 <= x \\/ &0 < --x")) ---->
    vASM_SIMP_TAC[vREAL_POW_LT2] ---->
    vSUBGOAL_THEN (parse_term "&0 < --x pow n /\\ &0 <= y pow n") vMP_TAC ++-->
     [vASM_SIMP_TAC[vREAL_POW_LE; vREAL_POW_LT];
      vASM_REWRITE_TAC[vREAL_POW_NEG; vGSYM vNOT_ODD] ----> vREAL_ARITH_TAC];
    vSUBGOAL_THEN (parse_term "--y pow n < --x pow n") vMP_TAC ++-->
     [vMATCH_MP_TAC vREAL_POW_LT2 ----> vASM_REWRITE_TAC[];
      vASM_REWRITE_TAC[vREAL_POW_NEG; vGSYM vNOT_ODD]] ---->
    vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC]);;

let vREAL_POW_LE2_ODD = try Cache.lookup_thm "REAL_POW_LE2_ODD" with _ ->  prove
 ((parse_term "!n x y. x <= y /\\ ODD n ==> x pow n <= y pow n"),
  vREWRITE_TAC[vREAL_LE_LT] ----> vREPEAT vSTRIP_TAC ---->
  vASM_SIMP_TAC[vREAL_POW_LT2_ODD]);;

let vREAL_POW_LT2_ODD_EQ = try Cache.lookup_thm "REAL_POW_LT2_ODD_EQ" with _ ->  prove
 ((parse_term "!n x y. ODD n ==> (x pow n < y pow n <=> x < y)"),
  vMESON_TAC[vREAL_POW_LT2_ODD; vREAL_POW_LE2_ODD; vREAL_NOT_LE]);;

let vREAL_POW_LE2_ODD_EQ = try Cache.lookup_thm "REAL_POW_LE2_ODD_EQ" with _ ->  prove
 ((parse_term "!n x y. ODD n ==> (x pow n <= y pow n <=> x <= y)"),
  vMESON_TAC[vREAL_POW_LT2_ODD; vREAL_POW_LE2_ODD; vREAL_NOT_LE]);;

let vREAL_POW_EQ_ODD_EQ = try Cache.lookup_thm "REAL_POW_EQ_ODD_EQ" with _ ->  prove
 ((parse_term "!n x y. ODD n ==> (x pow n = y pow n <=> x = y)"),
  vSIMP_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_POW_LE2_ODD_EQ]);;

let vREAL_POW_EQ_ODD = try Cache.lookup_thm "REAL_POW_EQ_ODD" with _ ->  prove
 ((parse_term "!n x y. ODD n /\\ x pow n = y pow n ==> x = y"),
  vMESON_TAC[vREAL_POW_EQ_ODD_EQ]);;

let vREAL_POW_EQ_EQ = try Cache.lookup_thm "REAL_POW_EQ_EQ" with _ ->  prove
 ((parse_term "!n x y. x pow n = y pow n <=>\n           if EVEN n then n = 0 \\/ abs x = abs y else x = y"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[real_pow; vARITH] ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vREAL_POW_EQ_ODD_EQ; vGSYM vNOT_EVEN] ---->
  vEQ_TAC ++--> [vASM_MESON_TAC[vREAL_POW_EQ_ABS]; vALL_TAC] ---->
  vREWRITE_TAC[vREAL_EQ_SQUARE_ABS] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vX_CHOOSE_THEN (parse_term "m:num") vSUBST1_TAC -|
    vREWRITE_RULE[vEVEN_EXISTS]) ----> vASM_REWRITE_TAC[vGSYM vREAL_POW_POW]);;

(* ------------------------------------------------------------------------- *)
(* Bounds on convex combinations.                                            *)
(* ------------------------------------------------------------------------- *)

let vREAL_CONVEX_BOUND2_LT = try Cache.lookup_thm "REAL_CONVEX_BOUND2_LT" with _ ->  prove
 ((parse_term "!x y a u v. x < a /\\ y < b /\\ &0 <= u /\\ &0 <= v /\\ u + v = &1\n               ==> u * x + v * y < u * a + v * b"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "u = &0") ++-->
   [vASM_REWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_LID] ----> vREPEAT vSTRIP_TAC;
    vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LTE_ADD2 ---->
    vASM_SIMP_TAC[vREAL_LE_LMUL; vREAL_LT_IMP_LE]] ---->
  vMATCH_MP_TAC vREAL_LT_LMUL ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC);;

let vREAL_CONVEX_BOUND2_LE = try Cache.lookup_thm "REAL_CONVEX_BOUND2_LE" with _ ->  prove
 ((parse_term "!x y a u v. x <= a /\\ y <= b /\\ &0 <= u /\\ &0 <= v /\\ u + v = &1\n               ==> u * x + v * y <= u * a + v * b"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_ADD2 ---->
  vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LE_LMUL ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC);;

let vREAL_CONVEX_BOUND_LT = try Cache.lookup_thm "REAL_CONVEX_BOUND_LT" with _ ->  prove
 ((parse_term "!x y a u v. x < a /\\ y < a /\\ &0 <= u /\\ &0 <= v /\\ (u + v = &1)\n               ==> u * x + v * y < a"),
  vMESON_TAC[vREAL_CONVEX_BOUND2_LT; vMESON[vREAL_MUL_LID; vREAL_ADD_RDISTRIB]
   (parse_term "u + v = &1 ==> u * a + v * a = a")]);;

let vREAL_CONVEX_BOUND_LE = try Cache.lookup_thm "REAL_CONVEX_BOUND_LE" with _ ->  prove
 ((parse_term "!x y a u v. x <= a /\\ y <= a /\\ &0 <= u /\\ &0 <= v /\\ (u + v = &1)\n               ==> u * x + v * y <= a"),
  vMESON_TAC[vREAL_CONVEX_BOUND2_LE; vMESON[vREAL_MUL_LID; vREAL_ADD_RDISTRIB]
   (parse_term "u + v = &1 ==> u * a + v * a = a")]);;

let vREAL_CONVEX_BOUND_GT = try Cache.lookup_thm "REAL_CONVEX_BOUND_GT" with _ ->  prove
 ((parse_term "!x y a u v.\n        a < x /\\ a < y /\\ &0 <= u /\\ &0 <= v /\\ u + v = &1\n        ==> a < u * x + v * y"),
  vMESON_TAC[vREAL_CONVEX_BOUND2_LT; vMESON[vREAL_MUL_LID; vREAL_ADD_RDISTRIB]
   (parse_term "u + v = &1 ==> u * a + v * a = a")]);;

let vREAL_CONVEX_BOUND_GE = try Cache.lookup_thm "REAL_CONVEX_BOUND_GE" with _ ->  prove
 ((parse_term "!x y a u v.\n        a <= x /\\ a <= y /\\ &0 <= u /\\ &0 <= v /\\ u + v = &1\n        ==> a <= u * x + v * y"),
  vMESON_TAC[vREAL_CONVEX_BOUND2_LE; vMESON[vREAL_MUL_LID; vREAL_ADD_RDISTRIB]
   (parse_term "u + v = &1 ==> u * a + v * a = a")]);;

let vREAL_CONVEX_BOUNDS_LE = try Cache.lookup_thm "REAL_CONVEX_BOUNDS_LE" with _ ->  prove
 ((parse_term "!x y a b u v.\n        a <= x /\\ x <= b /\\ a <= y /\\ y <= b /\\\n        &0 <= u /\\ &0 <= v /\\ u + v = &1\n        ==> a <= u * x + v * y /\\ u * x + v * y <= b"),
  vMESON_TAC[vREAL_CONVEX_BOUND2_LE; vMESON[vREAL_MUL_LID; vREAL_ADD_RDISTRIB]
   (parse_term "u + v = &1 ==> u * a + v * a = a")]);;

let vREAL_CONVEX_BOUNDS_LT = try Cache.lookup_thm "REAL_CONVEX_BOUNDS_LT" with _ ->  prove
 ((parse_term "!x y a b u v.\n        a < x /\\ x < b /\\ a < y /\\ y < b /\\\n        &0 <= u /\\ &0 <= v /\\ u + v = &1\n        ==> a < u * x + v * y /\\ u * x + v * y < b"),
  vMESON_TAC[vREAL_CONVEX_BOUND2_LT; vMESON[vREAL_MUL_LID; vREAL_ADD_RDISTRIB]
   (parse_term "u + v = &1 ==> u * a + v * a = a")]);;

(* ------------------------------------------------------------------------- *)
(* Some basic forms of the Archimedian property.                             *)
(* ------------------------------------------------------------------------- *)

let vREAL_ARCH_SIMPLE = try Cache.lookup_thm "REAL_ARCH_SIMPLE" with _ ->  prove
 ((parse_term "!x. ?n. x <= &n"),
  let lemma = prove((parse_term "(!x. (?n. x = &n) ==> P x) <=> !n. P(&n)"),vMESON_TAC[]) in
  vMP_TAC(vSPEC (parse_term "\\y. ?n. y = &n") vREAL_COMPLETE) ----> vREWRITE_TAC[lemma] ---->
  vMESON_TAC[vREAL_LE_SUB_LADD; vREAL_OF_NUM_ADD; vREAL_LE_TOTAL;
            vREAL_ARITH (parse_term "~(M <= M - &1)")]);;

let vREAL_ARCH_LT = try Cache.lookup_thm "REAL_ARCH_LT" with _ ->  prove
 ((parse_term "!x. ?n. x < &n"),
  vMESON_TAC[vREAL_ARCH_SIMPLE; vREAL_OF_NUM_ADD;
            vREAL_ARITH (parse_term "x <= n ==> x < n + &1")]);;

let vREAL_ARCH = try Cache.lookup_thm "REAL_ARCH" with _ ->  prove
 ((parse_term "!x. &0 < x ==> !y. ?n. y < &n * x"),
  vMESON_TAC[vREAL_ARCH_LT; vREAL_LT_LDIV_EQ]);;

let vREAL_ARCH_INV = try Cache.lookup_thm "REAL_ARCH_INV" with _ ->  prove
 ((parse_term "!e. &0 < e <=> ?n. ~(n = 0) /\\ &0 < inv(&n) /\\ inv(&n) < e"),
  vGEN_TAC ----> vEQ_TAC ++--> [vALL_TAC; vMESON_TAC[vREAL_LT_TRANS]] ---->
  vDISCH_TAC ----> vMP_TAC(vSPEC (parse_term "inv(e)") vREAL_ARCH_LT) ---->
  vMATCH_MP_TAC vMONO_EXISTS ---->
  vASM_MESON_TAC[vREAL_LT_INV2; vREAL_INV_INV; vREAL_LT_INV_EQ; vREAL_LT_TRANS;
                vREAL_LT_ANTISYM]);;

let vREAL_POW_LBOUND = try Cache.lookup_thm "REAL_POW_LBOUND" with _ ->  prove
 ((parse_term "!x n. &0 <= x ==> &1 + &n * x <= (&1 + x) pow n"),
  vGEN_TAC ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ----> vDISCH_TAC ---->
  vINDUCT_TAC ---->
  vREWRITE_TAC[real_pow; vREAL_MUL_LZERO; vREAL_ADD_RID; vREAL_LE_REFL] ---->
  vREWRITE_TAC[vGSYM vREAL_OF_NUM_SUC] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC (parse_term "(&1 + x) * (&1 + &n * x)") ---->
  vASM_SIMP_TAC[vREAL_LE_LMUL; vREAL_ARITH (parse_term "&0 <= x ==> &0 <= &1 + x")] ---->
  vASM_SIMP_TAC[vREAL_LE_MUL; vREAL_POS; vREAL_ARITH
   (parse_term "&1 + (n + &1) * x <= (&1 + x) * (&1 + n * x) <=> &0 <= n * x * x")]);;

let vREAL_ARCH_POW = try Cache.lookup_thm "REAL_ARCH_POW" with _ ->  prove
 ((parse_term "!x y. &1 < x ==> ?n. y < x pow n"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC (parse_term "x - &1") vREAL_ARCH) ----> vASM_REWRITE_TAC[vREAL_SUB_LT] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "y:real")) ----> vMATCH_MP_TAC vMONO_EXISTS ---->
  vX_GEN_TAC (parse_term "n:num") ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LTE_TRANS ---->
  vEXISTS_TAC (parse_term "&1 + &n * (x - &1)") ---->
  vASM_SIMP_TAC[vREAL_ARITH (parse_term "x < y ==> x < &1 + y")] ---->
  vASM_MESON_TAC[vREAL_POW_LBOUND; vREAL_SUB_ADD2; vREAL_ARITH
    (parse_term "&1 < x ==> &0 <= x - &1")]);;

let vREAL_ARCH_POW2 = try Cache.lookup_thm "REAL_ARCH_POW2" with _ ->  prove
 ((parse_term "!x. ?n. x < &2 pow n"),
  vSIMP_TAC[vREAL_ARCH_POW; vREAL_OF_NUM_LT; vARITH]);;

let vREAL_ARCH_POW_INV = try Cache.lookup_thm "REAL_ARCH_POW_INV" with _ ->  prove
 ((parse_term "!x y. &0 < y /\\ x < &1 ==> ?n. x pow n < y"),
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "&0 < x") ++-->
   [vALL_TAC; vASM_MESON_TAC[vREAL_POW_1; vREAL_LET_TRANS; vREAL_NOT_LT]] ---->
  vSUBGOAL_THEN (parse_term "inv(&1) < inv(x)") vMP_TAC ++-->
   [vASM_SIMP_TAC[vREAL_LT_INV2]; vREWRITE_TAC[vREAL_INV_1]] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "inv(y)") -| vMATCH_MP vREAL_ARCH_POW) ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vGEN_TAC ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC vBINOP_CONV [vGSYM vREAL_INV_INV] ---->
  vASM_SIMP_TAC[vGSYM vREAL_POW_INV; vREAL_LT_INV; vREAL_LT_INV2]);;

(* ------------------------------------------------------------------------- *)
(* The sign of a real number, as a real number.                              *)
(* ------------------------------------------------------------------------- *)

let real_sgn = new_definition
 (parse_term "(real_sgn:real->real) x =\n        if &0 < x then &1 else if x < &0 then -- &1 else &0");;

let vREAL_SGN_0 = try Cache.lookup_thm "REAL_SGN_0" with _ ->  prove
 ((parse_term "real_sgn(&0) = &0"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_SGN_NEG = try Cache.lookup_thm "REAL_SGN_NEG" with _ ->  prove
 ((parse_term "!x. real_sgn(--x) = --(real_sgn x)"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_SGN_ABS = try Cache.lookup_thm "REAL_SGN_ABS" with _ ->  prove
 ((parse_term "!x. real_sgn(x) * abs(x) = x"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_SGN_ABS_ALT = try Cache.lookup_thm "REAL_SGN_ABS_ALT" with _ ->  prove
 ((parse_term "!x. real_sgn x * x = abs x"),
  vGEN_TAC ----> vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_EQ_SGN_ABS = try Cache.lookup_thm "REAL_EQ_SGN_ABS" with _ ->  prove
 ((parse_term "!x y:real. x = y <=> real_sgn x = real_sgn y /\\ abs x = abs y"),
  vMESON_TAC[vREAL_SGN_ABS]);;

let vREAL_ABS_SGN = try Cache.lookup_thm "REAL_ABS_SGN" with _ ->  prove
 ((parse_term "!x. abs(real_sgn x) = real_sgn(abs x)"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_SGN = try Cache.lookup_thm "REAL_SGN" with _ ->  prove
 ((parse_term "!x. real_sgn x = x / abs x"),
  vGEN_TAC ----> vASM_CASES_TAC (parse_term "x = &0") ++-->
   [vASM_REWRITE_TAC[real_div; vREAL_MUL_LZERO; vREAL_SGN_0];
    vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vGSYM vREAL_SGN_ABS] ---->
    vASM_SIMP_TAC[real_div; vGSYM vREAL_MUL_ASSOC; vREAL_ABS_ZERO;
                 vREAL_MUL_RINV; vREAL_MUL_RID]]);;

let vREAL_SGN_MUL = try Cache.lookup_thm "REAL_SGN_MUL" with _ ->  prove
 ((parse_term "!x y. real_sgn(x * y) = real_sgn(x) * real_sgn(y)"),
  vREWRITE_TAC[vREAL_SGN; vREAL_ABS_MUL; real_div; vREAL_INV_MUL] ---->
  vREAL_ARITH_TAC);;

let vREAL_SGN_INV = try Cache.lookup_thm "REAL_SGN_INV" with _ ->  prove
 ((parse_term "!x. real_sgn(inv x) = real_sgn x"),
  vREWRITE_TAC[real_sgn; vREAL_LT_INV_EQ; vGSYM vREAL_INV_NEG;
              vREAL_ARITH (parse_term "x < &0 <=> &0 < --x")]);;

let vREAL_SGN_DIV = try Cache.lookup_thm "REAL_SGN_DIV" with _ ->  prove
 ((parse_term "!x y. real_sgn(x / y) = real_sgn(x) / real_sgn(y)"),
  vREWRITE_TAC[vREAL_SGN; vREAL_ABS_DIV] ---->
  vREWRITE_TAC[real_div; vREAL_INV_MUL; vREAL_INV_INV] ---->
  vREAL_ARITH_TAC);;

let vREAL_SGN_EQ = try Cache.lookup_thm "REAL_SGN_EQ" with _ ->  prove
 ((parse_term "(!x. real_sgn x = &0 <=> x = &0) /\\\n   (!x. real_sgn x = &1 <=> x > &0) /\\\n   (!x. real_sgn x = -- &1 <=> x < &0)"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_SGN_CASES = try Cache.lookup_thm "REAL_SGN_CASES" with _ ->  prove
 ((parse_term "!x. real_sgn x = &0 \\/ real_sgn x = &1 \\/ real_sgn x = -- &1"),
  vREWRITE_TAC[real_sgn] ----> vMESON_TAC[]);;

let vREAL_SGN_INEQS = try Cache.lookup_thm "REAL_SGN_INEQS" with _ ->  prove
 ((parse_term "(!x. &0 <= real_sgn x <=> &0 <= x) /\\\n   (!x. &0 < real_sgn x <=> &0 < x) /\\\n   (!x. &0 >= real_sgn x <=> &0 >= x) /\\\n   (!x. &0 > real_sgn x <=> &0 > x) /\\\n   (!x. &0 = real_sgn x <=> &0 = x) /\\\n   (!x. real_sgn x <= &0 <=> x <= &0) /\\\n   (!x. real_sgn x < &0 <=> x < &0) /\\\n   (!x. real_sgn x >= &0 <=> x >= &0) /\\\n   (!x. real_sgn x > &0 <=> x > &0) /\\\n   (!x. real_sgn x = &0 <=> x = &0)"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_SGN_POW = try Cache.lookup_thm "REAL_SGN_POW" with _ ->  prove
 ((parse_term "!x n. real_sgn(x pow n) = real_sgn(x) pow n"),
  vGEN_TAC ----> vINDUCT_TAC ----> vASM_REWRITE_TAC[vREAL_SGN_MUL; real_pow] ---->
  vREWRITE_TAC[real_sgn; vREAL_LT_01]);;

let vREAL_SGN_POW_2 = try Cache.lookup_thm "REAL_SGN_POW_2" with _ ->  prove
 ((parse_term "!x. real_sgn(x pow 2) = real_sgn(abs x)"),
  vREWRITE_TAC[real_sgn] ---->
  vSIMP_TAC[vGSYM vREAL_NOT_LE; vREAL_ABS_POS; vREAL_LE_POW_2;
           vREAL_ARITH (parse_term "&0 <= x ==> (x <= &0 <=> x = &0)")] ---->
  vREWRITE_TAC[vREAL_POW_EQ_0; vREAL_ABS_ZERO; vARITH]);;

let vREAL_SGN_REAL_SGN = try Cache.lookup_thm "REAL_SGN_REAL_SGN" with _ ->  prove
 ((parse_term "!x. real_sgn(real_sgn x) = real_sgn x"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_INV_SGN = try Cache.lookup_thm "REAL_INV_SGN" with _ ->  prove
 ((parse_term "!x. real_inv(real_sgn x) = real_sgn x"),
  vGEN_TAC ----> vREWRITE_TAC[real_sgn] ---->
  vREPEAT vCOND_CASES_TAC ---->
  vREWRITE_TAC[vREAL_INV_0; vREAL_INV_1; vREAL_INV_NEG]);;

let vREAL_SGN_EQ_INEQ = try Cache.lookup_thm "REAL_SGN_EQ_INEQ" with _ ->  prove
 ((parse_term "!x y. real_sgn x = real_sgn y <=>\n         x = y \\/ abs(x - y) < max (abs x) (abs y)"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_SGNS_EQ = try Cache.lookup_thm "REAL_SGNS_EQ" with _ ->  prove
 ((parse_term "!x y. real_sgn x = real_sgn y <=>\n         (x = &0 <=> y = &0) /\\\n         (x > &0 <=> y > &0) /\\\n         (x < &0 <=> y < &0)"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

let vREAL_SGNS_EQ_ALT = try Cache.lookup_thm "REAL_SGNS_EQ_ALT" with _ ->  prove
 ((parse_term "!x y. real_sgn x = real_sgn y <=>\n         (x = &0 ==> y = &0) /\\\n         (x > &0 ==> y > &0) /\\\n         (x < &0 ==> y < &0)"),
  vREWRITE_TAC[real_sgn] ----> vREAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Useful "without loss of generality" lemmas.                               *)
(* ------------------------------------------------------------------------- *)

let vREAL_WLOG_LE = try Cache.lookup_thm "REAL_WLOG_LE" with _ ->  prove
 ((parse_term "(!x y. P x y <=> P y x) /\\ (!x y. x <= y ==> P x y) ==> !x y. P x y"),
  vMESON_TAC[vREAL_LE_TOTAL]);;

let vREAL_WLOG_LT = try Cache.lookup_thm "REAL_WLOG_LT" with _ ->  prove
 ((parse_term "(!x. P x x) /\\ (!x y. P x y <=> P y x) /\\ (!x y. x < y ==> P x y)\n   ==> !x y. P x y"),
  vMESON_TAC[vREAL_LT_TOTAL]);;

let vREAL_WLOG_LE_3 = try Cache.lookup_thm "REAL_WLOG_LE_3" with _ ->  prove
 ((parse_term "!P. (!x y z. P x y z ==> P y x z /\\ P x z y) /\\\n       (!x y z:real. x <= y /\\ y <= z ==> P x y z)\n       ==> !x y z. P x y z"),
  vMESON_TAC[vREAL_LE_TOTAL]);;

(* ------------------------------------------------------------------------- *)
(* Square roots. The existence derivation is laborious but independent of    *)
(* any analytic or topological machinery, just using completeness directly.  *)
(* We totalize by making sqrt(-x) = -sqrt(x), which looks rather unnatural   *)
(* but allows many convenient properties to be used without sideconditions.  *)
(* ------------------------------------------------------------------------- *)

let sqrt = new_definition
 (parse_term "sqrt(x) = @y. real_sgn y = real_sgn x /\\ y pow 2 = abs x");;

let vSQRT_UNIQUE = try Cache.lookup_thm "SQRT_UNIQUE" with _ ->  prove
 ((parse_term "!x y. &0 <= y /\\ y pow 2 = x ==> sqrt(x) = y"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[sqrt] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vFIRST_X_ASSUM(vSUBST1_TAC -| vSYM) ---->
  vREWRITE_TAC[vREAL_SGN_POW_2; vREAL_ABS_POW] ---->
  vX_GEN_TAC (parse_term "z:real") ----> vASM_REWRITE_TAC[real_abs] ---->
  vREWRITE_TAC[vREAL_ENTIRE; vREAL_SUB_0; vREAL_ARITH
    (parse_term "x pow 2 = y pow 2 <=> (x - y) * (x - --y) = &0")] ---->
  vREWRITE_TAC[real_sgn] ----> vREPEAT(vPOP_ASSUM vMP_TAC) ---->
  vREAL_ARITH_TAC);;

let vPOW_2_SQRT = try Cache.lookup_thm "POW_2_SQRT" with _ ->  prove
 ((parse_term "!x. &0 <= x ==> sqrt(x pow 2) = x"),
  vMESON_TAC[vSQRT_UNIQUE]);;

let vSQRT_0 = try Cache.lookup_thm "SQRT_0" with _ ->  prove
 ((parse_term "sqrt(&0) = &0"),
  vMESON_TAC[vSQRT_UNIQUE; vREAL_POW_2; vREAL_MUL_LZERO; vREAL_POS]);;

let vSQRT_1 = try Cache.lookup_thm "SQRT_1" with _ ->  prove
 ((parse_term "sqrt(&1) = &1"),
   vMESON_TAC[vSQRT_UNIQUE; vREAL_POW_2; vREAL_MUL_LID; vREAL_POS]);;

let vPOW_2_SQRT_ABS = try Cache.lookup_thm "POW_2_SQRT_ABS" with _ ->  prove
 ((parse_term "!x. sqrt(x pow 2) = abs(x)"),
  vGEN_TAC ----> vMATCH_MP_TAC vSQRT_UNIQUE ---->
  vREWRITE_TAC[vREAL_ABS_POS; vREAL_POW_2; vGSYM vREAL_ABS_MUL] ---->
  vREWRITE_TAC[real_abs; vREAL_LE_SQUARE]);;

let vSQRT_WORKS_GEN = try Cache.lookup_thm "SQRT_WORKS_GEN" with _ ->  prove
 ((parse_term "!x. real_sgn(sqrt x) = real_sgn x /\\ sqrt(x) pow 2 = abs x"),
  let lemma = prove
   ((parse_term "!x y. x pow 2 < y ==> ?x'. x < x' /\\ x' pow 2 < y"),
    vREPEAT vSTRIP_TAC ---->
    vEXISTS_TAC (parse_term "abs x + min (&1) ((y - x pow 2) / (&2 * abs x + &2))") ---->
    vASSUME_TAC(vREAL_ARITH (parse_term "&0 < &2 * abs x + &1 /\\ &0 < &2 * abs x + &2")) ---->
    vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_SUB_LT; vREAL_ARITH
      (parse_term "&0 < y ==> x < abs x + min (&1) y")] ---->
    vREWRITE_TAC[vREAL_ARITH (parse_term "(x + e) pow 2 = e * (&2 * x + e) + x pow 2")] ---->
    vREWRITE_TAC[vREAL_POW2_ABS; vGSYM vREAL_LT_SUB_LADD] ---->
    vTRANS_TAC vREAL_LET_TRANS
      (parse_term "(y - x pow 2) / (&2 * abs x + &2) * (&2 * abs x + &1)") ---->
    vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_MUL2 ---->
      vREWRITE_TAC[vREAL_LE_MIN; vREAL_POS; vREAL_MIN_LE; vREAL_LE_REFL] ---->
      vASM_SIMP_TAC[vREAL_LE_ADD; vREAL_POS; vREAL_LE_MUL; vREAL_ABS_POS;
                   vREAL_LT_IMP_LE; vREAL_LT_DIV; vREAL_SUB_LT; vREAL_LE_MIN] ---->
      vREWRITE_TAC[vREAL_LE_LADD; vREAL_MIN_LE; vREAL_LE_REFL];
      vSIMP_TAC[real_div; vREAL_ARITH (parse_term "(a * inv b) * c = (a * c) * inv b")] ---->
      vREWRITE_TAC[vGSYM real_div] ---->
      vASM_SIMP_TAC[vREAL_LT_LDIV_EQ; vREAL_LT_LMUL_EQ; vREAL_SUB_LT] ---->
      vREAL_ARITH_TAC]) in
  let lemma' = prove
   ((parse_term "!x y. &0 < x /\\ &0 < y /\\ y < x pow 2\n           ==> ?x'. x' < x /\\ &0 < x' /\\ y < x' pow 2"),
    vREPEAT vSTRIP_TAC ---->
    vMP_TAC(vISPECL [(parse_term "inv(abs x):real"); (parse_term "inv y:real")] lemma) ---->
    vASM_SIMP_TAC[vREAL_POW_INV; vREAL_POW2_ABS; vREAL_LT_INV2] ---->
    vREWRITE_TAC[vGSYM vREAL_ABS_INV] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "x':real") vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC (parse_term "inv x':real") ----> vREWRITE_TAC[vREAL_POW_INV] ---->
    vREWRITE_TAC[vREAL_LT_INV_EQ] ----> vCONJ_TAC ++-->
     [vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_INV_INV];
      vCONJ_TAC ++--> [vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC;
      vALL_TAC] ---->
      vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_INV_INV]] ---->
    vMATCH_MP_TAC vREAL_LT_INV2 ---->
    (vCONJ_TAC ++-->
      [vALL_TAC; vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC]) ---->
    vASM_REWRITE_TAC[vREAL_LT_INV_EQ; vREAL_LT_POW_2] ---->
    vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC) in
  let main_lemma = prove
   ((parse_term "!y. &0 < y ==> ?x. x pow 2 = y"),
    vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_NZ) ---->
    vMP_TAC(vISPEC (parse_term "\\x. &0 <= x /\\ x pow 2 <= y") vREAL_COMPLETE) ---->
    vREWRITE_TAC[] ----> vANTS_TAC ++-->
     [vCONJ_TAC ++-->
       [vEXISTS_TAC (parse_term "&0") ----> vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC;
        vALL_TAC] ---->
      vEXISTS_TAC (parse_term "y + &1") ----> vX_GEN_TAC (parse_term "x:real") ---->
      vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
      vGEN_REWRITE_TAC vI [vGSYM vCONTRAPOS_THM] ---->
      vREWRITE_TAC[vREAL_NOT_LE] ----> vDISCH_TAC ---->
      vTRANS_TAC vREAL_LET_TRANS (parse_term "(y + &1) pow 2") ---->
      vASM_SIMP_TAC[vGSYM vREAL_LT_SQUARE_ABS; vREAL_POW_LT; vREAL_ARITH
       (parse_term "&0 < y /\\ &0 < y pow 2 ==> y <= (y + &1) pow 2")] ---->
      vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC;
      vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC (parse_term "s:real") ----> vSTRIP_TAC] ---->
    vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM; vGSYM vREAL_NOT_LT] ---->
    vREPEAT vSTRIP_TAC ++-->
     [vMP_TAC(vISPECL [(parse_term "s:real"); (parse_term "y:real")] lemma') ---->
      vASM_REWRITE_TAC[vNOT_IMP] ----> vCONJ_TAC ++-->
       [vUNDISCH_TAC (parse_term "y:real < s pow 2") ---->
        vASM_CASES_TAC (parse_term "s = &0") ----> vASM_REWRITE_TAC[vREAL_LT_LE] ---->
        vREWRITE_TAC[vREAL_POW_ZERO] ----> vCONV_TAC vNUM_REDUCE_CONV ---->
        vASM_REWRITE_TAC[vREAL_NOT_LE] ---->
        vSTRIP_TAC ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
        vUNDISCH_TAC (parse_term "&0 < y") ----> vREAL_ARITH_TAC;
        vDISCH_THEN(vX_CHOOSE_THEN (parse_term "z:real")
         (vCONJUNCTS_THEN2 vMP_TAC vSTRIP_ASSUME_TAC)) ---->
        vREWRITE_TAC[vREAL_NOT_LT] ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
        vX_GEN_TAC (parse_term "x:real") ---->
        vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
        vGEN_REWRITE_TAC vI [vGSYM vCONTRAPOS_THM] ---->
        vREWRITE_TAC[vREAL_NOT_LE] ----> vDISCH_TAC ---->
        vTRANS_TAC vREAL_LTE_TRANS (parse_term "(z:real) pow 2") ---->
        vASM_REWRITE_TAC[vGSYM vREAL_LE_SQUARE_ABS] ---->
        vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC];
      vMP_TAC(vISPECL [(parse_term "s:real"); (parse_term "y:real")] lemma) ----> vASM_REWRITE_TAC[] ---->
      vDISCH_THEN(vX_CHOOSE_THEN (parse_term "z:real")
       (vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC)) ---->
      vMATCH_MP_TAC(vREAL_ARITH (parse_term "abs z <= s ==> s < z ==> F")) ---->
      vFIRST_X_ASSUM vMATCH_MP_TAC ---->
      vASM_SIMP_TAC[vREAL_ABS_POS; vREAL_POW2_ABS; vREAL_LT_IMP_LE]]) in
  vGEN_TAC ----> vREWRITE_TAC[sqrt] ----> vCONV_TAC vSELECT_CONV ---->
  vSUBGOAL_THEN (parse_term "!x. &0 < x ==> ?y. &0 < y /\\ y pow 2 = x") vASSUME_TAC ++-->
   [vREPEAT vSTRIP_TAC ----> vMP_TAC(vSPEC (parse_term "x:real") main_lemma) ---->
    vASM_REWRITE_TAC[vLEFT_IMP_EXISTS_THM] ----> vX_GEN_TAC (parse_term "y:real") ---->
    vSTRIP_TAC ----> vEXISTS_TAC (parse_term "abs y:real") ---->
    vASM_REWRITE_TAC[vREAL_POW2_ABS; vGSYM vREAL_ABS_NZ] ---->
    vDISCH_THEN vSUBST_ALL_TAC ---->
    vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC;
    vASM_CASES_TAC (parse_term "x = &0") ---->
    vASM_REWRITE_TAC[vREAL_SGN_0; vREAL_SGN_EQ; vUNWIND_THM2] ---->
    vREWRITE_TAC[vREAL_ABS_NUM; vREAL_POW_ZERO; vARITH] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "abs x")) ---->
    vASM_REWRITE_TAC[vGSYM vREAL_ABS_NZ] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "y:real") vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC (parse_term "real_sgn x * y") ---->
    vASM_REWRITE_TAC[vREAL_POW_MUL; vGSYM vREAL_SGN_POW; vREAL_SGN_POW_2] ---->
    vREWRITE_TAC[vREAL_SGN_MUL; vREAL_SGN_REAL_SGN] ---->
    vASM_SIMP_TAC[real_sgn; vREAL_ARITH (parse_term "&0 < abs x <=> ~(x = &0)")] ---->
    vREWRITE_TAC[vREAL_MUL_LID; vREAL_MUL_RID]]);;

let vSQRT_UNIQUE_GEN = try Cache.lookup_thm "SQRT_UNIQUE_GEN" with _ ->  prove
 ((parse_term "!x y. real_sgn y = real_sgn x /\\ y pow 2 = abs x ==> sqrt x = y"),
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vGSYM(vSPEC (parse_term "x:real") vSQRT_WORKS_GEN)) ---->
  vSIMP_TAC[vREAL_ENTIRE; vREAL_SUB_0; vREAL_ARITH
    (parse_term "x pow 2 = y pow 2 <=> (x:real - y) * (x - --y) = &0")] ---->
  vDISCH_THEN(vK vALL_TAC) ----> vREWRITE_TAC[vIMP_CONJ_ALT] ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[vREAL_SGN_NEG] ---->
  vSIMP_TAC[vREAL_ARITH (parse_term "--x = x <=> x = &0"); vREAL_SGN_EQ; vREAL_NEG_0; vSQRT_0]);;

let vSQRT_NEG = try Cache.lookup_thm "SQRT_NEG" with _ ->  prove
 ((parse_term "!x. sqrt(--x) = --sqrt(x)"),
  vGEN_TAC ----> vMATCH_MP_TAC vSQRT_UNIQUE_GEN ---->
  vREWRITE_TAC[vREAL_SGN_NEG; vREAL_POW_NEG; vREAL_ABS_NEG; vARITH] ---->
  vREWRITE_TAC[vSQRT_WORKS_GEN]);;

let vREAL_SGN_SQRT = try Cache.lookup_thm "REAL_SGN_SQRT" with _ ->  prove
 ((parse_term "!x. real_sgn(sqrt x) = real_sgn x"),
  vREWRITE_TAC[vSQRT_WORKS_GEN]);;

let vSQRT_WORKS = try Cache.lookup_thm "SQRT_WORKS" with _ ->  prove
 ((parse_term "!x. &0 <= x ==> &0 <= sqrt(x) /\\ sqrt(x) pow 2 = x"),
  vREPEAT vSTRIP_TAC ----> vMP_TAC(vSPEC (parse_term "x:real") vSQRT_WORKS_GEN) ---->
  vREWRITE_TAC[real_sgn] ----> vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC);;

let vREAL_POS_EQ_SQUARE = try Cache.lookup_thm "REAL_POS_EQ_SQUARE" with _ ->  prove
 ((parse_term "!x. &0 <= x <=> ?y. y pow 2 = x"),
  vMESON_TAC[vREAL_LE_POW_2; vSQRT_WORKS]);;

let vSQRT_POS_LE = try Cache.lookup_thm "SQRT_POS_LE" with _ ->  prove
 ((parse_term "!x. &0 <= x ==> &0 <= sqrt(x)"),
  vMESON_TAC[vSQRT_WORKS]);;

let vSQRT_POW_2 = try Cache.lookup_thm "SQRT_POW_2" with _ ->  prove
 ((parse_term "!x. &0 <= x ==> sqrt(x) pow 2 = x"),
  vMESON_TAC[vSQRT_WORKS]);;

let vSQRT_POW2 = try Cache.lookup_thm "SQRT_POW2" with _ ->  prove
 ((parse_term "!x. sqrt(x) pow 2 = x <=> &0 <= x"),
  vMESON_TAC[vREAL_POW_2; vREAL_LE_SQUARE; vSQRT_POW_2]);;

let vSQRT_MUL = try Cache.lookup_thm "SQRT_MUL" with _ ->  prove
 ((parse_term "!x y. sqrt(x * y) = sqrt x * sqrt y"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vSQRT_UNIQUE_GEN ---->
  vREWRITE_TAC[vREAL_SGN_MUL; vREAL_POW_MUL; vSQRT_WORKS_GEN; vREAL_ABS_MUL]);;

let vSQRT_INV = try Cache.lookup_thm "SQRT_INV" with _ ->  prove
 ((parse_term "!x. sqrt (inv x) = inv(sqrt x)"),
  vGEN_TAC ----> vMATCH_MP_TAC vSQRT_UNIQUE_GEN ---->
  vREWRITE_TAC[vREAL_SGN_INV; vREAL_POW_INV; vREAL_ABS_INV; vSQRT_WORKS_GEN]);;

let vSQRT_DIV = try Cache.lookup_thm "SQRT_DIV" with _ ->  prove
 ((parse_term "!x y. sqrt (x / y) = sqrt x / sqrt y"),
  vREWRITE_TAC[real_div; vSQRT_MUL; vSQRT_INV]);;

let vSQRT_LT_0 = try Cache.lookup_thm "SQRT_LT_0" with _ ->  prove
 ((parse_term "!x. &0 < sqrt x <=> &0 < x"),
  vREWRITE_TAC[vGSYM real_gt; vGSYM vREAL_SGN_EQ; vREAL_SGN_SQRT]);;

let vSQRT_EQ_0 = try Cache.lookup_thm "SQRT_EQ_0" with _ ->  prove
 ((parse_term "!x. sqrt x = &0 <=> x = &0"),
  vONCE_REWRITE_TAC[vGSYM vREAL_SGN_EQ] ----> vREWRITE_TAC[vREAL_SGN_SQRT]);;

let vSQRT_LE_0 = try Cache.lookup_thm "SQRT_LE_0" with _ ->  prove
 ((parse_term "!x. &0 <= sqrt x <=> &0 <= x"),
  vREWRITE_TAC[vREAL_ARITH (parse_term "&0 <= x <=> &0 < x \\/ x = &0")] ---->
  vREWRITE_TAC[vSQRT_LT_0; vSQRT_EQ_0]);;

let vREAL_ABS_SQRT = try Cache.lookup_thm "REAL_ABS_SQRT" with _ ->  prove
 ((parse_term "!x. abs(sqrt x) = sqrt(abs x)"),
  vGEN_TAC ----> vREWRITE_TAC[real_abs; vSQRT_LE_0] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vSQRT_NEG]);;

let vSQRT_MONO_LT = try Cache.lookup_thm "SQRT_MONO_LT" with _ ->  prove
 ((parse_term "!x y. x < y ==> sqrt(x) < sqrt(y)"),
  vSUBGOAL_THEN (parse_term "!x y. &0 <= x /\\ x < y ==> sqrt x < sqrt y") vASSUME_TAC ++-->
   [vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_POW_LT2_REV ---->
    vEXISTS_TAC (parse_term "2") ----> vASM_REWRITE_TAC[vSQRT_WORKS_GEN; vSQRT_LE_0] ---->
    vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC;
    vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "&0 <= x") ----> vASM_SIMP_TAC[] ---->
    vASM_CASES_TAC (parse_term "&0 <= y") ++-->
     [vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC (parse_term "&0") ---->
      vASM_REWRITE_TAC[vGSYM vREAL_NOT_LE; vSQRT_LE_0];
      vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "--y:real"); (parse_term "--x:real")]) ---->
      vREWRITE_TAC[vSQRT_NEG] ----> vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC]]);;

let vSQRT_MONO_LE = try Cache.lookup_thm "SQRT_MONO_LE" with _ ->  prove
 ((parse_term "!x y. x <= y ==> sqrt(x) <= sqrt(y)"),
  vMESON_TAC[vREAL_LE_LT; vSQRT_MONO_LT]);;

let vSQRT_MONO_LT_EQ = try Cache.lookup_thm "SQRT_MONO_LT_EQ" with _ ->  prove
 ((parse_term "!x y. sqrt(x) < sqrt(y) <=> x < y"),
  vMESON_TAC[vREAL_NOT_LT; vSQRT_MONO_LT; vSQRT_MONO_LE]);;

let vSQRT_MONO_LE_EQ = try Cache.lookup_thm "SQRT_MONO_LE_EQ" with _ ->  prove
 ((parse_term "!x y. sqrt(x) <= sqrt(y) <=> x <= y"),
  vMESON_TAC[vREAL_NOT_LT; vSQRT_MONO_LT; vSQRT_MONO_LE]);;

let vSQRT_INJ = try Cache.lookup_thm "SQRT_INJ" with _ ->  prove
 ((parse_term "!x y. sqrt(x) = sqrt(y) <=> x = y"),
  vSIMP_TAC[vGSYM vREAL_LE_ANTISYM; vSQRT_MONO_LE_EQ]);;

let vSQRT_EQ_1 = try Cache.lookup_thm "SQRT_EQ_1" with _ ->  prove
 ((parse_term "!x. sqrt x = &1 <=> x = &1"),
  vMESON_TAC[vSQRT_INJ; vSQRT_1]);;

let vSQRT_POS_LT = try Cache.lookup_thm "SQRT_POS_LT" with _ ->  prove
 ((parse_term "!x. &0 < x ==> &0 < sqrt(x)"),
  vMESON_TAC[vREAL_LT_LE; vSQRT_POS_LE; vSQRT_EQ_0]);;

let vREAL_LE_LSQRT = try Cache.lookup_thm "REAL_LE_LSQRT" with _ ->  prove
 ((parse_term "!x y. &0 <= y /\\ x <= y pow 2 ==> sqrt(x) <= y"),
  vMESON_TAC[vSQRT_MONO_LE; vREAL_POW_LE; vPOW_2_SQRT]);;

let vREAL_LE_RSQRT = try Cache.lookup_thm "REAL_LE_RSQRT" with _ ->  prove
 ((parse_term "!x y. x pow 2 <= y ==> x <= sqrt(y)"),
  vMESON_TAC[vREAL_LE_TOTAL; vSQRT_MONO_LE; vSQRT_POS_LE; vREAL_POW_2;
            vREAL_LE_SQUARE; vREAL_LE_TRANS; vPOW_2_SQRT]);;

let vREAL_LT_LSQRT = try Cache.lookup_thm "REAL_LT_LSQRT" with _ ->  prove
 ((parse_term "!x y. &0 <= y /\\ x < y pow 2 ==> sqrt x < y"),
  vMESON_TAC[vSQRT_MONO_LT; vREAL_POW_LE; vPOW_2_SQRT]);;

let vREAL_LT_RSQRT = try Cache.lookup_thm "REAL_LT_RSQRT" with _ ->  prove
 ((parse_term "!x y. x pow 2 < y ==> x < sqrt(y)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC(vREAL_ARITH (parse_term "abs x < a ==> x < a")) ---->
  vREWRITE_TAC[vGSYM vPOW_2_SQRT_ABS] ----> vMATCH_MP_TAC vSQRT_MONO_LT ---->
  vASM_REWRITE_TAC[vREAL_POW_2; vREAL_LE_SQUARE]);;

let vSQRT_EVEN_POW2 = try Cache.lookup_thm "SQRT_EVEN_POW2" with _ ->  prove
 ((parse_term "!n. EVEN n ==> (sqrt(&2 pow n) = &2 pow (n DIV 2))"),
  vSIMP_TAC[vEVEN_EXISTS; vLEFT_IMP_EXISTS_THM; vDIV_MULT; vARITH_EQ] ---->
  vMESON_TAC[vSQRT_UNIQUE; vREAL_POW_POW; vMULT_SYM; vREAL_POW_LE; vREAL_POS]);;

let vREAL_DIV_SQRT = try Cache.lookup_thm "REAL_DIV_SQRT" with _ ->  prove
 ((parse_term "!x. &0 <= x ==> x / sqrt(x) = sqrt(x)"),
  vREWRITE_TAC[vREAL_LE_LT] ----> vREPEAT vSTRIP_TAC ++-->
   [vALL_TAC; vASM_MESON_TAC[vSQRT_0; real_div; vREAL_MUL_LZERO]] ---->
  vASM_SIMP_TAC[vREAL_EQ_LDIV_EQ; vSQRT_POS_LT; vGSYM vREAL_POW_2] ---->
  vASM_SIMP_TAC[vSQRT_POW_2; vREAL_LT_IMP_LE]);;

let vREAL_RSQRT_LE = try Cache.lookup_thm "REAL_RSQRT_LE" with _ ->  prove
 ((parse_term "!x y. &0 <= x /\\ &0 <= y /\\ x <= sqrt y ==> x pow 2 <= y"),
  vMESON_TAC[vREAL_POW_LE2; vSQRT_POW_2]);;

let vREAL_LSQRT_LE = try Cache.lookup_thm "REAL_LSQRT_LE" with _ ->  prove
 ((parse_term "!x y. &0 <= x /\\ sqrt x <= y ==> x <= y pow 2"),
  vMESON_TAC[vREAL_POW_LE2; vSQRT_POS_LE; vREAL_LE_TRANS; vSQRT_POW_2]);;

let vREAL_SQRT_POW_2 = try Cache.lookup_thm "REAL_SQRT_POW_2" with _ ->  prove
 ((parse_term "!x. sqrt x pow 2 = abs x"),
  vREWRITE_TAC[vSQRT_WORKS_GEN]);;

let vREAL_ABS_LE_SQRT_POS = try Cache.lookup_thm "REAL_ABS_LE_SQRT_POS" with _ ->  prove
 ((parse_term "!x y. &0 <= x /\\ &0 <= y ==> abs(sqrt x - sqrt y) <= sqrt(abs(x - y))"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_RSQRT ---->
  vREWRITE_TAC[vREAL_POW_2] ---->
  vTRANS_TAC vREAL_LE_TRANS (parse_term "abs(sqrt x - sqrt y) * abs(sqrt x + sqrt y)") ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_LE_LMUL ----> vREWRITE_TAC[vREAL_ABS_POS] ---->
    vMATCH_MP_TAC(vREAL_ARITH
     (parse_term "&0 <= x /\\ &0 <= y ==> abs(x - y) <= abs(x + y)")) ---->
    vASM_SIMP_TAC[vSQRT_POS_LE];
    vREWRITE_TAC[vGSYM vREAL_ABS_MUL; vREAL_ARITH
     (parse_term "(x - y:real) * (x + y) = x pow 2 - y pow 2")] ---->
    vASM_SIMP_TAC[vSQRT_POW_2; vREAL_LE_REFL]]);;

let vREAL_ABS_LE_SQRT = try Cache.lookup_thm "REAL_ABS_LE_SQRT" with _ ->  prove
 ((parse_term "!x y. abs(sqrt x - sqrt y) <= sqrt(&2 * abs(x - y))"),
  vMATCH_MP_TAC vREAL_WLOG_LE ---->
  vCONJ_TAC ++--> [vREWRITE_TAC[vREAL_ABS_SUB]; vALL_TAC] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "x:real"); (parse_term "y:real")] ----> vDISCH_TAC ---->
  vASM_CASES_TAC (parse_term "&0 <= x") ++-->
   [vTRANS_TAC vREAL_LE_TRANS (parse_term "sqrt(abs(x - y))") ---->
    vREWRITE_TAC[vSQRT_MONO_LE_EQ; vREAL_ARITH (parse_term "abs x <= &2 * abs x")] ---->
    vMATCH_MP_TAC vREAL_ABS_LE_SQRT_POS ---->
    vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC;
    vALL_TAC] ---->
  vASM_CASES_TAC (parse_term "&0 <= y") ++-->
   [vALL_TAC;
    vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "abs(x - y) = abs(--x - --y)")] ---->
    vREWRITE_TAC[vGSYM vSQRT_NEG] ---->
    vTRANS_TAC vREAL_LE_TRANS (parse_term "sqrt(abs(--x - --y))") ---->
    vREWRITE_TAC[vSQRT_MONO_LE_EQ; vREAL_ARITH (parse_term "abs x <= &2 * abs x")] ---->
    vMATCH_MP_TAC vREAL_ABS_LE_SQRT_POS ---->
    vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC] ---->
  vASM_SIMP_TAC[vSQRT_LE_0; vREAL_ARITH
   (parse_term "~(&0 <= x) /\\ &0 <= y ==> abs(x - y) = y - x")] ---->
  vMATCH_MP_TAC vREAL_LE_RSQRT ---->
  vMP_TAC(vSPEC (parse_term "sqrt(--x) - sqrt y") vREAL_LE_POW_2) ---->
  vREWRITE_TAC[vREAL_ARITH
   (parse_term "(x - y:real) pow 2 = (x pow 2 + y pow 2) - &2 * x * y")] ---->
  vREWRITE_TAC[vREAL_SQRT_POW_2] ----> vREWRITE_TAC[vSQRT_NEG; vREAL_ABS_NEG] ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREAL_ARITH_TAC);;
