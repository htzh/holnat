(* ========================================================================= *)
(* Theory of integers.                                                       *)
(*                                                                           *)
(* The integers are carved out of the real numbers; hence all the            *)
(* universal theorems can be derived trivially from the real analog.         *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Printer
open Preterm
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
open Pair
open Nums
open Arith
open Calc_num
open Normalizer
open Grobner
open Realax
open Calc_int
open Realarith
open Real

let [@warning "-33"] () = let open Calc_rat in ()

open Num

(* ------------------------------------------------------------------------- *)
(* Representing predicate. The "is_int" variant is useful for backwards      *)
(* compatibility with former definition of "is_int" constant, now removed.   *)
(* ------------------------------------------------------------------------- *)

let integer = new_definition
  (parse_term "integer(x) <=> ?n. abs(x) = &n");;

let is_int = try Cache.lookup_thm "is_int" with _ ->  prove
 ((parse_term "integer(x) <=> ?n. x = &n \\/ x = -- &n"),
  vREWRITE_TAC[integer] ----> vAP_TERM_TAC ----> vABS_TAC ----> vREAL_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Type of integers.                                                         *)
(* ------------------------------------------------------------------------- *)

let int_tybij = new_type_definition "int" ("int_of_real","real_of_int")
 (prove((parse_term "?x. integer x"),
       vEXISTS_TAC (parse_term "&0") ---->
       vREWRITE_TAC[is_int; vREAL_OF_NUM_EQ; vEXISTS_OR_THM; vGSYM vEXISTS_REFL]));;

let int_abstr,int_rep =
  vSPEC_ALL(vCONJUNCT1 int_tybij),vSPEC_ALL(vCONJUNCT2 int_tybij);;

let dest_int_rep = try Cache.lookup_thm "dest_int_rep" with _ ->  prove
 ((parse_term "!i. ?n. (real_of_int i = &n) \\/ (real_of_int i = --(&n))"),
  vREWRITE_TAC[vGSYM is_int; int_rep; int_abstr]);;

let vINTEGER_REAL_OF_INT = try Cache.lookup_thm "INTEGER_REAL_OF_INT" with _ ->  prove
 ((parse_term "!x. integer(real_of_int x)"),
  vMESON_TAC[int_tybij]);;

(* ------------------------------------------------------------------------- *)
(* We want the following too.                                                *)
(* ------------------------------------------------------------------------- *)

let int_eq = try Cache.lookup_thm "int_eq" with _ ->  prove
 ((parse_term "!x y. (x = y) <=> (real_of_int x = real_of_int y)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM(vMP_TAC -| vAP_TERM (parse_term "int_of_real")) ---->
  vREWRITE_TAC[int_abstr]);;

(* ------------------------------------------------------------------------- *)
(* Set up interface map.                                                     *)
(* ------------------------------------------------------------------------- *)

do_list overload_interface
 ["+",(parse_term "int_add:int->int->int"); "-",(parse_term "int_sub:int->int->int");
  "*",(parse_term "int_mul:int->int->int"); "<",(parse_term "int_lt:int->int->bool");
  "<=",(parse_term "int_le:int->int->bool"); ">",(parse_term "int_gt:int->int->bool");
  ">=",(parse_term "int_ge:int->int->bool"); "--",(parse_term "int_neg:int->int");
  "pow",(parse_term "int_pow:int->num->int"); "abs",(parse_term "int_abs:int->int");
  "max",(parse_term "int_max:int->int->int"); "min",(parse_term "int_min:int->int->int");
  "&",(parse_term "int_of_num:num->int")];;

let prioritize_int() = prioritize_overload(mk_type("int",[]));;

(* ------------------------------------------------------------------------- *)
(* Definitions and closure derivations of all operations but "inv" and "/".  *)
(* ------------------------------------------------------------------------- *)

let int_le = new_definition
  (parse_term "x <= y <=> (real_of_int x) <= (real_of_int y)");;

let int_lt = new_definition
  (parse_term "x < y <=> (real_of_int x) < (real_of_int y)");;

let int_ge = new_definition
  (parse_term "x >= y <=> (real_of_int x) >= (real_of_int y)");;

let int_gt = new_definition
  (parse_term "x > y <=> (real_of_int x) > (real_of_int y)");;

let int_of_num = new_definition
  (parse_term "&n = int_of_real(real_of_num n)");;

let int_of_num_th = try Cache.lookup_thm "int_of_num_th" with _ ->  prove
 ((parse_term "!n. real_of_int(int_of_num n) = real_of_num n"),
  vREWRITE_TAC[int_of_num; vGSYM int_rep; is_int] ---->
  vREWRITE_TAC[vREAL_OF_NUM_EQ; vEXISTS_OR_THM; vGSYM vEXISTS_REFL]);;

let int_neg = new_definition
 (parse_term "--i = int_of_real(--(real_of_int i))");;

let int_neg_th = try Cache.lookup_thm "int_neg_th" with _ ->  prove
 ((parse_term "!x. real_of_int(int_neg x) = --(real_of_int x)"),
  vREWRITE_TAC[int_neg; vGSYM int_rep; is_int] ---->
  vGEN_TAC ----> vSTRIP_ASSUME_TAC(vSPEC (parse_term "x:int") dest_int_rep) ---->
  vASM_REWRITE_TAC[vREAL_NEG_NEG; vEXISTS_OR_THM; vREAL_EQ_NEG2;
    vREAL_OF_NUM_EQ; vGSYM vEXISTS_REFL]);;

let int_add = new_definition
 (parse_term "x + y = int_of_real((real_of_int x) + (real_of_int y))");;

let int_add_th = try Cache.lookup_thm "int_add_th" with _ ->  prove
 ((parse_term "!x y. real_of_int(x + y) = (real_of_int x) + (real_of_int y)"),
  vREWRITE_TAC[int_add; vGSYM int_rep; is_int] ----> vREPEAT vGEN_TAC ---->
  vX_CHOOSE_THEN (parse_term "m:num") vDISJ_CASES_TAC (vSPEC (parse_term "x:int") dest_int_rep) ---->
  vX_CHOOSE_THEN (parse_term "n:num") vDISJ_CASES_TAC (vSPEC (parse_term "y:int") dest_int_rep) ---->
  vASM_REWRITE_TAC[vREAL_OF_NUM_ADD; vREAL_OF_NUM_EQ; vEXISTS_OR_THM] ---->
  vREWRITE_TAC[vGSYM vEXISTS_REFL] ---->
  vDISJ_CASES_THEN vMP_TAC (vSPECL [(parse_term "m:num"); (parse_term "n:num")] vLE_CASES) ---->
  vREWRITE_TAC[vLE_EXISTS] ----> vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:num") vSUBST1_TAC) ---->
  vREWRITE_TAC[vGSYM vREAL_OF_NUM_ADD; vOR_EXISTS_THM; vREAL_NEG_ADD] ---->
  vTRY(vEXISTS_TAC (parse_term "d:num") ----> vREAL_ARITH_TAC) ---->
  vREWRITE_TAC[vEXISTS_OR_THM; vGSYM vREAL_NEG_ADD; vREAL_EQ_NEG2;
    vREAL_OF_NUM_ADD; vREAL_OF_NUM_EQ; vGSYM vEXISTS_REFL]);;

let int_sub = new_definition
  (parse_term "x - y = int_of_real(real_of_int x - real_of_int y)");;

let int_sub_th = try Cache.lookup_thm "int_sub_th" with _ ->  prove
 ((parse_term "!x y. real_of_int(x - y) = (real_of_int x) - (real_of_int y)"),
  vREWRITE_TAC[int_sub; real_sub; vGSYM int_neg_th; vGSYM int_add_th] ---->
  vREWRITE_TAC[int_abstr]);;

let int_mul = new_definition
  (parse_term "x * y = int_of_real ((real_of_int x) * (real_of_int y))");;

let int_mul_th = try Cache.lookup_thm "int_mul_th" with _ ->  prove
 ((parse_term "!x y. real_of_int(x * y) = (real_of_int x) * (real_of_int y)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[int_mul; vGSYM int_rep; is_int] ---->
  vX_CHOOSE_THEN (parse_term "m:num") vDISJ_CASES_TAC (vSPEC (parse_term "x:int") dest_int_rep) ---->
  vX_CHOOSE_THEN (parse_term "n:num") vDISJ_CASES_TAC (vSPEC (parse_term "y:int") dest_int_rep) ---->
  vASM_REWRITE_TAC[vREAL_OF_NUM_ADD; vREAL_OF_NUM_EQ; vEXISTS_OR_THM] ---->
  vREWRITE_TAC[vREAL_MUL_LNEG; vREAL_MUL_RNEG; vREAL_NEG_NEG; vREAL_OF_NUM_MUL] ---->
  vREWRITE_TAC[vREAL_EQ_NEG2; vREAL_OF_NUM_EQ; vGSYM vEXISTS_REFL]);;

let int_abs = new_definition
  (parse_term "abs x = int_of_real(abs(real_of_int x))");;

let int_abs_th = try Cache.lookup_thm "int_abs_th" with _ ->  prove
 ((parse_term "!x. real_of_int(abs x) = abs(real_of_int x)"),
  vGEN_TAC ----> vREWRITE_TAC[int_abs; real_abs] ----> vCOND_CASES_TAC ---->
  vREWRITE_TAC[vGSYM int_neg; int_neg_th; int_abstr]);;

let int_sgn = new_definition
  (parse_term "int_sgn x = int_of_real(real_sgn(real_of_int x))");;

let int_sgn_th = try Cache.lookup_thm "int_sgn_th" with _ ->  prove
 ((parse_term "!x. real_of_int(int_sgn x) = real_sgn(real_of_int x)"),
  vGEN_TAC ----> vREWRITE_TAC[int_sgn; real_sgn; vGSYM int_rep] ---->
  vREPEAT(vCOND_CASES_TAC ----> vASM_REWRITE_TAC[]) ---->
  vMESON_TAC[is_int]);;

let int_max = new_definition
  (parse_term "int_max x y = int_of_real(max (real_of_int x) (real_of_int y))");;

let int_max_th = try Cache.lookup_thm "int_max_th" with _ ->  prove
 ((parse_term "!x y. real_of_int(max x y) = max (real_of_int x) (real_of_int y)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[int_max; real_max] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[int_abstr]);;

let int_min = new_definition
  (parse_term "int_min x y = int_of_real(min (real_of_int x) (real_of_int y))");;

let int_min_th = try Cache.lookup_thm "int_min_th" with _ ->  prove
 ((parse_term "!x y. real_of_int(min x y) = min (real_of_int x) (real_of_int y)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[int_min; real_min] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[int_abstr]);;

let int_pow = new_definition
  (parse_term "x pow n = int_of_real((real_of_int x) pow n)");;

let int_pow_th = try Cache.lookup_thm "int_pow_th" with _ ->  prove
 ((parse_term "!x n. real_of_int(x pow n) = (real_of_int x) pow n"),
  vGEN_TAC ----> vREWRITE_TAC[int_pow] ----> vINDUCT_TAC ---->
  vREWRITE_TAC[real_pow] ++-->
   [vREWRITE_TAC[vGSYM int_of_num; int_of_num_th];
    vPOP_ASSUM(vSUBST1_TAC -| vSYM) ---->
    vASM_REWRITE_TAC[vGSYM int_mul; int_mul_th]]);;

(* ------------------------------------------------------------------------- *)
(* A few convenient theorems about the integer type.                         *)
(* ------------------------------------------------------------------------- *)

let vINT_IMAGE = try Cache.lookup_thm "INT_IMAGE" with _ ->  prove
 ((parse_term "!x. (?n. x = &n) \\/ (?n. x = --(&n))"),
  vGEN_TAC ---->
  vX_CHOOSE_THEN (parse_term "n:num") vDISJ_CASES_TAC (vSPEC (parse_term "x:int") dest_int_rep) ---->
  vPOP_ASSUM(vMP_TAC -| vAP_TERM (parse_term "int_of_real")) ----> vREWRITE_TAC[int_abstr] ---->
  vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[int_of_num; int_neg] ++-->
   [vDISJ1_TAC; vDISJ2_TAC] ---->
  vEXISTS_TAC (parse_term "n:num") ----> vREWRITE_TAC[int_abstr] ---->
  vREWRITE_TAC[vGSYM int_of_num; int_of_num_th]);;

let vFORALL_INT_CASES = try Cache.lookup_thm "FORALL_INT_CASES" with _ ->  prove
 ((parse_term "!P:int->bool. (!x. P x) <=> (!n. P(&n)) /\\ (!n. P(-- &n))"),
  vMESON_TAC[vINT_IMAGE]);;

let vEXISTS_INT_CASES = try Cache.lookup_thm "EXISTS_INT_CASES" with _ ->  prove
 ((parse_term "!P:int->bool. (?x. P x) <=> (?n. P(&n)) \\/ (?n. P(-- &n))"),
  vMESON_TAC[vINT_IMAGE]);;

let vINT_LT_DISCRETE = try Cache.lookup_thm "INT_LT_DISCRETE" with _ ->  prove
 ((parse_term "!x y. x < y <=> (x + &1) <= y"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[int_le; int_lt; int_add_th] ---->
  vDISJ_CASES_THEN(vX_CHOOSE_THEN (parse_term "m:num") vSUBST1_TAC )
   (vSPEC (parse_term "x:int") vINT_IMAGE) ---->
  vDISJ_CASES_THEN(vX_CHOOSE_THEN (parse_term "n:num") vSUBST1_TAC )
   (vSPEC (parse_term "y:int") vINT_IMAGE) ---->
  vREWRITE_TAC[int_neg_th; int_of_num_th] ---->
  vREWRITE_TAC[vREAL_LE_NEG2; vREAL_LT_NEG2] ---->
  vREWRITE_TAC[vREAL_LE_LNEG; vREAL_LT_LNEG; vREAL_LE_RNEG; vREAL_LT_RNEG] ---->
  vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC] ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vREWRITE_TAC[vGSYM real_sub; vREAL_LE_SUB_RADD] ---->
  vREWRITE_TAC[vREAL_OF_NUM_LE; vREAL_OF_NUM_LT; vREAL_OF_NUM_ADD] ---->
  vREWRITE_TAC[vGSYM vADD1; vONCE_REWRITE_RULE[vADD_SYM] (vGSYM vADD1)] ---->
  vREWRITE_TAC[vSYM(vREWRITE_CONV[vARITH_SUC] (parse_term "SUC 0"))] ---->
  vREWRITE_TAC[vADD_CLAUSES; vLE_SUC_LT; vLT_SUC_LE]);;

let vINT_GT_DISCRETE = try Cache.lookup_thm "INT_GT_DISCRETE" with _ ->  prove
 ((parse_term "!x y. x > y <=> x >= (y + &1)"),
  vREWRITE_TAC[int_gt; int_ge; real_ge; real_gt; vGSYM int_le; vGSYM int_lt] ---->
  vMATCH_ACCEPT_TAC vINT_LT_DISCRETE);;

(* ------------------------------------------------------------------------- *)
(* Conversions of integer constants to and from OCaml numbers.               *)
(* ------------------------------------------------------------------------- *)

let is_intconst tm =
  match tm with
    Comb(Const("int_of_num",_),n) -> is_numeral n
  | Comb(Const("int_neg",_),Comb(Const("int_of_num",_),n)) ->
      is_numeral n && not(dest_numeral n = num_0)
  | _ -> false;;

let dest_intconst tm =
  match tm with
    Comb(Const("int_of_num",_),n) -> dest_numeral n
  | Comb(Const("int_neg",_),Comb(Const("int_of_num",_),n)) ->
        let nn = dest_numeral n in
        if nn <>/ num_0 then minus_num(dest_numeral n)
        else failwith "dest_intconst"
  | _ -> failwith "dest_intconst";;

let mk_intconst =
  let cast_tm = (parse_term "int_of_num") and neg_tm = (parse_term "int_neg") in
  let mk_numconst n = mk_comb(cast_tm,mk_numeral n) in
  fun x -> if x </ num_0 then mk_comb(neg_tm,mk_numconst(minus_num x))
           else mk_numconst x;;

(* ------------------------------------------------------------------------- *)
(* A simple procedure to lift most universal real theorems to integers.      *)
(* For a more complete procedure, give required term to INT_ARITH (below).   *)
(* ------------------------------------------------------------------------- *)

let vINT_OF_REAL_THM =
  let dest = (parse_term "real_of_int")
  and real_ty = (parse_type "real")
  and int_ty = (parse_type "int")
  and cond_th = prove
   ((parse_term "real_of_int(if b then x else y) =\n       if b then real_of_int x else real_of_int y"),
    vCOND_CASES_TAC ----> vREWRITE_TAC[]) in
  let thlist = map vGSYM
   [int_eq; int_le; int_lt; int_ge; int_gt;
    int_of_num_th; int_neg_th; int_add_th; int_mul_th; int_sgn_th;
    int_sub_th; int_abs_th; int_max_th; int_min_th; int_pow_th; cond_th] in
  let vREW_RULE = vGEN_REWRITE_RULE vDEPTH_CONV thlist in
  let int_tm_of_real_var v =
    let s,ty = dest_var v in
    if ty = real_ty then mk_comb(dest,mk_var(s,int_ty)) else v in
  let int_of_real_var v =
    let s,ty = dest_var v in
    if ty = real_ty then mk_var(s,int_ty) else v in
  let vINT_OF_REAL_THM1 th =
    let newavs = subtract (frees (concl th)) (freesl (hyp th)) in
    let avs,_bod = strip_forall(concl th) in
    let allavs = newavs@avs in
    let avs' = map int_tm_of_real_var allavs in
    let avs'' = map int_of_real_var avs in
    vGENL avs'' (vREW_RULE(vSPECL avs' (vGENL newavs th))) in
  let rec vINT_OF_REAL_THM th =
    if is_conj(concl th) then vCONJ (vINT_OF_REAL_THM (vCONJUNCT1 th))
                                   (vINT_OF_REAL_THM (vCONJUNCT2 th))
    else vINT_OF_REAL_THM1 th in
  vINT_OF_REAL_THM;;

(* ------------------------------------------------------------------------- *)
(* Collect together all the theorems derived automatically.                  *)
(* ------------------------------------------------------------------------- *)

let vINT_ABS_0 = try Cache.lookup_thm "INT_ABS_0" with _ ->  vINT_OF_REAL_THM vREAL_ABS_0;;
let vINT_ABS_1 = try Cache.lookup_thm "INT_ABS_1" with _ ->  vINT_OF_REAL_THM vREAL_ABS_1;;
let vINT_ABS_ABS = try Cache.lookup_thm "INT_ABS_ABS" with _ ->  vINT_OF_REAL_THM vREAL_ABS_ABS;;
let vINT_ABS_BETWEEN = try Cache.lookup_thm "INT_ABS_BETWEEN" with _ ->  vINT_OF_REAL_THM vREAL_ABS_BETWEEN;;
let vINT_ABS_BETWEEN1 = try Cache.lookup_thm "INT_ABS_BETWEEN1" with _ ->  vINT_OF_REAL_THM vREAL_ABS_BETWEEN1;;
let vINT_ABS_BETWEEN2 = try Cache.lookup_thm "INT_ABS_BETWEEN2" with _ ->  vINT_OF_REAL_THM vREAL_ABS_BETWEEN2;;
let vINT_ABS_BOUND = try Cache.lookup_thm "INT_ABS_BOUND" with _ ->  vINT_OF_REAL_THM vREAL_ABS_BOUND;;
let vINT_ABS_CASES = try Cache.lookup_thm "INT_ABS_CASES" with _ ->  vINT_OF_REAL_THM vREAL_ABS_CASES;;
let vINT_ABS_CIRCLE = try Cache.lookup_thm "INT_ABS_CIRCLE" with _ ->  vINT_OF_REAL_THM vREAL_ABS_CIRCLE;;
let vINT_ABS_LE = try Cache.lookup_thm "INT_ABS_LE" with _ ->  vINT_OF_REAL_THM vREAL_ABS_LE;;
let vINT_ABS_MUL = try Cache.lookup_thm "INT_ABS_MUL" with _ ->  vINT_OF_REAL_THM vREAL_ABS_MUL;;
let vINT_ABS_NEG = try Cache.lookup_thm "INT_ABS_NEG" with _ ->  vINT_OF_REAL_THM vREAL_ABS_NEG;;
let vINT_ABS_NUM = try Cache.lookup_thm "INT_ABS_NUM" with _ ->  vINT_OF_REAL_THM vREAL_ABS_NUM;;
let vINT_ABS_NZ = try Cache.lookup_thm "INT_ABS_NZ" with _ ->  vINT_OF_REAL_THM vREAL_ABS_NZ;;
let vINT_ABS_POS = try Cache.lookup_thm "INT_ABS_POS" with _ ->  vINT_OF_REAL_THM vREAL_ABS_POS;;
let vINT_ABS_POW = try Cache.lookup_thm "INT_ABS_POW" with _ ->  vINT_OF_REAL_THM vREAL_ABS_POW;;
let vINT_ABS_REFL = try Cache.lookup_thm "INT_ABS_REFL" with _ ->  vINT_OF_REAL_THM vREAL_ABS_REFL;;
let vINT_ABS_SGN = try Cache.lookup_thm "INT_ABS_SGN" with _ ->  vINT_OF_REAL_THM vREAL_ABS_SGN;;
let vINT_ABS_SIGN = try Cache.lookup_thm "INT_ABS_SIGN" with _ ->  vINT_OF_REAL_THM vREAL_ABS_SIGN;;
let vINT_ABS_SIGN2 = try Cache.lookup_thm "INT_ABS_SIGN2" with _ ->  vINT_OF_REAL_THM vREAL_ABS_SIGN2;;
let vINT_ABS_STILLNZ = try Cache.lookup_thm "INT_ABS_STILLNZ" with _ ->  vINT_OF_REAL_THM vREAL_ABS_STILLNZ;;
let vINT_ABS_SUB = try Cache.lookup_thm "INT_ABS_SUB" with _ ->  vINT_OF_REAL_THM vREAL_ABS_SUB;;
let vINT_ABS_SUB_ABS = try Cache.lookup_thm "INT_ABS_SUB_ABS" with _ ->  vINT_OF_REAL_THM vREAL_ABS_SUB_ABS;;
let vINT_ABS_TRIANGLE = try Cache.lookup_thm "INT_ABS_TRIANGLE" with _ ->  vINT_OF_REAL_THM vREAL_ABS_TRIANGLE;;
let vINT_ABS_ZERO = try Cache.lookup_thm "INT_ABS_ZERO" with _ ->  vINT_OF_REAL_THM vREAL_ABS_ZERO;;
let vINT_ADD2_SUB2 = try Cache.lookup_thm "INT_ADD2_SUB2" with _ ->  vINT_OF_REAL_THM vREAL_ADD2_SUB2;;
let vINT_ADD_AC = try Cache.lookup_thm "INT_ADD_AC" with _ ->  vINT_OF_REAL_THM vREAL_ADD_AC;;
let vINT_ADD_ASSOC = try Cache.lookup_thm "INT_ADD_ASSOC" with _ ->  vINT_OF_REAL_THM vREAL_ADD_ASSOC;;
let vINT_ADD_LDISTRIB = try Cache.lookup_thm "INT_ADD_LDISTRIB" with _ ->  vINT_OF_REAL_THM vREAL_ADD_LDISTRIB;;
let vINT_ADD_LID = try Cache.lookup_thm "INT_ADD_LID" with _ ->  vINT_OF_REAL_THM vREAL_ADD_LID;;
let vINT_ADD_LINV = try Cache.lookup_thm "INT_ADD_LINV" with _ ->  vINT_OF_REAL_THM vREAL_ADD_LINV;;
let vINT_ADD_RDISTRIB = try Cache.lookup_thm "INT_ADD_RDISTRIB" with _ ->  vINT_OF_REAL_THM vREAL_ADD_RDISTRIB;;
let vINT_ADD_RID = try Cache.lookup_thm "INT_ADD_RID" with _ ->  vINT_OF_REAL_THM vREAL_ADD_RID;;
let vINT_ADD_RINV = try Cache.lookup_thm "INT_ADD_RINV" with _ ->  vINT_OF_REAL_THM vREAL_ADD_RINV;;
let vINT_ADD_SUB = try Cache.lookup_thm "INT_ADD_SUB" with _ ->  vINT_OF_REAL_THM vREAL_ADD_SUB;;
let vINT_ADD_SUB2 = try Cache.lookup_thm "INT_ADD_SUB2" with _ ->  vINT_OF_REAL_THM vREAL_ADD_SUB2;;
let vINT_ADD_SYM = try Cache.lookup_thm "INT_ADD_SYM" with _ ->  vINT_OF_REAL_THM vREAL_ADD_SYM;;
let vINT_BOUNDS_LE = try Cache.lookup_thm "INT_BOUNDS_LE" with _ ->  vINT_OF_REAL_THM vREAL_BOUNDS_LE;;
let vINT_BOUNDS_LT = try Cache.lookup_thm "INT_BOUNDS_LT" with _ ->  vINT_OF_REAL_THM vREAL_BOUNDS_LT;;
let vINT_DIFFSQ = try Cache.lookup_thm "INT_DIFFSQ" with _ ->  vINT_OF_REAL_THM vREAL_DIFFSQ;;
let vINT_ENTIRE = try Cache.lookup_thm "INT_ENTIRE" with _ ->  vINT_OF_REAL_THM vREAL_ENTIRE;;
let vINT_EQ_ADD_LCANCEL = try Cache.lookup_thm "INT_EQ_ADD_LCANCEL" with _ ->  vINT_OF_REAL_THM vREAL_EQ_ADD_LCANCEL;;
let vINT_EQ_ADD_LCANCEL_0 = try Cache.lookup_thm "INT_EQ_ADD_LCANCEL_0" with _ ->  vINT_OF_REAL_THM vREAL_EQ_ADD_LCANCEL_0;;
let vINT_EQ_ADD_RCANCEL = try Cache.lookup_thm "INT_EQ_ADD_RCANCEL" with _ ->  vINT_OF_REAL_THM vREAL_EQ_ADD_RCANCEL;;
let vINT_EQ_ADD_RCANCEL_0 = try Cache.lookup_thm "INT_EQ_ADD_RCANCEL_0" with _ ->  vINT_OF_REAL_THM vREAL_EQ_ADD_RCANCEL_0;;
let vINT_EQ_IMP_LE = try Cache.lookup_thm "INT_EQ_IMP_LE" with _ ->  vINT_OF_REAL_THM vREAL_EQ_IMP_LE;;
let vINT_EQ_MUL_LCANCEL = try Cache.lookup_thm "INT_EQ_MUL_LCANCEL" with _ ->  vINT_OF_REAL_THM vREAL_EQ_MUL_LCANCEL;;
let vINT_EQ_MUL_RCANCEL = try Cache.lookup_thm "INT_EQ_MUL_RCANCEL" with _ ->  vINT_OF_REAL_THM vREAL_EQ_MUL_RCANCEL;;
let vINT_EQ_NEG2 = try Cache.lookup_thm "INT_EQ_NEG2" with _ ->  vINT_OF_REAL_THM vREAL_EQ_NEG2;;
let vINT_EQ_SGN_ABS = try Cache.lookup_thm "INT_EQ_SGN_ABS" with _ ->  vINT_OF_REAL_THM vREAL_EQ_SGN_ABS;;
let vINT_EQ_SQUARE_ABS = try Cache.lookup_thm "INT_EQ_SQUARE_ABS" with _ ->  vINT_OF_REAL_THM vREAL_EQ_SQUARE_ABS;;
let vINT_EQ_SUB_LADD = try Cache.lookup_thm "INT_EQ_SUB_LADD" with _ ->  vINT_OF_REAL_THM vREAL_EQ_SUB_LADD;;
let vINT_EQ_SUB_RADD = try Cache.lookup_thm "INT_EQ_SUB_RADD" with _ ->  vINT_OF_REAL_THM vREAL_EQ_SUB_RADD;;
let vINT_LET_ADD = try Cache.lookup_thm "INT_LET_ADD" with _ ->  vINT_OF_REAL_THM vREAL_LET_ADD;;
let vINT_LET_ADD2 = try Cache.lookup_thm "INT_LET_ADD2" with _ ->  vINT_OF_REAL_THM vREAL_LET_ADD2;;
let vINT_LET_ANTISYM = try Cache.lookup_thm "INT_LET_ANTISYM" with _ ->  vINT_OF_REAL_THM vREAL_LET_ANTISYM;;
let vINT_LET_TOTAL = try Cache.lookup_thm "INT_LET_TOTAL" with _ ->  vINT_OF_REAL_THM vREAL_LET_TOTAL;;
let vINT_LET_TRANS = try Cache.lookup_thm "INT_LET_TRANS" with _ ->  vINT_OF_REAL_THM vREAL_LET_TRANS;;
let vINT_LE_01 = try Cache.lookup_thm "INT_LE_01" with _ ->  vINT_OF_REAL_THM vREAL_LE_01;;
let vINT_LE_ADD = try Cache.lookup_thm "INT_LE_ADD" with _ ->  vINT_OF_REAL_THM vREAL_LE_ADD;;
let vINT_LE_ADD2 = try Cache.lookup_thm "INT_LE_ADD2" with _ ->  vINT_OF_REAL_THM vREAL_LE_ADD2;;
let vINT_LE_ADDL = try Cache.lookup_thm "INT_LE_ADDL" with _ ->  vINT_OF_REAL_THM vREAL_LE_ADDL;;
let vINT_LE_ADDR = try Cache.lookup_thm "INT_LE_ADDR" with _ ->  vINT_OF_REAL_THM vREAL_LE_ADDR;;
let vINT_LE_ANTISYM = try Cache.lookup_thm "INT_LE_ANTISYM" with _ ->  vINT_OF_REAL_THM vREAL_LE_ANTISYM;;
let vINT_LE_DOUBLE = try Cache.lookup_thm "INT_LE_DOUBLE" with _ ->  vINT_OF_REAL_THM vREAL_LE_DOUBLE;;
let vINT_LE_LADD = try Cache.lookup_thm "INT_LE_LADD" with _ ->  vINT_OF_REAL_THM vREAL_LE_LADD;;
let vINT_LE_LADD_IMP = try Cache.lookup_thm "INT_LE_LADD_IMP" with _ ->  vINT_OF_REAL_THM vREAL_LE_LADD_IMP;;
let vINT_LE_LMUL = try Cache.lookup_thm "INT_LE_LMUL" with _ ->  vINT_OF_REAL_THM vREAL_LE_LMUL;;
let vINT_LE_LMUL_EQ = try Cache.lookup_thm "INT_LE_LMUL_EQ" with _ ->  vINT_OF_REAL_THM vREAL_LE_LMUL_EQ;;
let vINT_LE_LNEG = try Cache.lookup_thm "INT_LE_LNEG" with _ ->  vINT_OF_REAL_THM vREAL_LE_LNEG;;
let vINT_LE_LT = try Cache.lookup_thm "INT_LE_LT" with _ ->  vINT_OF_REAL_THM vREAL_LE_LT;;
let vINT_LE_MAX = try Cache.lookup_thm "INT_LE_MAX" with _ ->  vINT_OF_REAL_THM vREAL_LE_MAX;;
let vINT_LE_MIN = try Cache.lookup_thm "INT_LE_MIN" with _ ->  vINT_OF_REAL_THM vREAL_LE_MIN;;
let vINT_LE_MUL = try Cache.lookup_thm "INT_LE_MUL" with _ ->  vINT_OF_REAL_THM vREAL_LE_MUL;;
let vINT_LE_MUL_EQ = try Cache.lookup_thm "INT_LE_MUL_EQ" with _ ->  vINT_OF_REAL_THM vREAL_LE_MUL_EQ;;
let vINT_LE_MUL2 = try Cache.lookup_thm "INT_LE_MUL2" with _ ->  vINT_OF_REAL_THM vREAL_LE_MUL2;;
let vINT_LE_NEG2 = try Cache.lookup_thm "INT_LE_NEG2" with _ ->  vINT_OF_REAL_THM vREAL_LE_NEG2;;
let vINT_LE_NEGL = try Cache.lookup_thm "INT_LE_NEGL" with _ ->  vINT_OF_REAL_THM vREAL_LE_NEGL;;
let vINT_LE_NEGR = try Cache.lookup_thm "INT_LE_NEGR" with _ ->  vINT_OF_REAL_THM vREAL_LE_NEGR;;
let vINT_LE_NEGTOTAL = try Cache.lookup_thm "INT_LE_NEGTOTAL" with _ ->  vINT_OF_REAL_THM vREAL_LE_NEGTOTAL;;
let vINT_LE_POW2 = try Cache.lookup_thm "INT_LE_POW2" with _ ->  vINT_OF_REAL_THM vREAL_LE_POW2;;
let vINT_LE_RADD = try Cache.lookup_thm "INT_LE_RADD" with _ ->  vINT_OF_REAL_THM vREAL_LE_RADD;;
let vINT_LE_REFL = try Cache.lookup_thm "INT_LE_REFL" with _ ->  vINT_OF_REAL_THM vREAL_LE_REFL;;
let vINT_LE_RMUL = try Cache.lookup_thm "INT_LE_RMUL" with _ ->  vINT_OF_REAL_THM vREAL_LE_RMUL;;
let vINT_LE_RNEG = try Cache.lookup_thm "INT_LE_RNEG" with _ ->  vINT_OF_REAL_THM vREAL_LE_RNEG;;
let vINT_LE_SQUARE = try Cache.lookup_thm "INT_LE_SQUARE" with _ ->  vINT_OF_REAL_THM vREAL_LE_SQUARE;;
let vINT_LE_SQUARE_ABS = try Cache.lookup_thm "INT_LE_SQUARE_ABS" with _ ->  vINT_OF_REAL_THM vREAL_LE_SQUARE_ABS;;
let vINT_LE_SUB_LADD = try Cache.lookup_thm "INT_LE_SUB_LADD" with _ ->  vINT_OF_REAL_THM vREAL_LE_SUB_LADD;;
let vINT_LE_SUB_RADD = try Cache.lookup_thm "INT_LE_SUB_RADD" with _ ->  vINT_OF_REAL_THM vREAL_LE_SUB_RADD;;
let vINT_LE_TOTAL = try Cache.lookup_thm "INT_LE_TOTAL" with _ ->  vINT_OF_REAL_THM vREAL_LE_TOTAL;;
let vINT_LE_TRANS = try Cache.lookup_thm "INT_LE_TRANS" with _ ->  vINT_OF_REAL_THM vREAL_LE_TRANS;;
let vINT_LNEG_UNIQ = try Cache.lookup_thm "INT_LNEG_UNIQ" with _ ->  vINT_OF_REAL_THM vREAL_LNEG_UNIQ;;
let vINT_LTE_ADD = try Cache.lookup_thm "INT_LTE_ADD" with _ ->  vINT_OF_REAL_THM vREAL_LTE_ADD;;
let vINT_LTE_ADD2 = try Cache.lookup_thm "INT_LTE_ADD2" with _ ->  vINT_OF_REAL_THM vREAL_LTE_ADD2;;
let vINT_LTE_ANTISYM = try Cache.lookup_thm "INT_LTE_ANTISYM" with _ ->  vINT_OF_REAL_THM vREAL_LTE_ANTISYM;;
let vINT_LTE_TOTAL = try Cache.lookup_thm "INT_LTE_TOTAL" with _ ->  vINT_OF_REAL_THM vREAL_LTE_TOTAL;;
let vINT_LTE_TRANS = try Cache.lookup_thm "INT_LTE_TRANS" with _ ->  vINT_OF_REAL_THM vREAL_LTE_TRANS;;
let vINT_LT_01 = try Cache.lookup_thm "INT_LT_01" with _ ->  vINT_OF_REAL_THM vREAL_LT_01;;
let vINT_LT_ADD = try Cache.lookup_thm "INT_LT_ADD" with _ ->  vINT_OF_REAL_THM vREAL_LT_ADD;;
let vINT_LT_ADD1 = try Cache.lookup_thm "INT_LT_ADD1" with _ ->  vINT_OF_REAL_THM vREAL_LT_ADD1;;
let vINT_LT_ADD2 = try Cache.lookup_thm "INT_LT_ADD2" with _ ->  vINT_OF_REAL_THM vREAL_LT_ADD2;;
let vINT_LT_ADDL = try Cache.lookup_thm "INT_LT_ADDL" with _ ->  vINT_OF_REAL_THM vREAL_LT_ADDL;;
let vINT_LT_ADDNEG = try Cache.lookup_thm "INT_LT_ADDNEG" with _ ->  vINT_OF_REAL_THM vREAL_LT_ADDNEG;;
let vINT_LT_ADDNEG2 = try Cache.lookup_thm "INT_LT_ADDNEG2" with _ ->  vINT_OF_REAL_THM vREAL_LT_ADDNEG2;;
let vINT_LT_ADDR = try Cache.lookup_thm "INT_LT_ADDR" with _ ->  vINT_OF_REAL_THM vREAL_LT_ADDR;;
let vINT_LT_ADD_SUB = try Cache.lookup_thm "INT_LT_ADD_SUB" with _ ->  vINT_OF_REAL_THM vREAL_LT_ADD_SUB;;
let vINT_LT_ANTISYM = try Cache.lookup_thm "INT_LT_ANTISYM" with _ ->  vINT_OF_REAL_THM vREAL_LT_ANTISYM;;
let vINT_LT_GT = try Cache.lookup_thm "INT_LT_GT" with _ ->  vINT_OF_REAL_THM vREAL_LT_GT;;
let vINT_LT_IMP_LE = try Cache.lookup_thm "INT_LT_IMP_LE" with _ ->  vINT_OF_REAL_THM vREAL_LT_IMP_LE;;
let vINT_LT_IMP_NE = try Cache.lookup_thm "INT_LT_IMP_NE" with _ ->  vINT_OF_REAL_THM vREAL_LT_IMP_NE;;
let vINT_LT_LADD = try Cache.lookup_thm "INT_LT_LADD" with _ ->  vINT_OF_REAL_THM vREAL_LT_LADD;;
let vINT_LT_LE = try Cache.lookup_thm "INT_LT_LE" with _ ->  vINT_OF_REAL_THM vREAL_LT_LE;;
let vINT_LT_LMUL_EQ = try Cache.lookup_thm "INT_LT_LMUL_EQ" with _ ->  vINT_OF_REAL_THM vREAL_LT_LMUL_EQ;;
let vINT_LT_MAX = try Cache.lookup_thm "INT_LT_MAX" with _ ->  vINT_OF_REAL_THM vREAL_LT_MAX;;
let vINT_LT_MIN = try Cache.lookup_thm "INT_LT_MIN" with _ ->  vINT_OF_REAL_THM vREAL_LT_MIN;;
let vINT_LT_MUL = try Cache.lookup_thm "INT_LT_MUL" with _ ->  vINT_OF_REAL_THM vREAL_LT_MUL;;
let vINT_LT_MUL_EQ = try Cache.lookup_thm "INT_LT_MUL_EQ" with _ ->  vINT_OF_REAL_THM vREAL_LT_MUL_EQ;;
let vINT_LT_MUL2 = try Cache.lookup_thm "INT_LT_MUL2" with _ ->  vINT_OF_REAL_THM vREAL_LT_MUL2;;
let vINT_LT_NEG2 = try Cache.lookup_thm "INT_LT_NEG2" with _ ->  vINT_OF_REAL_THM vREAL_LT_NEG2;;
let vINT_LT_NEGTOTAL = try Cache.lookup_thm "INT_LT_NEGTOTAL" with _ ->  vINT_OF_REAL_THM vREAL_LT_NEGTOTAL;;
let vINT_LT_POW2 = try Cache.lookup_thm "INT_LT_POW2" with _ ->  vINT_OF_REAL_THM vREAL_LT_POW2;;
let vINT_LT_RADD = try Cache.lookup_thm "INT_LT_RADD" with _ ->  vINT_OF_REAL_THM vREAL_LT_RADD;;
let vINT_LT_REFL = try Cache.lookup_thm "INT_LT_REFL" with _ ->  vINT_OF_REAL_THM vREAL_LT_REFL;;
let vINT_LT_RMUL_EQ = try Cache.lookup_thm "INT_LT_RMUL_EQ" with _ ->  vINT_OF_REAL_THM vREAL_LT_RMUL_EQ;;
let vINT_LT_SQUARE_ABS = try Cache.lookup_thm "INT_LT_SQUARE_ABS" with _ ->  vINT_OF_REAL_THM vREAL_LT_SQUARE_ABS;;
let vINT_LT_SUB_LADD = try Cache.lookup_thm "INT_LT_SUB_LADD" with _ ->  vINT_OF_REAL_THM vREAL_LT_SUB_LADD;;
let vINT_LT_SUB_RADD = try Cache.lookup_thm "INT_LT_SUB_RADD" with _ ->  vINT_OF_REAL_THM vREAL_LT_SUB_RADD;;
let vINT_LT_TOTAL = try Cache.lookup_thm "INT_LT_TOTAL" with _ ->  vINT_OF_REAL_THM vREAL_LT_TOTAL;;
let vINT_LT_TRANS = try Cache.lookup_thm "INT_LT_TRANS" with _ ->  vINT_OF_REAL_THM vREAL_LT_TRANS;;
let vINT_MAX_ACI = try Cache.lookup_thm "INT_MAX_ACI" with _ ->  vINT_OF_REAL_THM vREAL_MAX_ACI;;
let vINT_MAX_ASSOC = try Cache.lookup_thm "INT_MAX_ASSOC" with _ ->  vINT_OF_REAL_THM vREAL_MAX_ASSOC;;
let vINT_MAX_LE = try Cache.lookup_thm "INT_MAX_LE" with _ ->  vINT_OF_REAL_THM vREAL_MAX_LE;;
let vINT_MAX_LT = try Cache.lookup_thm "INT_MAX_LT" with _ ->  vINT_OF_REAL_THM vREAL_MAX_LT;;
let vINT_MAX_MAX = try Cache.lookup_thm "INT_MAX_MAX" with _ ->  vINT_OF_REAL_THM vREAL_MAX_MAX;;
let vINT_MAX_MIN = try Cache.lookup_thm "INT_MAX_MIN" with _ ->  vINT_OF_REAL_THM vREAL_MAX_MIN;;
let vINT_MAX_SYM = try Cache.lookup_thm "INT_MAX_SYM" with _ ->  vINT_OF_REAL_THM vREAL_MAX_SYM;;
let vINT_MIN_ACI = try Cache.lookup_thm "INT_MIN_ACI" with _ ->  vINT_OF_REAL_THM vREAL_MIN_ACI;;
let vINT_MIN_ASSOC = try Cache.lookup_thm "INT_MIN_ASSOC" with _ ->  vINT_OF_REAL_THM vREAL_MIN_ASSOC;;
let vINT_MIN_LE = try Cache.lookup_thm "INT_MIN_LE" with _ ->  vINT_OF_REAL_THM vREAL_MIN_LE;;
let vINT_MIN_LT = try Cache.lookup_thm "INT_MIN_LT" with _ ->  vINT_OF_REAL_THM vREAL_MIN_LT;;
let vINT_MIN_MAX = try Cache.lookup_thm "INT_MIN_MAX" with _ ->  vINT_OF_REAL_THM vREAL_MIN_MAX;;
let vINT_MIN_MIN = try Cache.lookup_thm "INT_MIN_MIN" with _ ->  vINT_OF_REAL_THM vREAL_MIN_MIN;;
let vINT_MIN_SYM = try Cache.lookup_thm "INT_MIN_SYM" with _ ->  vINT_OF_REAL_THM vREAL_MIN_SYM;;
let vINT_MUL_2 = try Cache.lookup_thm "INT_MUL_2" with _ ->  vINT_OF_REAL_THM vREAL_MUL_2;;
let vINT_MUL_AC = try Cache.lookup_thm "INT_MUL_AC" with _ ->  vINT_OF_REAL_THM vREAL_MUL_AC;;
let vINT_MUL_ASSOC = try Cache.lookup_thm "INT_MUL_ASSOC" with _ ->  vINT_OF_REAL_THM vREAL_MUL_ASSOC;;
let vINT_MUL_LID = try Cache.lookup_thm "INT_MUL_LID" with _ ->  vINT_OF_REAL_THM vREAL_MUL_LID;;
let vINT_MUL_LNEG = try Cache.lookup_thm "INT_MUL_LNEG" with _ ->  vINT_OF_REAL_THM vREAL_MUL_LNEG;;
let vINT_MUL_LZERO = try Cache.lookup_thm "INT_MUL_LZERO" with _ ->  vINT_OF_REAL_THM vREAL_MUL_LZERO;;
let vINT_MUL_POS_LE = try Cache.lookup_thm "INT_MUL_POS_LE" with _ ->  vINT_OF_REAL_THM vREAL_MUL_POS_LE;;
let vINT_MUL_POS_LT = try Cache.lookup_thm "INT_MUL_POS_LT" with _ ->  vINT_OF_REAL_THM vREAL_MUL_POS_LT;;
let vINT_MUL_RID = try Cache.lookup_thm "INT_MUL_RID" with _ ->  vINT_OF_REAL_THM vREAL_MUL_RID;;
let vINT_MUL_RNEG = try Cache.lookup_thm "INT_MUL_RNEG" with _ ->  vINT_OF_REAL_THM vREAL_MUL_RNEG;;
let vINT_MUL_RZERO = try Cache.lookup_thm "INT_MUL_RZERO" with _ ->  vINT_OF_REAL_THM vREAL_MUL_RZERO;;
let vINT_MUL_SYM = try Cache.lookup_thm "INT_MUL_SYM" with _ ->  vINT_OF_REAL_THM vREAL_MUL_SYM;;
let vINT_NEG_0 = try Cache.lookup_thm "INT_NEG_0" with _ ->  vINT_OF_REAL_THM vREAL_NEG_0;;
let vINT_NEG_ADD = try Cache.lookup_thm "INT_NEG_ADD" with _ ->  vINT_OF_REAL_THM vREAL_NEG_ADD;;
let vINT_NEG_EQ = try Cache.lookup_thm "INT_NEG_EQ" with _ ->  vINT_OF_REAL_THM vREAL_NEG_EQ;;
let vINT_NEG_EQ_0 = try Cache.lookup_thm "INT_NEG_EQ_0" with _ ->  vINT_OF_REAL_THM vREAL_NEG_EQ_0;;
let vINT_NEG_GE0 = try Cache.lookup_thm "INT_NEG_GE0" with _ ->  vINT_OF_REAL_THM vREAL_NEG_GE0;;
let vINT_NEG_GT0 = try Cache.lookup_thm "INT_NEG_GT0" with _ ->  vINT_OF_REAL_THM vREAL_NEG_GT0;;
let vINT_NEG_LE0 = try Cache.lookup_thm "INT_NEG_LE0" with _ ->  vINT_OF_REAL_THM vREAL_NEG_LE0;;
let vINT_NEG_LMUL = try Cache.lookup_thm "INT_NEG_LMUL" with _ ->  vINT_OF_REAL_THM vREAL_NEG_LMUL;;
let vINT_NEG_LT0 = try Cache.lookup_thm "INT_NEG_LT0" with _ ->  vINT_OF_REAL_THM vREAL_NEG_LT0;;
let vINT_NEG_MINUS1 = try Cache.lookup_thm "INT_NEG_MINUS1" with _ ->  vINT_OF_REAL_THM vREAL_NEG_MINUS1;;
let vINT_NEG_MUL2 = try Cache.lookup_thm "INT_NEG_MUL2" with _ ->  vINT_OF_REAL_THM vREAL_NEG_MUL2;;
let vINT_NEG_NEG = try Cache.lookup_thm "INT_NEG_NEG" with _ ->  vINT_OF_REAL_THM vREAL_NEG_NEG;;
let vINT_NEG_RMUL = try Cache.lookup_thm "INT_NEG_RMUL" with _ ->  vINT_OF_REAL_THM vREAL_NEG_RMUL;;
let vINT_NEG_SUB = try Cache.lookup_thm "INT_NEG_SUB" with _ ->  vINT_OF_REAL_THM vREAL_NEG_SUB;;
let vINT_NOT_EQ = try Cache.lookup_thm "INT_NOT_EQ" with _ ->  vINT_OF_REAL_THM vREAL_NOT_EQ;;
let vINT_NOT_LE = try Cache.lookup_thm "INT_NOT_LE" with _ ->  vINT_OF_REAL_THM vREAL_NOT_LE;;
let vINT_NOT_LT = try Cache.lookup_thm "INT_NOT_LT" with _ ->  vINT_OF_REAL_THM vREAL_NOT_LT;;
let vINT_OF_NUM_ADD = try Cache.lookup_thm "INT_OF_NUM_ADD" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_ADD;;
let vINT_OF_NUM_CLAUSES = try Cache.lookup_thm "INT_OF_NUM_CLAUSES" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_CLAUSES;;
let vINT_OF_NUM_EQ = try Cache.lookup_thm "INT_OF_NUM_EQ" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_EQ;;
let vINT_OF_NUM_GE = try Cache.lookup_thm "INT_OF_NUM_GE" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_GE;;
let vINT_OF_NUM_GT = try Cache.lookup_thm "INT_OF_NUM_GT" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_GT;;
let vINT_OF_NUM_LE = try Cache.lookup_thm "INT_OF_NUM_LE" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_LE;;
let vINT_OF_NUM_LT = try Cache.lookup_thm "INT_OF_NUM_LT" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_LT;;
let vINT_OF_NUM_MAX = try Cache.lookup_thm "INT_OF_NUM_MAX" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_MAX;;
let vINT_OF_NUM_MIN = try Cache.lookup_thm "INT_OF_NUM_MIN" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_MIN;;
let vINT_OF_NUM_MOD = try Cache.lookup_thm "INT_OF_NUM_MOD" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_MOD;;
let vINT_OF_NUM_MUL = try Cache.lookup_thm "INT_OF_NUM_MUL" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_MUL;;
let vINT_OF_NUM_POW = try Cache.lookup_thm "INT_OF_NUM_POW" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_POW;;
let vINT_OF_NUM_SUB = try Cache.lookup_thm "INT_OF_NUM_SUB" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_SUB;;
let vINT_OF_NUM_SUC = try Cache.lookup_thm "INT_OF_NUM_SUC" with _ ->  vINT_OF_REAL_THM vREAL_OF_NUM_SUC;;
let vINT_POS = try Cache.lookup_thm "INT_POS" with _ ->  vINT_OF_REAL_THM vREAL_POS;;
let vINT_POS_NZ = try Cache.lookup_thm "INT_POS_NZ" with _ ->  vINT_OF_REAL_THM vREAL_LT_IMP_NZ;;
let vINT_POW2_ABS = try Cache.lookup_thm "INT_POW2_ABS" with _ ->  vINT_OF_REAL_THM vREAL_POW2_ABS;;
let vINT_POW_1 = try Cache.lookup_thm "INT_POW_1" with _ ->  vINT_OF_REAL_THM vREAL_POW_1;;
let vINT_POW_1_LE = try Cache.lookup_thm "INT_POW_1_LE" with _ ->  vINT_OF_REAL_THM vREAL_POW_1_LE;;
let vINT_POW_1_LT = try Cache.lookup_thm "INT_POW_1_LT" with _ ->  vINT_OF_REAL_THM vREAL_POW_1_LT;;
let vINT_POW_2 = try Cache.lookup_thm "INT_POW_2" with _ ->  vINT_OF_REAL_THM vREAL_POW_2;;
let vINT_POW_ADD = try Cache.lookup_thm "INT_POW_ADD" with _ ->  vINT_OF_REAL_THM vREAL_POW_ADD;;
let vINT_POW_EQ = try Cache.lookup_thm "INT_POW_EQ" with _ ->  vINT_OF_REAL_THM vREAL_POW_EQ;;
let vINT_POW_EQ_0 = try Cache.lookup_thm "INT_POW_EQ_0" with _ ->  vINT_OF_REAL_THM vREAL_POW_EQ_0;;
let vINT_POW_EQ_ABS = try Cache.lookup_thm "INT_POW_EQ_ABS" with _ ->  vINT_OF_REAL_THM vREAL_POW_EQ_ABS;;
let vINT_POW_LE = try Cache.lookup_thm "INT_POW_LE" with _ ->  vINT_OF_REAL_THM vREAL_POW_LE;;
let vINT_POW_LE2 = try Cache.lookup_thm "INT_POW_LE2" with _ ->  vINT_OF_REAL_THM vREAL_POW_LE2;;
let vINT_POW_LE2_ODD = try Cache.lookup_thm "INT_POW_LE2_ODD" with _ ->  vINT_OF_REAL_THM vREAL_POW_LE2_ODD;;
let vINT_POW_LE2_REV = try Cache.lookup_thm "INT_POW_LE2_REV" with _ ->  vINT_OF_REAL_THM vREAL_POW_LE2_REV;;
let vINT_POW_LE_1 = try Cache.lookup_thm "INT_POW_LE_1" with _ ->  vINT_OF_REAL_THM vREAL_POW_LE_1;;
let vINT_POW_LT = try Cache.lookup_thm "INT_POW_LT" with _ ->  vINT_OF_REAL_THM vREAL_POW_LT;;
let vINT_POW_LT2 = try Cache.lookup_thm "INT_POW_LT2" with _ ->  vINT_OF_REAL_THM vREAL_POW_LT2;;
let vINT_POW_LT2_REV = try Cache.lookup_thm "INT_POW_LT2_REV" with _ ->  vINT_OF_REAL_THM vREAL_POW_LT2_REV;;
let vINT_POW_LT_1 = try Cache.lookup_thm "INT_POW_LT_1" with _ ->  vINT_OF_REAL_THM vREAL_POW_LT_1;;
let vINT_POW_MONO = try Cache.lookup_thm "INT_POW_MONO" with _ ->  vINT_OF_REAL_THM vREAL_POW_MONO;;
let vINT_POW_MONO_LT = try Cache.lookup_thm "INT_POW_MONO_LT" with _ ->  vINT_OF_REAL_THM vREAL_POW_MONO_LT;;
let vINT_POW_MUL = try Cache.lookup_thm "INT_POW_MUL" with _ ->  vINT_OF_REAL_THM vREAL_POW_MUL;;
let vINT_POW_NEG = try Cache.lookup_thm "INT_POW_NEG" with _ ->  vINT_OF_REAL_THM vREAL_POW_NEG;;
let vINT_POW_NZ = try Cache.lookup_thm "INT_POW_NZ" with _ ->  vINT_OF_REAL_THM vREAL_POW_NZ;;
let vINT_POW_ONE = try Cache.lookup_thm "INT_POW_ONE" with _ ->  vINT_OF_REAL_THM vREAL_POW_ONE;;
let vINT_POW_POW = try Cache.lookup_thm "INT_POW_POW" with _ ->  vINT_OF_REAL_THM vREAL_POW_POW;;
let vINT_POW_ZERO = try Cache.lookup_thm "INT_POW_ZERO" with _ ->  vINT_OF_REAL_THM vREAL_POW_ZERO;;
let vINT_RNEG_UNIQ = try Cache.lookup_thm "INT_RNEG_UNIQ" with _ ->  vINT_OF_REAL_THM vREAL_RNEG_UNIQ;;
let vINT_SGN = try Cache.lookup_thm "INT_SGN" with _ ->  vINT_OF_REAL_THM real_sgn;;
let vINT_SGN_0 = try Cache.lookup_thm "INT_SGN_0" with _ ->  vINT_OF_REAL_THM vREAL_SGN_0;;
let vINT_SGN_ABS = try Cache.lookup_thm "INT_SGN_ABS" with _ ->  vINT_OF_REAL_THM vREAL_SGN_ABS;;
let vINT_SGN_ABS_ALT = try Cache.lookup_thm "INT_SGN_ABS_ALT" with _ ->  vINT_OF_REAL_THM vREAL_SGN_ABS_ALT;;
let vINT_SGN_CASES = try Cache.lookup_thm "INT_SGN_CASES" with _ ->  vINT_OF_REAL_THM vREAL_SGN_CASES;;
let vINT_SGN_EQ = try Cache.lookup_thm "INT_SGN_EQ" with _ ->  vINT_OF_REAL_THM vREAL_SGN_EQ;;
let vINT_SGN_EQ_INEQ = try Cache.lookup_thm "INT_SGN_EQ_INEQ" with _ ->  vINT_OF_REAL_THM vREAL_SGN_EQ_INEQ;;
let vINT_SGN_INEQS = try Cache.lookup_thm "INT_SGN_INEQS" with _ ->  vINT_OF_REAL_THM vREAL_SGN_INEQS;;
let vINT_SGN_MUL = try Cache.lookup_thm "INT_SGN_MUL" with _ ->  vINT_OF_REAL_THM vREAL_SGN_MUL;;
let vINT_SGN_NEG = try Cache.lookup_thm "INT_SGN_NEG" with _ ->  vINT_OF_REAL_THM vREAL_SGN_NEG;;
let vINT_SGN_POW = try Cache.lookup_thm "INT_SGN_POW" with _ ->  vINT_OF_REAL_THM vREAL_SGN_POW;;
let vINT_SGN_POW_2 = try Cache.lookup_thm "INT_SGN_POW_2" with _ ->  vINT_OF_REAL_THM vREAL_SGN_POW_2;;
let vINT_SGN_INT_SGN = try Cache.lookup_thm "INT_SGN_INT_SGN" with _ ->  vINT_OF_REAL_THM vREAL_SGN_REAL_SGN;;
let vINT_SGNS_EQ = try Cache.lookup_thm "INT_SGNS_EQ" with _ ->  vINT_OF_REAL_THM vREAL_SGNS_EQ;;
let vINT_SGNS_EQ_ALT = try Cache.lookup_thm "INT_SGNS_EQ_ALT" with _ ->  vINT_OF_REAL_THM vREAL_SGNS_EQ_ALT;;
let vINT_SOS_EQ_0 = try Cache.lookup_thm "INT_SOS_EQ_0" with _ ->  vINT_OF_REAL_THM vREAL_SOS_EQ_0;;
let vINT_SUB_0 = try Cache.lookup_thm "INT_SUB_0" with _ ->  vINT_OF_REAL_THM vREAL_SUB_0;;
let vINT_SUB_ABS = try Cache.lookup_thm "INT_SUB_ABS" with _ ->  vINT_OF_REAL_THM vREAL_SUB_ABS;;
let vINT_SUB_ADD = try Cache.lookup_thm "INT_SUB_ADD" with _ ->  vINT_OF_REAL_THM vREAL_SUB_ADD;;
let vINT_SUB_ADD2 = try Cache.lookup_thm "INT_SUB_ADD2" with _ ->  vINT_OF_REAL_THM vREAL_SUB_ADD2;;
let vINT_SUB_LDISTRIB = try Cache.lookup_thm "INT_SUB_LDISTRIB" with _ ->  vINT_OF_REAL_THM vREAL_SUB_LDISTRIB;;
let vINT_SUB_LE = try Cache.lookup_thm "INT_SUB_LE" with _ ->  vINT_OF_REAL_THM vREAL_SUB_LE;;
let vINT_SUB_LNEG = try Cache.lookup_thm "INT_SUB_LNEG" with _ ->  vINT_OF_REAL_THM vREAL_SUB_LNEG;;
let vINT_SUB_LT = try Cache.lookup_thm "INT_SUB_LT" with _ ->  vINT_OF_REAL_THM vREAL_SUB_LT;;
let vINT_SUB_LZERO = try Cache.lookup_thm "INT_SUB_LZERO" with _ ->  vINT_OF_REAL_THM vREAL_SUB_LZERO;;
let vINT_SUB_NEG2 = try Cache.lookup_thm "INT_SUB_NEG2" with _ ->  vINT_OF_REAL_THM vREAL_SUB_NEG2;;
let vINT_SUB_RDISTRIB = try Cache.lookup_thm "INT_SUB_RDISTRIB" with _ ->  vINT_OF_REAL_THM vREAL_SUB_RDISTRIB;;
let vINT_SUB_REFL = try Cache.lookup_thm "INT_SUB_REFL" with _ ->  vINT_OF_REAL_THM vREAL_SUB_REFL;;
let vINT_SUB_RNEG = try Cache.lookup_thm "INT_SUB_RNEG" with _ ->  vINT_OF_REAL_THM vREAL_SUB_RNEG;;
let vINT_SUB_RZERO = try Cache.lookup_thm "INT_SUB_RZERO" with _ ->  vINT_OF_REAL_THM vREAL_SUB_RZERO;;
let vINT_SUB_SUB = try Cache.lookup_thm "INT_SUB_SUB" with _ ->  vINT_OF_REAL_THM vREAL_SUB_SUB;;
let vINT_SUB_SUB2 = try Cache.lookup_thm "INT_SUB_SUB2" with _ ->  vINT_OF_REAL_THM vREAL_SUB_SUB2;;
let vINT_SUB_TRIANGLE = try Cache.lookup_thm "INT_SUB_TRIANGLE" with _ ->  vINT_OF_REAL_THM vREAL_SUB_TRIANGLE;;

let vINT_WLOG_LE = try Cache.lookup_thm "INT_WLOG_LE" with _ ->  prove
 ((parse_term "(!x y:int. P x y <=> P y x) /\\ (!x y. x <= y ==> P x y) ==> !x y. P x y"),
  vMESON_TAC[vINT_LE_TOTAL]);;

let vINT_WLOG_LT = try Cache.lookup_thm "INT_WLOG_LT" with _ ->  prove
 ((parse_term "(!x:int. P x x) /\\ (!x y. P x y <=> P y x) /\\ (!x y. x < y ==> P x y)\n   ==> !x y. P x y"),
  vMESON_TAC[vINT_LT_TOTAL]);;

let vINT_WLOG_LE_3 = try Cache.lookup_thm "INT_WLOG_LE_3" with _ ->  prove
 ((parse_term "!P. (!x y z. P x y z ==> P y x z /\\ P x z y) /\\\n       (!x y z:int. x <= y /\\ y <= z ==> P x y z)\n       ==> !x y z. P x y z"),
  vMESON_TAC[vINT_LE_TOTAL]);;

(* ------------------------------------------------------------------------- *)
(* More useful "image" theorems.                                             *)
(* ------------------------------------------------------------------------- *)

let vINT_FORALL_POS = try Cache.lookup_thm "INT_FORALL_POS" with _ ->  prove
 ((parse_term "!P. (!n. P(&n)) <=> (!i:int. &0 <= i ==> P(i))"),
  vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vGEN_TAC ++-->
   [vDISJ_CASES_THEN (vCHOOSE_THEN vSUBST1_TAC) (vSPEC (parse_term "i:int") vINT_IMAGE) ---->
    vASM_REWRITE_TAC[vINT_LE_RNEG; vINT_ADD_LID; vINT_OF_NUM_LE; vLE] ---->
    vDISCH_THEN vSUBST1_TAC ----> vASM_REWRITE_TAC[vINT_NEG_0];
    vFIRST_ASSUM vMATCH_MP_TAC ----> vREWRITE_TAC[vINT_OF_NUM_LE; vLE_0]]);;

let vINT_EXISTS_POS = try Cache.lookup_thm "INT_EXISTS_POS" with _ ->  prove
 ((parse_term "!P. (?n. P(&n)) <=> (?i:int. &0 <= i /\\ P(i))"),
  vGEN_TAC ----> vGEN_REWRITE_TAC vI [vTAUT (parse_term "(p <=> q) <=> (~p <=> ~q)")] ---->
  vREWRITE_TAC[vNOT_EXISTS_THM; vINT_FORALL_POS] ----> vMESON_TAC[]);;

let vINT_FORALL_ABS = try Cache.lookup_thm "INT_FORALL_ABS" with _ ->  prove
 ((parse_term "!P. (!n. P(&n)) <=> (!x:int. P(abs x))"),
  vREWRITE_TAC[vINT_FORALL_POS] ----> vMESON_TAC[vINT_ABS_POS; vINT_ABS_REFL]);;

let vINT_EXISTS_ABS = try Cache.lookup_thm "INT_EXISTS_ABS" with _ ->  prove
 ((parse_term "!P. (?n. P(&n)) <=> (?x:int. P(abs x))"),
  vGEN_TAC ----> vGEN_REWRITE_TAC vI [vTAUT (parse_term "(p <=> q) <=> (~p <=> ~q)")] ---->
  vREWRITE_TAC[vNOT_EXISTS_THM; vINT_FORALL_ABS] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A few "pseudo definitions".                                               *)
(* ------------------------------------------------------------------------- *)

let vINT_POW = try Cache.lookup_thm "INT_POW" with _ ->  prove
 ((parse_term "(x pow 0 = &1) /\\\n   (!n. x pow (SUC n) = x * x pow n)"),
  vREWRITE_TAC(map vINT_OF_REAL_THM (vCONJUNCTS real_pow)));;

let vINT_ABS = try Cache.lookup_thm "INT_ABS" with _ ->  prove
 ((parse_term "!x. abs(x) = if &0 <= x then x else --x"),
  vGEN_TAC ----> vMP_TAC(vINT_OF_REAL_THM(vSPEC (parse_term "x:real") real_abs)) ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[int_eq]);;

let vINT_GE = try Cache.lookup_thm "INT_GE" with _ ->  prove
 ((parse_term "!x y. x >= y <=> y <= x"),
  vREWRITE_TAC[int_ge; int_le; real_ge]);;

let vINT_GT = try Cache.lookup_thm "INT_GT" with _ ->  prove
 ((parse_term "!x y. x > y <=> y < x"),
  vREWRITE_TAC[int_gt; int_lt; real_gt]);;

let vINT_LT = try Cache.lookup_thm "INT_LT" with _ ->  prove
 ((parse_term "!x y. x < y <=> ~(y <= x)"),
  vREWRITE_TAC[int_lt; int_le; real_lt]);;

(* ------------------------------------------------------------------------- *)
(* Now a decision procedure for the integers.                                *)
(* ------------------------------------------------------------------------- *)

let vINT_ARITH =
  let atom_CONV =
    let pth = prove
      ((parse_term "(~(x <= y) <=> y + &1 <= x) /\\\n        (~(x < y) <=> y <= x) /\\\n        (~(x = y) <=> x + &1 <= y \\/ y + &1 <= x) /\\\n        (x < y <=> x + &1 <= y)"),
       vREWRITE_TAC[vINT_NOT_LE; vINT_NOT_LT; vINT_NOT_EQ; vINT_LT_DISCRETE]) in
    vGEN_REWRITE_CONV vI [pth]
  and bub_CONV = vGEN_REWRITE_CONV vTOP_SWEEP_CONV
   [int_eq; int_le; int_lt; int_ge; int_gt;
    int_of_num_th; int_neg_th; int_add_th; int_mul_th;
    int_sub_th; int_pow_th; int_abs_th; int_max_th; int_min_th] in
  let base_CONV = vTRY_CONV atom_CONV +---> bub_CONV in
  let vNNF_NORM_CONV = vGEN_NNF_CONV false
   (base_CONV,fun t -> base_CONV t,base_CONV(mk_neg t)) in
  let init_CONV =
    vTOP_DEPTH_CONV vBETA_CONV +--->
    vPRESIMP_CONV +--->
    vGEN_REWRITE_CONV vDEPTH_CONV [vINT_GT; vINT_GE] +--->
    vNNF_CONV +---> vDEPTH_BINOP_CONV (parse_term "(\\/)") vCONDS_ELIM_CONV +--->
    vNNF_NORM_CONV in
  let p_tm = (parse_term "p:bool")
  and not_tm = (parse_term "(~)") in
  let pth = vTAUT(mk_eq(mk_neg(mk_neg p_tm),p_tm)) in
  fun tm ->
    let th0 = vINST [tm,p_tm] pth
    and th1 = init_CONV (mk_neg tm) in
    let th2 = vREAL_ARITH(mk_neg(rand(concl th1))) in
    vEQ_MP th0 (vEQ_MP (vAP_TERM not_tm (vSYM th1)) th2);;

let vINT_ARITH_TAC = vCONV_TAC(vEQT_INTRO -| vINT_ARITH);;

let vASM_INT_ARITH_TAC =
  vREPEAT(vFIRST_X_ASSUM(vMP_TAC -| check (not -| is_forall -| concl))) ---->
  vINT_ARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* Some pseudo-definitions.                                                  *)
(* ------------------------------------------------------------------------- *)

let vINT_SUB = try Cache.lookup_thm "INT_SUB" with _ ->  vINT_ARITH (parse_term "!x y. x - y = x + --y");;

let vINT_MAX = try Cache.lookup_thm "INT_MAX" with _ ->  vINT_ARITH (parse_term "!x y. max x y = if x <= y then y else x");;

let vINT_MIN = try Cache.lookup_thm "INT_MIN" with _ ->  vINT_ARITH (parse_term "!x y. min x y = if x <= y then x else y");;

(* ------------------------------------------------------------------------- *)
(* Additional useful lemmas.                                                 *)
(* ------------------------------------------------------------------------- *)

let vINT_OF_NUM_EXISTS = try Cache.lookup_thm "INT_OF_NUM_EXISTS" with _ ->  prove
 ((parse_term "!x:int. (?n. x = &n) <=> &0 <= x"),
  vGEN_TAC ----> vEQ_TAC ----> vSTRIP_TAC ----> vASM_SIMP_TAC[vINT_POS] ---->
  vMP_TAC(vISPEC (parse_term "x:int") vINT_IMAGE) ---->
  vREWRITE_TAC[vOR_EXISTS_THM] ----> vMATCH_MP_TAC vMONO_EXISTS ---->
  vASM_INT_ARITH_TAC);;

let vINT_LE_DISCRETE = try Cache.lookup_thm "INT_LE_DISCRETE" with _ ->  vINT_ARITH (parse_term "!x y:int. x <= y <=> x < y + &1");;

let vINT_LE_TRANS_LE = try Cache.lookup_thm "INT_LE_TRANS_LE" with _ ->  prove
 ((parse_term "!x y:int. x <= y <=> (!z. y <= z ==> x <= z)"),
  vMESON_TAC[vINT_LE_TRANS; vINT_LE_REFL]);;

let vINT_LE_TRANS_LT = try Cache.lookup_thm "INT_LE_TRANS_LT" with _ ->  prove
 ((parse_term "!x y:int. x <= y <=> (!z. y < z ==> x < z)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++--> [vINT_ARITH_TAC; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "y + &1:int")) ----> vINT_ARITH_TAC);;

let vINT_MUL_EQ_1 = try Cache.lookup_thm "INT_MUL_EQ_1" with _ ->  prove
 ((parse_term "!x y:int. x * y = &1 <=> x = &1 /\\ y = &1 \\/ x = --(&1) /\\ y = --(&1)"),
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vISPEC (parse_term "x:int") vINT_IMAGE) ---->
  vMP_TAC(vISPEC (parse_term "y:int") vINT_IMAGE) ---->
  vREPEAT vSTRIP_TAC ---->
  vASM_REWRITE_TAC[vINT_MUL_LNEG; vINT_MUL_RNEG; vINT_NEG_NEG;
     vINT_ARITH (parse_term "~(--(&n:int) = &1)"); vINT_OF_NUM_MUL;
     vINT_ARITH (parse_term "~(&n:int = -- &1)"); vINT_OF_NUM_EQ; vINT_NEG_EQ] ---->
  vREWRITE_TAC[vMULT_EQ_1]);;

let vINT_ABS_MUL_1 = try Cache.lookup_thm "INT_ABS_MUL_1" with _ ->  prove
 ((parse_term "!x y. abs(x * y) = &1 <=> abs(x) = &1 /\\ abs(y) = &1"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vINT_ABS_MUL] ---->
  vMP_TAC(vSPEC (parse_term "y:int") vINT_ABS_POS) ----> vSPEC_TAC((parse_term "abs(y)"),(parse_term "b:int")) ---->
  vMP_TAC(vSPEC (parse_term "x:int") vINT_ABS_POS) ----> vSPEC_TAC((parse_term "abs(x)"),(parse_term "a:int")) ---->
  vREWRITE_TAC[vGSYM vINT_FORALL_POS; vINT_OF_NUM_MUL; vINT_OF_NUM_EQ; vMULT_EQ_1]);;

let vINT_WOP = try Cache.lookup_thm "INT_WOP" with _ ->  prove
 ((parse_term "(?x. &0 <= x /\\ P x) <=>\n   (?x. &0 <= x /\\ P x /\\ !y. &0 <= y /\\ P y ==> x <= y)"),
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(?x. P x /\\ Q x) <=> ~(!x. P x ==> ~Q x)")] ---->
  vREWRITE_TAC[vIMP_CONJ; vGSYM vINT_FORALL_POS; vINT_OF_NUM_LE] ---->
  vREWRITE_TAC[vNOT_FORALL_THM] ----> vGEN_REWRITE_TAC vLAND_CONV [num_WOP] ---->
  vREWRITE_TAC[vGSYM vNOT_LE; vCONTRAPOS_THM]);;

(* ------------------------------------------------------------------------- *)
(* Archimedian property for the integers.                                    *)
(* ------------------------------------------------------------------------- *)

let vINT_ARCH = try Cache.lookup_thm "INT_ARCH" with _ ->  prove
 ((parse_term "!x d. ~(d = &0) ==> ?c. x < c * d"),
  vSUBGOAL_THEN (parse_term "!x. &0 <= x ==> ?n. x <= &n") vASSUME_TAC ++-->
   [vREWRITE_TAC[vGSYM vINT_FORALL_POS; vINT_OF_NUM_LE] ----> vMESON_TAC[vLE_REFL];
    vALL_TAC] ---->
  vSUBGOAL_THEN (parse_term "!x. ?n. x <= &n") vASSUME_TAC ++-->
   [vASM_MESON_TAC[vINT_LE_TOTAL]; vALL_TAC] ---->
  vSUBGOAL_THEN (parse_term "!x d. &0 < d ==> ?c. x < c * d") vASSUME_TAC ++-->
   [vREPEAT vGEN_TAC ----> vREWRITE_TAC[vINT_LT_DISCRETE; vINT_ADD_LID] ---->
    vASM_MESON_TAC[vINT_POS; vINT_LE_LMUL; vINT_ARITH
        (parse_term "x + &1 <= &n /\\ &n * &1 <= &n * d ==> x + &1 <= &n * d")];
    vALL_TAC] ---->
  vSUBGOAL_THEN (parse_term "!x d. ~(d = &0) ==> ?c. x < c * d") vASSUME_TAC ++-->
   [vASM_MESON_TAC[vINT_ARITH (parse_term "--x * y = x * --y");
                  vINT_ARITH (parse_term "~(d = &0) ==> &0 < d \\/ &0 < --d")];
    vALL_TAC] ---->
  vASM_MESON_TAC[vINT_ARITH (parse_term "--x * y = x * --y");
                vINT_ARITH (parse_term "~(d = &0) ==> &0 < d \\/ &0 < --d")]);;

(* ------------------------------------------------------------------------- *)
(* Definitions of ("Euclidean") integer division and remainder.              *)
(* ------------------------------------------------------------------------- *)

let vINT_DIVMOD_EXIST_0 = try Cache.lookup_thm "INT_DIVMOD_EXIST_0" with _ ->  prove
 ((parse_term "!m n:int. ?q r. if n = &0 then q = &0 /\\ r = m\n                   else &0 <= r /\\ r < abs(n) /\\ m = q * n + r"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = &0") ---->
  vASM_REWRITE_TAC[vRIGHT_EXISTS_AND_THM; vEXISTS_REFL] ---->
  vGEN_REWRITE_TAC vI [vSWAP_EXISTS_THM] ---->
  vSUBGOAL_THEN (parse_term "?r. &0 <= r /\\ ?q:int. m = n * q + r") vMP_TAC ++-->
   [vFIRST_ASSUM(vMP_TAC -| vSPEC (parse_term "--m:int") -| vMATCH_MP vINT_ARCH) ---->
    vDISCH_THEN(vX_CHOOSE_TAC (parse_term "s:int")) ---->
    vEXISTS_TAC (parse_term "m + s * n:int") ----> vCONJ_TAC ++-->
     [vASM_INT_ARITH_TAC; vEXISTS_TAC (parse_term "--s:int") ----> vINT_ARITH_TAC];
    vGEN_REWRITE_TAC vLAND_CONV [vINT_WOP] ---->
    vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC (parse_term "r:int") ---->
    vREWRITE_TAC[vLEFT_AND_EXISTS_THM; vRIGHT_AND_EXISTS_THM] ---->
    vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC (parse_term "q:int") ----> vSTRIP_TAC ---->
    vASM_REWRITE_TAC[] ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "r - abs n")) ---->
    vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "if &0 <= n then q + &1 else q - &1")) ---->
    vASM_INT_ARITH_TAC]);;

parse_as_infix("div",(22,"left"));;
parse_as_infix("rem",(22,"left"));;

let vINT_DIVISION_0 =  new_specification ["div"; "rem"]
  (vREWRITE_RULE[vSKOLEM_THM] vINT_DIVMOD_EXIST_0);;

let vINT_DIVISION = try Cache.lookup_thm "INT_DIVISION" with _ ->  prove
 ((parse_term "!m n. ~(n = &0)\n         ==> m = m div n * n + m rem n /\\ &0 <= m rem n /\\ m rem n < abs n"),
  vMESON_TAC[vINT_DIVISION_0]);;

let vINT_DIVISION_SIMP = try Cache.lookup_thm "INT_DIVISION_SIMP" with _ ->  prove
 ((parse_term "!m n. m div n * n + m rem n = m"),
  vMP_TAC vINT_DIVISION_0 ----> vREPEAT(vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC) ---->
  vCOND_CASES_TAC ----> vASM_SIMP_TAC[] ----> vCONV_TAC vINT_ARITH);;

let vINT_REM_POS = try Cache.lookup_thm "INT_REM_POS" with _ ->  prove
 ((parse_term "!a b. ~(b = &0) ==> &0 <= a rem b"),
  vMESON_TAC[vINT_DIVISION]);;

let vINT_DIV_0 = try Cache.lookup_thm "INT_DIV_0" with _ ->  prove
 ((parse_term "!m. m div &0 = &0"),
  vMESON_TAC[vINT_DIVISION_0]);;

let vINT_REM_0 = try Cache.lookup_thm "INT_REM_0" with _ ->  prove
 ((parse_term "!m. m rem &0 = m"),
  vMESON_TAC[vINT_DIVISION_0]);;

let vINT_REM_POS_EQ = try Cache.lookup_thm "INT_REM_POS_EQ" with _ ->  prove
 ((parse_term "!m n. &0 <= m rem n <=> n = &0 ==> &0 <= m"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n:int = &0") ---->
  vASM_SIMP_TAC[vINT_REM_0; vINT_REM_POS]);;

let vINT_REM_DIV = try Cache.lookup_thm "INT_REM_DIV" with _ ->  prove
 ((parse_term "!m n. m rem n = m - m div n * n"),
  vREWRITE_TAC[vINT_ARITH (parse_term "a:int = b - c <=> c + a = b")] ---->
  vREWRITE_TAC[vINT_DIVISION_SIMP]);;

let vINT_LT_REM = try Cache.lookup_thm "INT_LT_REM" with _ ->  prove
 ((parse_term "!x n. &0 < n ==> x rem n < n"),
  vMESON_TAC[vINT_DIVISION; vINT_LT_REFL; vINT_ARITH (parse_term "&0:int < n ==> abs n = n")]);;

let vINT_LT_REM_EQ = try Cache.lookup_thm "INT_LT_REM_EQ" with _ ->  prove
 ((parse_term "!m n. m rem n < n <=> &0 < n \\/ n = &0 /\\ m < &0"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n:int = &0") ---->
  vASM_SIMP_TAC[vINT_REM_0; vINT_LT_REFL] ---->
  vEQ_TAC ----> vREWRITE_TAC[vINT_LT_REM] ---->
  vMATCH_MP_TAC(vREWRITE_RULE[vIMP_CONJ] vINT_LET_TRANS) ---->
  vASM_SIMP_TAC[vINT_REM_POS]);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations on integers. Essentially a clone of stuff for reals *)
(* in the file "calc_int.ml", except for div and rem, which are more like N. *)
(* ------------------------------------------------------------------------- *)

let vINT_LE_CONV,vINT_LT_CONV,vINT_GE_CONV,vINT_GT_CONV,vINT_EQ_CONV =
  let tth =
    vTAUT (parse_term "(F /\\ F <=> F) /\\ (F /\\ T <=> F) /\\\n          (T /\\ F <=> F) /\\ (T /\\ T <=> T)") in
  let nth = vTAUT (parse_term "(~T <=> F) /\\ (~F <=> T)") in
  let vNUM2_EQ_CONV = vBINOP_CONV vNUM_EQ_CONV +---> vGEN_REWRITE_CONV vI [tth] in
  let vNUM2_NE_CONV =
    vRAND_CONV vNUM2_EQ_CONV +--->
    vGEN_REWRITE_CONV vI [nth] in
  let [@warning "-8"] [pth_le1; pth_le2a; pth_le2b; pth_le3] = (vCONJUNCTS -| prove)
   ((parse_term "(--(&m) <= &n <=> T) /\\\n     (&m <= &n <=> m <= n) /\\\n     (--(&m) <= --(&n) <=> n <= m) /\\\n     (&m <= --(&n) <=> (m = 0) /\\ (n = 0))"),
    vREWRITE_TAC[vINT_LE_NEG2] ---->
    vREWRITE_TAC[vINT_LE_LNEG; vINT_LE_RNEG] ---->
    vREWRITE_TAC[vINT_OF_NUM_ADD; vINT_OF_NUM_LE; vLE_0] ---->
    vREWRITE_TAC[vLE; vADD_EQ_0]) in
  let vINT_LE_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_le1];
    vGEN_REWRITE_CONV vI [pth_le2a; pth_le2b] +---> vNUM_LE_CONV;
    vGEN_REWRITE_CONV vI [pth_le3] +---> vNUM2_EQ_CONV] in
  let [@warning "-8"] [pth_lt1; pth_lt2a; pth_lt2b; pth_lt3] = (vCONJUNCTS -| prove)
   ((parse_term "(&m < --(&n) <=> F) /\\\n     (&m < &n <=> m < n) /\\\n     (--(&m) < --(&n) <=> n < m) /\\\n     (--(&m) < &n <=> ~((m = 0) /\\ (n = 0)))"),
    vREWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3;
                vGSYM vNOT_LE; vINT_LT] ---->
    vCONV_TAC vTAUT) in
  let vINT_LT_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_lt1];
    vGEN_REWRITE_CONV vI [pth_lt2a; pth_lt2b] +---> vNUM_LT_CONV;
    vGEN_REWRITE_CONV vI [pth_lt3] +---> vNUM2_NE_CONV] in
  let [@warning "-8"] [pth_ge1; pth_ge2a; pth_ge2b; pth_ge3] = (vCONJUNCTS -| prove)
   ((parse_term "(&m >= --(&n) <=> T) /\\\n     (&m >= &n <=> n <= m) /\\\n     (--(&m) >= --(&n) <=> m <= n) /\\\n     (--(&m) >= &n <=> (m = 0) /\\ (n = 0))"),
    vREWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; vINT_GE] ---->
    vCONV_TAC vTAUT) in
  let vINT_GE_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_ge1];
    vGEN_REWRITE_CONV vI [pth_ge2a; pth_ge2b] +---> vNUM_LE_CONV;
    vGEN_REWRITE_CONV vI [pth_ge3] +---> vNUM2_EQ_CONV] in
  let [@warning "-8"] [pth_gt1; pth_gt2a; pth_gt2b; pth_gt3] = (vCONJUNCTS -| prove)
   ((parse_term "(--(&m) > &n <=> F) /\\\n     (&m > &n <=> n < m) /\\\n     (--(&m) > --(&n) <=> m < n) /\\\n     (&m > --(&n) <=> ~((m = 0) /\\ (n = 0)))"),
    vREWRITE_TAC[pth_lt1; pth_lt2a; pth_lt2b; pth_lt3; vINT_GT] ---->
    vCONV_TAC vTAUT) in
  let vINT_GT_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_gt1];
    vGEN_REWRITE_CONV vI [pth_gt2a; pth_gt2b] +---> vNUM_LT_CONV;
    vGEN_REWRITE_CONV vI [pth_gt3] +---> vNUM2_NE_CONV] in
  let [@warning "-8"] [pth_eq1a; pth_eq1b; pth_eq2a; pth_eq2b] = (vCONJUNCTS -| prove)
   ((parse_term "((&m = &n) <=> (m = n)) /\\\n     ((--(&m) = --(&n)) <=> (m = n)) /\\\n     ((--(&m) = &n) <=> (m = 0) /\\ (n = 0)) /\\\n     ((&m = --(&n)) <=> (m = 0) /\\ (n = 0))"),
    vREWRITE_TAC[vGSYM vINT_LE_ANTISYM; vGSYM vLE_ANTISYM] ---->
    vREWRITE_TAC[pth_le1; pth_le2a; pth_le2b; pth_le3; vLE; vLE_0] ---->
    vCONV_TAC vTAUT) in
  let vINT_EQ_CONV = vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth_eq1a; pth_eq1b] +---> vNUM_EQ_CONV;
    vGEN_REWRITE_CONV vI [pth_eq2a; pth_eq2b] +---> vNUM2_EQ_CONV] in
  vINT_LE_CONV,vINT_LT_CONV,
  vINT_GE_CONV,vINT_GT_CONV,vINT_EQ_CONV;;

let vINT_NEG_CONV =
  let pth = prove
   ((parse_term "(--(&0) = &0) /\\\n     (--(--(&x)) = &x)"),
    vREWRITE_TAC[vINT_NEG_NEG; vINT_NEG_0]) in
  vGEN_REWRITE_CONV vI [pth];;

let vINT_MUL_CONV =
  let pth0 = prove
   ((parse_term "(&0 * &x = &0) /\\\n     (&0 * --(&x) = &0) /\\\n     (&x * &0 = &0) /\\\n     (--(&x) * &0 = &0)"),
    vREWRITE_TAC[vINT_MUL_LZERO; vINT_MUL_RZERO])
  and pth1,pth2 = (vCONJ_PAIR -| prove)
   ((parse_term "((&m * &n = &(m * n)) /\\\n      (--(&m) * --(&n) = &(m * n))) /\\\n     ((--(&m) * &n = --(&(m * n))) /\\\n      (&m * --(&n) = --(&(m * n))))"),
    vREWRITE_TAC[vINT_MUL_LNEG; vINT_MUL_RNEG; vINT_NEG_NEG] ---->
    vREWRITE_TAC[vINT_OF_NUM_MUL]) in
  vFIRST_CONV
   [vGEN_REWRITE_CONV vI [pth0];
    vGEN_REWRITE_CONV vI [pth1] +---> vRAND_CONV vNUM_MULT_CONV;
    vGEN_REWRITE_CONV vI [pth2] +---> vRAND_CONV(vRAND_CONV vNUM_MULT_CONV)];;

let vINT_ADD_CONV =
  let neg_tm = (parse_term "(--)") in
  let amp_tm = (parse_term "&") in
  let add_tm = (parse_term "(+)") in
  let dest = dest_binop (parse_term "(+)") in
  let m_tm = (parse_term "m:num") and n_tm = (parse_term "n:num") in
  let pth0 = prove
   ((parse_term "(--(&m) + &m = &0) /\\\n     (&m + --(&m) = &0)"),
    vREWRITE_TAC[vINT_ADD_LINV; vINT_ADD_RINV]) in
  let [@warning "-8"] [pth1; pth2; pth3; pth4; pth5; pth6] = (vCONJUNCTS -| prove)
   ((parse_term "(--(&m) + --(&n) = --(&(m + n))) /\\\n     (--(&m) + &(m + n) = &n) /\\\n     (--(&(m + n)) + &m = --(&n)) /\\\n     (&(m + n) + --(&m) = &n) /\\\n     (&m + --(&(m + n)) = --(&n)) /\\\n     (&m + &n = &(m + n))"),
    vREWRITE_TAC[vGSYM vINT_OF_NUM_ADD; vINT_NEG_ADD] ---->
    vREWRITE_TAC[vINT_ADD_ASSOC; vINT_ADD_LINV; vINT_ADD_LID] ---->
    vREWRITE_TAC[vINT_ADD_RINV; vINT_ADD_LID] ---->
    vONCE_REWRITE_TAC[vINT_ADD_SYM] ---->
    vREWRITE_TAC[vINT_ADD_ASSOC; vINT_ADD_LINV; vINT_ADD_LID] ---->
    vREWRITE_TAC[vINT_ADD_RINV; vINT_ADD_LID]) in
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
    with Failure _ -> failwith "INT_ADD_CONV");;

let vINT_SUB_CONV =
  vGEN_REWRITE_CONV vI [vINT_SUB] +--->
  vTRY_CONV(vRAND_CONV vINT_NEG_CONV) +--->
  vINT_ADD_CONV;;

let vINT_POW_CONV =
  let pth1,pth2 = (vCONJ_PAIR -| prove)
   ((parse_term "(&x pow n = &(x EXP n)) /\\\n     ((--(&x)) pow n = if EVEN n then &(x EXP n) else --(&(x EXP n)))"),
    vREWRITE_TAC[vINT_OF_NUM_POW; vINT_POW_NEG]) in
  let tth = prove
   ((parse_term "((if T then x:int else y) = x) /\\ ((if F then x:int else y) = y)"),
    vREWRITE_TAC[]) in
  let neg_tm = (parse_term "(--)") in
  (vGEN_REWRITE_CONV vI [pth1] +---> vRAND_CONV vNUM_EXP_CONV) ||-->
  (vGEN_REWRITE_CONV vI [pth2] +--->
   vRATOR_CONV(vRATOR_CONV(vRAND_CONV vNUM_EVEN_CONV)) +--->
   vGEN_REWRITE_CONV vI [tth] +--->
   (fun tm -> if rator tm = neg_tm then vRAND_CONV(vRAND_CONV vNUM_EXP_CONV) tm
              else vRAND_CONV vNUM_EXP_CONV  tm));;

let vINT_ABS_CONV =
  let pth = prove
   ((parse_term "(abs(--(&x)) = &x) /\\\n     (abs(&x) = &x)"),
    vREWRITE_TAC[vINT_ABS_NEG; vINT_ABS_NUM]) in
  vGEN_REWRITE_CONV vI [pth];;

let vINT_MAX_CONV =
  vREWR_CONV vINT_MAX +--->
  vRATOR_CONV(vRATOR_CONV(vRAND_CONV vINT_LE_CONV)) +--->
  vGEN_REWRITE_CONV vI [vCOND_CLAUSES];;

let vINT_MIN_CONV =
  vREWR_CONV vINT_MIN +--->
  vRATOR_CONV(vRATOR_CONV(vRAND_CONV vINT_LE_CONV)) +--->
  vGEN_REWRITE_CONV vI [vCOND_CLAUSES];;

let vINT_SGN_CONV =
  vGEN_REWRITE_CONV vI [vINT_SGN] +--->
  vRATOR_CONV(vLAND_CONV vINT_LT_CONV) +--->
  (vGEN_REWRITE_CONV vI [vCONJUNCT1(vSPEC_ALL vCOND_CLAUSES)] ||-->
   (vGEN_REWRITE_CONV vI [vCONJUNCT2(vSPEC_ALL vCOND_CLAUSES)] +--->
    vRATOR_CONV(vLAND_CONV vINT_LT_CONV) +--->
    vGEN_REWRITE_CONV vI [vCOND_CLAUSES]));;

(* ------------------------------------------------------------------------- *)
(* Instantiate the normalizer.                                               *)
(* ------------------------------------------------------------------------- *)

let vINT_POLY_CONV =
  let sth = prove
   ((parse_term "(!x y z. x + (y + z) = (x + y) + z) /\\\n     (!x y. x + y = y + x) /\\\n     (!x. &0 + x = x) /\\\n     (!x y z. x * (y * z) = (x * y) * z) /\\\n     (!x y. x * y = y * x) /\\\n     (!x. &1 * x = x) /\\\n     (!x. &0 * x = &0) /\\\n     (!x y z. x * (y + z) = x * y + x * z) /\\\n     (!x. x pow 0 = &1) /\\\n     (!x n. x pow (SUC n) = x * x pow n)"),
    vREWRITE_TAC[vINT_POW] ----> vINT_ARITH_TAC)
  and rth = prove
   ((parse_term "(!x. --x = --(&1) * x) /\\\n     (!x y. x - y = x + --(&1) * y)"),
    vINT_ARITH_TAC)
  and is_semiring_constant = is_intconst
  and vSEMIRING_ADD_CONV = vINT_ADD_CONV
  and vSEMIRING_MUL_CONV = vINT_MUL_CONV
  and vSEMIRING_POW_CONV = vINT_POW_CONV in
  let _,_,_,_,_,vINT_POLY_CONV =
    vSEMIRING_NORMALIZERS_CONV sth rth
     (is_semiring_constant,
      vSEMIRING_ADD_CONV,vSEMIRING_MUL_CONV,vSEMIRING_POW_CONV)
     (<) in
  vINT_POLY_CONV;;

(* ------------------------------------------------------------------------- *)
(* Instantiate the ring and ideal procedures.                                *)
(* ------------------------------------------------------------------------- *)

let vINT_RING,int_ideal_cofactors =
  let vINT_INTEGRAL = prove
   ((parse_term "(!x. &0 * x = &0) /\\\n     (!x y z. (x + y = x + z) <=> (y = z)) /\\\n     (!w x y z. (w * y + x * z = w * z + x * y) <=> (w = x) \\/ (y = z))"),
    vREWRITE_TAC[vMULT_CLAUSES; vEQ_ADD_LCANCEL] ---->
    vREWRITE_TAC[vGSYM vINT_OF_NUM_EQ;
                vGSYM vINT_OF_NUM_ADD; vGSYM vINT_OF_NUM_MUL] ---->
    vONCE_REWRITE_TAC[vGSYM vINT_SUB_0] ---->
    vREWRITE_TAC[vGSYM vINT_ENTIRE] ----> vINT_ARITH_TAC)
  and int_ty = (parse_type "int") in
  let pure,ideal =
  vRING_AND_IDEAL_CONV
      (dest_intconst,mk_intconst,vINT_EQ_CONV,
       (parse_term "(--):int->int"),(parse_term "(+):int->int->int"),(parse_term "(-):int->int->int"),
       genvar bool_ty,(parse_term "(*):int->int->int"),genvar bool_ty,
       (parse_term "(pow):int->num->int"),
       vINT_INTEGRAL,vTRUTH,vINT_POLY_CONV) in
  pure,
  (fun tms tm -> if forall (fun t -> type_of t = int_ty) (tm::tms)
                 then ideal tms tm
                 else failwith
                  "int_ideal_cofactors: not all terms have type :int");;

(* ------------------------------------------------------------------------- *)
(* Set up overloading so we can use same symbols for N, Z and even R.        *)
(* ------------------------------------------------------------------------- *)

make_overloadable "divides" (parse_type "A->A->bool");;
make_overloadable "mod" (parse_type "A->A->A->bool");;
make_overloadable "coprime" (parse_type "A#A->bool");;
make_overloadable "gcd" (parse_type "A#A->A");;
make_overloadable "lcm" (parse_type "A#A->A");;

(* ------------------------------------------------------------------------- *)
(* The general notion of congruence: just syntax for equivalence relation.   *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("==",(10,"right"));;

let cong = new_definition
  (parse_term "(x == y) (rel:A->A->bool) <=> rel x y");;

(* ------------------------------------------------------------------------- *)
(* Get real moduli defined and out of the way first.                         *)
(* ------------------------------------------------------------------------- *)

let real_mod = new_definition
  (parse_term "real_mod n (x:real) y = ?q. integer q /\\ x - y = q * n");;

overload_interface ("mod",(parse_term "real_mod"));;

(* ------------------------------------------------------------------------- *)
(* Integer divisibility.                                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("divides",(12,"right"));;
overload_interface("divides",(parse_term "int_divides:int->int->bool"));;

let int_divides = new_definition
  (parse_term "a divides b <=> ?x. b = a * x");;

let vINT_DIVIDES_LE = try Cache.lookup_thm "INT_DIVIDES_LE" with _ ->  prove
 ((parse_term "!x y:int. x divides y ==> abs(x) <= abs(y) \\/ y = &0"),
  vSIMP_TAC[int_divides; vLEFT_IMP_EXISTS_THM; vINT_ABS_MUL; vINT_ENTIRE] ---->
  vREWRITE_TAC[vTAUT (parse_term "p \\/ q \\/ r <=> ~q /\\ ~r ==> p")] ---->
  vREWRITE_TAC[vINT_ARITH (parse_term "x:int <= x * y <=> &0 <= x * (y - &1)")] ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vINT_LE_MUL ----> vASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integer congruences.                                                      *)
(* ------------------------------------------------------------------------- *)

parse_as_prefix "mod";;
overload_interface ("mod",(parse_term "int_mod:int->int->int->bool"));;

let int_mod = new_definition
  (parse_term "(mod n) x y = n divides (x - y)");;

let int_congruent = try Cache.lookup_thm "int_congruent" with _ ->  prove
 ((parse_term "!x y n. (x == y) (mod n) <=> ?d. x - y = n * d"),
  vREWRITE_TAC[int_mod; cong; int_divides]);;

let vINT_CONG_IMP_EQ = try Cache.lookup_thm "INT_CONG_IMP_EQ" with _ ->  prove
 ((parse_term "!x y n:int. abs(x - y) < n /\\ (x == y) (mod n) ==> x = y"),
  vREWRITE_TAC[int_congruent; vGSYM int_divides] ---->
  vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vINT_DIVIDES_LE) ---->
  vASM_INT_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Integer coprimality.                                                      *)
(* ------------------------------------------------------------------------- *)

overload_interface("coprime",(parse_term "int_coprime:int#int->bool"));;

let int_coprime = new_definition
 (parse_term "!a b. coprime(a,b) <=> ?x y. a * x + b * y = &1");;

(* ------------------------------------------------------------------------- *)
(* A tactic for simple divisibility/congruence/coprimality goals.            *)
(* ------------------------------------------------------------------------- *)

let vINTEGER_TAC =
  let int_ty = (parse_type "int") in
  let vINT_POLYEQ_CONV =
    vGEN_REWRITE_CONV vI [vGSYM vINT_SUB_0] +---> vLAND_CONV vINT_POLY_CONV in
  let vISOLATE_VARIABLE =
    let pth = vINT_ARITH (parse_term "!a x. a = &0 <=> x = x + a") in
    let is_defined v t =
      let mons = striplist(dest_binary "int_add") t in
      mem v mons && forall (fun m -> v = m || not(free_in v m)) mons in
    fun vars tm ->
      let th = vINT_POLYEQ_CONV tm
      and th' = (vSYM_CONV +---> vINT_POLYEQ_CONV) tm in
      let v,th1 =
          try find (fun v -> is_defined v (lhand(rand(concl th)))) vars,th'
          with Failure _ ->
              find (fun v -> is_defined v (lhand(rand(concl th')))) vars,th in
      let th2 = vTRANS th1 (vSPECL [lhs(rand(concl th1)); v] pth) in
      vCONV_RULE(vRAND_CONV(vRAND_CONV vINT_POLY_CONV)) th2 in
  let vUNWIND_POLYS_CONV tm =
    let vars,bod = strip_exists tm in
    let cjs = conjuncts bod in
    let th1 = tryfind (vISOLATE_VARIABLE vars) cjs in
    let eq = lhand(concl th1) in
    let bod' = list_mk_conj(eq::(subtract cjs [eq])) in
    let th2 = vCONJ_ACI_RULE(mk_eq(bod,bod')) in
    let th3 = vTRANS th2 (vMK_CONJ th1 (vREFL(rand(rand(concl th2))))) in
    let v = lhs(lhand(rand(concl th3))) in
    let vars' = (subtract vars [v]) @ [v] in
    let th4 = vCONV_RULE(vRAND_CONV(vREWR_CONV vUNWIND_THM2)) (vMK_EXISTS v th3) in
    let vIMP_RULE v v' =
     vDISCH_ALL(itlist vSIMPLE_CHOOSE v (itlist vSIMPLE_EXISTS v' (vASSUME bod))) in
    let th5 = vIMP_ANTISYM_RULE (vIMP_RULE vars vars') (vIMP_RULE vars' vars) in
    vTRANS th5 (itlist vMK_EXISTS (subtract vars [v]) th4) in
  let zero_tm = (parse_term "&0") and one_tm = (parse_term "&1") in
  let isolate_monomials =
    let mul_tm = (parse_term "(int_mul)") and add_tm = (parse_term "(int_add)")
    and neg_tm = (parse_term "(int_neg)") in
    let dest_mul = dest_binop mul_tm
    and dest_add = dest_binop add_tm
    and mk_mul = mk_binop mul_tm
    and mk_add = mk_binop add_tm in
    let scrub_var v m =
      let ps = striplist dest_mul m in
      let ps' = subtract ps [v] in
      if ps' = [] then one_tm else end_itlist mk_mul ps' in
    let find_multipliers v mons =
      let mons1 = filter (fun m -> free_in v m) mons in
      let mons2 = map (scrub_var v) mons1 in
      if mons2 = [] then zero_tm else end_itlist mk_add mons2 in
    fun vars tm ->
      let cmons,vmons =
         partition (fun m -> intersect (frees m) vars = [])
                   (striplist dest_add tm) in
      let cofactors = map (fun v -> find_multipliers v vmons) vars
      and cnc = if cmons = [] then zero_tm
                else mk_comb(neg_tm,end_itlist mk_add cmons) in
      cofactors,cnc in
  let isolate_variables evs ps eq =
    let vars = filter (fun v -> vfree_in v eq) evs in
    let qs,p = isolate_monomials vars eq in
    let rs = filter (fun t -> type_of t = int_ty) (qs @ ps) in
    let rs = int_ideal_cofactors rs p in
    eq,zip (fst(chop_list(length qs) rs)) vars in
  let subst_in_poly i p = rhs(concl(vINT_POLY_CONV (vsubst i p))) in
  let rec solve_idealism evs ps eqs =
    if evs = [] then [] else
    let eq,cfs = tryfind (isolate_variables evs ps) eqs in
    let evs' = subtract evs (map snd cfs)
    and eqs' = map (subst_in_poly cfs) (subtract eqs [eq]) in
    cfs @ solve_idealism evs' ps eqs' in
  let rec vGENVAR_EXISTS_CONV tm =
    if not(is_exists tm) then vREFL tm else
    let ev,_bod = dest_exists tm in
    let gv = genvar(type_of ev) in
    (vGEN_ALPHA_CONV gv +---> vBINDER_CONV vGENVAR_EXISTS_CONV) tm in
  let vEXISTS_POLY_TAC (asl,w as gl) =
    let evs,bod = strip_exists w
    and ps = mapfilter (check (fun t -> type_of t = int_ty) -|
                        lhs -| concl -| snd) asl in
    let cfs = solve_idealism evs ps (map lhs (conjuncts bod)) in
    (vMAP_EVERY vEXISTS_TAC(map (fun v -> rev_assocd v cfs zero_tm) evs) ---->
     vREPEAT(vPOP_ASSUM vMP_TAC) ----> vCONV_TAC vINT_RING) gl in
  let vSCRUB_NEQ_TAC = vMATCH_MP_TAC -| vMATCH_MP (vMESON[]
    (parse_term "~(x = y) ==> x = y \\/ p ==> p")) in
  vREWRITE_TAC[int_coprime; int_congruent; int_divides] ---->
  vREPEAT(vSTRIP_TAC |---> vEQ_TAC) ---->
  vREWRITE_TAC[vLEFT_AND_EXISTS_THM; vRIGHT_AND_EXISTS_THM;
              vLEFT_OR_EXISTS_THM; vRIGHT_OR_EXISTS_THM] ---->
  vCONV_TAC(vREPEATC vUNWIND_POLYS_CONV) ---->
  vREPEAT(vFIRST_X_ASSUM vSCRUB_NEQ_TAC) ---->
  vREWRITE_TAC[vLEFT_AND_EXISTS_THM; vRIGHT_AND_EXISTS_THM;
              vLEFT_OR_EXISTS_THM; vRIGHT_OR_EXISTS_THM] ---->
  vREPEAT(vFIRST_X_ASSUM(vMP_TAC -| vSYM)) ---->
  vCONV_TAC(vONCE_DEPTH_CONV vINT_POLYEQ_CONV) ---->
  vREWRITE_TAC[vGSYM vINT_ENTIRE;
              vTAUT (parse_term "a \\/ (b /\\ c) <=> (a \\/ b) /\\ (a \\/ c)")] ---->
  vPOP_ASSUM_LIST(vK vALL_TAC) ---->
  vREPEAT vDISCH_TAC ----> vCONV_TAC vGENVAR_EXISTS_CONV ---->
  vCONV_TAC(vONCE_DEPTH_CONV vINT_POLYEQ_CONV) ----> vEXISTS_POLY_TAC;;

let vINTEGER_RULE tm = prove(tm,vINTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* More div and rem properties.                                              *)
(* ------------------------------------------------------------------------- *)

let vINT_DIVMOD_UNIQ = try Cache.lookup_thm "INT_DIVMOD_UNIQ" with _ ->  prove
 ((parse_term "!m n q r. m = q * n + r /\\ &0 <= r /\\ r < abs n\n             ==> m div n = q /\\ m rem n = r"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "~(n = &0)") vMP_TAC ++--> [vASM_INT_ARITH_TAC; vALL_TAC] ---->
  vDISCH_THEN(vSTRIP_ASSUME_TAC -| vSPEC (parse_term "m:int") -| vMATCH_MP vINT_DIVISION) ---->
  vASM_CASES_TAC (parse_term "m div n = q") ++-->
   [vREPEAT(vPOP_ASSUM vMP_TAC) ----> vCONV_TAC vINT_RING; vALL_TAC] ---->
  vSUBGOAL_THEN (parse_term "abs(m rem n - r) < abs n") vMP_TAC ++-->
   [vASM_INT_ARITH_TAC; vMATCH_MP_TAC(vTAUT (parse_term "~p ==> p ==> q"))] ---->
  vMATCH_MP_TAC(vINT_ARITH
   (parse_term "&1 * abs n <= abs(q - m div n) * abs n /\\\n    abs(m rem n - r) = abs((q - m div n) * n)\n    ==> ~(abs(m rem n - r) < abs n)")) ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vINT_LE_RMUL ----> vASM_INT_ARITH_TAC;
    vAP_TERM_TAC ----> vREPEAT(vPOP_ASSUM vMP_TAC) ----> vCONV_TAC vINT_RING]);;

let vINT_DIV_UNIQ = try Cache.lookup_thm "INT_DIV_UNIQ" with _ ->  prove
 ((parse_term "!m n q r. m = q * n + r /\\ &0 <= r /\\ r < abs n\n             ==> m div n = q"),
  vMESON_TAC[vINT_DIVMOD_UNIQ]);;

let vINT_REM_UNIQ = try Cache.lookup_thm "INT_REM_UNIQ" with _ ->  prove
 ((parse_term "!m n q r. m = q * n + r /\\ &0 <= r /\\ r < abs n\n             ==> m rem n = r"),
    vMESON_TAC[vINT_DIVMOD_UNIQ]);;

let vINT_DIV_LT,vINT_REM_LT = (vCONJ_PAIR -| prove)
 ((parse_term "(!m n. (~(n = &0) ==> &0 <= m) /\\ m < n ==> m div n = &0) /\\\n   (!m n. (~(n = &0) ==> &0 <= m) /\\ m < n ==> m rem n = m)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n:int = &0") ----> vASM_REWRITE_TAC[vINT_DIV_0; vINT_REM_0] ---->
  vREWRITE_TAC[vTAUT (parse_term "(p ==> q) /\\ (p ==> r) <=> p ==> q /\\ r")] ---->
  vSTRIP_TAC ----> vMATCH_MP_TAC vINT_DIVMOD_UNIQ ----> vASM_INT_ARITH_TAC);;

let vINT_DIV_RNEG,vINT_REM_RNEG = (vCONJ_PAIR -| prove)
 ((parse_term "(!m n. m div (--n) = --(m div n)) /\\\n   (!m n. m rem (--n) = m rem n)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n:int = &0") ---->
  vASM_REWRITE_TAC[vINT_DIV_0; vINT_REM_0; vINT_NEG_0] ---->
  vMATCH_MP_TAC vINT_DIVMOD_UNIQ ---->
  vMP_TAC(vSPECL [(parse_term "m:int"); (parse_term "n:int")] vINT_DIVISION) ---->
  vASM_INT_ARITH_TAC);;

let vINT_REM_RABS = try Cache.lookup_thm "INT_REM_RABS" with _ ->  prove
 ((parse_term "!x y. x rem (abs y) = x rem y"),
  vREWRITE_TAC[vFORALL_INT_CASES; vINT_ABS_NEG; vINT_REM_RNEG; vINT_ABS_NUM]);;

let vINT_REM_REM = try Cache.lookup_thm "INT_REM_REM" with _ ->  prove
 ((parse_term "!m n. (m rem n) rem n = m rem n"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n:int = &0") ----> vASM_REWRITE_TAC[vINT_REM_0] ---->
  vMATCH_MP_TAC vINT_REM_UNIQ ----> vEXISTS_TAC (parse_term "&0:int") ---->
  vREWRITE_TAC[vINT_MUL_LZERO; vINT_ADD_LID] ---->
  vASM_MESON_TAC[vINT_DIVISION]);;

let vINT_REM_EQ = try Cache.lookup_thm "INT_REM_EQ" with _ ->  prove
 ((parse_term "!m n p. m rem p = n rem p <=> (m == n) (mod p)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[int_congruent] ---->
  vEQ_TAC ++-->
   [vDISCH_TAC ----> vEXISTS_TAC (parse_term "m div p - n div p") ---->
    vMP_TAC(vSPECL [(parse_term "m:int"); (parse_term "p:int")] vINT_DIVISION_SIMP) ---->
    vMP_TAC(vSPECL [(parse_term "n:int"); (parse_term "p:int")] vINT_DIVISION_SIMP) ---->
    vASM_REWRITE_TAC[] ----> vCONV_TAC vINT_RING;
    vREWRITE_TAC[vLEFT_IMP_EXISTS_THM; vINT_EQ_SUB_RADD] ---->
    vX_GEN_TAC (parse_term "d:int") ----> vDISCH_THEN vSUBST1_TAC ---->
    vASM_CASES_TAC (parse_term "p:int = &0") ---->
    vASM_REWRITE_TAC[vINT_REM_0; vINT_MUL_LZERO; vINT_ADD_LID] ---->
    vMATCH_MP_TAC vINT_REM_UNIQ ----> vEXISTS_TAC (parse_term "n div p + d") ---->
    vMP_TAC(vSPECL [(parse_term "n:int"); (parse_term "p:int")] vINT_DIVISION) ---->
    vASM_SIMP_TAC[] ----> vCONV_TAC vINT_RING]);;

let vINT_DIV_ZERO,vINT_REM_ZERO = (vCONJ_PAIR -| prove)
 ((parse_term "(!n. &0 div n = &0) /\\ (!n. &0 rem n = &0)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n:int = &0") ----> vASM_REWRITE_TAC[vINT_DIV_0; vINT_REM_0] ---->
  vMATCH_MP_TAC vINT_DIVMOD_UNIQ ---->
  vASM_INT_ARITH_TAC);;

let vINT_REM_EQ_0 = try Cache.lookup_thm "INT_REM_EQ_0" with _ ->  prove
 ((parse_term "!m n. m rem n = &0 <=> n divides m"),
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPEC (parse_term "n:int") vINT_REM_ZERO)) ---->
  vREWRITE_TAC[vINT_REM_EQ] ----> vCONV_TAC vINTEGER_RULE);;

let vINT_MUL_DIV_EQ = try Cache.lookup_thm "INT_MUL_DIV_EQ" with _ ->  prove
 ((parse_term "(!m n. n * m div n = m <=> n divides m) /\\\n   (!m n. m div n * n = m <=> n divides m)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vREPEAT vGEN_TAC ---->
  vMP_TAC(vSPECL [(parse_term "m:int"); (parse_term "n:int")] vINT_DIVISION_SIMP) ---->
  vREWRITE_TAC[vGSYM vINT_REM_EQ_0] ----> vCONV_TAC vINT_RING);;

let vINT_CONG_LREM = try Cache.lookup_thm "INT_CONG_LREM" with _ ->  prove
 ((parse_term "!x y n. (x rem n == y) (mod n) <=> (x == y) (mod n)"),
  vREWRITE_TAC[vGSYM vINT_REM_EQ; vINT_REM_REM]);;

let vINT_CONG_RREM = try Cache.lookup_thm "INT_CONG_RREM" with _ ->  prove
 ((parse_term "!x y n. (x == y rem n) (mod n) <=> (x == y) (mod n)"),
  vREWRITE_TAC[vGSYM vINT_REM_EQ; vINT_REM_REM]);;

let vINT_REM_MOD_SELF = try Cache.lookup_thm "INT_REM_MOD_SELF" with _ ->  prove
 ((parse_term "!m n. (m rem n == m) (mod n)"),
  vREWRITE_TAC[vINT_CONG_LREM] ----> vCONV_TAC vINTEGER_RULE);;

let vINT_REM_REM_MUL = try Cache.lookup_thm "INT_REM_REM_MUL" with _ ->  prove
 ((parse_term "(!m n p. m rem (n * p) rem n = m rem n) /\\\n   (!m n p. m rem (n * p) rem p = m rem p)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vINT_REM_EQ] ++-->
   [vMP_TAC(vISPECL [(parse_term "m:int"); (parse_term "n * p:int")] vINT_REM_MOD_SELF);
    vMP_TAC(vISPECL [(parse_term "m:int"); (parse_term "n * p:int")] vINT_REM_MOD_SELF)] ---->
  vCONV_TAC vINTEGER_RULE);;

let vINT_CONG_SOLVE_BOUNDS = try Cache.lookup_thm "INT_CONG_SOLVE_BOUNDS" with _ ->  prove
 ((parse_term "!a n:int. ~(n = &0) ==> ?x. &0 <= x /\\ x < abs n /\\ (x == a) (mod n)"),
  vMESON_TAC[vINT_DIVISION; vINT_REM_MOD_SELF]);;

let vINT_NEG_REM = try Cache.lookup_thm "INT_NEG_REM" with _ ->  prove
 ((parse_term "!n p. --(n rem p) rem p = --n rem p"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vINT_REM_EQ] ---->
  vMATCH_MP_TAC(vINTEGER_RULE
   (parse_term "(a:int == b) (mod n) ==> (--a == --b) (mod n)")) ---->
  vREWRITE_TAC[vINT_REM_MOD_SELF]);;

let vINT_ADD_REM = try Cache.lookup_thm "INT_ADD_REM" with _ ->  prove
 ((parse_term "!m n p. (m rem p + n rem p) rem p = (m + n) rem p"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vINT_REM_EQ] ----> vMATCH_MP_TAC(vINTEGER_RULE
   (parse_term "(x:int == x') (mod n) /\\ (y == y') (mod n)\n    ==> (x + y == x' + y') (mod n)")) ---->
  vREWRITE_TAC[vINT_REM_MOD_SELF]);;

let vINT_SUB_REM = try Cache.lookup_thm "INT_SUB_REM" with _ ->  prove
 ((parse_term "!m n p. (m rem p - n rem p) rem p = (m - n) rem p"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vINT_REM_EQ] ----> vMATCH_MP_TAC(vINTEGER_RULE
   (parse_term "(x:int == x') (mod n) /\\ (y == y') (mod n)\n    ==> (x - y == x' - y') (mod n)")) ---->
  vREWRITE_TAC[vINT_REM_MOD_SELF]);;

let vINT_MUL_REM = try Cache.lookup_thm "INT_MUL_REM" with _ ->  prove
 ((parse_term "!m n p. (m rem p * n rem p) rem p = (m * n) rem p"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vINT_REM_EQ] ----> vMATCH_MP_TAC(vINTEGER_RULE
   (parse_term "(x:int == x') (mod n) /\\ (y == y') (mod n)\n    ==> (x * y == x' * y') (mod n)")) ---->
  vREWRITE_TAC[vINT_REM_MOD_SELF]);;

let vINT_POW_REM = try Cache.lookup_thm "INT_POW_REM" with _ ->  prove
 ((parse_term "!m n p. ((m rem p) pow n) rem p = (m pow n) rem p"),
  vGEN_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[vINT_POW] ---->
  vGEN_TAC ----> vGEN_REWRITE_TAC vLAND_CONV [vGSYM vINT_MUL_REM] ---->
  vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vINT_REM_REM] ---->
  vREWRITE_TAC[vINT_MUL_REM]);;

let vINT_OF_NUM_DIV,vINT_OF_NUM_REM = (vCONJ_PAIR -| prove)
 ((parse_term "(!m n. &m div &n = &(m DIV n)) /\\\n   (!m n. &m rem &n = &(m MOD n))"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vINT_DIV_0; vINT_REM_0; vDIV_ZERO; vMOD_ZERO] ---->
  vMATCH_MP_TAC vINT_DIVMOD_UNIQ ---->
  vREWRITE_TAC[vINT_OF_NUM_MUL; vINT_OF_NUM_ADD; vINT_ABS_NUM] ---->
  vREWRITE_TAC[vINT_POS; vINT_OF_NUM_EQ; vINT_OF_NUM_LT] ---->
  vMATCH_MP_TAC vDIVISION ----> vASM_REWRITE_TAC[]);;

let vINT_DIV_REFL,vINT_REM_REFL = (vCONJ_PAIR -| prove)
 ((parse_term "(!n. n div n = if n = &0 then &0 else &1) /\\\n   (!n. n rem n = &0)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vX_GEN_TAC (parse_term "n:int") ---->
  vCOND_CASES_TAC ++--> [vASM_MESON_TAC[vINT_DIV_0; vINT_REM_0]; vALL_TAC] ---->
  vMATCH_MP_TAC vINT_DIVMOD_UNIQ ----> vASM_INT_ARITH_TAC);;

let vINT_DIV_LNEG,vINT_REM_LNEG = (vCONJ_PAIR -| prove)
 ((parse_term "(!m n. --m div n =\n          if m rem n = &0 then --(m div n) else --(m div n) - int_sgn n) /\\\n   (!m n. --m rem n =\n          if m rem n = &0 then &0 else abs n - m rem n)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vMAP_EVERY vX_GEN_TAC [(parse_term "m:int"); (parse_term "n:int")] ---->
  vASM_CASES_TAC (parse_term "n:int = &0") ++-->
   [vASM_REWRITE_TAC[vINT_DIV_0; vINT_REM_0; vINT_SGN_0] ----> vINT_ARITH_TAC;
    vALL_TAC] ---->
  vMATCH_MP_TAC vINT_DIVMOD_UNIQ ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC (parse_term "m:int") -| vMATCH_MP vINT_DIVISION) ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vINT_SGN_ABS_ALT; vINT_ARITH
   (parse_term "--m:int = (--x - y) * z + w <=> m = x * z + y * z - w")] ---->
  vASM_REWRITE_TAC[] ----> vASM_INT_ARITH_TAC);;

let vINT_DIV_NEG2 = try Cache.lookup_thm "INT_DIV_NEG2" with _ ->  prove
 ((parse_term "!m n. --m div --n = if m rem n = &0 then m div n else m div n + int_sgn n"),
  vREWRITE_TAC[vINT_DIV_RNEG; vINT_DIV_LNEG; vINT_SGN_NEG; vINT_REM_RNEG] ---->
  vINT_ARITH_TAC);;

let vINT_REM_NEG2 = try Cache.lookup_thm "INT_REM_NEG2" with _ ->  prove
 ((parse_term "!m n. --m rem --n = if m rem n = &0 then &0 else abs n - m rem n"),
  vREWRITE_TAC[vINT_REM_LNEG; vINT_REM_RNEG] ----> vINT_ARITH_TAC);;

let vINT_DIV_1,vINT_REM_1 = (vCONJ_PAIR -| prove)
 ((parse_term "(!n. n div &1 = n) /\\\n   (!n. n rem &1 = &0)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vGEN_TAC ---->
  vMATCH_MP_TAC vINT_DIVMOD_UNIQ ----> vINT_ARITH_TAC);;

let vINT_DIV_MUL,vINT_REM_MUL = (vCONJ_PAIR -| prove)
 ((parse_term "((!m n. ~(n = &0) ==> (m * n) div n = m) /\\\n    (!m n. ~(m = &0) ==> (m * n) div m = n)) /\\\n   ((!m n. (m * n) rem n = &0) /\\\n    (!m n. (m * n) rem m = &0))"),
  vMATCH_MP_TAC(vTAUT
   (parse_term "((p ==> p') /\\ (q ==> q')) /\\ p /\\ q ==> (p /\\ p') /\\ (q /\\ q')")) ---->
  vCONJ_TAC ++--> [vMESON_TAC[vINT_MUL_SYM]; vREWRITE_TAC[vAND_FORALL_THM]] ---->
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n:int = &0") ---->
  vASM_REWRITE_TAC[vINT_REM_0; vINT_MUL_RZERO] ---->
  vMATCH_MP_TAC vINT_DIVMOD_UNIQ ----> vASM_INT_ARITH_TAC);;

let vINT_DIV_LT_EQ = try Cache.lookup_thm "INT_DIV_LT_EQ" with _ ->  prove
 ((parse_term "!a b c. &0 < a ==> (b div a < c <=> b < a * c)"),
  vGEN_REWRITE_TAC vI [vFORALL_INT_CASES] ---->
  vREWRITE_TAC[vINT_ARITH (parse_term "~(&0:int < -- &n)")] ----> vX_GEN_TAC (parse_term "n:num") ---->
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM; vINT_OF_NUM_LT] ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC vI [vFORALL_INT_CASES] ---->
  vMATCH_MP_TAC(vTAUT (parse_term "p /\\ (p ==> q) ==> p /\\ q")) ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vINT_OF_NUM_DIV; vFORALL_INT_CASES] ---->
    vREWRITE_TAC[vINT_MUL_RNEG; vINT_OF_NUM_MUL] ---->
    vREWRITE_TAC[vINT_OF_NUM_LT; vINT_ARITH (parse_term "~(&m:int < -- &n)")] ---->
    vASM_SIMP_TAC[vRDIV_LT_EQ; vLE_1];
    vDISCH_TAC] ---->
  vX_GEN_TAC (parse_term "m:num") ---->
  vREWRITE_TAC[vINT_DIV_LNEG] ----> vCOND_CASES_TAC ++-->
   [vMP_TAC(vSPECL [(parse_term "&m:int"); (parse_term "&n:int")] vINT_DIVISION) ---->
    vMAP_EVERY vABBREV_TAC [(parse_term "q = &m div &n"); (parse_term "r = &m rem &n")] ---->
    vASM_SIMP_TAC[vINT_OF_NUM_EQ; vLE_1] ----> vDISCH_TAC ---->
    vREWRITE_TAC[vINT_ARITH (parse_term "--(q * &n + &0:int) = &n * --q")] ---->
    vASM_SIMP_TAC[vINT_LT_LMUL_EQ; vINT_OF_NUM_LT];
    vALL_TAC] ---->
  vASM_SIMP_TAC[vINT_SGN; vINT_OF_NUM_LT; vLE_1] ---->
  vREWRITE_TAC[vINT_LT_SUB_RADD; vGSYM vINT_LE_DISCRETE] ---->
  vASM_REWRITE_TAC[vINT_ARITH (parse_term "--a:int <= b <=> ~(a < --b)")] ---->
  vREWRITE_TAC[vINT_ARITH
   (parse_term "(~(m:int < n * --c) <=> --m < n * c) <=> ~(m = n * --c)")] ---->
  vASM_MESON_TAC[vINT_REM_MUL]);;

let vINT_LE_DIV_EQ = try Cache.lookup_thm "INT_LE_DIV_EQ" with _ ->  prove
 ((parse_term "!a b c. &0 < a ==> (c <= b div a <=> a * c <= b)"),
  vSIMP_TAC[vGSYM vINT_NOT_LT; vINT_DIV_LT_EQ]);;

let vINT_DIV_LE_EQ = try Cache.lookup_thm "INT_DIV_LE_EQ" with _ ->  prove
 ((parse_term "!a b c. &0 < a ==> (b div a <= c <=> b < a * (c + &1))"),
  vSIMP_TAC[vINT_LE_DISCRETE; vINT_DIV_LT_EQ]);;

let vINT_LT_DIV_EQ = try Cache.lookup_thm "INT_LT_DIV_EQ" with _ ->  prove
 ((parse_term "!a b c. &0 < a ==> (c < b div a <=> a * (c + &1) <= b)"),
  vSIMP_TAC[vGSYM vINT_NOT_LE; vINT_DIV_LE_EQ]);;

let vINT_DIV_LE = try Cache.lookup_thm "INT_DIV_LE" with _ ->  prove
 ((parse_term "!m n. abs(m div n) <= abs m"),
  vGEN_REWRITE_TAC vBINDER_CONV [vFORALL_INT_CASES] ---->
  vREWRITE_TAC[vINT_DIV_RNEG; vINT_ABS_NEG] ---->
  vGEN_REWRITE_TAC vI [vSWAP_FORALL_THM] ----> vX_GEN_TAC (parse_term "n:num") ---->
  vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vINT_DIV_0; vINT_ABS_NUM; vINT_ABS_POS] ---->
  vREWRITE_TAC[vINT_ARITH (parse_term "abs(x:int) <= a <=> --a <= x /\\ x <= a")] ---->
  vASM_SIMP_TAC[vINT_LE_DIV_EQ; vINT_DIV_LE_EQ; vINT_OF_NUM_LT; vLE_1] ---->
  vX_GEN_TAC (parse_term "m:int") ----> vMATCH_MP_TAC(vINT_ARITH
   (parse_term "&0:int < n /\\ abs m * &1 <= abs m * n\n    ==> n * --abs m <= m /\\ m < n * (abs m + &1)")) ---->
  vASM_SIMP_TAC[vINT_OF_NUM_LT; vLE_1] ---->
  vMATCH_MP_TAC vINT_LE_LMUL ----> vREWRITE_TAC[vINT_ABS_POS] ---->
  vASM_SIMP_TAC[vINT_OF_NUM_LE; vLE_1]);;

let vINT_DIV_DIV,vINT_REM_MUL_REM = (vCONJ_PAIR -| prove)
 ((parse_term "(!m n p. &0 <= n ==> (m div n) div p = m div (n * p)) /\\\n   (!m n p. &0 <= n ==> m rem (n * p) = n * (m div n) rem p + m rem n)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n:int = &0") ---->
  vASM_REWRITE_TAC[vINT_MUL_LZERO; vINT_DIV_0; vINT_REM_0;
                  vINT_DIV_ZERO; vINT_ADD_LID; vINT_LE_LT] ---->
  vASM_CASES_TAC (parse_term "&0:int < n") ----> vASM_REWRITE_TAC[] ---->
  vASM_CASES_TAC (parse_term "p:int = &0") ---->
  vASM_REWRITE_TAC[vINT_MUL_RZERO; vINT_DIV_0; vINT_REM_0] ++-->
   [vREWRITE_TAC[vINT_REM_DIV] ----> vINT_ARITH_TAC; vALL_TAC] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vEQ_SYM_EQ] ---->
  vMATCH_MP_TAC vINT_DIVMOD_UNIQ ----> vREPEAT vCONJ_TAC ++-->
   [vREWRITE_TAC[vINT_REM_DIV] ----> vINT_ARITH_TAC;
    vASM_SIMP_TAC[vINT_LE_ADD; vINT_LE_MUL; vINT_LT_IMP_LE; vINT_DIVISION];
    vTRANS_TAC vINT_LTE_TRANS (parse_term "n * (abs p - &1) + n:int") ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vINT_LET_ADD2 ----> vASM_SIMP_TAC[vINT_LT_REM] ---->
      vASM_SIMP_TAC[vINT_LE_LMUL_EQ; vINT_LE_SUB_LADD; vGSYM vINT_LT_DISCRETE] ---->
      vASM_SIMP_TAC[vINT_DIVISION];
      vREWRITE_TAC[vINT_ARITH (parse_term "n * (p - &1) + n:int = n * p"); vINT_ABS_MUL] ---->
      vMATCH_MP_TAC vINT_LE_RMUL ----> vINT_ARITH_TAC]]);;

let vINT_DIV_EQ_0 = try Cache.lookup_thm "INT_DIV_EQ_0" with _ ->  prove
 ((parse_term "!m n. m div n = &0 <=> n = &0 \\/ &0 <= m /\\ m < abs n"),
  vGEN_REWRITE_TAC vBINDER_CONV [vFORALL_INT_CASES] ---->
  vREWRITE_TAC[vINT_DIV_RNEG; vINT_NEG_EQ_0; vINT_ABS_NEG] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "m:int"); (parse_term "n:num")] ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vINT_DIV_0; vINT_OF_NUM_EQ; vINT_ABS_NUM] ---->
  vASM_SIMP_TAC[vGSYM vINT_LE_ANTISYM; vINT_DIV_LE_EQ; vINT_LE_DIV_EQ; vCONJ_SYM;
               vINT_OF_NUM_LT; vLE_1; vINT_ADD_LID; vINT_MUL_RZERO; vINT_MUL_RID]);;

let vINT_REM_EQ_SELF = try Cache.lookup_thm "INT_REM_EQ_SELF" with _ ->  prove
 ((parse_term "!m n. m rem n = m <=> n = &0 \\/ &0 <= m /\\ m < abs n"),
  vREWRITE_TAC[vINT_REM_DIV; vINT_ARITH (parse_term "m - x:int = m <=> x = &0")] ---->
  vREWRITE_TAC[vINT_DIV_EQ_0; vINT_ENTIRE] ----> vINT_ARITH_TAC);;

let vINT_DIV_REM = try Cache.lookup_thm "INT_DIV_REM" with _ ->  prove
 ((parse_term "!m n p. &0 <= n ==> (m div n) rem p = (m rem (n * p)) div n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n:int = &0") ---->
  vASM_REWRITE_TAC[vINT_LE_LT; vINT_DIV_0; vINT_REM_ZERO] ----> vDISCH_TAC ---->
  vASM_SIMP_TAC[vINT_REM_MUL_REM; vINT_LT_IMP_LE] ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vINT_DIV_UNIQ ---->
  vEXISTS_TAC (parse_term "m rem n") ----> vASM_SIMP_TAC[vINT_DIVISION] ---->
  vREWRITE_TAC[vINT_ADD_AC; vINT_MUL_AC]);;

let vINT_LE_DIV = try Cache.lookup_thm "INT_LE_DIV" with _ ->  prove
 ((parse_term "!m n. &0 <= m /\\ &0 <= n ==> &0 <= m div n"),
  vREWRITE_TAC[vGSYM vINT_FORALL_POS; vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vREWRITE_TAC[vINT_OF_NUM_DIV; vINT_POS]);;

let vINT_LT_DIV = try Cache.lookup_thm "INT_LT_DIV" with _ ->  prove
 ((parse_term "!m n. &0 < n /\\ n <= m ==> &0 < m div n"),
  vREPEAT vSTRIP_TAC ---->
  vREWRITE_TAC[vINT_ARITH (parse_term "&0:int < x <=> &0 <= x /\\ ~(x = &0)")] ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vINT_LE_DIV ----> vASM_INT_ARITH_TAC;
    vREWRITE_TAC[vINT_DIV_EQ_0] ----> vASM_INT_ARITH_TAC]);;

let vINT_REM_MUL_ADD = try Cache.lookup_thm "INT_REM_MUL_ADD" with _ ->  prove
 ((parse_term "(!m n p. (m * n + p) rem n = p rem n) /\\\n   (!m n p. (n * m + p) rem n = p rem n) /\\\n   (!m n p. (p + m * n) rem n = p rem n) /\\\n   (!m n p. (p + n * m) rem n = p rem n)"),
  vONCE_REWRITE_TAC[vGSYM vINT_ADD_REM] ---->
  vREWRITE_TAC[vINT_REM_MUL; vINT_ADD_LID; vINT_ADD_RID; vINT_REM_REM]);;

let vINT_DIV_MUL_ADD = try Cache.lookup_thm "INT_DIV_MUL_ADD" with _ ->  prove
 ((parse_term "(!m n p. ~(n = &0) ==> (m * n + p) div n = m + p div n) /\\\n   (!m n p. ~(n = &0) ==> (n * m + p) div n = m + p div n) /\\\n   (!m n p. ~(n = &0) ==> (p + m * n) div n = p div n + m) /\\\n   (!m n p. ~(n = &0) ==> (p + n * m) div n = p div n + m)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vINT_DIV_UNIQ ---->
  vEXISTS_TAC (parse_term "p rem n") ---->
  vMP_TAC(vSPECL [(parse_term "p:int"); (parse_term "n:int")] vINT_DIVISION) ---->
  vASM_REWRITE_TAC[] ----> vASM_INT_ARITH_TAC);;

let vINT_CONG_DIV2 = try Cache.lookup_thm "INT_CONG_DIV2" with _ ->  prove
 ((parse_term "!a b m n.\n      (a == b) (mod (m * n)) ==> (a div m == b div m) (mod n)"),
  vGEN_REWRITE_TAC (funpow 2 vBINDER_CONV) [vFORALL_INT_CASES] ---->
  vREWRITE_TAC[vINT_DIV_RNEG; vINT_MUL_LNEG;
     vINTEGER_RULE (parse_term "(--a:int == --b) (mod n) <=> (a == b) (mod n)");
     vINTEGER_RULE (parse_term "(a:int == b) (mod(--n)) <=> (a == b) (mod n)")] ---->
  vSIMP_TAC[vGSYM vINT_REM_EQ; vINT_DIV_REM; vINT_POS]);;

let vINT_REM_2_CASES = try Cache.lookup_thm "INT_REM_2_CASES" with _ ->  prove
 ((parse_term "!n. n rem &2 = &0 \\/ n rem &2 = &1"),
  vGEN_TAC ----> vMP_TAC(vSPECL [(parse_term "n:int"); (parse_term "&2:int")] vINT_DIVISION) ---->
  vINT_ARITH_TAC);;

let vNOT_INT_REM_2 = try Cache.lookup_thm "NOT_INT_REM_2" with _ ->  prove
 ((parse_term "(!n. ~(n rem &2 = &0) <=> n rem &2 = &1) /\\\n   (!n. ~(n rem &2 = &1) <=> n rem &2 = &0)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vMP_TAC vINT_REM_2_CASES ---->
  vMATCH_MP_TAC vMONO_FORALL ----> vINT_ARITH_TAC);;

let vINT_REM_2_DIVIDES = try Cache.lookup_thm "INT_REM_2_DIVIDES" with _ ->  prove
 ((parse_term "(!n. n rem &2 = &0 <=> &2 divides n) /\\\n   (!n. n rem &2 = &1 <=> ~(&2 divides n))"),
  vREWRITE_TAC[vGSYM(vCONJUNCT1 vNOT_INT_REM_2)] ---->
  vREWRITE_TAC[vINT_REM_EQ_0]);;

let vINT_DIVIDES_DIV_SELF = try Cache.lookup_thm "INT_DIVIDES_DIV_SELF" with _ ->  prove
 ((parse_term "!n d. d divides n ==> n div d divides n"),
  vMESON_TAC[vINT_MUL_DIV_EQ; int_divides]);;

let vINT_DIV_BY_DIV = try Cache.lookup_thm "INT_DIV_BY_DIV" with _ ->  prove
 ((parse_term "!m n:int. ~(n = &0) /\\ m divides n ==> n div (n div m) = m"),
  vMESON_TAC[vINT_DIVIDES_DIV_SELF; vINT_MUL_DIV_EQ; vINT_RING
    (parse_term "a * x:int = n /\\ a * y = n /\\ ~(n = &0) ==> x = y")]);;

let vINT_DIVIDES_DIV_DIVIDES = try Cache.lookup_thm "INT_DIVIDES_DIV_DIVIDES" with _ ->  prove
 ((parse_term "!n d e. d divides n /\\ (n = &0 ==> e = &0)\n           ==> (n div d divides e <=> n divides d * e)"),
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV) [vGSYM(vCONJUNCT1 vINT_MUL_DIV_EQ)] ---->
  vASM_CASES_TAC (parse_term "e:int = &0") ----> vASM_REWRITE_TAC[] ----> vINTEGER_TAC);;

let vINT_DIVIDES_DIVIDES_DIV = try Cache.lookup_thm "INT_DIVIDES_DIVIDES_DIV" with _ ->  prove
 ((parse_term "!n d e. d divides n ==> (e divides (n div d) <=> (d * e) divides n)"),
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM(vCONJUNCT1 vINT_MUL_DIV_EQ)] ---->
  vASM_CASES_TAC (parse_term "d:int = &0") ----> vASM_REWRITE_TAC[vINT_DIV_ZERO; vINT_DIV_0] ---->
  vINTEGER_TAC);;

let vINT_DIVIDES_DIVIDES_DIV_EQ = try Cache.lookup_thm "INT_DIVIDES_DIVIDES_DIV_EQ" with _ ->  prove
 ((parse_term "!n d e. d divides n /\\ e divides (n div d) <=> (d * e) divides n"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC(vTAUT
   (parse_term "(r ==> p) /\\ (p ==> (q <=> r)) ==> (p /\\ q <=> r)")) ---->
  vREWRITE_TAC[vINT_DIVIDES_DIVIDES_DIV] ----> vINTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Arithmetic operations also on div and rem, hence the whole lot.           *)
(* ------------------------------------------------------------------------- *)

let vINT_DIV_CONV,vINT_REM_CONV =
  let pth = prove
   ((parse_term "q * n + r = m ==> &0 <= r ==> r < abs n ==> m div n = q /\\ m rem n = r"),
    vMESON_TAC[vINT_DIVMOD_UNIQ])
  and m = (parse_term "m:int") and n = (parse_term "n:int") and q = (parse_term "q:int") and r = (parse_term "r:int")
  and dtm = (parse_term "(div)") and mtm = (parse_term "(rem)") in
  let emod_num x y =
    let r = mod_num x y in
    if r </ Int 0 then r +/ abs_num y else r in
  let equo_num x y = quo_num (x -/ emod_num x y) y in
  let vINT_DIVMOD_CONV x y =
    let k = equo_num x y
    and l = emod_num x y in
    let th0 = vINST [mk_intconst x,m; mk_intconst y,n;
                    mk_intconst k,q; mk_intconst l,r] pth in
    let tm0 = lhand(lhand(concl th0)) in
    let th1 = (vLAND_CONV vINT_MUL_CONV +---> vINT_ADD_CONV) tm0 in
    let th2 = vMP th0 th1 in
    let tm2 = lhand(concl th2) in
    let th3 = vMP th2 (vEQT_ELIM(vINT_LE_CONV tm2)) in
    let tm3 = lhand(concl th3) in
    vMP th3 (vEQT_ELIM((vRAND_CONV vINT_ABS_CONV +---> vINT_LT_CONV) tm3)) in
  (fun tm -> try let l,r = dest_binop dtm tm in
                 vCONJUNCT1(vINT_DIVMOD_CONV (dest_intconst l) (dest_intconst r))
             with Failure _ -> failwith "INT_DIV_CONV"),
  (fun tm -> try let l,r = dest_binop mtm tm in
                 vCONJUNCT2(vINT_DIVMOD_CONV (dest_intconst l) (dest_intconst r))
             with Failure _ -> failwith "INT_MOD_CONV");;

let vINT_RED_CONV =
  let gconv_net = itlist (uncurry net_of_conv)
    [(parse_term "x <= y"),vINT_LE_CONV;
     (parse_term "x < y"),vINT_LT_CONV;
     (parse_term "x >= y"),vINT_GE_CONV;
     (parse_term "x > y"),vINT_GT_CONV;
     (parse_term "x:int = y"),vINT_EQ_CONV;
     (parse_term "--x"),vCHANGED_CONV vINT_NEG_CONV;
     (parse_term "int_sgn(x)"),vINT_SGN_CONV;
     (parse_term "abs(x)"),vINT_ABS_CONV;
     (parse_term "x + y"),vINT_ADD_CONV;
     (parse_term "x - y"),vINT_SUB_CONV;
     (parse_term "x * y"),vINT_MUL_CONV;
     (parse_term "x div y"),vINT_DIV_CONV;
     (parse_term "x rem y"),vINT_REM_CONV;
     (parse_term "x pow n"),vINT_POW_CONV;
     (parse_term "max x y"),vINT_MAX_CONV;
     (parse_term "min x y"),vINT_MIN_CONV]
    (basic_net()) in
  vREWRITES_CONV gconv_net;;

let vINT_REDUCE_CONV = vDEPTH_CONV vINT_RED_CONV;;

(* ------------------------------------------------------------------------- *)
(* Integer analogs of the usual even/odd combining theorems EVEN_ADD etc.    *)
(* ------------------------------------------------------------------------- *)

let vINT_2_DIVIDES_ADD = try Cache.lookup_thm "INT_2_DIVIDES_ADD" with _ ->  prove
 ((parse_term "!m n:int. &2 divides (m + n) <=> (&2 divides m <=> &2 divides n)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vINT_REM_2_DIVIDES] ---->
  vONCE_REWRITE_TAC[vGSYM vINT_ADD_REM] ---->
  vDISJ_CASES_TAC(vSPEC (parse_term "m:int") vINT_REM_2_CASES) ---->
  vDISJ_CASES_TAC(vSPEC (parse_term "n:int") vINT_REM_2_CASES) ---->
  vASM_REWRITE_TAC[] ----> vCONV_TAC vINT_REDUCE_CONV);;

let vINT_2_DIVIDES_SUB = try Cache.lookup_thm "INT_2_DIVIDES_SUB" with _ ->  prove
 ((parse_term "!m n:int. &2 divides (m - n) <=> (&2 divides m <=> &2 divides n)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vINT_REM_2_DIVIDES] ---->
  vONCE_REWRITE_TAC[vGSYM vINT_SUB_REM] ---->
  vDISJ_CASES_TAC(vSPEC (parse_term "m:int") vINT_REM_2_CASES) ---->
  vDISJ_CASES_TAC(vSPEC (parse_term "n:int") vINT_REM_2_CASES) ---->
  vASM_REWRITE_TAC[] ----> vCONV_TAC vINT_REDUCE_CONV);;

let vINT_2_DIVIDES_MUL = try Cache.lookup_thm "INT_2_DIVIDES_MUL" with _ ->  prove
 ((parse_term "!m n:int. &2 divides (m * n) <=> &2 divides m \\/ &2 divides n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vINT_REM_2_DIVIDES] ---->
  vONCE_REWRITE_TAC[vGSYM vINT_MUL_REM] ---->
  vDISJ_CASES_TAC(vSPEC (parse_term "m:int") vINT_REM_2_CASES) ---->
  vDISJ_CASES_TAC(vSPEC (parse_term "n:int") vINT_REM_2_CASES) ---->
  vASM_REWRITE_TAC[] ----> vCONV_TAC vINT_REDUCE_CONV);;

let vINT_2_DIVIDES_POW = try Cache.lookup_thm "INT_2_DIVIDES_POW" with _ ->  prove
 ((parse_term "!n k. &2 divides (n pow k) <=> &2 divides n /\\ ~(k = 0)"),
  vGEN_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[vINT_POW] ++-->
   [vREWRITE_TAC[vGSYM(vCONJUNCT2 vINT_REM_2_DIVIDES)] ---->
    vCONV_TAC vINT_REDUCE_CONV;
    vASM_REWRITE_TAC[vINT_2_DIVIDES_MUL; vNOT_SUC] ---->
    vCONV_TAC vTAUT]);;

(* ------------------------------------------------------------------------- *)
(* Pushing and pulling to combine nested rem terms into a single rem.        *)
(* ------------------------------------------------------------------------- *)

let vINT_REM_DOWN_CONV =
  let addmul_conv = vGEN_REWRITE_CONV vI
    [vGSYM vINT_NEG_REM; vGSYM vINT_ADD_REM; vGSYM vINT_SUB_REM;
     vGSYM vINT_MUL_REM; vGSYM vINT_POW_REM]
  and mod_conv = vGEN_REWRITE_CONV vI [vINT_REM_REM] in
  let rec downconv tm =
   ((addmul_conv +---> vLAND_CONV downconv) ||-->
    (mod_conv +---> downconv) ||-->
    vSUB_CONV downconv) tm
  and upconv =
    vGEN_REWRITE_CONV vDEPTH_CONV
     [vINT_NEG_REM; vINT_ADD_REM; vINT_SUB_REM; vINT_MUL_REM;
      vINT_POW_REM; vINT_REM_REM] in
  downconv +---> upconv;;

(* ------------------------------------------------------------------------- *)
(* Existence of integer gcd, and the Bezout identity.                        *)
(* ------------------------------------------------------------------------- *)

let vWF_INT_MEASURE = try Cache.lookup_thm "WF_INT_MEASURE" with _ ->  prove
 ((parse_term "!P m. (!x. &0 <= m(x)) /\\ (!x. (!y. m(y) < m(x) ==> P(y)) ==> P(x))\n         ==> !x:A. P(x)"),
  vREPEAT vSTRIP_TAC ----> vSUBGOAL_THEN (parse_term "!n x:A. m(x) = &n ==> P(x)") vMP_TAC ++-->
   [vMATCH_MP_TAC num_WF; vALL_TAC] ---->
  vREWRITE_TAC[vGSYM vINT_OF_NUM_LT; vINT_FORALL_POS] ----> vASM_MESON_TAC[]);;

let vWF_INT_MEASURE_2 = try Cache.lookup_thm "WF_INT_MEASURE_2" with _ ->  prove
 ((parse_term "!P m. (!x y. &0 <= m x y) /\\\n         (!x y. (!x' y'. m x' y' < m x y ==> P x' y') ==> P x y)\n         ==> !x:A y:B. P x y"),
  vREWRITE_TAC[vFORALL_UNCURRY; vGSYM vFORALL_PAIR_THM; vWF_INT_MEASURE]);;

let vINT_GCD_EXISTS = try Cache.lookup_thm "INT_GCD_EXISTS" with _ ->  prove
 ((parse_term "!a b. ?d. d divides a /\\ d divides b /\\ ?x y. d = a * x + b * y"),
  let vINT_GCD_EXISTS_CASES = vINT_ARITH
   (parse_term "(a = &0 \\/ b = &0) \\/\n    abs(a - b) + abs b < abs a + abs b \\/ abs(a + b) + abs b < abs a + abs b \\/\n    abs a + abs(b - a) < abs a + abs b \\/ abs a + abs(b + a) < abs a + abs b") in
  vMATCH_MP_TAC vWF_INT_MEASURE_2 ----> vEXISTS_TAC (parse_term "\\x y. abs(x) + abs(y)") ---->
  vREWRITE_TAC[] ----> vREPEAT vSTRIP_TAC ++--> [vINT_ARITH_TAC; vALL_TAC] ---->
  vDISJ_CASES_THEN vMP_TAC vINT_GCD_EXISTS_CASES ++-->
   [vSTRIP_TAC ----> vASM_REWRITE_TAC[vINTEGER_RULE (parse_term "d divides &0")] ---->
    vREWRITE_TAC[vINT_MUL_LZERO; vINT_ADD_LID; vINT_ADD_RID] ---->
    vMESON_TAC[vINTEGER_RULE (parse_term "d divides d"); vINT_MUL_RID];
    vDISCH_THEN(vREPEAT_TCL vDISJ_CASES_THEN (vANTE_RES_THEN vMP_TAC)) ---->
    vMATCH_MP_TAC vMONO_EXISTS ----> vINTEGER_TAC]);;

let vINT_GCD_EXISTS_POS = try Cache.lookup_thm "INT_GCD_EXISTS_POS" with _ ->  prove
 ((parse_term "!a b. ?d. &0 <= d /\\ d divides a /\\ d divides b /\\ ?x y. d = a * x + b * y"),
  vREPEAT vGEN_TAC ---->
  vX_CHOOSE_TAC (parse_term "d:int") (vSPECL [(parse_term "a:int"); (parse_term "b:int")] vINT_GCD_EXISTS) ---->
  vDISJ_CASES_TAC(vSPEC (parse_term "d:int") vINT_LE_NEGTOTAL) ---->
  vASM_MESON_TAC[vINTEGER_RULE (parse_term "(--d) divides x <=> d divides x");
                vINT_ARITH (parse_term "a * --x + b * --y = --(a * x + b * y)")]);;

(* ------------------------------------------------------------------------- *)
(* Hence define (positive) integer gcd and lcm operations, with a few        *)
(* basic properties of the latter; most analogous gcd ones get automated.    *)
(* ------------------------------------------------------------------------- *)

overload_interface("gcd",(parse_term "int_gcd:int#int->int"));;
overload_interface("lcm",(parse_term "int_lcm:int#int->int"));;

let int_gcd = new_specification ["int_gcd"]
 (vREWRITE_RULE[vEXISTS_UNCURRY; vSKOLEM_THM] vINT_GCD_EXISTS_POS);;

let int_lcm = new_definition
 (parse_term "int_lcm(m,n) = if m * n = &0 then &0 else abs(m * n) div gcd(m,n)");;

let vINT_DIVIDES_LABS = try Cache.lookup_thm "INT_DIVIDES_LABS" with _ ->  prove
 ((parse_term "!d n. abs(d) divides n <=> d divides n"),
  vREPEAT vGEN_TAC ----> vSIMP_TAC[vINT_ABS] ----> vCOND_CASES_TAC ----> vINTEGER_TAC);;

let vINT_DIVIDES_RABS = try Cache.lookup_thm "INT_DIVIDES_RABS" with _ ->  prove
 ((parse_term "!d n. d divides (abs n) <=> d divides n"),
  vREPEAT vGEN_TAC ----> vSIMP_TAC[vINT_ABS] ----> vCOND_CASES_TAC ----> vINTEGER_TAC);;

let vINT_DIVIDES_ABS = try Cache.lookup_thm "INT_DIVIDES_ABS" with _ ->  prove
 ((parse_term "(!d n. abs(d) divides n <=> d divides n) /\\\n   (!d n. d divides (abs n) <=> d divides n)"),
  vREWRITE_TAC[vINT_DIVIDES_LABS; vINT_DIVIDES_RABS]);;

let vINT_LCM_POS = try Cache.lookup_thm "INT_LCM_POS" with _ ->  prove
 ((parse_term "!m n. &0 <= lcm(m,n)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[int_lcm] ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vINT_POS; vINT_ABS_POS; vINT_LE_DIV; int_gcd]);;

let vINT_MUL_GCD_LCM = try Cache.lookup_thm "INT_MUL_GCD_LCM" with _ ->  prove
 ((parse_term "!m n:int. gcd(m,n) * lcm(m,n) = abs(m * n)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[int_lcm] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vINT_MUL_RZERO; vINT_ABS_NUM] ---->
  vREWRITE_TAC[vINT_MUL_DIV_EQ] ----> vREWRITE_TAC[vINT_ABS] ---->
  vASM_MESON_TAC[int_gcd; vINTEGER_RULE
   (parse_term "d divides m ==> d divides (m * n:int) /\\ d divides --(m * n)")]);;

let vINT_MUL_LCM_GCD = try Cache.lookup_thm "INT_MUL_LCM_GCD" with _ ->  prove
 ((parse_term "!m n:int. lcm(m,n) * gcd(m,n) = abs(m * n)"),
  vMESON_TAC[vINT_MUL_SYM; vINT_MUL_GCD_LCM]);;

let vINT_DIVIDES_LCM_GCD = try Cache.lookup_thm "INT_DIVIDES_LCM_GCD" with _ ->  prove
 ((parse_term "!m n d:int. d divides lcm(m,n) <=> d * gcd(m,n) divides m * n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[int_lcm] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ++--> [vINTEGER_TAC; vALL_TAC] ---->
  vW(vMP_TAC -| vPART_MATCH (lhand -| rand)
    vINT_DIVIDES_DIVIDES_DIV -| lhand -| snd) ---->
  vASM_REWRITE_TAC[vINT_ABS_ZERO; vINT_DIVIDES_ABS] ----> vANTS_TAC ++-->
   [vMESON_TAC[int_gcd; vINTEGER_RULE (parse_term "d divides m ==> d divides (m * n:int)")];
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vINT_MUL_SYM]]);;

let vINT_LCM_DIVIDES = try Cache.lookup_thm "INT_LCM_DIVIDES" with _ ->  prove
 ((parse_term "!m n d:int. lcm(m,n) divides d <=> m divides d /\\ n divides d"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[int_lcm] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ++--> [vINTEGER_TAC; vALL_TAC] ---->
  vW(vMP_TAC -| vPART_MATCH (lhand -| rand)
    vINT_DIVIDES_DIV_DIVIDES -| lhand -| snd) ---->
  vASM_REWRITE_TAC[vINT_ABS_ZERO; vINT_DIVIDES_ABS] ----> vANTS_TAC ++-->
   [vMESON_TAC[int_gcd; vINTEGER_RULE (parse_term "d divides m ==> d divides (m * n:int)")];
    vDISCH_THEN vSUBST1_TAC] ---->
  vMP_TAC(vSPECL [(parse_term "m:int"); (parse_term "n:int")] int_gcd) ----> vINTEGER_TAC);;

let vINT_LCM = try Cache.lookup_thm "INT_LCM" with _ ->  prove
 ((parse_term "!m n. m divides lcm(m,n) /\\\n         n divides lcm(m,n) /\\\n         (!d. m divides d /\\ n divides d ==> lcm(m,n) divides d)"),
  vREWRITE_TAC[vINT_LCM_DIVIDES; vINT_DIVIDES_LCM_GCD] ---->
  vREPEAT vGEN_TAC ----> vMP_TAC(vSPECL [(parse_term "m:int"); (parse_term "n:int")] int_gcd) ---->
  vINTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Add their elimination to INTEGER_TAC (better for gcd at the moment).      *)
(* ------------------------------------------------------------------------- *)

let vINTEGER_TAC =
  let vGCD_ELIM_TAC =
    let gcd_tm = (parse_term "gcd:int#int->int") in
    let dest_gcd tm =
      let l,r = dest_comb tm in
      if l = gcd_tm then dest_pair r else failwith "dest_gcd" in
    vREPEAT vGEN_TAC ---->
    vW(fun (_asl,w) ->
          let gts = find_terms (can dest_gcd) w in
          let ths = map
           (fun tm -> let a,b = dest_gcd tm in vSPECL [a;b] int_gcd) gts in
          vMAP_EVERY vMP_TAC ths ---->
          vMAP_EVERY vSPEC_TAC (zip gts (map (genvar -| type_of) gts))) in
  let pth = prove
   ((parse_term "!d a b:int. d divides gcd(a,b) <=> d divides a /\\ d divides b"),
    vGCD_ELIM_TAC ----> vINTEGER_TAC) in
  vGEN_REWRITE_TAC vTOP_DEPTH_CONV
   [pth; vINT_DIVIDES_ABS; vINT_DIVIDES_LCM_GCD; vINT_LCM_DIVIDES] ---->
  vREPEAT(vGEN_TAC |---> vCONJ_TAC) ----> vGCD_ELIM_TAC ----> vINTEGER_TAC;;

let vINTEGER_RULE tm = prove(tm,vINTEGER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Mapping from nonnegative integers back to natural numbers.                *)
(* ------------------------------------------------------------------------- *)

let num_of_int = new_definition
  (parse_term "num_of_int x = @n. &n = x");;

let vNUM_OF_INT_OF_NUM = try Cache.lookup_thm "NUM_OF_INT_OF_NUM" with _ ->  prove
 ((parse_term "!n. num_of_int(&n) = n"),
  vREWRITE_TAC[num_of_int; vINT_OF_NUM_EQ; vSELECT_UNIQUE]);;

let vINT_OF_NUM_OF_INT = try Cache.lookup_thm "INT_OF_NUM_OF_INT" with _ ->  prove
 ((parse_term "!x. &0 <= x ==> &(num_of_int x) = x"),
  vREWRITE_TAC[vGSYM vINT_FORALL_POS; num_of_int] ---->
  vGEN_TAC ----> vCONV_TAC vSELECT_CONV ----> vMESON_TAC[]);;

let vNUM_OF_INT = try Cache.lookup_thm "NUM_OF_INT" with _ ->  prove
 ((parse_term "!x. &0 <= x <=> (&(num_of_int x) = x)"),
  vMESON_TAC[vINT_OF_NUM_OF_INT; vINT_POS]);;

let vNUM_OF_INT_ADD = try Cache.lookup_thm "NUM_OF_INT_ADD" with _ ->  prove
 ((parse_term "!x y. &0 <= x /\\ &0 <= y\n         ==> num_of_int(x + y) = num_of_int x + num_of_int y"),
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM; vIMP_CONJ] ---->
  vREWRITE_TAC[vGSYM vINT_FORALL_POS; vINT_OF_NUM_ADD; vNUM_OF_INT_OF_NUM]);;

let vNUM_OF_INT_MUL = try Cache.lookup_thm "NUM_OF_INT_MUL" with _ ->  prove
 ((parse_term "!x y. &0 <= x /\\ &0 <= y\n         ==> num_of_int(x * y) = num_of_int x * num_of_int y"),
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM; vIMP_CONJ] ---->
  vREWRITE_TAC[vGSYM vINT_FORALL_POS; vINT_OF_NUM_MUL; vNUM_OF_INT_OF_NUM]);;

let vNUM_OF_INT_POW = try Cache.lookup_thm "NUM_OF_INT_POW" with _ ->  prove
 ((parse_term "!x n. &0 <= x ==> num_of_int(x pow n) = num_of_int x EXP n"),
  vGEN_REWRITE_TAC vI [vSWAP_FORALL_THM] ---->
  vREWRITE_TAC[vGSYM vINT_FORALL_POS; vINT_OF_NUM_POW; vNUM_OF_INT_OF_NUM]);;

(* ------------------------------------------------------------------------- *)
(* Now define similar notions over the natural numbers.                      *)
(* ------------------------------------------------------------------------- *)

overload_interface("divides",(parse_term "num_divides:num->num->bool"));;
overload_interface ("mod",(parse_term "num_mod:num->num->num->bool"));;
overload_interface("coprime",(parse_term "num_coprime:num#num->bool"));;
overload_interface("gcd",(parse_term "num_gcd:num#num->num"));;
overload_interface("lcm",(parse_term "num_lcm:num#num->num"));;

let num_divides = new_definition
 (parse_term "a divides b <=> &a divides &b");;

let num_mod = new_definition
  (parse_term "(mod n) x y <=> (mod &n) (&x) (&y)");;

let num_congruent = try Cache.lookup_thm "num_congruent" with _ ->  prove
 ((parse_term "!x y n. (x == y) (mod n) <=> (&x == &y) (mod &n)"),
  vREWRITE_TAC[cong; num_mod]);;

let num_coprime = new_definition
 (parse_term "coprime(a,b) <=> coprime(&a,&b)");;

let num_gcd = new_definition
 (parse_term "gcd(a,b) = num_of_int(gcd(&a,&b))");;

let num_lcm = new_definition
 (parse_term "lcm(a,b) = num_of_int(lcm(&a,&b))");;

(* ------------------------------------------------------------------------- *)
(* Map an assertion over N to an integer equivalent.                         *)
(* To make this work nicely, all variables of type num should be quantified. *)
(* ------------------------------------------------------------------------- *)

let vNUM_TO_INT_CONV =
  let pth_relativize = prove
   ((parse_term "((!n. P(&n)) <=> (!i. ~(&0 <= i) \\/ P i)) /\\\n     ((?n. P(&n)) <=> (?i. &0 <= i /\\ P i))"),
    vREWRITE_TAC[vINT_EXISTS_POS; vINT_FORALL_POS] ----> vMESON_TAC[]) in
  let relation_conv = (vGEN_REWRITE_CONV vTOP_SWEEP_CONV -| map vGSYM)
   [vINT_OF_NUM_EQ; vINT_OF_NUM_LE; vINT_OF_NUM_LT; vINT_OF_NUM_GE; vINT_OF_NUM_GT;
    vINT_OF_NUM_SUC; vINT_OF_NUM_ADD; vINT_OF_NUM_MUL; vINT_OF_NUM_POW]
  and quantifier_conv = vGEN_REWRITE_CONV vDEPTH_CONV [pth_relativize] in
  vNUM_SIMPLIFY_CONV +---> relation_conv +---> quantifier_conv;;

(* ------------------------------------------------------------------------- *)
(* Linear decision procedure for the naturals at last!                       *)
(* ------------------------------------------------------------------------- *)

let vARITH_RULE =
  let init_conv =
    vNUM_SIMPLIFY_CONV +--->
    vGEN_REWRITE_CONV vDEPTH_CONV [vADD1] +--->
    vPROP_ATOM_CONV (vBINOP_CONV vNUM_NORMALIZE_CONV) +--->
    vPRENEX_CONV +--->
    (vGEN_REWRITE_CONV vTOP_SWEEP_CONV -| map vGSYM)
      [vINT_OF_NUM_EQ; vINT_OF_NUM_LE; vINT_OF_NUM_LT; vINT_OF_NUM_GE;
       vINT_OF_NUM_GT; vINT_OF_NUM_ADD; vSPEC (parse_term "NUMERAL k") vINT_OF_NUM_MUL;
       vINT_OF_NUM_MAX; vINT_OF_NUM_MIN]
  and is_numimage t =
    match t with
      Comb(Const("int_of_num",_),n) when not(is_numeral n) -> true
    | _ -> false in
  fun tm ->
    let th1 = init_conv tm in
    let tm1 = rand(concl th1) in
    let avs,bod = strip_forall tm1 in
    let nim = setify(find_terms is_numimage bod) in
    let gvs = map (genvar -| type_of) nim in
    let pths = map (fun v -> vSPEC (rand v) vINT_POS) nim in
    let ibod = itlist (curry mk_imp -| concl) pths bod in
    let gbod = subst (zip gvs nim) ibod in
    let th2 = vINST (zip nim gvs) (vINT_ARITH gbod) in
    let th3 = vGENL avs (rev_itlist (vC vMP) pths th2) in
    vEQ_MP (vSYM th1) th3;;

let vARITH_TAC = vCONV_TAC(vEQT_INTRO -| vARITH_RULE);;

let vASM_ARITH_TAC =
  vREPEAT(vFIRST_X_ASSUM(vMP_TAC -| check (not -| is_forall -| concl))) ---->
  vARITH_TAC;;

(* ------------------------------------------------------------------------- *)
(* A few miscellaneous applications.                                         *)
(* ------------------------------------------------------------------------- *)

let vBINARY_INDUCT = try Cache.lookup_thm "BINARY_INDUCT" with _ ->  prove
 ((parse_term "!P. P 0 /\\ (!n. P n ==> P(2 * n) /\\ P(2 * n + 1)) ==> !n. P n"),
  vGEN_TAC ----> vSTRIP_TAC ----> vMATCH_MP_TAC num_WF ----> vGEN_TAC ---->
  vSTRIP_ASSUME_TAC(vARITH_RULE
   (parse_term "n = 0 \\/ n DIV 2 < n /\\ (n = 2 * n DIV 2 \\/ n = 2 * n DIV 2 + 1)")) ---->
  vASM_MESON_TAC[]);;

let vNUM_CASES_BINARY = try Cache.lookup_thm "NUM_CASES_BINARY" with _ ->  prove
 ((parse_term "!P. (!n. P n) <=> (!n. P(2 * n)) /\\ (!n. P(2 * n + 1))"),
  vMESON_TAC[vARITH_RULE (parse_term "n = 2 * n DIV 2 \\/ n = 2 * n DIV 2 + 1")]);;

let num_WF_DOWN = try Cache.lookup_thm "num_WF_DOWN" with _ ->  prove
 ((parse_term "!P m:num.\n        (!n. m <= n ==> P n) /\\\n        (!n. n < m /\\ (!p. n < p ==> P p) ==> P n)\n        ==> (!n. P n)"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vASM_CASES_TAC (parse_term "m = 0") ++--> [vASM_MESON_TAC[vLE_0]; vALL_TAC] ---->
  vSUBGOAL_THEN (parse_term "!i. P(m - 1 - i)") vMP_TAC ++-->
   [vMATCH_MP_TAC num_WF ----> vGEN_TAC ---->
    vDISCH_THEN(fun th -> vFIRST_X_ASSUM vMATCH_MP_TAC ----> vASSUME_TAC th) ---->
    vCONJ_TAC ++--> [vASM_ARITH_TAC; vX_GEN_TAC (parse_term "p:num")] ---->
    vASM_CASES_TAC (parse_term "m:num <= p") ----> vASM_SIMP_TAC[] ---->
    vSTRIP_TAC ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "m - 1 - p")) ---->
    vASM_SIMP_TAC[vARITH_RULE
     (parse_term "~(m <= p) ==> m - 1 - (m - 1 - p) = p")] ---->
    vDISCH_THEN vMATCH_MP_TAC ----> vASM_ARITH_TAC;
    vASM_MESON_TAC[vARITH_RULE (parse_term "~(m <= n) ==> n = m - 1 - (m - 1 - n)")]]);;

(* ------------------------------------------------------------------------- *)
(* Also a similar divisibility procedure for natural numbers.                *)
(* ------------------------------------------------------------------------- *)

let vNUM_GCD = try Cache.lookup_thm "NUM_GCD" with _ ->  prove
 ((parse_term "!a b. &(gcd(a,b)) = gcd(&a,&b)"),
  vREWRITE_TAC[num_gcd; vGSYM vNUM_OF_INT; int_gcd]);;

let vNUM_LCM = try Cache.lookup_thm "NUM_LCM" with _ ->  prove
 ((parse_term "!a b. &(lcm(a,b)) = lcm(&a,&b)"),
  vREWRITE_TAC[num_lcm; vGSYM vNUM_OF_INT; vINT_LCM_POS]);;

let vCONG = try Cache.lookup_thm "CONG" with _ ->  prove
 ((parse_term "!x y n. (x == y) (mod n) <=> x MOD n = y MOD n"),
  vREWRITE_TAC[num_congruent; vGSYM vINT_REM_EQ; vINT_OF_NUM_REM; vINT_OF_NUM_EQ]);;

let vCONG_LMOD = try Cache.lookup_thm "CONG_LMOD" with _ ->  prove
 ((parse_term "!x y n. (x MOD n == y) (mod n) <=> (x == y) (mod n)"),
  vREWRITE_TAC[vCONG; vMOD_MOD_REFL]);;

let vCONG_RMOD = try Cache.lookup_thm "CONG_RMOD" with _ ->  prove
 ((parse_term "!x y n. (x == y MOD n) (mod n) <=> (x == y) (mod n)"),
  vREWRITE_TAC[vCONG; vMOD_MOD_REFL]);;

let vCONG_DIV2 = try Cache.lookup_thm "CONG_DIV2" with _ ->  prove
 ((parse_term "!a b m n. (a == b) (mod (m * n)) ==> (a DIV m == b DIV m) (mod n)"),
  vSIMP_TAC[vCONG; vDIV_MOD]);;

let divides = try Cache.lookup_thm "divides" with _ ->  prove
 ((parse_term "a divides b <=> ?x. b = a * x"),
  vREWRITE_TAC[num_divides; int_divides] ---->
  vEQ_TAC ++--> [vALL_TAC; vMESON_TAC[vINT_OF_NUM_MUL; vINT_OF_NUM_EQ]] ---->
  vDISCH_THEN(vX_CHOOSE_TAC (parse_term "x:int")) ----> vEXISTS_TAC (parse_term "num_of_int(abs x)") ---->
  vSIMP_TAC[vGSYM vINT_OF_NUM_EQ;
           vINT_ARITH (parse_term "&m:int = &n <=> abs(&m :int) = abs(&n)")] ---->
  vASM_REWRITE_TAC[vGSYM vINT_OF_NUM_MUL; vINT_ABS_MUL] ---->
  vSIMP_TAC[vINT_OF_NUM_OF_INT; vINT_ABS_POS; vINT_ABS_ABS]);;

let vDIVIDES_LE = try Cache.lookup_thm "DIVIDES_LE" with _ ->  prove
 ((parse_term "!m n. m divides n ==> m <= n \\/ n = 0"),
  vSUBGOAL_THEN (parse_term "!m n. m <= m * n \\/ m * n = 0")
    (fun th -> vMESON_TAC[divides; th]) ---->
  vREWRITE_TAC[vLE_MULT_LCANCEL; vMULT_EQ_0; vARITH_RULE
   (parse_term "m <= m * n <=> m * 1 <= m * n")] ---->
  vASM_ARITH_TAC);;

let vDIVIDES_LE_STRONG = try Cache.lookup_thm "DIVIDES_LE_STRONG" with _ ->  prove
 ((parse_term "!m n. m divides n ==> 1 <= m /\\ m <= n \\/ n = 0"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "m = 0") ---->
  vASM_SIMP_TAC[vDIVIDES_LE; vLE_1; vLE_0] ---->
  vREWRITE_TAC[divides] ----> vMESON_TAC[vMULT_CLAUSES]);;

let vDIVIDES_LE_IMP = try Cache.lookup_thm "DIVIDES_LE_IMP" with _ ->  prove
 ((parse_term "!m n. m divides n /\\ (n = 0 ==> m = 0) ==> m <= n"),
  vMESON_TAC[vDIVIDES_LE; vLE_REFL]);;

let vPROPERLY_DIVIDES_LE_IMP = try Cache.lookup_thm "PROPERLY_DIVIDES_LE_IMP" with _ ->  prove
 ((parse_term "!m n. m divides n /\\ ~(n = 0) /\\ ~(m = n) ==> 2 * m <= n"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vMULT_SYM] ---->
  vSIMP_TAC[vIMP_CONJ; divides; vLEFT_IMP_EXISTS_THM] ---->
  vREWRITE_TAC[vNUM_RING (parse_term "~(m = m * d) <=> ~(m = 0) /\\ ~(d = 1)")] ---->
  vSIMP_TAC[vLE_MULT_LCANCEL; vMULT_EQ_0] ----> vARITH_TAC);;

let vDIVIDES_ANTISYM = try Cache.lookup_thm "DIVIDES_ANTISYM" with _ ->  prove
 ((parse_term "!m n. m divides n /\\ n divides m <=> m = n"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vALL_TAC; vREWRITE_TAC[divides] ----> vMESON_TAC[vMULT_CLAUSES]] ---->
  vDISCH_THEN(vCONJUNCTS_THEN(vMP_TAC -| vMATCH_MP vDIVIDES_LE_STRONG)) ---->
  vARITH_TAC);;

let vDIVIDES_ONE = try Cache.lookup_thm "DIVIDES_ONE" with _ ->  prove
 ((parse_term "!n. n divides 1 <=> n = 1"),
  vREWRITE_TAC[divides] ----> vMESON_TAC[vMULT_EQ_1; vMULT_CLAUSES]);;

let vDIV_ADD = try Cache.lookup_thm "DIV_ADD" with _ ->  prove
 ((parse_term "!d a b. d divides a \\/ d divides b\n           ==> (a + b) DIV d = a DIV d + b DIV d"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "d = 0") ---->
  vASM_SIMP_TAC[vDIV_ZERO; vADD_CLAUSES] ---->
  vREWRITE_TAC[divides] ----> vSTRIP_TAC ---->
  vASM_SIMP_TAC[vDIV_MULT_ADD; vDIV_MULT]);;

let vDIVIDES_MOD = try Cache.lookup_thm "DIVIDES_MOD" with _ ->  prove
 ((parse_term "!m n. m divides n <=> n MOD m = 0"),
  vREWRITE_TAC[divides; vMOD_EQ_0] ----> vMESON_TAC[vMULT_SYM]);;

let vDIVIDES_DIV_MULT = try Cache.lookup_thm "DIVIDES_DIV_MULT" with _ ->  prove
 ((parse_term "!m n. m divides n <=> ((n DIV m) * m = n)"),
  vREWRITE_TAC[vGSYM vINT_OF_NUM_EQ; vGSYM vINT_OF_NUM_MUL; vGSYM vINT_OF_NUM_DIV;
              vINT_MUL_DIV_EQ; vGSYM num_divides]);;

let vDIV_BY_DIV = try Cache.lookup_thm "DIV_BY_DIV" with _ ->  prove
 ((parse_term "!m n. ~(n = 0) /\\ m divides n ==> n DIV (n DIV m) = m"),
  vREWRITE_TAC[vGSYM vINT_OF_NUM_EQ; vGSYM vINT_OF_NUM_DIV; num_divides;
              vINT_DIV_BY_DIV]);;

let vDIVIDES_DIV_DIVIDES = try Cache.lookup_thm "DIVIDES_DIV_DIVIDES" with _ ->  prove
 ((parse_term "!n d e. d divides n /\\ (n = 0 ==> e = 0)\n           ==> (n DIV d divides e <=> n divides d * e)"),
  vREWRITE_TAC[vGSYM vINT_OF_NUM_EQ; vGSYM vINT_OF_NUM_DIV; num_divides;
              vGSYM vINT_OF_NUM_MUL; vINT_DIVIDES_DIV_DIVIDES]);;

let vDIVIDES_DIV_SELF = try Cache.lookup_thm "DIVIDES_DIV_SELF" with _ ->  prove
 ((parse_term "!n d. d divides n ==> n DIV d divides n"),
  vREWRITE_TAC[num_divides; vGSYM vINT_OF_NUM_DIV; vINT_DIVIDES_DIV_SELF]);;

let vDIVIDES_DIVIDES_DIV = try Cache.lookup_thm "DIVIDES_DIVIDES_DIV" with _ ->  prove
 ((parse_term "!n d e. d divides n ==> (e divides (n DIV d) <=> (d * e) divides n)"),
  vREWRITE_TAC[vGSYM vINT_OF_NUM_EQ; vGSYM vINT_OF_NUM_DIV; num_divides;
              vGSYM vINT_OF_NUM_MUL; vINT_DIVIDES_DIVIDES_DIV]);;

let vDIVIDES_DIVIDES_DIV_EQ = try Cache.lookup_thm "DIVIDES_DIVIDES_DIV_EQ" with _ ->  prove
 ((parse_term "!n d e:num. d divides n /\\ e divides n DIV d <=> d * e divides n"),
  vREWRITE_TAC[num_divides; vGSYM vINT_OF_NUM_DIV; vGSYM vINT_OF_NUM_MUL] ---->
  vREWRITE_TAC[vINT_DIVIDES_DIVIDES_DIV_EQ]);;

let vDIVIDES_DIVIDES_DIV_IMP = try Cache.lookup_thm "DIVIDES_DIVIDES_DIV_IMP" with _ ->  prove
 ((parse_term "!n d e. d * e divides n ==> e divides n DIV d"),
  vMESON_TAC[vDIVIDES_DIVIDES_DIV_EQ]);;

let vNUMBER_TAC =
  let conva = vGEN_REWRITE_CONV vTRY_CONV [vGSYM vDIVIDES_ANTISYM] in
  let rec antisym_conv tm =
    if is_forall tm || is_exists tm then vBINDER_CONV antisym_conv tm
    else if is_conj tm || is_disj tm then vBINOP_CONV antisym_conv tm
    else if is_imp tm then vRAND_CONV antisym_conv tm
    else conva tm in
  let pth_relativize = prove
   ((parse_term "((!n. P(&n)) <=> (!i:int. &0 <= i ==> P i)) /\\\n     ((?n. P(&n)) <=> (?i:int. &0 <= i /\\ P i))"),
    vGEN_REWRITE_TAC vRAND_CONV [vTAUT (parse_term "(a <=> b) <=> (~a <=> ~b)")] ---->
    vREWRITE_TAC[vNOT_EXISTS_THM; vINT_FORALL_POS] ----> vMESON_TAC[]) in
  let relation_conv =
   vGEN_REWRITE_CONV vTOP_SWEEP_CONV
    (num_divides::num_congruent::num_coprime::vNUM_GCD::vNUM_LCM::(map vGSYM
    [vINT_OF_NUM_EQ; vINT_OF_NUM_LE; vINT_OF_NUM_LT; vINT_OF_NUM_GE; vINT_OF_NUM_GT;
     vINT_OF_NUM_SUC; vINT_OF_NUM_ADD; vINT_OF_NUM_MUL; vINT_OF_NUM_POW]))
  and quantifier_conv = vGEN_REWRITE_CONV vDEPTH_CONV [pth_relativize] in
  vREPEAT(vCONJ_TAC |---> vGEN_TAC |---> vEQ_TAC) ----> vCONV_TAC antisym_conv ---->
  vW(fun (_,w) -> vMAP_EVERY (fun v -> vSPEC_TAC(v,v)) (frees w)) ---->
  vCONV_TAC(relation_conv +---> quantifier_conv) ---->
  vREWRITE_TAC[vRIGHT_IMP_FORALL_THM] ----> vREPEAT vGEN_TAC ---->
  vINTEGER_TAC;;

let vNUMBER_RULE tm = prove(tm,vNUMBER_TAC);;

let vCOPRIME_LMOD = try Cache.lookup_thm "COPRIME_LMOD" with _ ->  prove
 ((parse_term "!a n. coprime(a MOD n,n) <=> coprime(a,n)"),
  vMESON_TAC[vCONG_LMOD; vNUMBER_RULE (parse_term "(x:num == x) (mod n)"); vNUMBER_RULE
   (parse_term "(a:num == b) (mod n) /\\ coprime(a,n) ==> coprime(b,n)")]);;

let vCOPRIME_RMOD = try Cache.lookup_thm "COPRIME_RMOD" with _ ->  prove
 ((parse_term "!a n. coprime(n,a MOD n) <=> coprime(n,a)"),
  vONCE_REWRITE_TAC[vNUMBER_RULE (parse_term "coprime(a:num,b) <=> coprime(b,a)")] ---->
  vREWRITE_TAC[vCOPRIME_LMOD]);;

let vINT_CONG_NUM_EXISTS = try Cache.lookup_thm "INT_CONG_NUM_EXISTS" with _ ->  prove
 ((parse_term "!x y:int.\n        (y = &0 ==> &0 <= x)\n        ==> ?n. (&n == x) (mod y)"),
  vREPEAT vSTRIP_TAC ---->
  vEXISTS_TAC (parse_term "num_of_int(x + abs(x * y))") ---->
  vW(vMP_TAC -| vPART_MATCH (lhand -| rand) vINT_OF_NUM_OF_INT -|
        lhand -| rator -| snd) ---->
  vANTS_TAC ++-->
   [vPOP_ASSUM vMP_TAC ----> vASM_CASES_TAC (parse_term "y:int = &0") ---->
    vASM_REWRITE_TAC[] ++--> [vASM_ARITH_TAC; vALL_TAC] ---->
    vMATCH_MP_TAC(vINT_ARITH (parse_term "abs(x) * &1:int <= y ==> &0 <= x + y")) ---->
    vREWRITE_TAC[vINT_ABS_MUL] ----> vMATCH_MP_TAC vINT_LE_LMUL ---->
    vASM_INT_ARITH_TAC;
    vDISCH_THEN vSUBST1_TAC ---->
    vREWRITE_TAC[vINTEGER_RULE (parse_term "(x + a:int == x) (mod n) <=> n divides a")] ---->
    vREWRITE_TAC[vINT_ABS] ----> vCOND_CASES_TAC ----> vCONV_TAC vINTEGER_RULE]);;

let vGCD = try Cache.lookup_thm "GCD" with _ ->  prove
 ((parse_term "!a b. (gcd(a,b) divides a /\\ gcd(a,b) divides b) /\\\n         (!e. e divides a /\\ e divides b ==> e divides gcd(a,b))"),
  vNUMBER_TAC);;

let coprime = try Cache.lookup_thm "coprime" with _ ->  prove
 ((parse_term "coprime(a,b) <=> !d. d divides a /\\ d divides b ==> d = 1"),
  vEQ_TAC ++--> [vCONV_TAC vNUMBER_RULE; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "gcd(a,b)")) ----> vREWRITE_TAC[vGCD] ---->
  vNUMBER_TAC);;

(* ------------------------------------------------------------------------- *)
(* Definition (and not much more) of primality.                              *)
(* ------------------------------------------------------------------------- *)

let prime = new_definition
  (parse_term "prime(p) <=> ~(p = 1) /\\ !x. x divides p ==> x = 1 \\/ x = p");;

let vONE_OR_PRIME = try Cache.lookup_thm "ONE_OR_PRIME" with _ ->  prove
 ((parse_term "!p. p = 1 \\/ prime p <=> !n. n divides p ==> n = 1 \\/ n = p"),
  vGEN_TAC ----> vREWRITE_TAC[prime] ---->
  vASM_CASES_TAC (parse_term "p = 1") ----> vASM_REWRITE_TAC[vDIVIDES_ONE]);;

let vONE_OR_PRIME_DIVIDES_OR_COPRIME = try Cache.lookup_thm "ONE_OR_PRIME_DIVIDES_OR_COPRIME" with _ ->  prove
 ((parse_term "!p. p = 1 \\/ prime p <=> !n. p divides n \\/ coprime(p,n)"),
  vGEN_TAC ----> vEQ_TAC ----> vSTRIP_TAC ++-->
   [vASM_REWRITE_TAC[] ----> vGEN_TAC ----> vDISJ1_TAC ----> vCONV_TAC vNUMBER_RULE;
    vASM_MESON_TAC[prime; coprime];
    vREWRITE_TAC[vONE_OR_PRIME] ---->
    vX_GEN_TAC (parse_term "n:num") ----> vDISCH_TAC ----> vONCE_REWRITE_TAC[vDISJ_SYM] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "n:num")) ----> vMATCH_MP_TAC vMONO_OR ---->
    vCONJ_TAC ----> vPOP_ASSUM vMP_TAC ----> vCONV_TAC vNUMBER_RULE]);;

let vPRIME_COPRIME_EQ_NONDIVISIBLE = try Cache.lookup_thm "PRIME_COPRIME_EQ_NONDIVISIBLE" with _ ->  prove
 ((parse_term "!p. prime p <=> !n. coprime(p,n) <=> ~(p divides n)"),
  vX_GEN_TAC (parse_term "p:num") ----> vASM_CASES_TAC (parse_term "p = 1") ----> vASM_REWRITE_TAC[] ++-->
   [vASM_REWRITE_TAC[prime] ----> vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "1")) ---->
    vMATCH_MP_TAC(vTAUT (parse_term "p /\\ q ==> (p <=> ~q) ==> F")) ----> vCONV_TAC vNUMBER_RULE;
    vMP_TAC(vSPEC (parse_term "p:num") vONE_OR_PRIME_DIVIDES_OR_COPRIME) ---->
    vASM_REWRITE_TAC[] ----> vDISCH_THEN vSUBST1_TAC ---->
    vEQ_TAC ----> vMATCH_MP_TAC vMONO_FORALL ----> vSIMP_TAC[vTAUT (parse_term "p \\/ ~p")] ---->
    vGEN_TAC ----> vMATCH_MP_TAC(vTAUT (parse_term "~(p /\\ q) ==> q \\/ p ==> (p <=> ~q)")) ---->
    vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vCONTRAPOS_THM] ---->
    vCONV_TAC vNUMBER_RULE]);;

let vZERO_ONE_OR_PRIME_DIVPROD = try Cache.lookup_thm "ZERO_ONE_OR_PRIME_DIVPROD" with _ ->  prove
 ((parse_term "!p a b.\n        p = 0 \\/ p = 1 \\/ prime p\n        ==> (p divides (a * b) <=> p divides a \\/ p divides b)"),
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[vNUMBER_RULE (parse_term "1 divides n")] ---->
  vASM_REWRITE_TAC[vNUMBER_RULE (parse_term "0 divides n <=> n = 0"); vMULT_EQ_0] ---->
  vEQ_TAC ++--> [vALL_TAC; vCONV_TAC vNUMBER_RULE] ---->
  vASM_MESON_TAC[prime; coprime; vNUMBER_RULE
   (parse_term "!d a b:num. d divides (a * b) /\\ coprime(d,a) ==> d divides b")]);;

let vZERO_ONE_OR_PRIME = try Cache.lookup_thm "ZERO_ONE_OR_PRIME" with _ ->  prove
 ((parse_term "!p. p = 0 \\/ p = 1 \\/ prime p <=>\n       !a b. p divides (a * b) ==> p divides a \\/ p divides b"),
  vGEN_TAC ----> vEQ_TAC ----> vSIMP_TAC[vZERO_ONE_OR_PRIME_DIVPROD] ---->
  vDISCH_TAC ----> vREWRITE_TAC[vTAUT (parse_term "p \\/ q <=> ~p ==> q")] ---->
  vREPEAT vSTRIP_TAC ---->
  vASM_REWRITE_TAC[prime; divides; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "a:num"); (parse_term "b:num")] ----> vDISCH_THEN(vASSUME_TAC -| vSYM) ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "a:num"); (parse_term "b:num")]) ---->
  vFIRST_X_ASSUM(vSUBST_ALL_TAC -| vSYM) ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vMULT_EQ_0; vMULT_EQ_1; vDE_MORGAN_THM]) ---->
  vREWRITE_TAC[vNUMBER_RULE (parse_term "(n:num) divides n")] ---->
  vSTRIP_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vMATCH_MP vDIVIDES_LE_STRONG) ---->
  vONCE_REWRITE_TAC[vARITH_RULE (parse_term "a * b <= a <=> a * b <= a * 1");
                   vARITH_RULE (parse_term "a * b <= b <=> a * b <= 1 * b")]---->
  vREWRITE_TAC[vLE_MULT_LCANCEL; vLE_MULT_RCANCEL] ---->
  vASM_SIMP_TAC[vMULT_CLAUSES; vARITH_RULE (parse_term "n <= 1 <=> n = 0 \\/ n = 1")]);;

(* ------------------------------------------------------------------------- *)
(* Integer powers of real numbers.                                           *)
(* ------------------------------------------------------------------------- *)

make_overloadable "zpow" (parse_type "A->int->A");;
parse_as_infix("zpow",(24,"left"));;
overload_interface ("zpow",(parse_term "real_zpow:real->int->real"));;

let real_zpow = new_definition
 (parse_term "(z:real) zpow (i:int) = if &0 <= i then z pow (num_of_int i)\n                          else inv(z pow (num_of_int(--i)))");;

let vREAL_POW_ZPOW = try Cache.lookup_thm "REAL_POW_ZPOW" with _ ->  prove
 ((parse_term "!x n. x pow n = x zpow (&n)"),
  vREWRITE_TAC[real_zpow; vINT_POS; vNUM_OF_INT_OF_NUM]);;

let vREAL_ZPOW_NUM = try Cache.lookup_thm "REAL_ZPOW_NUM" with _ ->  prove
 ((parse_term "!x n. x zpow (&n) = x pow n"),
  vREWRITE_TAC[real_zpow; vINT_POS; vNUM_OF_INT_OF_NUM]);;

let vREAL_ZPOW_0 = try Cache.lookup_thm "REAL_ZPOW_0" with _ ->  prove
 ((parse_term "!x:real. x zpow (&0) = &1"),
  vREWRITE_TAC[vREAL_ZPOW_NUM; real_pow]);;

let vREAL_ZPOW_1 = try Cache.lookup_thm "REAL_ZPOW_1" with _ ->  prove
 ((parse_term "!x:real. x zpow (&1) = x"),
  vREWRITE_TAC[vREAL_ZPOW_NUM; vREAL_POW_1]);;

let vREAL_ZPOW_2 = try Cache.lookup_thm "REAL_ZPOW_2" with _ ->  prove
 ((parse_term "!x:real. x zpow (&2) = x * x"),
  vREWRITE_TAC[vREAL_ZPOW_NUM; vREAL_POW_2]);;

let vREAL_ZPOW_ONE = try Cache.lookup_thm "REAL_ZPOW_ONE" with _ ->  prove
 ((parse_term "!n. &1 zpow n = &1"),
  vREWRITE_TAC[real_zpow; vREAL_POW_ONE; vREAL_INV_1; vCOND_ID]);;

let vREAL_ZPOW_NEG = try Cache.lookup_thm "REAL_ZPOW_NEG" with _ ->  prove
 ((parse_term "!x n. x zpow (--n) = inv(x zpow n)"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n:int = &0") ---->
  vASM_REWRITE_TAC[vINT_NEG_0; vREAL_ZPOW_0; vREAL_INV_1] ---->
  vASM_SIMP_TAC[real_zpow; vCOND_SWAP; vINT_NEG_NEG; vINT_ARITH
   (parse_term "~(n:int = &0) ==> (&0 <= --n <=> ~(&0 <= n))")] ---->
  vMESON_TAC[vREAL_INV_INV]);;

let vREAL_ZPOW_MINUS1 = try Cache.lookup_thm "REAL_ZPOW_MINUS1" with _ ->  prove
 ((parse_term "!x. x zpow --(&1) = inv x"),
  vREWRITE_TAC[vREAL_ZPOW_NEG; vREAL_ZPOW_1]);;

let vREAL_ZPOW_ZERO = try Cache.lookup_thm "REAL_ZPOW_ZERO" with _ ->  prove
 ((parse_term "!n. &0 zpow n = if n = &0 then &1 else &0"),
  vREWRITE_TAC[vFORALL_INT_CASES; vREAL_ZPOW_NEG; vREAL_ZPOW_NUM] ---->
  vREWRITE_TAC[vREAL_POW_ZERO; vINT_NEG_EQ_0; vINT_OF_NUM_EQ] ---->
  vMESON_TAC[vREAL_INV_0; vREAL_INV_1]);;

let vREAL_ZPOW_POW = try Cache.lookup_thm "REAL_ZPOW_POW" with _ ->  prove
 ((parse_term "(!(x:real) n. x zpow (&n) = x pow n) /\\\n   (!(x:real) n. x zpow (-- &n) = inv(x pow n))"),
  vREWRITE_TAC[vREAL_ZPOW_NEG; vREAL_ZPOW_NUM]);;

let vREAL_INV_ZPOW = try Cache.lookup_thm "REAL_INV_ZPOW" with _ ->  prove
 ((parse_term "!(x:real) n. inv(x zpow n) = inv(x) zpow n"),
  vREWRITE_TAC[vFORALL_INT_CASES; vREAL_ZPOW_POW] ---->
  vREWRITE_TAC[vREAL_INV_POW; vREAL_INV_INV]);;

let vREAL_ZPOW_INV = try Cache.lookup_thm "REAL_ZPOW_INV" with _ ->  prove
 ((parse_term "!(x:real) n. inv x zpow n = inv(x zpow n)"),
  vREWRITE_TAC[vREAL_INV_ZPOW]);;

let vREAL_ZPOW_ZPOW = try Cache.lookup_thm "REAL_ZPOW_ZPOW" with _ ->  prove
 ((parse_term "!(x:real) m n. (x zpow m) zpow n = x zpow (m * n)"),
  vREWRITE_TAC[vFORALL_INT_CASES; vINT_MUL_LNEG; vINT_MUL_RNEG; vINT_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_ZPOW_POW; vREAL_INV_POW; vINT_OF_NUM_MUL; vREAL_INV_INV] ---->
  vREWRITE_TAC[vREAL_POW_POW]);;

let vREAL_ZPOW_MUL = try Cache.lookup_thm "REAL_ZPOW_MUL" with _ ->  prove
 ((parse_term "!(x:real) (y:real) n. (x * y) zpow n = x zpow n * y zpow n"),
  vREWRITE_TAC[vFORALL_INT_CASES; vREAL_ZPOW_POW; vREAL_POW_MUL; vREAL_INV_MUL]);;

let vREAL_ZPOW_DIV = try Cache.lookup_thm "REAL_ZPOW_DIV" with _ ->  prove
 ((parse_term "!(x:real) (y:real) n. (x / y) zpow n = x zpow n / y zpow n"),
  vREWRITE_TAC[real_div; vREAL_INV_ZPOW; vREAL_ZPOW_MUL]);;

let vREAL_ZPOW_ADD = try Cache.lookup_thm "REAL_ZPOW_ADD" with _ ->  prove
 ((parse_term "!(x:real) m n.\n        ~(x = &0) ==> x zpow (m + n) = x zpow m * x zpow n"),
  vREWRITE_TAC[vFORALL_INT_CASES; vGSYM vINT_NEG_ADD; vINT_OF_NUM_ADD] ---->
  vREWRITE_TAC[vREAL_ZPOW_POW; vREAL_POW_ADD; vREAL_INV_MUL] ---->
  vX_GEN_TAC (parse_term "x:real") ----> vGEN_REWRITE_TAC vLAND_CONV [vSWAP_FORALL_THM] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV)
    [vREAL_MUL_SYM; vINT_ADD_SYM] ---->
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vWLOG_LE ----> vCONJ_TAC ++-->
   [vREPEAT vGEN_TAC ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_EQ_INV2] ---->
    vREWRITE_TAC[vREAL_INV_MUL; vREAL_INV_INV; vGSYM vREAL_ZPOW_NEG] ---->
    vREWRITE_TAC[vINT_ARITH (parse_term "--(--x + y):int = --y + x")] ---->
    vREWRITE_TAC[vREAL_MUL_AC];
    vMAP_EVERY vX_GEN_TAC [(parse_term "n:num"); (parse_term "p:num")] ---->
    vREWRITE_TAC[vLE_EXISTS; vLEFT_IMP_EXISTS_THM] ---->
    vSIMP_TAC[vGSYM vINT_OF_NUM_ADD; vARITH_RULE (parse_term "--n + (n + m):int = m")] ---->
    vREWRITE_TAC[vREAL_POW_ADD; vREAL_ZPOW_NUM; vREAL_MUL_ASSOC] ---->
    vASM_SIMP_TAC[vREAL_MUL_LINV; vREAL_POW_EQ_0; vREAL_MUL_LID]]);;

let vREAL_ZPOW_SUB = try Cache.lookup_thm "REAL_ZPOW_SUB" with _ ->  prove
 ((parse_term "!(x:real) m n.\n        ~(x = &0) ==> x zpow (m - n) = x zpow m / x zpow n"),
  vSIMP_TAC[vINT_SUB; vREAL_ZPOW_ADD; vREAL_ZPOW_NEG; real_div]);;

let vREAL_ZPOW_LE = try Cache.lookup_thm "REAL_ZPOW_LE" with _ ->  prove
 ((parse_term "!x n. &0 <= x ==> &0 <= x zpow n"),
  vSIMP_TAC[vFORALL_INT_CASES; vREAL_ZPOW_POW; vREAL_LE_INV_EQ; vREAL_POW_LE]);;

let vREAL_ZPOW_LT = try Cache.lookup_thm "REAL_ZPOW_LT" with _ ->  prove
 ((parse_term "!x n. &0 < x ==> &0 < x zpow n"),
  vSIMP_TAC[vFORALL_INT_CASES; vREAL_ZPOW_POW; vREAL_LT_INV_EQ; vREAL_POW_LT]);;

let vREAL_ZPOW_EQ_0 = try Cache.lookup_thm "REAL_ZPOW_EQ_0" with _ ->  prove
 ((parse_term "!x n. x zpow n = &0 <=> x = &0 /\\ ~(n = &0)"),
  vREWRITE_TAC[vFORALL_INT_CASES; vREAL_ZPOW_POW; vREAL_INV_EQ_0] ---->
  vREWRITE_TAC[vINT_NEG_EQ_0; vREAL_POW_EQ_0; vINT_OF_NUM_EQ]);;

let vREAL_ABS_ZPOW = try Cache.lookup_thm "REAL_ABS_ZPOW" with _ ->  prove
 ((parse_term "!x n. abs(x zpow n) = abs(x) zpow n"),
  vREWRITE_TAC[vFORALL_INT_CASES; vREAL_ZPOW_POW; vREAL_ABS_INV; vREAL_ABS_POW]);;

let vREAL_SGN_ZPOW = try Cache.lookup_thm "REAL_SGN_ZPOW" with _ ->  prove
 ((parse_term "!x n. real_sgn(x zpow n) = real_sgn(x) zpow n"),
  vREWRITE_TAC[vFORALL_INT_CASES; vREAL_ZPOW_POW] ---->
  vREWRITE_TAC[vGSYM vREAL_SGN_POW] ---->
  vREWRITE_TAC[vREAL_SGN_INV; vREAL_INV_SGN]);;

(* ------------------------------------------------------------------------- *)
(* Make sure we give priority to N.                                          *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;
