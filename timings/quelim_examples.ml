open Hol.All
open Mathlib.Quelim

let ppth th =
        pp_print_thm Format.std_formatter th;
        print_newline ()
;;
(* ========================================================================= *)
(* Some examples of full complex quantifier elimination.                     *)
(* ========================================================================= *)

let th = time prove
 ([%q {|!x y. (x pow 2 = Cx(&2)) /\ (y pow 2 = Cx(&3))
         ==> ((x * y) pow 2 = Cx(&6))|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

let th = time prove
 ([%q {|!x a. (a pow 2 = Cx(&2)) /\ (x pow 2 + a * x + Cx(&1) = Cx(&0))
         ==> (x pow 4 + Cx(&1) = Cx(&0))|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

let th = time prove
 ([%q {|!a x. (a pow 2 = Cx(&2)) /\ (x pow 2 + a * x + Cx(&1) = Cx(&0))
         ==> (x pow 4 + Cx(&1) = Cx(&0))|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

let th = time prove
 ([%q {|~(?a x y. (a pow 2 = Cx(&2)) /\
             (x pow 2 + a * x + Cx(&1) = Cx(&0)) /\
             (y * (x pow 4 + Cx(&1)) + Cx(&1) = Cx(&0)))|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

let th = time prove
 ([%q {|!x. ?y. x pow 2 = y pow 3|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

let th = time prove
 ([%q {|!x y z a b. (a + b) * (x - y + z) - (a - b) * (x + y + z) =
               Cx(&2) * (b * x + b * z - a * y)|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

let th = time prove
 ([%q {|!a b. ~(a = b) ==> ?x y. (y * x pow 2 = a) /\ (y * x pow 2 + x = b)|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

let th = time prove
 ([%q {|!a b c x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
               (a * y pow 2 + b * y + c = Cx(&0)) /\
               ~(x = y)
               ==> (a * x * y = c) /\ (a * (x + y) + b = Cx(&0))|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

let th = time prove
 ([%q {|~(!a b c x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
                 (a * y pow 2 + b * y + c = Cx(&0))
                 ==> (a * x * y = c) /\ (a * (x + y) + b = Cx(&0)))|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

(** geometric example from ``Algorithms for Computer Algebra'':
    right triangle where perp. bisector of hypotenuse passes through the
    right angle is isoseles.
 **)

let th = time prove
 ([%q {|!y_1 y_2 y_3 y_4.
     (y_1 = Cx(&2) * y_3) /\
     (y_2 = Cx(&2) * y_4) /\
     (y_1 * y_3 = y_2 * y_4)
     ==> (y_1 pow 2 = y_2 pow 2)|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

(** geometric example: gradient condition for two lines to be non-parallel.
 **)

let th = time prove
 ([%q {|!a1 b1 c1 a2 b2 c2.
        ~(a1 * b2 = a2 * b1)
        ==> ?x y. (a1 * x + b1 * y = c1) /\ (a2 * x + b2 * y = c2)|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

(*********** Apparently takes too long

let th = time prove
 ([%q {|!a b c x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
               (a * y pow 2 + b * y + c = Cx(&0)) /\
               (!z. (a * z pow 2 + b * z + c = Cx(&0))
                    ==> (z = x) \/ (z = y))
               ==> (a * x * y = c) /\ (a * (x + y) + b = Cx(&0))|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

*************)

(* ------------------------------------------------------------------------- *)
(* Any three points determine a circle. Not true in complex number version!  *)
(* ------------------------------------------------------------------------- *)

(******** And it takes a lot of memory!

let th = time prove
 ([%q {|~(!x1 y1 x2 y2 x3 y3.
        ?x0 y0. ((x1 - x0) pow 2 + (y1 - y0) pow 2 =
                 (x2 - x0) pow 2 + (y2 - y0) pow 2) /\
                ((x2 - x0) pow 2 + (y2 - y0) pow 2 =
                 (x3 - x0) pow 2 + (y3 - y0) pow 2))|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

 **************)

(* ------------------------------------------------------------------------- *)
(* To show we don't need to consider only closed formulas.                   *)
(* Can eliminate some, then deal with the rest manually and painfully.       *)
(* ------------------------------------------------------------------------- *)

let th = time prove
 ([%q {|(?x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
          (a * y pow 2 + b * y + c = Cx(&0)) /\
          ~(x = y)) <=>
   (a = Cx(&0)) /\ (b = Cx(&0)) /\ (c = Cx(&0)) \/
   ~(a = Cx(&0)) /\ ~(b pow 2 = Cx(&4) * a * c)|} ],
  vCONV_TAC(vLAND_CONV vFULL_COMPLEX_QUELIM_CONV) ---->
  vREWRITE_TAC[poly; vCOMPLEX_MUL_RZERO; vCOMPLEX_ADD_LID; vCOMPLEX_ADD_RID] ---->
  vREWRITE_TAC[vCOMPLEX_ENTIRE; vCX_INJ; vREAL_OF_NUM_EQ; vARITH] ---->
  vASM_CASES_TAC [%q {|a = Cx(&0)|} ] ---->
  vASM_REWRITE_TAC[vCOMPLEX_MUL_LZERO; vCOMPLEX_MUL_RZERO] ++-->
   [vASM_CASES_TAC [%q {|b = Cx(&0)|} ] ---->
    vASM_REWRITE_TAC[vCOMPLEX_MUL_LZERO; vCOMPLEX_MUL_RZERO];
    vONCE_REWRITE_TAC[vSIMPLE_COMPLEX_ARITH
     [%q {|b * b * c * Cx(--(&1)) + a * c * c * Cx(&4) =
      c * (Cx(&4) * a * c - b * b)|} ]] ---->
    vONCE_REWRITE_TAC[vSIMPLE_COMPLEX_ARITH
     [%q {|b * b * b * Cx(--(&1)) + a * b * c * Cx (&4) =
      b * (Cx(&4) * a * c - b * b)|} ]] ---->
    vONCE_REWRITE_TAC[vSIMPLE_COMPLEX_ARITH
     [%q {|b * b * Cx (&1) + a * c * Cx(--(&4)) =
      Cx(--(&1)) * (Cx(&4) * a * c - b * b)|} ]] ---->
    vREWRITE_TAC[vCOMPLEX_ENTIRE; vCOMPLEX_SUB_0; vCX_INJ] ---->
    vCONV_TAC vREAL_RAT_REDUCE_CONV ---->
    vASM_CASES_TAC [%q {|b = Cx(&0)|} ] ----> vASM_REWRITE_TAC[] ---->
    vASM_CASES_TAC [%q {|c = Cx(&0)|} ] ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vCOMPLEX_POW_2; vCOMPLEX_MUL_RZERO; vCOMPLEX_MUL_LZERO] ---->
    vREWRITE_TAC[vEQ_SYM_EQ]]) in ppth th;;

(* ------------------------------------------------------------------------- *)
(* Do the same thing directly.                                               *)
(* ------------------------------------------------------------------------- *)

(**** This seems barely feasible
 ****)

let th = time prove
 ([%q {|!a b c.
      (?x y. (a * x pow 2 + b * x + c = Cx(&0)) /\
             (a * y pow 2 + b * y + c = Cx(&0)) /\
             ~(x = y)) <=>
      (a = Cx(&0)) /\ (b = Cx(&0)) /\ (c = Cx(&0)) \/
      ~(a = Cx(&0)) /\ ~(b pow 2 = Cx(&4) * a * c)|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

(* ------------------------------------------------------------------------- *)
(* More ambitious: determine a unique circle. Also not true over complexes.  *)
(* (consider the points (k, k i) where i is the imaginary unit...)           *)
(* ------------------------------------------------------------------------- *)

(********** Takes too long, I think, and too much memory too
 *************)

let th = time prove
 ([%q {|~(!x1 y1 x2 y2 x3 y3 x0 y0 x0' y0'.
        ((x1 - x0) pow 2 + (y1 - y0) pow 2 =
         (x2 - x0) pow 2 + (y2 - y0) pow 2) /\
        ((x2 - x0) pow 2 + (y2 - y0) pow 2 =
         (x3 - x0) pow 2 + (y3 - y0) pow 2) /\
        ((x1 - x0') pow 2 + (y1 - y0') pow 2 =
         (x2 - x0') pow 2 + (y2 - y0') pow 2) /\
        ((x2 - x0') pow 2 + (y2 - y0') pow 2 =
         (x3 - x0') pow 2 + (y3 - y0') pow 2)
        ==> (x0 = x0') /\ (y0 = y0'))|} ],
  vCONV_TAC vFULL_COMPLEX_QUELIM_CONV) in ppth th;;

(* ------------------------------------------------------------------------- *)
(* Side of a triangle in terms of its bisectors; Kapur survey 5.1.           *)
(* ------------------------------------------------------------------------- *)

(*************
let th = time FULL_COMPLEX_QUELIM_CONV
 `?b c. (p1 = ai pow 2 * (b + c) pow 2 - c * b * (c + b - a) * (c + b + a)) /\
        (p2 = ae pow 2 * (c - b) pow 2 - c * b * (a + b - c) * (a - b + a)) /\
        (p3 = be pow 2 * (c - a) pow 2 - a * c * (a + b - c) * (c + b - a))`;;

 *************)
