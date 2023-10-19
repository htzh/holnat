[@@@warning "-27-8"]
open Hol.All
include Complex_grobner
;;
(* ========================================================================= *)
(* Trivial restriction of complex Groebner bases to reals.                   *)
(* ========================================================================= *)

let vGROBNER_REAL_ARITH =
  let trans_conv = vGEN_REWRITE_CONV vTOP_SWEEP_CONV
     [vGSYM vCX_INJ; vCX_POW; vCX_MUL; vCX_ADD; vCX_NEG; vCX_SUB] in
  fun tm -> let th = trans_conv tm in
            vEQ_MP (vSYM th) (vCOMPLEX_ARITH(rand(concl th)));;
