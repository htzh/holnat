(* ========================================================================= *)
(* Examples of using the Grobner basis procedure.                            *)
(* ========================================================================= *)
open Hol.All
open Mathlib.Complex_real
;;

time vCOMPLEX_ARITH
  [%q {|!a b c.
        (a * x pow 2 + b * x + c = Cx(&0)) /\
        (a * y pow 2 + b * y + c = Cx(&0)) /\
        ~(x = y)
        ==> (a * (x + y) + b = Cx(&0))|} ];;

time vCOMPLEX_ARITH
  [%q {|!a b c.
        (a * x pow 2 + b * x + c = Cx(&0)) /\
        (Cx(&2) * a * y pow 2 + Cx(&2) * b * y + Cx(&2) * c = Cx(&0)) /\
        ~(x = y)
        ==> (a * (x + y) + b = Cx(&0))|} ];;

(* ------------------------------------------------------------------------- *)
(* Another example.                                                          *)
(* ------------------------------------------------------------------------- *)

time vCOMPLEX_ARITH
 [%q {|~((y_1 = Cx(&2) * y_3) /\
    (y_2 = Cx(&2) * y_4) /\
    (y_1 * y_3 = y_2 * y_4) /\
    ((y_1 pow 2 - y_2 pow 2) * z = Cx(&1)))|} ];;

time vCOMPLEX_ARITH
  [%q {|!y_1 y_2 y_3 y_4.
       (y_1 = Cx(&2) * y_3) /\
       (y_2 = Cx(&2) * y_4) /\
       (y_1 * y_3 = y_2 * y_4)
       ==> (y_1 pow 2 = y_2 pow 2)|} ];;

(* ------------------------------------------------------------------------- *)
(* Angle at centre vs. angle at circumference.                               *)
(* Formulation from "Real quantifier elimination in practice" paper.         *)
(* ------------------------------------------------------------------------- *)

time vCOMPLEX_ARITH
  [%q {|~((c pow 2 = a pow 2 + b pow 2) /\
     (c pow 2 = x0 pow 2 + (y0 - b) pow 2) /\
     (y0 * t1 = a + x0) /\
     (y0 * t2 = a - x0) /\
     ((Cx(&1) - t1 * t2) * t = t1 + t2) /\
     (u * (b * t - a) = Cx(&1)) /\
     (v1 * a + v2 * x0 + v3 * y0 = Cx(&1)))|} ];;

time vCOMPLEX_ARITH
  [%q {|(c pow 2 = a pow 2 + b pow 2) /\
   (c pow 2 = x0 pow 2 + (y0 - b) pow 2) /\
   (y0 * t1 = a + x0) /\
   (y0 * t2 = a - x0) /\
   ((Cx(&1) - t1 * t2) * t = t1 + t2) /\
   (~(a = Cx(&0)) \/ ~(x0 = Cx(&0)) \/ ~(y0 = Cx(&0)))
   ==> (b * t = a)|} ];;

time vCOMPLEX_ARITH
  [%q {|(c pow 2 = a pow 2 + b pow 2) /\
   (c pow 2 = x0 pow 2 + (y0 - b) pow 2) /\
   (y0 * t1 = a + x0) /\
   (y0 * t2 = a - x0) /\
   ((Cx(&1) - t1 * t2) * t = t1 + t2) /\
   (~(a = Cx(&0)) /\ ~(x0 = Cx(&0)) /\ ~(y0 = Cx(&0)))
   ==> (b * t = a)|} ];;

(* ------------------------------------------------------------------------- *)
(* Another example (note we rule out points 1, 2 or 3 coinciding).           *)
(* ------------------------------------------------------------------------- *)

time vCOMPLEX_ARITH
 [%q {|((x1 - x0) pow 2 + (y1 - y0) pow 2 =
   (x2 - x0) pow 2 + (y2 - y0) pow 2) /\
  ((x2 - x0) pow 2 + (y2 - y0) pow 2 =
   (x3 - x0) pow 2 + (y3 - y0) pow 2) /\
  ((x1 - x0') pow 2 + (y1 - y0') pow 2 =
   (x2 - x0') pow 2 + (y2 - y0') pow 2) /\
  ((x2 - x0') pow 2 + (y2 - y0') pow 2 =
   (x3 - x0') pow 2 + (y3 - y0') pow 2) /\
  (a12 * (x1 - x2) + b12 * (y1 - y2) = Cx(&1)) /\
  (a13 * (x1 - x3) + b13 * (y1 - y3) = Cx(&1)) /\
  (a23 * (x2 - x3) + b23 * (y2 - y3) = Cx(&1)) /\
  ~((x1 - x0) pow 2 + (y1 - y0) pow 2 = Cx(&0))
  ==> (x0' = x0) /\ (y0' = y0)|} ];;

time vCOMPLEX_ARITH
 [%q {|~(((x1 - x0) pow 2 + (y1 - y0) pow 2 =
   (x2 - x0) pow 2 + (y2 - y0) pow 2) /\
  ((x2 - x0) pow 2 + (y2 - y0) pow 2 =
   (x3 - x0) pow 2 + (y3 - y0) pow 2) /\
  ((x1 - x0') pow 2 + (y1 - y0') pow 2 =
   (x2 - x0') pow 2 + (y2 - y0') pow 2) /\
  ((x2 - x0') pow 2 + (y2 - y0') pow 2 =
   (x3 - x0') pow 2 + (y3 - y0') pow 2) /\
  (a12 * (x1 - x2) + b12 * (y1 - y2) = Cx(&1)) /\
  (a13 * (x1 - x3) + b13 * (y1 - y3) = Cx(&1)) /\
  (a23 * (x2 - x3) + b23 * (y2 - y3) = Cx(&1)) /\
  (z * (x0' - x0) = Cx(&1)) /\
  (z' * (y0' - y0) = Cx(&1)) /\
  (z'' * ((x1 - x0) pow 2 + (y1 - y0) pow 2) = Cx(&1)) /\
  (z''' * ((x1 - x09) pow 2 + (y1 - y09) pow 2) = Cx(&1)))|} ];;

(* ------------------------------------------------------------------------- *)
(* These are pure algebraic simplification.                                  *)
(* ------------------------------------------------------------------------- *)

let vLAGRANGE_4 = time vCOMPLEX_ARITH
 [%q {|(((x1 pow 2) + (x2 pow 2) + (x3 pow 2) + (x4 pow 2)) *
   ((y1 pow 2) + (y2 pow 2) + (y3 pow 2) + (y4 pow 2))) =
  ((((((x1*y1) - (x2*y2)) - (x3*y3)) - (x4*y4)) pow 2)  +
   (((((x1*y2) + (x2*y1)) + (x3*y4)) - (x4*y3)) pow 2)  +
   (((((x1*y3) - (x2*y4)) + (x3*y1)) + (x4*y2)) pow 2)  +
   (((((x1*y4) + (x2*y3)) - (x3*y2)) + (x4*y1)) pow 2))|} ];;

let vLAGRANGE_8 = time vCOMPLEX_ARITH
 [%q {|((p1 pow 2 + q1 pow 2 + r1 pow 2 + s1 pow 2 + t1 pow 2 + u1 pow 2 + v1 pow 2 + w1 pow 2) *
   (p2 pow 2 + q2 pow 2 + r2 pow 2 + s2 pow 2 + t2 pow 2 + u2 pow 2 + v2 pow 2 + w2 pow 2)) =
   ((p1 * p2 - q1 * q2 - r1 * r2 - s1 * s2 - t1 * t2 - u1 * u2 - v1 * v2 - w1* w2) pow 2 +
    (p1 * q2 + q1 * p2 + r1 * s2 - s1 * r2 + t1 * u2 - u1 * t2 - v1 * w2 + w1* v2) pow 2 +
    (p1 * r2 - q1 * s2 + r1 * p2 + s1 * q2 + t1 * v2 + u1 * w2 - v1 * t2 - w1* u2) pow 2 +
    (p1 * s2 + q1 * r2 - r1 * q2 + s1 * p2 + t1 * w2 - u1 * v2 + v1 * u2 - w1* t2) pow 2 +
    (p1 * t2 - q1 * u2 - r1 * v2 - s1 * w2 + t1 * p2 + u1 * q2 + v1 * r2 + w1* s2) pow 2 +
    (p1 * u2 + q1 * t2 - r1 * w2 + s1 * v2 - t1 * q2 + u1 * p2 - v1 * s2 + w1* r2) pow 2 +
    (p1 * v2 + q1 * w2 + r1 * t2 - s1 * u2 - t1 * r2 + u1 * s2 + v1 * p2 - w1* q2) pow 2 +
    (p1 * w2 - q1 * v2 + r1 * u2 + s1 * t2 - t1 * s2 - u1 * r2 + v1 * q2 + w1* p2) pow 2)|} ];;

let vLIOUVILLE = time vCOMPLEX_ARITH
 [%q {|((x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 2) =
  (Cx(&1 / &6) * ((x1 + x2) pow 4 + (x1 + x3) pow 4 + (x1 + x4) pow 4 +
                (x2 + x3) pow 4 + (x2 + x4) pow 4 + (x3 + x4) pow 4) +
   Cx(&1 / &6) * ((x1 - x2) pow 4 + (x1 - x3) pow 4 + (x1 - x4) pow 4 +
                (x2 - x3) pow 4 + (x2 - x4) pow 4 + (x3 - x4) pow 4))|} ];;

let vFLECK = time vCOMPLEX_ARITH
 [%q {|((x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 3) =
  (Cx(&1 / &60) * ((x1 + x2 + x3) pow 6 + (x1 + x2 - x3) pow 6 +
                 (x1 - x2 + x3) pow 6 + (x1 - x2 - x3) pow 6 +
                 (x1 + x2 + x4) pow 6 + (x1 + x2 - x4) pow 6 +
                 (x1 - x2 + x4) pow 6 + (x1 - x2 - x4) pow 6 +
                 (x1 + x3 + x4) pow 6 + (x1 + x3 - x4) pow 6 +
                 (x1 - x3 + x4) pow 6 + (x1 - x3 - x4) pow 6 +
                 (x2 + x3 + x4) pow 6 + (x2 + x3 - x4) pow 6 +
                 (x2 - x3 + x4) pow 6 + (x2 - x3 - x4) pow 6) +
   Cx(&1 / &30) * ((x1 + x2) pow 6 + (x1 - x2) pow 6 +
                 (x1 + x3) pow 6 + (x1 - x3) pow 6 +
                 (x1 + x4) pow 6 + (x1 - x4) pow 6 +
                 (x2 + x3) pow 6 + (x2 - x3) pow 6 +
                 (x2 + x4) pow 6 + (x2 - x4) pow 6 +
                 (x3 + x4) pow 6 + (x3 - x4) pow 6) +
   Cx(&3 / &5) *  (x1 pow 6 + x2 pow 6 + x3 pow 6 + x4 pow 6))|} ];;

let vHURWITZ = time vCOMPLEX_ARITH
 [%q {|!x1 x2 x3 x4.
    (x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 4 =
    Cx(&1 / &840) * ((x1 + x2 + x3 + x4) pow 8 +
                     (x1 + x2 + x3 - x4) pow 8 +
                     (x1 + x2 - x3 + x4) pow 8 +
                     (x1 + x2 - x3 - x4) pow 8 +
                     (x1 - x2 + x3 + x4) pow 8 +
                     (x1 - x2 + x3 - x4) pow 8 +
                     (x1 - x2 - x3 + x4) pow 8 +
                     (x1 - x2 - x3 - x4) pow 8) +
    Cx(&1 / &5040) * ((Cx(&2) * x1 + x2 + x3) pow 8 +
                      (Cx(&2) * x1 + x2 - x3) pow 8 +
                      (Cx(&2) * x1 - x2 + x3) pow 8 +
                      (Cx(&2) * x1 - x2 - x3) pow 8 +
                      (Cx(&2) * x1 + x2 + x4) pow 8 +
                      (Cx(&2) * x1 + x2 - x4) pow 8 +
                      (Cx(&2) * x1 - x2 + x4) pow 8 +
                      (Cx(&2) * x1 - x2 - x4) pow 8 +
                      (Cx(&2) * x1 + x3 + x4) pow 8 +
                      (Cx(&2) * x1 + x3 - x4) pow 8 +
                      (Cx(&2) * x1 - x3 + x4) pow 8 +
                      (Cx(&2) * x1 - x3 - x4) pow 8 +
                      (Cx(&2) * x2 + x3 + x4) pow 8 +
                      (Cx(&2) * x2 + x3 - x4) pow 8 +
                      (Cx(&2) * x2 - x3 + x4) pow 8 +
                      (Cx(&2) * x2 - x3 - x4) pow 8 +
                      (x1 + Cx(&2) * x2 + x3) pow 8 +
                      (x1 + Cx(&2) * x2 - x3) pow 8 +
                      (x1 - Cx(&2) * x2 + x3) pow 8 +
                      (x1 - Cx(&2) * x2 - x3) pow 8 +
                      (x1 + Cx(&2) * x2 + x4) pow 8 +
                      (x1 + Cx(&2) * x2 - x4) pow 8 +
                      (x1 - Cx(&2) * x2 + x4) pow 8 +
                      (x1 - Cx(&2) * x2 - x4) pow 8 +
                      (x1 + Cx(&2) * x3 + x4) pow 8 +
                      (x1 + Cx(&2) * x3 - x4) pow 8 +
                      (x1 - Cx(&2) * x3 + x4) pow 8 +
                      (x1 - Cx(&2) * x3 - x4) pow 8 +
                      (x2 + Cx(&2) * x3 + x4) pow 8 +
                      (x2 + Cx(&2) * x3 - x4) pow 8 +
                      (x2 - Cx(&2) * x3 + x4) pow 8 +
                      (x2 - Cx(&2) * x3 - x4) pow 8 +
                      (x1 + x2 + Cx(&2) * x3) pow 8 +
                      (x1 + x2 - Cx(&2) * x3) pow 8 +
                      (x1 - x2 + Cx(&2) * x3) pow 8 +
                      (x1 - x2 - Cx(&2) * x3) pow 8 +
                      (x1 + x2 + Cx(&2) * x4) pow 8 +
                      (x1 + x2 - Cx(&2) * x4) pow 8 +
                      (x1 - x2 + Cx(&2) * x4) pow 8 +
                      (x1 - x2 - Cx(&2) * x4) pow 8 +
                      (x1 + x3 + Cx(&2) * x4) pow 8 +
                      (x1 + x3 - Cx(&2) * x4) pow 8 +
                      (x1 - x3 + Cx(&2) * x4) pow 8 +
                      (x1 - x3 - Cx(&2) * x4) pow 8 +
                      (x2 + x3 + Cx(&2) * x4) pow 8 +
                      (x2 + x3 - Cx(&2) * x4) pow 8 +
                      (x2 - x3 + Cx(&2) * x4) pow 8 +
                      (x2 - x3 - Cx(&2) * x4) pow 8) +
     Cx(&1 / &84) * ((x1 + x2) pow 8 + (x1 - x2) pow 8 +
                     (x1 + x3) pow 8 + (x1 - x3) pow 8 +
                     (x1 + x4) pow 8 + (x1 - x4) pow 8 +
                     (x2 + x3) pow 8 + (x2 - x3) pow 8 +
                     (x2 + x4) pow 8 + (x2 - x4) pow 8 +
                     (x3 + x4) pow 8 + (x3 - x4) pow 8) +
     Cx(&1 / &840) * ((Cx(&2) * x1) pow 8 + (Cx(&2) * x2) pow 8 +
                      (Cx(&2) * x3) pow 8 + (Cx(&2) * x4) pow 8)|} ];;

let vSCHUR = time vCOMPLEX_ARITH
 [%q {|Cx(&22680) * (x1 pow 2 + x2 pow 2 + x3 pow 2 + x4 pow 2) pow 5 =
  Cx(&9) * ((Cx(&2) * x1) pow 10 +
            (Cx(&2) * x2) pow 10 +
            (Cx(&2) * x3) pow 10 +
            (Cx(&2) * x4) pow 10) +
  Cx(&180) * ((x1 + x2) pow 10 + (x1 - x2) pow 10 +
              (x1 + x3) pow 10 + (x1 - x3) pow 10 +
              (x1 + x4) pow 10 + (x1 - x4) pow 10 +
              (x2 + x3) pow 10 + (x2 - x3) pow 10 +
              (x2 + x4) pow 10 + (x2 - x4) pow 10 +
              (x3 + x4) pow 10 + (x3 - x4) pow 10) +
  ((Cx(&2) * x1 + x2 + x3) pow 10 +
   (Cx(&2) * x1 + x2 - x3) pow 10 +
   (Cx(&2) * x1 - x2 + x3) pow 10 +
   (Cx(&2) * x1 - x2 - x3) pow 10 +
   (Cx(&2) * x1 + x2 + x4) pow 10 +
   (Cx(&2) * x1 + x2 - x4) pow 10 +
   (Cx(&2) * x1 - x2 + x4) pow 10 +
   (Cx(&2) * x1 - x2 - x4) pow 10 +
   (Cx(&2) * x1 + x3 + x4) pow 10 +
   (Cx(&2) * x1 + x3 - x4) pow 10 +
   (Cx(&2) * x1 - x3 + x4) pow 10 +
   (Cx(&2) * x1 - x3 - x4) pow 10 +
   (Cx(&2) * x2 + x3 + x4) pow 10 +
   (Cx(&2) * x2 + x3 - x4) pow 10 +
   (Cx(&2) * x2 - x3 + x4) pow 10 +
   (Cx(&2) * x2 - x3 - x4) pow 10 +
   (x1 + Cx(&2) * x2 + x3) pow 10 +
   (x1 + Cx(&2) * x2 - x3) pow 10 +
   (x1 - Cx(&2) * x2 + x3) pow 10 +
   (x1 - Cx(&2) * x2 - x3) pow 10 +
   (x1 + Cx(&2) * x2 + x4) pow 10 +
   (x1 + Cx(&2) * x2 - x4) pow 10 +
   (x1 - Cx(&2) * x2 + x4) pow 10 +
   (x1 - Cx(&2) * x2 - x4) pow 10 +
   (x1 + Cx(&2) * x3 + x4) pow 10 +
   (x1 + Cx(&2) * x3 - x4) pow 10 +
   (x1 - Cx(&2) * x3 + x4) pow 10 +
   (x1 - Cx(&2) * x3 - x4) pow 10 +
   (x2 + Cx(&2) * x3 + x4) pow 10 +
   (x2 + Cx(&2) * x3 - x4) pow 10 +
   (x2 - Cx(&2) * x3 + x4) pow 10 +
   (x2 - Cx(&2) * x3 - x4) pow 10 +
   (x1 + x2 + Cx(&2) * x3) pow 10 +
   (x1 + x2 - Cx(&2) * x3) pow 10 +
   (x1 - x2 + Cx(&2) * x3) pow 10 +
   (x1 - x2 - Cx(&2) * x3) pow 10 +
   (x1 + x2 + Cx(&2) * x4) pow 10 +
   (x1 + x2 - Cx(&2) * x4) pow 10 +
   (x1 - x2 + Cx(&2) * x4) pow 10 +
   (x1 - x2 - Cx(&2) * x4) pow 10 +
   (x1 + x3 + Cx(&2) * x4) pow 10 +
   (x1 + x3 - Cx(&2) * x4) pow 10 +
   (x1 - x3 + Cx(&2) * x4) pow 10 +
   (x1 - x3 - Cx(&2) * x4) pow 10 +
   (x2 + x3 + Cx(&2) * x4) pow 10 +
   (x2 + x3 - Cx(&2) * x4) pow 10 +
   (x2 - x3 + Cx(&2) * x4) pow 10 +
   (x2 - x3 - Cx(&2) * x4) pow 10) +
  Cx(&9) * ((x1 + x2 + x3 + x4) pow 10 +
            (x1 + x2 + x3 - x4) pow 10 +
            (x1 + x2 - x3 + x4) pow 10 +
            (x1 + x2 - x3 - x4) pow 10 +
            (x1 - x2 + x3 + x4) pow 10 +
            (x1 - x2 + x3 - x4) pow 10 +
            (x1 - x2 - x3 + x4) pow 10 +
            (x1 - x2 - x3 - x4) pow 10)|} ];;

(* ------------------------------------------------------------------------- *)
(* Intersection of diagonals of a parallelogram is their midpoint.           *)
(* Kapur "...Dixon resultants, Groebner Bases, and Characteristic Sets", 3.1 *)
(* ------------------------------------------------------------------------- *)

time vCOMPLEX_ARITH
 [%q {|(x1 = u3) /\
  (x1 * (u2 - u1) = x2 * u3) /\
  (x4 * (x2 - u1) = x1 * (x3 - u1)) /\
  (x3 * u3 = x4 * u2) /\
  ~(u1 = Cx(&0)) /\
  ~(u3 = Cx(&0))
  ==> (x3 pow 2 + x4 pow 2 = (u2 - x3) pow 2 + (u3 - x4) pow 2)|} ];;

(* ------------------------------------------------------------------------- *)
(* Chou's formulation of same property.                                      *)
(* ------------------------------------------------------------------------- *)

time vCOMPLEX_ARITH
 [%q {|(u1 * x1 - u1 * u3 = Cx(&0)) /\
  (u3 * x2 - (u2 - u1) * x1 = Cx(&0)) /\
  (x1 * x4 - (x2 - u1) * x3 - u1 * x1 = Cx(&0)) /\
  (u3 * x4 - u2 * x3 = Cx(&0)) /\
  ~(u1 = Cx(&0)) /\
  ~(u3 = Cx(&0))
  ==> (Cx(&2) * u2 * x4 + Cx(&2) * u3 * x3 - u3 pow 2 - u2 pow 2 = Cx(&0))|} ];;

(* ------------------------------------------------------------------------- *)
(* Perpendicular lines property; from Kapur's earlier paper.                 *)
(* ------------------------------------------------------------------------- *)

time vCOMPLEX_ARITH
 [%q {|(y1 * y3 + x1 * x3 = Cx(&0)) /\
  (y3 * (y2 - y3) + (x2 - x3) * x3 = Cx(&0)) /\
  ~(x3 = Cx(&0)) /\
  ~(y3 = Cx(&0))
  ==> (y1 * (x2 - x3) = x1 * (y2 - y3))|} ];;

(* ------------------------------------------------------------------------- *)
(* Simson's theorem (Chou, p7).                                              *)
(* ------------------------------------------------------------------------- *)

time vCOMPLEX_ARITH
 [%q {|(Cx(&2) * u2 * x2 + Cx(&2) * u3 * x1 - u3 pow 2 - u2 pow 2 = Cx(&0)) /\
  (Cx(&2) * u1 * x2 - u1 pow 2 = Cx(&0)) /\
  (--(x3 pow 2) + Cx(&2) * x2 * x3 + Cx(&2) * u4 * x1 - u4 pow 2 = Cx(&0)) /\
  (u3 * x5 + (--u2 + u1) * x4 - u1 * u3 = Cx(&0)) /\
  ((u2 - u1) * x5 + u3 * x4 + (--u2 + u1) * x3 - u3 * u4 = Cx(&0)) /\
  (u3 * x7 - u2 * x6 = Cx(&0)) /\
  (u2 * x7 + u3 * x6 - u2 * x3 - u3 * u4 = Cx(&0)) /\
  ~(Cx(&4) * u1 * u3 = Cx(&0)) /\
  ~(Cx(&2) * u1 = Cx(&0)) /\
  ~(--(u3 pow 2) - u2 pow 2 + Cx(&2) * u1 * u2 - u1 pow 2 = Cx(&0)) /\
  ~(u3 = Cx(&0)) /\
  ~(--(u3 pow 2) - u2 pow 2 = Cx(&0)) /\
  ~(u2 = Cx(&0))
  ==> (x4 * x7 + (--x5 + x3) * x6 - x3 * x4 = Cx(&0))|} ];;

(* ------------------------------------------------------------------------- *)
(* Determinants from Coq convex hull paper (some require reals or order).    *)
(* ------------------------------------------------------------------------- *)

let det3 = new_definition
  [%q {|det3(a11,a12,a13,
        a21,a22,a23,
        a31,a32,a33) =
    a11 * (a22 * a33 - a32 * a23) -
    a12 * (a21 * a33 - a31 * a23) +
    a13 * (a21 * a32 - a31 * a22)|} ];;

let vDET_TRANSPOSE = prove
 ([%q {|det3(a1,b1,c1,a2,b2,c2,a3,b3,c3) =
   det3(a1,a2,a3,b1,b2,b3,c1,c2,c3)|} ],
  vREWRITE_TAC[det3] ----> vCONV_TAC(time vCOMPLEX_ARITH));;

let sdet3 = new_definition
  [%q {|sdet3(p,q,r) = det3(FST p,SND p,Cx(&1),
                       FST q,SND q,Cx(&1),
                       FST r,SND r,Cx(&1))|} ];;

let vSDET3_PERMUTE_1 = prove
 ([%q {|sdet3(p,q,r) = sdet3(q,r,p)|} ],
  vREWRITE_TAC[sdet3; det3] ----> vCONV_TAC(time vCOMPLEX_ARITH));;

let vSDET3_PERMUTE_2 = prove
 ([%q {|sdet3(p,q,r) = --(sdet3(p,r,q))|} ],
  vREWRITE_TAC[sdet3; det3] ----> vCONV_TAC(time vCOMPLEX_ARITH));;

let vSDET_SUM = prove
 ([%q {|sdet3(p,q,r) - sdet3(t,q,r) - sdet3(p,t,r) - sdet3(p,q,t) = Cx(&0)|} ],
  vREWRITE_TAC[sdet3; det3] ----> vCONV_TAC(time vCOMPLEX_ARITH));;

let vSDET_CRAMER = prove
 ([%q {|sdet3(s,t,q) * sdet3(t,p,r) = sdet3(t,q,r) * sdet3(s,t,p) +
                                 sdet3(t,p,q) * sdet3(s,t,r)|} ],
  vREWRITE_TAC[sdet3; det3] ----> vCONV_TAC(time vCOMPLEX_ARITH));;

let vSDET_NZ = prove
 ([%q {|!p q r. ~(sdet3(p,q,r) = Cx(&0))
           ==> ~(p = q) /\ ~(q = r) /\ ~(r = p)|} ],
  vREWRITE_TAC[vFORALL_PAIR_THM; vPAIR_EQ; sdet3; det3] ---->
  vCONV_TAC(time vCOMPLEX_ARITH));;

let vSDET_LINCOMB = prove
 ([%q {|(FST p * sdet3(i,j,k) =
    FST i * sdet3(j,k,p) + FST j * sdet3(k,i,p) + FST k * sdet3(i,j,p)) /\
   (SND p * sdet3(i,j,k) =
    SND i * sdet3(j,k,p) + SND j * sdet3(k,i,p) + SND k * sdet3(i,j,p))|} ],
  vREWRITE_TAC[sdet3; det3] ----> vCONV_TAC(time vCOMPLEX_ARITH));;

(***** I'm not sure if this is true; there must be some
       sufficient degenerate conditions....

let th = prove
 (`~(~(xp pow 2 + yp pow 2 = Cx(&0)) /\
     ~(xq pow 2 + yq pow 2 = Cx(&0)) /\
     ~(xr pow 2 + yr pow 2 = Cx(&0)) /\
     (det3(xp,yp,Cx(&1),
           xq,yq,Cx(&1),
           xr,yr,Cx(&1)) = Cx(&0)) /\
     (det3(yp,xp pow 2 + yp pow 2,Cx(&1),
           yq,xq pow 2 + yq pow 2,Cx(&1),
           yr,xr pow 2 + yr pow 2,Cx(&1)) = Cx(&0)) /\
     (det3(xp,xp pow 2 + yp pow 2,Cx(&1),
           xq,xq pow 2 + yq pow 2,Cx(&1),
           xr,xr pow 2 + yr pow 2,Cx(&1)) = Cx(&0)))`,
  REWRITE_TAC[det3] THEN
  CONV_TAC(time COMPLEX_ARITH));;

***************)

(* ------------------------------------------------------------------------- *)
(* Some geometry concepts (just "axiomatic" in this file).                   *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let collinear = new_definition
  [%q {|collinear (a:real#real) b c <=>
        ((FST a - FST b) * (SND b - SND c) =
         (SND a - SND b) * (FST b - FST c))|} ];;

let parallel = new_definition
  [%q {|parallel (a,b) (c,d) <=>
     ((FST a - FST b) * (SND c - SND d) = (SND a - SND b) * (FST c - FST d))|} ];;

let perpendicular = new_definition
  [%q {|perpendicular (a,b) (c,d) <=>
     ((FST a - FST b) * (FST c - FST d) + (SND a - SND b) * (SND c - SND d) =
      &0)|} ];;

let oncircle_with_diagonal = new_definition
  [%q {|oncircle_with_diagonal a (b,c) = perpendicular (b,a) (c,a)|} ];;

let length = new_definition
  [%q {|length (a,b) = sqrt((FST a - FST b) pow 2 + (SND a - SND b) pow 2)|} ];;

let lengths_eq = new_definition
  [%q {|lengths_eq (a,b) (c,d) <=>
        ((FST a - FST b) pow 2 + (SND a - SND b) pow 2 =
         (FST c - FST d) pow 2 + (SND c - SND d) pow 2)|} ];;

let is_midpoint = new_definition
  [%q {|is_midpoint b (a,c) <=>
     (&2 * FST b = FST a + FST c) /\
     (&2 * SND b = SND a + SND c)|} ];;

(* ------------------------------------------------------------------------- *)
(* Chou isn't explicit about this.                                           *)
(* ------------------------------------------------------------------------- *)

let is_intersection = new_definition
  [%q {|is_intersection p (a,b) (c,d) <=>
      collinear a p b /\ collinear c p d|} ];;

(* ------------------------------------------------------------------------- *)
(* This is used in some degenerate conditions. See Chou, p18.                *)
(* ------------------------------------------------------------------------- *)

let isotropic = new_definition
  [%q {|isotropic (a,b) = perpendicular (a,b) (a,b)|} ];;

(* ------------------------------------------------------------------------- *)
(* This increases degree, but sometimes makes complex assertion useful.      *)
(* ------------------------------------------------------------------------- *)

let distinctpairs = new_definition
  [%q {|distinctpairs pprs <=>
     ~(ITLIST (\(a,b) pr. ((FST a - FST b) pow 2 + (SND a - SND b) pow 2) * pr)
              pprs (&1) = &0)|} ];;

(* ------------------------------------------------------------------------- *)
(* Simple tactic to remove defined concepts and expand coordinates.          *)
(* ------------------------------------------------------------------------- *)

let (vEXPAND_COORDS_TAC:tactic) =
  let complex2_ty = [%q {|:real#real|} ] in
  fun (asl,w) ->
    (let fvs = filter (fun v -> type_of v = complex2_ty) (frees w) in
     vMAP_EVERY (fun v -> vSPEC_TAC(v,v)) fvs ---->
     vGEN_REWRITE_TAC vDEPTH_CONV [vFORALL_PAIR_THM; vEXISTS_PAIR_THM] ---->
     vREPEAT vGEN_TAC) (asl,w);;

let vPAIR_BETA_THM = prove
 ([%q {|(\(x,y). P x y) (a,b) = P a b|} ],
  vCONV_TAC(vLAND_CONV vGEN_BETA_CONV) ----> vREFL_TAC);;

let vGEOM_TAC =
  vEXPAND_COORDS_TAC ---->
  vGEN_REWRITE_TAC vTOP_DEPTH_CONV
   [collinear; parallel; perpendicular; oncircle_with_diagonal;
    length; lengths_eq; is_midpoint; is_intersection; distinctpairs;
    isotropic; vITLIST; vPAIR_BETA_THM; vBETA_THM; vPAIR_EQ; vFST; vSND];;

(* ------------------------------------------------------------------------- *)
(* Centroid (Chou, example 142).                                             *)
(* ------------------------------------------------------------------------- *)

let vCENTROID = time prove
 ([%q {|is_midpoint d (b,c) /\
   is_midpoint e (a,c) /\
   is_midpoint f (a,b) /\
   is_intersection m (b,e) (a,d)
   ==> collinear c f m|} ],
  vGEOM_TAC ----> vCONV_TAC vGROBNER_REAL_ARITH);;

(* ------------------------------------------------------------------------- *)
(* Gauss's theorem (Chou, example 15).                                       *)
(* ------------------------------------------------------------------------- *)

let vGAUSS = time prove
 ([%q {|collinear x a0 a3 /\
   collinear x a1 a2 /\
   collinear y a2 a3 /\
   collinear y a1 a0 /\
   is_midpoint m1 (a1,a3) /\
   is_midpoint m2 (a0,a2) /\
   is_midpoint m3 (x,y)
   ==> collinear m1 m2 m3|} ],
  vGEOM_TAC ----> vCONV_TAC vGROBNER_REAL_ARITH);;

(* ------------------------------------------------------------------------- *)
(* Simson's theorem (Chou, example 288).                                     *)
(* ------------------------------------------------------------------------- *)

(**** These are all hideously slow. At least the first one works.
      I haven't had the patience to try the rest.

let SIMSON = time prove
 (`lengths_eq (O,a) (O,b) /\
   lengths_eq (O,a) (O,c) /\
   lengths_eq (d,O) (O,a) /\
   perpendicular (e,d) (b,c) /\
   collinear e b c /\
   perpendicular (f,d) (a,c) /\
   collinear f a c /\
   perpendicular (g,d) (a,b) /\
   collinear g a b /\
   ~(collinear a c b) /\
   ~(lengths_eq (a,b) (a,a)) /\
   ~(lengths_eq (a,c) (a,a)) /\
   ~(lengths_eq (b,c) (a,a))
   ==> collinear e f g`,
  GEOM_TAC THEN CONV_TAC GROBNER_REAL_ARITH);;

let SIMSON = time prove
 (`lengths_eq (O,a) (O,b) /\
   lengths_eq (O,a) (O,c) /\
   lengths_eq (d,O) (O,a) /\
   perpendicular (e,d) (b,c) /\
   collinear e b c /\
   perpendicular (f,d) (a,c) /\
   collinear f a c /\
   perpendicular (g,d) (a,b) /\
   collinear g a b /\
   ~(a = b) /\ ~(a = c) /\ ~(a = d) /\ ~(b = c) /\ ~(b = d) /\ ~(c = d)
   ==> collinear e f g`,
  GEOM_TAC THEN CONV_TAC GROBNER_REAL_ARITH);;

let SIMSON = time prove
 (`lengths_eq (O,a) (O,b) /\
   lengths_eq (O,a) (O,c) /\
   lengths_eq (d,O) (O,a) /\
   perpendicular (e,d) (b,c) /\
   collinear e b c /\
   perpendicular (f,d) (a,c) /\
   collinear f a c /\
   perpendicular (g,d) (a,b) /\
   collinear g a b /\
   ~(collinear a c b) /\
   ~(isotropic (a,b)) /\
   ~(isotropic (a,c)) /\
   ~(isotropic (b,c)) /\
   ~(isotropic (a,d)) /\
   ~(isotropic (b,d)) /\
   ~(isotropic (c,d))
   ==> collinear e f g`,
  GEOM_TAC THEN CONV_TAC GROBNER_REAL_ARITH);;

****************)
