(* ========================================================================= *)
(* Definition of finite Cartesian product types.                             *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*     (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018              *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Printer
open Parser
open Equal
open Boolean
open Drule
open Tactics
open Simp
open Theorems
open Class
open Trivia
open Meson
open Pair
open Nums
open Arith
open Calc_num
open Ind_types
open Int
open Sets
open Iterate

(* ------------------------------------------------------------------------- *)
(* Association of a number with an indexing type.                            *)
(* ------------------------------------------------------------------------- *)

let dimindex = new_definition
  (parse_term "dimindex(s:A->bool) = if FINITE(:A) then CARD(:A) else 1");;

let vDIMINDEX_NONZERO = try Cache.lookup_thm "DIMINDEX_NONZERO" with _ ->  prove
 ((parse_term "!s:A->bool. ~(dimindex(s) = 0)"),
  vGEN_TAC ----> vREWRITE_TAC[dimindex] ---->
  vCOND_CASES_TAC ----> vASM_SIMP_TAC[vCARD_EQ_0; vARITH] ----> vSET_TAC[]);;

let vDIMINDEX_GE_1 = try Cache.lookup_thm "DIMINDEX_GE_1" with _ ->  prove
 ((parse_term "!s:A->bool. 1 <= dimindex(s)"),
  vREWRITE_TAC[vARITH_RULE (parse_term "1 <= x <=> ~(x = 0)"); vDIMINDEX_NONZERO]);;

let vDIMINDEX_UNIV = try Cache.lookup_thm "DIMINDEX_UNIV" with _ ->  prove
 ((parse_term "!s. dimindex(s:A->bool) = dimindex(:A)"),
  vREWRITE_TAC[dimindex]);;

let vDIMINDEX_UNIQUE = try Cache.lookup_thm "DIMINDEX_UNIQUE" with _ ->  prove
 ((parse_term "(:A) HAS_SIZE n ==> dimindex(:A) = n"),
  vMESON_TAC[dimindex; vHAS_SIZE]);;

let vUNIV_HAS_SIZE_DIMINDEX = try Cache.lookup_thm "UNIV_HAS_SIZE_DIMINDEX" with _ ->  prove
 ((parse_term "(:N) HAS_SIZE dimindex (:N) <=> FINITE(:N)"),
  vMESON_TAC[vHAS_SIZE; dimindex]);;

let vHAS_SIZE_1 = try Cache.lookup_thm "HAS_SIZE_1" with _ ->  prove
 ((parse_term "(:1) HAS_SIZE 1"),
  vSUBGOAL_THEN (parse_term "(:1) = {one}") vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_SING] ----> vMESON_TAC[one];
    vSIMP_TAC[vNOT_IN_EMPTY; vHAS_SIZE; vFINITE_RULES; vCARD_CLAUSES; vARITH]]);;

let vDIMINDEX_1 = try Cache.lookup_thm "DIMINDEX_1" with _ ->  vMATCH_MP vDIMINDEX_UNIQUE vHAS_SIZE_1;;

(* ------------------------------------------------------------------------- *)
(* An indexing type with that size, parametrized by base type.               *)
(* ------------------------------------------------------------------------- *)

let finite_image_tybij =
  new_type_definition "finite_image" ("finite_index","dest_finite_image")
  (prove
   ((parse_term "?x. x IN 1..dimindex(:A)"),
    vEXISTS_TAC (parse_term "1") ----> vREWRITE_TAC[vIN_NUMSEG; vLE_REFL; vDIMINDEX_GE_1]));;

let vFINITE_IMAGE_IMAGE = try Cache.lookup_thm "FINITE_IMAGE_IMAGE" with _ ->  prove
 ((parse_term "UNIV:(A)finite_image->bool = IMAGE finite_index (1..dimindex(:A))"),
  vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_IMAGE] ---->
  vMESON_TAC[finite_image_tybij]);;

(* ------------------------------------------------------------------------- *)
(* Dimension of such a type, and indexing over it.                           *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_FINITE_IMAGE = try Cache.lookup_thm "HAS_SIZE_FINITE_IMAGE" with _ ->  prove
 ((parse_term "!s. (UNIV:(A)finite_image->bool) HAS_SIZE dimindex(s:A->bool)"),
  vGEN_TAC ----> vSIMP_TAC[vFINITE_IMAGE_IMAGE] ---->
  vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ---->
  vONCE_REWRITE_TAC[vDIMINDEX_UNIV] ----> vREWRITE_TAC[vHAS_SIZE_NUMSEG_1] ---->
  vMESON_TAC[finite_image_tybij]);;

let vCARD_FINITE_IMAGE = try Cache.lookup_thm "CARD_FINITE_IMAGE" with _ ->  prove
 ((parse_term "!s. CARD(UNIV:(A)finite_image->bool) = dimindex(s:A->bool)"),
  vMESON_TAC[vHAS_SIZE_FINITE_IMAGE; vHAS_SIZE]);;

let vFINITE_FINITE_IMAGE = try Cache.lookup_thm "FINITE_FINITE_IMAGE" with _ ->  prove
 ((parse_term "FINITE(UNIV:(A)finite_image->bool)"),
  vMESON_TAC[vHAS_SIZE_FINITE_IMAGE; vHAS_SIZE]);;

let vDIMINDEX_FINITE_IMAGE = try Cache.lookup_thm "DIMINDEX_FINITE_IMAGE" with _ ->  prove
 ((parse_term "!s t. dimindex(s:(A)finite_image->bool) = dimindex(t:A->bool)"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vLAND_CONV [dimindex] ---->
  vMP_TAC(vISPEC (parse_term "t:A->bool") vHAS_SIZE_FINITE_IMAGE) ---->
  vSIMP_TAC[vFINITE_FINITE_IMAGE; vHAS_SIZE]);;

let vFINITE_INDEX_WORKS = try Cache.lookup_thm "FINITE_INDEX_WORKS" with _ ->  prove
 ((parse_term "!i:(A)finite_image.\n        ?!n. 1 <= n /\\ n <= dimindex(:A) /\\ (finite_index n = i)"),
  vREWRITE_TAC[vCONJ_ASSOC; vGSYM vIN_NUMSEG] ----> vMESON_TAC[finite_image_tybij]);;

let vFINITE_INDEX_INJ = try Cache.lookup_thm "FINITE_INDEX_INJ" with _ ->  prove
 ((parse_term "!i j. 1 <= i /\\ i <= dimindex(:A) /\\\n         1 <= j /\\ j <= dimindex(:A)\n         ==> ((finite_index i :A finite_image = finite_index j) <=>\n              (i = j))"),
  vMESON_TAC[vFINITE_INDEX_WORKS]);;

let vFORALL_FINITE_INDEX = try Cache.lookup_thm "FORALL_FINITE_INDEX" with _ ->  prove
 ((parse_term "(!k:(N)finite_image. P k) =\n   (!i. 1 <= i /\\ i <= dimindex(:N) ==> P(finite_index i))"),
  vMESON_TAC[vFINITE_INDEX_WORKS]);;

(* ------------------------------------------------------------------------- *)
(* Hence finite Cartesian products, with indexing and lambdas.               *)
(* ------------------------------------------------------------------------- *)

let cart_tybij =
  new_type_definition "cart" ("mk_cart","dest_cart")
   (prove((parse_term "?f:(B)finite_image->A. T"),vREWRITE_TAC[]));;

parse_as_infix("$",(25,"left"));;

let finite_index = new_definition
  (parse_term "x$i = dest_cart x (finite_index i)");;

let vCART_EQ = try Cache.lookup_thm "CART_EQ" with _ ->  prove
 ((parse_term "!x:A^B y.\n    (x = y) <=> !i. 1 <= i /\\ i <= dimindex(:B) ==> (x$i = y$i)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[finite_index; vGSYM vFORALL_FINITE_INDEX] ---->
  vREWRITE_TAC[vGSYM vFUN_EQ_THM; vETA_AX] ----> vMESON_TAC[cart_tybij]);;

parse_as_binder "lambda";;

let lambda = new_definition
  (parse_term "(lambda) g =\n     @f:A^B. !i. 1 <= i /\\ i <= dimindex(:B) ==> (f$i = g i)");;

let vLAMBDA_BETA = try Cache.lookup_thm "LAMBDA_BETA" with _ ->  prove
 ((parse_term "!i. 1 <= i /\\ i <= dimindex(:B)\n       ==> (((lambda) g:A^B) $i = g i)"),
  vREWRITE_TAC[lambda] ----> vCONV_TAC vSELECT_CONV ---->
  vEXISTS_TAC (parse_term "mk_cart(\\k. g(@i. 1 <= i /\\  i <= dimindex(:B) /\\\n                                (finite_index i = k))):A^B") ---->
  vREWRITE_TAC[finite_index; vREWRITE_RULE[] cart_tybij] ---->
  vREPEAT vSTRIP_TAC ----> vAP_TERM_TAC ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vGEN_TAC ----> vREWRITE_TAC[] ---->
  vASM_MESON_TAC[vFINITE_INDEX_INJ; vDIMINDEX_FINITE_IMAGE]);;

let vLAMBDA_UNIQUE = try Cache.lookup_thm "LAMBDA_UNIQUE" with _ ->  prove
 ((parse_term "!f:A^B g.\n        (!i. 1 <= i /\\ i <= dimindex(:B) ==> (f$i = g i)) <=>\n        ((lambda) g = f)"),
  vSIMP_TAC[vCART_EQ; vLAMBDA_BETA] ----> vMESON_TAC[]);;

let vLAMBDA_ETA = try Cache.lookup_thm "LAMBDA_ETA" with _ ->  prove
 ((parse_term "!g. (lambda i. g$i) = g"),
  vREWRITE_TAC[vCART_EQ; vLAMBDA_BETA]);;

(* ------------------------------------------------------------------------- *)
(* For some purposes we can avoid side-conditions on the index.              *)
(* ------------------------------------------------------------------------- *)

let vFINITE_INDEX_INRANGE = try Cache.lookup_thm "FINITE_INDEX_INRANGE" with _ ->  prove
 ((parse_term "!i. ?k. 1 <= k /\\ k <= dimindex(:N) /\\ !x:A^N. x$i = x$k"),
  vREWRITE_TAC[finite_index] ----> vMESON_TAC[vFINITE_INDEX_WORKS]);;

let vFINITE_INDEX_INRANGE_2 = try Cache.lookup_thm "FINITE_INDEX_INRANGE_2" with _ ->  prove
 ((parse_term "!i. ?k. 1 <= k /\\ k <= dimindex(:N) /\\\n           (!x:A^N. x$i = x$k) /\\ (!y:B^N. y$i = y$k)"),
  vREWRITE_TAC[finite_index] ----> vMESON_TAC[vFINITE_INDEX_WORKS]);;

let vCART_EQ_FULL = try Cache.lookup_thm "CART_EQ_FULL" with _ ->  prove
 ((parse_term "!x y:A^N. x = y <=> !i. x$i = y$i"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vSIMP_TAC[] ----> vSIMP_TAC[vCART_EQ]);;

(* ------------------------------------------------------------------------- *)
(* We need a non-standard sum to "paste" together Cartesian products.        *)
(* ------------------------------------------------------------------------- *)

let finite_sum_tybij =
  let th = prove
   ((parse_term "?x. x IN 1..(dimindex(:A) + dimindex(:B))"),
    vEXISTS_TAC (parse_term "1") ----> vSIMP_TAC[vIN_NUMSEG; vLE_REFL; vDIMINDEX_GE_1;
      vARITH_RULE (parse_term "1 <= a ==> 1 <= a + b")]) in
  new_type_definition "finite_sum" ("mk_finite_sum","dest_finite_sum") th;;

let pastecart = new_definition
  (parse_term "(pastecart:A^M->A^N->A^(M,N)finite_sum) f g =\n        lambda i. if i <= dimindex(:M) then f$i\n                  else g$(i - dimindex(:M))");;

let fstcart = new_definition
  (parse_term "(fstcart:A^(M,N)finite_sum->A^M) f = lambda i. f$i");;

let sndcart = new_definition
  (parse_term "(sndcart:A^(M,N)finite_sum->A^N) f =\n        lambda i. f$(i + dimindex(:M))");;

let vFINITE_SUM_IMAGE = try Cache.lookup_thm "FINITE_SUM_IMAGE" with _ ->  prove
 ((parse_term "UNIV:(A,B)finite_sum->bool =\n       IMAGE mk_finite_sum (1..(dimindex(:A)+dimindex(:B)))"),
  vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_IMAGE] ---->
  vMESON_TAC[finite_sum_tybij]);;

let vDIMINDEX_HAS_SIZE_FINITE_SUM = try Cache.lookup_thm "DIMINDEX_HAS_SIZE_FINITE_SUM" with _ ->  prove
 ((parse_term "(UNIV:(M,N)finite_sum->bool) HAS_SIZE (dimindex(:M) + dimindex(:N))"),
  vSIMP_TAC[vFINITE_SUM_IMAGE] ---->
  vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ---->
  vONCE_REWRITE_TAC[vDIMINDEX_UNIV] ----> vREWRITE_TAC[vHAS_SIZE_NUMSEG_1] ---->
  vMESON_TAC[finite_sum_tybij]);;

let vDIMINDEX_FINITE_SUM = try Cache.lookup_thm "DIMINDEX_FINITE_SUM" with _ ->  prove
 ((parse_term "dimindex(:(M,N)finite_sum) = dimindex(:M) + dimindex(:N)"),
  vGEN_REWRITE_TAC vLAND_CONV [dimindex] ---->
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vDIMINDEX_HAS_SIZE_FINITE_SUM]);;

let vFSTCART_PASTECART = try Cache.lookup_thm "FSTCART_PASTECART" with _ ->  prove
 ((parse_term "!x y. fstcart(pastecart (x:A^M) (y:A^N)) = x"),
  vSIMP_TAC[pastecart; fstcart; vCART_EQ; vLAMBDA_BETA; vDIMINDEX_FINITE_SUM;
           vARITH_RULE (parse_term "a <= b ==> a <= b + c")]);;

let vSNDCART_PASTECART = try Cache.lookup_thm "SNDCART_PASTECART" with _ ->  prove
 ((parse_term "!x y. sndcart(pastecart (x:A^M) (y:A^N)) = y"),
  vSIMP_TAC[pastecart; sndcart; vCART_EQ; vLAMBDA_BETA] ----> vREPEAT vSTRIP_TAC ---->
  vW(fun (_,w) -> vMP_TAC (vPART_MATCH (lhs -| rand) vLAMBDA_BETA (lhand w))) ---->
  vANTS_TAC ++-->
   [vREWRITE_TAC[vDIMINDEX_FINITE_SUM] ----> vMATCH_MP_TAC
     (vARITH_RULE (parse_term "1 <= i /\\ i <= b ==> 1 <= i + a /\\ i + a <= a + b")) ---->
    vASM_REWRITE_TAC[];
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[] ---->
    vASM_SIMP_TAC[vADD_SUB; vARITH_RULE (parse_term "1 <= i ==> ~(i + a <= a)")]]);;

let vPASTECART_FST_SND = try Cache.lookup_thm "PASTECART_FST_SND" with _ ->  prove
 ((parse_term "!z. pastecart (fstcart z) (sndcart z) = z"),
  vSIMP_TAC[pastecart; fstcart; sndcart; vCART_EQ; vLAMBDA_BETA] ---->
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
  vASM_SIMP_TAC[vDIMINDEX_FINITE_SUM; vLAMBDA_BETA;
     vARITH_RULE (parse_term "i <= a + b ==> i - a <= b");
     vARITH_RULE (parse_term "~(i <= a) ==> 1 <= i - a");
     vARITH_RULE (parse_term "~(i <= a) ==> ((i - a) + a = i)")]);;

let vPASTECART_EQ = try Cache.lookup_thm "PASTECART_EQ" with _ ->  prove
 ((parse_term "!x y. (x = y) <=> (fstcart x = fstcart y) /\\ (sndcart x = sndcart y)"),
  vMESON_TAC[vPASTECART_FST_SND]);;

let vFORALL_PASTECART = try Cache.lookup_thm "FORALL_PASTECART" with _ ->  prove
 ((parse_term "(!p. P p) <=> !x y. P (pastecart x y)"),
  vMESON_TAC[vPASTECART_FST_SND; vFSTCART_PASTECART; vSNDCART_PASTECART]);;

let vEXISTS_PASTECART = try Cache.lookup_thm "EXISTS_PASTECART" with _ ->  prove
 ((parse_term "(?p. P p) <=> ?x y. P (pastecart x y)"),
  vMESON_TAC[vPASTECART_FST_SND; vFSTCART_PASTECART; vSNDCART_PASTECART]);;

let vPASTECART_INJ = try Cache.lookup_thm "PASTECART_INJ" with _ ->  prove
 ((parse_term "!x:A^M y:A^N w z. pastecart x y = pastecart w z <=> x = w /\\ y = z"),
  vREWRITE_TAC[vPASTECART_EQ; vFSTCART_PASTECART; vSNDCART_PASTECART]);;

let vFSTCART_COMPONENT = try Cache.lookup_thm "FSTCART_COMPONENT" with _ ->  prove
 ((parse_term "!x:A^(M,N)finite_sum i. 1 <= i /\\ i <= dimindex(:M)\n                           ==> fstcart x$i = x$i"),
  vSIMP_TAC[fstcart; vLAMBDA_BETA]);;

let vSNDCART_COMPONENT = try Cache.lookup_thm "SNDCART_COMPONENT" with _ ->  prove
 ((parse_term "!x:A^(M,N)finite_sum i. 1 <= i /\\ i <= dimindex(:N)\n                           ==> sndcart x$i = x$(i + dimindex(:M))"),
  vSIMP_TAC[sndcart; vLAMBDA_BETA]);;

let vPASTECART_COMPONENT = try Cache.lookup_thm "PASTECART_COMPONENT" with _ ->  prove
 ((parse_term "(!u:A^M v:A^N i. 1 <= i /\\ i <= dimindex(:M) ==> pastecart u v$i = u$i) /\\\n   (!u:A^M v:A^N i. dimindex(:M) + 1 <= i /\\ i <= dimindex(:M) + dimindex(:N)\n                    ==> pastecart u v$i = v$(i - dimindex(:M)))"),
  vREWRITE_TAC[pastecart] ----> vCONJ_TAC ----> vREPEAT vGEN_TAC ----> vSTRIP_TAC ++-->
  [vSUBGOAL_THEN (parse_term "i <= dimindex(:(M,N)finite_sum)")
     (fun th -> vASM_SIMP_TAC[vLAMBDA_BETA; th]) ---->
   vREWRITE_TAC[vDIMINDEX_FINITE_SUM] ----> vASM_ARITH_TAC;
   vASM_SIMP_TAC[vLAMBDA_BETA; vDIMINDEX_FINITE_SUM;
                vARITH_RULE (parse_term "dimindex(:M) + 1 <= i ==> 1 <= i")] ---->
   vCOND_CASES_TAC ----> vREWRITE_TAC[] ----> vASM_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Likewise a "subtraction" function on type indices.                        *)
(* ------------------------------------------------------------------------- *)

let finite_diff_tybij =
  let th = prove
   ((parse_term "?x. x IN 1..(if dimindex(:B) < dimindex(:A)\n                  then dimindex(:A) - dimindex(:B) else 1)"),
    vEXISTS_TAC (parse_term "1") ----> vREWRITE_TAC[vIN_NUMSEG] ----> vARITH_TAC) in
  new_type_definition "finite_diff" ("mk_finite_diff","dest_finite_diff") th;;

let vFINITE_DIFF_IMAGE = try Cache.lookup_thm "FINITE_DIFF_IMAGE" with _ ->  prove
 ((parse_term "UNIV:(A,B)finite_diff->bool =\n       IMAGE mk_finite_diff\n       (1..(if dimindex(:B) < dimindex(:A)\n                  then dimindex(:A) - dimindex(:B) else 1))"),
  vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_IMAGE] ---->
  vMESON_TAC[finite_diff_tybij]);;

let vDIMINDEX_HAS_SIZE_FINITE_DIFF = try Cache.lookup_thm "DIMINDEX_HAS_SIZE_FINITE_DIFF" with _ ->  prove
 ((parse_term "(UNIV:(M,N)finite_diff->bool) HAS_SIZE\n   (if dimindex(:N) < dimindex(:M) then dimindex(:M) - dimindex(:N) else 1)"),
  vSIMP_TAC[vFINITE_DIFF_IMAGE] ---->
  vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ---->
  vONCE_REWRITE_TAC[vDIMINDEX_UNIV] ----> vREWRITE_TAC[vHAS_SIZE_NUMSEG_1] ---->
  vMESON_TAC[finite_diff_tybij]);;

let vDIMINDEX_FINITE_DIFF = try Cache.lookup_thm "DIMINDEX_FINITE_DIFF" with _ ->  prove
 ((parse_term "dimindex(:(M,N)finite_diff) =\n     if dimindex(:N) < dimindex(:M) then dimindex(:M) - dimindex(:N) else 1"),
  vGEN_REWRITE_TAC vLAND_CONV [dimindex] ---->
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vDIMINDEX_HAS_SIZE_FINITE_DIFF]);;

(* ------------------------------------------------------------------------- *)
(* And a finite-forcing "multiplication" on type indices.                    *)
(* ------------------------------------------------------------------------- *)

let finite_prod_tybij =
  let th = prove
   ((parse_term "?x. x IN 1..(dimindex(:A) * dimindex(:B))"),
     vEXISTS_TAC (parse_term "1") ----> vREWRITE_TAC[vIN_NUMSEG; vLE_REFL] ---->
     vMESON_TAC[vLE_1; vDIMINDEX_GE_1; vMULT_EQ_0]) in
  new_type_definition "finite_prod" ("mk_finite_prod","dest_finite_prod") th;;

let vFINITE_PROD_IMAGE = try Cache.lookup_thm "FINITE_PROD_IMAGE" with _ ->  prove
 ((parse_term "UNIV:(A,B)finite_prod->bool =\n       IMAGE mk_finite_prod (1..(dimindex(:A)*dimindex(:B)))"),
  vREWRITE_TAC[vEXTENSION; vIN_UNIV; vIN_IMAGE] ---->
  vMESON_TAC[finite_prod_tybij]);;

let vDIMINDEX_HAS_SIZE_FINITE_PROD = try Cache.lookup_thm "DIMINDEX_HAS_SIZE_FINITE_PROD" with _ ->  prove
 ((parse_term "(UNIV:(M,N)finite_prod->bool) HAS_SIZE (dimindex(:M) * dimindex(:N))"),
  vSIMP_TAC[vFINITE_PROD_IMAGE] ---->
  vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ---->
  vONCE_REWRITE_TAC[vDIMINDEX_UNIV] ----> vREWRITE_TAC[vHAS_SIZE_NUMSEG_1] ---->
  vMESON_TAC[finite_prod_tybij]);;

let vDIMINDEX_FINITE_PROD = try Cache.lookup_thm "DIMINDEX_FINITE_PROD" with _ ->  prove
 ((parse_term "dimindex(:(M,N)finite_prod) = dimindex(:M) * dimindex(:N)"),
  vGEN_REWRITE_TAC vLAND_CONV [dimindex] ---->
  vREWRITE_TAC[vREWRITE_RULE[vHAS_SIZE] vDIMINDEX_HAS_SIZE_FINITE_PROD]);;

(* ------------------------------------------------------------------------- *)
(* Type constructors for setting up finite types indexed by binary numbers.  *)
(* ------------------------------------------------------------------------- *)

let tybit0_INDUCT,tybit0_RECURSION = define_type
  "tybit0 = mktybit0((A,A)finite_sum)";;

let tybit1_INDUCT,tybit1_RECURSION = define_type
  "tybit1 = mktybit1(((A,A)finite_sum,1)finite_sum)";;

let vHAS_SIZE_TYBIT0 = try Cache.lookup_thm "HAS_SIZE_TYBIT0" with _ ->  prove
 ((parse_term "(:(A)tybit0) HAS_SIZE 2 * dimindex(:A)"),
  vSUBGOAL_THEN
   (parse_term "(:(A)tybit0) = IMAGE mktybit0 (:(A,A)finite_sum)")
  vSUBST1_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSURJECTIVE_IMAGE_EQ ---->
    vREWRITE_TAC[vIN_UNIV] ----> vMESON_TAC[cases "tybit0"];
    vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ---->
    vREWRITE_TAC[vIN_UNIV; injectivity "tybit0"] ---->
    vW(vMP_TAC -| vPART_MATCH lhand
      vDIMINDEX_HAS_SIZE_FINITE_SUM -| lhand -| snd) ---->
    vREWRITE_TAC[vDIMINDEX_FINITE_SUM; vGSYM vMULT_2]]);;

let vHAS_SIZE_TYBIT1 = try Cache.lookup_thm "HAS_SIZE_TYBIT1" with _ ->  prove
 ((parse_term "(:(A)tybit1) HAS_SIZE 2 * dimindex(:A) + 1"),
  vSUBGOAL_THEN
   (parse_term "(:(A)tybit1) = IMAGE mktybit1 (:((A,A)finite_sum,1)finite_sum)")
  vSUBST1_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vSURJECTIVE_IMAGE_EQ ---->
    vREWRITE_TAC[vIN_UNIV] ----> vMESON_TAC[cases "tybit1"];
    vMATCH_MP_TAC vHAS_SIZE_IMAGE_INJ ---->
    vREWRITE_TAC[vIN_UNIV; injectivity "tybit1"] ---->
    vW(vMP_TAC -| vPART_MATCH lhand
      vDIMINDEX_HAS_SIZE_FINITE_SUM -| lhand -| snd) ---->
    vREWRITE_TAC[vDIMINDEX_FINITE_SUM; vDIMINDEX_1; vGSYM vMULT_2]]);;

let vDIMINDEX_TYBIT0 = try Cache.lookup_thm "DIMINDEX_TYBIT0" with _ ->  prove
 ((parse_term "dimindex(:(A)tybit0) = 2 * dimindex(:A)"),
  vMATCH_MP_TAC vDIMINDEX_UNIQUE ----> vMATCH_ACCEPT_TAC vHAS_SIZE_TYBIT0);;

let vDIMINDEX_TYBIT1 = try Cache.lookup_thm "DIMINDEX_TYBIT1" with _ ->  prove
 ((parse_term "dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1"),
  vMATCH_MP_TAC vDIMINDEX_UNIQUE ----> vMATCH_ACCEPT_TAC vHAS_SIZE_TYBIT1);;

let vDIMINDEX_CLAUSES = try Cache.lookup_thm "DIMINDEX_CLAUSES" with _ ->  prove
 ((parse_term "dimindex(:1) = 1 /\\\n   dimindex(:(A)tybit0) = 2 * dimindex(:A) /\\\n   dimindex(:(A)tybit1) = 2 * dimindex(:A) + 1"),
 vREWRITE_TAC[vDIMINDEX_1] ----> vCONJ_TAC ---->
 vMATCH_MP_TAC vDIMINDEX_UNIQUE ---->
 vREWRITE_TAC[ vHAS_SIZE_TYBIT0; vHAS_SIZE_TYBIT1]);;

let vFINITE_1 = try Cache.lookup_thm "FINITE_1" with _ ->  prove
 ((parse_term "FINITE (:1)"),
  vMESON_TAC[vHAS_SIZE_1; vHAS_SIZE]);;

let vFINITE_TYBIT0 = try Cache.lookup_thm "FINITE_TYBIT0" with _ ->  prove
 ((parse_term "FINITE (:A tybit0)"),
  vMESON_TAC[vHAS_SIZE_TYBIT0; vHAS_SIZE]);;

let vFINITE_TYBIT1 = try Cache.lookup_thm "FINITE_TYBIT1" with _ ->  prove
 ((parse_term "FINITE (:A tybit1)"),
  vMESON_TAC[vHAS_SIZE_TYBIT1; vHAS_SIZE]);;

let vFINITE_CLAUSES = try Cache.lookup_thm "FINITE_CLAUSES" with _ ->  prove
 ((parse_term "FINITE(:1) /\\ FINITE(:A tybit0) /\\ FINITE(:A tybit1)"),
  vREWRITE_TAC[vFINITE_1; vFINITE_TYBIT0; vFINITE_TYBIT1]);;

(* ------------------------------------------------------------------------- *)
(* Computing dimindex of fintypes.                                           *)
(* ------------------------------------------------------------------------- *)

let vDIMINDEX_CONV : conv =
  let [@warning "-8"] [pth_num;pth0;pth1;pth_one] = (vCONJUNCTS -| prove)
   ((parse_term "(dimindex(:A) = n <=> dimindex(s:A->bool) = NUMERAL n) /\\\n     (dimindex(:A) = n <=> dimindex(:A tybit0) = BIT0 n) /\\\n     (dimindex(:A) = n <=> dimindex(:A tybit1) = BIT1 n) /\\\n     dimindex(:1) = BIT1 _0"),
    vCONJ_TAC ++--> [vREWRITE_TAC[vNUMERAL; dimindex]; vALL_TAC] ---->
    vREWRITE_TAC[vDIMINDEX_CLAUSES] ----> vCONV_TAC vBITS_ELIM_CONV ---->
    vARITH_TAC) in
  let nvar = (parse_term "n:num") in
  let rec calc_dimindex ty =
    match ty with
      Tyapp("1",_) -> pth_one
    | Tyapp("tybit0",ty'::_) ->
        let th = calc_dimindex ty' in
        let n = rand(concl th) in
        vEQ_MP (vINST [n,nvar] (vINST_TYPE [ty',aty] pth0)) th
    | Tyapp("tybit1",ty'::_) ->
        let th = calc_dimindex ty' in
        let n = rand(concl th) in
        vEQ_MP (vINST [n,nvar] (vINST_TYPE [ty',aty] pth1)) th
    | _ -> fail() in
  function
    Comb(Const("dimindex",_),tm) ->
      let uty = type_of tm in
      let [@warning "-8"] _,(sty::_) = dest_type uty in
      let th = calc_dimindex sty in
      let svar = mk_var("s",uty)
      and ntm = rand(concl th) in
      let pth = vINST [tm,svar;ntm,nvar] (vINST_TYPE [sty,aty] pth_num) in
      vEQ_MP pth th
   | _ -> failwith "DIMINDEX_CONV";;

let vHAS_SIZE_DIMINDEX_RULE =
  let pth = prove
   ((parse_term "(:A) HAS_SIZE n <=> FINITE(:A) /\\ dimindex(:A) = n"),
    vMESON_TAC[vUNIV_HAS_SIZE_DIMINDEX; vHAS_SIZE]) in
  let htm = (parse_term "(HAS_SIZE) (:A)")
  and conv = vGEN_REWRITE_CONV vI [pth]
  and rule = vEQT_ELIM -| vGEN_REWRITE_CONV vI [vFINITE_CLAUSES] in
  fun nty ->
    let tm = mk_comb(inst[nty,aty] htm,mk_numeral (dest_finty nty)) in
    let th1 = conv tm in
    vEQ_MP (vSYM th1)
          (vCONJ (rule (lhand(rand(concl th1))))
                (vDIMINDEX_CONV (lhand(rand(rand(concl th1))))));;

let vDIMINDEX_TAC : tactic =
  vCONV_TAC (vONCE_DEPTH_CONV vDIMINDEX_CONV);;

(* ------------------------------------------------------------------------- *)
(* Remember cases 2, 3 and 4, which are especially useful for real^N.        *)
(* ------------------------------------------------------------------------- *)

let vDIMINDEX_2 = try Cache.lookup_thm "DIMINDEX_2" with _ ->  prove
 ((parse_term "dimindex (:2) = 2"),
  vDIMINDEX_TAC ----> vREFL_TAC);;

let vDIMINDEX_3 = try Cache.lookup_thm "DIMINDEX_3" with _ ->  prove
 ((parse_term "dimindex (:3) = 3"),
  vDIMINDEX_TAC ----> vREFL_TAC);;

let vDIMINDEX_4 = try Cache.lookup_thm "DIMINDEX_4" with _ ->  prove
 ((parse_term "dimindex (:4) = 4"),
  vDIMINDEX_TAC ----> vREFL_TAC);;

let vHAS_SIZE_2 = try Cache.lookup_thm "HAS_SIZE_2" with _ ->  vHAS_SIZE_DIMINDEX_RULE (parse_type "2");;
let vHAS_SIZE_3 = try Cache.lookup_thm "HAS_SIZE_3" with _ ->  vHAS_SIZE_DIMINDEX_RULE (parse_type "3");;
let vHAS_SIZE_4 = try Cache.lookup_thm "HAS_SIZE_4" with _ ->  vHAS_SIZE_DIMINDEX_RULE (parse_type "4");;

(* ------------------------------------------------------------------------- *)
(* Finiteness lemma.                                                         *)
(* ------------------------------------------------------------------------- *)

let vFINITE_CART = try Cache.lookup_thm "FINITE_CART" with _ ->  prove
 ((parse_term "!P. (!i. 1 <= i /\\ i <= dimindex(:N) ==> FINITE {x | P i x})\n       ==> FINITE {v:A^N | !i. 1 <= i /\\ i <= dimindex(:N) ==> P i (v$i)}"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vSUBGOAL_THEN
   (parse_term "!n. n <= dimindex(:N)\n        ==> FINITE {v:A^N | (!i. 1 <= i /\\ i <= dimindex(:N) /\\ i <= n\n                                 ==> P i (v$i)) /\\\n                            (!i. 1 <= i /\\ i <= dimindex(:N) /\\ n < i\n                                 ==> v$i = @x. F)}")
   (vMP_TAC -| vSPEC (parse_term "dimindex(:N)")) ----> vREWRITE_TAC[vLE_REFL; vLET_ANTISYM] ---->
  vINDUCT_TAC ++-->
   [vREWRITE_TAC[vARITH_RULE (parse_term "1 <= i /\\ i <= n /\\ i <= 0 <=> F")] ---->
    vSIMP_TAC[vARITH_RULE (parse_term "1 <= i /\\ i <= n /\\ 0 < i <=> 1 <= i /\\ i <= n")] ---->
    vSUBGOAL_THEN
     (parse_term "{v | !i. 1 <= i /\\ i <= dimindex (:N) ==> v$i = (@x. F)} =\n      {(lambda i. @x. F):A^N}")
     (fun th -> vSIMP_TAC[vFINITE_RULES;th]) ---->
    vSIMP_TAC[vEXTENSION; vIN_SING; vIN_ELIM_THM; vCART_EQ; vLAMBDA_BETA];
    vALL_TAC] ---->
  vDISCH_TAC ---->
  vMATCH_MP_TAC vFINITE_SUBSET ----> vEXISTS_TAC
   (parse_term "IMAGE (\\(x:A,v:A^N). (lambda i. if i = SUC n then x else v$i):A^N)\n          {x,v | x IN {x:A | P (SUC n) x} /\\\n                 v IN {v:A^N | (!i. 1 <= i /\\ i <= dimindex(:N) /\\ i <= n\n                                ==> P i (v$i)) /\\\n                           (!i. 1 <= i /\\ i <= dimindex (:N) /\\ n < i\n                                ==> v$i = (@x. F))}}") ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vFINITE_IMAGE ---->
    vASM_SIMP_TAC[vFINITE_PRODUCT; vARITH_RULE (parse_term "1 <= SUC n");
                 vARITH_RULE (parse_term "SUC n <= m ==> n <= m")];
    vALL_TAC] ---->
  vREWRITE_TAC[vSUBSET; vIN_IMAGE; vIN_ELIM_PAIR_THM; vEXISTS_PAIR_THM] ---->
  vX_GEN_TAC (parse_term "v:A^N") ----> vREWRITE_TAC[vIN_ELIM_THM] ---->
  vSTRIP_TAC ----> vEXISTS_TAC (parse_term "(v:A^N)$(SUC n)") ---->
  vEXISTS_TAC (parse_term "(lambda i. if i = SUC n then @x. F else (v:A^N)$i):A^N") ---->
  vSIMP_TAC[vCART_EQ; vLAMBDA_BETA; vARITH_RULE (parse_term "i <= n ==> ~(i = SUC n)")] ---->
  vASM_MESON_TAC[vLE; vARITH_RULE (parse_term "1 <= SUC n");
                vARITH_RULE (parse_term "n < i /\\ ~(i = SUC n) ==> SUC n < i")]);;

(* ------------------------------------------------------------------------- *)
(* More cardinality results for whole universe.                              *)
(* ------------------------------------------------------------------------- *)

let vHAS_SIZE_CART_UNIV = try Cache.lookup_thm "HAS_SIZE_CART_UNIV" with _ ->  prove
 ((parse_term "!m. (:A) HAS_SIZE m ==> (:A^N) HAS_SIZE m EXP (dimindex(:N))"),
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN
   (parse_term "(:(N)finite_image->A) HAS_SIZE m EXP (dimindex(:N))")
  vMP_TAC ++-->
   [vASM_SIMP_TAC[vHAS_SIZE_FUNSPACE_UNIV; vHAS_SIZE_FINITE_IMAGE];
    vDISCH_THEN(vMP_TAC -| vISPEC (parse_term "mk_cart:((N)finite_image->A)->A^N") -|
      vMATCH_MP (vREWRITE_RULE[vIMP_CONJ_ALT] vHAS_SIZE_IMAGE_INJ)) ---->
    vREWRITE_TAC[vIN_UNIV] ---->
    vANTS_TAC ++--> [vMESON_TAC[cart_tybij]; vMATCH_MP_TAC vEQ_IMP] ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ----> vMATCH_MP_TAC vSURJECTIVE_IMAGE_EQ ---->
    vREWRITE_TAC[vIN_UNIV] ----> vMESON_TAC[cart_tybij]]);;

let vCARD_CART_UNIV = try Cache.lookup_thm "CARD_CART_UNIV" with _ ->  prove
 ((parse_term "FINITE(:A) ==> CARD(:A^N) = CARD(:A) EXP dimindex(:N)"),
  vMESON_TAC[vHAS_SIZE_CART_UNIV; vHAS_SIZE]);;

let vFINITE_CART_UNIV = try Cache.lookup_thm "FINITE_CART_UNIV" with _ ->  prove
 ((parse_term "FINITE(:A) ==> FINITE(:A^N)"),
  vMESON_TAC[vHAS_SIZE_CART_UNIV; vHAS_SIZE]);;

(* ------------------------------------------------------------------------- *)
(* Explicit construction of a vector from a list of components.              *)
(* ------------------------------------------------------------------------- *)

let vector = new_definition
  (parse_term "(vector l):A^N = lambda i. EL (i - 1) l");;

(* ------------------------------------------------------------------------- *)
(* Convenient set membership elimination theorem.                            *)
(* ------------------------------------------------------------------------- *)

let vIN_ELIM_PASTECART_THM = try Cache.lookup_thm "IN_ELIM_PASTECART_THM" with _ ->  prove
 ((parse_term "!P a b. pastecart a b IN {pastecart x y | P x y} <=> P a b"),
  vREWRITE_TAC[vIN_ELIM_THM; vPASTECART_EQ;
              vFSTCART_PASTECART; vSNDCART_PASTECART] ---->
  vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Variant of product types using pasting of vectors.                        *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("PCROSS",(22,"right"));;

let vPCROSS = new_definition
 (parse_term "s PCROSS t = {pastecart (x:A^M) (y:A^N) | x IN s /\\ y IN t}");;

let vFORALL_IN_PCROSS = try Cache.lookup_thm "FORALL_IN_PCROSS" with _ ->  prove
 ((parse_term "(!z. z IN s PCROSS t ==> P z) <=>\n   (!x y. x IN s /\\ y IN t ==> P(pastecart x y))"),
  vREWRITE_TAC[vPCROSS; vFORALL_IN_GSPEC]);;

let vEXISTS_IN_PCROSS = try Cache.lookup_thm "EXISTS_IN_PCROSS" with _ ->  prove
 ((parse_term "(?z. z IN s PCROSS t /\\ P z) <=>\n   (?x y. x IN s /\\ y IN t /\\ P(pastecart x y))"),
  vREWRITE_TAC[vPCROSS; vEXISTS_IN_GSPEC; vCONJ_ASSOC]);;

let vPASTECART_IN_PCROSS = try Cache.lookup_thm "PASTECART_IN_PCROSS" with _ ->  prove
 ((parse_term "!s t x y. (pastecart x y) IN (s PCROSS t) <=> x IN s /\\ y IN t"),
  vREWRITE_TAC[vPCROSS; vIN_ELIM_PASTECART_THM]);;

let vPCROSS_EQ_EMPTY = try Cache.lookup_thm "PCROSS_EQ_EMPTY" with _ ->  prove
 ((parse_term "!s t. s PCROSS t = {} <=> s = {} \\/ t = {}"),
  vREWRITE_TAC[vPCROSS] ----> vSET_TAC[]);;

let vPCROSS_EMPTY = try Cache.lookup_thm "PCROSS_EMPTY" with _ ->  prove
 ((parse_term "(!s. s PCROSS {} = {}) /\\ (!t. {} PCROSS t = {})"),
  vREWRITE_TAC[vPCROSS_EQ_EMPTY]);;

let vPCROSS_SING = try Cache.lookup_thm "PCROSS_SING" with _ ->  prove
 ((parse_term "!x y:A^N. {x} PCROSS {y} = {pastecart x y}"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PASTECART; vIN_SING; vPASTECART_IN_PCROSS;
              vPASTECART_INJ]);;

let vSUBSET_PCROSS = try Cache.lookup_thm "SUBSET_PCROSS" with _ ->  prove
 ((parse_term "!s t s' t'. s PCROSS t SUBSET s' PCROSS t' <=>\n                s = {} \\/ t = {} \\/ s SUBSET s' /\\ t SUBSET t'"),
  vSIMP_TAC[vPCROSS; vEXTENSION; vIN_ELIM_PASTECART_THM; vSUBSET;
   vFORALL_PASTECART; vPASTECART_IN_PCROSS; vNOT_IN_EMPTY] ----> vMESON_TAC[]);;

let vPCROSS_MONO = try Cache.lookup_thm "PCROSS_MONO" with _ ->  prove
 ((parse_term "!s t s' t'. s SUBSET s' /\\ t SUBSET t' ==> s PCROSS t SUBSET s' PCROSS t'"),
  vSIMP_TAC[vSUBSET_PCROSS]);;

let vPCROSS_EQ = try Cache.lookup_thm "PCROSS_EQ" with _ ->  prove
 ((parse_term "!s s':real^M->bool t t':real^N->bool.\n        s PCROSS t = s' PCROSS t' <=>\n        (s = {} \\/ t = {}) /\\ (s' = {} \\/ t' = {}) \\/ s = s' /\\ t = t'"),
  vREWRITE_TAC[vGSYM vSUBSET_ANTISYM_EQ; vSUBSET_PCROSS] ----> vSET_TAC[]);;

let vUNIV_PCROSS_UNIV = try Cache.lookup_thm "UNIV_PCROSS_UNIV" with _ ->  prove
 ((parse_term "(:A^M) PCROSS (:A^N) = (:A^(M,N)finite_sum)"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PASTECART; vPASTECART_IN_PCROSS; vIN_UNIV]);;

let vHAS_SIZE_PCROSS = try Cache.lookup_thm "HAS_SIZE_PCROSS" with _ ->  prove
 ((parse_term "!(s:A^M->bool) (t:A^N->bool) m n.\n        s HAS_SIZE m /\\ t HAS_SIZE n ==> (s PCROSS t) HAS_SIZE (m * n)"),
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vHAS_SIZE_PRODUCT) ---->
  vMATCH_MP_TAC vEQ_IMP ----> vSPEC_TAC((parse_term "m * n:num"),(parse_term "k:num")) ---->
  vMATCH_MP_TAC vBIJECTIONS_HAS_SIZE_EQ ---->
  vEXISTS_TAC (parse_term "\\(x:A^M,y:A^N). pastecart x y") ---->
  vEXISTS_TAC (parse_term "\\z:A^(M,N)finite_sum. fstcart z,sndcart z") ---->
  vREWRITE_TAC[vFORALL_IN_GSPEC; vPASTECART_IN_PCROSS] ---->
  vREWRITE_TAC[vIN_ELIM_PAIR_THM; vPASTECART_FST_SND] ---->
  vREWRITE_TAC[vFORALL_IN_PCROSS; vFSTCART_PASTECART; vSNDCART_PASTECART]);;

let vFINITE_PCROSS = try Cache.lookup_thm "FINITE_PCROSS" with _ ->  prove
 ((parse_term "!(s:A^M->bool) (t:A^N->bool).\n        FINITE s /\\ FINITE t ==> FINITE(s PCROSS t)"),
  vMESON_TAC[vREWRITE_RULE[vHAS_SIZE] vHAS_SIZE_PCROSS]);;

let vFINITE_PCROSS_EQ = try Cache.lookup_thm "FINITE_PCROSS_EQ" with _ ->  prove
 ((parse_term "!(s:A^M->bool) (t:A^N->bool).\n        FINITE(s PCROSS t) <=> s = {} \\/ t = {} \\/ FINITE s /\\ FINITE t"),
  vREPEAT vGEN_TAC ---->
  vMAP_EVERY vASM_CASES_TAC [(parse_term "s:A^M->bool = {}"); (parse_term "t:A^N->bool = {}")] ---->
  vASM_REWRITE_TAC[vPCROSS_EMPTY; vFINITE_EMPTY] ---->
  vEQ_TAC ----> vSIMP_TAC[vFINITE_PCROSS] ----> vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC vFINITE_SUBSET ++-->
   [vEXISTS_TAC (parse_term "IMAGE fstcart ((s PCROSS t):A^(M,N)finite_sum->bool)");
    vEXISTS_TAC (parse_term "IMAGE sndcart ((s PCROSS t):A^(M,N)finite_sum->bool)")] ---->
  vASM_SIMP_TAC[vFINITE_IMAGE; vSUBSET; vIN_IMAGE; vEXISTS_PASTECART] ---->
  vREWRITE_TAC[vPASTECART_IN_PCROSS; vFSTCART_PASTECART; vSNDCART_PASTECART] ---->
  vASM vSET_TAC[]);;

let vIMAGE_FSTCART_PCROSS = try Cache.lookup_thm "IMAGE_FSTCART_PCROSS" with _ ->  prove
 ((parse_term "!s:real^M->bool t:real^N->bool.\n        IMAGE fstcart (s PCROSS t) = if t = {} then {} else s"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vPCROSS_EMPTY; vIMAGE_CLAUSES] ---->
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE] ----> vONCE_REWRITE_TAC[vCONJ_SYM] ---->
  vREWRITE_TAC[vEXISTS_IN_PCROSS; vFSTCART_PASTECART] ----> vASM vSET_TAC[]);;

let vIMAGE_SNDCART_PCROSS = try Cache.lookup_thm "IMAGE_SNDCART_PCROSS" with _ ->  prove
 ((parse_term "!s:real^M->bool t:real^N->bool.\n        IMAGE sndcart (s PCROSS t) = if s = {} then {} else t"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vPCROSS_EMPTY; vIMAGE_CLAUSES] ---->
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE] ----> vONCE_REWRITE_TAC[vCONJ_SYM] ---->
  vREWRITE_TAC[vEXISTS_IN_PCROSS; vSNDCART_PASTECART] ----> vASM vSET_TAC[]);;

let vPCROSS_INTER = try Cache.lookup_thm "PCROSS_INTER" with _ ->  prove
 ((parse_term "(!s t u. s PCROSS (t INTER u) = (s PCROSS t) INTER (s PCROSS u)) /\\\n   (!s t u. (s INTER t) PCROSS u = (s PCROSS u) INTER (t PCROSS u))"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PASTECART; vIN_INTER; vPASTECART_IN_PCROSS] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vTAUT);;

let vPCROSS_UNION = try Cache.lookup_thm "PCROSS_UNION" with _ ->  prove
 ((parse_term "(!s t u. s PCROSS (t UNION u) = (s PCROSS t) UNION (s PCROSS u)) /\\\n   (!s t u. (s UNION t) PCROSS u = (s PCROSS u) UNION (t PCROSS u))"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PASTECART; vIN_UNION; vPASTECART_IN_PCROSS] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vTAUT);;

let vPCROSS_DIFF = try Cache.lookup_thm "PCROSS_DIFF" with _ ->  prove
 ((parse_term "(!s t u. s PCROSS (t DIFF u) = (s PCROSS t) DIFF (s PCROSS u)) /\\\n   (!s t u. (s DIFF t) PCROSS u = (s PCROSS u) DIFF (t PCROSS u))"),
  vREWRITE_TAC[vEXTENSION; vFORALL_PASTECART; vIN_DIFF; vPASTECART_IN_PCROSS] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vTAUT);;

let vINTER_PCROSS = try Cache.lookup_thm "INTER_PCROSS" with _ ->  prove
 ((parse_term "!s s' t t'.\n      (s PCROSS t) INTER (s' PCROSS t') = (s INTER s') PCROSS (t INTER t')"),
  vREWRITE_TAC[vEXTENSION; vIN_INTER; vFORALL_PASTECART; vPASTECART_IN_PCROSS] ---->
  vCONV_TAC vTAUT);;

let vPCROSS_UNIONS_UNIONS,vPCROSS_UNIONS = (vCONJ_PAIR -| prove)
 ((parse_term "(!f g. (UNIONS f) PCROSS (UNIONS g) =\n          UNIONS {s PCROSS t | s IN f /\\ t IN g}) /\\\n   (!s f. s PCROSS (UNIONS f) = UNIONS {s PCROSS t | t IN f}) /\\\n   (!f t. (UNIONS f) PCROSS t = UNIONS {s PCROSS t | s IN f})"),
  vREWRITE_TAC[vUNIONS_GSPEC; vEXTENSION; vFORALL_PASTECART; vIN_ELIM_THM;
              vPASTECART_IN_PCROSS] ---->
  vSET_TAC[]);;

let vPCROSS_INTERS_INTERS,vPCROSS_INTERS = (vCONJ_PAIR -| prove)
 ((parse_term "(!f g. (INTERS f) PCROSS (INTERS g) =\n          if f = {} then INTERS {UNIV PCROSS t | t IN g}\n          else if g = {} then INTERS {s PCROSS UNIV | s IN f}\n          else INTERS {s PCROSS t | s IN f /\\ t IN g}) /\\\n   (!s f. s PCROSS (INTERS f) =\n          if f = {} then s PCROSS UNIV else INTERS {s PCROSS t | t IN f}) /\\\n   (!f t. (INTERS f) PCROSS t =\n          if f = {} then UNIV PCROSS t else INTERS {s PCROSS t | s IN f})"),
  vREPEAT vSTRIP_TAC ----> vREPEAT (vCOND_CASES_TAC ----> vREWRITE_TAC[]) ---->
  vASM_REWRITE_TAC[vINTERS_GSPEC; vEXTENSION; vFORALL_PASTECART; vIN_ELIM_THM;
                  vPASTECART_IN_PCROSS; vNOT_IN_EMPTY] ---->
  vASM vSET_TAC[]);;

let vDISJOINT_PCROSS = try Cache.lookup_thm "DISJOINT_PCROSS" with _ ->  prove
 ((parse_term "!s:A^M->bool t:A^N->bool s' t'.\n        DISJOINT (s PCROSS t) (s' PCROSS t') <=>\n        DISJOINT s s' \\/ DISJOINT t t'"),
  vREWRITE_TAC[vDISJOINT; vINTER_PCROSS; vPCROSS_EQ_EMPTY]);;
