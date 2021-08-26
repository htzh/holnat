(* ========================================================================= *)
(* Generic iterated operations and special cases of sums over N and R.       *)
(*                                                                           *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*              (c) Copyright, Lars Schewe 2007                              *)
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
open Wf
open Calc_num
open Realax
open Calc_int
open Realarith
open Real
open Calc_rat
open Int
open Sets

open Num
;;

prioritize_num();;

(* ------------------------------------------------------------------------- *)
(* A natural notation for segments of the naturals.                          *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("..",(15,"right"));;

let numseg = new_definition
  (parse_term "m..n = {x:num | m <= x /\\ x <= n}");;

let vFINITE_NUMSEG = try Cache.lookup_thm "FINITE_NUMSEG" with _ ->  prove
 ((parse_term "!m n. FINITE(m..n)"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vFINITE_SUBSET ---->
  vEXISTS_TAC (parse_term "{x:num | x <= n}") ----> vREWRITE_TAC[vFINITE_NUMSEG_LE] ---->
  vSIMP_TAC[vSUBSET; vIN_ELIM_THM; numseg]);;

let vNUMSEG_COMBINE_R = try Cache.lookup_thm "NUMSEG_COMBINE_R" with _ ->  prove
 ((parse_term "!m p n. m <= p + 1 /\\ p <= n ==> ((m..p) UNION ((p+1)..n) = m..n)"),
  vREWRITE_TAC[vEXTENSION; vIN_UNION; numseg; vIN_ELIM_THM] ----> vARITH_TAC);;

let vNUMSEG_COMBINE_L = try Cache.lookup_thm "NUMSEG_COMBINE_L" with _ ->  prove
 ((parse_term "!m p n. m <= p /\\ p <= n + 1 ==> ((m..(p-1)) UNION (p..n) = m..n)"),
  vREWRITE_TAC[vEXTENSION; vIN_UNION; numseg; vIN_ELIM_THM] ----> vARITH_TAC);;

let vNUMSEG_LREC = try Cache.lookup_thm "NUMSEG_LREC" with _ ->  prove
 ((parse_term "!m n. m <= n ==> (m INSERT ((m+1)..n) = m..n)"),
  vREWRITE_TAC[vEXTENSION; vIN_INSERT; numseg; vIN_ELIM_THM] ----> vARITH_TAC);;

let vNUMSEG_RREC = try Cache.lookup_thm "NUMSEG_RREC" with _ ->  prove
 ((parse_term "!m n. m <= n ==> (n INSERT (m..(n-1)) = m..n)"),
  vREWRITE_TAC[vEXTENSION; vIN_INSERT; numseg; vIN_ELIM_THM] ----> vARITH_TAC);;

let vNUMSEG_REC = try Cache.lookup_thm "NUMSEG_REC" with _ ->  prove
 ((parse_term "!m n. m <= SUC n ==> (m..SUC n = (SUC n) INSERT (m..n))"),
  vSIMP_TAC[vGSYM vNUMSEG_RREC; vSUC_SUB1]);;

let vIN_NUMSEG = try Cache.lookup_thm "IN_NUMSEG" with _ ->  prove
 ((parse_term "!m n p. p IN (m..n) <=> m <= p /\\ p <= n"),
  vREWRITE_TAC[numseg; vIN_ELIM_THM]);;

let vIN_NUMSEG_0 = try Cache.lookup_thm "IN_NUMSEG_0" with _ ->  prove
 ((parse_term "!m n. m IN (0..n) <=> m <= n"),
  vREWRITE_TAC[vIN_NUMSEG; vLE_0]);;

let vNUMSEG_SING = try Cache.lookup_thm "NUMSEG_SING" with _ ->  prove
 ((parse_term "!n. n..n = {n}"),
  vREWRITE_TAC[vEXTENSION; vIN_SING; vIN_NUMSEG] ----> vARITH_TAC);;

let vNUMSEG_EMPTY = try Cache.lookup_thm "NUMSEG_EMPTY" with _ ->  prove
 ((parse_term "!m n. (m..n = {}) <=> n < m"),
  vREWRITE_TAC[vEXTENSION; vNOT_IN_EMPTY; vIN_NUMSEG] ---->
  vMESON_TAC[vNOT_LE; vLE_TRANS; vLE_REFL]);;

let vEMPTY_NUMSEG = try Cache.lookup_thm "EMPTY_NUMSEG" with _ ->  prove
 ((parse_term "!m n. n < m ==> m..n = {}"),
  vREWRITE_TAC[vNUMSEG_EMPTY]);;

let vFINITE_SUBSET_NUMSEG = try Cache.lookup_thm "FINITE_SUBSET_NUMSEG" with _ ->  prove
 ((parse_term "!s:num->bool. FINITE s <=> ?n. s SUBSET 0..n"),
  vGEN_TAC ----> vEQ_TAC ++-->
   [vREWRITE_TAC[vSUBSET; vIN_NUMSEG; vLE_0] ---->
    vSPEC_TAC((parse_term "s:num->bool"),(parse_term "s:num->bool")) ---->
    vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
    vREWRITE_TAC[vIN_INSERT; vNOT_IN_EMPTY] ---->
    vMESON_TAC[vLE_CASES; vLE_REFL; vLE_TRANS];
    vMESON_TAC[vFINITE_SUBSET; vFINITE_NUMSEG]]);;

let vCARD_NUMSEG_LEMMA = try Cache.lookup_thm "CARD_NUMSEG_LEMMA" with _ ->  prove
 ((parse_term "!m d. CARD(m..(m+d)) = d + 1"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_SIMP_TAC[vADD_CLAUSES; vNUMSEG_REC; vNUMSEG_SING; vFINITE_RULES;
               vARITH_RULE (parse_term "m <= SUC(m + d)"); vCARD_CLAUSES; vFINITE_NUMSEG;
               vNOT_IN_EMPTY; vARITH; vIN_NUMSEG; vARITH_RULE (parse_term "~(SUC n <= n)")]);;

let vCARD_NUMSEG = try Cache.lookup_thm "CARD_NUMSEG" with _ ->  prove
 ((parse_term "!m n. CARD(m..n) = (n + 1) - m"),
  vREPEAT vGEN_TAC ---->
  vDISJ_CASES_THEN vMP_TAC (vARITH_RULE (parse_term "n:num < m \\/ m <= n")) ++-->
   [vASM_MESON_TAC[vNUMSEG_EMPTY; vCARD_CLAUSES;
                  vARITH_RULE (parse_term "n < m ==> ((n + 1) - m = 0)")];
    vSIMP_TAC[vLE_EXISTS; vLEFT_IMP_EXISTS_THM; vCARD_NUMSEG_LEMMA] ---->
    vREPEAT vSTRIP_TAC ----> vARITH_TAC]);;

let vHAS_SIZE_NUMSEG = try Cache.lookup_thm "HAS_SIZE_NUMSEG" with _ ->  prove
 ((parse_term "!m n. (m..n) HAS_SIZE ((n + 1) - m)"),
  vREWRITE_TAC[vHAS_SIZE; vFINITE_NUMSEG; vCARD_NUMSEG]);;

let vCARD_NUMSEG_1 = try Cache.lookup_thm "CARD_NUMSEG_1" with _ ->  prove
 ((parse_term "!n. CARD(1..n) = n"),
  vREWRITE_TAC[vCARD_NUMSEG] ----> vARITH_TAC);;

let vHAS_SIZE_NUMSEG_1 = try Cache.lookup_thm "HAS_SIZE_NUMSEG_1" with _ ->  prove
 ((parse_term "!n. (1..n) HAS_SIZE n"),
  vREWRITE_TAC[vCARD_NUMSEG; vHAS_SIZE; vFINITE_NUMSEG] ----> vARITH_TAC);;

let vNUMSEG_CLAUSES = try Cache.lookup_thm "NUMSEG_CLAUSES" with _ ->  prove
 ((parse_term "(!m. m..0 = if m = 0 then {0} else {}) /\\\n   (!m n. m..SUC n = if m <= SUC n then (SUC n) INSERT (m..n) else m..n)"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ---->
  vGEN_REWRITE_TAC vI [vEXTENSION] ---->
  vREWRITE_TAC[vIN_NUMSEG; vNOT_IN_EMPTY; vIN_INSERT] ---->
  vPOP_ASSUM vMP_TAC ----> vARITH_TAC);;

let vFINITE_INDEX_NUMSEG = try Cache.lookup_thm "FINITE_INDEX_NUMSEG" with _ ->  prove
 ((parse_term "!s:A->bool.\n        FINITE s <=>\n        ?f. (!i j. i IN 1..CARD s /\\ j IN 1..CARD s /\\ f i = f j ==> i = j) /\\\n            s = IMAGE f (1..CARD s)"),
  vGEN_TAC ----> 
  vEQ_TAC ++--> [vDISCH_TAC; vMESON_TAC[vFINITE_IMAGE; vFINITE_NUMSEG]] ---->
  vMP_TAC(vISPECL [(parse_term "1..CARD(s:A->bool)"); (parse_term "s:A->bool")] 
        vCARD_EQ_BIJECTIONS) ---->
  vASM_REWRITE_TAC[vFINITE_NUMSEG; vCARD_NUMSEG_1] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vSET_TAC[]);;

let vFINITE_INDEX_NUMBERS = try Cache.lookup_thm "FINITE_INDEX_NUMBERS" with _ ->  prove
 ((parse_term "!s:A->bool.\n        FINITE s <=>\n        ?k:num->bool f. (!i j. i IN k /\\ j IN k /\\ f i = f j ==> i = j) /\\\n                        FINITE k /\\ s = IMAGE f k"),
  vMESON_TAC[vFINITE_INDEX_NUMSEG; vFINITE_NUMSEG; vFINITE_IMAGE]);;

let vINTER_NUMSEG = try Cache.lookup_thm "INTER_NUMSEG" with _ ->  prove
 ((parse_term "!m n p q. (m..n) INTER (p..q) = (MAX m p)..(MIN n q)"),
  vREWRITE_TAC[vEXTENSION; vIN_INTER; vIN_NUMSEG] ----> vARITH_TAC);;

let vDISJOINT_NUMSEG = try Cache.lookup_thm "DISJOINT_NUMSEG" with _ ->  prove
 ((parse_term "!m n p q. DISJOINT (m..n) (p..q) <=> n < p \\/ q < m \\/ n < m \\/ q < p"),
  vREWRITE_TAC[vDISJOINT; vNUMSEG_EMPTY; vINTER_NUMSEG] ----> vARITH_TAC);;

let vNUMSEG_ADD_SPLIT = try Cache.lookup_thm "NUMSEG_ADD_SPLIT" with _ ->  prove
 ((parse_term "!m n p. m <= n + 1 ==> (m..(n+p) = (m..n) UNION (n+1..n+p))"),
  vREWRITE_TAC[vEXTENSION; vIN_UNION; vIN_NUMSEG] ----> vARITH_TAC);;

let vNUMSEG_OFFSET_IMAGE = try Cache.lookup_thm "NUMSEG_OFFSET_IMAGE" with _ ->  prove
 ((parse_term "!m n p. (m+p..n+p) = IMAGE (\\i. i + p) (m..n)"),
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vIN_NUMSEG] ---->
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(fun th -> vEXISTS_TAC (parse_term "x - p:num") ----> vMP_TAC th); vALL_TAC] ---->
  vARITH_TAC);;

let vSUBSET_NUMSEG = try Cache.lookup_thm "SUBSET_NUMSEG" with _ ->  prove
 ((parse_term "!m n p q. (m..n) SUBSET (p..q) <=> n < m \\/ p <= m /\\ n <= q"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vSUBSET; vIN_NUMSEG] ---->
  vEQ_TAC ++--> [vMESON_TAC[vLE_TRANS; vNOT_LE; vLE_REFL]; vARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Equivalence with the more ad-hoc comprehension notation.                  *)
(* ------------------------------------------------------------------------- *)

let vNUMSEG_LE = try Cache.lookup_thm "NUMSEG_LE" with _ ->  prove
 ((parse_term "!n. {x | x <= n} = 0..n"),
  vREWRITE_TAC[vEXTENSION; vIN_NUMSEG; vIN_ELIM_THM] ----> vARITH_TAC);;

let vNUMSEG_LT = try Cache.lookup_thm "NUMSEG_LT" with _ ->  prove
 ((parse_term "!n. {x | x < n} = if n = 0 then {} else 0..(n-1)"),
  vGEN_TAC ----> vCOND_CASES_TAC ---->
  vREWRITE_TAC[vEXTENSION; vIN_NUMSEG; vIN_ELIM_THM; vNOT_IN_EMPTY] ---->
  vASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Conversion to evaluate m..n for specific numerals.                        *)
(* ------------------------------------------------------------------------- *)

let vNUMSEG_CONV =
  let pth_0 = vMESON[vNUMSEG_EMPTY] (parse_term "n < m ==> m..n = {}")
  and pth_1 = vMESON[vNUMSEG_SING] (parse_term "m..m = {m}")
  and pth_2 = vMESON[vNUMSEG_LREC; vADD1] (parse_term "m <= n ==> m..n = m INSERT (SUC m..n)")
  and ns_tm = (parse_term "(..)") and m_tm = (parse_term "m:num") and n_tm = (parse_term "n:num") in
  let rec vNUMSEG_CONV tm =
    let nstm,nt = dest_comb tm in
    let nst,mt = dest_comb nstm in
    if nst <> ns_tm then failwith "NUMSEG_CONV" else
    let m = dest_numeral mt and n = dest_numeral nt in
    if n </ m then vMP_CONV vNUM_LT_CONV (vINST [mt,m_tm; nt,n_tm] pth_0)
    else if n =/ m then vINST [mt,m_tm] pth_1
    else let th = vMP_CONV vNUM_LE_CONV (vINST [mt,m_tm; nt,n_tm] pth_2) in
         vCONV_RULE(funpow 2 vRAND_CONV
          (vLAND_CONV vNUM_SUC_CONV +---> vNUMSEG_CONV)) th in
  vNUMSEG_CONV;;

(* ------------------------------------------------------------------------- *)
(* Topological sorting of a finite set.                                      *)
(* ------------------------------------------------------------------------- *)

let vTOPOLOGICAL_SORT = try Cache.lookup_thm "TOPOLOGICAL_SORT" with _ ->  prove
 ((parse_term "!(<<). (!x y:A. x << y /\\ y << x ==> x = y) /\\\n          (!x y z. x << y /\\ y << z ==> x << z)\n          ==> !n s. s HAS_SIZE n\n                    ==> ?f. s = IMAGE f (1..n) /\\\n                            (!j k. j IN 1..n /\\ k IN 1..n /\\ j < k\n                                   ==> ~(f k << f j))"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vSUBGOAL_THEN (parse_term "!n s. s HAS_SIZE n /\\ ~(s = {})\n                      ==> ?a:A. a IN s /\\ !b. b IN (s DELETE a) ==> ~(b << a)")
  vASSUME_TAC ++-->
   [vINDUCT_TAC ---->
    vREWRITE_TAC[vHAS_SIZE_0; vHAS_SIZE_SUC; vTAUT (parse_term "~(a /\\ ~a)")] ---->
    vX_GEN_TAC (parse_term "s:A->bool") ----> vSTRIP_TAC ---->
    vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vGSYM vMEMBER_NOT_EMPTY]) ---->
    vDISCH_THEN(vX_CHOOSE_TAC (parse_term "a:A")) ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "a:A")) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "s DELETE (a:A)")) ---->
    vASM_SIMP_TAC[vSET_RULE (parse_term "a IN s ==> (s DELETE a = {} <=> s = {a})")] ---->
    vASM_CASES_TAC (parse_term "s = {a:A}") ----> vASM_REWRITE_TAC[] ++-->
     [vEXISTS_TAC (parse_term "a:A") ----> vSET_TAC[]; vALL_TAC] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "b:A") vSTRIP_ASSUME_TAC) ---->
    vASM_CASES_TAC (parse_term "((a:A) << (b:A)) :bool") ++-->
     [vEXISTS_TAC (parse_term "a:A"); vEXISTS_TAC (parse_term "b:A")] ----> vASM vSET_TAC[];
    vALL_TAC] ---->
  vINDUCT_TAC ++-->
   [vSIMP_TAC[vHAS_SIZE_0; vNUMSEG_CLAUSES; vARITH; vIMAGE_CLAUSES; vNOT_IN_EMPTY];
    vALL_TAC] ---->
  vREWRITE_TAC[vHAS_SIZE_SUC] ----> vX_GEN_TAC (parse_term "s:A->bool") ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "SUC n"); (parse_term "s:A->bool")]) ---->
  vASM_REWRITE_TAC[vHAS_SIZE_SUC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "a:A") vMP_TAC) ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "s DELETE (a:A)")) ----> vASM_SIMP_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "f:num->A") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "\\k. if k = 1 then a:A else f(k - 1)") ---->
  vSIMP_TAC[vARITH_RULE (parse_term "1 <= k ==> ~(SUC k = 1)"); vSUC_SUB1] ---->
  vSUBGOAL_THEN (parse_term "!i. i IN 1..SUC n <=> i = 1 \\/ 1 < i /\\ (i - 1) IN 1..n")
   (fun th -> vREWRITE_TAC[vEXTENSION; vIN_IMAGE; th])
  ++--> [vREWRITE_TAC[vIN_NUMSEG] ----> vARITH_TAC; vALL_TAC] ----> vCONJ_TAC ++-->
   [vX_GEN_TAC (parse_term "b:A") ----> vASM_CASES_TAC (parse_term "b:A = a") ++-->
     [vASM_MESON_TAC[]; vALL_TAC] ---->
    vFIRST_ASSUM(fun th -> vONCE_REWRITE_TAC[vMATCH_MP
     (vSET_RULE (parse_term "~(b = a) ==> (b IN s <=> b IN (s DELETE a))")) th]) ---->
    vONCE_REWRITE_TAC[vCOND_RAND] ---->
    vASM_REWRITE_TAC[vIN_IMAGE; vIN_NUMSEG] ---->
    vEQ_TAC ++--> [vALL_TAC; vMESON_TAC[]] ---->
    vDISCH_THEN(vX_CHOOSE_TAC (parse_term "i:num")) ----> vEXISTS_TAC (parse_term "i + 1") ---->
    vASM_SIMP_TAC[vARITH_RULE (parse_term "1 <= x ==> 1 < x + 1 /\\ ~(x + 1 = 1)"); vADD_SUB];
    vMAP_EVERY vX_GEN_TAC [(parse_term "j:num"); (parse_term "k:num")] ---->
    vMAP_EVERY vASM_CASES_TAC [(parse_term "j = 1"); (parse_term "k = 1")] ---->
    vASM_REWRITE_TAC[vLT_REFL] ++-->
     [vSTRIP_TAC ----> vFIRST_X_ASSUM vMATCH_MP_TAC ----> vASM vSET_TAC[];
      vARITH_TAC;
      vSTRIP_TAC ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
      vASM_REWRITE_TAC[] ----> vASM_ARITH_TAC]]);;

(* ------------------------------------------------------------------------- *)
(* Analogous finiteness theorem for segments of integers.                    *)
(* ------------------------------------------------------------------------- *)

let vFINITE_INT_SEG = try Cache.lookup_thm "FINITE_INT_SEG" with _ ->  prove
 ((parse_term "(!l r. FINITE {x:int | l <= x /\\ x <= r}) /\\\n   (!l r. FINITE {x:int | l <= x /\\ x < r}) /\\\n   (!l r. FINITE {x:int | l < x /\\ x <= r}) /\\\n   (!l r. FINITE {x:int | l < x /\\ x < r})"),
  vMATCH_MP_TAC(vTAUT (parse_term "(a ==> b) /\\ a ==> a /\\ b")) ----> vCONJ_TAC ++-->
   [vDISCH_TAC ----> vREPEAT vCONJ_TAC ----> vPOP_ASSUM vMP_TAC ---->
    vREPEAT(vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC) ---->
    vMATCH_MP_TAC(vREWRITE_RULE[vIMP_CONJ_ALT] vFINITE_SUBSET) ---->
    vREWRITE_TAC[vSUBSET; vIN_ELIM_THM] ----> vINT_ARITH_TAC;
    vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "&0:int <= r - l") ---->
    vASM_SIMP_TAC[vINT_ARITH (parse_term "~(&0 <= r - l:int) ==> ~(l <= x /\\ x <= r)")] ---->
    vASM_SIMP_TAC[vEMPTY_GSPEC; vFINITE_EMPTY] ---->
    vMATCH_MP_TAC vFINITE_SUBSET ---->
    vEXISTS_TAC (parse_term "IMAGE (\\n. l + &n) (0..num_of_int(r - l))") ---->
    vASM_SIMP_TAC[vFINITE_IMAGE; vFINITE_NUMSEG] ---->
    vREWRITE_TAC[vSUBSET; vIN_IMAGE; vIN_ELIM_THM] ---->
    vREWRITE_TAC[vGSYM vINT_OF_NUM_LE; vIN_NUMSEG] ---->
    vX_GEN_TAC (parse_term "x:int") ----> vSTRIP_TAC ----> vEXISTS_TAC (parse_term "num_of_int(x - l)") ---->
    vASM_SIMP_TAC[vINT_OF_NUM_OF_INT; vINT_SUB_LE] ----> vASM_INT_ARITH_TAC]);;

(* ------------------------------------------------------------------------- *)
(* Generic iteration of operation over set with finite support.              *)
(* ------------------------------------------------------------------------- *)

let neutral = new_definition
  (parse_term "neutral op = @x. !y. (op x y = y) /\\ (op y x = y)");;

let monoidal = new_definition
  (parse_term "monoidal op <=> (!x y. op x y = op y x) /\\\n                   (!x y z. op x (op y z) = op (op x y) z) /\\\n                   (!x:A. op (neutral op) x = x)");;

let vMONOIDAL_AC = try Cache.lookup_thm "MONOIDAL_AC" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> (!a. op (neutral op) a = a) /\\\n            (!a. op a (neutral op) = a) /\\\n            (!a b. op a b = op b a) /\\\n            (!a b c. op (op a b) c = op a (op b c)) /\\\n            (!a b c. op a (op b c) = op b (op a c))"),
  vREWRITE_TAC[monoidal] ----> vMESON_TAC[]);;

let support = new_definition
  (parse_term "support op (f:A->B) s = {x | x IN s /\\ ~(f x = neutral op)}");;

let iterate = new_definition
  (parse_term "iterate op (s:A->bool) f =\n        if FINITE(support op f s)\n        then ITSET (\\x a. op (f x) a) (support op f s) (neutral op)\n        else neutral op");;

let vIN_SUPPORT = try Cache.lookup_thm "IN_SUPPORT" with _ ->  prove
 ((parse_term "!op f x s. x IN (support op f s) <=> x IN s /\\ ~(f x = neutral op)"),
  vREWRITE_TAC[support; vIN_ELIM_THM]);;

let vSUPPORT_SUPPORT = try Cache.lookup_thm "SUPPORT_SUPPORT" with _ ->  prove
 ((parse_term "!op f s. support op f (support op f s) = support op f s"),
  vREWRITE_TAC[support; vIN_ELIM_THM; vEXTENSION] ----> vREWRITE_TAC[vCONJ_ACI]);;

let vSUPPORT_EMPTY = try Cache.lookup_thm "SUPPORT_EMPTY" with _ ->  prove
 ((parse_term "!op f s. (!x. x IN s ==> (f(x) = neutral op)) <=> (support op f s = {})"),
  vREWRITE_TAC[vIN_SUPPORT; vEXTENSION; vIN_ELIM_THM; vNOT_IN_EMPTY] ---->
  vMESON_TAC[]);;

let vSUPPORT_SUBSET = try Cache.lookup_thm "SUPPORT_SUBSET" with _ ->  prove
 ((parse_term "!op f s. (support op f s) SUBSET s"),
  vSIMP_TAC[vSUBSET; vIN_SUPPORT]);;

let vFINITE_SUPPORT = try Cache.lookup_thm "FINITE_SUPPORT" with _ ->  prove
 ((parse_term "!op f s. FINITE s ==> FINITE(support op f s)"),
  vMESON_TAC[vSUPPORT_SUBSET; vFINITE_SUBSET]);;

let vSUPPORT_CLAUSES = try Cache.lookup_thm "SUPPORT_CLAUSES" with _ ->  prove
 ((parse_term "(!f. support op f {} = {}) /\\\n   (!f x s. support op f (x INSERT s) =\n       if f(x) = neutral op then support op f s\n       else x INSERT (support op f s)) /\\\n   (!f x s. support op f (s DELETE x) = (support op f s) DELETE x) /\\\n   (!f s t. support op f (s UNION t) =\n                    (support op f s) UNION (support op f t)) /\\\n   (!f s t. support op f (s INTER t) =\n                    (support op f s) INTER (support op f t)) /\\\n   (!f s t. support op f (s DIFF t) =\n                    (support op f s) DIFF (support op f t)) /\\\n   (!f g s.  support op g (IMAGE f s) = IMAGE f (support op (g o f) s))"),
  vREWRITE_TAC[support; vEXTENSION; vIN_ELIM_THM; vIN_INSERT; vIN_DELETE; o_THM;
    vIN_IMAGE; vNOT_IN_EMPTY; vIN_UNION; vIN_INTER; vIN_DIFF; vCOND_RAND] ---->
  vREPEAT vSTRIP_TAC ----> vTRY vCOND_CASES_TAC ----> vASM_MESON_TAC[]);;

let vSUPPORT_DELTA = try Cache.lookup_thm "SUPPORT_DELTA" with _ ->  prove
 ((parse_term "!op s f a. support op (\\x. if x = a then f(x) else neutral op) s =\n              if a IN s then support op f {a} else {}"),
  vREWRITE_TAC[vEXTENSION; support; vIN_ELIM_THM; vIN_SING] ---->
  vREPEAT vGEN_TAC ----> vREPEAT vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vIN_ELIM_THM; vNOT_IN_EMPTY]);;

let vFINITE_SUPPORT_DELTA = try Cache.lookup_thm "FINITE_SUPPORT_DELTA" with _ ->  prove
 ((parse_term "!op f a. FINITE(support op (\\x. if x = a then f(x) else neutral op) s)"),
  vREWRITE_TAC[vSUPPORT_DELTA] ----> vREPEAT vGEN_TAC ---->
  vCOND_CASES_TAC ----> vSIMP_TAC[vFINITE_RULES; vFINITE_SUPPORT]);;

(* ------------------------------------------------------------------------- *)
(* Key lemmas about the generic notion.                                      *)
(* ------------------------------------------------------------------------- *)

let vITERATE_SUPPORT = try Cache.lookup_thm "ITERATE_SUPPORT" with _ ->  prove
 ((parse_term "!op f s. iterate op (support op f s) f = iterate op s f"),
  vSIMP_TAC[iterate; vSUPPORT_SUPPORT]);;

let vITERATE_EXPAND_CASES = try Cache.lookup_thm "ITERATE_EXPAND_CASES" with _ ->  prove
 ((parse_term "!op f s. iterate op s f =\n              if FINITE(support op f s) then iterate op (support op f s) f\n              else neutral op"),
  vSIMP_TAC[iterate; vSUPPORT_SUPPORT]);;

let vITERATE_CLAUSES_GEN = try Cache.lookup_thm "ITERATE_CLAUSES_GEN" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> (!(f:A->B). iterate op {} f = neutral op) /\\\n            (!f x s. FINITE(support op (f:A->B) s)\n                     ==> (iterate op (x INSERT s) f =\n                                if x IN s then iterate op s f\n                                else op (f x) (iterate op s f)))"),
  vGEN_TAC ----> vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vAND_FORALL_THM] ----> vGEN_TAC ---->
  vMP_TAC(vISPECL [(parse_term "\\x a. (op:B->B->B) ((f:A->B)(x)) a"); (parse_term "neutral op :B")]
   vFINITE_RECURSION) ---->
  vANTS_TAC ++--> [vASM_MESON_TAC[monoidal]; vALL_TAC] ---->
  vREPEAT vSTRIP_TAC ---->
  vASM_REWRITE_TAC[iterate; vSUPPORT_CLAUSES; vFINITE_RULES] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRATOR_CONV -| vLAND_CONV) [vCOND_RAND] ---->
  vASM_REWRITE_TAC[vSUPPORT_CLAUSES; vFINITE_INSERT; vCOND_ID] ---->
  vASM_CASES_TAC (parse_term "(f:A->B) x = neutral op") ---->
  vASM_SIMP_TAC[vIN_SUPPORT] ----> vCOND_CASES_TAC ----> vASM_MESON_TAC[monoidal]);;

let vITERATE_CLAUSES = try Cache.lookup_thm "ITERATE_CLAUSES" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> (!f. iterate op {} f = neutral op) /\\\n            (!f x s. FINITE(s)\n                     ==> (iterate op (x INSERT s) f =\n                          if x IN s then iterate op s f\n                          else op (f x) (iterate op s f)))"),
  vSIMP_TAC[vITERATE_CLAUSES_GEN; vFINITE_SUPPORT]);;

let vITERATE_UNION = try Cache.lookup_thm "ITERATE_UNION" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f s t. FINITE s /\\ FINITE t /\\ DISJOINT s t\n                    ==> (iterate op (s UNION t) f =\n                         op (iterate op s f) (iterate op t f))"),
  let lemma = prove
   ((parse_term "(s UNION (x INSERT t) = x INSERT (s UNION t)) /\\\n     (DISJOINT s (x INSERT t) <=> ~(x IN s) /\\ DISJOINT s t)"),
    vSET_TAC[]) in
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ----> vGEN_TAC ---->
  vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ----> vREPEAT vDISCH_TAC ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vASM_SIMP_TAC[vITERATE_CLAUSES; vIN_UNION; vUNION_EMPTY; vREAL_ADD_RID; lemma;
               vFINITE_UNION] ---->
  vASM_MESON_TAC[monoidal]);;

let vITERATE_UNION_GEN = try Cache.lookup_thm "ITERATE_UNION_GEN" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !(f:A->B) s t. FINITE(support op f s) /\\ FINITE(support op f t) /\\\n                           DISJOINT (support op f s) (support op f t)\n                           ==> (iterate op (s UNION t) f =\n                                op (iterate op s f) (iterate op t f))"),
  vONCE_REWRITE_TAC[vGSYM vITERATE_SUPPORT] ---->
  vSIMP_TAC[vSUPPORT_CLAUSES; vITERATE_UNION]);;

let vITERATE_DIFF = try Cache.lookup_thm "ITERATE_DIFF" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f s t. FINITE s /\\ t SUBSET s\n                    ==> (op (iterate op (s DIFF t) f) (iterate op t f) =\n                         iterate op s f)"),
  let lemma = prove
   ((parse_term "t SUBSET s ==> (s = (s DIFF t) UNION t) /\\ DISJOINT (s DIFF t) t"),
    vSET_TAC[]) in
  vMESON_TAC[lemma; vITERATE_UNION; vFINITE_UNION; vFINITE_SUBSET; vSUBSET_DIFF]);;

let vITERATE_DIFF_GEN = try Cache.lookup_thm "ITERATE_DIFF_GEN" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f:A->B s t. FINITE (support op f s) /\\\n                         (support op f t) SUBSET (support op f s)\n                         ==> (op (iterate op (s DIFF t) f) (iterate op t f) =\n                              iterate op s f)"),
  vONCE_REWRITE_TAC[vGSYM vITERATE_SUPPORT] ---->
  vSIMP_TAC[vSUPPORT_CLAUSES; vITERATE_DIFF]);;

let vITERATE_INCL_EXCL = try Cache.lookup_thm "ITERATE_INCL_EXCL" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !s t f. FINITE s /\\ FINITE t\n                    ==> op (iterate op s f) (iterate op t f) =\n                        op (iterate op (s UNION t) f)\n                           (iterate op (s INTER t) f)"),
  vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vSET_RULE
    (parse_term "a UNION b = ((a DIFF b) UNION (b DIFF a)) UNION (a INTER b)")] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV -| vONCE_DEPTH_CONV)
    [vSET_RULE (parse_term "s:A->bool = s DIFF t UNION s INTER t")] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV -| vONCE_DEPTH_CONV)
    [vSET_RULE (parse_term "t:A->bool = t DIFF s UNION s INTER t")] ---->
  vASM_SIMP_TAC[vITERATE_UNION; vFINITE_UNION; vFINITE_DIFF; vFINITE_INTER;
    vSET_RULE (parse_term "DISJOINT (s DIFF s' UNION s' DIFF s) (s INTER s')");
    vSET_RULE (parse_term "DISJOINT (s DIFF s') (s' DIFF s)");
    vSET_RULE (parse_term "DISJOINT (s DIFF s') (s' INTER s)");
    vSET_RULE (parse_term "DISJOINT (s DIFF s') (s INTER s')")] ---->
  vFIRST_X_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vMONOIDAL_AC th]));;

let vITERATE_CLOSED = try Cache.lookup_thm "ITERATE_CLOSED" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !P. P(neutral op) /\\ (!x y. P x /\\ P y ==> P (op x y))\n                ==> !f:A->B s. (!x. x IN s /\\ ~(f x = neutral op) ==> P(f x))\n                               ==> P(iterate op s f)"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vITERATE_EXPAND_CASES] ---->
  vREPEAT(vPOP_ASSUM vMP_TAC) ----> vREWRITE_TAC[vGSYM vIN_SUPPORT] ---->
  vCOND_CASES_TAC ----> vASM_SIMP_TAC[] ----> vPOP_ASSUM vMP_TAC ---->
  vSPEC_TAC((parse_term "support op (f:A->B) s"),(parse_term "s:A->bool")) ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vASM_SIMP_TAC[vITERATE_CLAUSES; vFINITE_INSERT; vIN_INSERT]);;

let vITERATE_RELATED = try Cache.lookup_thm "ITERATE_RELATED" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !R. R (neutral op) (neutral op) /\\\n                (!x1 y1 x2 y2. R x1 x2 /\\ R y1 y2 ==> R (op x1 y1) (op x2 y2))\n                ==> !f:A->B g s.\n                      FINITE s /\\\n                      (!x. x IN s ==> R (f x) (g x))\n                      ==> R (iterate op s f) (iterate op s g)"),
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ----> vSTRIP_TAC ----> vGEN_TAC ---->
  vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vASM_SIMP_TAC[vITERATE_CLAUSES; vFINITE_INSERT; vIN_INSERT]);;

let vITERATE_EQ_NEUTRAL = try Cache.lookup_thm "ITERATE_EQ_NEUTRAL" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f:A->B s. (!x. x IN s ==> (f(x) = neutral op))\n                       ==> (iterate op s f = neutral op)"),
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "support op (f:A->B) s = {}") vASSUME_TAC ++-->
   [vASM_MESON_TAC[vEXTENSION; vNOT_IN_EMPTY; vIN_SUPPORT];
    vASM_MESON_TAC[vITERATE_CLAUSES; vFINITE_RULES; vITERATE_SUPPORT]]);;

let vITERATE_SING = try Cache.lookup_thm "ITERATE_SING" with _ ->  prove
 ((parse_term "!op. monoidal op ==> !f:A->B x. (iterate op {x} f = f x)"),
  vSIMP_TAC[vITERATE_CLAUSES; vFINITE_RULES; vNOT_IN_EMPTY] ---->
  vMESON_TAC[monoidal]);;

let vITERATE_CLOSED_NONEMPTY = try Cache.lookup_thm "ITERATE_CLOSED_NONEMPTY" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !P. (!x y. P x /\\ P y ==> P (op x y))\n                ==> !f:A->B s. FINITE s /\\ ~(s = {}) /\\\n                               (!x. x IN s ==> P(f x))\n                               ==> P(iterate op s f)"),
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ---->
  vREWRITE_TAC[vIMP_CONJ] ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vFORALL_IN_INSERT; vNOT_IN_EMPTY; vNOT_INSERT_EMPTY] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "a:A"); (parse_term "t:A->bool")] ---->
  vASM_CASES_TAC (parse_term "t:A->bool = {}") ---->
  vASM_SIMP_TAC[vITERATE_SING] ---->  vASM_SIMP_TAC[vITERATE_CLAUSES]);;

let vITERATE_RELATED_NONEMPTY = try Cache.lookup_thm "ITERATE_RELATED_NONEMPTY" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !R. (!x1 y1 x2 y2. R x1 x2 /\\ R y1 y2 ==> R (op x1 y1) (op x2 y2))\n                ==> !f:A->B g s.\n                      FINITE s /\\\n                      ~(s = {}) /\\\n                      (!x. x IN s ==> R (f x) (g x))\n                      ==> R (iterate op s f) (iterate op s g)"),
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ---->
  vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vFORALL_IN_INSERT; vNOT_IN_EMPTY; vNOT_INSERT_EMPTY] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "a:A"); (parse_term "t:A->bool")] ---->
  vASM_CASES_TAC (parse_term "t:A->bool = {}") ---->
  vASM_SIMP_TAC[vITERATE_SING] ---->  vASM_SIMP_TAC[vITERATE_CLAUSES]);;

let vITERATE_DELETE = try Cache.lookup_thm "ITERATE_DELETE" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f:A->B s a. FINITE s /\\ a IN s\n                         ==> op (f a) (iterate op (s DELETE a) f) =\n                             iterate op s f"),
  vMESON_TAC[vITERATE_CLAUSES; vFINITE_DELETE; vIN_DELETE; vINSERT_DELETE]);;

let vITERATE_DELTA = try Cache.lookup_thm "ITERATE_DELTA" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f a s. iterate op s (\\x. if x = a then f(x) else neutral op) =\n                    if a IN s then f(a) else neutral op"),
  vGEN_TAC ----> vDISCH_TAC ----> vONCE_REWRITE_TAC[vGSYM vITERATE_SUPPORT] ---->
  vREWRITE_TAC[vSUPPORT_DELTA] ----> vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vITERATE_CLAUSES] ----> vREWRITE_TAC[vSUPPORT_CLAUSES] ---->
  vCOND_CASES_TAC ----> vASM_SIMP_TAC[vITERATE_CLAUSES; vITERATE_SING]);;

let vITERATE_IMAGE = try Cache.lookup_thm "ITERATE_IMAGE" with _ ->  prove
 ((parse_term "!op. monoidal op\n       ==> !f:A->B g:B->C s.\n                (!x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y))\n                ==> (iterate op (IMAGE f s) g = iterate op s (g o f))"),
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ----> vGEN_TAC ---->
  vSUBGOAL_THEN
   (parse_term "!s. FINITE s /\\\n        (!x y:A. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y))\n        ==> (iterate op (IMAGE f s) (g:B->C) = iterate op s (g o f))")
  vASSUME_TAC ++-->
   [vREWRITE_TAC[vIMP_CONJ] ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
    vASM_SIMP_TAC[vITERATE_CLAUSES; vIMAGE_CLAUSES; vFINITE_IMAGE] ---->
    vREWRITE_TAC[o_THM; vIN_INSERT] ----> vASM_MESON_TAC[vIN_IMAGE];
    vGEN_TAC ----> vDISCH_TAC ----> vONCE_REWRITE_TAC[vITERATE_EXPAND_CASES] ---->
    vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC(vTAUT
     (parse_term "(a <=> a') /\\ (a' ==> (b = b'))\n      ==> (if a then b else c) = (if a' then b' else c)")) ---->
    vREWRITE_TAC[vSUPPORT_CLAUSES] ----> vREPEAT vSTRIP_TAC ++-->
     [vMATCH_MP_TAC vFINITE_IMAGE_INJ_EQ ----> vASM_MESON_TAC[vIN_SUPPORT];
      vFIRST_X_ASSUM vMATCH_MP_TAC ----> vASM_MESON_TAC[vIN_SUPPORT]]]);;

let vITERATE_BIJECTION = try Cache.lookup_thm "ITERATE_BIJECTION" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==>  !f:A->B p s.\n                (!x. x IN s ==> p(x) IN s) /\\\n                (!y. y IN s ==> ?!x. x IN s /\\ p(x) = y)\n                ==> iterate op s f = iterate op s (f o p)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "iterate op (IMAGE (p:A->A) s) (f:A->B)") ----> vCONJ_TAC ++-->
   [vAP_THM_TAC ----> vAP_TERM_TAC ----> vREWRITE_TAC[vEXTENSION; vIN_IMAGE];
    vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP
      (vINST_TYPE [aty,bty] vITERATE_IMAGE))] ---->
  vASM_MESON_TAC[]);;

let vITERATE_ITERATE_PRODUCT = try Cache.lookup_thm "ITERATE_ITERATE_PRODUCT" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !s:A->bool t:A->B->bool x:A->B->C.\n                FINITE s /\\ (!i. i IN s ==> FINITE(t i))\n                ==> iterate op s (\\i. iterate op (t i) (x i)) =\n                    iterate op {i,j | i IN s /\\ j IN t i} (\\(i,j). x i j)"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vASM_SIMP_TAC[vNOT_IN_EMPTY; vSET_RULE (parse_term "{a,b | F} = {}"); vITERATE_CLAUSES] ---->
  vREWRITE_TAC[vSET_RULE (parse_term "{i,j | i IN a INSERT s /\\ j IN t i} =\n            IMAGE (\\j. a,j) (t a) UNION {i,j | i IN s /\\ j IN t i}")] ---->
  vASM_SIMP_TAC[vFINITE_INSERT; vITERATE_CLAUSES; vIN_INSERT] ---->
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(fun th ->
   vW(vMP_TAC -| vPART_MATCH (lhand -| rand) (vMATCH_MP vITERATE_UNION th) -|
   rand -| snd)) ---->
  vANTS_TAC ++-->
   [vASM_SIMP_TAC[vFINITE_IMAGE; vFINITE_PRODUCT_DEPENDENT; vIN_INSERT] ---->
    vREWRITE_TAC[vDISJOINT; vEXTENSION; vIN_IMAGE; vIN_INTER; vNOT_IN_EMPTY;
                vIN_ELIM_THM; vEXISTS_PAIR_THM; vFORALL_PAIR_THM; vPAIR_EQ] ---->
    vASM_MESON_TAC[];
    vALL_TAC] ---->
  vDISCH_THEN vSUBST1_TAC ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vFIRST_ASSUM(fun th ->
   vW(vMP_TAC -| vPART_MATCH (lhand -| rand) (vMATCH_MP vITERATE_IMAGE th) -|
   rand -| snd)) ---->
  vANTS_TAC ++-->
   [vSIMP_TAC[vFORALL_PAIR_THM] ----> vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ---->
    vASM_SIMP_TAC[vPAIR_EQ];
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[o_DEF] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ----> vREWRITE_TAC[vETA_AX]]);;

let vITERATE_EQ = try Cache.lookup_thm "ITERATE_EQ" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f:A->B g s.\n              (!x. x IN s ==> f x = g x) ==> iterate op s f = iterate op s g"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vITERATE_EXPAND_CASES] ---->
  vSUBGOAL_THEN (parse_term "support op g s = support op (f:A->B) s") vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_SUPPORT] ----> vASM_MESON_TAC[]; vALL_TAC] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
  vSUBGOAL_THEN
   (parse_term "FINITE(support op (f:A->B) s) /\\\n    (!x. x IN (support op f s) ==> f x = g x)")
  vMP_TAC ++--> [vASM_MESON_TAC[vIN_SUPPORT]; vREWRITE_TAC[vIMP_CONJ]] ---->
  vSPEC_TAC((parse_term "support op (f:A->B) s"),(parse_term "t:A->bool")) ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ----> vASM_SIMP_TAC[vITERATE_CLAUSES] ---->
  vMESON_TAC[vIN_INSERT]);;

let vITERATE_RESTRICT_SET = try Cache.lookup_thm "ITERATE_RESTRICT_SET" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !P s f:A->B. iterate op {x | x IN s /\\ P x} f =\n                         iterate op s (\\x. if P x then f x else neutral op)"),
  vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vITERATE_SUPPORT] ---->
  vREWRITE_TAC[support; vIN_ELIM_THM] ---->
  vREWRITE_TAC[vMESON[] (parse_term "~((if P x then f x else a) = a) <=> P x /\\ ~(f x = a)");
              vGSYM vCONJ_ASSOC] ---->
  vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_EQ) ---->
  vSIMP_TAC[vIN_ELIM_THM]);;

let vITERATE_EQ_GENERAL = try Cache.lookup_thm "ITERATE_EQ_GENERAL" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !s:A->bool t:B->bool f:A->C g h.\n                (!y. y IN t ==> ?!x. x IN s /\\ h(x) = y) /\\\n                (!x. x IN s ==> h(x) IN t /\\ g(h x) = f x)\n                ==> iterate op s f = iterate op t g"),
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "t = IMAGE (h:A->B) s") vSUBST1_TAC ++-->
   [vREWRITE_TAC[vEXTENSION; vIN_IMAGE] ----> vASM_MESON_TAC[]; vALL_TAC] ---->
  vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "iterate op s ((g:B->C) o (h:A->B))") ----> vCONJ_TAC ++-->
   [vASM_MESON_TAC[vITERATE_EQ; o_THM];
    vCONV_TAC vSYM_CONV ---->
    vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_IMAGE) ---->
    vASM_MESON_TAC[]]);;

let vITERATE_EQ_GENERAL_INVERSES = try Cache.lookup_thm "ITERATE_EQ_GENERAL_INVERSES" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !s:A->bool t:B->bool f:A->C g h k.\n                (!y. y IN t ==> k(y) IN s /\\ h(k y) = y) /\\\n                (!x. x IN s ==> h(x) IN t /\\ k(h x) = x /\\ g(h x) = f x)\n                ==> iterate op s f = iterate op t g"),
  vREPEAT vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_EQ_GENERAL) ---->
  vEXISTS_TAC (parse_term "h:A->B") ----> vASM_MESON_TAC[]);;

let vITERATE_INJECTION = try Cache.lookup_thm "ITERATE_INJECTION" with _ ->  prove
 ((parse_term "!op. monoidal op\n          ==> !f:A->B p:A->A s.\n                      FINITE s /\\\n                      (!x. x IN s ==> p x IN s) /\\\n                      (!x y. x IN s /\\ y IN s /\\ p x = p y ==> x = y)\n                      ==> iterate op s (f o p) = iterate op s f"),
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vSYM_CONV ---->
  vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_BIJECTION) ---->
  vMP_TAC(vISPECL [(parse_term "s:A->bool"); (parse_term "p:A->A")] vSURJECTIVE_IFF_INJECTIVE) ---->
  vASM_REWRITE_TAC[vSUBSET; vIN_IMAGE] ----> vASM_MESON_TAC[]);;

let vITERATE_UNION_NONZERO = try Cache.lookup_thm "ITERATE_UNION_NONZERO" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f:A->B s t.\n                FINITE(s) /\\ FINITE(t) /\\\n                (!x. x IN (s INTER t) ==> f x = neutral(op))\n                ==> iterate op (s UNION t) f =\n                    op (iterate op s f) (iterate op t f)"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vITERATE_SUPPORT] ---->
  vREWRITE_TAC[vSUPPORT_CLAUSES] ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_UNION) ---->
  vASM_SIMP_TAC[vFINITE_SUPPORT; vDISJOINT; vIN_INTER; vIN_SUPPORT; vEXTENSION] ---->
  vASM_MESON_TAC[vIN_INTER; vNOT_IN_EMPTY]);;

let vITERATE_OP = try Cache.lookup_thm "ITERATE_OP" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f g s. FINITE s\n                    ==> iterate op s (\\x. op (f x) (g x)) =\n                        op (iterate op s f) (iterate op s g)"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vGEN_TAC ----> vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vASM_SIMP_TAC[vITERATE_CLAUSES; vMONOIDAL_AC]);;

let vITERATE_SUPERSET = try Cache.lookup_thm "ITERATE_SUPERSET" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f:A->B u v.\n                u SUBSET v /\\\n                (!x. x IN v /\\ ~(x IN u) ==> f(x) = neutral op)\n                ==> iterate op v f = iterate op u f"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vITERATE_SUPPORT] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vREWRITE_TAC[support; vEXTENSION; vIN_ELIM_THM] ----> vASM_MESON_TAC[vSUBSET]);;

let vITERATE_UNIV = try Cache.lookup_thm "ITERATE_UNIV" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f:A->B s. support op f UNIV SUBSET s\n                  ==> iterate op s f = iterate op UNIV f"),
  vREWRITE_TAC[support; vSUBSET; vIN_ELIM_THM] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vSYM_CONV ---->
  vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_SUPERSET) ---->
  vASM vSET_TAC[]);;

let vITERATE_SWAP = try Cache.lookup_thm "ITERATE_SWAP" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f:A->B->C s t.\n                FINITE s /\\ FINITE t\n                ==> iterate op s (\\i. iterate op t (f i)) =\n                    iterate op t (\\j. iterate op s (\\i. f i j))"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vASM_SIMP_TAC[vITERATE_CLAUSES] ---->
  vASM_SIMP_TAC[vITERATE_EQ_NEUTRAL; vGSYM vITERATE_OP]);;

let vITERATE_IMAGE_NONZERO = try Cache.lookup_thm "ITERATE_IMAGE_NONZERO" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !g:B->C f:A->B s.\n                    FINITE s /\\\n                    (!x y. x IN s /\\ y IN s /\\ ~(x = y) /\\ f x = f y\n                           ==> g(f x) = neutral op)\n                    ==> iterate op (IMAGE f s) g = iterate op s (g o f)"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vGEN_TAC ----> vGEN_TAC ----> vONCE_REWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vASM_SIMP_TAC[vIMAGE_CLAUSES; vITERATE_CLAUSES; vFINITE_IMAGE] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "a:A"); (parse_term "s:A->bool")] ---->
  vREWRITE_TAC[vIN_INSERT] ----> vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "iterate op s ((g:B->C) o (f:A->B)) = iterate op (IMAGE f s) g")
  vSUBST1_TAC ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[vIN_IMAGE] ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[o_THM] ---->
  vSUBGOAL_THEN (parse_term "(g:B->C) ((f:A->B) a) = neutral op") vSUBST1_TAC ---->
  vASM_MESON_TAC[vMONOIDAL_AC]);;

let vITERATE_IMAGE_GEN = try Cache.lookup_thm "ITERATE_IMAGE_GEN" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f:A->B g:A->C s.\n                FINITE s\n                ==> iterate op s g =\n                    iterate op (IMAGE f s)\n                       (\\y. iterate op {x | x IN s /\\ f x = y} g)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vEQ_TRANS ----> vEXISTS_TAC
   (parse_term "iterate op s (\\x:A. iterate op {y:B | y IN IMAGE f s /\\ (f x = y)}\n       (\\y. (g:A->C) x))") ---->
  vCONJ_TAC ++-->
   [vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_EQ) ---->
    vASM_REWRITE_TAC[] ----> vX_GEN_TAC (parse_term "x:A") ----> vDISCH_TAC ---->
    vSUBGOAL_THEN (parse_term "{y | y IN IMAGE (f:A->B) s /\\ f x = y} = {(f x)}")
    vSUBST1_TAC ++--> [vASM vSET_TAC[]; vASM_SIMP_TAC[vITERATE_SING]];
    vASM_SIMP_TAC[vITERATE_RESTRICT_SET] ---->
    vFIRST_ASSUM(fun th -> vW(vMP_TAC -| vPART_MATCH (lhand -| rand)
     (vMATCH_MP vITERATE_SWAP th) -| lhand -| snd)) ---->
    vASM_SIMP_TAC[vFINITE_IMAGE]]);;

let vITERATE_CASES = try Cache.lookup_thm "ITERATE_CASES" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !s P f g:A->B.\n                FINITE s\n                ==> iterate op s (\\x. if P x then f x else g x) =\n                    op (iterate op {x | x IN s /\\ P x} f)\n                       (iterate op {x | x IN s /\\ ~P x} g)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC
   (parse_term "op (iterate op {x | x IN s /\\ P x} (\\x. if P x then f x else (g:A->B) x))\n       (iterate op {x | x IN s /\\ ~P x} (\\x. if P x then f x else g x))") ---->
  vCONJ_TAC ++-->
   [vFIRST_ASSUM(fun th -> vASM_SIMP_TAC[vGSYM(vMATCH_MP vITERATE_UNION th);
      vFINITE_RESTRICT;
      vSET_RULE (parse_term "DISJOINT {x | x IN s /\\ P x} {x | x IN s /\\ ~P x}")]) ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ----> vSET_TAC[];
    vBINOP_TAC ----> vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_EQ) ---->
    vSIMP_TAC[vIN_ELIM_THM]]);;

let vITERATE_OP_GEN = try Cache.lookup_thm "ITERATE_OP_GEN" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f g:A->B s.\n                FINITE(support op f s) /\\ FINITE(support op g s)\n                ==> iterate op s (\\x. op (f x) (g x)) =\n                    op (iterate op s f) (iterate op s g)"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vITERATE_SUPPORT] ---->
  vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "iterate op (support op f s UNION support op g s)\n                         (\\x. op ((f:A->B) x) (g x))") ---->
  vCONJ_TAC ++-->
   [vCONV_TAC vSYM_CONV;
    vASM_SIMP_TAC[vITERATE_OP; vFINITE_UNION] ----> vBINOP_TAC] ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_SUPERSET) ---->
  vREWRITE_TAC[support; vIN_ELIM_THM; vSUBSET; vIN_UNION] ---->
  vASM_MESON_TAC[monoidal]);;

let vITERATE_CLAUSES_NUMSEG = try Cache.lookup_thm "ITERATE_CLAUSES_NUMSEG" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> (!m. iterate op (m..0) f = if m = 0 then f(0) else neutral op) /\\\n            (!m n. iterate op (m..SUC n) f =\n                      if m <= SUC n then op (iterate op (m..n) f) (f(SUC n))\n                      else iterate op (m..n) f)"),
  vREWRITE_TAC[vNUMSEG_CLAUSES] ----> vREPEAT vSTRIP_TAC ---->
  vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vITERATE_CLAUSES; vFINITE_NUMSEG; vIN_NUMSEG; vFINITE_EMPTY] ---->
  vREWRITE_TAC[vARITH_RULE (parse_term "~(SUC n <= n)"); vNOT_IN_EMPTY] ---->
  vASM_MESON_TAC[monoidal]);;

let vITERATE_CLAUSES_NUMSEG_LT = try Cache.lookup_thm "ITERATE_CLAUSES_NUMSEG_LT" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> iterate op {i | i < 0} f = neutral op /\\\n            (!k. iterate op {i | i < SUC k} f =\n                 op (iterate op {i | i < k} f) (f k))"),
  vSIMP_TAC[vNUMSEG_CLAUSES_LT; vITERATE_CLAUSES; vFINITE_NUMSEG_LT] ---->
  vREWRITE_TAC[vIN_ELIM_THM; vLT_REFL; monoidal] ----> vMESON_TAC[]);;

let vITERATE_CLAUSES_NUMSEG_LE = try Cache.lookup_thm "ITERATE_CLAUSES_NUMSEG_LE" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> iterate op {i | i <= 0} f = f 0 /\\\n            (!k. iterate op {i | i <= SUC k} f =\n                 op (iterate op {i | i <= k} f) (f(SUC k)))"),
  vSIMP_TAC[vNUMSEG_CLAUSES_LE; vITERATE_CLAUSES;
           vFINITE_NUMSEG_LE; vITERATE_SING] ---->
  vREWRITE_TAC[monoidal; vIN_ELIM_THM; vARITH_RULE (parse_term "~(SUC k <= k)")] ---->
  vMESON_TAC[]);;

let vITERATE_PAIR = try Cache.lookup_thm "ITERATE_PAIR" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f m n. iterate op (2*m..2*n+1) f =\n                    iterate op (m..n) (\\i. op (f(2*i)) (f(2*i+1)))"),
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ----> vGEN_TAC ---->
  vINDUCT_TAC ----> vCONV_TAC vNUM_REDUCE_CONV ++-->
   [vASM_SIMP_TAC[num_CONV (parse_term "1"); vITERATE_CLAUSES_NUMSEG] ---->
    vREWRITE_TAC[vARITH_RULE (parse_term "2 * m <= SUC 0 <=> m = 0")] ---->
    vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vMULT_EQ_0; vARITH];
    vREWRITE_TAC[vARITH_RULE (parse_term "2 * SUC n + 1 = SUC(SUC(2 * n + 1))")] ---->
    vASM_SIMP_TAC[vITERATE_CLAUSES_NUMSEG] ---->
    vREWRITE_TAC[vARITH_RULE (parse_term "2 * m <= SUC(SUC(2 * n + 1)) <=> m <= SUC n");
                vARITH_RULE (parse_term "2 * m <= SUC(2 * n + 1) <=> m <= SUC n")] ---->
    vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vARITH_RULE (parse_term "2 * SUC n = SUC(2 * n + 1)");
                vARITH_RULE (parse_term "2 * SUC n + 1 = SUC(SUC(2 * n + 1))")] ---->
    vASM_MESON_TAC[monoidal]]);;

let vITERATE_REFLECT = try Cache.lookup_thm "ITERATE_REFLECT" with _ ->  prove
 ((parse_term "!op:A->A->A.\n        monoidal op\n        ==> !x m n. iterate op (m..n) x =\n                    if n < m then neutral op\n                    else iterate op (0..n-m) (\\i. x(n - i))"),
  vREWRITE_TAC[vGSYM vNUMSEG_EMPTY] ----> vREPEAT vSTRIP_TAC ---->
  vCOND_CASES_TAC ++-->
   [vASM_MESON_TAC[vITERATE_CLAUSES];
    vRULE_ASSUM_TAC(vREWRITE_RULE[vNUMSEG_EMPTY; vNOT_LT])] ---->
  vFIRST_ASSUM(vMP_TAC -|
   vISPECL [(parse_term "\\i:num. n - i"); (parse_term "x:num->A"); (parse_term "0..n-m")] -|
   vMATCH_MP (vINST_TYPE [(parse_type "X"),(parse_type "A")] vITERATE_IMAGE)) ---->
  vREWRITE_TAC[o_DEF; vIN_NUMSEG] ---->
  vANTS_TAC ++--> [vARITH_TAC; vDISCH_THEN(vSUBST1_TAC -| vSYM)] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vREWRITE_TAC[vEXTENSION; vIN_IMAGE; vIN_NUMSEG] ---->
  vREWRITE_TAC[vUNWIND_THM2; vARITH_RULE
    (parse_term "x = n - y /\\ 0 <= y /\\ y <= n - m <=>\n     y = n - x /\\ x <= n /\\ y <= n - m")] ---->
  vASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* A more general notion of iteration, using a specific order (<<=)          *)
(* and hence applying to non-commutative operations, as well as giving       *)
(* more refined notions of domain ("dom") and neutral element ("neut").      *)
(* Otherwise it tries to be stylistically similar to "iterate" above.        *)
(* ------------------------------------------------------------------------- *)

let iterato = (new_specification ["iterato"] -| prove)
 ((parse_term "?itty.\n      !dom neut op (<<=) k (f:K->A).\n         itty dom neut op (<<=) k f =\n         if FINITE {i | i IN k /\\ f i IN dom DIFF {neut}} /\\\n            ~({i | i IN k /\\ f i IN dom DIFF {neut}} = {})\n         then let i = if ?i. i IN k /\\ f i IN dom DIFF {neut} /\\\n                             !j. j <<= i /\\ j IN k /\\ f j IN dom DIFF {neut}\n                                 ==> j = i\n                       then @i. i IN k /\\ f i IN dom DIFF {neut} /\\\n                                !j. j <<= i /\\ j IN k /\\\n                                    f j IN dom DIFF {neut}\n                                    ==> j = i\n                       else @i. i IN k /\\ f i IN dom DIFF {neut} in\n              op (f i) (itty dom neut op (<<=)\n                          {j | j IN k DELETE i /\\ f j IN dom DIFF {neut}} f)\n         else neut"),
  vREPLICATE_TAC 4 (vONCE_REWRITE_TAC[vGSYM vSKOLEM_THM]) ----> vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC vI [vEXISTS_SWAP_FUN_THM] ----> vREWRITE_TAC[] ---->
  vGEN_REWRITE_TAC vBINDER_CONV [vSWAP_FORALL_THM] ---->
  vONCE_REWRITE_TAC[vGSYM vSKOLEM_THM] ----> vGEN_TAC ---->
  vMATCH_MP_TAC(vMATCH_MP vWF_REC (vISPEC
   (parse_term "\\k. CARD {i | i IN k /\\ (f:K->A) i IN dom DIFF {neut}}") vWF_MEASURE)) ---->
  vREWRITE_TAC[vMEASURE] ----> vREPEAT vSTRIP_TAC ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
  vLET_TAC ----> vCONV_TAC(vONCE_DEPTH_CONV let_CONV) ---->
  vAP_TERM_TAC ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
  vREWRITE_TAC[vSET_RULE
   (parse_term "{i | i IN k DIFF {a} /\\ P i} = {i | i IN k /\\ P i} DELETE a")] ---->
  vMATCH_MP_TAC vCARD_PSUBSET ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vPSUBSET_ALT] ----> vCONJ_TAC ++--> [vSET_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[vIN_ELIM_THM; vIN_DELETE; vGSYM vCONJ_ASSOC] ---->
  vREWRITE_TAC[vSET_RULE (parse_term "p /\\ q /\\ ~(p /\\ ~r /\\ q) <=> r /\\ p /\\ q")] ---->
  vREWRITE_TAC[vUNWIND_THM2] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vREWRITE_RULE[vGSYM vMEMBER_NOT_EMPTY] -| vCONJUNCT2) ---->
  vREWRITE_TAC[vIN_ELIM_THM; vIN_DELETE] ----> vASM_MESON_TAC[]);;

let vITERATO_SUPPORT = try Cache.lookup_thm "ITERATO_SUPPORT" with _ ->  prove
 ((parse_term "!dom neut op (<<=) k (f:K->A).\n        iterato dom neut op (<<=) {i | i IN k /\\ f i IN dom DIFF {neut}} f =\n        iterato dom neut op (<<=) k f"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[iterato] ---->
  vREWRITE_TAC[vCONJ_ASSOC; vSET_RULE (parse_term "y IN {x | x IN s /\\ P x} /\\ P y <=>\n                        y IN {x | x IN s /\\ P x}")] ---->
  vREWRITE_TAC[vIN_ELIM_THM; vGSYM vCONJ_ASSOC] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ----> vLET_TAC ---->
  vCONV_TAC(vONCE_DEPTH_CONV let_CONV) ----> vAP_TERM_TAC ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vASM vSET_TAC[]);;

let vITERATO_EXPAND_CASES = try Cache.lookup_thm "ITERATO_EXPAND_CASES" with _ ->  prove
 ((parse_term "!dom neut op (<<=) k (f:K->A).\n        iterato dom neut op (<<=) k f =\n        if FINITE {i | i IN k /\\ f i IN dom DIFF {neut}}\n        then iterato dom neut op (<<=) {i | i IN k /\\ f i IN dom DIFF {neut}} f\n        else neut"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ++-->
   [vREWRITE_TAC[vITERATO_SUPPORT];
    vGEN_REWRITE_TAC vLAND_CONV [iterato] ----> vASM_REWRITE_TAC[]]);;

let vITERATO_CLAUSES_GEN = try Cache.lookup_thm "ITERATO_CLAUSES_GEN" with _ ->  prove
 ((parse_term "!dom neut op (<<=) (f:K->A).\n        (iterato dom neut op (<<=) {} f = neut) /\\\n        (!i k. FINITE {j | j IN k /\\ f j IN dom DIFF {neut}} /\\\n               (!j. j IN k ==> i = j \\/ i <<= j \\/ j <<= i) /\\\n               (!j. j <<= i /\\ j IN k /\\ f j IN dom DIFF {neut} ==> j = i)\n               ==> iterato dom neut op (<<=) (i INSERT k) f =\n                   if f i IN dom ==> f i = neut \\/ i IN k\n                   then iterato dom neut op (<<=) k f\n                   else op (f i) (iterato dom neut op (<<=) k f))"),
  vREPEAT vGEN_TAC ----> vCONJ_TAC ++-->
   [vGEN_REWRITE_TAC vLAND_CONV [iterato] ---->
    vASM_REWRITE_TAC[vNOT_IN_EMPTY; vEMPTY_GSPEC];
    vREPEAT vGEN_TAC ----> vSTRIP_TAC] ---->
  vASM_CASES_TAC (parse_term "(i:K) IN k") ---->
  vASM_SIMP_TAC[vCOND_SWAP; vSET_RULE (parse_term "i IN k ==> i INSERT k = k")] ---->
  vREWRITE_TAC[vSET_RULE (parse_term "x IN dom ==> x = a <=> ~(x IN dom DIFF {a})")] ---->
  vREWRITE_TAC[vCOND_SWAP] ----> vCOND_CASES_TAC ++-->
   [vGEN_REWRITE_TAC vLAND_CONV [iterato] ---->
    vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vIN_DIFF]) ---->
    vREWRITE_TAC[vIN_SING] ----> vSTRIP_TAC;
    vONCE_REWRITE_TAC[vGSYM vITERATO_SUPPORT] ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ----> vASM vSET_TAC[]] ---->
  vMATCH_MP_TAC(vMESON[]
   (parse_term "q /\\ p /\\ x = z ==> (if p /\\ q then x else y) = z")) ---->
  vREPEAT vCONJ_TAC ++-->
   [vASM vSET_TAC[];
    vMATCH_MP_TAC vFINITE_SUBSET ---->
    vEXISTS_TAC (parse_term "i INSERT {j | j IN k /\\ (f:K->A) j IN dom DIFF {neut}}") ---->
    vASM_REWRITE_TAC[vFINITE_INSERT] ----> vASM vSET_TAC[];
    vALL_TAC] ---->
  vCOND_CASES_TAC ++-->
   [vFIRST_X_ASSUM(vK vALL_TAC -| check (is_exists -| concl));
    vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "i:K") -| vREWRITE_RULE[vNOT_EXISTS_THM]) ---->
    vASM vSET_TAC[]] ---->
  vSUBGOAL_THEN
   (parse_term "(@i'. i' IN i INSERT k /\\\n          (f:K->A) i' IN dom DIFF {neut} /\\\n          (!j. j <<= i' /\\ j IN i INSERT k /\\ f j IN dom DIFF {neut}\n               ==> j = i')) = i")
  vSUBST1_TAC ++-->
   [vALL_TAC;
    vCONV_TAC(vONCE_DEPTH_CONV let_CONV) ---->
    vASM_SIMP_TAC[vSET_RULE (parse_term "~(i IN k) ==> (i INSERT k) DELETE i = k")] ---->
    vREWRITE_TAC[vITERATO_SUPPORT]] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ----> vX_GEN_TAC (parse_term "j:K") ---->
  vREWRITE_TAC[] ----> vEQ_TAC ----> vSIMP_TAC[] ++--> [vALL_TAC; vASM vSET_TAC[]] ---->
  vASM_CASES_TAC (parse_term "j:K = i") ----> vASM_REWRITE_TAC[vIN_INSERT] ----> vASM vSET_TAC[]);;

let vITERATO_CLAUSES = try Cache.lookup_thm "ITERATO_CLAUSES" with _ ->  prove
 ((parse_term "!dom neut op (<<=) (f:K->A).\n        (iterato dom neut op (<<=) {} f = neut) /\\\n        (!i k. FINITE {i | i IN k /\\ f i IN dom DIFF {neut}} /\\\n               (!j. j IN k ==> i <<= j /\\ ~(j <<= i))\n               ==> iterato dom neut op (<<=) (i INSERT k) f =\n                   if f i IN dom ==> f i = neut \\/ i IN k\n                   then iterato dom neut op (<<=) k f\n                   else op (f i) (iterato dom neut op (<<=) k f))"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vITERATO_CLAUSES_GEN] ---->
  vMATCH_MP_TAC(vCONJUNCT2(vSPEC_ALL vITERATO_CLAUSES_GEN)) ---->
  vASM_MESON_TAC[]);;

let vITERATO_CLAUSES_EXISTS = try Cache.lookup_thm "ITERATO_CLAUSES_EXISTS" with _ ->  prove
 ((parse_term "!dom neut op (<<=) (f:K->A).\n        (iterato dom neut op (<<=) {} f = neut) /\\\n        (!k. FINITE {i | i IN k /\\ f i IN dom DIFF {neut}} /\\\n             ~({i | i IN k /\\ f i IN dom DIFF {neut}} = {})\n             ==> ?i. i IN k /\\ f i IN dom DIFF {neut} /\\\n                     iterato dom neut op (<<=) k f =\n                     op (f i) (iterato dom neut op (<<=) (k DELETE i) f))"),
  vREPEAT vGEN_TAC ----> vCONJ_TAC ++-->
   [vGEN_REWRITE_TAC vLAND_CONV [iterato] ---->
    vASM_REWRITE_TAC[vNOT_IN_EMPTY; vEMPTY_GSPEC];
    vREPEAT vGEN_TAC ----> vSTRIP_TAC] ---->
  vGEN_REWRITE_TAC (vBINDER_CONV -| vRAND_CONV -| vRAND_CONV -| vLAND_CONV)
   [iterato] ---->
  vASM_REWRITE_TAC[] ----> vLET_TAC ---->
  vGEN_REWRITE_TAC (vBINDER_CONV -| funpow 4 vRAND_CONV)
   [vGSYM vITERATO_SUPPORT] ---->
  vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vMESON[]
   (parse_term "t = i ==> (t = i ==> P i) ==> ?j. P j"))) ---->
  vREWRITE_TAC[] ----> vCOND_CASES_TAC ++--> [vDISCH_TAC; vASM vSET_TAC[]] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSELECT_RULE) ----> vASM_REWRITE_TAC[] ----> vSIMP_TAC[]);;

let vITERATO_EQ = try Cache.lookup_thm "ITERATO_EQ" with _ ->  prove
 ((parse_term "!dom neut op (<<=) k f (g:K->A).\n        (!i. i IN k ==> f i = g i)\n        ==> iterato dom neut op (<<=) k f = iterato dom neut op (<<=) k g"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vITERATO_EXPAND_CASES] ---->
  vASM_SIMP_TAC[vTAUT (parse_term "p /\\ q <=> ~(p ==> ~q)")] ---->
  vREWRITE_TAC[vNOT_IMP] ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
  vSUBGOAL_THEN
   (parse_term "!i. i IN {i | i IN k /\\ (g:K->A) i IN dom DIFF {neut}} ==> f i = g i")
  vMP_TAC ++--> [vASM vSET_TAC[]; vALL_TAC] ---->
  vUNDISCH_TAC (parse_term "FINITE {i | i IN k /\\ (g:K->A) i IN dom DIFF {neut}}") ---->
  vSPEC_TAC((parse_term "{i | i IN k /\\ (g:K->A) i IN dom DIFF {neut}}"),(parse_term "k:K->bool")) ---->
  vPOP_ASSUM_LIST(vK vALL_TAC) ----> vMATCH_MP_TAC(vMESON[]
   (parse_term "(!n k. FINITE k /\\ CARD k = n ==> P k) ==> (!k. FINITE k ==> P k)")) ---->
  vREWRITE_TAC[vIMP_IMP] ----> vMATCH_MP_TAC num_WF ---->
  vX_GEN_TAC (parse_term "n:num") ----> vDISCH_TAC ----> vX_GEN_TAC (parse_term "k:K->bool") ---->
  vSTRIP_TAC ----> vRULE_ASSUM_TAC(vREWRITE_RULE
   [vIMP_IMP; vRIGHT_IMP_FORALL_THM; vGSYM vCONJ_ASSOC]) ---->
  vASM_CASES_TAC (parse_term "k:K->bool = {}") ---->
  vASM_REWRITE_TAC[vITERATO_CLAUSES_EXISTS] ----> vONCE_REWRITE_TAC[iterato] ---->
    vSUBGOAL_THEN (parse_term "!s i. i IN k /\\ (f:K->A) i IN s <=> i IN k /\\ g i IN s")
  vASSUME_TAC ++--> [vASM_MESON_TAC[]; vASM_REWRITE_TAC[vCONJ_ASSOC]] ---->
  vASM_REWRITE_TAC[vGSYM vCONJ_ASSOC] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ----> vLET_TAC ---->
  vCONV_TAC(vTOP_DEPTH_CONV let_CONV) ---->
  vSUBGOAL_THEN (parse_term "(i:K) IN k") vASSUME_TAC ++-->
   [vEXPAND_TAC "i" ---->
    vRULE_ASSUM_TAC(vREWRITE_RULE[vGSYM vMEMBER_NOT_EMPTY; vIN_ELIM_THM]) ---->
    vFIRST_X_ASSUM(vMP_TAC -| vCONJUNCT2) ----> vMESON_TAC[];
    vALL_TAC] ---->
  vBINOP_TAC ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
  vASM_REWRITE_TAC[vSET_RULE
   (parse_term "{j | j IN s DELETE i /\\ P j} = {j | j IN s /\\ P j} DELETE i")] ---->
  vFIRST_X_ASSUM vMATCH_MP_TAC ---->
  vASM_SIMP_TAC[vFINITE_DELETE; vFINITE_RESTRICT; vIN_DELETE; vIN_ELIM_THM] ---->
  vREWRITE_TAC[vONCE_REWRITE_RULE[vCONJ_SYM] vUNWIND_THM1] ---->
  vFIRST_X_ASSUM(fun th -> vGEN_REWRITE_TAC vRAND_CONV [vSYM th]) ---->
  vMATCH_MP_TAC vCARD_PSUBSET ----> vASM vSET_TAC[]);;

let vITERATO_INDUCT = try Cache.lookup_thm "ITERATO_INDUCT" with _ ->  prove
 ((parse_term "!dom neut op (<<=) k (f:K->A) P.\n        P neut /\\\n        (!i x. i IN k /\\ f i IN dom /\\ ~(f i = neut) /\\ P x ==> P (op (f i) x))\n        ==> P(iterato dom neut op (<<=) k f)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vSET_RULE
   (parse_term "i IN k /\\ f i IN s /\\ ~(f i = z) /\\ Q <=>\n    i IN {j | j IN k /\\ f j IN s DIFF {z}} /\\ Q")] ---->
  vONCE_REWRITE_TAC[vITERATO_EXPAND_CASES] ---->
  vONCE_REWRITE_TAC[vCOND_RAND] ----> vSIMP_TAC[] ---->
  vREWRITE_TAC[vTAUT
   (parse_term "(a /\\ p ==> if q then r else T) <=> a ==> q ==> p ==> r")] ---->
  vSTRIP_TAC ---->
  vSPEC_TAC((parse_term "{i | i IN k /\\ (f:K->A) i IN dom DIFF {neut}}"),(parse_term "k:K->bool")) ---->
  vMATCH_MP_TAC(vMESON[]
   (parse_term "(!n k. FINITE k /\\ CARD k = n ==> P k) ==> (!k. FINITE k ==> P k)")) ---->
  vREWRITE_TAC[vIMP_IMP] ----> vMATCH_MP_TAC num_WF ---->
  vX_GEN_TAC (parse_term "n:num") ----> vDISCH_TAC ---->
  vX_GEN_TAC (parse_term "k:K->bool") ----> vSTRIP_TAC ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE
   [vIMP_IMP; vRIGHT_IMP_FORALL_THM; vGSYM vCONJ_ASSOC]) ---->
  vASM_CASES_TAC (parse_term "k:K->bool = {}") ---->
  vASM_REWRITE_TAC[vITERATO_CLAUSES_EXISTS] ---->
  vMP_TAC(vISPECL
   [(parse_term "dom:A->bool"); (parse_term "neut:A"); (parse_term "op:A->A->A"); (parse_term "(<<=):K->K->bool"); (parse_term "f:K->A")]
   vITERATO_CLAUSES_EXISTS) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "k:K->bool") -| vCONJUNCT2) ---->
  vASM_SIMP_TAC[vFINITE_RESTRICT] ----> vMATCH_MP_TAC(vTAUT
   (parse_term "(p ==> r) /\\ (q ==> r) ==> (~p ==> q) ==> r")) ---->
  vCONJ_TAC ++-->
   [vONCE_REWRITE_TAC[vGSYM vITERATO_SUPPORT] ----> vSIMP_TAC[] ---->
    vASM_REWRITE_TAC[vITERATO_CLAUSES_EXISTS];
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "i:K") vMP_TAC)] ---->
  vREWRITE_TAC[vIN_DIFF; vIN_SING] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM vSUBST1_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vASM_REWRITE_TAC[] ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
  vEXISTS_TAC (parse_term "n - 1") ---->
  vASM_SIMP_TAC[vCARD_DELETE; vFINITE_DELETE; vIN_DELETE] ---->
  vREWRITE_TAC[vARITH_RULE (parse_term "n - 1 < n <=> ~(n = 0)")] ---->
  vASM_MESON_TAC[vCARD_EQ_0]);;

let vITERATO_CLOSED = try Cache.lookup_thm "ITERATO_CLOSED" with _ ->  prove
 ((parse_term "!dom neut op (<<=) k (f:K->A) P.\n        P neut /\\\n        (!x y. P x /\\ P y ==> P(op x y)) /\\\n        (!i. i IN k /\\ f i IN dom /\\ ~(f i = neut) ==> P(f i))\n        ==> P(iterato dom neut op (<<=) k f)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vITERATO_INDUCT ----> vASM_SIMP_TAC[]);;

let vITERATO_ITERATE = try Cache.lookup_thm "ITERATO_ITERATE" with _ ->  prove
 ((parse_term "!(op:A->A->A) ((<<=):K->K->bool).\n        monoidal op ==> iterato (:A) (neutral op) op (<<=) = iterate op"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vFUN_EQ_THM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "k:K->bool"); (parse_term "f:K->A")] ---->
  vONCE_REWRITE_TAC[vITERATE_EXPAND_CASES; vITERATO_EXPAND_CASES] ---->
  vREWRITE_TAC[support; vIN_UNIV; vIN_DIFF; vIN_SING] ----> vMATCH_MP_TAC(vMESON[]
   (parse_term "(p ==> x = y) ==> (if p then x else z) = (if p then y else z)")) ---->
  vSPEC_TAC((parse_term "{i | i IN k /\\ ~((f:K->A) i = neutral op)}"),(parse_term "k:K->bool")) ---->
  vMATCH_MP_TAC(vMESON[]
   (parse_term "(!n k. FINITE k /\\ CARD k = n ==> P k) ==> (!k. FINITE k ==> P k)")) ---->
  vREWRITE_TAC[vIMP_IMP] ----> vMATCH_MP_TAC num_WF ---->
  vX_GEN_TAC (parse_term "n:num") ----> vDISCH_TAC ---->
  vX_GEN_TAC (parse_term "k:K->bool") ----> vSTRIP_TAC ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE
   [vIMP_IMP; vRIGHT_IMP_FORALL_THM; vGSYM vCONJ_ASSOC]) ---->
  vASM_CASES_TAC (parse_term "k:K->bool = {}") ---->
  vASM_SIMP_TAC[vITERATE_CLAUSES; vITERATO_CLAUSES_EXISTS] ---->
  vMP_TAC(vISPECL
   [(parse_term "(:A)"); (parse_term "neutral op:A"); (parse_term "op:A->A->A"); (parse_term "(<<=):K->K->bool"); (parse_term "f:K->A")]
   vITERATO_CLAUSES_EXISTS) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "k:K->bool") -| vCONJUNCT2) ---->
  vASM_SIMP_TAC[vFINITE_RESTRICT] ----> vMATCH_MP_TAC(vTAUT
   (parse_term "(p ==> r) /\\ (q ==> r) ==> (~p ==> q) ==> r")) ---->
  vCONJ_TAC ++-->
   [vONCE_REWRITE_TAC[vGSYM vITERATO_SUPPORT; vGSYM vITERATE_SUPPORT] ---->
    vREWRITE_TAC[support; vIN_UNIV; vIN_DIFF; vIN_SING] ---->
    vASM_SIMP_TAC[vITERATE_CLAUSES; vITERATO_CLAUSES_EXISTS];
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "i:K") vMP_TAC)] ---->
  vREWRITE_TAC[vIN_DIFF; vIN_SING] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM vSUBST1_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "n - 1"); (parse_term "k DELETE (i:K)")]) ---->
  vREWRITE_TAC[vARITH_RULE (parse_term "n - 1 < n <=> ~(n = 0)")] ---->
  vASM_SIMP_TAC[vFINITE_DELETE; vCARD_DELETE] ---->
  vANTS_TAC ++--> [vASM_MESON_TAC[vCARD_EQ_0]; vDISCH_THEN vSUBST1_TAC] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vISPECL [(parse_term "f:K->A"); (parse_term "i:K"); (parse_term "k DELETE (i:K)")] -|
    vCONJUNCT2 -| vMATCH_MP vITERATE_CLAUSES) ---->
  vASM_REWRITE_TAC[vFINITE_DELETE; vIN_DELETE] ---->
  vASM_SIMP_TAC[vSET_RULE (parse_term "i IN k ==> i INSERT (k DELETE i) = k")]);;

let vITERATO_CLAUSES_NUMSEG_LEFT = try Cache.lookup_thm "ITERATO_CLAUSES_NUMSEG_LEFT" with _ ->  prove
 ((parse_term "!dom neut op (f:num->A) m n.\n       iterato dom neut op (<=) (m..n) f =\n         if m <= n then\n           if f m IN dom ==> f m = neut\n           then iterato dom neut op (<=) (m+1..n) f\n           else op (f m) (iterato dom neut op (<=) (m+1..n) f)\n         else neut"),
  vREPEAT vGEN_TAC ----> vMP_TAC(vISPECL
     [(parse_term "dom:A->bool"); (parse_term "neut:A"); (parse_term "op:A->A->A");
      (parse_term "(<=):num->num->bool"); (parse_term "f:num->A")] vITERATO_CLAUSES_GEN) ---->
  vCOND_CASES_TAC ++-->
   [vDISCH_THEN(fun th -> vASM_SIMP_TAC[vGSYM vNUMSEG_LREC] ----> vMP_TAC th);
    vDISCH_THEN(vMP_TAC -| vCONJUNCT1) ---->
    vASM_MESON_TAC[vNUMSEG_EMPTY; vNOT_LE]] ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [(parse_term "m:num"); (parse_term "m+1..n")] -| vCONJUNCT2) ---->
  vANTS_TAC ++-->
   [vSIMP_TAC[vFINITE_RESTRICT; vFINITE_NUMSEG; vIN_NUMSEG] ----> vARITH_TAC;
    vREWRITE_TAC[vIN_NUMSEG; vARITH_RULE (parse_term "~(m + 1 <= m)")]]);;

(* ------------------------------------------------------------------------- *)
(* Four iterated operations where we just more or less express the basic     *)
(* definition and clausal form of the recursion, but don't develop any       *)
(* more lemmas; for products load "Library/products.ml" and for sums of      *)
(* intgers load "Library/isum.ml".                                           *)
(* ------------------------------------------------------------------------- *)

let nproduct = new_definition
  (parse_term "nproduct = iterate(( * ):num->num->num)");;

let vNEUTRAL_MUL = try Cache.lookup_thm "NEUTRAL_MUL" with _ ->  prove
 ((parse_term "neutral(( * ):num->num->num) = 1"),
  vREWRITE_TAC[neutral] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vMESON_TAC[vMULT_CLAUSES; vMULT_EQ_1]);;

let vMONOIDAL_MUL = try Cache.lookup_thm "MONOIDAL_MUL" with _ ->  prove
 ((parse_term "monoidal(( * ):num->num->num)"),
  vREWRITE_TAC[monoidal; vNEUTRAL_MUL] ----> vARITH_TAC);;

let vNPRODUCT_CLAUSES = try Cache.lookup_thm "NPRODUCT_CLAUSES" with _ ->  prove
 ((parse_term "(!f. nproduct {} f = 1) /\\\n   (!x f s. FINITE(s)\n            ==> (nproduct (x INSERT s) f =\n                 if x IN s then nproduct s f else f(x) * nproduct s f))"),
  vREWRITE_TAC[nproduct; vGSYM vNEUTRAL_MUL] ---->
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vMATCH_MP_TAC vITERATE_CLAUSES ----> vREWRITE_TAC[vMONOIDAL_MUL]);;

let iproduct = new_definition
  (parse_term "iproduct = iterate (( * ):int->int->int)");;

let vNEUTRAL_INT_MUL = try Cache.lookup_thm "NEUTRAL_INT_MUL" with _ ->  prove
 ((parse_term "neutral(( * ):int->int->int) = &1"),
  vREWRITE_TAC[neutral] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vMESON_TAC[vINT_MUL_LID; vINT_MUL_RID]);;

let vMONOIDAL_INT_MUL = try Cache.lookup_thm "MONOIDAL_INT_MUL" with _ ->  prove
 ((parse_term "monoidal(( * ):int->int->int)"),
  vREWRITE_TAC[monoidal; vNEUTRAL_INT_MUL] ----> vINT_ARITH_TAC);;

let vIPRODUCT_CLAUSES = try Cache.lookup_thm "IPRODUCT_CLAUSES" with _ ->  prove
 ((parse_term "(!f. iproduct {} f = &1) /\\\n   (!x f s. FINITE(s)\n            ==> (iproduct (x INSERT s) f =\n                 if x IN s then iproduct s f else f(x) * iproduct s f))"),
  vREWRITE_TAC[iproduct; vGSYM vNEUTRAL_INT_MUL] ---->
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vMATCH_MP_TAC vITERATE_CLAUSES ----> vREWRITE_TAC[vMONOIDAL_INT_MUL]);;

let product = new_definition
  (parse_term "product = iterate (( * ):real->real->real)");;

let vNEUTRAL_REAL_MUL = try Cache.lookup_thm "NEUTRAL_REAL_MUL" with _ ->  prove
 ((parse_term "neutral(( * ):real->real->real) = &1"),
  vREWRITE_TAC[neutral] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vMESON_TAC[vREAL_MUL_LID; vREAL_MUL_RID]);;

let vMONOIDAL_REAL_MUL = try Cache.lookup_thm "MONOIDAL_REAL_MUL" with _ ->  prove
 ((parse_term "monoidal(( * ):real->real->real)"),
  vREWRITE_TAC[monoidal; vNEUTRAL_REAL_MUL] ----> vREAL_ARITH_TAC);;

let vPRODUCT_CLAUSES = try Cache.lookup_thm "PRODUCT_CLAUSES" with _ ->  prove
 ((parse_term "(!f. product {} f = &1) /\\\n   (!x f s. FINITE(s)\n            ==> (product (x INSERT s) f =\n                 if x IN s then product s f else f(x) * product s f))"),
  vREWRITE_TAC[product; vGSYM vNEUTRAL_REAL_MUL] ---->
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vMATCH_MP_TAC vITERATE_CLAUSES ----> vREWRITE_TAC[vMONOIDAL_REAL_MUL]);;

let isum = new_definition
 (parse_term "isum = iterate((+):int->int->int)");;

let vNEUTRAL_INT_ADD = try Cache.lookup_thm "NEUTRAL_INT_ADD" with _ ->  prove
 ((parse_term "neutral((+):int->int->int) = &0"),
  vREWRITE_TAC[neutral] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vMESON_TAC[vINT_ADD_LID; vINT_ADD_RID]);;

let vMONOIDAL_INT_ADD = try Cache.lookup_thm "MONOIDAL_INT_ADD" with _ ->  prove
 ((parse_term "monoidal((+):int->int->int)"),
  vREWRITE_TAC[monoidal; vNEUTRAL_INT_ADD] ----> vINT_ARITH_TAC);;

let vISUM_CLAUSES = try Cache.lookup_thm "ISUM_CLAUSES" with _ ->  prove
 ((parse_term "(!f. isum {} f = &0) /\\\n   (!x f s. FINITE(s)\n            ==> (isum (x INSERT s) f =\n                 if x IN s then isum s f else f(x) + isum s f))"),
  vREWRITE_TAC[isum; vGSYM vNEUTRAL_INT_ADD] ---->
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vMATCH_MP_TAC vITERATE_CLAUSES ----> vREWRITE_TAC[vMONOIDAL_INT_ADD]);;

(* ------------------------------------------------------------------------- *)
(* Sums of natural numbers.                                                  *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;

let nsum = new_definition
  (parse_term "nsum = iterate (+)");;

let vNEUTRAL_ADD = try Cache.lookup_thm "NEUTRAL_ADD" with _ ->  prove
 ((parse_term "neutral((+):num->num->num) = 0"),
  vREWRITE_TAC[neutral] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vMESON_TAC[vADD_CLAUSES]);;

let vMONOIDAL_ADD = try Cache.lookup_thm "MONOIDAL_ADD" with _ ->  prove
 ((parse_term "monoidal((+):num->num->num)"),
  vREWRITE_TAC[monoidal; vNEUTRAL_ADD] ----> vARITH_TAC);;

let vNSUM_DEGENERATE = try Cache.lookup_thm "NSUM_DEGENERATE" with _ ->  prove
 ((parse_term "!f s. ~(FINITE {x | x IN s /\\ ~(f x = 0)}) ==> nsum s f = 0"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nsum] ---->
  vSIMP_TAC[iterate; support; vNEUTRAL_ADD]);;

let vNSUM_CLAUSES = try Cache.lookup_thm "NSUM_CLAUSES" with _ ->  prove
 ((parse_term "(!f. nsum {} f = 0) /\\\n   (!x f s. FINITE(s)\n            ==> (nsum (x INSERT s) f =\n                 if x IN s then nsum s f else f(x) + nsum s f))"),
  vREWRITE_TAC[nsum; vGSYM vNEUTRAL_ADD] ---->
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vMATCH_MP_TAC vITERATE_CLAUSES ----> vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_UNION = try Cache.lookup_thm "NSUM_UNION" with _ ->  prove
 ((parse_term "!f s t. FINITE s /\\ FINITE t /\\ DISJOINT s t\n           ==> (nsum (s UNION t) f = nsum s f + nsum t f)"),
  vSIMP_TAC[nsum; vITERATE_UNION; vMONOIDAL_ADD]);;

let vNSUM_DIFF = try Cache.lookup_thm "NSUM_DIFF" with _ ->  prove
 ((parse_term "!f s t. FINITE s /\\ t SUBSET s\n           ==> (nsum (s DIFF t) f = nsum s f - nsum t f)"),
  vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC(vARITH_RULE (parse_term "(x + z = y:num) ==> (x = y - z)")) ---->
  vASM_SIMP_TAC[nsum; vITERATE_DIFF; vMONOIDAL_ADD]);;

let vNSUM_INCL_EXCL = try Cache.lookup_thm "NSUM_INCL_EXCL" with _ ->  prove
 ((parse_term "!s t (f:A->num).\n     FINITE s /\\ FINITE t\n     ==> nsum s f + nsum t f = nsum (s UNION t) f + nsum (s INTER t) f"),
  vREWRITE_TAC[nsum; vGSYM vNEUTRAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_INCL_EXCL ----> vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_SUPPORT = try Cache.lookup_thm "NSUM_SUPPORT" with _ ->  prove
 ((parse_term "!f s. nsum (support (+) f s) f = nsum s f"),
  vSIMP_TAC[nsum; iterate; vSUPPORT_SUPPORT]);;

let vNSUM_ADD = try Cache.lookup_thm "NSUM_ADD" with _ ->  prove
 ((parse_term "!f g s. FINITE s ==> (nsum s (\\x. f(x) + g(x)) = nsum s f + nsum s g)"),
  vSIMP_TAC[nsum; vITERATE_OP; vMONOIDAL_ADD]);;

let vNSUM_ADD_GEN = try Cache.lookup_thm "NSUM_ADD_GEN" with _ ->  prove
 ((parse_term "!f g s.\n       FINITE {x | x IN s /\\ ~(f x = 0)} /\\ FINITE {x | x IN s /\\ ~(g x = 0)}\n       ==> nsum s (\\x. f x + g x) = nsum s f + nsum s g"),
  vREWRITE_TAC[vGSYM vNEUTRAL_ADD; vGSYM support; nsum] ---->
  vMATCH_MP_TAC vITERATE_OP_GEN ----> vACCEPT_TAC vMONOIDAL_ADD);;

let vNSUM_EQ_0 = try Cache.lookup_thm "NSUM_EQ_0" with _ ->  prove
 ((parse_term "!f s. (!x:A. x IN s ==> (f(x) = 0)) ==> (nsum s f = 0)"),
  vREWRITE_TAC[nsum; vGSYM vNEUTRAL_ADD] ---->
  vSIMP_TAC[vITERATE_EQ_NEUTRAL; vMONOIDAL_ADD]);;

let vNSUM_0 = try Cache.lookup_thm "NSUM_0" with _ ->  prove
 ((parse_term "!s:A->bool. nsum s (\\n. 0) = 0"),
  vSIMP_TAC[vNSUM_EQ_0]);;

let vNSUM_LMUL = try Cache.lookup_thm "NSUM_LMUL" with _ ->  prove
 ((parse_term "!f c s:A->bool. nsum s (\\x. c * f(x)) = c * nsum s f"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "c = 0") ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vNSUM_0] ----> vREWRITE_TAC[nsum] ---->
  vONCE_REWRITE_TAC[vITERATE_EXPAND_CASES] ---->
  vSUBGOAL_THEN (parse_term "support (+) (\\x:A. c * f(x)) s = support (+) f s") vSUBST1_TAC
  ++--> [vASM_SIMP_TAC[support; vMULT_EQ_0; vNEUTRAL_ADD]; vALL_TAC] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vNEUTRAL_ADD; vMULT_CLAUSES] ---->
  vUNDISCH_TAC (parse_term "FINITE (support (+) f (s:A->bool))") ---->
  vSPEC_TAC((parse_term "support (+) f (s:A->bool)"),(parse_term "t:A->bool")) ---->
  vREWRITE_TAC[vGSYM nsum] ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vNSUM_CLAUSES; vMULT_CLAUSES; vLEFT_ADD_DISTRIB]);;

let vNSUM_RMUL = try Cache.lookup_thm "NSUM_RMUL" with _ ->  prove
 ((parse_term "!f c s:A->bool. nsum s (\\x. f(x) * c) = nsum s f * c"),
  vONCE_REWRITE_TAC[vMULT_SYM] ----> vREWRITE_TAC[vNSUM_LMUL]);;

let vNSUM_LE = try Cache.lookup_thm "NSUM_LE" with _ ->  prove
 ((parse_term "!f g s. FINITE(s) /\\ (!x. x IN s ==> f(x) <= g(x))\n           ==> nsum s f <= nsum s g"),
  vONCE_REWRITE_TAC[vIMP_CONJ] ---->
  vGEN_TAC ----> vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vNSUM_CLAUSES; vLE_REFL; vLE_ADD2; vIN_INSERT]);;

let vNSUM_LT = try Cache.lookup_thm "NSUM_LT" with _ ->  prove
 ((parse_term "!f g s:A->bool.\n        FINITE(s) /\\ (!x. x IN s ==> f(x) <= g(x)) /\\\n        (?x. x IN s /\\ f(x) < g(x))\n         ==> nsum s f < nsum s g"),
  vREPEAT vGEN_TAC ---->
  vREPEAT(vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "a:A") vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN (parse_term "s = (a:A) INSERT (s DELETE a)") vSUBST1_TAC ++-->
   [vUNDISCH_TAC (parse_term "a:A IN s") ----> vSET_TAC[]; vALL_TAC] ---->
  vASM_SIMP_TAC[vNSUM_CLAUSES; vFINITE_DELETE; vIN_DELETE] ---->
  vASM_SIMP_TAC[vLTE_ADD2; vNSUM_LE; vIN_DELETE; vFINITE_DELETE]);;

let vNSUM_LT_ALL = try Cache.lookup_thm "NSUM_LT_ALL" with _ ->  prove
 ((parse_term "!f g s. FINITE s /\\ ~(s = {}) /\\ (!x. x IN s ==> f(x) < g(x))\n           ==> nsum s f < nsum s g"),
  vMESON_TAC[vMEMBER_NOT_EMPTY; vLT_IMP_LE; vNSUM_LT]);;

let vNSUM_EQ = try Cache.lookup_thm "NSUM_EQ" with _ ->  prove
 ((parse_term "!f g s. (!x. x IN s ==> (f x = g x)) ==> (nsum s f = nsum s g)"),
  vREWRITE_TAC[nsum] ---->
  vMATCH_MP_TAC vITERATE_EQ ----> vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_CONST = try Cache.lookup_thm "NSUM_CONST" with _ ->  prove
 ((parse_term "!c s. FINITE s ==> (nsum s (\\n. c) = (CARD s) * c)"),
  vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vNSUM_CLAUSES; vCARD_CLAUSES] ---->
  vREPEAT vSTRIP_TAC ----> vARITH_TAC);;

let vNSUM_POS_BOUND = try Cache.lookup_thm "NSUM_POS_BOUND" with _ ->  prove
 ((parse_term "!f b s. FINITE s /\\ nsum s f <= b ==> !x:A. x IN s ==> f x <= b"),
  vGEN_TAC ----> vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vNSUM_CLAUSES; vNOT_IN_EMPTY; vIN_INSERT] ---->
  vMESON_TAC[vLE_0; vARITH_RULE
   (parse_term "0 <= x /\\ 0 <= y /\\ x + y <= b ==> x <= b /\\ y <= b")]);;

let vNSUM_EQ_0_IFF = try Cache.lookup_thm "NSUM_EQ_0_IFF" with _ ->  prove
 ((parse_term "!s. FINITE s ==> (nsum s f = 0 <=> !x. x IN s ==> f x = 0)"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vASM_SIMP_TAC[vNSUM_EQ_0] ---->
  vASM_MESON_TAC[vARITH_RULE (parse_term "n = 0 <=> n <= 0"); vNSUM_POS_BOUND]);;

let vNSUM_POS_LT = try Cache.lookup_thm "NSUM_POS_LT" with _ ->  prove
 ((parse_term "!f s:A->bool.\n        FINITE s /\\ (?x. x IN s /\\ 0 < f x)\n        ==> 0 < nsum s f"),
  vSIMP_TAC[vARITH_RULE (parse_term "0 < n <=> ~(n = 0)"); vNSUM_EQ_0_IFF] ----> vMESON_TAC[]);;

let vNSUM_POS_LT_ALL = try Cache.lookup_thm "NSUM_POS_LT_ALL" with _ ->  prove
 ((parse_term "!s f:A->num.\n     FINITE s /\\ ~(s = {}) /\\ (!i. i IN s ==> 0 < f i) ==> 0 < nsum s f"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vNSUM_POS_LT ---->
  vASM_MESON_TAC[vMEMBER_NOT_EMPTY; vREAL_LT_IMP_LE]);;

let vNSUM_DELETE = try Cache.lookup_thm "NSUM_DELETE" with _ ->  prove
 ((parse_term "!f s a. FINITE s /\\ a IN s ==> f(a) + nsum(s DELETE a) f = nsum s f"),
  vSIMP_TAC[nsum; vITERATE_DELETE; vMONOIDAL_ADD]);;

let vNSUM_SING = try Cache.lookup_thm "NSUM_SING" with _ ->  prove
 ((parse_term "!f x. nsum {x} f = f(x)"),
  vSIMP_TAC[vNSUM_CLAUSES; vFINITE_RULES; vNOT_IN_EMPTY; vADD_CLAUSES]);;

let vNSUM_DELTA = try Cache.lookup_thm "NSUM_DELTA" with _ ->  prove
 ((parse_term "!s a. nsum s (\\x. if x = a:A then b else 0) = if a IN s then b else 0"),
  vREWRITE_TAC[nsum; vGSYM vNEUTRAL_ADD] ---->
  vSIMP_TAC[vITERATE_DELTA; vMONOIDAL_ADD]);;

let vNSUM_SWAP = try Cache.lookup_thm "NSUM_SWAP" with _ ->  prove
 ((parse_term "!f:A->B->num s t.\n      FINITE(s) /\\ FINITE(t)\n      ==> (nsum s (\\i. nsum t (f i)) = nsum t (\\j. nsum s (\\i. f i j)))"),
  vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vNSUM_CLAUSES; vNSUM_0; vNSUM_ADD; vETA_AX]);;

let vNSUM_IMAGE = try Cache.lookup_thm "NSUM_IMAGE" with _ ->  prove
 ((parse_term "!f g s. (!x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y))\n           ==> (nsum (IMAGE f s) g = nsum s (g o f))"),
  vREWRITE_TAC[nsum; vGSYM vNEUTRAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_IMAGE ----> vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_SUPERSET = try Cache.lookup_thm "NSUM_SUPERSET" with _ ->  prove
 ((parse_term "!f:A->num u v.\n        u SUBSET v /\\ (!x. x IN v /\\ ~(x IN u) ==> (f(x) = 0))\n        ==> (nsum v f = nsum u f)"),
  vSIMP_TAC[nsum; vGSYM vNEUTRAL_ADD; vITERATE_SUPERSET; vMONOIDAL_ADD]);;

let vNSUM_UNIV = try Cache.lookup_thm "NSUM_UNIV" with _ ->  prove
 ((parse_term "!f:A->num s. support (+) f (:A) SUBSET s ==> nsum s f = nsum (:A) f"),
  vREWRITE_TAC[nsum] ----> vMATCH_MP_TAC vITERATE_UNIV ---->
  vREWRITE_TAC[vMONOIDAL_ADD]);;

let vITERATE_UNIV = try Cache.lookup_thm "ITERATE_UNIV" with _ ->  prove
 ((parse_term "!op. monoidal op\n        ==> !f s. support op f UNIV SUBSET s\n                  ==> iterate op s f = iterate op UNIV f"),
  vREWRITE_TAC[support; vSUBSET; vIN_ELIM_THM] ---->
  vREPEAT vSTRIP_TAC ----> vCONV_TAC vSYM_CONV ---->
  vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vITERATE_SUPERSET) ---->
  vASM vSET_TAC[]);;

let vNSUM_UNION_RZERO = try Cache.lookup_thm "NSUM_UNION_RZERO" with _ ->  prove
 ((parse_term "!f:A->num u v.\n        FINITE u /\\ (!x. x IN v /\\ ~(x IN u) ==> (f(x) = 0))\n        ==> (nsum (u UNION v) f = nsum u f)"),
  let lemma = prove((parse_term "u UNION v = u UNION (v DIFF u)"),vSET_TAC[]) in
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[lemma] ---->
  vMATCH_MP_TAC vNSUM_SUPERSET ----> vASM_MESON_TAC[vIN_UNION; vIN_DIFF; vSUBSET]);;

let vNSUM_UNION_LZERO = try Cache.lookup_thm "NSUM_UNION_LZERO" with _ ->  prove
 ((parse_term "!f:A->num u v.\n        FINITE v /\\ (!x. x IN u /\\ ~(x IN v) ==> (f(x) = 0))\n        ==> (nsum (u UNION v) f = nsum v f)"),
  vMESON_TAC[vNSUM_UNION_RZERO; vUNION_COMM]);;

let vNSUM_RESTRICT = try Cache.lookup_thm "NSUM_RESTRICT" with _ ->  prove
 ((parse_term "!f s. FINITE s ==> (nsum s (\\x. if x IN s then f(x) else 0) = nsum s f)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vNSUM_EQ ----> vASM_SIMP_TAC[]);;

let vNSUM_BOUND = try Cache.lookup_thm "NSUM_BOUND" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ (!x:A. x IN s ==> f(x) <= b)\n           ==> nsum s f <= (CARD s) * b"),
  vSIMP_TAC[vGSYM vNSUM_CONST; vNSUM_LE]);;

let vNSUM_BOUND_GEN = try Cache.lookup_thm "NSUM_BOUND_GEN" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ ~(s = {}) /\\ (!x:A. x IN s ==> f(x) <= b DIV (CARD s))\n           ==> nsum s f <= b"),
  vSIMP_TAC[vIMP_CONJ; vCARD_EQ_0; vLE_RDIV_EQ] ----> vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "nsum s (\\x. CARD(s:A->bool) * f x) <= CARD s * b") vMP_TAC ++-->
   [vASM_SIMP_TAC[vNSUM_BOUND];
    vASM_SIMP_TAC[vNSUM_LMUL; vLE_MULT_LCANCEL; vCARD_EQ_0]]);;

let vNSUM_BOUND_LT = try Cache.lookup_thm "NSUM_BOUND_LT" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ (!x:A. x IN s ==> f x <= b) /\\ (?x. x IN s /\\ f x < b)\n           ==> nsum s f < (CARD s) * b"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vLTE_TRANS ---->
  vEXISTS_TAC (parse_term "nsum s (\\x:A. b)") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vNSUM_LT ----> vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[];
    vASM_SIMP_TAC[vNSUM_CONST; vLE_REFL]]);;

let vNSUM_BOUND_LT_ALL = try Cache.lookup_thm "NSUM_BOUND_LT_ALL" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ ~(s = {}) /\\ (!x. x IN s ==> f(x) < b)\n           ==> nsum s f <  (CARD s) * b"),
  vMESON_TAC[vMEMBER_NOT_EMPTY; vLT_IMP_LE; vNSUM_BOUND_LT]);;

let vNSUM_BOUND_LT_GEN = try Cache.lookup_thm "NSUM_BOUND_LT_GEN" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ ~(s = {}) /\\ (!x:A. x IN s ==> f(x) < b DIV (CARD s))\n           ==> nsum s f < b"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vLTE_TRANS ---->
  vEXISTS_TAC (parse_term "nsum (s:A->bool) (\\a. f(a) + 1)") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vNSUM_LT_ALL ----> vASM_SIMP_TAC[] ----> vARITH_TAC;
    vMATCH_MP_TAC vNSUM_BOUND_GEN ---->
    vASM_REWRITE_TAC[vARITH_RULE (parse_term "a + 1 <= b <=> a < b")]]);;

let vNSUM_UNION_EQ = try Cache.lookup_thm "NSUM_UNION_EQ" with _ ->  prove
 ((parse_term "!s t u. FINITE u /\\ (s INTER t = {}) /\\ (s UNION t = u)\n           ==> (nsum s f + nsum t f = nsum u f)"),
  vMESON_TAC[vNSUM_UNION; vDISJOINT; vFINITE_SUBSET; vSUBSET_UNION]);;

let vNSUM_EQ_SUPERSET = try Cache.lookup_thm "NSUM_EQ_SUPERSET" with _ ->  prove
 ((parse_term "!f s t:A->bool.\n        FINITE t /\\ t SUBSET s /\\\n        (!x. x IN t ==> (f x = g x)) /\\\n        (!x. x IN s /\\ ~(x IN t) ==> (f(x) = 0))\n        ==> (nsum s f = nsum t g)"),
  vMESON_TAC[vNSUM_SUPERSET; vNSUM_EQ]);;

let vNSUM_RESTRICT_SET = try Cache.lookup_thm "NSUM_RESTRICT_SET" with _ ->  prove
 ((parse_term "!P s f. nsum {x:A | x IN s /\\ P x} f = nsum s (\\x. if P x then f(x) else 0)"),
  vREWRITE_TAC[nsum; vGSYM vNEUTRAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_RESTRICT_SET ----> vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_NSUM_RESTRICT = try Cache.lookup_thm "NSUM_NSUM_RESTRICT" with _ ->  prove
 ((parse_term "!R f s t.\n        FINITE s /\\ FINITE t\n        ==> (nsum s (\\x. nsum {y | y IN t /\\ R x y} (\\y. f x y)) =\n             nsum t (\\y. nsum {x | x IN s /\\ R x y} (\\x. f x y)))"),
  vREPEAT vGEN_TAC ----> vSIMP_TAC[vNSUM_RESTRICT_SET] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vNSUM_SWAP th]));;

let vCARD_EQ_NSUM = try Cache.lookup_thm "CARD_EQ_NSUM" with _ ->  prove
 ((parse_term "!s. FINITE s ==> ((CARD s) = nsum s (\\x. 1))"),
  vSIMP_TAC[vNSUM_CONST; vMULT_CLAUSES]);;

let vNSUM_MULTICOUNT_GEN = try Cache.lookup_thm "NSUM_MULTICOUNT_GEN" with _ ->  prove
 ((parse_term "!R:A->B->bool s t k.\n        FINITE s /\\ FINITE t /\\\n        (!j. j IN t ==> (CARD {i | i IN s /\\ R i j} = k(j)))\n        ==> (nsum s (\\i. (CARD {j | j IN t /\\ R i j})) =\n             nsum t (\\i. (k i)))"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vCONJ_ASSOC] ---->
  vDISCH_THEN(vCONJUNCTS_THEN vASSUME_TAC) ---->
  vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "nsum s (\\i:A. nsum {j:B | j IN t /\\ R i j} (\\j. 1))") ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vNSUM_EQ ----> vASM_REWRITE_TAC[] ----> vREPEAT vSTRIP_TAC ---->
    vASM_SIMP_TAC[vCARD_EQ_NSUM; vFINITE_RESTRICT];
    vFIRST_ASSUM(fun t -> vONCE_REWRITE_TAC[vMATCH_MP vNSUM_NSUM_RESTRICT t]) ---->
    vMATCH_MP_TAC vNSUM_EQ ----> vASM_SIMP_TAC[vNSUM_CONST; vFINITE_RESTRICT] ---->
    vREWRITE_TAC[vMULT_CLAUSES]]);;

let vNSUM_MULTICOUNT = try Cache.lookup_thm "NSUM_MULTICOUNT" with _ ->  prove
 ((parse_term "!R:A->B->bool s t k.\n        FINITE s /\\ FINITE t /\\\n        (!j. j IN t ==> (CARD {i | i IN s /\\ R i j} = k))\n        ==> (nsum s (\\i. (CARD {j | j IN t /\\ R i j})) = (k * CARD t))"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "nsum t (\\i:B. k)") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vNSUM_MULTICOUNT_GEN ----> vASM_REWRITE_TAC[];
    vASM_SIMP_TAC[vNSUM_CONST] ----> vREWRITE_TAC[vMULT_AC]]);;

let vNSUM_IMAGE_GEN = try Cache.lookup_thm "NSUM_IMAGE_GEN" with _ ->  prove
 ((parse_term "!f:A->B g s.\n        FINITE s\n        ==> nsum s g =\n            nsum (IMAGE f s) (\\y. nsum {x | x IN s /\\ f x = y} g)"),
  vREWRITE_TAC[nsum] ----> vMATCH_MP_TAC vITERATE_IMAGE_GEN ---->
  vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_GROUP = try Cache.lookup_thm "NSUM_GROUP" with _ ->  prove
 ((parse_term "!f:A->B g s t.\n        FINITE s /\\ IMAGE f s SUBSET t\n        ==> nsum t (\\y. nsum {x | x IN s /\\ f(x) = y} g) = nsum s g"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "g:A->num"); (parse_term "s:A->bool")] vNSUM_IMAGE_GEN) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN vSUBST1_TAC ---->
  vMATCH_MP_TAC vNSUM_SUPERSET ----> vASM_REWRITE_TAC[] ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vNSUM_EQ_0 ----> vASM vSET_TAC[]);;

let vNSUM_GROUP_RELATION = try Cache.lookup_thm "NSUM_GROUP_RELATION" with _ ->  prove
 ((parse_term "!R:A->B->bool g s t.\n         FINITE s /\\\n         (!x. x IN s ==> ?!y. y IN t /\\ R x y)\n         ==> nsum t (\\y. nsum {x | x IN s /\\ R x y} g) = nsum s g"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "\\x:A. @y:B. y IN t /\\ R x y"); (parse_term "g:A->num");
                 (parse_term "s:A->bool"); (parse_term "t:B->bool")]
        vNSUM_GROUP) ---->
  vASM_REWRITE_TAC[vSUBSET; vFORALL_IN_IMAGE] ---->
  vANTS_TAC ++--> [vASM_MESON_TAC[]; vDISCH_THEN(vSUBST1_TAC -| vSYM)] ---->
  vMATCH_MP_TAC vNSUM_EQ ----> vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vASM vSET_TAC[]);;

let vNSUM_SUBSET = try Cache.lookup_thm "NSUM_SUBSET" with _ ->  prove
 ((parse_term "!u v f. FINITE u /\\ FINITE v /\\ (!x:A. x IN (u DIFF v) ==> f(x) = 0)\n           ==> nsum u f <= nsum v f"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->num"); (parse_term "u INTER v :A->bool")] vNSUM_UNION) ---->
  vDISCH_THEN(fun th -> vMP_TAC(vSPEC (parse_term "v DIFF u :A->bool") th) ---->
                       vMP_TAC(vSPEC (parse_term "u DIFF v :A->bool") th)) ---->
  vREWRITE_TAC[vSET_RULE (parse_term "(u INTER v) UNION (u DIFF v) = u");
              vSET_RULE (parse_term "(u INTER v) UNION (v DIFF u) = v")] ---->
  vASM_SIMP_TAC[vFINITE_DIFF; vFINITE_INTER] ---->
  vREPEAT(vANTS_TAC ++--> [vSET_TAC[]; vDISCH_THEN vSUBST1_TAC]) ---->
  vASM_SIMP_TAC[vNSUM_EQ_0] ----> vARITH_TAC);;

let vNSUM_SUBSET_SIMPLE = try Cache.lookup_thm "NSUM_SUBSET_SIMPLE" with _ ->  prove
 ((parse_term "!u v f. FINITE v /\\ u SUBSET v ==> nsum u f <= nsum v f"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vNSUM_SUBSET ---->
  vASM_MESON_TAC[vIN_DIFF; vSUBSET; vFINITE_SUBSET]);;

let vNSUM_LE_GEN = try Cache.lookup_thm "NSUM_LE_GEN" with _ ->  prove
 ((parse_term "!f g s. (!x:A. x IN s ==> f x <= g x) /\\ FINITE {x | x IN s /\\ ~(g x = 0)}\n           ==> nsum s f <= nsum s g"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vNSUM_SUPPORT] ---->
  vREWRITE_TAC[support; vNEUTRAL_ADD] ---->
  vTRANS_TAC vLE_TRANS (parse_term "nsum {x | x IN s /\\ ~(g(x:A) = 0)} f") ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vNSUM_SUBSET ---->
    vASM_REWRITE_TAC[vIN_ELIM_THM; vIN_DIFF] ---->
    vCONJ_TAC ++--> [vALL_TAC; vASM_MESON_TAC[vLE]] ---->
    vFIRST_X_ASSUM(vMATCH_MP_TAC -| vMATCH_MP (vREWRITE_RULE[vIMP_CONJ]
      vFINITE_SUBSET)) ---->
    vREWRITE_TAC[vSUBSET; vIN_ELIM_THM] ----> vASM_MESON_TAC[vLE];
    vMATCH_MP_TAC vNSUM_LE ----> vASM_SIMP_TAC[vIN_ELIM_THM]]);;

let vNSUM_MUL_BOUND = try Cache.lookup_thm "NSUM_MUL_BOUND" with _ ->  prove
 ((parse_term "!a b s:A->bool.\n        FINITE s\n        ==> nsum s (\\i. a i * b i) <= nsum s a * nsum s b"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vNSUM_LMUL] ---->
  vMATCH_MP_TAC vNSUM_LE ----> vASM_REWRITE_TAC[vLE_MULT_RCANCEL] ---->
  vX_GEN_TAC (parse_term "i:A") ----> vDISCH_TAC ----> vDISJ1_TAC ---->
  vASM_SIMP_TAC[] ----> vGEN_REWRITE_TAC vLAND_CONV [vGSYM vNSUM_SING] ---->
  vMATCH_MP_TAC vNSUM_SUBSET_SIMPLE ---->
  vASM_SIMP_TAC[vSING_SUBSET; vIN_DIFF]);;

let vNSUM_IMAGE_NONZERO = try Cache.lookup_thm "NSUM_IMAGE_NONZERO" with _ ->  prove
 ((parse_term "!d:B->num i:A->B s.\n    FINITE s /\\\n    (!x y. x IN s /\\ y IN s /\\ ~(x = y) /\\ i x = i y ==> d(i x) = 0)\n    ==> nsum (IMAGE i s) d = nsum s (d o i)"),
  vREWRITE_TAC[vGSYM vNEUTRAL_ADD; nsum] ---->
  vMATCH_MP_TAC vITERATE_IMAGE_NONZERO ----> vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_BIJECTION = try Cache.lookup_thm "NSUM_BIJECTION" with _ ->  prove
 ((parse_term "!f p s:A->bool.\n                (!x. x IN s ==> p(x) IN s) /\\\n                (!y. y IN s ==> ?!x. x IN s /\\ p(x) = y)\n                ==> nsum s f = nsum s (f o p)"),
  vREWRITE_TAC[nsum] ----> vMATCH_MP_TAC vITERATE_BIJECTION ---->
  vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_NSUM_PRODUCT = try Cache.lookup_thm "NSUM_NSUM_PRODUCT" with _ ->  prove
 ((parse_term "!s:A->bool t:A->B->bool x.\n        FINITE s /\\ (!i. i IN s ==> FINITE(t i))\n        ==> nsum s (\\i. nsum (t i) (x i)) =\n            nsum {i,j | i IN s /\\ j IN t i} (\\(i,j). x i j)"),
  vREWRITE_TAC[nsum] ----> vMATCH_MP_TAC vITERATE_ITERATE_PRODUCT ---->
  vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_EQ_GENERAL = try Cache.lookup_thm "NSUM_EQ_GENERAL" with _ ->  prove
 ((parse_term "!s:A->bool t:B->bool f g h.\n        (!y. y IN t ==> ?!x. x IN s /\\ h(x) = y) /\\\n        (!x. x IN s ==> h(x) IN t /\\ g(h x) = f x)\n        ==> nsum s f = nsum t g"),
  vREWRITE_TAC[nsum] ----> vMATCH_MP_TAC vITERATE_EQ_GENERAL ---->
  vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_EQ_GENERAL_INVERSES = try Cache.lookup_thm "NSUM_EQ_GENERAL_INVERSES" with _ ->  prove
 ((parse_term "!s:A->bool t:B->bool f g h k.\n        (!y. y IN t ==> k(y) IN s /\\ h(k y) = y) /\\\n        (!x. x IN s ==> h(x) IN t /\\ k(h x) = x /\\ g(h x) = f x)\n        ==> nsum s f = nsum t g"),
  vREWRITE_TAC[nsum] ----> vMATCH_MP_TAC vITERATE_EQ_GENERAL_INVERSES ---->
  vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_INJECTION = try Cache.lookup_thm "NSUM_INJECTION" with _ ->  prove
 ((parse_term "!f p s. FINITE s /\\\n           (!x. x IN s ==> p x IN s) /\\\n           (!x y. x IN s /\\ y IN s /\\ p x = p y ==> x = y)\n           ==> nsum s (f o p) = nsum s f"),
  vREWRITE_TAC[nsum] ----> vMATCH_MP_TAC vITERATE_INJECTION ---->
  vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_UNION_NONZERO = try Cache.lookup_thm "NSUM_UNION_NONZERO" with _ ->  prove
 ((parse_term "!f s t. FINITE s /\\ FINITE t /\\ (!x. x IN s INTER t ==> f(x) = 0)\n           ==> nsum (s UNION t) f = nsum s f + nsum t f"),
  vREWRITE_TAC[nsum; vGSYM vNEUTRAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_UNION_NONZERO ----> vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_UNIONS_NONZERO = try Cache.lookup_thm "NSUM_UNIONS_NONZERO" with _ ->  prove
 ((parse_term "!f s. FINITE s /\\ (!t:A->bool. t IN s ==> FINITE t) /\\\n         (!t1 t2 x. t1 IN s /\\ t2 IN s /\\ ~(t1 = t2) /\\ x IN t1 /\\ x IN t2\n                    ==> f x = 0)\n         ==> nsum (UNIONS s) f = nsum s (\\t. nsum t f)"),
  vGEN_TAC ----> vONCE_REWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vUNIONS_0; vUNIONS_INSERT; vNSUM_CLAUSES; vIN_INSERT] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "t:A->bool"); (parse_term "s:(A->bool)->bool")] ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ---->
  vONCE_REWRITE_TAC[vIMP_CONJ] ----> vASM_SIMP_TAC[vNSUM_CLAUSES] ---->
  vANTS_TAC ++-->  [vASM_MESON_TAC[]; vDISCH_THEN(vSUBST_ALL_TAC -| vSYM)] ---->
  vSTRIP_TAC ----> vMATCH_MP_TAC vNSUM_UNION_NONZERO ---->
  vASM_SIMP_TAC[vFINITE_UNIONS; vIN_INTER; vIN_UNIONS] ----> vASM_MESON_TAC[]);;

let vNSUM_CASES = try Cache.lookup_thm "NSUM_CASES" with _ ->  prove
 ((parse_term "!s P f g. FINITE s\n             ==> nsum s (\\x:A. if P x then f x else g x) =\n                 nsum {x | x IN s /\\ P x} f + nsum {x | x IN s /\\ ~P x} g"),
  vREWRITE_TAC[nsum; vGSYM vNEUTRAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_CASES ----> vREWRITE_TAC[vMONOIDAL_ADD]);;

let vNSUM_CLOSED = try Cache.lookup_thm "NSUM_CLOSED" with _ ->  prove
 ((parse_term "!P f:A->num s.\n        P(0) /\\ (!x y. P x /\\ P y ==> P(x + y)) /\\ (!a. a IN s ==> P(f a))\n        ==> P(nsum s f)"),
  vREPEAT vSTRIP_TAC ----> vMP_TAC(vMATCH_MP vITERATE_CLOSED vMONOIDAL_ADD) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "P:num->bool")) ---->
  vASM_SIMP_TAC[vNEUTRAL_ADD; vGSYM nsum]);;

let vNSUM_RELATED = try Cache.lookup_thm "NSUM_RELATED" with _ ->  prove
 ((parse_term "!R (f:A->num) g s.\n        R 0 0 /\\\n        (!m n m' n'. R m n /\\ R m' n' ==> R (m + m') (n + n')) /\\\n        FINITE s /\\ (!x. x IN s ==> R (f x) (g x))\n        ==> R (nsum s f) (nsum s g)"),
  vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vGEN_TAC ----> vREPEAT vDISCH_TAC ---->
  vMP_TAC(vISPEC (parse_term "R:num->num->bool")
    (vMATCH_MP vITERATE_RELATED vMONOIDAL_ADD)) ---->
  vASM_REWRITE_TAC[vGSYM nsum; vNEUTRAL_ADD] ----> vASM_MESON_TAC[]);;

let vNSUM_CLOSED_NONEMPTY = try Cache.lookup_thm "NSUM_CLOSED_NONEMPTY" with _ ->  prove
 ((parse_term "!P f:A->num s.\n        FINITE s /\\ ~(s = {}) /\\\n        (!x y. P x /\\ P y ==> P(x + y)) /\\ (!a. a IN s ==> P(f a))\n        ==> P(nsum s f)"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vMATCH_MP vITERATE_CLOSED_NONEMPTY vMONOIDAL_ADD) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "P:num->bool")) ---->
  vASM_SIMP_TAC[vNEUTRAL_ADD; vGSYM nsum]);;

let vNSUM_RELATED_NONEMPTY = try Cache.lookup_thm "NSUM_RELATED_NONEMPTY" with _ ->  prove
 ((parse_term "!R (f:A->num) g s.\n        (!m n m' n'. R m n /\\ R m' n' ==> R (m + m') (n + n')) /\\\n        FINITE s /\\ ~(s = {}) /\\ (!x. x IN s ==> R (f x) (g x))\n        ==> R (nsum s f) (nsum s g)"),
  vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vGEN_TAC ----> vREPEAT vDISCH_TAC ---->
  vMP_TAC(vISPEC (parse_term "R:num->num->bool")
    (vMATCH_MP vITERATE_RELATED_NONEMPTY vMONOIDAL_ADD)) ---->
  vASM_REWRITE_TAC[vGSYM nsum; vNEUTRAL_ADD] ----> vASM_MESON_TAC[]);;

let vNSUM_ADD_NUMSEG = try Cache.lookup_thm "NSUM_ADD_NUMSEG" with _ ->  prove
 ((parse_term "!f g m n. nsum(m..n) (\\i. f(i) + g(i)) = nsum(m..n) f + nsum(m..n) g"),
  vSIMP_TAC[vNSUM_ADD; vFINITE_NUMSEG]);;

let vNSUM_LE_NUMSEG = try Cache.lookup_thm "NSUM_LE_NUMSEG" with _ ->  prove
 ((parse_term "!f g m n. (!i. m <= i /\\ i <= n ==> f(i) <= g(i))\n             ==> nsum(m..n) f <= nsum(m..n) g"),
  vSIMP_TAC[vNSUM_LE; vFINITE_NUMSEG; vIN_NUMSEG]);;

let vNSUM_EQ_NUMSEG = try Cache.lookup_thm "NSUM_EQ_NUMSEG" with _ ->  prove
 ((parse_term "!f g m n. (!i. m <= i /\\ i <= n ==> (f(i) = g(i)))\n             ==> (nsum(m..n) f = nsum(m..n) g)"),
  vMESON_TAC[vNSUM_EQ; vFINITE_NUMSEG; vIN_NUMSEG]);;

let vNSUM_CONST_NUMSEG = try Cache.lookup_thm "NSUM_CONST_NUMSEG" with _ ->  prove
 ((parse_term "!c m n. nsum(m..n) (\\n. c) = ((n + 1) - m) * c"),
  vSIMP_TAC[vNSUM_CONST; vFINITE_NUMSEG; vCARD_NUMSEG]);;

let vNSUM_EQ_0_NUMSEG = try Cache.lookup_thm "NSUM_EQ_0_NUMSEG" with _ ->  prove
 ((parse_term "!f m n. (!i. m <= i /\\ i <= n ==> (f(i) = 0)) ==> (nsum(m..n) f = 0)"),
  vSIMP_TAC[vNSUM_EQ_0; vIN_NUMSEG]);;

let vNSUM_EQ_0_IFF_NUMSEG = try Cache.lookup_thm "NSUM_EQ_0_IFF_NUMSEG" with _ ->  prove
 ((parse_term "!f m n. nsum (m..n) f = 0 <=> !i. m <= i /\\ i <= n ==> f i = 0"),
  vSIMP_TAC[vNSUM_EQ_0_IFF; vFINITE_NUMSEG; vIN_NUMSEG]);;

let vNSUM_TRIV_NUMSEG = try Cache.lookup_thm "NSUM_TRIV_NUMSEG" with _ ->  prove
 ((parse_term "!f m n. n < m ==> (nsum(m..n) f = 0)"),
  vMESON_TAC[vNSUM_EQ_0_NUMSEG; vLE_TRANS; vNOT_LT]);;

let vNSUM_SING_NUMSEG = try Cache.lookup_thm "NSUM_SING_NUMSEG" with _ ->  prove
 ((parse_term "!f n. nsum(n..n) f = f(n)"),
  vSIMP_TAC[vNSUM_SING; vNUMSEG_SING]);;

let vNSUM_CLAUSES_NUMSEG = try Cache.lookup_thm "NSUM_CLAUSES_NUMSEG" with _ ->  prove
 ((parse_term "(!m. nsum(m..0) f = if m = 0 then f(0) else 0) /\\\n   (!m n. nsum(m..SUC n) f = if m <= SUC n then nsum(m..n) f + f(SUC n)\n                             else nsum(m..n) f)"),
  vMP_TAC(vMATCH_MP vITERATE_CLAUSES_NUMSEG vMONOIDAL_ADD) ---->
  vREWRITE_TAC[vNEUTRAL_ADD; nsum]);;

let vNSUM_CLAUSES_NUMSEG_LT = try Cache.lookup_thm "NSUM_CLAUSES_NUMSEG_LT" with _ ->  prove
 ((parse_term "nsum {i | i < 0} f = 0 /\\\n   (!k. nsum {i | i < SUC k} f = nsum {i | i < k} f + f k)"),
  vMP_TAC(vMATCH_MP vITERATE_CLAUSES_NUMSEG_LT vMONOIDAL_ADD) ---->
  vREWRITE_TAC[vNEUTRAL_ADD; nsum]);;

let vNSUM_CLAUSES_NUMSEG_LE = try Cache.lookup_thm "NSUM_CLAUSES_NUMSEG_LE" with _ ->  prove
 ((parse_term "nsum {i | i <= 0} f = f 0 /\\\n   (!k. nsum {i | i <= SUC k} f = nsum {i | i <= k} f + f(SUC k))"),
  vMP_TAC(vMATCH_MP vITERATE_CLAUSES_NUMSEG_LE vMONOIDAL_ADD) ---->
  vREWRITE_TAC[vNEUTRAL_ADD; nsum]);;

let vNSUM_SWAP_NUMSEG = try Cache.lookup_thm "NSUM_SWAP_NUMSEG" with _ ->  prove
 ((parse_term "!a b c d f.\n     nsum(a..b) (\\i. nsum(c..d) (f i)) =\n     nsum(c..d) (\\j. nsum(a..b) (\\i. f i j))"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vNSUM_SWAP ----> vREWRITE_TAC[vFINITE_NUMSEG]);;

let vNSUM_ADD_SPLIT = try Cache.lookup_thm "NSUM_ADD_SPLIT" with _ ->  prove
 ((parse_term "!f m n p.\n        m <= n + 1 ==> (nsum (m..(n+p)) f = nsum(m..n) f + nsum(n+1..n+p) f)"),
  vSIMP_TAC[vNUMSEG_ADD_SPLIT; vNSUM_UNION; vDISJOINT_NUMSEG; vFINITE_NUMSEG;
           vARITH_RULE (parse_term "x < x + 1")]);;

let vNSUM_OFFSET = try Cache.lookup_thm "NSUM_OFFSET" with _ ->  prove
 ((parse_term "!p f m n. nsum(m+p..n+p) f = nsum(m..n) (\\i. f(i + p))"),
  vSIMP_TAC[vNUMSEG_OFFSET_IMAGE; vNSUM_IMAGE; vEQ_ADD_RCANCEL; vFINITE_NUMSEG] ---->
  vREWRITE_TAC[o_DEF]);;

let vNSUM_OFFSET_0 = try Cache.lookup_thm "NSUM_OFFSET_0" with _ ->  prove
 ((parse_term "!f m n. m <= n ==> (nsum(m..n) f = nsum(0..n-m) (\\i. f(i + m)))"),
  vSIMP_TAC[vGSYM vNSUM_OFFSET; vADD_CLAUSES; vSUB_ADD]);;

let vNSUM_CLAUSES_LEFT = try Cache.lookup_thm "NSUM_CLAUSES_LEFT" with _ ->  prove
 ((parse_term "!f m n. m <= n ==> nsum(m..n) f = f(m) + nsum(m+1..n) f"),
  vSIMP_TAC[vGSYM vNUMSEG_LREC; vNSUM_CLAUSES; vFINITE_NUMSEG; vIN_NUMSEG] ---->
  vARITH_TAC);;

let vNSUM_CLAUSES_RIGHT = try Cache.lookup_thm "NSUM_CLAUSES_RIGHT" with _ ->  prove
 ((parse_term "!f m n. 0 < n /\\ m <= n ==> nsum(m..n) f = nsum(m..n-1) f + f(n)"),
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vSIMP_TAC[vLT_REFL; vNSUM_CLAUSES_NUMSEG; vSUC_SUB1]);;

let vNSUM_PAIR = try Cache.lookup_thm "NSUM_PAIR" with _ ->  prove
 ((parse_term "!f m n. nsum(2*m..2*n+1) f = nsum(m..n) (\\i. f(2*i) + f(2*i+1))"),
  vMP_TAC(vMATCH_MP vITERATE_PAIR vMONOIDAL_ADD) ---->
  vREWRITE_TAC[nsum; vNEUTRAL_ADD]);;

let vNSUM_REFLECT = try Cache.lookup_thm "NSUM_REFLECT" with _ ->  prove
 ((parse_term "!x m n. nsum(m..n) x = if n < m then 0 else nsum(0..n-m) (\\i. x(n - i))"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[nsum] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vMATCH_MP vITERATE_REFLECT vMONOIDAL_ADD] ---->
  vREWRITE_TAC[vNEUTRAL_ADD]);;

let vMOD_NSUM_MOD = try Cache.lookup_thm "MOD_NSUM_MOD" with _ ->  prove
 ((parse_term "!f:A->num n s.\n        FINITE s ==> (nsum s f) MOD n = nsum s (\\i. f(i) MOD n) MOD n"),
  vGEN_TAC ----> vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vMOD_ZERO; vETA_AX] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ----> vSIMP_TAC[vNSUM_CLAUSES] ---->
  vREPEAT vSTRIP_TAC ----> vGEN_REWRITE_TAC vLAND_CONV [vGSYM vMOD_ADD_MOD] ---->
  vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vGSYM vMOD_ADD_MOD] ---->
  vREWRITE_TAC[vMOD_MOD_REFL]);;

let vMOD_NSUM_MOD_NUMSEG = try Cache.lookup_thm "MOD_NSUM_MOD_NUMSEG" with _ ->  prove
 ((parse_term "!f a b n.\n        (nsum(a..b) f) MOD n = nsum(a..b) (\\i. f i MOD n) MOD n"),
  vMESON_TAC[vMOD_NSUM_MOD; vFINITE_NUMSEG]);;

let vCONG_NSUM = try Cache.lookup_thm "CONG_NSUM" with _ ->  prove
 ((parse_term "!n (f:A->num) g s.\n        FINITE s /\\ (!x. x IN s ==> (f x == g x) (mod n))\n        ==> (nsum s f == nsum s g) (mod n)"),
  vREPEAT vSTRIP_TAC ----> vMP_TAC(vISPECL
   [(parse_term "\\x y:num. (x == y) (mod n)"); (parse_term "f:A->num"); (parse_term "g:A->num"); (parse_term "s:A->bool")]
        vNSUM_RELATED) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN vMATCH_MP_TAC ---->
  vCONV_TAC vNUMBER_RULE);;

let th = prove
 ((parse_term "(!f g s.   (!x. x IN s ==> f(x) = g(x))\n              ==> nsum s (\\i. f(i)) = nsum s g) /\\\n   (!f g a b. (!i. a <= i /\\ i <= b ==> f(i) = g(i))\n              ==> nsum(a..b) (\\i. f(i)) = nsum(a..b) g) /\\\n   (!f g p.   (!x. p x ==> f x = g x)\n              ==> nsum {y | p y} (\\i. f(i)) = nsum {y | p y} g)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vNSUM_EQ ---->
  vASM_SIMP_TAC[vIN_ELIM_THM; vIN_NUMSEG]) in
  extend_basic_congs (map vSPEC_ALL (vCONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* Thanks to finite sums, we can express cardinality of finite union.        *)
(* ------------------------------------------------------------------------- *)

let vCARD_UNIONS = try Cache.lookup_thm "CARD_UNIONS" with _ ->  prove
 ((parse_term "!s:(A->bool)->bool.\n        FINITE s /\\ (!t. t IN s ==> FINITE t) /\\\n        (!t u. t IN s /\\ u IN s /\\ ~(t = u) ==> t INTER u = {})\n        ==> CARD(UNIONS s) = nsum s CARD"),
  vONCE_REWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vUNIONS_0; vUNIONS_INSERT; vNOT_IN_EMPTY; vIN_INSERT] ---->
  vREWRITE_TAC[vCARD_CLAUSES; vNSUM_CLAUSES] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "t:A->bool"); (parse_term "f:(A->bool)->bool")] ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ---->
  vASM_SIMP_TAC[vNSUM_CLAUSES] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vSUBST1_TAC -| vSYM) vSTRIP_ASSUME_TAC) ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vCARD_UNION_EQ ---->
  vASM_SIMP_TAC[vFINITE_UNIONS; vFINITE_UNION; vINTER_UNIONS] ---->
  vREWRITE_TAC[vEMPTY_UNIONS; vIN_ELIM_THM] ----> vASM vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Expand "nsum (m..n) f" where m and n are numerals.                        *)
(* ------------------------------------------------------------------------- *)

let vEXPAND_NSUM_CONV =
  let [@warning "-8"] [pth_0; pth_1; pth_2] = (vCONJUNCTS -| prove)
   ((parse_term "(n < m ==> nsum(m..n) f = 0) /\\\n     nsum(m..m) f = f m /\\\n     (m <= n ==> nsum (m..n) f = f m + nsum (m + 1..n) f)"),
    vREWRITE_TAC[vNSUM_CLAUSES_LEFT; vNSUM_SING_NUMSEG; vNSUM_TRIV_NUMSEG])
  and ns_tm = (parse_term "..") and f_tm = (parse_term "f:num->num")
  and m_tm = (parse_term "m:num") and n_tm = (parse_term "n:num") in
  let rec conv tm =
    let smn,ftm = dest_comb tm in
    let s,mn = dest_comb smn in
    if not(is_const s && fst(dest_const s) = "nsum")
    then failwith "EXPAND_NSUM_CONV" else
    let mtm,ntm = dest_binop ns_tm mn in
    let m = dest_numeral mtm and n = dest_numeral ntm in
    if n < m then
      let th1 = vINST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_0 in
      vMP th1 (vEQT_ELIM(vNUM_LT_CONV(lhand(concl th1))))
    else if n = m then vCONV_RULE (vRAND_CONV(vTRY_CONV vBETA_CONV))
                                 (vINST [ftm,f_tm; mtm,m_tm] pth_1)
    else
      let th1 = vINST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_2 in
      let th2 = vMP th1 (vEQT_ELIM(vNUM_LE_CONV(lhand(concl th1)))) in
      vCONV_RULE (vRAND_CONV(vCOMB2_CONV (vRAND_CONV(vTRY_CONV vBETA_CONV))
       (vLAND_CONV(vLAND_CONV vNUM_ADD_CONV) +---> conv))) th2 in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Sums of real numbers.                                                     *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let sum = new_definition
  (parse_term "sum = iterate (+)");;

let vNEUTRAL_REAL_ADD = try Cache.lookup_thm "NEUTRAL_REAL_ADD" with _ ->  prove
 ((parse_term "neutral((+):real->real->real) = &0"),
  vREWRITE_TAC[neutral] ----> vMATCH_MP_TAC vSELECT_UNIQUE ---->
  vMESON_TAC[vREAL_ADD_LID; vREAL_ADD_RID]);;

let vMONOIDAL_REAL_ADD = try Cache.lookup_thm "MONOIDAL_REAL_ADD" with _ ->  prove
 ((parse_term "monoidal((+):real->real->real)"),
  vREWRITE_TAC[monoidal; vNEUTRAL_REAL_ADD] ----> vREAL_ARITH_TAC);;

let vSUM_DEGENERATE = try Cache.lookup_thm "SUM_DEGENERATE" with _ ->  prove
 ((parse_term "!f s. ~(FINITE {x | x IN s /\\ ~(f x = &0)}) ==> sum s f = &0"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[sum] ---->
  vSIMP_TAC[iterate; support; vNEUTRAL_REAL_ADD]);;

let vSUM_CLAUSES = try Cache.lookup_thm "SUM_CLAUSES" with _ ->  prove
 ((parse_term "(!f. sum {} f = &0) /\\\n   (!x f s. FINITE(s)\n            ==> (sum (x INSERT s) f =\n                 if x IN s then sum s f else f(x) + sum s f))"),
  vREWRITE_TAC[sum; vGSYM vNEUTRAL_REAL_ADD] ---->
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vMATCH_MP_TAC vITERATE_CLAUSES ----> vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_UNION = try Cache.lookup_thm "SUM_UNION" with _ ->  prove
 ((parse_term "!f s t. FINITE s /\\ FINITE t /\\ DISJOINT s t\n           ==> (sum (s UNION t) f = sum s f + sum t f)"),
  vSIMP_TAC[sum; vITERATE_UNION; vMONOIDAL_REAL_ADD]);;

let vSUM_DIFF = try Cache.lookup_thm "SUM_DIFF" with _ ->  prove
 ((parse_term "!f s t. FINITE s /\\ t SUBSET s ==> (sum (s DIFF t) f = sum s f - sum t f)"),
  vSIMP_TAC[vREAL_EQ_SUB_LADD; sum; vITERATE_DIFF; vMONOIDAL_REAL_ADD]);;

let vSUM_INCL_EXCL = try Cache.lookup_thm "SUM_INCL_EXCL" with _ ->  prove
 ((parse_term "!s t (f:A->real).\n     FINITE s /\\ FINITE t\n     ==> sum s f + sum t f = sum (s UNION t) f + sum (s INTER t) f"),
  vREWRITE_TAC[sum; vGSYM vNEUTRAL_REAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_INCL_EXCL ----> vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_SUPPORT = try Cache.lookup_thm "SUM_SUPPORT" with _ ->  prove
 ((parse_term "!f s. sum (support (+) f s) f = sum s f"),
  vSIMP_TAC[sum; iterate; vSUPPORT_SUPPORT]);;

let vSUM_ADD = try Cache.lookup_thm "SUM_ADD" with _ ->  prove
 ((parse_term "!f g s. FINITE s ==> (sum s (\\x. f(x) + g(x)) = sum s f + sum s g)"),
  vSIMP_TAC[sum; vITERATE_OP; vMONOIDAL_REAL_ADD]);;

let vSUM_ADD_GEN = try Cache.lookup_thm "SUM_ADD_GEN" with _ ->  prove
 ((parse_term "!f g s.\n       FINITE {x | x IN s /\\ ~(f x = &0)} /\\ FINITE {x | x IN s /\\ ~(g x = &0)}\n       ==> sum s (\\x. f x + g x) = sum s f + sum s g"),
  vREWRITE_TAC[vGSYM vNEUTRAL_REAL_ADD; vGSYM support; sum] ---->
  vMATCH_MP_TAC vITERATE_OP_GEN ----> vACCEPT_TAC vMONOIDAL_REAL_ADD);;

let vSUM_EQ_0 = try Cache.lookup_thm "SUM_EQ_0" with _ ->  prove
 ((parse_term "!f s. (!x:A. x IN s ==> (f(x) = &0)) ==> (sum s f = &0)"),
  vREWRITE_TAC[sum; vGSYM vNEUTRAL_REAL_ADD] ---->
  vSIMP_TAC[vITERATE_EQ_NEUTRAL; vMONOIDAL_REAL_ADD]);;

let vSUM_0 = try Cache.lookup_thm "SUM_0" with _ ->  prove
 ((parse_term "!s:A->bool. sum s (\\n. &0) = &0"),
  vSIMP_TAC[vSUM_EQ_0]);;

let vSUM_LMUL = try Cache.lookup_thm "SUM_LMUL" with _ ->  prove
 ((parse_term "!f c s:A->bool. sum s (\\x. c * f(x)) = c * sum s f"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "c = &0") ---->
  vASM_REWRITE_TAC[vREAL_MUL_LZERO; vSUM_0] ----> vREWRITE_TAC[sum] ---->
  vONCE_REWRITE_TAC[vITERATE_EXPAND_CASES] ---->
  vSUBGOAL_THEN (parse_term "support (+) (\\x:A. c * f(x)) s = support (+) f s") vSUBST1_TAC
  ++--> [vASM_SIMP_TAC[support; vREAL_ENTIRE; vNEUTRAL_REAL_ADD]; vALL_TAC] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vNEUTRAL_REAL_ADD; vREAL_MUL_RZERO] ---->
  vUNDISCH_TAC (parse_term "FINITE (support (+) f (s:A->bool))") ---->
  vSPEC_TAC((parse_term "support (+) f (s:A->bool)"),(parse_term "t:A->bool")) ---->
  vREWRITE_TAC[vGSYM sum] ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vSUM_CLAUSES; vREAL_MUL_RZERO; vREAL_MUL_LZERO;
           vREAL_ADD_LDISTRIB]);;

let vSUM_RMUL = try Cache.lookup_thm "SUM_RMUL" with _ ->  prove
 ((parse_term "!f c s:A->bool. sum s (\\x. f(x) * c) = sum s f * c"),
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vSUM_LMUL]);;

let vSUM_NEG = try Cache.lookup_thm "SUM_NEG" with _ ->  prove
 ((parse_term "!f s. sum s (\\x. --(f(x))) = --(sum s f)"),
  vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "--x = --(&1) * x")] ---->
  vSIMP_TAC[vSUM_LMUL]);;

let vSUM_SUB = try Cache.lookup_thm "SUM_SUB" with _ ->  prove
 ((parse_term "!f g s. FINITE s ==> (sum s (\\x. f(x) - g(x)) = sum s f - sum s g)"),
  vONCE_REWRITE_TAC[real_sub] ----> vSIMP_TAC[vSUM_NEG; vSUM_ADD]);;

let vSUM_LE = try Cache.lookup_thm "SUM_LE" with _ ->  prove
 ((parse_term "!f g s. FINITE(s) /\\ (!x. x IN s ==> f(x) <= g(x)) ==> sum s f <= sum s g"),
  vONCE_REWRITE_TAC[vIMP_CONJ] ---->
  vGEN_TAC ----> vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vSUM_CLAUSES; vREAL_LE_REFL; vREAL_LE_ADD2; vIN_INSERT]);;

let vSUM_LT = try Cache.lookup_thm "SUM_LT" with _ ->  prove
 ((parse_term "!f g s:A->bool.\n        FINITE(s) /\\ (!x. x IN s ==> f(x) <= g(x)) /\\\n        (?x. x IN s /\\ f(x) < g(x))\n         ==> sum s f < sum s g"),
  vREPEAT vGEN_TAC ---->
  vREPEAT(vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "a:A") vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN (parse_term "s = (a:A) INSERT (s DELETE a)") vSUBST1_TAC ++-->
   [vUNDISCH_TAC (parse_term "a:A IN s") ----> vSET_TAC[]; vALL_TAC] ---->
  vASM_SIMP_TAC[vSUM_CLAUSES; vFINITE_DELETE; vIN_DELETE] ---->
  vASM_SIMP_TAC[vREAL_LTE_ADD2; vSUM_LE; vIN_DELETE; vFINITE_DELETE]);;

let vSUM_LT_ALL = try Cache.lookup_thm "SUM_LT_ALL" with _ ->  prove
 ((parse_term "!f g s. FINITE s /\\ ~(s = {}) /\\ (!x. x IN s ==> f(x) < g(x))\n           ==> sum s f < sum s g"),
  vMESON_TAC[vMEMBER_NOT_EMPTY; vREAL_LT_IMP_LE; vSUM_LT]);;

let vSUM_POS_LT = try Cache.lookup_thm "SUM_POS_LT" with _ ->  prove
 ((parse_term "!f s:A->bool.\n        FINITE s /\\\n        (!x. x IN s ==> &0 <= f x) /\\\n        (?x. x IN s /\\ &0 < f x)\n        ==> &0 < sum s f"),
  vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC (parse_term "sum (s:A->bool) (\\i. &0)") ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vSUM_0; vREAL_LE_REFL]; vMATCH_MP_TAC vSUM_LT] ---->
  vASM_MESON_TAC[]);;

let vSUM_POS_LT_ALL = try Cache.lookup_thm "SUM_POS_LT_ALL" with _ ->  prove
 ((parse_term "!s f:A->real.\n     FINITE s /\\ ~(s = {}) /\\ (!i. i IN s ==> &0 < f i) ==> &0 < sum s f"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_POS_LT ---->
  vASM_MESON_TAC[vMEMBER_NOT_EMPTY; vREAL_LT_IMP_LE]);;

let vSUM_EQ = try Cache.lookup_thm "SUM_EQ" with _ ->  prove
 ((parse_term "!f g s. (!x. x IN s ==> (f x = g x)) ==> (sum s f = sum s g)"),
  vREWRITE_TAC[sum] ---->
  vMATCH_MP_TAC vITERATE_EQ ----> vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_ABS = try Cache.lookup_thm "SUM_ABS" with _ ->  prove
 ((parse_term "!f s. FINITE(s) ==> abs(sum s f) <= sum s (\\x. abs(f x))"),
  vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vSUM_CLAUSES; vREAL_ABS_NUM; vREAL_LE_REFL;
           vREAL_ARITH (parse_term "abs(a) <= b ==> abs(x + a) <= abs(x) + b")]);;

let vSUM_ABS_LE = try Cache.lookup_thm "SUM_ABS_LE" with _ ->  prove
 ((parse_term "!f:A->real g s.\n        FINITE s /\\ (!x. x IN s ==> abs(f x) <= g x)\n        ==> abs(sum s f) <= sum s g"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC (parse_term "sum s (\\x:A. abs(f x))") ---->
  vASM_SIMP_TAC[vSUM_ABS] ----> vMATCH_MP_TAC vSUM_LE ---->
  vASM_REWRITE_TAC[]);;

let vSUM_CONST = try Cache.lookup_thm "SUM_CONST" with _ ->  prove
 ((parse_term "!c s. FINITE s ==> (sum s (\\n. c) = &(CARD s) * c)"),
  vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vSUM_CLAUSES; vCARD_CLAUSES; vGSYM vREAL_OF_NUM_SUC] ---->
  vREPEAT vSTRIP_TAC ----> vREAL_ARITH_TAC);;

let vSUM_POS_LE = try Cache.lookup_thm "SUM_POS_LE" with _ ->  prove
 ((parse_term "!s:A->bool. (!x. x IN s ==> &0 <= f x) ==> &0 <= sum s f"),
  vREPEAT vSTRIP_TAC ---->
  vASM_CASES_TAC (parse_term "FINITE {x:A | x IN s /\\ ~(f x = &0)}") ---->
  vASM_SIMP_TAC[vSUM_DEGENERATE; vREAL_LE_REFL] ---->
  vONCE_REWRITE_TAC[vGSYM vSUM_SUPPORT] ---->
  vREWRITE_TAC[support; vNEUTRAL_REAL_ADD] ---->
  vMP_TAC(vISPECL [(parse_term "\\x:A. &0"); (parse_term "f:A->real"); (parse_term "{x:A | x IN s /\\ ~(f x = &0)}")]
        vSUM_LE) ---->
  vASM_SIMP_TAC[vSUM_0; vIN_ELIM_THM]);;

let vSUM_POS_BOUND = try Cache.lookup_thm "SUM_POS_BOUND" with _ ->  prove
 ((parse_term "!f b s. FINITE s /\\ (!x. x IN s ==> &0 <= f x) /\\ sum s f <= b\n           ==> !x:A. x IN s ==> f x <= b"),
  vGEN_TAC ----> vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vSUM_CLAUSES; vNOT_IN_EMPTY; vIN_INSERT] ---->
  vMESON_TAC[vSUM_POS_LE;
   vREAL_ARITH (parse_term "&0 <= x /\\ &0 <= y /\\ x + y <= b ==> x <= b /\\ y <= b")]);;

let vSUM_POS_EQ_0 = try Cache.lookup_thm "SUM_POS_EQ_0" with _ ->  prove
 ((parse_term "!f s. FINITE s /\\ (!x. x IN s ==> &0 <= f x) /\\ (sum s f = &0)\n         ==> !x. x IN s ==> f x = &0"),
  vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
  vMESON_TAC[vSUM_POS_BOUND; vSUM_POS_LE]);;

let vSUM_ZERO_EXISTS = try Cache.lookup_thm "SUM_ZERO_EXISTS" with _ ->  prove
 ((parse_term "!(u:A->real) s.\n         FINITE s /\\ sum s u = &0\n         ==> (!i. i IN s ==> u i = &0) \\/\n             (?j k. j IN s /\\ u j < &0 /\\ k IN s /\\ u k > &0)"),
  vREPEAT vSTRIP_TAC ----> vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC
   (vMESON[vREAL_ARITH (parse_term "(&0 <= --u <=> ~(u > &0)) /\\ (&0 <= u <=> ~(u < &0))")]
     (parse_term "(?j k:A. j IN s /\\ u j < &0 /\\ k IN s /\\ u k > &0) \\/\n      (!i. i IN s ==> &0 <= u i) \\/ (!i. i IN s ==> &0 <= --(u i))")) ---->
  vASM_REWRITE_TAC[] ----> vDISJ1_TAC ++-->
   [vALL_TAC; vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "x = &0 <=> --x = &0")]] ---->
  vMATCH_MP_TAC vSUM_POS_EQ_0 ----> vASM_REWRITE_TAC[vSUM_NEG; vREAL_NEG_0]);;

let vSUM_DELETE = try Cache.lookup_thm "SUM_DELETE" with _ ->  prove
 ((parse_term "!f s a. FINITE s /\\ a IN s ==> sum (s DELETE a) f = sum s f - f(a)"),
  vSIMP_TAC[vREAL_ARITH (parse_term "y = z - x <=> x + y = z:real"); sum; vITERATE_DELETE;
           vMONOIDAL_REAL_ADD]);;

let vSUM_DELETE_CASES = try Cache.lookup_thm "SUM_DELETE_CASES" with _ ->  prove
 ((parse_term "!f s a. FINITE s\n           ==> sum (s DELETE a) f = if a IN s then sum s f - f(a)\n                                    else sum s f"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vSET_RULE (parse_term "~(a IN s) ==> (s DELETE a = s)"); vSUM_DELETE]);;

let vSUM_SING = try Cache.lookup_thm "SUM_SING" with _ ->  prove
 ((parse_term "!f x. sum {x} f = f(x)"),
  vSIMP_TAC[vSUM_CLAUSES; vFINITE_RULES; vNOT_IN_EMPTY; vREAL_ADD_RID]);;

let vSUM_DELTA = try Cache.lookup_thm "SUM_DELTA" with _ ->  prove
 ((parse_term "!s a. sum s (\\x. if x = a:A then b else &0) = if a IN s then b else &0"),
  vREWRITE_TAC[sum; vGSYM vNEUTRAL_REAL_ADD] ---->
  vSIMP_TAC[vITERATE_DELTA; vMONOIDAL_REAL_ADD]);;

let vSUM_SWAP = try Cache.lookup_thm "SUM_SWAP" with _ ->  prove
 ((parse_term "!f:A->B->real s t.\n      FINITE(s) /\\ FINITE(t)\n      ==> (sum s (\\i. sum t (f i)) = sum t (\\j. sum s (\\i. f i j)))"),
  vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vSUM_CLAUSES; vSUM_0; vSUM_ADD; vETA_AX]);;

let vSUM_IMAGE = try Cache.lookup_thm "SUM_IMAGE" with _ ->  prove
 ((parse_term "!f g s. (!x y. x IN s /\\ y IN s /\\ (f x = f y) ==> (x = y))\n           ==> (sum (IMAGE f s) g = sum s (g o f))"),
  vREWRITE_TAC[sum; vGSYM vNEUTRAL_REAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_IMAGE ----> vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_SUPERSET = try Cache.lookup_thm "SUM_SUPERSET" with _ ->  prove
 ((parse_term "!f:A->real u v.\n        u SUBSET v /\\ (!x. x IN v /\\ ~(x IN u) ==> (f(x) = &0))\n        ==> (sum v f = sum u f)"),
  vSIMP_TAC[sum; vGSYM vNEUTRAL_REAL_ADD; vITERATE_SUPERSET; vMONOIDAL_REAL_ADD]);;

let vSUM_UNIV = try Cache.lookup_thm "SUM_UNIV" with _ ->  prove
 ((parse_term "!f:A->real s. support (+) f (:A) SUBSET s ==> sum s f = sum (:A) f"),
  vREWRITE_TAC[sum] ----> vMATCH_MP_TAC vITERATE_UNIV ---->
  vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_UNION_RZERO = try Cache.lookup_thm "SUM_UNION_RZERO" with _ ->  prove
 ((parse_term "!f:A->real u v.\n        FINITE u /\\ (!x. x IN v /\\ ~(x IN u) ==> (f(x) = &0))\n        ==> (sum (u UNION v) f = sum u f)"),
  let lemma = prove((parse_term "u UNION v = u UNION (v DIFF u)"),vSET_TAC[]) in
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[lemma] ---->
  vMATCH_MP_TAC vSUM_SUPERSET ---->
  vASM_MESON_TAC[vIN_UNION; vIN_DIFF; vSUBSET]);;

let vSUM_UNION_LZERO = try Cache.lookup_thm "SUM_UNION_LZERO" with _ ->  prove
 ((parse_term "!f:A->real u v.\n        FINITE v /\\ (!x. x IN u /\\ ~(x IN v) ==> (f(x) = &0))\n        ==> (sum (u UNION v) f = sum v f)"),
  vMESON_TAC[vSUM_UNION_RZERO; vUNION_COMM]);;

let vSUM_RESTRICT = try Cache.lookup_thm "SUM_RESTRICT" with _ ->  prove
 ((parse_term "!f s. FINITE s ==> (sum s (\\x. if x IN s then f(x) else &0) = sum s f)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_EQ ----> vASM_SIMP_TAC[]);;

let vSUM_BOUND = try Cache.lookup_thm "SUM_BOUND" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ (!x:A. x IN s ==> f(x) <= b)\n           ==> sum s f <= &(CARD s) * b"),
  vSIMP_TAC[vGSYM vSUM_CONST; vSUM_LE]);;

let vSUM_BOUND_GEN = try Cache.lookup_thm "SUM_BOUND_GEN" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ ~(s = {}) /\\ (!x:A. x IN s ==> f(x) <= b / &(CARD s))\n           ==> sum s f <= b"),
  vMESON_TAC[vSUM_BOUND; vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vHAS_SIZE_0;
            vHAS_SIZE]);;

let vSUM_ABS_BOUND = try Cache.lookup_thm "SUM_ABS_BOUND" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ (!x:A. x IN s ==> abs(f(x)) <= b)\n           ==> abs(sum s f) <= &(CARD s) * b"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC (parse_term "sum s (\\x:A. abs(f x))") ---->
  vASM_SIMP_TAC[vSUM_BOUND; vSUM_ABS]);;

let vSUM_BOUND_LT = try Cache.lookup_thm "SUM_BOUND_LT" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ (!x:A. x IN s ==> f x <= b) /\\ (?x. x IN s /\\ f x < b)\n           ==> sum s f < &(CARD s) * b"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LTE_TRANS ---->
  vEXISTS_TAC (parse_term "sum s (\\x:A. b)") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSUM_LT ----> vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[];
    vASM_SIMP_TAC[vSUM_CONST; vREAL_LE_REFL]]);;

let vSUM_BOUND_LT_ALL = try Cache.lookup_thm "SUM_BOUND_LT_ALL" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ ~(s = {}) /\\ (!x. x IN s ==> f(x) < b)\n           ==> sum s f <  &(CARD s) * b"),
  vMESON_TAC[vMEMBER_NOT_EMPTY; vREAL_LT_IMP_LE; vSUM_BOUND_LT]);;

let vSUM_BOUND_LT_GEN = try Cache.lookup_thm "SUM_BOUND_LT_GEN" with _ ->  prove
 ((parse_term "!s f b. FINITE s /\\ ~(s = {}) /\\ (!x:A. x IN s ==> f(x) < b / &(CARD s))\n           ==> sum s f < b"),
  vMESON_TAC[vSUM_BOUND_LT_ALL; vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vHAS_SIZE_0;
            vHAS_SIZE]);;

let vSUM_UNION_EQ = try Cache.lookup_thm "SUM_UNION_EQ" with _ ->  prove
 ((parse_term "!s t u. FINITE u /\\ (s INTER t = {}) /\\ (s UNION t = u)\n           ==> (sum s f + sum t f = sum u f)"),
  vMESON_TAC[vSUM_UNION; vDISJOINT; vFINITE_SUBSET; vSUBSET_UNION]);;

let vSUM_EQ_SUPERSET = try Cache.lookup_thm "SUM_EQ_SUPERSET" with _ ->  prove
 ((parse_term "!f s t:A->bool.\n        FINITE t /\\ t SUBSET s /\\\n        (!x. x IN t ==> (f x = g x)) /\\\n        (!x. x IN s /\\ ~(x IN t) ==> (f(x) = &0))\n        ==> (sum s f = sum t g)"),
  vMESON_TAC[vSUM_SUPERSET; vSUM_EQ]);;

let vSUM_RESTRICT_SET = try Cache.lookup_thm "SUM_RESTRICT_SET" with _ ->  prove
 ((parse_term "!P s f. sum {x | x IN s /\\ P x} f = sum s (\\x. if P x then f x else &0)"),
  vREWRITE_TAC[sum; vGSYM vNEUTRAL_REAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_RESTRICT_SET ----> vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_SUM_RESTRICT = try Cache.lookup_thm "SUM_SUM_RESTRICT" with _ ->  prove
 ((parse_term "!R f s t.\n        FINITE s /\\ FINITE t\n        ==> (sum s (\\x. sum {y | y IN t /\\ R x y} (\\y. f x y)) =\n             sum t (\\y. sum {x | x IN s /\\ R x y} (\\x. f x y)))"),
  vREPEAT vGEN_TAC ----> vSIMP_TAC[vSUM_RESTRICT_SET] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vSUM_SWAP th]));;

let vCARD_EQ_SUM = try Cache.lookup_thm "CARD_EQ_SUM" with _ ->  prove
 ((parse_term "!s. FINITE s ==> (&(CARD s) = sum s (\\x. &1))"),
  vSIMP_TAC[vSUM_CONST; vREAL_MUL_RID]);;

let vSUM_MULTICOUNT_GEN = try Cache.lookup_thm "SUM_MULTICOUNT_GEN" with _ ->  prove
 ((parse_term "!R:A->B->bool s t k.\n        FINITE s /\\ FINITE t /\\\n        (!j. j IN t ==> (CARD {i | i IN s /\\ R i j} = k(j)))\n        ==> (sum s (\\i. &(CARD {j | j IN t /\\ R i j})) =\n             sum t (\\i. &(k i)))"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vCONJ_ASSOC] ---->
  vDISCH_THEN(vCONJUNCTS_THEN vASSUME_TAC) ---->
  vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "sum s (\\i:A. sum {j:B | j IN t /\\ R i j} (\\j. &1))") ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSUM_EQ ----> vASM_REWRITE_TAC[] ----> vREPEAT vSTRIP_TAC ---->
    vASM_SIMP_TAC[vCARD_EQ_SUM; vFINITE_RESTRICT];
    vFIRST_ASSUM(fun th ->
      vONCE_REWRITE_TAC[vMATCH_MP vSUM_SUM_RESTRICT th]) ---->
    vMATCH_MP_TAC vSUM_EQ ---->
    vASM_SIMP_TAC[vSUM_CONST; vFINITE_RESTRICT] ---->
    vREWRITE_TAC[vREAL_MUL_RID]]);;

let vSUM_MULTICOUNT = try Cache.lookup_thm "SUM_MULTICOUNT" with _ ->  prove
 ((parse_term "!R:A->B->bool s t k.\n        FINITE s /\\ FINITE t /\\\n        (!j. j IN t ==> (CARD {i | i IN s /\\ R i j} = k))\n        ==> (sum s (\\i. &(CARD {j | j IN t /\\ R i j})) = &(k * CARD t))"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "sum t (\\i:B. &k)") ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSUM_MULTICOUNT_GEN ----> vASM_REWRITE_TAC[];
    vASM_SIMP_TAC[vSUM_CONST; vREAL_OF_NUM_MUL] ----> vREWRITE_TAC[vMULT_AC]]);;

let vSUM_IMAGE_GEN = try Cache.lookup_thm "SUM_IMAGE_GEN" with _ ->  prove
 ((parse_term "!f:A->B g s.\n        FINITE s\n        ==> sum s g =\n            sum (IMAGE f s) (\\y. sum {x | x IN s /\\ f x = y} g)"),
  vREWRITE_TAC[sum] ----> vMATCH_MP_TAC vITERATE_IMAGE_GEN ---->
  vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_GROUP = try Cache.lookup_thm "SUM_GROUP" with _ ->  prove
 ((parse_term "!f:A->B g s t.\n        FINITE s /\\ IMAGE f s SUBSET t\n        ==> sum t (\\y. sum {x | x IN s /\\ f(x) = y} g) = sum s g"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->B"); (parse_term "g:A->real"); (parse_term "s:A->bool")] vSUM_IMAGE_GEN) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN vSUBST1_TAC ---->
  vMATCH_MP_TAC vSUM_SUPERSET ----> vASM_REWRITE_TAC[] ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_EQ_0 ----> vASM vSET_TAC[]);;

let vSUM_GROUP_RELATION = try Cache.lookup_thm "SUM_GROUP_RELATION" with _ ->  prove
 ((parse_term "!R:A->B->bool g s t.\n         FINITE s /\\\n         (!x. x IN s ==> ?!y. y IN t /\\ R x y)\n         ==> sum t (\\y. sum {x | x IN s /\\ R x y} g) = sum s g"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "\\x:A. @y:B. y IN t /\\ R x y"); (parse_term "g:A->real");
                 (parse_term "s:A->bool"); (parse_term "t:B->bool")]
        vSUM_GROUP) ---->
  vASM_REWRITE_TAC[vSUBSET; vFORALL_IN_IMAGE] ---->
  vANTS_TAC ++--> [vASM_MESON_TAC[]; vDISCH_THEN(vSUBST1_TAC -| vSYM)] ---->
  vMATCH_MP_TAC vSUM_EQ ----> vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vASM vSET_TAC[]);;

let vREAL_OF_NUM_SUM = try Cache.lookup_thm "REAL_OF_NUM_SUM" with _ ->  prove
 ((parse_term "!f s. FINITE s ==> (&(nsum s f) = sum s (\\x. &(f x)))"),
  vGEN_TAC ----> vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vSUM_CLAUSES; vNSUM_CLAUSES; vGSYM vREAL_OF_NUM_ADD]);;

let vSUM_SUBSET = try Cache.lookup_thm "SUM_SUBSET" with _ ->  prove
 ((parse_term "!u v f. FINITE u /\\ FINITE v /\\\n           (!x. x IN (u DIFF v) ==> f(x) <= &0) /\\\n           (!x:A. x IN (v DIFF u) ==> &0 <= f(x))\n           ==> sum u f <= sum v f"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:A->real"); (parse_term "u INTER v :A->bool")] vSUM_UNION) ---->
  vDISCH_THEN(fun th -> vMP_TAC(vSPEC (parse_term "v DIFF u :A->bool") th) ---->
                       vMP_TAC(vSPEC (parse_term "u DIFF v :A->bool") th)) ---->
  vREWRITE_TAC[vSET_RULE (parse_term "(u INTER v) UNION (u DIFF v) = u");
              vSET_RULE (parse_term "(u INTER v) UNION (v DIFF u) = v")] ---->
  vASM_SIMP_TAC[vFINITE_DIFF; vFINITE_INTER] ---->
  vREPEAT(vANTS_TAC ++--> [vSET_TAC[]; vDISCH_THEN vSUBST1_TAC]) ---->
  vMATCH_MP_TAC(vREAL_ARITH (parse_term "&0 <= --x /\\ &0 <= y ==> a + x <= a + y")) ---->
  vASM_SIMP_TAC[vGSYM vSUM_NEG; vFINITE_DIFF] ----> vCONJ_TAC ---->
  vMATCH_MP_TAC vSUM_POS_LE ---->
  vASM_SIMP_TAC[vFINITE_DIFF; vREAL_LE_RNEG; vREAL_ADD_LID]);;

let vSUM_SUBSET_SIMPLE = try Cache.lookup_thm "SUM_SUBSET_SIMPLE" with _ ->  prove
 ((parse_term "!u v f. FINITE v /\\ u SUBSET v /\\ (!x:A. x IN (v DIFF u) ==> &0 <= f(x))\n\n           ==> sum u f <= sum v f"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_SUBSET ---->
  vASM_MESON_TAC[vIN_DIFF; vSUBSET; vFINITE_SUBSET]);;

let vSUM_MUL_BOUND = try Cache.lookup_thm "SUM_MUL_BOUND" with _ ->  prove
 ((parse_term "!a b s:A->bool.\n        FINITE s /\\ (!i. i IN s ==> &0 <= a i /\\ &0 <= b i)\n        ==> sum s (\\i. a i * b i) <= sum s a * sum s b"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vSUM_LMUL] ---->
  vMATCH_MP_TAC vSUM_LE ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC (parse_term "i:A") ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LE_RMUL ---->
  vASM_SIMP_TAC[] ----> vGEN_REWRITE_TAC vLAND_CONV [vGSYM vSUM_SING] ---->
  vMATCH_MP_TAC vSUM_SUBSET_SIMPLE ---->
  vASM_SIMP_TAC[vSING_SUBSET; vIN_DIFF]);;

let vSUM_IMAGE_NONZERO = try Cache.lookup_thm "SUM_IMAGE_NONZERO" with _ ->  prove
 ((parse_term "!d:B->real i:A->B s.\n    FINITE s /\\\n    (!x y. x IN s /\\ y IN s /\\ ~(x = y) /\\ i x = i y ==> d(i x) = &0)\n    ==> sum (IMAGE i s) d = sum s (d o i)"),
  vREWRITE_TAC[vGSYM vNEUTRAL_REAL_ADD; sum] ---->
  vMATCH_MP_TAC vITERATE_IMAGE_NONZERO ----> vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_BIJECTION = try Cache.lookup_thm "SUM_BIJECTION" with _ ->  prove
 ((parse_term "!f p s:A->bool.\n                (!x. x IN s ==> p(x) IN s) /\\\n                (!y. y IN s ==> ?!x. x IN s /\\ p(x) = y)\n                ==> sum s f = sum s (f o p)"),
  vREWRITE_TAC[sum] ----> vMATCH_MP_TAC vITERATE_BIJECTION ---->
  vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_SUM_PRODUCT = try Cache.lookup_thm "SUM_SUM_PRODUCT" with _ ->  prove
 ((parse_term "!s:A->bool t:A->B->bool x.\n        FINITE s /\\ (!i. i IN s ==> FINITE(t i))\n        ==> sum s (\\i. sum (t i) (x i)) =\n            sum {i,j | i IN s /\\ j IN t i} (\\(i,j). x i j)"),
  vREWRITE_TAC[sum] ----> vMATCH_MP_TAC vITERATE_ITERATE_PRODUCT ---->
  vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_EQ_GENERAL = try Cache.lookup_thm "SUM_EQ_GENERAL" with _ ->  prove
 ((parse_term "!s:A->bool t:B->bool f g h.\n        (!y. y IN t ==> ?!x. x IN s /\\ h(x) = y) /\\\n        (!x. x IN s ==> h(x) IN t /\\ g(h x) = f x)\n        ==> sum s f = sum t g"),
  vREWRITE_TAC[sum] ----> vMATCH_MP_TAC vITERATE_EQ_GENERAL ---->
  vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_EQ_GENERAL_INVERSES = try Cache.lookup_thm "SUM_EQ_GENERAL_INVERSES" with _ ->  prove
 ((parse_term "!s:A->bool t:B->bool f g h k.\n        (!y. y IN t ==> k(y) IN s /\\ h(k y) = y) /\\\n        (!x. x IN s ==> h(x) IN t /\\ k(h x) = x /\\ g(h x) = f x)\n        ==> sum s f = sum t g"),
  vREWRITE_TAC[sum] ----> vMATCH_MP_TAC vITERATE_EQ_GENERAL_INVERSES ---->
  vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_INJECTION = try Cache.lookup_thm "SUM_INJECTION" with _ ->  prove
 ((parse_term "!f p s. FINITE s /\\\n           (!x. x IN s ==> p x IN s) /\\\n           (!x y. x IN s /\\ y IN s /\\ p x = p y ==> x = y)\n           ==> sum s (f o p) = sum s f"),
  vREWRITE_TAC[sum] ----> vMATCH_MP_TAC vITERATE_INJECTION ---->
  vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_UNION_NONZERO = try Cache.lookup_thm "SUM_UNION_NONZERO" with _ ->  prove
 ((parse_term "!f s t. FINITE s /\\ FINITE t /\\ (!x. x IN s INTER t ==> f(x) = &0)\n           ==> sum (s UNION t) f = sum s f + sum t f"),
  vREWRITE_TAC[sum; vGSYM vNEUTRAL_REAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_UNION_NONZERO ----> vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_UNIONS_NONZERO = try Cache.lookup_thm "SUM_UNIONS_NONZERO" with _ ->  prove
 ((parse_term "!f s. FINITE s /\\ (!t:A->bool. t IN s ==> FINITE t) /\\\n         (!t1 t2 x. t1 IN s /\\ t2 IN s /\\ ~(t1 = t2) /\\ x IN t1 /\\ x IN t2\n                    ==> f x = &0)\n         ==> sum (UNIONS s) f = sum s (\\t. sum t f)"),
  vGEN_TAC ----> vONCE_REWRITE_TAC[vIMP_CONJ] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vREWRITE_TAC[vUNIONS_0; vUNIONS_INSERT; vSUM_CLAUSES; vIN_INSERT] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "t:A->bool"); (parse_term "s:(A->bool)->bool")] ---->
  vDISCH_THEN(fun th -> vSTRIP_TAC ----> vMP_TAC th) ---->
  vONCE_REWRITE_TAC[vIMP_CONJ] ----> vASM_SIMP_TAC[vSUM_CLAUSES] ---->
  vANTS_TAC ++-->  [vASM_MESON_TAC[]; vDISCH_THEN(vSUBST_ALL_TAC -| vSYM)] ---->
  vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_UNION_NONZERO ---->
  vASM_SIMP_TAC[vFINITE_UNIONS; vIN_INTER; vIN_UNIONS] ----> vASM_MESON_TAC[]);;

let vSUM_CASES = try Cache.lookup_thm "SUM_CASES" with _ ->  prove
 ((parse_term "!s P f g. FINITE s\n             ==> sum s (\\x:A. if P x then f x else g x) =\n                 sum {x | x IN s /\\ P x} f + sum {x | x IN s /\\ ~P x} g"),
  vREWRITE_TAC[sum; vGSYM vNEUTRAL_REAL_ADD] ---->
  vMATCH_MP_TAC vITERATE_CASES ----> vREWRITE_TAC[vMONOIDAL_REAL_ADD]);;

let vSUM_CASES_1 = try Cache.lookup_thm "SUM_CASES_1" with _ ->  prove
 ((parse_term "!s a. FINITE s /\\ a IN s\n         ==> sum s (\\x. if x = a then y else f(x)) = sum s f + (y - f a)"),
  vREPEAT vSTRIP_TAC ----> vASM_SIMP_TAC[vSUM_CASES] ---->
  vASM_SIMP_TAC[vGSYM vDELETE; vSUM_DELETE] ---->
  vASM_SIMP_TAC[vSET_RULE (parse_term "a IN s ==> {x | x IN s /\\ x = a} = {a}")] ---->
  vREWRITE_TAC[vSUM_SING] ----> vREAL_ARITH_TAC);;

let vSUM_LE_INCLUDED = try Cache.lookup_thm "SUM_LE_INCLUDED" with _ ->  prove
 ((parse_term "!f:A->real g:B->real s t i.\n        FINITE s /\\ FINITE t /\\\n        (!y. y IN t ==> &0 <= g y) /\\\n        (!x. x IN s ==> ?y. y IN t /\\ i y = x /\\ f(x) <= g(y))\n        ==> sum s f <= sum t g"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC (parse_term "sum (IMAGE (i:B->A) t) (\\y. sum {x | x IN t /\\ i x = y} g)") ---->
  vCONJ_TAC ++-->
   [vALL_TAC;
    vMATCH_MP_TAC vREAL_EQ_IMP_LE ---->
    vMATCH_MP_TAC(vGSYM vSUM_IMAGE_GEN) ----> vASM_REWRITE_TAC[]] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC (parse_term "sum s (\\y. sum {x | x IN t /\\ (i:B->A) x = y} g)") ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSUM_LE ----> vASM_REWRITE_TAC[] ----> vX_GEN_TAC (parse_term "x:A") ---->
    vDISCH_TAC ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "x:A")) ---->
    vASM_REWRITE_TAC[vLEFT_IMP_EXISTS_THM] ----> vX_GEN_TAC (parse_term "y:B") ---->
    vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
    vEXISTS_TAC (parse_term "sum {y:B} g") ----> vCONJ_TAC ++-->
     [vASM_REWRITE_TAC[vSUM_SING]; vALL_TAC];
    vALL_TAC] ---->
  vMATCH_MP_TAC vSUM_SUBSET_SIMPLE ----> vASM_SIMP_TAC[vFINITE_IMAGE] ---->
  vASM_SIMP_TAC[vSUM_POS_LE; vFINITE_RESTRICT; vIN_ELIM_THM] ---->
  vASM vSET_TAC[]);;

let vSUM_IMAGE_LE = try Cache.lookup_thm "SUM_IMAGE_LE" with _ ->  prove
 ((parse_term "!f:A->B g s.\n        FINITE s /\\\n        (!x. x IN s ==> &0 <= g(f x))\n        ==> sum (IMAGE f s) g <= sum s (g o f)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_LE_INCLUDED ---->
  vASM_SIMP_TAC[vFINITE_IMAGE; vFORALL_IN_IMAGE] ---->
  vASM_REWRITE_TAC[o_THM] ----> vEXISTS_TAC (parse_term "f:A->B") ---->
  vMESON_TAC[vREAL_LE_REFL]);;

let vSUM_CLOSED = try Cache.lookup_thm "SUM_CLOSED" with _ ->  prove
 ((parse_term "!P f:A->real s.\n        P(&0) /\\ (!x y. P x /\\ P y ==> P(x + y)) /\\ (!a. a IN s ==> P(f a))\n        ==> P(sum s f)"),
  vREPEAT vSTRIP_TAC ----> vMP_TAC(vMATCH_MP vITERATE_CLOSED vMONOIDAL_REAL_ADD) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "P:real->bool")) ---->
  vASM_SIMP_TAC[vNEUTRAL_REAL_ADD; vGSYM sum]);;

let vSUM_RELATED = try Cache.lookup_thm "SUM_RELATED" with _ ->  prove
 ((parse_term "!R (f:A->real) g s.\n        R (&0) (&0) /\\\n        (!m n m' n'. R m n /\\ R m' n' ==> R (m + m') (n + n')) /\\\n        FINITE s /\\ (!x. x IN s ==> R (f x) (g x))\n        ==> R (sum s f) (sum s g)"),
  vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vGEN_TAC ----> vREPEAT vDISCH_TAC ---->
  vMP_TAC(vISPEC (parse_term "R:real->real->bool")
    (vMATCH_MP vITERATE_RELATED vMONOIDAL_REAL_ADD)) ---->
  vASM_REWRITE_TAC[vGSYM sum; vNEUTRAL_REAL_ADD] ----> vASM_MESON_TAC[]);;

let vSUM_CLOSED_NONEMPTY = try Cache.lookup_thm "SUM_CLOSED_NONEMPTY" with _ ->  prove
 ((parse_term "!P f:A->real s.\n        FINITE s /\\ ~(s = {}) /\\\n        (!x y. P x /\\ P y ==> P(x + y)) /\\ (!a. a IN s ==> P(f a))\n        ==> P(sum s f)"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vMATCH_MP vITERATE_CLOSED_NONEMPTY vMONOIDAL_REAL_ADD) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "P:real->bool")) ---->
  vASM_SIMP_TAC[vNEUTRAL_REAL_ADD; vGSYM sum]);;

let vSUM_RELATED_NONEMPTY = try Cache.lookup_thm "SUM_RELATED_NONEMPTY" with _ ->  prove
 ((parse_term "!R (f:A->real) g s.\n        (!m n m' n'. R m n /\\ R m' n' ==> R (m + m') (n + n')) /\\\n        FINITE s /\\ ~(s = {}) /\\ (!x. x IN s ==> R (f x) (g x))\n        ==> R (sum s f) (sum s g)"),
  vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vGEN_TAC ----> vREPEAT vDISCH_TAC ---->
  vMP_TAC(vISPEC (parse_term "R:real->real->bool")
    (vMATCH_MP vITERATE_RELATED_NONEMPTY vMONOIDAL_REAL_ADD)) ---->
  vASM_REWRITE_TAC[vGSYM sum; vNEUTRAL_REAL_ADD] ----> vASM_MESON_TAC[]);;

let vREAL_OF_NUM_SUM_GEN = try Cache.lookup_thm "REAL_OF_NUM_SUM_GEN" with _ ->  prove
 ((parse_term "!f s:A->bool.\n       FINITE {i | i IN s /\\ ~(f i = 0)} ==> &(nsum s f) = sum s (\\x. &(f x))"),
  vREPEAT vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vSUM_SUPPORT; vGSYM vNSUM_SUPPORT] ---->
  vREWRITE_TAC[support; vNEUTRAL_ADD; vNEUTRAL_REAL_ADD; vREAL_OF_NUM_EQ] ---->
  vASM_SIMP_TAC[vREAL_OF_NUM_SUM]);;

(* ------------------------------------------------------------------------- *)
(* Specialize them to sums over intervals of numbers.                        *)
(* ------------------------------------------------------------------------- *)

let vSUM_ADD_NUMSEG = try Cache.lookup_thm "SUM_ADD_NUMSEG" with _ ->  prove
 ((parse_term "!f g m n. sum(m..n) (\\i. f(i) + g(i)) = sum(m..n) f + sum(m..n) g"),
  vSIMP_TAC[vSUM_ADD; vFINITE_NUMSEG]);;

let vSUM_SUB_NUMSEG = try Cache.lookup_thm "SUM_SUB_NUMSEG" with _ ->  prove
 ((parse_term "!f g m n. sum(m..n) (\\i. f(i) - g(i)) = sum(m..n) f - sum(m..n) g"),
   vSIMP_TAC[vSUM_SUB; vFINITE_NUMSEG]);;

let vSUM_LE_NUMSEG = try Cache.lookup_thm "SUM_LE_NUMSEG" with _ ->  prove
 ((parse_term "!f g m n. (!i. m <= i /\\ i <= n ==> f(i) <= g(i))\n             ==> sum(m..n) f <= sum(m..n) g"),
  vSIMP_TAC[vSUM_LE; vFINITE_NUMSEG; vIN_NUMSEG]);;

let vSUM_EQ_NUMSEG = try Cache.lookup_thm "SUM_EQ_NUMSEG" with _ ->  prove
 ((parse_term "!f g m n. (!i. m <= i /\\ i <= n ==> (f(i) = g(i)))\n             ==> (sum(m..n) f = sum(m..n) g)"),
  vMESON_TAC[vSUM_EQ; vFINITE_NUMSEG; vIN_NUMSEG]);;

let vSUM_ABS_NUMSEG = try Cache.lookup_thm "SUM_ABS_NUMSEG" with _ ->  prove
 ((parse_term "!f m n. abs(sum(m..n) f) <= sum(m..n) (\\i. abs(f i))"),
  vSIMP_TAC[vSUM_ABS; vFINITE_NUMSEG]);;

let vSUM_CONST_NUMSEG = try Cache.lookup_thm "SUM_CONST_NUMSEG" with _ ->  prove
 ((parse_term "!c m n. sum(m..n) (\\n. c) = &((n + 1) - m) * c"),
  vSIMP_TAC[vSUM_CONST; vFINITE_NUMSEG; vCARD_NUMSEG]);;

let vSUM_EQ_0_NUMSEG = try Cache.lookup_thm "SUM_EQ_0_NUMSEG" with _ ->  prove
 ((parse_term "!f m n. (!i. m <= i /\\ i <= n ==> (f(i) = &0)) ==> (sum(m..n) f = &0)"),
  vSIMP_TAC[vSUM_EQ_0; vIN_NUMSEG]);;

let vSUM_TRIV_NUMSEG = try Cache.lookup_thm "SUM_TRIV_NUMSEG" with _ ->  prove
 ((parse_term "!f m n. n < m ==> (sum(m..n) f = &0)"),
  vMESON_TAC[vSUM_EQ_0_NUMSEG; vLE_TRANS; vNOT_LT]);;

let vSUM_POS_LE_NUMSEG = try Cache.lookup_thm "SUM_POS_LE_NUMSEG" with _ ->  prove
 ((parse_term "!m n f. (!p. m <= p /\\ p <= n ==> &0 <= f(p)) ==> &0 <= sum(m..n) f"),
  vSIMP_TAC[vSUM_POS_LE; vFINITE_NUMSEG; vIN_NUMSEG]);;

let vSUM_POS_EQ_0_NUMSEG = try Cache.lookup_thm "SUM_POS_EQ_0_NUMSEG" with _ ->  prove
 ((parse_term "!f m n. (!p. m <= p /\\ p <= n ==> &0 <= f(p)) /\\ (sum(m..n) f = &0)\n           ==> !p. m <= p /\\ p <= n ==> (f(p) = &0)"),
  vMESON_TAC[vSUM_POS_EQ_0; vFINITE_NUMSEG; vIN_NUMSEG]);;

let vSUM_SING_NUMSEG = try Cache.lookup_thm "SUM_SING_NUMSEG" with _ ->  prove
 ((parse_term "!f n. sum(n..n) f = f(n)"),
  vSIMP_TAC[vSUM_SING; vNUMSEG_SING]);;

let vSUM_CLAUSES_NUMSEG = try Cache.lookup_thm "SUM_CLAUSES_NUMSEG" with _ ->  prove
 ((parse_term "(!m. sum(m..0) f = if m = 0 then f(0) else &0) /\\\n   (!m n. sum(m..SUC n) f = if m <= SUC n then sum(m..n) f + f(SUC n)\n                            else sum(m..n) f)"),
  vMP_TAC(vMATCH_MP vITERATE_CLAUSES_NUMSEG vMONOIDAL_REAL_ADD) ---->
  vREWRITE_TAC[vNEUTRAL_REAL_ADD; sum]);;

let vSUM_CLAUSES_NUMSEG_LT = try Cache.lookup_thm "SUM_CLAUSES_NUMSEG_LT" with _ ->  prove
 ((parse_term "sum {i | i < 0} f = &0 /\\\n   (!k. sum {i | i < SUC k} f = sum {i | i < k} f + f k)"),
  vMP_TAC(vMATCH_MP vITERATE_CLAUSES_NUMSEG_LT vMONOIDAL_REAL_ADD) ---->
  vREWRITE_TAC[vNEUTRAL_REAL_ADD; sum]);;

let vSUM_CLAUSES_NUMSEG_LE = try Cache.lookup_thm "SUM_CLAUSES_NUMSEG_LE" with _ ->  prove
 ((parse_term "sum {i | i <= 0} f = f 0 /\\\n   (!k. sum {i | i <= SUC k} f = sum {i | i <= k} f + f(SUC k))"),
  vMP_TAC(vMATCH_MP vITERATE_CLAUSES_NUMSEG_LE vMONOIDAL_REAL_ADD) ---->
  vREWRITE_TAC[vNEUTRAL_REAL_ADD; sum]);;

let vSUM_SWAP_NUMSEG = try Cache.lookup_thm "SUM_SWAP_NUMSEG" with _ ->  prove
 ((parse_term "!a b c d f.\n     sum(a..b) (\\i. sum(c..d) (f i)) = sum(c..d) (\\j. sum(a..b) (\\i. f i j))"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vSUM_SWAP ---->
  vREWRITE_TAC[vFINITE_NUMSEG]);;

let vSUM_ADD_SPLIT = try Cache.lookup_thm "SUM_ADD_SPLIT" with _ ->  prove
 ((parse_term "!f m n p.\n        m <= n + 1 ==> (sum (m..(n+p)) f = sum(m..n) f + sum(n+1..n+p) f)"),
  vSIMP_TAC[vNUMSEG_ADD_SPLIT; vSUM_UNION; vDISJOINT_NUMSEG; vFINITE_NUMSEG;
           vARITH_RULE (parse_term "x < x + 1")]);;

let vSUM_OFFSET = try Cache.lookup_thm "SUM_OFFSET" with _ ->  prove
 ((parse_term "!p f m n. sum(m+p..n+p) f = sum(m..n) (\\i. f(i + p))"),
  vSIMP_TAC[vNUMSEG_OFFSET_IMAGE; vSUM_IMAGE;
           vEQ_ADD_RCANCEL; vFINITE_NUMSEG] ---->
  vREWRITE_TAC[o_DEF]);;

let vSUM_OFFSET_0 = try Cache.lookup_thm "SUM_OFFSET_0" with _ ->  prove
 ((parse_term "!f m n. m <= n ==> (sum(m..n) f = sum(0..n-m) (\\i. f(i + m)))"),
  vSIMP_TAC[vGSYM vSUM_OFFSET; vADD_CLAUSES; vSUB_ADD]);;

let vSUM_CLAUSES_LEFT = try Cache.lookup_thm "SUM_CLAUSES_LEFT" with _ ->  prove
 ((parse_term "!f m n. m <= n ==> sum(m..n) f = f(m) + sum(m+1..n) f"),
  vSIMP_TAC[vGSYM vNUMSEG_LREC; vSUM_CLAUSES; vFINITE_NUMSEG; vIN_NUMSEG] ---->
  vARITH_TAC);;

let vSUM_CLAUSES_RIGHT = try Cache.lookup_thm "SUM_CLAUSES_RIGHT" with _ ->  prove
 ((parse_term "!f m n. 0 < n /\\ m <= n ==> sum(m..n) f = sum(m..n-1) f + f(n)"),
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vSIMP_TAC[vLT_REFL; vSUM_CLAUSES_NUMSEG; vSUC_SUB1]);;

let vSUM_PAIR = try Cache.lookup_thm "SUM_PAIR" with _ ->  prove
 ((parse_term "!f m n. sum(2*m..2*n+1) f = sum(m..n) (\\i. f(2*i) + f(2*i+1))"),
  vMP_TAC(vMATCH_MP vITERATE_PAIR vMONOIDAL_REAL_ADD) ---->
  vREWRITE_TAC[sum; vNEUTRAL_REAL_ADD]);;

let vSUM_REFLECT = try Cache.lookup_thm "SUM_REFLECT" with _ ->  prove
 ((parse_term "!x m n. sum(m..n) x = if n < m then &0 else sum(0..n-m) (\\i. x(n - i))"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[sum] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vMATCH_MP vITERATE_REFLECT vMONOIDAL_REAL_ADD] ---->
  vREWRITE_TAC[vNEUTRAL_REAL_ADD]);;

let vREAL_OF_NUM_SUM_NUMSEG = try Cache.lookup_thm "REAL_OF_NUM_SUM_NUMSEG" with _ ->  prove
 ((parse_term "!f m n. (&(nsum(m..n) f) = sum (m..n) (\\i. &(f i)))"),
  vSIMP_TAC[vREAL_OF_NUM_SUM; vFINITE_NUMSEG]);;

(* ------------------------------------------------------------------------- *)
(* Partial summation and other theorems specific to number segments.         *)
(* ------------------------------------------------------------------------- *)

let vSUM_PARTIAL_SUC = try Cache.lookup_thm "SUM_PARTIAL_SUC" with _ ->  prove
 ((parse_term "!f g m n.\n        sum (m..n) (\\k. f(k) * (g(k + 1) - g(k))) =\n            if m <= n then f(n + 1) * g(n + 1) - f(m) * g(m) -\n                           sum (m..n) (\\k. g(k + 1) * (f(k + 1) - f(k)))\n            else &0"),
  vGEN_TAC ----> vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vCOND_CASES_TAC ----> vASM_SIMP_TAC[vSUM_TRIV_NUMSEG; vGSYM vNOT_LE] ---->
  vASM_REWRITE_TAC[vSUM_CLAUSES_NUMSEG] ++-->
   [vCOND_CASES_TAC ----> vASM_SIMP_TAC[] ++--> [vREAL_ARITH_TAC; vASM_ARITH_TAC];
    vALL_TAC] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vLE]) ---->
  vDISCH_THEN(vDISJ_CASES_THEN2 vSUBST_ALL_TAC vASSUME_TAC) ---->
  vASM_SIMP_TAC[vGSYM vNOT_LT; vSUM_TRIV_NUMSEG; vARITH_RULE (parse_term "n < SUC n")] ---->
  vASM_SIMP_TAC[vGSYM vADD1; vADD_CLAUSES] ----> vREAL_ARITH_TAC);;

let vSUM_PARTIAL_PRE = try Cache.lookup_thm "SUM_PARTIAL_PRE" with _ ->  prove
 ((parse_term "!f g m n.\n        sum (m..n) (\\k. f(k) * (g(k) - g(k - 1))) =\n            if m <= n then f(n + 1) * g(n) - f(m) * g(m - 1) -\n                           sum (m..n) (\\k. g k * (f(k + 1) - f(k)))\n            else &0"),
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vISPECL [(parse_term "f:num->real"); (parse_term "\\k. (g:num->real)(k - 1)");
                 (parse_term "m:num"); (parse_term "n:num")] vSUM_PARTIAL_SUC) ---->
  vREWRITE_TAC[vADD_SUB] ----> vDISCH_THEN vSUBST1_TAC ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[]);;

let vSUM_DIFFS = try Cache.lookup_thm "SUM_DIFFS" with _ ->  prove
 ((parse_term "!m n. sum(m..n) (\\k. f(k) - f(k + 1)) =\n          if m <= n then f(m) - f(n + 1) else &0"),
  vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "a - b = -- &1 * (b - a)")] ---->
  vONCE_REWRITE_TAC[vSUM_PARTIAL_SUC] ---->
  vREWRITE_TAC[vREAL_SUB_REFL; vREAL_MUL_RZERO; vSUM_0] ---->
  vREAL_ARITH_TAC);;

let vSUM_DIFFS_ALT = try Cache.lookup_thm "SUM_DIFFS_ALT" with _ ->  prove
 ((parse_term "!m n. sum(m..n) (\\k. f(k + 1) - f(k)) =\n          if m <= n then f(n + 1) - f(m) else &0"),
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_NEG_SUB] ---->
  vSIMP_TAC[vSUM_NEG; vSUM_DIFFS] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_NEG_SUB; vREAL_NEG_0]);;

let vSUM_COMBINE_R = try Cache.lookup_thm "SUM_COMBINE_R" with _ ->  prove
 ((parse_term "!f m n p. m <= n + 1 /\\ n <= p\n             ==> sum(m..n) f + sum(n+1..p) f = sum(m..p) f"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_UNION_EQ ---->
  vREWRITE_TAC[vFINITE_NUMSEG; vEXTENSION; vIN_INTER; vIN_UNION; vNOT_IN_EMPTY;
              vIN_NUMSEG] ---->
  vASM_ARITH_TAC);;

let vSUM_COMBINE_L = try Cache.lookup_thm "SUM_COMBINE_L" with _ ->  prove
 ((parse_term "!f m n p. 0 < n /\\ m <= n /\\ n <= p + 1\n             ==> sum(m..n-1) f + sum(n..p) f = sum(m..p) f"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_UNION_EQ ---->
  vREWRITE_TAC[vFINITE_NUMSEG; vEXTENSION; vIN_INTER; vIN_UNION; vNOT_IN_EMPTY;
              vIN_NUMSEG] ---->
  vASM_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Extend congruences to deal with sum. Note that we must have the eta       *)
(* redex or we'll get a loop since f(x) will lambda-reduce recursively.      *)
(* ------------------------------------------------------------------------- *)

let th = prove
 ((parse_term "(!f g s.   (!x. x IN s ==> f(x) = g(x))\n              ==> sum s (\\i. f(i)) = sum s g) /\\\n   (!f g a b. (!i. a <= i /\\ i <= b ==> f(i) = g(i))\n              ==> sum(a..b) (\\i. f(i)) = sum(a..b) g) /\\\n   (!f g p.   (!x. p x ==> f x = g x)\n              ==> sum {y | p y} (\\i. f(i)) = sum {y | p y} g)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vSUM_EQ ---->
  vASM_SIMP_TAC[vIN_ELIM_THM; vIN_NUMSEG]) in
  extend_basic_congs (map vSPEC_ALL (vCONJUNCTS th));;

(* ------------------------------------------------------------------------- *)
(* Expand "sum (m..n) f" where m and n are numerals.                         *)
(* ------------------------------------------------------------------------- *)

let vEXPAND_SUM_CONV =
  let [@warning "-8"] [pth_0; pth_1; pth_2] = (vCONJUNCTS -| prove)
   ((parse_term "(n < m ==> sum(m..n) f = &0) /\\\n     sum(m..m) f = f m /\\\n     (m <= n ==> sum (m..n) f = f m + sum (m + 1..n) f)"),
    vREWRITE_TAC[vSUM_CLAUSES_LEFT; vSUM_SING_NUMSEG; vSUM_TRIV_NUMSEG])
  and ns_tm = (parse_term "..") and f_tm = (parse_term "f:num->real")
  and m_tm = (parse_term "m:num") and n_tm = (parse_term "n:num") in
  let rec conv tm =
    let smn,ftm = dest_comb tm in
    let s,mn = dest_comb smn in
    if not(is_const s && fst(dest_const s) = "sum")
    then failwith "EXPAND_SUM_CONV" else
    let mtm,ntm = dest_binop ns_tm mn in
    let m = dest_numeral mtm and n = dest_numeral ntm in
    if n < m then
      let th1 = vINST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_0 in
      vMP th1 (vEQT_ELIM(vNUM_LT_CONV(lhand(concl th1))))
    else if n = m then vCONV_RULE (vRAND_CONV(vTRY_CONV vBETA_CONV))
                                 (vINST [ftm,f_tm; mtm,m_tm] pth_1)
    else
      let th1 = vINST [ftm,f_tm; mtm,m_tm; ntm,n_tm] pth_2 in
      let th2 = vMP th1 (vEQT_ELIM(vNUM_LE_CONV(lhand(concl th1)))) in
      vCONV_RULE (vRAND_CONV(vCOMB2_CONV (vRAND_CONV(vTRY_CONV vBETA_CONV))
       (vLAND_CONV(vLAND_CONV vNUM_ADD_CONV) +---> conv))) th2 in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Some special algebraic rearrangements.                                    *)
(* ------------------------------------------------------------------------- *)

let vREAL_SUB_POW = try Cache.lookup_thm "REAL_SUB_POW" with _ ->  prove
 ((parse_term "!x y n.\n        1 <= n ==> x pow n - y pow n =\n                   (x - y) * sum(0..n-1) (\\i. x pow i * y pow (n - 1 - i))"),
  vREWRITE_TAC[vGSYM vSUM_LMUL] ---->
  vREWRITE_TAC[vREAL_ARITH
   (parse_term "(x - y) * (a * b):real = (x * a) * b - a * (y * b)")] ---->
  vSIMP_TAC[vGSYM real_pow; vADD1; vARITH_RULE
    (parse_term "1 <= n /\\ x <= n - 1\n     ==> n - 1 - x = n - (x + 1) /\\ SUC(n - 1 - x) = n - x")] ---->
  vREWRITE_TAC[vSUM_DIFFS_ALT; vLE_0] ---->
  vSIMP_TAC[vSUB_0; vSUB_ADD; vSUB_REFL; real_pow; vREAL_MUL_LID; vREAL_MUL_RID]);;

let vREAL_SUB_POW_R1 = try Cache.lookup_thm "REAL_SUB_POW_R1" with _ ->  prove
 ((parse_term "!x n. 1 <= n ==> x pow n - &1 = (x - &1) * sum(0..n-1) (\\i. x pow i)"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [(parse_term "x:real"); (parse_term "&1")] -| vMATCH_MP vREAL_SUB_POW) ---->
  vREWRITE_TAC[vREAL_POW_ONE; vREAL_MUL_RID]);;

let vREAL_SUB_POW_L1 = try Cache.lookup_thm "REAL_SUB_POW_L1" with _ ->  prove
 ((parse_term "!x n. 1 <= n ==> &1 - x pow n = (&1 - x) * sum(0..n-1) (\\i. x pow i)"),
  vONCE_REWRITE_TAC[vGSYM vREAL_NEG_SUB] ---->
  vSIMP_TAC[vREAL_SUB_POW_R1] ----> vREWRITE_TAC[vREAL_MUL_LNEG]);;

(* ------------------------------------------------------------------------- *)
(* Some useful facts about real polynomial functions.                        *)
(* ------------------------------------------------------------------------- *)

let vREAL_SUB_POLYFUN = try Cache.lookup_thm "REAL_SUB_POLYFUN" with _ ->  prove
 ((parse_term "!a x y n.\n    1 <= n\n    ==> sum(0..n) (\\i. a i * x pow i) - sum(0..n) (\\i. a i * y pow i) =\n        (x - y) *\n        sum(0..n-1) (\\j. sum(j+1..n) (\\i. a i * y pow (i - j - 1)) * x pow j)"),
  vREPEAT vSTRIP_TAC ---->
  vREWRITE_TAC[vGSYM vSUM_SUB_NUMSEG; vGSYM vREAL_SUB_LDISTRIB] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vMATCH_MP vSUM_CLAUSES_LEFT (vSPEC_ALL vLE_0)] ---->
  vREWRITE_TAC[vREAL_SUB_REFL; real_pow; vREAL_MUL_RZERO; vREAL_ADD_LID] ---->
  vSIMP_TAC[vREAL_SUB_POW; vADD_CLAUSES] ---->
  vONCE_REWRITE_TAC[vREAL_ARITH (parse_term "a * x * s:real = x * a * s")] ---->
  vREWRITE_TAC[vSUM_LMUL] ----> vAP_TERM_TAC ---->
  vSIMP_TAC[vGSYM vSUM_LMUL; vGSYM vSUM_RMUL; vSUM_SUM_PRODUCT; vFINITE_NUMSEG] ---->
  vMATCH_MP_TAC vSUM_EQ_GENERAL_INVERSES ---->
  vREPEAT(vEXISTS_TAC (parse_term "\\(x:num,y:num). (y,x)")) ---->
  vREWRITE_TAC[vFORALL_IN_GSPEC; vIN_ELIM_PAIR_THM; vIN_NUMSEG] ---->
  vREWRITE_TAC[vARITH_RULE (parse_term "a - b - c:num = a - (b + c)"); vADD_SYM] ---->
  vREWRITE_TAC[vREAL_MUL_AC] ----> vARITH_TAC);;

let vREAL_SUB_POLYFUN_ALT = try Cache.lookup_thm "REAL_SUB_POLYFUN_ALT" with _ ->  prove
 ((parse_term "!a x y n.\n    1 <= n\n    ==> sum(0..n) (\\i. a i * x pow i) - sum(0..n) (\\i. a i * y pow i) =\n        (x - y) *\n        sum(0..n-1) (\\j. sum(0..n-j-1) (\\k. a(j+k+1) * y pow k) * x pow j)"),
  vREPEAT vSTRIP_TAC ----> vASM_SIMP_TAC[vREAL_SUB_POLYFUN] ----> vAP_TERM_TAC ---->
  vMATCH_MP_TAC vSUM_EQ_NUMSEG ----> vX_GEN_TAC (parse_term "j:num") ----> vREPEAT vSTRIP_TAC ---->
  vREWRITE_TAC[] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vMATCH_MP_TAC vSUM_EQ_GENERAL_INVERSES ---->
  vMAP_EVERY vEXISTS_TAC
   [(parse_term "\\i. i - (j + 1)"); (parse_term "\\k. j + k + 1")] ---->
  vREWRITE_TAC[vIN_NUMSEG] ----> vREPEAT vSTRIP_TAC ---->
  vTRY(vBINOP_TAC ----> vAP_TERM_TAC) ----> vASM_ARITH_TAC);;

let vREAL_POLYFUN_ROOTBOUND = try Cache.lookup_thm "REAL_POLYFUN_ROOTBOUND" with _ ->  prove
 ((parse_term "!n c. ~(!i. i IN 0..n ==> c i = &0)\n         ==> FINITE {x | sum(0..n) (\\i. c i * x pow i) = &0} /\\\n             CARD {x | sum(0..n) (\\i. c i * x pow i) = &0} <= n"),
  vREWRITE_TAC[vNOT_FORALL_THM; vNOT_IMP] ----> vINDUCT_TAC ++-->
   [vREWRITE_TAC[vNUMSEG_SING; vIN_SING; vUNWIND_THM2; vSUM_CLAUSES_NUMSEG] ---->
    vSIMP_TAC[real_pow; vREAL_MUL_RID; vEMPTY_GSPEC; vCARD_CLAUSES; vFINITE_EMPTY;
             vLE_REFL];
    vX_GEN_TAC (parse_term "c:num->real") ----> vREWRITE_TAC[vIN_NUMSEG] ---->
    vDISCH_TAC ----> vASM_CASES_TAC (parse_term "(c:num->real) (SUC n) = &0") ++-->
     [vASM_SIMP_TAC[vSUM_CLAUSES_NUMSEG; vLE_0; vREAL_MUL_LZERO; vREAL_ADD_RID] ---->
      vREWRITE_TAC[vLE; vLEFT_OR_DISTRIB] ----> vDISJ2_TAC ---->
      vFIRST_X_ASSUM vMATCH_MP_TAC ----> vASM_MESON_TAC[vIN_NUMSEG; vLE];
      vASM_CASES_TAC (parse_term "{x | sum (0..SUC n) (\\i. c i * x pow i) = &0} = {}") ---->
      vASM_REWRITE_TAC[vFINITE_RULES; vCARD_CLAUSES; vLE_0] ---->
      vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vGSYM vMEMBER_NOT_EMPTY]) ---->
      vREWRITE_TAC[vIN_ELIM_THM; vLEFT_IMP_EXISTS_THM] ---->
      vX_GEN_TAC (parse_term "r:real") ----> vDISCH_TAC ---->
      vMP_TAC(vGEN (parse_term "x:real") (vISPECL [(parse_term "c:num->real"); (parse_term "x:real"); (parse_term "r:real"); (parse_term "SUC n")]
        vREAL_SUB_POLYFUN)) ---->
      vASM_REWRITE_TAC[vARITH_RULE (parse_term "1 <= SUC n"); vREAL_SUB_RZERO] ---->
      vDISCH_THEN(fun th -> vREWRITE_TAC[th; vREAL_ENTIRE; vREAL_SUB_0]) ---->
      vREWRITE_TAC[vSET_RULE (parse_term "{x | x = c \\/ P x} = c INSERT {x | P x}")] ---->
      vMATCH_MP_TAC(vMESON[vFINITE_INSERT; vCARD_CLAUSES;
                         vARITH_RULE (parse_term "x <= n ==> SUC x <= SUC n /\\ x <= SUC n")]
        (parse_term "FINITE s /\\ CARD s <= n\n         ==> FINITE(r INSERT s) /\\ CARD(r INSERT s) <= SUC n")) ---->
      vREWRITE_TAC[vSUC_SUB1] ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
      vEXISTS_TAC (parse_term "n:num") ----> vREWRITE_TAC[vIN_NUMSEG; vADD1; vLE_REFL; vLE_0] ---->
      vREWRITE_TAC[vSUM_SING_NUMSEG; vARITH_RULE (parse_term "(n + 1) - n - 1 = 0")] ---->
      vASM_REWRITE_TAC[vGSYM vADD1; real_pow; vREAL_MUL_RID]]]);;

let vREAL_POLYFUN_FINITE_ROOTS = try Cache.lookup_thm "REAL_POLYFUN_FINITE_ROOTS" with _ ->  prove
 ((parse_term "!n c. FINITE {x | sum(0..n) (\\i. c i * x pow i) = &0} <=>\n         ?i. i IN 0..n /\\ ~(c i = &0)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vTAUT (parse_term "a /\\ ~b <=> ~(a ==> b)")] ---->
  vREWRITE_TAC[vGSYM vNOT_FORALL_THM] ----> vEQ_TAC ---->
  vSIMP_TAC[vREAL_POLYFUN_ROOTBOUND] ---->
  vONCE_REWRITE_TAC[vGSYM vCONTRAPOS_THM] ---->
  vSIMP_TAC[vREAL_MUL_LZERO; vSUM_0] ---->
  vREWRITE_TAC[vSET_RULE (parse_term "{x | T} = (:real)"); real_INFINITE; vGSYM vINFINITE]);;

let vREAL_POLYFUN_EQ_0 = try Cache.lookup_thm "REAL_POLYFUN_EQ_0" with _ ->  prove
 ((parse_term "!n c. (!x. sum(0..n) (\\i. c i * x pow i) = &0) <=>\n         (!i. i IN 0..n ==> c i = &0)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vGEN_REWRITE_TAC vI [vTAUT (parse_term "p <=> ~ ~p")] ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP
     vREAL_POLYFUN_ROOTBOUND) ---->
    vASM_REWRITE_TAC[real_INFINITE; vGSYM vINFINITE; vDE_MORGAN_THM;
                    vSET_RULE (parse_term "{x | T} = (:real)")];
    vASM_SIMP_TAC[vIN_NUMSEG; vLE_0; vREAL_MUL_LZERO; vSUM_0]]);;

let vREAL_POLYFUN_EQ_CONST = try Cache.lookup_thm "REAL_POLYFUN_EQ_CONST" with _ ->  prove
 ((parse_term "!n c k. (!x. sum(0..n) (\\i. c i * x pow i) = k) <=>\n           c 0 = k /\\ (!i. i IN 1..n ==> c i = &0)"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC vEQ_TRANS ----> vEXISTS_TAC
   (parse_term "!x. sum(0..n) (\\i. (if i = 0 then c 0 - k else c i) * x pow i) = &0") ---->
  vCONJ_TAC ++-->
   [vSIMP_TAC[vSUM_CLAUSES_LEFT; vLE_0; real_pow; vREAL_MUL_RID] ---->
    vREWRITE_TAC[vREAL_ARITH (parse_term "(c - k) + s = &0 <=> c + s = k")] ---->
    vAP_TERM_TAC ----> vABS_TAC ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
    vAP_TERM_TAC ----> vMATCH_MP_TAC vSUM_EQ ----> vGEN_TAC ---->
    vREWRITE_TAC[vIN_NUMSEG] ---->
    vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vARITH];
    vREWRITE_TAC[vREAL_POLYFUN_EQ_0; vIN_NUMSEG; vLE_0] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vMESON[]
     (parse_term "(!n. P n) <=> P 0 /\\ (!n. ~(n = 0) ==> P n)")] ---->
    vSIMP_TAC[vLE_0; vREAL_SUB_0] ----> vMESON_TAC[vLE_1]]);;

(* ------------------------------------------------------------------------- *)
(* A general notion of polynomial function.                                  *)
(* ------------------------------------------------------------------------- *)

let polynomial_function = new_definition
 (parse_term "polynomial_function p <=> ?m c. !x. p x = sum(0..m) (\\i. c i * x pow i)");;

let vPOLYNOMIAL_FUNCTION_CONST = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_CONST" with _ ->  prove
 ((parse_term "!c. polynomial_function (\\x. c)"),
  vGEN_TAC ----> vREWRITE_TAC[polynomial_function] ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "0"); (parse_term "(\\i. c):num->real")] ---->
  vREWRITE_TAC[vSUM_SING_NUMSEG; real_pow; vREAL_MUL_RID]);;

let vPOLYNOMIAL_FUNCTION_ID = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_ID" with _ ->  prove
 ((parse_term "polynomial_function (\\x. x)"),
  vREWRITE_TAC[polynomial_function] ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "SUC 0"); (parse_term "\\i. if i = 1 then &1 else &0")] ---->
  vREWRITE_TAC[vSUM_CLAUSES_NUMSEG; vLE_0; vARITH] ----> vREAL_ARITH_TAC);;

let vPOLYNOMIAL_FUNCTION_I = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_I" with _ ->  prove
 ((parse_term "polynomial_function I"),
  vREWRITE_TAC[vI_DEF; vPOLYNOMIAL_FUNCTION_ID]);;

let vPOLYNOMIAL_FUNCTION_ADD = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_ADD" with _ ->  prove
 ((parse_term "!p q. polynomial_function p /\\ polynomial_function q\n         ==> polynomial_function (\\x. p x + q x)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vIMP_CONJ; polynomial_function; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC  [(parse_term "m:num"); (parse_term "a:num->real")] ----> vSTRIP_TAC ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "n:num"); (parse_term "b:num->real")] ----> vSTRIP_TAC ---->
  vASM_REWRITE_TAC[] ----> vEXISTS_TAC (parse_term "MAX m n") ----> vEXISTS_TAC
   (parse_term "\\i:num. (if i <= m then a i else &0) + (if i <= n then b i else &0)") ---->
  vGEN_TAC ----> vREWRITE_TAC[vREAL_ADD_RDISTRIB; vSUM_ADD_NUMSEG] ---->
  vREWRITE_TAC[vCOND_RAND; vCOND_RATOR; vREAL_MUL_LZERO] ---->
  vREWRITE_TAC[vGSYM vSUM_RESTRICT_SET] ----> vBINOP_TAC ---->
  vBINOP_TAC ----> vREWRITE_TAC[] ---->
  vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vIN_NUMSEG] ----> vARITH_TAC);;

let vPOLYNOMIAL_FUNCTION_LMUL = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_LMUL" with _ ->  prove
 ((parse_term "!p c. polynomial_function p ==> polynomial_function (\\x. c * p x)"),
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vIMP_CONJ; polynomial_function; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC  [(parse_term "n:num"); (parse_term "a:num->real")] ----> vSTRIP_TAC ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "n:num"); (parse_term "\\i. c * (a:num->real) i")] ---->
  vASM_REWRITE_TAC[vSUM_LMUL; vGSYM vREAL_MUL_ASSOC]);;

let vPOLYNOMIAL_FUNCTION_RMUL = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_RMUL" with _ ->  prove
 ((parse_term "!p c. polynomial_function p ==> polynomial_function (\\x. p x * c)"),
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vPOLYNOMIAL_FUNCTION_LMUL]);;

let vPOLYNOMIAL_FUNCTION_NEG = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_NEG" with _ ->  prove
 ((parse_term "!p. polynomial_function(\\x. --(p x)) <=> polynomial_function p"),
  vGEN_TAC ----> vEQ_TAC ---->
  vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "--(&1)") -| vMATCH_MP vPOLYNOMIAL_FUNCTION_LMUL) ---->
  vREWRITE_TAC[vREAL_MUL_LNEG; vREAL_MUL_LID; vETA_AX; vREAL_NEG_NEG]);;

let vPOLYNOMIAL_FUNCTION_SUB = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_SUB" with _ ->  prove
 ((parse_term "!p q. polynomial_function p /\\ polynomial_function q\n         ==> polynomial_function (\\x. p x - q x)"),
  vSIMP_TAC[real_sub; vPOLYNOMIAL_FUNCTION_NEG; vPOLYNOMIAL_FUNCTION_ADD]);;

let vPOLYNOMIAL_FUNCTION_MUL = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_MUL" with _ ->  prove
 ((parse_term "!p q. polynomial_function p /\\ polynomial_function q\n         ==> polynomial_function (\\x. p x * q x)"),
  vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vGEN_TAC ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC (vBINDER_CONV -| vLAND_CONV) [polynomial_function] ---->
  vSIMP_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(!q m c. P q m c) <=> (!m c q. P q m c)")] ---->
  vONCE_REWRITE_TAC[vGSYM vFUN_EQ_THM] ---->
  vREWRITE_TAC[vLEFT_FORALL_IMP_THM; vEXISTS_REFL] ---->
  vINDUCT_TAC ---->
  vASM_SIMP_TAC[vSUM_SING_NUMSEG; real_pow; vPOLYNOMIAL_FUNCTION_RMUL] ---->
  vX_GEN_TAC (parse_term "c:num->real") ----> vSIMP_TAC[vSUM_CLAUSES_LEFT; vLE_0; vADD1] ---->
  vREWRITE_TAC[vREAL_ADD_LDISTRIB; real_pow] ---->
  vMATCH_MP_TAC vPOLYNOMIAL_FUNCTION_ADD ---->
  vASM_SIMP_TAC[vPOLYNOMIAL_FUNCTION_RMUL] ---->
  vREWRITE_TAC[vSPEC (parse_term "1") vSUM_OFFSET] ---->
  vREWRITE_TAC[vREAL_POW_ADD; vREAL_POW_1; vREAL_MUL_ASSOC; vSUM_RMUL] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "\\i. (c:num->real)(i + 1)")) ---->
  vABBREV_TAC (parse_term "q = \\x. p x * sum (0..m) (\\i. c (i + 1) * x pow i)") ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vFUN_EQ_THM]) ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[polynomial_function; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "n:num"); (parse_term "a:num->real")] ----> vSTRIP_TAC ---->
  vEXISTS_TAC (parse_term "n + 1") ---->
  vEXISTS_TAC (parse_term "\\i. if i = 0 then &0 else (a:num->real)(i - 1)") ---->
  vSIMP_TAC[vSUM_CLAUSES_LEFT; vLE_0] ---->
  vASM_REWRITE_TAC[vSPEC (parse_term "1") vSUM_OFFSET; vADD_EQ_0; vARITH_EQ; vADD_SUB] ---->
  vREWRITE_TAC[vREAL_POW_ADD; vREAL_MUL_ASSOC; vSUM_RMUL] ----> vREAL_ARITH_TAC);;

let vPOLYNOMIAL_FUNCTION_SUM = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_SUM" with _ ->  prove
 ((parse_term "!s:A->bool p.\n        FINITE s /\\ (!i. i IN s ==> polynomial_function(\\x. p x i))\n        ==> polynomial_function (\\x. sum s (p x))"),
  vREWRITE_TAC[vIMP_CONJ; vRIGHT_FORALL_IMP_THM] ---->
  vMATCH_MP_TAC vFINITE_INDUCT_STRONG ---->
  vSIMP_TAC[vSUM_CLAUSES; vPOLYNOMIAL_FUNCTION_CONST] ---->
  vSIMP_TAC[vFORALL_IN_INSERT; vPOLYNOMIAL_FUNCTION_ADD]);;

let vPOLYNOMIAL_FUNCTION_POW = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_POW" with _ ->  prove
 ((parse_term "!p n. polynomial_function p ==> polynomial_function (\\x. p x pow n)"),
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ----> vGEN_TAC ----> vDISCH_TAC ---->
  vINDUCT_TAC ---->
  vASM_SIMP_TAC[real_pow; vPOLYNOMIAL_FUNCTION_CONST; vPOLYNOMIAL_FUNCTION_MUL]);;

let vPOLYNOMIAL_FUNCTION_INDUCT = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_INDUCT" with _ ->  prove
 ((parse_term "!P. P (\\x. x) /\\ (!c. P (\\x. c)) /\\\n      (!p q. P p /\\ P q ==> P (\\x. p x + q x)) /\\\n      (!p q. P p /\\ P q ==> P (\\x. p x * q x))\n      ==> !p. polynomial_function p ==> P p"),
  vGEN_TAC ----> vSTRIP_TAC ---->
  vREWRITE_TAC[polynomial_function; vLEFT_IMP_EXISTS_THM] ---->
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(!q m c. P q m c) <=> (!m c q. P q m c)")] ---->
  vONCE_REWRITE_TAC[vGSYM vFUN_EQ_THM] ---->
  vSIMP_TAC[vLEFT_FORALL_IMP_THM; vEXISTS_REFL] ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vSUM_SING_NUMSEG; real_pow] ---->
  vGEN_TAC ----> vSIMP_TAC[vSUM_CLAUSES_LEFT; vADD1; vLE_0] ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[real_pow] ---->
  vREWRITE_TAC[vSPEC (parse_term "1") vSUM_OFFSET] ---->
  vREWRITE_TAC[vREAL_POW_ADD; vREAL_POW_1; vREAL_MUL_ASSOC; vSUM_RMUL] ---->
  vASM_SIMP_TAC[]);;

let vPOLYNOMIAL_FUNCTION_o = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_o" with _ ->  prove
 ((parse_term "!p q. polynomial_function p /\\ polynomial_function q\n         ==> polynomial_function (p o q)"),
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vREWRITE_TAC[vIMP_CONJ_ALT; vRIGHT_FORALL_IMP_THM] ---->
  vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vPOLYNOMIAL_FUNCTION_INDUCT ---->
  vSIMP_TAC[o_DEF; vPOLYNOMIAL_FUNCTION_ADD; vPOLYNOMIAL_FUNCTION_MUL] ---->
  vASM_REWRITE_TAC[vETA_AX; vPOLYNOMIAL_FUNCTION_CONST]);;

let vPOLYNOMIAL_FUNCTION_FINITE_ROOTS = try Cache.lookup_thm "POLYNOMIAL_FUNCTION_FINITE_ROOTS" with _ ->  prove
 ((parse_term "!p a. polynomial_function p\n         ==> (FINITE {x | p x = a} <=> ~(!x. p x = a))"),
  vONCE_REWRITE_TAC[vGSYM vREAL_SUB_0] ---->
  vSUBGOAL_THEN
   (parse_term "!p. polynomial_function p ==> (FINITE {x | p x = &0} <=> ~(!x. p x = &0))")
   (fun th ->
      vSIMP_TAC[th; vPOLYNOMIAL_FUNCTION_SUB; vPOLYNOMIAL_FUNCTION_CONST]) ---->
  vGEN_TAC ----> vREWRITE_TAC[polynomial_function] ---->
  vSTRIP_TAC ----> vEQ_TAC ----> vONCE_REWRITE_TAC[vGSYM vCONTRAPOS_THM] ++-->
   [vSIMP_TAC[vUNIV_GSPEC; vGSYM vINFINITE; real_INFINITE];
    vASM_REWRITE_TAC[vREAL_POLYFUN_FINITE_ROOTS] ---->
    vSIMP_TAC[vNOT_EXISTS_THM; vTAUT (parse_term "~(p /\\ ~q) <=> p ==> q")] ---->
    vREWRITE_TAC[vREAL_MUL_LZERO; vSUM_0]]);;

(* ------------------------------------------------------------------------- *)
(* Make natural numbers the default again.                                   *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;
