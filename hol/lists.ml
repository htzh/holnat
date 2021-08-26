(* ========================================================================= *)
(* Theory of lists, plus characters and strings as lists of characters.      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2014                         *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Preterm
open Parser
open Equal
open Boolean
open Tactics
open Simp
open Theorems
open Ind_defs
open Class
open Trivia
open Meson
open Pair
open Nums
open Recursion
open Arith
open Calc_num
open Ind_types

(* ------------------------------------------------------------------------- *)
(* Standard tactic for list induction using MATCH_MP_TAC list_INDUCT         *)
(* ------------------------------------------------------------------------- *)

let vLIST_INDUCT_TAC =
  let list_INDUCT = prove
   ((parse_term "!P:(A)list->bool. P [] /\\ (!h t. P t ==> P (CONS h t)) ==> !l. P l"),
    vMATCH_ACCEPT_TAC list_INDUCT) in
  vMATCH_MP_TAC list_INDUCT ---->
  vCONJ_TAC ++--> [vALL_TAC; vGEN_TAC ----> vGEN_TAC ----> vDISCH_TAC];;

(* ------------------------------------------------------------------------- *)
(* Basic definitions.                                                        *)
(* ------------------------------------------------------------------------- *)

let vHD = new_recursive_definition list_RECURSION
  (parse_term "HD(CONS (h:A) t) = h");;

let vTL = new_recursive_definition list_RECURSION
  (parse_term "TL(CONS (h:A) t) = t");;

let vAPPEND = new_recursive_definition list_RECURSION
  (parse_term "(!l:(A)list. APPEND [] l = l) /\\\n   (!h t l. APPEND (CONS h t) l = CONS h (APPEND t l))");;

let vREVERSE = new_recursive_definition list_RECURSION
  (parse_term "(REVERSE [] = []) /\\\n   (REVERSE (CONS (x:A) l) = APPEND (REVERSE l) [x])");;

let vLENGTH = new_recursive_definition list_RECURSION
  (parse_term "(LENGTH [] = 0) /\\\n   (!h:A. !t. LENGTH (CONS h t) = SUC (LENGTH t))");;

let vMAP = new_recursive_definition list_RECURSION
  (parse_term "(!f:A->B. MAP f NIL = NIL) /\\\n   (!f h t. MAP f (CONS h t) = CONS (f h) (MAP f t))");;

let vLAST = new_recursive_definition list_RECURSION
  (parse_term "LAST (CONS (h:A) t) = if t = [] then h else LAST t");;

let vBUTLAST = new_recursive_definition list_RECURSION
 (parse_term "(BUTLAST [] = []) /\\\n  (BUTLAST (CONS h t) = if t = [] then [] else CONS h (BUTLAST t))");;

let vREPLICATE = new_recursive_definition num_RECURSION
  (parse_term "(REPLICATE 0 x = []) /\\\n   (REPLICATE (SUC n) x = CONS x (REPLICATE n x))");;

let vNULL = new_recursive_definition list_RECURSION
  (parse_term "(NULL [] = T) /\\\n   (NULL (CONS h t) = F)");;

let vALL = new_recursive_definition list_RECURSION
  (parse_term "(ALL P [] = T) /\\\n   (ALL P (CONS h t) <=> P h /\\ ALL P t)");;

let vEX = new_recursive_definition list_RECURSION
  (parse_term "(EX P [] = F) /\\\n   (EX P (CONS h t) <=> P h \\/ EX P t)");;

let vITLIST = new_recursive_definition list_RECURSION
  (parse_term "(ITLIST f [] b = b) /\\\n   (ITLIST f (CONS h t) b = f h (ITLIST f t b))");;

let vMEM = new_recursive_definition list_RECURSION
  (parse_term "(MEM x [] <=> F) /\\\n   (MEM x (CONS h t) <=> (x = h) \\/ MEM x t)");;

let vALL2_DEF = new_recursive_definition list_RECURSION
  (parse_term "(ALL2 P [] l2 <=> (l2 = [])) /\\\n   (ALL2 P (CONS h1 t1) l2 <=>\n        if l2 = [] then F\n        else P h1 (HD l2) /\\ ALL2 P t1 (TL l2))");;

let vALL2 = try Cache.lookup_thm "ALL2" with _ ->  prove
 ((parse_term "(ALL2 P [] [] <=> T) /\\\n   (ALL2 P (CONS h1 t1) [] <=> F) /\\\n   (ALL2 P [] (CONS h2 t2) <=> F) /\\\n   (ALL2 P (CONS h1 t1) (CONS h2 t2) <=> P h1 h2 /\\ ALL2 P t1 t2)"),
  vREWRITE_TAC[distinctness "list"; vALL2_DEF; vHD; vTL]);;

let vMAP2_DEF = new_recursive_definition list_RECURSION
  (parse_term "(MAP2 f [] l = []) /\\\n   (MAP2 f (CONS h1 t1) l = CONS (f h1 (HD l)) (MAP2 f t1 (TL l)))");;

let vMAP2 = try Cache.lookup_thm "MAP2" with _ ->  prove
 ((parse_term "(MAP2 f [] [] = []) /\\\n   (MAP2 f (CONS h1 t1) (CONS h2 t2) = CONS (f h1 h2) (MAP2 f t1 t2))"),
  vREWRITE_TAC[vMAP2_DEF; vHD; vTL]);;

let vEL = new_recursive_definition num_RECURSION
  (parse_term "(EL 0 l = HD l) /\\\n   (EL (SUC n) l = EL n (TL l))");;

let vFILTER = new_recursive_definition list_RECURSION
  (parse_term "(FILTER P [] = []) /\\\n   (FILTER P (CONS h t) = if P h then CONS h (FILTER P t) else FILTER P t)");;

let vASSOC = new_recursive_definition list_RECURSION
  (parse_term "ASSOC a (CONS h t) = if FST h = a then SND h else ASSOC a t");;

let vITLIST2_DEF = new_recursive_definition list_RECURSION
  (parse_term "(ITLIST2 f [] l2 b = b) /\\\n   (ITLIST2 f (CONS h1 t1) l2 b = f h1 (HD l2) (ITLIST2 f t1 (TL l2) b))");;

let vITLIST2 = try Cache.lookup_thm "ITLIST2" with _ ->  prove
 ((parse_term "(ITLIST2 f [] [] b = b) /\\\n   (ITLIST2 f (CONS h1 t1) (CONS h2 t2) b = f h1 h2 (ITLIST2 f t1 t2 b))"),
  vREWRITE_TAC[vITLIST2_DEF; vHD; vTL]);;

let vZIP_DEF = new_recursive_definition list_RECURSION
  (parse_term "(ZIP [] l2 = []) /\\\n   (ZIP (CONS h1 t1) l2 = CONS (h1,HD l2) (ZIP t1 (TL l2)))");;

let vZIP = try Cache.lookup_thm "ZIP" with _ ->  prove
 ((parse_term "(ZIP [] [] = []) /\\\n   (ZIP (CONS h1 t1) (CONS h2 t2) = CONS (h1,h2) (ZIP t1 t2))"),
  vREWRITE_TAC[vZIP_DEF; vHD; vTL]);;

let vALLPAIRS = new_recursive_definition list_RECURSION
  (parse_term "(ALLPAIRS f [] l <=> T) /\\\n   (ALLPAIRS f (CONS h t) l <=> ALL (f h) l /\\ ALLPAIRS f t l)");;

let vPAIRWISE = new_recursive_definition list_RECURSION
  (parse_term "(PAIRWISE (r:A->A->bool) [] <=> T) /\\\n   (PAIRWISE (r:A->A->bool) (CONS h t) <=> ALL (r h) t /\\ PAIRWISE r t)");;

let list_of_seq = new_recursive_definition num_RECURSION
 (parse_term "list_of_seq (s:num->A) 0 = [] /\\\n  list_of_seq s (SUC n) = APPEND (list_of_seq s n) [s n]");;

(* ------------------------------------------------------------------------- *)
(* Various trivial theorems.                                                 *)
(* ------------------------------------------------------------------------- *)

let vNOT_CONS_NIL = try Cache.lookup_thm "NOT_CONS_NIL" with _ ->  prove
 ((parse_term "!(h:A) t. ~(CONS h t = [])"),
  vREWRITE_TAC[distinctness "list"]);;

let vLAST_CLAUSES = try Cache.lookup_thm "LAST_CLAUSES" with _ ->  prove
 ((parse_term "(LAST [h:A] = h) /\\\n   (LAST (CONS h (CONS k t)) = LAST (CONS k t))"),
  vREWRITE_TAC[vLAST; vNOT_CONS_NIL]);;

let vAPPEND_NIL = try Cache.lookup_thm "APPEND_NIL" with _ ->  prove
 ((parse_term "!l:A list. APPEND l [] = l"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vAPPEND]);;

let vAPPEND_ASSOC = try Cache.lookup_thm "APPEND_ASSOC" with _ ->  prove
 ((parse_term "!(l:A list) m n. APPEND l (APPEND m n) = APPEND (APPEND l m) n"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vAPPEND]);;

let vREVERSE_APPEND = try Cache.lookup_thm "REVERSE_APPEND" with _ ->  prove
 ((parse_term "!(l:A list) m. REVERSE (APPEND l m) = APPEND (REVERSE m) (REVERSE l)"),
  vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vAPPEND; vREVERSE; vAPPEND_NIL; vAPPEND_ASSOC]);;

let vREVERSE_REVERSE = try Cache.lookup_thm "REVERSE_REVERSE" with _ ->  prove
 ((parse_term "!l:A list. REVERSE(REVERSE l) = l"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vREVERSE; vREVERSE_APPEND; vAPPEND]);;

let vREVERSE_EQ_EMPTY = try Cache.lookup_thm "REVERSE_EQ_EMPTY" with _ ->  prove
 ((parse_term "!l:A list. REVERSE l = [] <=> l = []"),
  vMESON_TAC[vREVERSE_REVERSE; vREVERSE]);;

let vCONS_11 = try Cache.lookup_thm "CONS_11" with _ ->  prove
 ((parse_term "!(h1:A) h2 t1 t2. (CONS h1 t1 = CONS h2 t2) <=> (h1 = h2) /\\ (t1 = t2)"),
  vREWRITE_TAC[injectivity "list"]);;

let list_CASES = try Cache.lookup_thm "list_CASES" with _ ->  prove
 ((parse_term "!l:(A)list. (l = []) \\/ ?h t. l = CONS h t"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vCONS_11; vNOT_CONS_NIL] ---->
  vMESON_TAC[]);;

let vLIST_EQ = try Cache.lookup_thm "LIST_EQ" with _ ->  prove
 ((parse_term "!l1 l2:A list.\n        l1 = l2 <=>\n        LENGTH l1 = LENGTH l2 /\\ !n. n < LENGTH l2 ==> EL n l1 = EL n l2"),
  vREPEAT vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[vNOT_CONS_NIL; vCONS_11; vLENGTH; vCONJUNCT1 vLT; vNOT_SUC] ---->
  vASM_REWRITE_TAC[vSUC_INJ] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV)
   [vMESON[num_CASES] (parse_term "(!n. P n) <=> P 0 /\\ (!n. P(SUC n))")] ---->
  vREWRITE_TAC[vEL; vHD; vTL; vLT_0; vLT_SUC; vCONJ_ACI]);;

let vLENGTH_APPEND = try Cache.lookup_thm "LENGTH_APPEND" with _ ->  prove
 ((parse_term "!(l:A list) m. LENGTH(APPEND l m) = LENGTH l + LENGTH m"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vAPPEND; vLENGTH; vADD_CLAUSES]);;

let vMAP_APPEND = try Cache.lookup_thm "MAP_APPEND" with _ ->  prove
 ((parse_term "!f:A->B. !l1 l2. MAP f (APPEND l1 l2) = APPEND (MAP f l1) (MAP f l2)"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vMAP; vAPPEND]);;

let vLENGTH_MAP = try Cache.lookup_thm "LENGTH_MAP" with _ ->  prove
 ((parse_term "!l. !f:A->B. LENGTH (MAP f l) = LENGTH l"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vMAP; vLENGTH]);;

let vLENGTH_EQ_NIL = try Cache.lookup_thm "LENGTH_EQ_NIL" with _ ->  prove
 ((parse_term "!l:A list. (LENGTH l = 0) <=> (l = [])"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vLENGTH; vNOT_CONS_NIL; vNOT_SUC]);;

let vLENGTH_EQ_CONS = try Cache.lookup_thm "LENGTH_EQ_CONS" with _ ->  prove
 ((parse_term "!l n. (LENGTH l = SUC n) <=> ?h t. (l = CONS h t) /\\ (LENGTH t = n)"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vLENGTH; vNOT_SUC; vNOT_CONS_NIL] ---->
  vASM_REWRITE_TAC[vSUC_INJ; vCONS_11] ----> vMESON_TAC[]);;

let vLENGTH_REVERSE = try Cache.lookup_thm "LENGTH_REVERSE" with _ ->  prove
 ((parse_term "!l:A list. LENGTH(REVERSE l) = LENGTH l"),
  vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vREVERSE; vLENGTH_APPEND; vLENGTH] ---->
  vREWRITE_TAC[vADD_CLAUSES; vMULT_CLAUSES]);;

let vMAP_o = try Cache.lookup_thm "MAP_o" with _ ->  prove
 ((parse_term "!f:A->B. !g:B->C. !l. MAP (g o f) l = MAP g (MAP f l)"),
  vGEN_TAC ----> vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vMAP; o_THM]);;

let vMAP_EQ = try Cache.lookup_thm "MAP_EQ" with _ ->  prove
 ((parse_term "!f g l. ALL (\\x. f x = g x) l ==> (MAP f l = MAP g l)"),
  vGEN_TAC ----> vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[vMAP; vALL] ----> vASM_MESON_TAC[]);;

let vALL_IMP = try Cache.lookup_thm "ALL_IMP" with _ ->  prove
 ((parse_term "!P Q l. (!x. MEM x l /\\ P x ==> Q x) /\\ ALL P l ==> ALL Q l"),
  vGEN_TAC ----> vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[vMEM; vALL] ----> vASM_MESON_TAC[]);;

let vNOT_EX = try Cache.lookup_thm "NOT_EX" with _ ->  prove
 ((parse_term "!P l. ~(EX P l) <=> ALL (\\x. ~(P x)) l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vEX; vALL; vDE_MORGAN_THM]);;

let vNOT_ALL = try Cache.lookup_thm "NOT_ALL" with _ ->  prove
 ((parse_term "!P l. ~(ALL P l) <=> EX (\\x. ~(P x)) l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vEX; vALL; vDE_MORGAN_THM]);;

let vALL_MAP = try Cache.lookup_thm "ALL_MAP" with _ ->  prove
 ((parse_term "!P f l. ALL P (MAP f l) <=> ALL (P o f) l"),
  vGEN_TAC ----> vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vALL; vMAP; o_THM]);;

let vALL_EQ = try Cache.lookup_thm "ALL_EQ" with _ ->  prove
 ((parse_term "!l. ALL R l /\\ (!x. R x ==> (P x <=> Q x))\n       ==> (ALL P l <=> ALL Q l)"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vALL] ---->
  vSTRIP_TAC ----> vBINOP_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vASM_REWRITE_TAC[]);;

let vALL_T = try Cache.lookup_thm "ALL_T" with _ ->  prove
 ((parse_term "!l. ALL (\\x. T) l"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL]);;

let vMAP_EQ_ALL2 = try Cache.lookup_thm "MAP_EQ_ALL2" with _ ->  prove
 ((parse_term "!l m. ALL2 (\\x y. f x = f y) l m ==> (MAP f l = MAP f m)"),
  vREPEAT vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vMAP; vALL2; vCONS_11] ---->
  vASM_MESON_TAC[]);;

let vALL2_MAP = try Cache.lookup_thm "ALL2_MAP" with _ ->  prove
 ((parse_term "!P f l. ALL2 P (MAP f l) l <=> ALL (\\a. P (f a) a) l"),
  vGEN_TAC ----> vGEN_TAC ---->
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL2; vMAP; vALL]);;

let vMAP_EQ_DEGEN = try Cache.lookup_thm "MAP_EQ_DEGEN" with _ ->  prove
 ((parse_term "!l f. ALL (\\x. f(x) = x) l ==> (MAP f l = l)"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vALL; vMAP; vCONS_11] ---->
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]);;

let vALL2_AND_RIGHT = try Cache.lookup_thm "ALL2_AND_RIGHT" with _ ->  prove
 ((parse_term "!l m P Q. ALL2 (\\x y. P x /\\ Q x y) l m <=> ALL P l /\\ ALL2 Q l m"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL; vALL2] ---->
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL; vALL2] ---->
  vREWRITE_TAC[vCONJ_ACI]);;

let vITLIST_APPEND = try Cache.lookup_thm "ITLIST_APPEND" with _ ->  prove
 ((parse_term "!f a l1 l2. ITLIST f (APPEND l1 l2) a = ITLIST f l1 (ITLIST f l2 a)"),
  vGEN_TAC ----> vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vITLIST; vAPPEND]);;

let vITLIST_EXTRA = try Cache.lookup_thm "ITLIST_EXTRA" with _ ->  prove
 ((parse_term "!l. ITLIST f (APPEND l [a]) b = ITLIST f l (f a b)"),
  vREWRITE_TAC[vITLIST_APPEND; vITLIST]);;

let vALL_MP = try Cache.lookup_thm "ALL_MP" with _ ->  prove
 ((parse_term "!P Q l. ALL (\\x. P x ==> Q x) l /\\ ALL P l ==> ALL Q l"),
  vGEN_TAC ----> vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[vALL] ----> vASM_MESON_TAC[]);;

let vAND_ALL = try Cache.lookup_thm "AND_ALL" with _ ->  prove
 ((parse_term "!l. ALL P l /\\ ALL Q l <=> ALL (\\x. P x /\\ Q x) l"),
  vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ---->
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL; vCONJ_ACI]);;

let vEX_IMP = try Cache.lookup_thm "EX_IMP" with _ ->  prove
 ((parse_term "!P Q l. (!x. MEM x l /\\ P x ==> Q x) /\\ EX P l ==> EX Q l"),
  vGEN_TAC ----> vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[vMEM; vEX] ----> vASM_MESON_TAC[]);;

let vALL_MEM = try Cache.lookup_thm "ALL_MEM" with _ ->  prove
 ((parse_term "!P l. (!x. MEM x l ==> P x) <=> ALL P l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vREWRITE_TAC[vALL; vMEM] ---->
  vASM_MESON_TAC[]);;

let vLENGTH_REPLICATE = try Cache.lookup_thm "LENGTH_REPLICATE" with _ ->  prove
 ((parse_term "!n x. LENGTH(REPLICATE n x) = n"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vLENGTH; vREPLICATE]);;

let vMEM_REPLICATE = try Cache.lookup_thm "MEM_REPLICATE" with _ ->  prove
 ((parse_term "!n x y:A. MEM x (REPLICATE n y) <=> x = y /\\ ~(n = 0)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vMEM; vREPLICATE; vNOT_SUC] ---->
  vMESON_TAC[]);;

let vEX_MAP = try Cache.lookup_thm "EX_MAP" with _ ->  prove
 ((parse_term "!P f l. EX P (MAP f l) <=> EX (P o f) l"),
  vGEN_TAC ----> vGEN_TAC ---->
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vMAP; vEX; o_THM]);;

let vEXISTS_EX = try Cache.lookup_thm "EXISTS_EX" with _ ->  prove
 ((parse_term "!P l. (?x. EX (P x) l) <=> EX (\\s. ?x. P x s) l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vEX] ---->
  vASM_MESON_TAC[]);;

let vFORALL_ALL = try Cache.lookup_thm "FORALL_ALL" with _ ->  prove
 ((parse_term "!P l. (!x. ALL (P x) l) <=> ALL (\\s. !x. P x s) l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL] ---->
  vASM_MESON_TAC[]);;

let vMEM_APPEND = try Cache.lookup_thm "MEM_APPEND" with _ ->  prove
 ((parse_term "!x l1 l2. MEM x (APPEND l1 l2) <=> MEM x l1 \\/ MEM x l2"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vMEM; vAPPEND; vDISJ_ACI]);;

let vMEM_MAP = try Cache.lookup_thm "MEM_MAP" with _ ->  prove
 ((parse_term "!f y l. MEM y (MAP f l) <=> ?x. MEM x l /\\ (y = f x)"),
  vGEN_TAC ----> vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vMEM; vMAP] ----> vMESON_TAC[]);;

let vFILTER_APPEND = try Cache.lookup_thm "FILTER_APPEND" with _ ->  prove
 ((parse_term "!P l1 l2. FILTER P (APPEND l1 l2) = APPEND (FILTER P l1) (FILTER P l2)"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vFILTER; vAPPEND] ---->
  vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vAPPEND]);;

let vFILTER_MAP = try Cache.lookup_thm "FILTER_MAP" with _ ->  prove
 ((parse_term "!P f l. FILTER P (MAP f l) = MAP f (FILTER (P o f) l)"),
  vGEN_TAC ----> vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vMAP; vFILTER; o_THM] ----> vCOND_CASES_TAC ---->
  vREWRITE_TAC[vMAP]);;

let vMEM_FILTER = try Cache.lookup_thm "MEM_FILTER" with _ ->  prove
 ((parse_term "!P l x. MEM x (FILTER P l) <=> P x /\\ MEM x l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vMEM; vFILTER] ---->
  vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vMEM] ---->
  vASM_MESON_TAC[]);;

let vEX_MEM = try Cache.lookup_thm "EX_MEM" with _ ->  prove
 ((parse_term "!P l. (?x. P x /\\ MEM x l) <=> EX P l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vEX; vMEM] ---->
  vASM_MESON_TAC[]);;

let vMAP_FST_ZIP = try Cache.lookup_thm "MAP_FST_ZIP" with _ ->  prove
 ((parse_term "!l1 l2. (LENGTH l1 = LENGTH l2) ==> (MAP FST (ZIP l1 l2) = l1)"),
  vLIST_INDUCT_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_SIMP_TAC[vLENGTH; vSUC_INJ; vMAP; vFST; vZIP; vNOT_SUC]);;

let vMAP_SND_ZIP = try Cache.lookup_thm "MAP_SND_ZIP" with _ ->  prove
 ((parse_term "!l1 l2. (LENGTH l1 = LENGTH l2) ==> (MAP SND (ZIP l1 l2) = l2)"),
  vLIST_INDUCT_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_SIMP_TAC[vLENGTH; vSUC_INJ; vMAP; vFST; vZIP; vNOT_SUC]);;

let vLENGTH_ZIP = try Cache.lookup_thm "LENGTH_ZIP" with _ ->  prove
 ((parse_term "!l1 l2. LENGTH l1 = LENGTH l2 ==> LENGTH(ZIP l1 l2) = LENGTH l2"),
  vREPEAT(vLIST_INDUCT_TAC |---> vGEN_TAC) ---->
  vASM_SIMP_TAC[vLENGTH; vNOT_SUC; vZIP; vSUC_INJ]);;

let vMEM_ASSOC = try Cache.lookup_thm "MEM_ASSOC" with _ ->  prove
 ((parse_term "!l x. MEM (x,ASSOC x l) l <=> MEM x (MAP FST l)"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vMEM; vMAP; vASSOC] ---->
  vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
  vASM_MESON_TAC[vPAIR; vFST]);;

let vALL_APPEND = try Cache.lookup_thm "ALL_APPEND" with _ ->  prove
 ((parse_term "!P l1 l2. ALL P (APPEND l1 l2) <=> ALL P l1 /\\ ALL P l2"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vALL; vAPPEND; vGSYM vCONJ_ASSOC]);;

let vMEM_EL = try Cache.lookup_thm "MEM_EL" with _ ->  prove
 ((parse_term "!l n. n < LENGTH l ==> MEM (EL n l) l"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vMEM; vCONJUNCT1 vLT; vLENGTH] ---->
  vINDUCT_TAC ----> vASM_SIMP_TAC[vEL; vHD; vLT_SUC; vTL]);;

let vMEM_EXISTS_EL = try Cache.lookup_thm "MEM_EXISTS_EL" with _ ->  prove
 ((parse_term "!l x. MEM x l <=> ?i. i < LENGTH l /\\ x = EL i l"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vLENGTH; vEL; vMEM; vCONJUNCT1 vLT] ---->
  vGEN_TAC ----> vGEN_REWRITE_TAC vRAND_CONV
   [vMESON[num_CASES] (parse_term "(?i. P i) <=> P 0 \\/ (?i. P(SUC i))")] ---->
  vREWRITE_TAC[vLT_SUC; vLT_0; vEL; vHD; vTL]);;

let vALL_EL = try Cache.lookup_thm "ALL_EL" with _ ->  prove
 ((parse_term "!P l. (!i. i < LENGTH l ==> P (EL i l)) <=> ALL P l"),
  vREWRITE_TAC[vGSYM vALL_MEM; vMEM_EXISTS_EL] ----> vMESON_TAC[]);;

let vALL2_MAP2 = try Cache.lookup_thm "ALL2_MAP2" with _ ->  prove
 ((parse_term "!l m. ALL2 P (MAP f l) (MAP g m) = ALL2 (\\x y. P (f x) (g y)) l m"),
  vLIST_INDUCT_TAC ----> vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL2; vMAP]);;

let vAND_ALL2 = try Cache.lookup_thm "AND_ALL2" with _ ->  prove
 ((parse_term "!P Q l m. ALL2 P l m /\\ ALL2 Q l m <=> ALL2 (\\x y. P x y /\\ Q x y) l m"),
  vGEN_TAC ----> vGEN_TAC ----> vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ---->
  vLIST_INDUCT_TAC ----> vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL2] ---->
  vREWRITE_TAC[vCONJ_ACI]);;

let vALLPAIRS_SYM = try Cache.lookup_thm "ALLPAIRS_SYM" with _ ->  prove
 ((parse_term "!P l m. ALLPAIRS P l m <=> ALLPAIRS (\\x y. P y x) m l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vREWRITE_TAC[vALLPAIRS] ---->
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALLPAIRS; vALL] ---->
  vASM_MESON_TAC[]);;

let vALLPAIRS_MEM = try Cache.lookup_thm "ALLPAIRS_MEM" with _ ->  prove
 ((parse_term "!P l m. (!x y. MEM x l /\\ MEM y m ==> P x y) <=> ALLPAIRS P l m"),
  vGEN_TAC ---->
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vALLPAIRS; vGSYM vALL_MEM; vMEM] ---->
  vASM_MESON_TAC[]);;

let vALLPAIRS_MAP = try Cache.lookup_thm "ALLPAIRS_MAP" with _ ->  prove
 ((parse_term "!P l m. ALLPAIRS P (MAP f l) (MAP g m) <=>\n           ALLPAIRS (\\x y. P (f x) (g y)) l m"),
  vREWRITE_TAC[vGSYM vALLPAIRS_MEM; vMEM_MAP] ----> vMESON_TAC[]);;

let vALLPAIRS_EQ = try Cache.lookup_thm "ALLPAIRS_EQ" with _ ->  prove
 ((parse_term "!l m. !P Q. ALL P (l:A list) /\\ ALL Q (m:B list) /\\\n               (!p q. P p /\\ Q q ==> (R p q <=> R' p q))\n               ==> (ALLPAIRS R l m <=> ALLPAIRS R' l m)"),
  vREWRITE_TAC[vGSYM vALLPAIRS_MEM; vGSYM vALL_MEM] ----> vMESON_TAC[]);;

let vALL2_ALL = try Cache.lookup_thm "ALL2_ALL" with _ ->  prove
 ((parse_term "!P l. ALL2 P l l <=> ALL (\\x. P x x) l"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vALL2; vALL]);;

let vAPPEND_EQ_NIL = try Cache.lookup_thm "APPEND_EQ_NIL" with _ ->  prove
 ((parse_term "!l m. (APPEND l m = []) <=> (l = []) /\\ (m = [])"),
  vREWRITE_TAC[vGSYM vLENGTH_EQ_NIL; vLENGTH_APPEND; vADD_EQ_0]);;

let vAPPEND_LCANCEL = try Cache.lookup_thm "APPEND_LCANCEL" with _ ->  prove
 ((parse_term "!l1 l2 l3:A list. APPEND l1 l2 = APPEND l1 l3 <=> l2 = l3"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vAPPEND; vCONS_11]);;

let vAPPEND_RCANCEL = try Cache.lookup_thm "APPEND_RCANCEL" with _ ->  prove
 ((parse_term "!l1 l2 l3:A list. APPEND l1 l3 = APPEND l2 l3 <=> l1 = l2"),
  vONCE_REWRITE_TAC[vMESON[vREVERSE_REVERSE]
   (parse_term "l = l' <=> REVERSE l = REVERSE l'")] ---->
  vREWRITE_TAC[vREVERSE_APPEND; vAPPEND_LCANCEL]);;

let vLENGTH_MAP2 = try Cache.lookup_thm "LENGTH_MAP2" with _ ->  prove
 ((parse_term "!f l m. LENGTH l = LENGTH m ==> LENGTH(MAP2 f l m) = LENGTH m"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_SIMP_TAC[vLENGTH; vNOT_CONS_NIL; vNOT_SUC; vMAP2; vSUC_INJ]);;

let vEL_MAP2 = try Cache.lookup_thm "EL_MAP2" with _ ->  prove
 ((parse_term "!f l m k. k < LENGTH l /\\ k < LENGTH m\n             ==> EL k (MAP2 f l m) = f (EL k l) (EL k m)"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_SIMP_TAC[vLENGTH; vCONJUNCT1 vLT] ---->
  vINDUCT_TAC ----> vASM_SIMP_TAC[vLENGTH; vMAP2; vEL; vHD; vTL; vLT_SUC]);;

let vMAP_EQ_NIL  = try Cache.lookup_thm "MAP_EQ_NIL" with _ ->  prove
 ((parse_term "!f l. MAP f l = [] <=> l = []"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ----> vREWRITE_TAC[vMAP; vNOT_CONS_NIL]);;

let vINJECTIVE_MAP = try Cache.lookup_thm "INJECTIVE_MAP" with _ ->  prove
 ((parse_term "!f:A->B. (!l m. MAP f l = MAP f m ==> l = m) <=>\n            (!x y. f x = f y ==> x = y)"),
  vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vMAP_EVERY vX_GEN_TAC [(parse_term "x:A"); (parse_term "y:A")] ----> vDISCH_TAC ---->
    vFIRST_X_ASSUM(vMP_TAC -| vSPECL [(parse_term "[x:A]"); (parse_term "[y:A]")]) ---->
    vASM_REWRITE_TAC[vMAP; vCONS_11];
    vREPEAT vLIST_INDUCT_TAC ----> vASM_SIMP_TAC[vMAP; vNOT_CONS_NIL; vCONS_11] ---->
    vASM_MESON_TAC[]]);;

let vSURJECTIVE_MAP = try Cache.lookup_thm "SURJECTIVE_MAP" with _ ->  prove
 ((parse_term "!f:A->B. (!m. ?l. MAP f l = m) <=> (!y. ?x. f x = y)"),
  vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vX_GEN_TAC (parse_term "y:B") ----> vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "[y:B]")) ---->
    vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
    vLIST_INDUCT_TAC ----> vREWRITE_TAC[vMAP; vCONS_11; vNOT_CONS_NIL; vMAP_EQ_NIL];
    vMATCH_MP_TAC list_INDUCT] ---->
  vASM_MESON_TAC[vMAP]);;

let vMAP_ID = try Cache.lookup_thm "MAP_ID" with _ ->  prove
 ((parse_term "!l. MAP (\\x. x) l = l"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vMAP]);;

let vMAP_I = try Cache.lookup_thm "MAP_I" with _ ->  prove
 ((parse_term "MAP I = I"),
  vREWRITE_TAC[vFUN_EQ_THM; vI_DEF; vMAP_ID]);;

let vBUTLAST_APPEND = try Cache.lookup_thm "BUTLAST_APPEND" with _ ->  prove
 ((parse_term "!l m:A list. BUTLAST(APPEND l m) =\n                if m = [] then BUTLAST l else APPEND l (BUTLAST m)"),
  vSIMP_TAC[vCOND_RAND; vAPPEND_NIL; vMESON[]
   (parse_term "(if p then T else q) <=> ~p ==> q")] ---->
  vLIST_INDUCT_TAC ----> vASM_SIMP_TAC[vAPPEND; vBUTLAST; vAPPEND_EQ_NIL]);;

let vAPPEND_BUTLAST_LAST = try Cache.lookup_thm "APPEND_BUTLAST_LAST" with _ ->  prove
 ((parse_term "!l. ~(l = []) ==> APPEND (BUTLAST l) [LAST l] = l"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vLAST; vBUTLAST; vNOT_CONS_NIL] ---->
  vCOND_CASES_TAC ----> vASM_SIMP_TAC[vAPPEND]);;

let vLAST_APPEND = try Cache.lookup_thm "LAST_APPEND" with _ ->  prove
 ((parse_term "!p q. LAST(APPEND p q) = if q = [] then LAST p else LAST q"),
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vAPPEND; vLAST; vAPPEND_EQ_NIL] ---->
  vMESON_TAC[]);;

let vLENGTH_TL = try Cache.lookup_thm "LENGTH_TL" with _ ->  prove
 ((parse_term "!l. ~(l = []) ==> LENGTH(TL l) = LENGTH l - 1"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vLENGTH; vTL; vARITH; vSUC_SUB1]);;

let vLAST_REVERSE = try Cache.lookup_thm "LAST_REVERSE" with _ ->  prove
 ((parse_term "!l:A list. ~(l = []) ==> LAST(REVERSE l) = HD l"),
  vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[vHD; vREVERSE; vLAST; vLAST_APPEND; vNOT_CONS_NIL]);;

let vHD_REVERSE = try Cache.lookup_thm "HD_REVERSE" with _ ->  prove
 ((parse_term "!l:A list. ~(l = []) ==> HD(REVERSE l) = LAST l"),
  vMESON_TAC[vLAST_REVERSE; vREVERSE_REVERSE; vREVERSE_EQ_EMPTY]);;

let vEL_APPEND = try Cache.lookup_thm "EL_APPEND" with _ ->  prove
 ((parse_term "!k l m. EL k (APPEND l m) = if k < LENGTH l then EL k l\n                               else EL (k - LENGTH l) m"),
  vINDUCT_TAC ----> vREWRITE_TAC[vEL] ---->
  vLIST_INDUCT_TAC ---->
  vREWRITE_TAC[vHD; vAPPEND; vLENGTH; vSUB_0; vEL; vLT_0; vCONJUNCT1 vLT] ---->
  vASM_REWRITE_TAC[vTL; vLT_SUC; vSUB_SUC]);;

let vEL_TL = try Cache.lookup_thm "EL_TL" with _ ->  prove
 ((parse_term "!n. EL n (TL l) = EL (n + 1) l"),
  vREWRITE_TAC[vGSYM vADD1; vEL]);;

let vEL_CONS = try Cache.lookup_thm "EL_CONS" with _ ->  prove
 ((parse_term "!n h t. EL n (CONS h t) = if n = 0 then h else EL (n - 1) t"),
  vINDUCT_TAC ----> vREWRITE_TAC[vEL; vHD; vTL; vNOT_SUC; vSUC_SUB1]);;

let vLAST_EL = try Cache.lookup_thm "LAST_EL" with _ ->  prove
 ((parse_term "!l. ~(l = []) ==> LAST l = EL (LENGTH l - 1) l"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vLAST; vLENGTH; vSUC_SUB1] ---->
  vDISCH_TAC ----> vCOND_CASES_TAC ---->
  vASM_SIMP_TAC[vLENGTH; vEL; vHD; vEL_CONS; vLENGTH_EQ_NIL]);;

let vHD_APPEND = try Cache.lookup_thm "HD_APPEND" with _ ->  prove
 ((parse_term "!l m:A list. HD(APPEND l m) = if l = [] then HD m else HD l"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vHD; vAPPEND; vNOT_CONS_NIL]);;

let vCONS_HD_TL = try Cache.lookup_thm "CONS_HD_TL" with _ ->  prove
 ((parse_term "!l. ~(l = []) ==> l = CONS (HD l) (TL l)"),
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vNOT_CONS_NIL;vHD;vTL]);;

let vEL_MAP = try Cache.lookup_thm "EL_MAP" with _ ->  prove
 ((parse_term "!f n l. n < LENGTH l ==> EL n (MAP f l) = f(EL n l)"),
  vGEN_TAC ----> vINDUCT_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vLENGTH; vCONJUNCT1 vLT; vLT_0; vEL; vHD; vTL; vMAP; vLT_SUC]);;

let vMAP_REVERSE = try Cache.lookup_thm "MAP_REVERSE" with _ ->  prove
 ((parse_term "!f l. REVERSE(MAP f l) = MAP f (REVERSE l)"),
  vGEN_TAC ----> vLIST_INDUCT_TAC ---->
  vASM_REWRITE_TAC[vMAP; vREVERSE; vMAP_APPEND]);;

let vALL_FILTER = try Cache.lookup_thm "ALL_FILTER" with _ ->  prove
 ((parse_term "!P Q l:A list. ALL P (FILTER Q l) <=> ALL (\\x. Q x ==> P x) l"),
  vGEN_TAC ----> vGEN_TAC ---->
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vALL; vFILTER] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vALL]);;

let vAPPEND_SING = try Cache.lookup_thm "APPEND_SING" with _ ->  prove
 ((parse_term "!h t. APPEND [h] t = CONS h t"),
  vREWRITE_TAC[vAPPEND]);;

let vMEM_APPEND_DECOMPOSE_LEFT = try Cache.lookup_thm "MEM_APPEND_DECOMPOSE_LEFT" with _ ->  prove
 ((parse_term "!x:A l. MEM x l <=> ?l1 l2. ~(MEM x l1) /\\ l = APPEND l1 (CONS x l2)"),
  vREWRITE_TAC[vTAUT (parse_term "(p <=> q) <=> (p ==> q) /\\ (q ==> p)")] ---->
  vSIMP_TAC[vLEFT_IMP_EXISTS_THM; vMEM_APPEND; vMEM] ----> vX_GEN_TAC (parse_term "x:A") ---->
  vMATCH_MP_TAC list_INDUCT ----> vREWRITE_TAC[vMEM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "y:A"); (parse_term "l:A list")] ---->
  vASM_CASES_TAC (parse_term "x:A = y") ----> vASM_MESON_TAC[vMEM; vAPPEND]);;

let vMEM_APPEND_DECOMPOSE = try Cache.lookup_thm "MEM_APPEND_DECOMPOSE" with _ ->  prove
 ((parse_term "!x:A l. MEM x l <=> ?l1 l2. l = APPEND l1 (CONS x l2)"),
  vREWRITE_TAC[vTAUT (parse_term "(p <=> q) <=> (p ==> q) /\\ (q ==> p)")] ---->
  vSIMP_TAC[vLEFT_IMP_EXISTS_THM; vMEM_APPEND; vMEM] ---->
  vONCE_REWRITE_TAC[vMEM_APPEND_DECOMPOSE_LEFT] ----> vMESON_TAC[]);;

let vPAIRWISE_APPEND = try Cache.lookup_thm "PAIRWISE_APPEND" with _ ->  prove
 ((parse_term "!R:A->A->bool l m.\n        PAIRWISE R (APPEND l m) <=>\n        PAIRWISE R l /\\ PAIRWISE R m /\\ (!x y. MEM x l /\\ MEM y m ==> R x y)"),
  vGEN_TAC ----> vMATCH_MP_TAC list_INDUCT ---->
  vREWRITE_TAC[vAPPEND; vPAIRWISE; vMEM; vALL_APPEND; vGSYM vALL_MEM] ---->
  vMESON_TAC[]);;

let vPAIRWISE_MAP = try Cache.lookup_thm "PAIRWISE_MAP" with _ ->  prove
 ((parse_term "!R f:A->B l.\n        PAIRWISE R (MAP f l) <=> PAIRWISE (\\x y. R (f x) (f y)) l"),
  vGEN_TAC ----> vGEN_TAC ---->
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vPAIRWISE; vMAP; vALL_MAP; o_DEF]);;

let vPAIRWISE_IMPLIES = try Cache.lookup_thm "PAIRWISE_IMPLIES" with _ ->  prove
 ((parse_term "!R:A->A->bool R' l.\n        PAIRWISE R l /\\ (!x y. MEM x l /\\ MEM y l /\\ R x y ==> R' x y)\n        ==> PAIRWISE R' l"),
  vGEN_TAC ----> vGEN_TAC ----> vMATCH_MP_TAC list_INDUCT ---->
  vREWRITE_TAC[vPAIRWISE; vGSYM vALL_MEM; vMEM] ----> vMESON_TAC[]);;

let vPAIRWISE_TRANSITIVE = try Cache.lookup_thm "PAIRWISE_TRANSITIVE" with _ ->  prove
 ((parse_term "!R x y:A l.\n      (!x y z. R x y /\\ R y z ==> R x z)\n      ==> (PAIRWISE R (CONS x (CONS y l)) <=> R x y /\\ PAIRWISE R (CONS y l))"),
  vREPEAT vSTRIP_TAC ---->
  vREWRITE_TAC[vPAIRWISE; vALL; vGSYM vCONJ_ASSOC;
              vTAUT (parse_term "(p /\\ q /\\ r /\\ s <=> p /\\ r /\\ s) <=>\n                    p /\\ s ==> r ==> q")] ---->
  vSTRIP_TAC ----> vMATCH_MP_TAC(vREWRITE_RULE[vIMP_CONJ] vALL_IMP) ---->
  vASM_MESON_TAC[]);;

let vLENGTH_LIST_OF_SEQ = try Cache.lookup_thm "LENGTH_LIST_OF_SEQ" with _ ->  prove
 ((parse_term "!s:num->A n. LENGTH(list_of_seq s n) = n"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[list_of_seq; vLENGTH; vLENGTH_APPEND; vADD_CLAUSES]);;

let vEL_LIST_OF_SEQ = try Cache.lookup_thm "EL_LIST_OF_SEQ" with _ ->  prove
 ((parse_term "!s:num->A m n. m < n ==> EL m (list_of_seq s n) = s m"),
  vGEN_TAC ----> vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vINDUCT_TAC ---->
  vREWRITE_TAC[list_of_seq; vLT; vEL_APPEND; vLENGTH_LIST_OF_SEQ] ---->
  vREPEAT vSTRIP_TAC ----> vASM_SIMP_TAC[vSUB_REFL; vEL; vHD; vLT_REFL]);;

let vLIST_OF_SEQ_EQ_NIL = try Cache.lookup_thm "LIST_OF_SEQ_EQ_NIL" with _ ->  prove
 ((parse_term "!s:num->A n. list_of_seq s n = [] <=> n = 0"),
  vREWRITE_TAC[vGSYM vLENGTH_EQ_NIL; vLENGTH_LIST_OF_SEQ; vLENGTH]);;

(* ------------------------------------------------------------------------- *)
(* Syntax.                                                                   *)
(* ------------------------------------------------------------------------- *)

let mk_cons h t =
  try let cons = mk_const("CONS",[type_of h,aty]) in
      mk_comb(mk_comb(cons,h),t)
  with Failure _ -> failwith "mk_cons";;

let mk_list (tms,ty) =
  try let nil = mk_const("NIL",[ty,aty]) in
      if tms = [] then nil else
      let cons = mk_const("CONS",[ty,aty]) in
      itlist (mk_binop cons) tms nil
  with Failure _ -> failwith "mk_list";;

let mk_flist tms =
  try mk_list(tms,type_of(hd tms))
  with Failure _ -> failwith "mk_flist";;

(* ------------------------------------------------------------------------- *)
(* Extra monotonicity theorems for inductive definitions.                    *)
(* ------------------------------------------------------------------------- *)

let vMONO_ALL = try Cache.lookup_thm "MONO_ALL" with _ ->  prove
 ((parse_term "(!x:A. P x ==> Q x) ==> ALL P l ==> ALL Q l"),
  vDISCH_TAC ----> vSPEC_TAC((parse_term "l:A list"),(parse_term "l:A list")) ---->
  vLIST_INDUCT_TAC ----> vASM_REWRITE_TAC[vALL] ----> vASM_MESON_TAC[]);;

let vMONO_ALL2 = try Cache.lookup_thm "MONO_ALL2" with _ ->  prove
 ((parse_term "(!x y. (P:A->B->bool) x y ==> Q x y) ==> ALL2 P l l' ==> ALL2 Q l l'"),
  vDISCH_TAC ---->
  vSPEC_TAC((parse_term "l':B list"),(parse_term "l':B list")) ----> vSPEC_TAC((parse_term "l:A list"),(parse_term "l:A list")) ---->
  vLIST_INDUCT_TAC ----> vREWRITE_TAC[vALL2_DEF] ---->
  vGEN_TAC ----> vCOND_CASES_TAC ----> vREWRITE_TAC[] ----> vASM_MESON_TAC[]);;

monotonicity_theorems := [vMONO_ALL; vMONO_ALL2] @ !monotonicity_theorems;;

(* ------------------------------------------------------------------------- *)
(* Apply a conversion down a list.                                           *)
(* ------------------------------------------------------------------------- *)

let rec vLIST_CONV conv tm =
  if is_cons tm then
    vCOMB2_CONV (vRAND_CONV conv) (vLIST_CONV conv) tm
  else if fst(dest_const tm) = "NIL" then vREFL tm
  else failwith "LIST_CONV";;

(* ------------------------------------------------------------------------- *)
(* Type of characters, like the HOL88 "ascii" type, with syntax              *)
(* constructors and equality conversions for chars and strings.              *)
(* ------------------------------------------------------------------------- *)

let char_INDUCT,char_RECURSION = define_type
 "char = ASCII bool bool bool bool bool bool bool bool";;

new_type_abbrev("string",(parse_type "char list"));;

let dest_char,mk_char,dest_string,mk_string,vCHAR_EQ_CONV,vSTRING_EQ_CONV =
  let bool_of_term t =
    match t with
      Const("T",_) -> true
    | Const("F",_) -> false
    | _ -> failwith "bool_of_term" in
  let code_of_term t =
    let f,tms = strip_comb t in
    if not(is_const f && fst(dest_const f) = "ASCII")
       || not(length tms = 8) then failwith "code_of_term"
    else
       itlist (fun b f -> if b then 1 + 2 * f else 2 * f)
              (map bool_of_term (rev tms)) 0 in
  let char_of_term = Char.chr -| code_of_term in
  let dest_string tm =
    try let tms = dest_list tm in
        if fst(dest_type(hd(snd(dest_type(type_of tm))))) <> "char"
        then fail() else
        let ccs = map (String.make 1 -| char_of_term) tms in
        String.escaped (implode ccs)
    with Failure _ -> failwith "dest_string" in
  let mk_bool b =
    let true_tm,false_tm = (parse_term "T"),(parse_term "F") in
    if b then true_tm else false_tm in
  let mk_code =
    let ascii_tm = (parse_term "ASCII") in
    let mk_code c =
      let lis = map (fun i -> mk_bool((c / (1 lsl i)) mod 2 = 1)) (0--7) in
      itlist (fun x y -> mk_comb(y,x)) lis ascii_tm in
    let codes = Array.map mk_code (Array.of_list (0--255)) in
    fun c -> Array.get codes c in
  let mk_char = mk_code -| Char.code in
  let mk_string s =
    let ns = map (fun i -> Char.code(String.get s i))
                 (0--(String.length s - 1)) in
    mk_list(map mk_code ns,(parse_type "char")) in
  let vCHAR_DISTINCTNESS =
    let avars,bvars,cvars =
     [(parse_term "a0:bool");(parse_term "a1:bool");(parse_term "a2:bool");(parse_term "a3:bool");(parse_term "a4:bool");(parse_term "a5:bool");(parse_term "a6:bool")],
     [(parse_term "b1:bool");(parse_term "b2:bool");(parse_term "b3:bool");(parse_term "b4:bool");(parse_term "b5:bool");(parse_term "b6:bool");(parse_term "b7:bool")],
     [(parse_term "c1:bool");(parse_term "c2:bool");(parse_term "c3:bool");(parse_term "c4:bool");(parse_term "c5:bool");(parse_term "c6:bool");(parse_term "c7:bool")] in
    let vASCII_NEQS_FT = (map vEQF_INTRO -| vCONJUNCTS -| prove)
     ((parse_term "~(ASCII F b1 b2 b3 b4 b5 b6 b7 = ASCII T c1 c2 c3 c4 c5 c6 c7) /\\\n       ~(ASCII a0 F b2 b3 b4 b5 b6 b7 = ASCII a0 T c2 c3 c4 c5 c6 c7) /\\\n       ~(ASCII a0 a1 F b3 b4 b5 b6 b7 = ASCII a0 a1 T c3 c4 c5 c6 c7) /\\\n       ~(ASCII a0 a1 a2 F b4 b5 b6 b7 = ASCII a0 a1 a2 T c4 c5 c6 c7) /\\\n       ~(ASCII a0 a1 a2 a3 F b5 b6 b7 = ASCII a0 a1 a2 a3 T c5 c6 c7) /\\\n       ~(ASCII a0 a1 a2 a3 a4 F b6 b7 = ASCII a0 a1 a2 a3 a4 T c6 c7) /\\\n       ~(ASCII a0 a1 a2 a3 a4 a5 F b7 = ASCII a0 a1 a2 a3 a4 a5 T c7) /\\\n       ~(ASCII a0 a1 a2 a3 a4 a5 a6 F = ASCII a0 a1 a2 a3 a4 a5 a6 T)"),
      vREWRITE_TAC[injectivity "char"]) in
    let vASCII_NEQS_TF =
      let ilist = zip bvars cvars @ zip cvars bvars in
      let f = vEQF_INTRO -| vINST ilist -| vGSYM -| vEQF_ELIM in
      map f vASCII_NEQS_FT in
    let rec prefix n l =
      if n = 0 then [] else
      match l with
        h::t -> h :: prefix (n-1) t
      | _ -> l in
    let rec findneq n prefix a b =
      match a,b with
        b1::a, b2::b -> if b1 <> b2 then n,rev prefix,bool_of_term b2,a,b else
                        findneq (n+1) (b1 :: prefix) a b
      | _, _ -> fail() in
    fun c1 c2 ->
      let _,a = strip_comb c1
      and _,b = strip_comb c2 in
      let n,p,b,s1,s2 = findneq 0 [] a b in
      let ss1 = funpow n tl bvars
      and ss2 = funpow n tl cvars in
      let pp = prefix n avars in
      let pth = if b then vASCII_NEQS_FT else vASCII_NEQS_TF in
      vINST (zip p pp @ zip s1 ss1 @ zip s2 ss2) (el n pth) in
  let vSTRING_DISTINCTNESS =
    let xtm,xstm = (parse_term "x:char"),(parse_term "xs:string")
    and ytm,ystm = (parse_term "y:char"),(parse_term "ys:string")
    and niltm = (parse_term "[]:string") in
    let vNIL_EQ_THM = vEQT_INTRO (vREFL niltm)
    and vCONS_EQ_THM,vCONS_NEQ_THM = (vCONJ_PAIR -| prove)
     ((parse_term "(CONS x xs:string = CONS x ys <=> xs = ys) /\\\n       ((x = y <=> F) ==> (CONS x xs:string = CONS y ys <=> F))"),
      vREWRITE_TAC[vCONS_11] ----> vMESON_TAC[])
    and vNIL_NEQ_CONS,vCONS_NEQ_NIL = (vCONJ_PAIR -| prove)
     ((parse_term "(NIL:string = CONS x xs <=> F) /\\\n       (CONS x xs:string = NIL <=> F)"),
      vREWRITE_TAC[vNOT_CONS_NIL]) in
    let rec vSTRING_DISTINCTNESS s1 s2 =
      if s1 = niltm
      then if s2 = niltm then vNIL_EQ_THM
           else let c2,s2 = rand (rator s2),rand s2 in
                vINST [c2,xtm;s2,xstm] vNIL_NEQ_CONS
      else let c1,s1 = rand (rator s1),rand s1 in
           if s2 = niltm then vINST [c1,xtm;s1,xstm] vCONS_NEQ_NIL
           else let c2,s2 = rand (rator s2),rand s2 in
           if c1 = c2
           then let th1 = vINST [c1,xtm; s1,xstm; s2,ystm] vCONS_EQ_THM
                and th2 = vSTRING_DISTINCTNESS s1 s2 in
                vTRANS th1 th2
           else let ilist = [c1,xtm; c2,ytm; s1,xstm; s2,ystm] in
                let itm = vINST ilist vCONS_NEQ_THM in
                vMP itm (vCHAR_DISTINCTNESS c1 c2) in
    vSTRING_DISTINCTNESS in
  let vCHAR_EQ_CONV : conv =
    fun tm ->
      let c1,c2 = dest_eq tm in
      if compare c1 c2 = 0 then vEQT_INTRO (vREFL c1) else
      vCHAR_DISTINCTNESS c1 c2
  and vSTRING_EQ_CONV tm =
    let ltm,rtm = dest_eq tm in
    if compare ltm rtm = 0 then vEQT_INTRO (vREFL ltm) else
    vSTRING_DISTINCTNESS ltm rtm in
  char_of_term,mk_char,dest_string,mk_string,vCHAR_EQ_CONV,vSTRING_EQ_CONV;;
