(* ========================================================================= *)
(* Natural number arithmetic.                                                *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2015                         *)
(*      (c) Copyright, Andrea Gabrielli, Marco Maggesi 2017-2018             *)
(*                (c) Copyright, Mario Carneiro 2020                         *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Printer
open Parser
open Equal
open Bool
open Drule
open Tactics
open Itab
open Simp
open Theorems
open Class
open Meson
open Metis
open Impconv
open Nums
open Recursion
;;

(* ------------------------------------------------------------------------- *)
(* Note: all the following proofs are intuitionistic and intensional, except *)
(* for the least number principle num_WOP.                                   *)
(* (And except the arith rewrites at the end; these could be done that way   *)
(* but they use the conditional anyway.) In fact, one could very easily      *)
(* write a "decider" returning P \/ ~P for quantifier-free P.                *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<",(12,"right"));;
parse_as_infix("<=",(12,"right"));;
parse_as_infix(">",(12,"right"));;
parse_as_infix(">=",(12,"right"));;

parse_as_infix("+",(16,"right"));;
parse_as_infix("-",(18,"left"));;
parse_as_infix("*",(20,"right"));;
parse_as_infix("EXP",(24,"left"));;

parse_as_infix("DIV",(22,"left"));;
parse_as_infix("MOD",(22,"left"));;

(* ------------------------------------------------------------------------- *)
(* The predecessor function.                                                 *)
(* ------------------------------------------------------------------------- *)

let vPRE = new_recursive_definition num_RECURSION
 (parse_term "(PRE 0 = 0) /\\\n  (!n. PRE (SUC n) = n)");;

(* ------------------------------------------------------------------------- *)
(* Addition.                                                                 *)
(* ------------------------------------------------------------------------- *)

let vADD = new_recursive_definition num_RECURSION
 (parse_term "(!n. 0 + n = n) /\\\n  (!m n. (SUC m) + n = SUC(m + n))");;

let vADD_0 = prove
 ((parse_term "!m. m + 0 = m"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD]);;

let vADD_SUC = prove
 ((parse_term "!m n. m + (SUC n) = SUC(m + n)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD]);;

let vADD_CLAUSES = prove
 ((parse_term "(!n. 0 + n = n) /\\\n   (!m. m + 0 = m) /\\\n   (!m n. (SUC m) + n = SUC(m + n)) /\\\n   (!m n. m + (SUC n) = SUC(m + n))"),
  vREWRITE_TAC[vADD; vADD_0; vADD_SUC]);;

let vADD_SYM = prove
 ((parse_term "!m n. m + n = n + m"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES]);;

let vADD_ASSOC = prove
 ((parse_term "!m n p. m + (n + p) = (m + n) + p"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES]);;

let vADD_AC = prove
 ((parse_term "(m + n = n + m) /\\\n   ((m + n) + p = m + (n + p)) /\\\n   (m + (n + p) = n + (m + p))"),
  vMESON_TAC[vADD_ASSOC; vADD_SYM]);;

let vADD_EQ_0 = prove
 ((parse_term "!m n. (m + n = 0) <=> (m = 0) /\\ (n = 0)"),
  vREPEAT vINDUCT_TAC ----> vREWRITE_TAC[vADD_CLAUSES; vNOT_SUC]);;

let vEQ_ADD_LCANCEL = prove
 ((parse_term "!m n p. (m + n = m + p) <=> (n = p)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES; vSUC_INJ]);;

let vEQ_ADD_RCANCEL = prove
 ((parse_term "!m n p. (m + p = n + p) <=> (m = n)"),
  vONCE_REWRITE_TAC[vADD_SYM] ----> vMATCH_ACCEPT_TAC vEQ_ADD_LCANCEL);;

let vEQ_ADD_LCANCEL_0 = prove
 ((parse_term "!m n. (m + n = m) <=> (n = 0)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES; vSUC_INJ]);;

let vEQ_ADD_RCANCEL_0 = prove
 ((parse_term "!m n. (m + n = n) <=> (m = 0)"),
  vONCE_REWRITE_TAC[vADD_SYM] ----> vMATCH_ACCEPT_TAC vEQ_ADD_LCANCEL_0);;

(* ------------------------------------------------------------------------- *)
(* Now define "bitwise" binary representation of numerals.                   *)
(* ------------------------------------------------------------------------- *)

let vBIT0 = prove
 ((parse_term "!n. BIT0 n = n + n"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vBIT0_DEF; vADD_CLAUSES]);;

let vBIT1 = prove
 ((parse_term "!n. BIT1 n = SUC(n + n)"),
  vREWRITE_TAC[vBIT1_DEF; vBIT0]);;

let vBIT0_THM = prove
 ((parse_term "!n. NUMERAL (BIT0 n) = NUMERAL n + NUMERAL n"),
  vREWRITE_TAC[vNUMERAL; vBIT0]);;

let vBIT1_THM = prove
 ((parse_term "!n. NUMERAL (BIT1 n) = SUC(NUMERAL n + NUMERAL n)"),
  vREWRITE_TAC[vNUMERAL; vBIT1]);;

(* ------------------------------------------------------------------------- *)
(* Following is handy before num_CONV arrives.                               *)
(* ------------------------------------------------------------------------- *)

let vONE = prove
 ((parse_term "1 = SUC 0"),
  vREWRITE_TAC[vBIT1; vREWRITE_RULE[vNUMERAL] vADD_CLAUSES; vNUMERAL]);;

let vTWO = prove
 ((parse_term "2 = SUC 1"),
  vREWRITE_TAC[vBIT0; vBIT1; vREWRITE_RULE[vNUMERAL] vADD_CLAUSES; vNUMERAL]);;

(* ------------------------------------------------------------------------- *)
(* One immediate consequence.                                                *)
(* ------------------------------------------------------------------------- *)

let vADD1 = prove
 ((parse_term "!m. SUC m = m + 1"),
  vREWRITE_TAC[vBIT1_THM; vADD_CLAUSES]);;

(* ------------------------------------------------------------------------- *)
(* Multiplication.                                                           *)
(* ------------------------------------------------------------------------- *)

let vMULT = new_recursive_definition num_RECURSION
 (parse_term "(!n. 0 * n = 0) /\\\n  (!m n. (SUC m) * n = (m * n) + n)");;

let vMULT_0 = prove
 ((parse_term "!m. m * 0 = 0"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vMULT; vADD_CLAUSES]);;

let vMULT_SUC = prove
 ((parse_term "!m n. m * (SUC n) = m + (m * n)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vMULT; vADD_CLAUSES; vADD_ASSOC]);;

let vMULT_CLAUSES = prove
 ((parse_term "(!n. 0 * n = 0) /\\\n   (!m. m * 0 = 0) /\\\n   (!n. 1 * n = n) /\\\n   (!m. m * 1 = m) /\\\n   (!m n. (SUC m) * n = (m * n) + n) /\\\n   (!m n. m * (SUC n) = m + (m * n))"),
  vREWRITE_TAC[vBIT1_THM; vMULT; vMULT_0; vMULT_SUC; vADD_CLAUSES]);;

let vMULT_SYM = prove
 ((parse_term "!m n. m * n = n * m"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vEQT_INTRO(vSPEC_ALL vADD_SYM)]);;

let vLEFT_ADD_DISTRIB = prove
 ((parse_term "!m n p. m * (n + p) = (m * n) + (m * p)"),
  vGEN_TAC ----> vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD; vMULT_CLAUSES; vADD_ASSOC]);;

let vRIGHT_ADD_DISTRIB = prove
 ((parse_term "!m n p. (m + n) * p = (m * p) + (n * p)"),
  vONCE_REWRITE_TAC[vMULT_SYM] ----> vMATCH_ACCEPT_TAC vLEFT_ADD_DISTRIB);;

let vMULT_ASSOC = prove
 ((parse_term "!m n p. m * (n * p) = (m * n) * p"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vRIGHT_ADD_DISTRIB]);;

let vMULT_AC = prove
 ((parse_term "(m * n = n * m) /\\\n   ((m * n) * p = m * (n * p)) /\\\n   (m * (n * p) = n * (m * p))"),
  vMESON_TAC[vMULT_ASSOC; vMULT_SYM]);;

let vMULT_EQ_0 = prove
 ((parse_term "!m n. (m * n = 0) <=> (m = 0) \\/ (n = 0)"),
  vREPEAT vINDUCT_TAC ----> vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vNOT_SUC]);;

let vEQ_MULT_LCANCEL = prove
 ((parse_term "!m n p. (m * n = m * p) <=> (m = 0) \\/ (n = p)"),
  vINDUCT_TAC ----> vREWRITE_TAC[vMULT_CLAUSES; vNOT_SUC] ---->
  vREPEAT vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vGSYM vNOT_SUC; vNOT_SUC] ---->
  vASM_REWRITE_TAC[vSUC_INJ; vGSYM vADD_ASSOC; vEQ_ADD_LCANCEL]);;

let vEQ_MULT_RCANCEL = prove
 ((parse_term "!m n p. (m * p = n * p) <=> (m = n) \\/ (p = 0)"),
  vONCE_REWRITE_TAC[vMULT_SYM; vDISJ_SYM] ----> vMATCH_ACCEPT_TAC vEQ_MULT_LCANCEL);;

let vMULT_2 = prove
 ((parse_term "!n. 2 * n = n + n"),
  vGEN_TAC ----> vREWRITE_TAC[vBIT0_THM; vMULT_CLAUSES; vRIGHT_ADD_DISTRIB]);;

let vMULT_EQ_1 = prove
 ((parse_term "!m n. (m * n = 1) <=> (m = 1) /\\ (n = 1)"),
  vINDUCT_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC
    [vMULT_CLAUSES; vADD_CLAUSES; vBIT0_THM; vBIT1_THM; vGSYM vNOT_SUC] ---->
  vREWRITE_TAC[vSUC_INJ; vADD_EQ_0; vMULT_EQ_0] ---->
  vCONV_TAC vTAUT);;

(* ------------------------------------------------------------------------- *)
(* Exponentiation.                                                           *)
(* ------------------------------------------------------------------------- *)

let vEXP = new_recursive_definition num_RECURSION
 (parse_term "(!m. m EXP 0 = 1) /\\\n  (!m n. m EXP (SUC n) = m * (m EXP n))");;

let vEXP_EQ_0 = prove
 ((parse_term "!m n. (m EXP n = 0) <=> (m = 0) /\\ ~(n = 0)"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC
    [vBIT1_THM; vNOT_SUC; vNOT_SUC; vEXP; vMULT_CLAUSES; vADD_CLAUSES; vADD_EQ_0]);;

let vEXP_EQ_1 = prove
 ((parse_term "!x n. x EXP n = 1 <=> x = 1 \\/ n = 0"),
  vGEN_TAC ----> vINDUCT_TAC ----> vASM_REWRITE_TAC[vEXP; vMULT_EQ_1; vNOT_SUC] ---->
  vCONV_TAC vTAUT);;

let vEXP_ZERO = prove
 ((parse_term "!n. 0 EXP n = if n = 0 then 1 else 0"),
  vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vEXP_EQ_0; vEXP_EQ_1]);;

let vEXP_ADD = prove
 ((parse_term "!m n p. m EXP (n + p) = (m EXP n) * (m EXP p)"),
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vEXP; vADD_CLAUSES; vMULT_CLAUSES; vMULT_AC]);;

let vEXP_ONE = prove
 ((parse_term "!n. 1 EXP n = 1"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vEXP; vMULT_CLAUSES]);;

let vEXP_1 = prove
 ((parse_term "!n. n EXP 1 = n"),
  vREWRITE_TAC[vONE; vEXP; vMULT_CLAUSES; vADD_CLAUSES]);;

let vEXP_2 = prove
 ((parse_term "!n. n EXP 2 = n * n"),
  vREWRITE_TAC[vBIT0_THM; vBIT1_THM; vEXP; vEXP_ADD; vMULT_CLAUSES; vADD_CLAUSES]);;

let vMULT_EXP = prove
 ((parse_term "!p m n. (m * n) EXP p = m EXP p * n EXP p"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vEXP; vMULT_CLAUSES; vMULT_AC]);;

let vEXP_MULT = prove
 ((parse_term "!m n p. m EXP (n * p) = (m EXP n) EXP p"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vEXP_ADD; vEXP; vMULT_CLAUSES] ++-->
   [vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ---->
    vINDUCT_TAC ----> vASM_REWRITE_TAC[vEXP; vMULT_CLAUSES];
    vREWRITE_TAC[vMULT_EXP] ----> vMATCH_ACCEPT_TAC vMULT_SYM]);;

let vEXP_EXP = prove
 ((parse_term "!x m n. (x EXP m) EXP n = x EXP (m * n)"),
  vREWRITE_TAC[vEXP_MULT]);;

(* ------------------------------------------------------------------------- *)
(* Define the orderings recursively too.                                     *)
(* ------------------------------------------------------------------------- *)

let vLE = new_recursive_definition num_RECURSION
 (parse_term "(!m. (m <= 0) <=> (m = 0)) /\\\n  (!m n. (m <= SUC n) <=> (m = SUC n) \\/ (m <= n))");;

let vLT = new_recursive_definition num_RECURSION
 (parse_term "(!m. (m < 0) <=> F) /\\\n  (!m n. (m < SUC n) <=> (m = n) \\/ (m < n))");;

let vGE = new_definition
  (parse_term "m >= n <=> n <= m");;

let vGT = new_definition
  (parse_term "m > n <=> n < m");;

(* ------------------------------------------------------------------------- *)
(* Maximum and minimum of natural numbers.                                   *)
(* ------------------------------------------------------------------------- *)

let vMAX = new_definition
  (parse_term "!m n. MAX m n = if m <= n then n else m");;

let vMIN = new_definition
  (parse_term "!m n. MIN m n = if m <= n then m else n");;

(* ------------------------------------------------------------------------- *)
(* Step cases.                                                               *)
(* ------------------------------------------------------------------------- *)

let vLE_SUC_LT = prove
 ((parse_term "!m n. (SUC m <= n) <=> (m < n)"),
  vGEN_TAC ----> vINDUCT_TAC ----> vASM_REWRITE_TAC[vLE; vLT; vNOT_SUC; vSUC_INJ]);;

let vLT_SUC_LE = prove
 ((parse_term "!m n. (m < SUC n) <=> (m <= n)"),
  vGEN_TAC ----> vINDUCT_TAC ----> vONCE_REWRITE_TAC[vLT; vLE] ---->
  vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vLT]);;

let vLE_SUC = prove
 ((parse_term "!m n. (SUC m <= SUC n) <=> (m <= n)"),
  vREWRITE_TAC[vLE_SUC_LT; vLT_SUC_LE]);;

let vLT_SUC = prove
 ((parse_term "!m n. (SUC m < SUC n) <=> (m < n)"),
  vREWRITE_TAC[vLT_SUC_LE; vLE_SUC_LT]);;

(* ------------------------------------------------------------------------- *)
(* Base cases.                                                               *)
(* ------------------------------------------------------------------------- *)

let vLE_0 = prove
 ((parse_term "!n. 0 <= n"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vLE]);;

let vLT_0 = prove
 ((parse_term "!n. 0 < SUC n"),
  vREWRITE_TAC[vLT_SUC_LE; vLE_0]);;

(* ------------------------------------------------------------------------- *)
(* Reflexivity.                                                              *)
(* ------------------------------------------------------------------------- *)

let vLE_REFL = prove
 ((parse_term "!n. n <= n"),
  vINDUCT_TAC ----> vREWRITE_TAC[vLE]);;

let vLT_REFL = prove
 ((parse_term "!n. ~(n < n)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vLT_SUC] ----> vREWRITE_TAC[vLT]);;

let vLT_IMP_NE = prove
 ((parse_term "!m n:num. m < n ==> ~(m = n)"),
  vMESON_TAC[vLT_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Antisymmetry.                                                             *)
(* ------------------------------------------------------------------------- *)

let vLE_ANTISYM = prove
 ((parse_term "!m n. (m <= n /\\ n <= m) <=> (m = n)"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vLE_SUC; vSUC_INJ] ---->
  vREWRITE_TAC[vLE; vNOT_SUC; vGSYM vNOT_SUC]);;

let vLT_ANTISYM = prove
 ((parse_term "!m n. ~(m < n /\\ n < m)"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vLT_SUC] ----> vREWRITE_TAC[vLT]);;

let vLET_ANTISYM = prove
 ((parse_term "!m n. ~(m <= n /\\ n < m)"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vLE_SUC; vLT_SUC] ---->
  vREWRITE_TAC[vLE; vLT; vNOT_SUC]);;

let vLTE_ANTISYM = prove
 ((parse_term "!m n. ~(m < n /\\ n <= m)"),
  vONCE_REWRITE_TAC[vCONJ_SYM] ----> vREWRITE_TAC[vLET_ANTISYM]);;

(* ------------------------------------------------------------------------- *)
(* Transitivity.                                                             *)
(* ------------------------------------------------------------------------- *)

let vLE_TRANS = prove
 ((parse_term "!m n p. m <= n /\\ n <= p ==> m <= p"),
  vREPEAT vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vLE_SUC; vLE_0] ----> vREWRITE_TAC[vLE; vNOT_SUC]);;

let vLT_TRANS = prove
 ((parse_term "!m n p. m < n /\\ n < p ==> m < p"),
  vREPEAT vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vLT_SUC; vLT_0] ----> vREWRITE_TAC[vLT; vNOT_SUC]);;

let vLET_TRANS = prove
 ((parse_term "!m n p. m <= n /\\ n < p ==> m < p"),
  vREPEAT vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vLE_SUC; vLT_SUC; vLT_0] ----> vREWRITE_TAC[vLT; vLE; vNOT_SUC]);;

let vLTE_TRANS = prove
 ((parse_term "!m n p. m < n /\\ n <= p ==> m < p"),
  vREPEAT vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vLE_SUC; vLT_SUC; vLT_0] ----> vREWRITE_TAC[vLT; vLE; vNOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Totality.                                                                 *)
(* ------------------------------------------------------------------------- *)

let vLE_CASES = prove
 ((parse_term "!m n. m <= n \\/ n <= m"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vLE_0; vLE_SUC]);;

let vLT_CASES = prove
 ((parse_term "!m n. (m < n) \\/ (n < m) \\/ (m = n)"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vLT_SUC; vSUC_INJ] ---->
  vREWRITE_TAC[vLT; vNOT_SUC; vGSYM vNOT_SUC] ---->
  vW(vW (curry vSPEC_TAC) -| hd -| frees -| snd) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vLT_0]);;

let vLET_CASES = prove
 ((parse_term "!m n. m <= n \\/ n < m"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vLE_SUC_LT; vLT_SUC_LE; vLE_0]);;

let vLTE_CASES = prove
 ((parse_term "!m n. m < n \\/ n <= m"),
  vONCE_REWRITE_TAC[vDISJ_SYM] ----> vMATCH_ACCEPT_TAC vLET_CASES);;

(* ------------------------------------------------------------------------- *)
(* Relationship between orderings.                                           *)
(* ------------------------------------------------------------------------- *)

let vLE_LT = prove
 ((parse_term "!m n. (m <= n) <=> (m < n) \\/ (m = n)"),
  vREPEAT vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vLE_SUC; vLT_SUC; vSUC_INJ; vLE_0; vLT_0] ---->
  vREWRITE_TAC[vLE; vLT]);;

let vLT_LE = prove
 ((parse_term "!m n. (m < n) <=> (m <= n) /\\ ~(m = n)"),
  vREWRITE_TAC[vLE_LT] ----> vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vASM_REWRITE_TAC[] ----> vDISCH_THEN vSUBST_ALL_TAC ---->
    vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vLT_REFL];
    vDISCH_THEN(vCONJUNCTS_THEN2 vSTRIP_ASSUME_TAC vMP_TAC) ---->
    vASM_REWRITE_TAC[]]);;

let vNOT_LE = prove
 ((parse_term "!m n. ~(m <= n) <=> (n < m)"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vLE_SUC; vLT_SUC] ---->
  vREWRITE_TAC[vLE; vLT; vNOT_SUC; vGSYM vNOT_SUC; vLE_0] ---->
  vW(vW (curry vSPEC_TAC) -| hd -| frees -| snd) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vLT_0]);;

let vNOT_LT = prove
 ((parse_term "!m n. ~(m < n) <=> n <= m"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vLE_SUC; vLT_SUC] ---->
  vREWRITE_TAC[vLE; vLT; vNOT_SUC; vGSYM vNOT_SUC; vLE_0] ---->
  vW(vW (curry vSPEC_TAC) -| hd -| frees -| snd) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vLT_0]);;

let vLT_IMP_LE = prove
 ((parse_term "!m n. m < n ==> m <= n"),
  vREWRITE_TAC[vLT_LE] ----> vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[]);;

let vEQ_IMP_LE = prove
 ((parse_term "!m n. (m = n) ==> m <= n"),
  vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[vLE_REFL]);;

(* ------------------------------------------------------------------------- *)
(* Often useful to shuffle between different versions of "0 < n".            *)
(* ------------------------------------------------------------------------- *)

let vLT_NZ = prove
 ((parse_term "!n. 0 < n <=> ~(n = 0)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vNOT_SUC; vLT; vEQ_SYM_EQ] ---->
  vCONV_TAC vTAUT);;

let vLE_1 = prove
 ((parse_term "(!n. ~(n = 0) ==> 0 < n) /\\\n   (!n. ~(n = 0) ==> 1 <= n) /\\\n   (!n. 0 < n ==> ~(n = 0)) /\\\n   (!n. 0 < n ==> 1 <= n) /\\\n   (!n. 1 <= n ==> 0 < n) /\\\n   (!n. 1 <= n ==> ~(n = 0))"),
  vREWRITE_TAC[vLT_NZ; vGSYM vNOT_LT; vONE; vLT]);;

(* ------------------------------------------------------------------------- *)
(* Relate the orderings to arithmetic operations.                            *)
(* ------------------------------------------------------------------------- *)

let vLE_EXISTS = prove
 ((parse_term "!m n. (m <= n) <=> (?d. n = m + d)"),
  vGEN_TAC ----> vINDUCT_TAC ----> vASM_REWRITE_TAC[vLE] ++-->
   [vREWRITE_TAC[vCONV_RULE(vLAND_CONV vSYM_CONV) (vSPEC_ALL vADD_EQ_0)] ---->
    vREWRITE_TAC[vRIGHT_EXISTS_AND_THM; vEXISTS_REFL];
    vEQ_TAC ++-->
     [vDISCH_THEN(vDISJ_CASES_THEN2 vSUBST1_TAC vMP_TAC) ++-->
       [vEXISTS_TAC (parse_term "0") ----> vREWRITE_TAC[vADD_CLAUSES];
        vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:num") vSUBST1_TAC) ---->
        vEXISTS_TAC (parse_term "SUC d") ----> vREWRITE_TAC[vADD_CLAUSES]];
      vONCE_REWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
      vINDUCT_TAC ----> vREWRITE_TAC[vADD_CLAUSES; vSUC_INJ] ---->
      vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[] ----> vDISJ2_TAC ---->
      vREWRITE_TAC[vEQ_ADD_LCANCEL; vGSYM vEXISTS_REFL]]]);;

let vLT_EXISTS = prove
 ((parse_term "!m n. (m < n) <=> (?d. n = m + SUC d)"),
  vGEN_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[vLT; vADD_CLAUSES; vGSYM vNOT_SUC] ---->
  vASM_REWRITE_TAC[vSUC_INJ] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vDISJ_CASES_THEN2 vSUBST1_TAC vMP_TAC) ++-->
     [vEXISTS_TAC (parse_term "0") ----> vREWRITE_TAC[vADD_CLAUSES];
      vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:num") vSUBST1_TAC) ---->
      vEXISTS_TAC (parse_term "SUC d") ----> vREWRITE_TAC[vADD_CLAUSES]];
    vONCE_REWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
    vINDUCT_TAC ----> vREWRITE_TAC[vADD_CLAUSES; vSUC_INJ] ---->
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[] ----> vDISJ2_TAC ---->
    vREWRITE_TAC[vSUC_INJ; vEQ_ADD_LCANCEL; vGSYM vEXISTS_REFL]]);;

(* ------------------------------------------------------------------------- *)
(* Interaction with addition.                                                *)
(* ------------------------------------------------------------------------- *)

let vLE_ADD = prove
 ((parse_term "!m n. m <= m + n"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vLE; vADD_CLAUSES; vLE_REFL]);;

let vLE_ADDR = prove
 ((parse_term "!m n. n <= m + n"),
  vONCE_REWRITE_TAC[vADD_SYM] ----> vMATCH_ACCEPT_TAC vLE_ADD);;

let vLT_ADD = prove
 ((parse_term "!m n. (m < m + n) <=> (0 < n)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES; vLT_SUC]);;

let vLT_ADDR = prove
 ((parse_term "!m n. (n < m + n) <=> (0 < m)"),
  vONCE_REWRITE_TAC[vADD_SYM] ----> vMATCH_ACCEPT_TAC vLT_ADD);;

let vLE_ADD_LCANCEL = prove
 ((parse_term "!m n p. (m + n) <= (m + p) <=> n <= p"),
  vREWRITE_TAC[vLE_EXISTS; vGSYM vADD_ASSOC; vEQ_ADD_LCANCEL]);;

let vLE_ADD_RCANCEL = prove
 ((parse_term "!m n p. (m + p) <= (n + p) <=> (m <= n)"),
  vONCE_REWRITE_TAC[vADD_SYM] ----> vMATCH_ACCEPT_TAC vLE_ADD_LCANCEL);;

let vLT_ADD_LCANCEL = prove
 ((parse_term "!m n p. (m + n) < (m + p) <=> n < p"),
  vREWRITE_TAC[vLT_EXISTS; vGSYM vADD_ASSOC; vEQ_ADD_LCANCEL; vSUC_INJ]);;

let vLT_ADD_RCANCEL = prove
 ((parse_term "!m n p. (m + p) < (n + p) <=> (m < n)"),
  vONCE_REWRITE_TAC[vADD_SYM] ----> vMATCH_ACCEPT_TAC vLT_ADD_LCANCEL);;

let vLE_ADD2 = prove
 ((parse_term "!m n p q. m <= p /\\ n <= q ==> m + n <= p + q"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLE_EXISTS] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2
    (vX_CHOOSE_TAC (parse_term "a:num")) (vX_CHOOSE_TAC (parse_term "b:num"))) ---->
  vEXISTS_TAC (parse_term "a + b") ----> vASM_REWRITE_TAC[vADD_AC]);;

let vLET_ADD2 = prove
 ((parse_term "!m n p q. m <= p /\\ n < q ==> m + n < p + q"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLE_EXISTS; vLT_EXISTS] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2
    (vX_CHOOSE_TAC (parse_term "a:num")) (vX_CHOOSE_TAC (parse_term "b:num"))) ---->
  vEXISTS_TAC (parse_term "a + b") ----> vASM_REWRITE_TAC[vSUC_INJ; vADD_CLAUSES; vADD_AC]);;

let vLTE_ADD2 = prove
 ((parse_term "!m n p q. m < p /\\ n <= q ==> m + n < p + q"),
  vONCE_REWRITE_TAC[vADD_SYM; vCONJ_SYM] ---->
  vMATCH_ACCEPT_TAC vLET_ADD2);;

let vLT_ADD2 = prove
 ((parse_term "!m n p q. m < p /\\ n < q ==> m + n < p + q"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vLTE_ADD2 ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vLT_IMP_LE ---->
  vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* And multiplication.                                                       *)
(* ------------------------------------------------------------------------- *)

let vLT_MULT = prove
 ((parse_term "!m n. (0 < m * n) <=> (0 < m) /\\ (0 < n)"),
  vREPEAT vINDUCT_TAC ----> vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vLT_0]);;

let vLE_MULT2 = prove
 ((parse_term "!m n p q. m <= n /\\ p <= q ==> m * p <= n * q"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLE_EXISTS] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2
    (vX_CHOOSE_TAC (parse_term "a:num")) (vX_CHOOSE_TAC (parse_term "b:num"))) ---->
  vEXISTS_TAC (parse_term "a * p + m * b + a * b") ---->
  vASM_REWRITE_TAC[vLEFT_ADD_DISTRIB] ---->
  vREWRITE_TAC[vLEFT_ADD_DISTRIB; vRIGHT_ADD_DISTRIB; vADD_ASSOC]);;

let vLT_LMULT = prove
 ((parse_term "!m n p. ~(m = 0) /\\ n < p ==> m * n < m * p"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLT_LE] ----> vSTRIP_TAC ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vLE_MULT2 ----> vASM_REWRITE_TAC[vLE_REFL];
    vASM_REWRITE_TAC[vEQ_MULT_LCANCEL]]);;

let vLE_MULT_LCANCEL = prove
 ((parse_term "!m n p. (m * n) <= (m * p) <=> (m = 0) \\/ n <= p"),
  vREPEAT vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vLE_REFL; vLE_0; vNOT_SUC] ---->
  vREWRITE_TAC[vLE_SUC] ---->
  vREWRITE_TAC[vLE; vLE_ADD_LCANCEL; vGSYM vADD_ASSOC] ---->
  vASM_REWRITE_TAC[vGSYM(el 4(vCONJUNCTS vMULT_CLAUSES)); vNOT_SUC]);;

let vLE_MULT_RCANCEL = prove
 ((parse_term "!m n p. (m * p) <= (n * p) <=> (m <= n) \\/ (p = 0)"),
  vONCE_REWRITE_TAC[vMULT_SYM; vDISJ_SYM] ---->
  vMATCH_ACCEPT_TAC vLE_MULT_LCANCEL);;

let vLT_MULT_LCANCEL = prove
 ((parse_term "!m n p. (m * n) < (m * p) <=> ~(m = 0) /\\ n < p"),
  vREPEAT vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vLT_REFL; vLT_0; vNOT_SUC] ---->
  vREWRITE_TAC[vLT_SUC] ---->
  vREWRITE_TAC[vLT; vLT_ADD_LCANCEL; vGSYM vADD_ASSOC] ---->
  vASM_REWRITE_TAC[vGSYM(el 4(vCONJUNCTS vMULT_CLAUSES)); vNOT_SUC]);;

let vLT_MULT_RCANCEL = prove
 ((parse_term "!m n p. (m * p) < (n * p) <=> (m < n) /\\ ~(p = 0)"),
  vONCE_REWRITE_TAC[vMULT_SYM; vCONJ_SYM] ---->
  vMATCH_ACCEPT_TAC vLT_MULT_LCANCEL);;

let vLT_MULT2 = prove
 ((parse_term "!m n p q. m < n /\\ p < q ==> m * p < n * q"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vLET_TRANS ---->
  vEXISTS_TAC (parse_term "n * p") ---->
  vASM_SIMP_TAC[vLE_MULT_RCANCEL; vLT_IMP_LE; vLT_MULT_LCANCEL] ---->
  vUNDISCH_TAC (parse_term "m < n") ----> vCONV_TAC vCONTRAPOS_CONV ----> vSIMP_TAC[vLT]);;

let vLE_SQUARE_REFL = prove
 ((parse_term "!n. n <= n * n"),
  vINDUCT_TAC ----> vREWRITE_TAC[vMULT_CLAUSES; vLE_0; vLE_ADDR]);;

let vLT_POW2_REFL = prove
 ((parse_term "!n. n < 2 EXP n"),
  vINDUCT_TAC ----> vREWRITE_TAC[vEXP] ----> vREWRITE_TAC[vMULT_2; vADD1] ---->
  vREWRITE_TAC[vONE; vLT] ----> vMATCH_MP_TAC vLTE_ADD2 ---->
  vASM_REWRITE_TAC[vLE_SUC_LT; vTWO] ---->
  vMESON_TAC[vEXP_EQ_0; vLE_1; vNOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Useful "without loss of generality" lemmas.                               *)
(* ------------------------------------------------------------------------- *)

let vWLOG_LE = prove
 ((parse_term "(!m n. P m n <=> P n m) /\\ (!m n. m <= n ==> P m n) ==> !m n. P m n"),
  vMESON_TAC[vLE_CASES]);;

let vWLOG_LT = prove
 ((parse_term "(!m. P m m) /\\ (!m n. P m n <=> P n m) /\\ (!m n. m < n ==> P m n)\n   ==> !m y. P m y"),
  vMESON_TAC[vLT_CASES]);;

let vWLOG_LE_3 = prove
 ((parse_term "!P. (!x y z. P x y z ==> P y x z /\\ P x z y) /\\\n       (!x y z. x <= y /\\ y <= z ==> P x y z)\n       ==> !x y z. P x y z"),
  vMESON_TAC[vLE_CASES]);;

(* ------------------------------------------------------------------------- *)
(* Existence of least and greatest elements of (finite) set.                 *)
(* ------------------------------------------------------------------------- *)

let num_WF = prove
 ((parse_term "!P. (!n. (!m. m < n ==> P m) ==> P n) ==> !n. P n"),
  vGEN_TAC ----> vMP_TAC(vSPEC (parse_term "\\n. !m. m < n ==> P m") num_INDUCTION) ---->
  vREWRITE_TAC[vLT; vBETA_THM] ----> vMESON_TAC[vLT]);;

let num_WOP = prove
 ((parse_term "!P. (?n. P n) <=> (?n. P(n) /\\ !m. m < n ==> ~P(m))"),
  vGEN_TAC ----> vEQ_TAC ++--> [vALL_TAC; vMESON_TAC[]] ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vNOT_EXISTS_THM] ---->
  vDISCH_TAC ----> vMATCH_MP_TAC num_WF ----> vASM_MESON_TAC[]);;

let num_MAX = prove
 ((parse_term "!P. (?x. P x) /\\ (?M. !x. P x ==> x <= M) <=>\n       ?m. P m /\\ (!x. P x ==> x <= m)"),
  vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "a:num")) vMP_TAC) ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "m:num") vMP_TAC -| vONCE_REWRITE_RULE[num_WOP]) ---->
    vDISCH_THEN(fun th -> vEXISTS_TAC (parse_term "m:num") ----> vMP_TAC th) ---->
    vREWRITE_TAC[vTAUT (parse_term "(a /\\ b ==> c /\\ a) <=> (a /\\ b ==> c)")] ---->
    vSPEC_TAC((parse_term "m:num"),(parse_term "m:num")) ----> vINDUCT_TAC ++-->
     [vREWRITE_TAC[vLE; vLT] ----> vDISCH_THEN(vIMP_RES_THEN vSUBST_ALL_TAC) ---->
      vPOP_ASSUM vACCEPT_TAC;
      vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vMP_TAC -| vSPEC (parse_term "m:num"))) ---->
      vREWRITE_TAC[vLT] ----> vCONV_TAC vCONTRAPOS_CONV ---->
      vDISCH_TAC ----> vREWRITE_TAC[] ----> vX_GEN_TAC (parse_term "p:num") ---->
      vFIRST_ASSUM(vMP_TAC -| vSPEC (parse_term "p:num")) ----> vREWRITE_TAC[vLE] ---->
      vASM_CASES_TAC (parse_term "p = SUC m") ----> vASM_REWRITE_TAC[]];
    vREPEAT vSTRIP_TAC ----> vEXISTS_TAC (parse_term "m:num") ----> vASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Other variants of induction.                                              *)
(* ------------------------------------------------------------------------- *)

let vLE_INDUCT = prove
 ((parse_term "!P. (!m:num. P m m) /\\\n       (!m n. m <= n /\\ P m n ==> P m (SUC n))\n       ==> (!m n. m <= n ==> P m n)"),
   vGEN_TAC ----> vREWRITE_TAC[vIMP_CONJ; vMESON[vLE_EXISTS]
    (parse_term "(!m n:num. m <= n ==> R m n) <=> (!m d. R m (m + d))")] ---->
  vREPEAT vDISCH_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_SIMP_TAC[vADD_CLAUSES]);;

let num_INDUCTION_DOWN = prove
 ((parse_term "!(P:num->bool) m.\n        (!n. m <= n ==> P n) /\\\n        (!n. n < m /\\ P(n + 1) ==> P n)\n        ==> !n. P n"),
  vREWRITE_TAC[vGSYM vADD1] ----> vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(!x. P x) <=> ~(?x. ~P x)")] ---->
  vW(vMP_TAC -| vPART_MATCH (lhand -| lhand) num_MAX -| rand -| snd) ---->
  vMATCH_MP_TAC(vTAUT (parse_term "q /\\ ~r ==> (p /\\ q <=> r) ==> ~p")) ---->
  vONCE_REWRITE_TAC[vTAUT (parse_term "~p ==> q <=> ~q ==> p")] ---->
  vREWRITE_TAC[vNOT_EXISTS_THM; vTAUT (parse_term "~(~p /\\ q) <=> q ==> p"); vNOT_LE] ---->
  vASM_MESON_TAC[vLTE_CASES; vLT; vLT_IMP_LE]);;

(* ------------------------------------------------------------------------- *)
(* Oddness and evenness (recursively rather than inductively!)               *)
(* ------------------------------------------------------------------------- *)

let vEVEN = new_recursive_definition num_RECURSION
  (parse_term "(EVEN 0 <=> T) /\\\n   (!n. EVEN (SUC n) <=> ~(EVEN n))");;

let vODD = new_recursive_definition num_RECURSION
  (parse_term "(ODD 0 <=> F) /\\\n   (!n. ODD (SUC n) <=> ~(ODD n))");;

let vNOT_EVEN = prove
 ((parse_term "!n. ~(EVEN n) <=> ODD n"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vEVEN; vODD]);;

let vNOT_ODD = prove
 ((parse_term "!n. ~(ODD n) <=> EVEN n"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vEVEN; vODD]);;

let vEVEN_OR_ODD = prove
 ((parse_term "!n. EVEN n \\/ ODD n"),
  vINDUCT_TAC ----> vREWRITE_TAC[vEVEN; vODD; vNOT_EVEN; vNOT_ODD] ---->
  vONCE_REWRITE_TAC[vDISJ_SYM] ----> vASM_REWRITE_TAC[]);;

let vEVEN_AND_ODD = prove
 ((parse_term "!n. ~(EVEN n /\\ ODD n)"),
  vREWRITE_TAC[vGSYM vNOT_EVEN; vITAUT (parse_term "~(p /\\ ~p)")]);;

let vEVEN_ADD = prove
 ((parse_term "!m n. EVEN(m + n) <=> (EVEN m <=> EVEN n)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vEVEN; vADD_CLAUSES] ---->
  vX_GEN_TAC (parse_term "p:num") ---->
  vDISJ_CASES_THEN vMP_TAC (vSPEC (parse_term "n:num") vEVEN_OR_ODD) ---->
  vDISJ_CASES_THEN vMP_TAC (vSPEC (parse_term "p:num") vEVEN_OR_ODD) ---->
  vREWRITE_TAC[vGSYM vNOT_EVEN] ----> vDISCH_TAC ---->
  vASM_REWRITE_TAC[]);;

let vEVEN_MULT = prove
 ((parse_term "!m n. EVEN(m * n) <=> EVEN(m) \\/ EVEN(n)"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vEVEN_ADD; vEVEN] ---->
  vX_GEN_TAC (parse_term "p:num") ---->
  vDISJ_CASES_THEN vMP_TAC (vSPEC (parse_term "n:num") vEVEN_OR_ODD) ---->
  vDISJ_CASES_THEN vMP_TAC (vSPEC (parse_term "p:num") vEVEN_OR_ODD) ---->
  vREWRITE_TAC[vGSYM vNOT_EVEN] ----> vDISCH_TAC ---->
  vASM_REWRITE_TAC[]);;

let vEVEN_EXP = prove
 ((parse_term "!m n. EVEN(m EXP n) <=> EVEN(m) /\\ ~(n = 0)"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vEVEN; vEXP; vONE; vEVEN_MULT; vNOT_SUC] ---->
  vCONV_TAC vITAUT);;

let vODD_ADD = prove
 ((parse_term "!m n. ODD(m + n) <=> ~(ODD m <=> ODD n)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vNOT_EVEN; vEVEN_ADD] ---->
  vCONV_TAC vITAUT);;

let vODD_MULT = prove
 ((parse_term "!m n. ODD(m * n) <=> ODD(m) /\\ ODD(n)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vNOT_EVEN; vEVEN_MULT] ---->
  vCONV_TAC vITAUT);;

let vODD_EXP = prove
 ((parse_term "!m n. ODD(m EXP n) <=> ODD(m) \\/ (n = 0)"),
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[vODD; vEXP; vONE; vODD_MULT; vNOT_SUC] ---->
  vCONV_TAC vITAUT);;

let vEVEN_DOUBLE = prove
 ((parse_term "!n. EVEN(2 * n)"),
  vGEN_TAC ----> vREWRITE_TAC[vEVEN_MULT] ----> vDISJ1_TAC ---->
  vPURE_REWRITE_TAC[vBIT0_THM; vBIT1_THM] ----> vREWRITE_TAC[vEVEN; vEVEN_ADD]);;

let vODD_DOUBLE = prove
 ((parse_term "!n. ODD(SUC(2 * n))"),
  vREWRITE_TAC[vODD] ----> vREWRITE_TAC[vNOT_ODD; vEVEN_DOUBLE]);;

let vEVEN_EXISTS_LEMMA = prove
 ((parse_term "!n. (EVEN n ==> ?m. n = 2 * m) /\\\n       (~EVEN n ==> ?m. n = SUC(2 * m))"),
  vINDUCT_TAC ----> vREWRITE_TAC[vEVEN] ++-->
   [vEXISTS_TAC (parse_term "0") ----> vREWRITE_TAC[vMULT_CLAUSES];
    vPOP_ASSUM vSTRIP_ASSUME_TAC ----> vCONJ_TAC ---->
    vDISCH_THEN(vANTE_RES_THEN(vX_CHOOSE_TAC (parse_term "m:num"))) ++-->
     [vEXISTS_TAC (parse_term "SUC m") ----> vASM_REWRITE_TAC[] ---->
      vREWRITE_TAC[vMULT_2] ----> vREWRITE_TAC[vADD_CLAUSES];
      vEXISTS_TAC (parse_term "m:num") ----> vASM_REWRITE_TAC[]]]);;

let vEVEN_EXISTS = prove
 ((parse_term "!n. EVEN n <=> ?m. n = 2 * m"),
  vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vMATCH_MP_TAC(vCONJUNCT1(vSPEC_ALL vEVEN_EXISTS_LEMMA)) ----> vASM_REWRITE_TAC[];
    vPOP_ASSUM(vCHOOSE_THEN vSUBST1_TAC) ----> vREWRITE_TAC[vEVEN_DOUBLE]]);;

let vODD_EXISTS = prove
 ((parse_term "!n. ODD n <=> ?m. n = SUC(2 * m)"),
  vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vMATCH_MP_TAC(vCONJUNCT2(vSPEC_ALL vEVEN_EXISTS_LEMMA)) ---->
    vASM_REWRITE_TAC[vNOT_EVEN];
    vPOP_ASSUM(vCHOOSE_THEN vSUBST1_TAC) ----> vREWRITE_TAC[vODD_DOUBLE]]);;

let vEVEN_ODD_DECOMPOSITION = prove
 ((parse_term "!n. (?k m. ODD m /\\ (n = 2 EXP k * m)) <=> ~(n = 0)"),
  vMATCH_MP_TAC num_WF ----> vX_GEN_TAC (parse_term "n:num") ----> vDISCH_TAC ---->
  vDISJ_CASES_TAC(vSPEC (parse_term "n:num") vEVEN_OR_ODD) ++-->
   [vALL_TAC; vASM_MESON_TAC[vODD; vEXP; vMULT_CLAUSES]] ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vEVEN_EXISTS]) ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "m:num") vSUBST_ALL_TAC) ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC (parse_term "m:num")) ---->
  vASM_CASES_TAC (parse_term "m = 0") ----> vASM_REWRITE_TAC[vMULT_EQ_0] ++-->
   [vREWRITE_TAC[vMULT_CLAUSES; vLT] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ---->
    vREWRITE_TAC[vEXP_EQ_0; vMULT_EQ_0; vTWO; vNOT_SUC] ----> vMESON_TAC[vODD];
    vALL_TAC] ---->
  vANTS_TAC ++-->
   [vGEN_REWRITE_TAC vLAND_CONV [vGSYM(el 2 (vCONJUNCTS vMULT_CLAUSES))] ---->
    vASM_REWRITE_TAC[vLT_MULT_RCANCEL; vTWO; vLT];
    vALL_TAC] ---->
  vREWRITE_TAC[vTWO; vNOT_SUC] ----> vREWRITE_TAC[vGSYM vTWO] ---->
  vONCE_REWRITE_TAC[vSWAP_EXISTS_THM] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC (parse_term "p:num") ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "k:num") vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC (parse_term "SUC k") ----> vASM_REWRITE_TAC[vEXP; vMULT_ASSOC]);;

(* ------------------------------------------------------------------------- *)
(* Cutoff subtraction, also defined recursively. (Not the HOL88 defn.)       *)
(* ------------------------------------------------------------------------- *)

let vSUB = new_recursive_definition num_RECURSION
 (parse_term "(!m. m - 0 = m) /\\\n  (!m n. m - (SUC n) = PRE(m - n))");;

let vSUB_0 = prove
 ((parse_term "!m. (0 - m = 0) /\\ (m - 0 = m)"),
  vREWRITE_TAC[vSUB] ----> vINDUCT_TAC ----> vASM_REWRITE_TAC[vSUB; vPRE]);;

let vSUB_PRESUC = prove
 ((parse_term "!m n. PRE(SUC m - n) = m - n"),
  vGEN_TAC ----> vINDUCT_TAC ----> vASM_REWRITE_TAC[vSUB; vPRE]);;

let vSUB_SUC = prove
 ((parse_term "!m n. SUC m - SUC n = m - n"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vSUB; vPRE; vSUB_PRESUC]);;

let vSUB_REFL = prove
 ((parse_term "!n. n - n = 0"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vSUB_SUC; vSUB_0]);;

let vADD_SUB = prove
 ((parse_term "!m n. (m + n) - n = m"),
  vGEN_TAC ----> vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES; vSUB_SUC; vSUB_0]);;

let vADD_SUB2 = prove
 ((parse_term "!m n. (m + n) - m = n"),
  vONCE_REWRITE_TAC[vADD_SYM] ----> vMATCH_ACCEPT_TAC vADD_SUB);;

let vSUB_EQ_0 = prove
 ((parse_term "!m n. (m - n = 0) <=> m <= n"),
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC[vSUB_SUC; vLE_SUC; vSUB_0] ---->
  vREWRITE_TAC[vLE; vLE_0]);;

let vADD_SUBR2 = prove
 ((parse_term "!m n. m - (m + n) = 0"),
  vREWRITE_TAC[vSUB_EQ_0; vLE_ADD]);;

let vADD_SUBR = prove
 ((parse_term "!m n. n - (m + n) = 0"),
  vONCE_REWRITE_TAC[vADD_SYM] ----> vMATCH_ACCEPT_TAC vADD_SUBR2);;

let vSUB_ADD = prove
 ((parse_term "!m n. n <= m ==> ((m - n) + n = m)"),
  vREWRITE_TAC[vLE_EXISTS] ----> vREPEAT vSTRIP_TAC ---->
  vASM_REWRITE_TAC[vONCE_REWRITE_RULE[vADD_SYM] vADD_SUB] ---->
  vMATCH_ACCEPT_TAC vADD_SYM);;

let vSUB_ADD_LCANCEL = prove
 ((parse_term "!m n p. (m + n) - (m + p) = n - p"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES; vSUB_0; vSUB_SUC]);;

let vSUB_ADD_RCANCEL = prove
 ((parse_term "!m n p. (m + p) - (n + p) = m - n"),
  vONCE_REWRITE_TAC[vADD_SYM] ----> vMATCH_ACCEPT_TAC vSUB_ADD_LCANCEL);;

let vLEFT_SUB_DISTRIB = prove
 ((parse_term "!m n p. m * (n - p) = m * n - m * p"),
  vREPEAT vGEN_TAC ----> vCONV_TAC vSYM_CONV ---->
  vDISJ_CASES_TAC(vSPECL [(parse_term "n:num"); (parse_term "p:num")] vLE_CASES) ++-->
   [vFIRST_ASSUM(fun th -> vREWRITE_TAC[vREWRITE_RULE[vGSYM vSUB_EQ_0] th]) ---->
    vASM_REWRITE_TAC[vMULT_CLAUSES; vSUB_EQ_0; vLE_MULT_LCANCEL];
    vPOP_ASSUM(vCHOOSE_THEN vSUBST1_TAC -| vREWRITE_RULE[vLE_EXISTS]) ---->
    vREWRITE_TAC[vLEFT_ADD_DISTRIB] ---->
    vREWRITE_TAC[vONCE_REWRITE_RULE[vADD_SYM] vADD_SUB]]);;

let vRIGHT_SUB_DISTRIB = prove
 ((parse_term "!m n p. (m - n) * p = m * p - n * p"),
  vONCE_REWRITE_TAC[vMULT_SYM] ----> vMATCH_ACCEPT_TAC vLEFT_SUB_DISTRIB);;

let vSUC_SUB1 = prove
 ((parse_term "!n. SUC n - 1 = n"),
  vREWRITE_TAC[vONE; vSUB_SUC; vSUB_0]);;

let vEVEN_SUB = prove
 ((parse_term "!m n. EVEN(m - n) <=> m <= n \\/ (EVEN(m) <=> EVEN(n))"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "m <= n:num") ++-->
   [vASM_MESON_TAC[vSUB_EQ_0; vEVEN]; vALL_TAC] ---->
  vDISJ_CASES_TAC(vSPECL [(parse_term "m:num"); (parse_term "n:num")] vLE_CASES) ----> vASM_SIMP_TAC[] ---->
  vFIRST_ASSUM(vMP_TAC -| vAP_TERM (parse_term "EVEN") -| vMATCH_MP vSUB_ADD) ---->
  vASM_MESON_TAC[vEVEN_ADD]);;

let vODD_SUB = prove
 ((parse_term "!m n. ODD(m - n) <=> n < m /\\ ~(ODD m <=> ODD n)"),
  vREWRITE_TAC[vGSYM vNOT_EVEN; vEVEN_SUB; vDE_MORGAN_THM; vNOT_LE] ---->
  vCONV_TAC vTAUT);;

(* ------------------------------------------------------------------------- *)
(* The factorial function.                                                   *)
(* ------------------------------------------------------------------------- *)

let vFACT = new_recursive_definition num_RECURSION
  (parse_term "(FACT 0 = 1) /\\\n   (!n. FACT (SUC n) = (SUC n) * FACT(n))");;

let vFACT_LT = prove
 ((parse_term "!n. 0 < FACT n"),
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vFACT; vLT_MULT] ---->
  vREWRITE_TAC[vONE; vLT_0]);;

let vFACT_LE = prove
 ((parse_term "!n. 1 <= FACT n"),
  vREWRITE_TAC[vONE; vLE_SUC_LT; vFACT_LT]);;

let vFACT_NZ = prove
 ((parse_term "!n. ~(FACT n = 0)"),
  vREWRITE_TAC[vGSYM vLT_NZ; vFACT_LT]);;

let vFACT_MONO = prove
 ((parse_term "!m n. m <= n ==> FACT m <= FACT n"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:num") vSUBST1_TAC -| vREWRITE_RULE[vLE_EXISTS]) ---->
  vSPEC_TAC((parse_term "d:num"),(parse_term "d:num")) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vADD_CLAUSES; vLE_REFL] ---->
  vREWRITE_TAC[vFACT] ---->
  vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "FACT(m + d)") ---->
  vASM_REWRITE_TAC[] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM(el 2 (vCONJUNCTS vMULT_CLAUSES))] ---->
  vREWRITE_TAC[vLE_MULT_RCANCEL] ---->
  vREWRITE_TAC[vONE; vLE_SUC; vLE_0]);;

(* ------------------------------------------------------------------------- *)
(* More complicated theorems about exponential.                              *)
(* ------------------------------------------------------------------------- *)

let vEXP_LT_0 = prove
 ((parse_term "!n x. 0 < x EXP n <=> ~(x = 0) \\/ (n = 0)"),
  vREWRITE_TAC[vGSYM vNOT_LE; vLE; vEXP_EQ_0; vDE_MORGAN_THM]);;

let vLT_EXP = prove
 ((parse_term "!x m n. x EXP m < x EXP n <=> 2 <= x /\\ m < n \\/\n                                 (x = 0) /\\ ~(m = 0) /\\ (n = 0)"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "x = 0") ----> vASM_REWRITE_TAC[] ++-->
   [vREWRITE_TAC[vGSYM vNOT_LT; vTWO; vONE; vLT] ---->
    vSPEC_TAC ((parse_term "n:num"),(parse_term "n:num")) ----> vINDUCT_TAC ---->
    vREWRITE_TAC[vEXP; vNOT_SUC; vMULT_CLAUSES; vLT] ---->
    vSPEC_TAC ((parse_term "m:num"),(parse_term "m:num")) ----> vINDUCT_TAC ---->
    vREWRITE_TAC[vEXP; vMULT_CLAUSES; vNOT_SUC; vLT_REFL; vLT] ---->
    vREWRITE_TAC[vONE; vLT_0]; vALL_TAC] ---->
  vEQ_TAC ++-->
   [vCONV_TAC vCONTRAPOS_CONV ---->
    vREWRITE_TAC[vNOT_LT; vDE_MORGAN_THM; vNOT_LE] ---->
    vREWRITE_TAC[vTWO; vONE; vLT] ---->
    vASM_REWRITE_TAC[vSYM vONE] ---->
    vSTRIP_TAC ----> vASM_REWRITE_TAC[vEXP_ONE; vLE_REFL] ---->
    vFIRST_ASSUM(vX_CHOOSE_THEN (parse_term "d:num") vSUBST1_TAC -|
      vREWRITE_RULE[vLE_EXISTS]) ---->
    vSPEC_TAC((parse_term "d:num"),(parse_term "d:num")) ----> vINDUCT_TAC ---->
    vREWRITE_TAC[vADD_CLAUSES; vEXP; vLE_REFL] ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "1 * x EXP (n + d)") ---->
    vCONJ_TAC ++-->
     [vASM_REWRITE_TAC[vMULT_CLAUSES];
      vREWRITE_TAC[vLE_MULT_RCANCEL] ---->
      vDISJ1_TAC ----> vUNDISCH_TAC (parse_term "~(x = 0)") ---->
      vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vNOT_LE] ---->
      vREWRITE_TAC[vONE; vLT]];
    vSTRIP_TAC ---->
    vFIRST_ASSUM(vX_CHOOSE_THEN (parse_term "d:num") vSUBST1_TAC -|
      vREWRITE_RULE[vLT_EXISTS]) ---->
    vSPEC_TAC((parse_term "d:num"),(parse_term "d:num")) ----> vINDUCT_TAC ---->
    vREWRITE_TAC[vADD_CLAUSES; vEXP] ++-->
     [vMATCH_MP_TAC vLTE_TRANS ----> vEXISTS_TAC (parse_term "2 * x EXP m") ---->
      vCONJ_TAC ++-->
       [vASM_REWRITE_TAC[vMULT_2; vLT_ADD; vEXP_LT_0];
        vASM_REWRITE_TAC[vLE_MULT_RCANCEL]];
      vMATCH_MP_TAC vLTE_TRANS ---->
      vEXISTS_TAC (parse_term "x EXP (m + SUC d)") ----> vASM_REWRITE_TAC[] ---->
      vREWRITE_TAC[vADD_CLAUSES; vEXP; vMULT_ASSOC; vLE_MULT_RCANCEL] ---->
      vDISJ1_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
      vEXISTS_TAC (parse_term "x * 1") ----> vCONJ_TAC ++-->
       [vREWRITE_TAC[vMULT_CLAUSES; vLE_REFL];
        vREWRITE_TAC[vLE_MULT_LCANCEL] ----> vDISJ2_TAC ---->
        vUNDISCH_TAC (parse_term "~(x = 0)") ---->
        vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vNOT_LE] ---->
        vREWRITE_TAC[vONE; vLT]]]]);;

let vLE_EXP = prove
 ((parse_term "!x m n. x EXP m <= x EXP n <=>\n           if x = 0 then (m = 0) ==> (n = 0)\n           else (x = 1) \\/ m <= n"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vNOT_LT; vLT_EXP; vDE_MORGAN_THM] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vTWO; vLT; vONE] ---->
  vCONV_TAC(vEQT_INTRO -| vTAUT));;

let vEQ_EXP = prove
 ((parse_term "!x m n. x EXP m = x EXP n <=>\n           if x = 0 then (m = 0 <=> n = 0)\n           else (x = 1) \\/ m = n"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vLAND_CONV [vGSYM vLE_ANTISYM; vLE_EXP] ---->
  vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vLE_EXP] ---->
  vREWRITE_TAC[vGSYM vLE_ANTISYM] ----> vCONV_TAC vTAUT);;

let vEXP_MONO_LE_IMP = prove
 ((parse_term "!x y n. x <= y ==> x EXP n <= y EXP n"),
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vINDUCT_TAC ----> vASM_SIMP_TAC[vLE_MULT2; vEXP; vLE_REFL]);;

let vEXP_MONO_LT_IMP = prove
 ((parse_term "!x y n. x < y /\\ ~(n = 0) ==> x EXP n < y EXP n"),
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[vNOT_SUC; vEXP] ---->
  vDISCH_TAC ----> vMATCH_MP_TAC vLET_TRANS ----> vEXISTS_TAC (parse_term "x * y EXP n") ---->
  vASM_SIMP_TAC[vLT_IMP_LE; vLE_MULT_LCANCEL; vLT_MULT_RCANCEL; vEXP_MONO_LE_IMP;
               vEXP_EQ_0] ---->
  vASM_MESON_TAC[vCONJUNCT1 vLT]);;

let vEXP_MONO_LE = prove
 ((parse_term "!x y n. x EXP n <= y EXP n <=> x <= y \\/ n = 0"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vSTRIP_TAC ---->
  vASM_SIMP_TAC[vEXP; vLE_REFL; vEXP_MONO_LE_IMP] ---->
  vASM_MESON_TAC[vNOT_LE; vEXP_MONO_LT_IMP]);;

let vEXP_MONO_LT = prove
 ((parse_term "!x y n. x EXP n < y EXP n <=> x < y /\\ ~(n = 0)"),
  vREWRITE_TAC[vGSYM vNOT_LE; vEXP_MONO_LE; vDE_MORGAN_THM]);;

let vEXP_MONO_EQ = prove
 ((parse_term "!x y n. x EXP n = y EXP n <=> x = y \\/ n = 0"),
  vREWRITE_TAC[vGSYM vLE_ANTISYM; vEXP_MONO_LE] ----> vCONV_TAC vTAUT);;

(* ------------------------------------------------------------------------- *)
(* Division and modulus, via existence proof of their basic property.        *)
(* ------------------------------------------------------------------------- *)

let vDIVMOD_EXIST = prove
 ((parse_term "!m n. ~(n = 0) ==> ?q r. (m = q * n + r) /\\ r < n"),
  vREPEAT vSTRIP_TAC ----> vMP_TAC(vSPEC (parse_term "\\r. ?q. m = q * n + r") num_WOP) ---->
  vBETA_TAC ----> vDISCH_THEN(vMP_TAC -| fst -| vEQ_IMP_RULE) ---->
  vREWRITE_TAC[vLEFT_IMP_EXISTS_THM] ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [(parse_term "m:num"); (parse_term "0")]) ---->
  vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "r:num") vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC (parse_term "q:num")) vMP_TAC) ---->
  vDISCH_THEN(fun th ->
    vMAP_EVERY vEXISTS_TAC [(parse_term "q:num"); (parse_term "r:num")] ----> vMP_TAC th) ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vASM_REWRITE_TAC[vNOT_LT] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:num") vSUBST_ALL_TAC -|
    vREWRITE_RULE[vLE_EXISTS]) ---->
  vREWRITE_TAC[vNOT_FORALL_THM] ----> vEXISTS_TAC (parse_term "d:num") ---->
  vREWRITE_TAC[vNOT_IMP; vRIGHT_AND_EXISTS_THM] ---->
  vEXISTS_TAC (parse_term "q + 1") ----> vREWRITE_TAC[vRIGHT_ADD_DISTRIB] ---->
  vREWRITE_TAC[vMULT_CLAUSES; vADD_ASSOC; vLT_ADDR] ---->
  vASM_REWRITE_TAC[vGSYM vNOT_LE; vLE]);;

let vDIVMOD_EXIST_0 = prove
 ((parse_term "!m n. ?q r. if n = 0 then q = 0 /\\ r = m\n               else m = q * n + r /\\ r < n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_SIMP_TAC[vDIVMOD_EXIST; vRIGHT_EXISTS_AND_THM; vEXISTS_REFL]);;

let vDIVISION_0 =  new_specification ["DIV"; "MOD"]
  (vREWRITE_RULE[vSKOLEM_THM] vDIVMOD_EXIST_0);;

let vDIVISION = prove
 ((parse_term "!m n. ~(n = 0) ==> (m = m DIV n * n + m MOD n) /\\ m MOD n < n"),
  vMESON_TAC[vDIVISION_0]);;

let vDIV_ZERO = prove
 ((parse_term "!n. n DIV 0 = 0"),
  vMESON_TAC[vDIVISION_0]);;

let vMOD_ZERO = prove
 ((parse_term "!n. n MOD 0 = n"),
  vMESON_TAC[vDIVISION_0]);;

let vDIVISION_SIMP = prove
 ((parse_term "(!m n. m DIV n * n + m MOD n = m) /\\\n   (!m n. n * m DIV n + m MOD n = m)"),
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_SIMP_TAC[vDIV_ZERO; vMOD_ZERO; vMULT_CLAUSES; vADD_CLAUSES] ---->
  vASM_MESON_TAC[vDIVISION; vMULT_SYM]);;

let vEQ_DIVMOD = prove
 ((parse_term "!p m n. m DIV p = n DIV p /\\ m MOD p = n MOD p <=> m = n"),
  vMESON_TAC[vDIVISION_SIMP]);;

let vMOD_LT_EQ = prove
 ((parse_term "!m n. m MOD n < n <=> ~(n = 0)"),
  vMESON_TAC[vDIVISION; vLE_1; vCONJUNCT1 vLT]);;

let vMOD_LT_EQ_LT = prove
 ((parse_term "!m n. m MOD n < n <=> 0 < n"),
  vMESON_TAC[vDIVISION; vLE_1; vCONJUNCT1 vLT]);;

let vDIVMOD_UNIQ_LEMMA = prove
 ((parse_term "!m n q1 r1 q2 r2. ((m = q1 * n + r1) /\\ r1 < n) /\\\n                     ((m = q2 * n + r2) /\\ r2 < n)\n                     ==> (q1 = q2) /\\ (r1 = r2)"),
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN (parse_term "r1:num = r2") vMP_TAC ++-->
   [vUNDISCH_TAC (parse_term "m = q2 * n + r2") ---->
    vASM_REWRITE_TAC[] ---->
    vDISJ_CASES_THEN vMP_TAC (vSPECL [(parse_term "q1:num"); (parse_term "q2:num")] vLE_CASES) ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "d:num") vSUBST1_TAC -| vREWRITE_RULE[vLE_EXISTS]) ---->
    vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vGSYM vADD_ASSOC; vEQ_ADD_LCANCEL] ++-->
     [vDISCH_TAC ----> vUNDISCH_TAC (parse_term "r1 < n");
      vDISCH_THEN(vASSUME_TAC -| vSYM) ----> vUNDISCH_TAC (parse_term "r2 < n")] ---->
    vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vMULT_SYM] ---->
    vSPEC_TAC((parse_term "d:num"),(parse_term "d:num")) ----> vINDUCT_TAC ---->
    vREWRITE_TAC[vADD_CLAUSES; vMULT_CLAUSES;
      vGSYM vNOT_LE; vLE_ADD; vGSYM vADD_ASSOC];
    vDISCH_THEN vSUBST_ALL_TAC ----> vREWRITE_TAC[] ---->
    vCONV_TAC vSYM_CONV ---->
    vUNDISCH_TAC (parse_term "m = q1 * n + r2") ---->
    vASM_REWRITE_TAC[vEQ_ADD_RCANCEL; vEQ_MULT_RCANCEL] ---->
    vREPEAT (vUNDISCH_TAC (parse_term "r2 < n")) ---->
    vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vGSYM vNOT_LE; vLE_0]]);;

let vDIVMOD_UNIQ = prove
 ((parse_term "!m n q r. (m = q * n + r) /\\ r < n ==> (m DIV n = q) /\\ (m MOD n = r)"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN vASSUME_TAC -| vGSYM) ---->
  vMATCH_MP_TAC vDIVMOD_UNIQ_LEMMA ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "m:num"); (parse_term "n:num")] ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vDIVISION ---->
  vDISCH_TAC ----> vUNDISCH_TAC (parse_term "r < n") ---->
  vASM_REWRITE_TAC[vGSYM vNOT_LE; vLE_0]);;

let vMOD_UNIQ = prove
 ((parse_term "!m n q r. (m = q * n + r) /\\ r < n ==> (m MOD n = r)"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vDIVMOD_UNIQ th]));;

let vDIV_UNIQ = prove
 ((parse_term "!m n q r. (m = q * n + r) /\\ r < n ==> (m DIV n = q)"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vDIVMOD_UNIQ th]));;

let vDIV_0,vMOD_0 = (vCONJ_PAIR -| prove)
 ((parse_term "(!n. 0 DIV n = 0) /\\ (!n. 0 MOD n = 0)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vDIV_ZERO; vMOD_ZERO] ---->
  vMATCH_MP_TAC vDIVMOD_UNIQ ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vLT_NZ]);;

let vDIV_MULT,vMOD_MULT = (vCONJ_PAIR -| prove)
 ((parse_term "(!m n. ~(m = 0) ==> (m * n) DIV m = n) /\\\n   (!m n. (m * n) MOD m = 0)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "m = 0") ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vMOD_0] ---->
  vMATCH_MP_TAC vDIVMOD_UNIQ ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES; vMULT_AC; vLT_NZ]);;

let vMOD_LT = prove
 ((parse_term "!m n. m < n ==> m MOD n = m"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vMOD_UNIQ ---->
  vEXISTS_TAC (parse_term "0") ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES]);;

let vMOD_EQ_SELF = prove
 ((parse_term "!m n. m MOD n = m <=> n = 0 \\/ m < n"),
  vMESON_TAC[vMOD_ZERO; vMOD_LT; vDIVISION; vLE_1]);;

let vMOD_CASES = prove
 ((parse_term "!n p. n < 2 * p ==> n MOD p = if n < p then n else n - p"),
  vREPEAT vSTRIP_TAC ----> vCOND_CASES_TAC ----> vASM_SIMP_TAC[vMOD_LT] ---->
  vMATCH_MP_TAC vMOD_UNIQ ----> vEXISTS_TAC (parse_term "1") ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vNOT_LT]) ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vMULT_CLAUSES] ----> vASM_MESON_TAC[vSUB_ADD; vADD_SYM];
    vASM_MESON_TAC[vLT_ADD_RCANCEL; vSUB_ADD; vMULT_2; vLT_ADD2]]);;

let vMOD_ADD_CASES = prove
 ((parse_term "!m n p.\n        m < p /\\ n < p\n        ==> (m + n) MOD p = if m + n < p then m + n else (m + n) - p"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vMOD_CASES ---->
  vREWRITE_TAC[vMULT_2] ----> vASM_MESON_TAC[vLT_ADD2]);;

let vMOD_EQ = prove
 ((parse_term "!m n p q. m = n + q * p ==> m MOD p = n MOD p"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "p = 0") ++-->
   [vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES] ---->
    vDISCH_THEN vSUBST1_TAC ----> vREFL_TAC;
    vDISCH_THEN vSUBST1_TAC ---->
    vMATCH_MP_TAC vMOD_UNIQ ---->
    vEXISTS_TAC (parse_term "q + n DIV p") ---->
    vPOP_ASSUM(vMP_TAC -| vMATCH_MP vDIVISION) ---->
    vDISCH_THEN(vSTRIP_ASSUME_TAC -| vGSYM -| vSPEC (parse_term "n:num")) ---->
    vASM_REWRITE_TAC[vRIGHT_ADD_DISTRIB; vGSYM vADD_ASSOC] ---->
    vMATCH_ACCEPT_TAC vADD_SYM]);;

let vDIV_LE = prove
 ((parse_term "!m n. m DIV n <= m"),
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vDIV_ZERO; vLE_0] ---->
  vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vRAND_CONV [vMATCH_MP vDIVISION th]) ---->
  vUNDISCH_TAC (parse_term "~(n = 0)") ----> vSPEC_TAC((parse_term "n:num"),(parse_term "n:num")) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vMULT_CLAUSES; vGSYM vADD_ASSOC; vLE_ADD]);;

let vDIV_MUL_LE = prove
 ((parse_term "!m n. n * (m DIV n) <= m"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vLE_0] ---->
  vPOP_ASSUM(vMP_TAC -| vSPEC (parse_term "m:num") -| vMATCH_MP vDIVISION) ---->
  vDISCH_THEN(fun th -> vGEN_REWRITE_TAC vRAND_CONV [vCONJUNCT1 th]) ---->
  vREWRITE_TAC[vLE_ADD; vMULT_AC]);;

let vMOD_LE_TWICE = prove
 ((parse_term "!m n. 0 < m /\\ m <= n ==> 2 * n MOD m <= n"),
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "2 * m <= n") ++-->
   [vTRANS_TAC vLE_TRANS (parse_term "2 * m") ---->
    vASM_SIMP_TAC[vLE_MULT_LCANCEL; vDIVISION; vLT_IMP_LE; vLE_1];
    vRULE_ASSUM_TAC(vREWRITE_RULE[vNOT_LE])] ---->
  vTRANS_TAC vLE_TRANS (parse_term "m + n MOD m") ---->
  vASM_SIMP_TAC[vMULT_2; vLE_ADD_RCANCEL; vDIVISION; vLT_IMP_LE; vLE_1] ---->
  vONCE_REWRITE_TAC[vADD_SYM] ---->
  vSUBGOAL_THEN (parse_term "n MOD m = n - m")
   (fun th -> vASM_SIMP_TAC[vLE_REFL; vSUB_ADD; th]) ---->
  vMATCH_MP_TAC vMOD_UNIQ ----> vEXISTS_TAC (parse_term "1") ---->
  vONCE_REWRITE_TAC[vADD_SYM] ----> vASM_SIMP_TAC[vMULT_CLAUSES; vSUB_ADD] ---->
  vONCE_REWRITE_TAC[vMESON[vLT_ADD_RCANCEL]
   (parse_term "n - m:num < m <=> (n - m) + m < m + m")] ---->
  vASM_SIMP_TAC[vGSYM vMULT_2; vSUB_ADD]);;

let vDIV_1,vMOD_1 = (vCONJ_PAIR -| prove)
 ((parse_term "(!n. n DIV 1 = n) /\\ (!n. n MOD 1 = 0)"),
  vSIMP_TAC[vAND_FORALL_THM] ----> vGEN_TAC ----> vMATCH_MP_TAC vDIVMOD_UNIQ ---->
  vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES] ----> vREWRITE_TAC[vONE; vLT]);;

let vDIV_LT = prove
 ((parse_term "!m n. m < n ==> m DIV n = 0"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDIV_UNIQ ----> vEXISTS_TAC (parse_term "m:num") ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES]);;

let vMOD_MOD = prove
 ((parse_term "!m n p. (m MOD (n * p)) MOD n = m MOD n"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "p = 0") ----> vASM_REWRITE_TAC[vMOD_ZERO; vMULT_CLAUSES] ---->
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vMOD_ZERO; vMULT_CLAUSES] ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vMOD_EQ ---->
  vEXISTS_TAC (parse_term "m DIV (n * p) * p") ---->
  vMP_TAC(vSPECL [(parse_term "m:num"); (parse_term "n * p:num")] vDIVISION) ---->
  vASM_REWRITE_TAC[vMULT_EQ_0; vMULT_AC; vADD_AC] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[vGSYM th]));;

let vMOD_MOD_REFL = prove
 ((parse_term "!m n. (m MOD n) MOD n = m MOD n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vMOD_ZERO] ---->
  vMP_TAC(vSPECL [(parse_term "m:num"); (parse_term "n:num"); (parse_term "1")] vMOD_MOD) ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vMULT_EQ_0] ---->
  vREWRITE_TAC[vONE; vNOT_SUC]);;

let vMOD_MOD_LE = prove
 ((parse_term "!m n p. ~(n = 0) /\\ n <= p ==> (m MOD n) MOD p = m MOD n"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vMOD_LT ---->
  vASM_MESON_TAC[vDIVISION; vLTE_TRANS]);;

let vMOD_EVEN_2 = prove
 ((parse_term "!m n. EVEN n ==> m MOD n MOD 2 = m MOD 2"),
  vSIMP_TAC[vEVEN_EXISTS; vLEFT_IMP_EXISTS_THM; vMOD_MOD]);;

let vDIV_MULT2 = prove
 ((parse_term "!m n p. ~(m = 0) ==> ((m * n) DIV (m * p) = n DIV p)"),
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "p = 0") ---->
  vASM_REWRITE_TAC[vDIV_ZERO; vMULT_CLAUSES] ---->
  vMATCH_MP_TAC vDIV_UNIQ ----> vEXISTS_TAC (parse_term "m * (n MOD p)") ---->
  vASM_SIMP_TAC[vLT_MULT_LCANCEL; vDIVISION] ---->
  vONCE_REWRITE_TAC[vAC vMULT_AC (parse_term "a * b * c:num = b * a * c")] ---->
  vREWRITE_TAC[vGSYM vLEFT_ADD_DISTRIB; vEQ_MULT_LCANCEL] ---->
  vASM_SIMP_TAC[vGSYM vDIVISION]);;

let vMOD_MULT2 = prove
 ((parse_term "!m n p. (m * n) MOD (m * p) = m * n MOD p"),
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "p = 0") ---->
  vASM_REWRITE_TAC[vMOD_ZERO; vMULT_CLAUSES] ----> vASM_CASES_TAC (parse_term "m = 0") ---->
  vASM_REWRITE_TAC[vMOD_ZERO; vMULT_CLAUSES] ---->
  vMATCH_MP_TAC vMOD_UNIQ ----> vEXISTS_TAC (parse_term "n DIV p") ---->
  vASM_SIMP_TAC[vLT_MULT_LCANCEL; vDIVISION] ---->
  vONCE_REWRITE_TAC[vAC vMULT_AC (parse_term "a * b * c:num = b * a * c")] ---->
  vREWRITE_TAC[vGSYM vLEFT_ADD_DISTRIB; vEQ_MULT_LCANCEL] ---->
  vASM_SIMP_TAC[vGSYM vDIVISION]);;

let vMOD_EXISTS = prove
 ((parse_term "!m n. (?q. m = n * q) <=> if n = 0 then (m = 0) else (m MOD n = 0)"),
  vREPEAT vGEN_TAC ----> vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vMULT_CLAUSES] ---->
  vEQ_TAC ----> vSTRIP_TAC ----> vASM_SIMP_TAC[vMOD_MULT] ---->
  vEXISTS_TAC (parse_term "m DIV n") ---->
  vSUBGOAL_THEN (parse_term "m = (m DIV n) * n + m MOD n")
   (fun th -> vGEN_REWRITE_TAC vLAND_CONV [th]) ++-->
   [vASM_MESON_TAC[vDIVISION]; vASM_REWRITE_TAC[vADD_CLAUSES; vMULT_AC]]);;

let vLE_RDIV_EQ = prove
 ((parse_term "!a b n. ~(a = 0) ==> (n <= b DIV a <=> a * n <= b)"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "a * (b DIV a)") ---->
    vASM_REWRITE_TAC[vDIV_MUL_LE; vLE_MULT_LCANCEL];
    vSUBGOAL_THEN (parse_term "a * n < a * (b DIV a + 1)") vMP_TAC ++-->
     [vMATCH_MP_TAC vLET_TRANS ----> vEXISTS_TAC (parse_term "(b DIV a) * a + b MOD a") ---->
      vCONJ_TAC ++--> [vASM_MESON_TAC[vDIVISION]; vALL_TAC] ---->
      vSIMP_TAC[vLEFT_ADD_DISTRIB; vMULT_SYM; vMULT_CLAUSES; vLT_ADD_LCANCEL] ---->
      vASM_MESON_TAC[vDIVISION];
      vASM_REWRITE_TAC[vLT_MULT_LCANCEL; vGSYM vADD1; vLT_SUC_LE]]]);;

let vRDIV_LT_EQ = prove
 ((parse_term "!a b n. ~(a = 0) ==> (b DIV a < n <=> b < a * n)"),
  vSIMP_TAC[vGSYM vNOT_LE; vLE_RDIV_EQ]);;

let vLE_LDIV_EQ = prove
 ((parse_term "!a b n. ~(a = 0) ==> (b DIV a <= n <=> b < a * (n + 1))"),
  vREPEAT vSTRIP_TAC ----> vONCE_REWRITE_TAC[vGSYM vNOT_LT] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vLE_SUC_LT] ---->
  vASM_SIMP_TAC[vLE_RDIV_EQ] ----> vREWRITE_TAC[vNOT_LT; vNOT_LE; vADD1]);;

let vLDIV_LT_EQ = prove
 ((parse_term "!a b n. ~(a = 0) ==> (n < b DIV a <=> a * (n + 1) <= b)"),
  vSIMP_TAC[vGSYM vNOT_LE; vLE_LDIV_EQ]);;

let vLE_LDIV = prove
 ((parse_term "!a b n. ~(a = 0) /\\ b <= a * n ==> b DIV a <= n"),
  vSIMP_TAC[vLE_LDIV_EQ; vLEFT_ADD_DISTRIB; vMULT_CLAUSES] ---->
  vMESON_TAC[vLT_ADD; vLT_NZ; vLET_TRANS]);;

let vDIV_MONO = prove
 ((parse_term "!m n p. m <= n ==> m DIV p <= n DIV p"),
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "p = 0") ---->
  vASM_REWRITE_TAC[vDIV_ZERO; vLE_REFL] ---->
  vMATCH_MP_TAC(vMESON[vLE_REFL] (parse_term "(!k:num. k <= a ==> k <= b) ==> a <= b")) ---->
  vASM_SIMP_TAC[vLE_RDIV_EQ] ----> vASM_MESON_TAC[vLE_TRANS]);;

let vDIV_MONO_LT = prove
 ((parse_term "!m n p. ~(p = 0) /\\ m + p <= n ==> m DIV p < n DIV p"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC(vMESON[vADD1; vLE_SUC_LT; vLE_REFL]
   (parse_term "(!k:num. k <= a ==> k + 1 <= b) ==> a < b")) ---->
  vASM_SIMP_TAC[vLE_RDIV_EQ; vLEFT_ADD_DISTRIB; vMULT_CLAUSES] ---->
  vASM_MESON_TAC[vLE_REFL; vLE_TRANS; vLE_ADD2; vADD_SYM]);;

let vDIV_EQ_0 = prove
 ((parse_term "!m n. ~(n = 0) ==> ((m DIV n = 0) <=> m < n)"),
  vREPEAT(vSTRIP_TAC |---> vEQ_TAC) ++-->
   [vFIRST_ASSUM(vSUBST1_TAC -| vCONJUNCT1 -| vSPEC (parse_term "m:num") -| vMATCH_MP vDIVISION) ---->
    vASM_SIMP_TAC[vMULT_CLAUSES; vADD_CLAUSES; vDIVISION];
    vMATCH_MP_TAC vDIV_UNIQ ----> vEXISTS_TAC (parse_term "m:num") ---->
    vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES]]);;

let vMOD_DIV_EQ_0 = prove
 ((parse_term "!m n. ~(n = 0) ==> (m MOD n) DIV n = 0"),
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN (fun th -> vIMP_REWRITE_TAC [th; vDIV_EQ_0; vMOD_LT_EQ]));;

let vMOD_EQ_0 = prove
 ((parse_term "!m n. (m MOD n = 0) <=> ?q. m = q * n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vMOD_ZERO] ---->
  vREPEAT(vSTRIP_TAC |---> vEQ_TAC) ++-->
   [vFIRST_ASSUM(vSUBST1_TAC -| vCONJUNCT1 -| vSPEC (parse_term "m:num") -| vMATCH_MP vDIVISION) ---->
    vASM_SIMP_TAC[vMULT_CLAUSES; vADD_CLAUSES; vDIVISION] ----> vMESON_TAC[];
    vMATCH_MP_TAC vMOD_UNIQ ----> vASM_SIMP_TAC[vADD_CLAUSES; vMULT_AC] ---->
    vASM_MESON_TAC[vNOT_LE; vCONJUNCT1 vLE]]);;

let vDIV_EQ_SELF = prove
 ((parse_term "!m n. m DIV n = m <=> m = 0 \\/ n = 1"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "m = 0") ----> vASM_REWRITE_TAC[vDIV_0] ---->
  vASM_CASES_TAC (parse_term "n = 1") ----> vASM_REWRITE_TAC[vDIV_1] ---->
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vDIV_ZERO] ---->
  vMATCH_MP_TAC vLT_IMP_NE ----> vASM_SIMP_TAC[vRDIV_LT_EQ] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM(el 2 (vCONJUNCTS vMULT_CLAUSES))] ---->
  vASM_REWRITE_TAC[vLT_MULT_RCANCEL] ---->
  vREWRITE_TAC[vGSYM vNOT_LE; vONE; vLE] ----> vASM_REWRITE_TAC[vGSYM vONE]);;

let vMOD_REFL = prove
 ((parse_term "!n. n MOD n = 0"),
  vSIMP_TAC[vMOD_EQ_0] ----> vMESON_TAC[vMULT_CLAUSES]);;

let vEVEN_MOD = prove
 ((parse_term "!n. EVEN(n) <=> n MOD 2 = 0"),
  vREWRITE_TAC[vEVEN_EXISTS; vMOD_EQ_0] ----> vMESON_TAC[vMULT_SYM]);;

let vODD_MOD = prove
 ((parse_term "!n. ODD(n) <=> n MOD 2 = 1"),
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vNOT_EVEN; vEVEN_MOD] ---->
  vSUBGOAL_THEN (parse_term "n MOD 2 < 2") vMP_TAC ++-->
   [vSIMP_TAC[vDIVISION; vTWO; vNOT_SUC]; vALL_TAC] ---->
  vSPEC_TAC((parse_term "n MOD 2"),(parse_term "n:num")) ---->
  vREWRITE_TAC[vTWO; vONE; vLT] ----> vMESON_TAC[vNOT_SUC]);;

let vMOD_2_CASES = prove
 ((parse_term "!n. n MOD 2 = if EVEN n then 0 else 1"),
  vMESON_TAC[vEVEN_MOD; vODD_MOD; vNOT_ODD]);;

let vEVEN_MOD_EVEN = prove
 ((parse_term "!m n. EVEN n ==> (EVEN(m MOD n) <=> EVEN m)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vEVEN_MOD] ---->
  vASM_SIMP_TAC[vMOD_EVEN_2]);;

let vODD_MOD_EVEN = prove
 ((parse_term "!m n. EVEN n ==> (ODD(m MOD n) <=> ODD m)"),
  vSIMP_TAC[vGSYM vNOT_EVEN; vEVEN_MOD_EVEN]);;

let vHALF_DOUBLE = prove
 ((parse_term "(!n. (2 * n) DIV 2 = n) /\\ (!n. (n * 2) DIV 2 = n)"),
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vMULT_SYM] ---->
  vSIMP_TAC[vDIV_MULT; vTWO; vNOT_SUC]);;

let vDOUBLE_HALF = prove
 ((parse_term "(!n. EVEN n ==> 2 * n DIV 2 = n) /\\\n   (!n. EVEN n ==> n DIV 2 * 2 = n)"),
  vSIMP_TAC[vEVEN_EXISTS; vLEFT_IMP_EXISTS_THM; vHALF_DOUBLE] ---->
  vREWRITE_TAC[vMULT_SYM]);;

let vMOD_MULT_RMOD = prove
 ((parse_term "!m n p. (m * (p MOD n)) MOD n = (m * p) MOD n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vMOD_ZERO] ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vMOD_EQ ----> vEXISTS_TAC (parse_term "m * p DIV n") ---->
  vREWRITE_TAC[vGSYM vMULT_ASSOC; vGSYM vLEFT_ADD_DISTRIB] ---->
  vREWRITE_TAC[vEQ_MULT_LCANCEL] ----> vDISJ2_TAC ---->
  vONCE_REWRITE_TAC[vADD_SYM] ----> vASM_SIMP_TAC[vDIVISION]);;

let vMOD_MULT_LMOD = prove
 ((parse_term "!m n p. ((m MOD n) * p) MOD n = (m * p) MOD n"),
  vONCE_REWRITE_TAC[vMULT_SYM] ----> vSIMP_TAC[vMOD_MULT_RMOD]);;

let vMOD_MULT_MOD2 = prove
 ((parse_term "!m n p. ((m MOD n) * (p MOD n)) MOD n = (m * p) MOD n"),
  vSIMP_TAC[vMOD_MULT_RMOD; vMOD_MULT_LMOD]);;

let vMOD_EXP_MOD = prove
 ((parse_term "!m n p. ((m MOD n) EXP p) MOD n = (m EXP p) MOD n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vMOD_ZERO] ----> vSPEC_TAC((parse_term "p:num"),(parse_term "p:num")) ---->
  vINDUCT_TAC ----> vASM_REWRITE_TAC[vEXP] ----> vASM_SIMP_TAC[vMOD_MULT_LMOD] ---->
  vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "(m * ((m MOD n) EXP p) MOD n) MOD n") ----> vCONJ_TAC ++-->
   [vALL_TAC; vASM_REWRITE_TAC[]] ---->
  vASM_SIMP_TAC[vMOD_MULT_RMOD]);;

let vMOD_MULT_ADD = prove
 ((parse_term "(!m n p. (m * n + p) MOD n = p MOD n) /\\\n   (!m n p. (n * m + p) MOD n = p MOD n) /\\\n   (!m n p. (p + m * n) MOD n = p MOD n) /\\\n   (!m n p. (p + n * m) MOD n = p MOD n)"),
  vMATCH_MP_TAC(vTAUT (parse_term "(p ==> q) /\\ p ==> p /\\ q")) ---->
  vCONJ_TAC ++--> [vSIMP_TAC[vMULT_AC; vADD_AC]; vREPEAT vGEN_TAC] ---->
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES] ---->
  vMATCH_MP_TAC vMOD_UNIQ ----> vEXISTS_TAC (parse_term "m + p DIV n") ---->
  vASM_SIMP_TAC[vRIGHT_ADD_DISTRIB; vGSYM vADD_ASSOC; vEQ_ADD_LCANCEL; vDIVISION]);;

let vDIV_MULT_ADD = prove
 ((parse_term "(!a b n. ~(n = 0) ==> (a * n + b) DIV n = a + b DIV n) /\\\n   (!a b n. ~(n = 0) ==> (n * a + b) DIV n = a + b DIV n) /\\\n   (!a b n. ~(n = 0) ==> (b + a * n) DIV n = b DIV n + a) /\\\n   (!a b n. ~(n = 0) ==> (b + n * a) DIV n = b DIV n + a)"),
  vMATCH_MP_TAC(vTAUT (parse_term "(p ==> q) /\\ p ==> p /\\ q")) ---->
  vCONJ_TAC ++--> [vSIMP_TAC[vMULT_AC; vADD_AC]; vREPEAT vSTRIP_TAC] ---->
  vMATCH_MP_TAC vDIV_UNIQ ----> vEXISTS_TAC (parse_term "b MOD n") ---->
  vREWRITE_TAC[vRIGHT_ADD_DISTRIB; vGSYM vADD_ASSOC] ---->
  vASM_MESON_TAC[vDIVISION]);;

let vMOD_ADD_MOD = prove
 ((parse_term "!a b n. (a MOD n + b MOD n) MOD n = (a + b) MOD n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vMOD_ZERO] ---->
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vMOD_EQ ---->
  vEXISTS_TAC (parse_term "a DIV n + b DIV n") ----> vREWRITE_TAC[vRIGHT_ADD_DISTRIB] ---->
  vONCE_REWRITE_TAC[vAC vADD_AC (parse_term "(a + b) + (c + d) = (c + a) + (d + b)")] ---->
  vBINOP_TAC ----> vASM_SIMP_TAC[vDIVISION]);;

let vDIV_ADD_MOD = prove
 ((parse_term "!a b n. ~(n = 0)\n           ==> (((a + b) MOD n = a MOD n + b MOD n) <=>\n                ((a + b) DIV n = a DIV n + b DIV n))"),
  vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vDIVISION) ---->
  vDISCH_THEN(fun th -> vMAP_EVERY (vMP_TAC -| vCONJUNCT1 -| vC vSPEC th)
    [(parse_term "a + b:num"); (parse_term "a:num"); (parse_term "b:num")]) ---->
  vDISCH_THEN(fun th1 -> vDISCH_THEN(fun th2 ->
    vMP_TAC(vMK_COMB(vAP_TERM (parse_term "(+)") th2,th1)))) ---->
  vDISCH_THEN(fun th -> vGEN_REWRITE_TAC (funpow 2 vLAND_CONV) [th]) ---->
  vONCE_REWRITE_TAC[vAC vADD_AC (parse_term "(a + b) + c + d = (a + c) + (b + d)")] ---->
  vREWRITE_TAC[vGSYM vRIGHT_ADD_DISTRIB] ---->
  vDISCH_THEN(fun th -> vEQ_TAC ----> vDISCH_TAC ----> vMP_TAC th) ---->
  vASM_REWRITE_TAC[vEQ_ADD_RCANCEL; vEQ_ADD_LCANCEL; vEQ_MULT_RCANCEL] ---->
  vREWRITE_TAC[vEQ_SYM_EQ]);;

let vDIV_REFL = prove
 ((parse_term "!n. ~(n = 0) ==> (n DIV n = 1)"),
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDIV_UNIQ ---->
  vEXISTS_TAC (parse_term "0") ----> vREWRITE_TAC[vADD_CLAUSES; vMULT_CLAUSES] ---->
  vPOP_ASSUM vMP_TAC ----> vSPEC_TAC((parse_term "n:num"),(parse_term "n:num")) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vLT_0]);;

let vMOD_LE = prove
 ((parse_term "!m n. m MOD n <= m"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vMOD_ZERO; vLE_REFL] ----> vFIRST_ASSUM
  (fun th -> vGEN_REWRITE_TAC vRAND_CONV
   [vMATCH_MP vDIVISION th]) ---->
  vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vLE_ADD]);;

let vDIV_MONO2 = prove
 ((parse_term "!m n p. ~(p = 0) /\\ p <= m ==> n DIV m <= n DIV p"),
  vREPEAT vSTRIP_TAC ----> vASM_SIMP_TAC[vLE_RDIV_EQ] ---->
  vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC (parse_term "m * n DIV m") ---->
  vASM_REWRITE_TAC[vLE_MULT_RCANCEL] ----> vONCE_REWRITE_TAC[vMULT_SYM] ---->
  vMP_TAC(vSPECL [(parse_term "n:num"); (parse_term "m:num")] vDIVISION) ----> vASM_MESON_TAC[vLE_ADD; vLE]);;

let vDIV_LE_EXCLUSION = prove
 ((parse_term "!a b c d. ~(b = 0) /\\ b * c < (a + 1) * d ==> c DIV d <= a DIV b"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "d = 0") ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vLT] ----> vSTRIP_TAC ---->
  vMATCH_MP_TAC(vMESON[vLE_REFL] (parse_term "(!k:num. k <= a ==> k <= b) ==> a <= b")) ---->
  vX_GEN_TAC (parse_term "k:num") ---->
  vSUBGOAL_THEN (parse_term "b * d * k <= b * c ==> (b * k) * d < (a + 1) * d") vMP_TAC ++-->
   [vASM_MESON_TAC[vLET_TRANS; vMULT_AC]; vALL_TAC] ---->
  vMATCH_MP_TAC vMONO_IMP ---->
  vASM_SIMP_TAC[vLE_MULT_LCANCEL; vLT_MULT_RCANCEL; vLE_RDIV_EQ] ---->
  vREWRITE_TAC[vGSYM vADD1; vLT_SUC_LE]);;

let vDIV_EQ_EXCLUSION = prove
 ((parse_term "!a b c d.\n        b * c < (a + 1) * d /\\ a * d < (c + 1) * b ==> (a DIV b = c DIV d)"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "b = 0") ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vLT] ---->
  vASM_CASES_TAC (parse_term "d = 0") ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vLT] ---->
  vASM_MESON_TAC[vMULT_SYM; vLE_ANTISYM; vDIV_LE_EXCLUSION]);;

let vMULT_DIV_LE = prove
 ((parse_term "!m n p. m * (n DIV p) <= (m * n) DIV p"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "p = 0") ---->
  vASM_REWRITE_TAC[vLE_REFL; vDIV_ZERO; vMULT_CLAUSES] ---->
  vASM_SIMP_TAC[vLE_RDIV_EQ] ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC (parse_term "n:num") -| vMATCH_MP vDIVISION) ---->
  vDISCH_THEN(fun th ->
    vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vCONJUNCT1 th]) ---->
  vREWRITE_TAC[vLEFT_ADD_DISTRIB] ----> vREWRITE_TAC[vMULT_AC; vLE_ADD]);;

let vDIV_DIV = prove
 ((parse_term "!m n p. (m DIV n) DIV p = m DIV (n * p)"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "p = 0") ----> vASM_REWRITE_TAC[vMULT_CLAUSES; vDIV_ZERO] ---->
  vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vDIV_0; vMULT_CLAUSES; vDIV_ZERO] ---->
  vREWRITE_TAC[vMULT_EQ_0; vDE_MORGAN_THM] ----> vREPEAT vSTRIP_TAC ---->
  vMATCH_MP_TAC(vMESON[vLE_ANTISYM] (parse_term "(!k. k <= m <=> k <= n) ==> m = n")) ---->
  vASM_SIMP_TAC[vLE_RDIV_EQ; vMULT_EQ_0; vMULT_ASSOC]);;

let vDIV_MOD = prove
 ((parse_term "!m n p. (m DIV n) MOD p = (m MOD (n * p)) DIV n"),
  vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "p = 0") ----> vASM_REWRITE_TAC[vMOD_ZERO; vMULT_CLAUSES] ---->
  vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vMOD_0; vMULT_CLAUSES; vDIV_ZERO] ---->
  vMATCH_MP_TAC(vMESON[vLE_ANTISYM] (parse_term "(!k. k <= m <=> k <= n) ==> m = n")) ---->
  vX_GEN_TAC (parse_term "k:num") ----> vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC (parse_term "k + p * ((m DIV n) DIV p) <= (m DIV n)") ----> vCONJ_TAC ++-->
   [vMP_TAC(vSPECL [(parse_term "m DIV n"); (parse_term "p:num")] vDIVISION) ----> vASM_REWRITE_TAC[];
    vMP_TAC(vSPECL [(parse_term "m:num"); (parse_term "n * p:num")] vDIVISION) ---->
    vASM_SIMP_TAC[vLE_RDIV_EQ; vMULT_EQ_0; vDIV_DIV; vLEFT_ADD_DISTRIB]] ---->
  vREWRITE_TAC[vMULT_AC] ----> vMESON_TAC[vADD_SYM; vMULT_SYM; vLE_ADD_RCANCEL]);;

let vMOD_MULT_MOD = prove
 ((parse_term "!m n p. m MOD (n * p) = n * (m DIV n) MOD p + m MOD n"),
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC (parse_term "n = 0") ---->
  vASM_REWRITE_TAC[vMULT_CLAUSES; vMOD_ZERO; vADD_CLAUSES] ---->
  vASM_CASES_TAC (parse_term "p = 0") ++-->
   [vASM_REWRITE_TAC[vMULT_CLAUSES; vMOD_ZERO] ---->
    vASM_METIS_TAC[vDIVISION; vMULT_SYM];
    vALL_TAC] ---->
  vMATCH_MP_TAC(vMESON[vEQ_ADD_LCANCEL] (parse_term "(?a. a + x = a + y) ==> x = y")) ---->
  vEXISTS_TAC (parse_term "m DIV n DIV p * n * p") ---->
  vREWRITE_TAC[vDIVISION_SIMP; vDIV_DIV] ---->
  vREWRITE_TAC[vAC vMULT_AC (parse_term "d * n * p = n * (d * p)")] ---->
  vREWRITE_TAC[vGSYM vLEFT_ADD_DISTRIB; vADD_ASSOC; vGSYM vDIV_DIV] ---->
  vREWRITE_TAC[vDIVISION_SIMP]);;

let vMOD_MOD_EXP_MIN = prove
 ((parse_term "!x p m n. x MOD (p EXP m) MOD (p EXP n) = x MOD (p EXP (MIN m n))"),
  vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC (parse_term "p = 0") ++-->
   [vASM_REWRITE_TAC[vEXP_ZERO; vMIN] ----> vASM_CASES_TAC (parse_term "m = 0") ---->
    vASM_REWRITE_TAC[vMOD_ZERO; vMOD_1; vMOD_0; vLE_0] ---->
    vASM_CASES_TAC (parse_term "m:num <= n") ----> vASM_REWRITE_TAC[] ---->
    vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ----> vASM_MESON_TAC[vLE];
    vREWRITE_TAC[vMIN]] ---->
   vASM_CASES_TAC (parse_term "m:num <= n") ----> vASM_REWRITE_TAC[] ++-->
   [vFIRST_X_ASSUM(vCHOOSE_THEN vSUBST1_TAC -| vGEN_REWRITE_RULE vI [vLE_EXISTS]) ---->
    vMATCH_MP_TAC vMOD_LT ----> vMATCH_MP_TAC vLTE_TRANS ---->
    vEXISTS_TAC (parse_term "p EXP m") ---->
    vASM_SIMP_TAC[vDIVISION; vEXP_EQ_0; vLE_EXP; vLE_ADD];
    vSUBGOAL_THEN (parse_term "?d. m = n + d") (vCHOOSE_THEN vSUBST1_TAC) ++-->
     [vASM_MESON_TAC[vLE_CASES; vLE_EXISTS];
      vASM_SIMP_TAC[vEXP_ADD; vMOD_MOD; vMULT_EQ_0; vEXP_EQ_0]]]);;

let vDIV_EXP,vMOD_EXP = (vCONJ_PAIR -| prove)
 ((parse_term "(!m n p. ~(m = 0)\n            ==> (m EXP n) DIV (m EXP p) =\n                if p <= n then m EXP (n - p)\n                else if m = 1 then 1 else 0) /\\\n   (!m n p. ~(m = 0)\n            ==> (m EXP n) MOD (m EXP p) =\n                if p <= n \\/ m = 1 then 0 else m EXP n)"),
  vREWRITE_TAC[vAND_FORALL_THM] ----> vREPEAT vGEN_TAC ---->
  vASM_CASES_TAC (parse_term "m = 0") ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vDIVMOD_UNIQ ---->
  vASM_CASES_TAC (parse_term "p:num <= n") ---->
  vASM_SIMP_TAC[vGSYM vEXP_ADD; vEXP_LT_0; vSUB_ADD; vADD_CLAUSES] ---->
  vASM_CASES_TAC (parse_term "m = 1") ---->
  vASM_REWRITE_TAC[vEXP_ONE; vADD_CLAUSES; vMULT_CLAUSES; vLT_EXP] ---->
  vREWRITE_TAC[vLT; vGSYM vNOT_LT; vONE; vTWO] ---->
  vASM_REWRITE_TAC[vSYM vONE; vGSYM vNOT_LE]);;

let vFORALL_LT_MOD_THM = prove
 ((parse_term "!P n. (!a. a < n ==> P a) <=> n = 0 \\/ !a. P(a MOD n)"),
  vMESON_TAC[vLT; vMOD_EQ_SELF; vMOD_LT_EQ]);;

let vFORALL_MOD_THM = prove
 ((parse_term "!P n. ~(n = 0) ==> ((!a. P(a MOD n)) <=> (!a. a < n ==> P a))"),
  vSIMP_TAC[vFORALL_LT_MOD_THM]);;

let vEXISTS_LT_MOD_THM = prove
 ((parse_term "!P n. (?a. a < n /\\ P a) <=> ~(n = 0) /\\ ?a. P(a MOD n)"),
  vMESON_TAC[vLT; vMOD_EQ_SELF; vMOD_LT_EQ]);;

let vEXISTS_MOD_THM = prove
 ((parse_term "!P n. ~(n = 0) ==> ((?a. P(a MOD n)) <=> (?a. a < n /\\ P a))"),
  vSIMP_TAC[vEXISTS_LT_MOD_THM]);;

(* ------------------------------------------------------------------------- *)
(* Theorems for eliminating cutoff subtraction, predecessor, DIV and MOD.    *)
(* We have versions that introduce universal or existential quantifiers.     *)
(* ------------------------------------------------------------------------- *)

let vPRE_ELIM_THM = prove
 ((parse_term "P(PRE n) <=> !m. n = SUC m \\/ m = 0 /\\ n = 0 ==> P m"),
  vSPEC_TAC((parse_term "n:num"),(parse_term "n:num")) ----> vINDUCT_TAC ---->
  vREWRITE_TAC[vNOT_SUC; vSUC_INJ; vPRE] ----> vMESON_TAC[]);;

let vPRE_ELIM_THM' = prove
 ((parse_term "P(PRE n) <=> ?m. (n = SUC m \\/ m = 0 /\\ n = 0) /\\ P m"),
  vMP_TAC(vINST [(parse_term "\\x:num. ~P x"),(parse_term "P:num->bool")] vPRE_ELIM_THM) ----> vMESON_TAC[]);;

let vSUB_ELIM_THM = prove
 ((parse_term "P(a - b) <=> !d. a = b + d \\/ a < b /\\ d = 0 ==> P d"),
  vDISJ_CASES_TAC(vSPECL [(parse_term "a:num"); (parse_term "b:num")] vLTE_CASES) ++-->
   [vASM_MESON_TAC[vNOT_LT; vSUB_EQ_0; vLT_IMP_LE; vLE_ADD]; vALL_TAC] ---->
  vFIRST_ASSUM(vX_CHOOSE_THEN (parse_term "e:num") vSUBST1_TAC -| vREWRITE_RULE[vLE_EXISTS]) ---->
  vSIMP_TAC[vADD_SUB2; vGSYM vNOT_LE; vLE_ADD; vEQ_ADD_LCANCEL] ----> vMESON_TAC[]);;

let vSUB_ELIM_THM' = prove
 ((parse_term "P(a - b) <=> ?d. (a = b + d \\/ a < b /\\ d = 0) /\\ P d"),
  vMP_TAC(vINST [(parse_term "\\x:num. ~P x"),(parse_term "P:num->bool")] vSUB_ELIM_THM) ----> vMESON_TAC[]);;

let vDIVMOD_ELIM_THM = prove
 ((parse_term "P (m DIV n) (m MOD n) <=>\n        !q r. n = 0 /\\ q = 0 /\\ r = m \\/ m = q * n + r /\\ r < n ==> P q r"),
  vASM_CASES_TAC (parse_term "n = 0") ----> vASM_REWRITE_TAC[] ++-->
   [vASM_MESON_TAC[vDIVISION_0; vLT];
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vDIVISION) ----> vMESON_TAC[vDIVMOD_UNIQ]]);;

let vDIVMOD_ELIM_THM' = prove
 ((parse_term "P (m DIV n) (m MOD n) <=>\n        ?q r. (n = 0 /\\ q = 0 /\\ r = m \\/ m = q * n + r /\\ r < n) /\\ P q r"),
  vMP_TAC(vINST [(parse_term "\\x:num y:num. ~P x y"),(parse_term "P:num->num->bool")] vDIVMOD_ELIM_THM) ---->
  vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Pushing and pulling to combine nested MOD terms into a single MOD.        *)
(* ------------------------------------------------------------------------- *)

let vMOD_DOWN_CONV =
  let vMOD_SUC_MOD = vMETIS[vADD1; vMOD_ADD_MOD; vMOD_MOD_REFL]
   (parse_term "(SUC(m MOD n)) MOD n = SUC m MOD n") in
  let addmul_conv = vGEN_REWRITE_CONV vI
    [vGSYM vMOD_SUC_MOD; vGSYM vMOD_ADD_MOD; vGSYM vMOD_MULT_MOD2; vGSYM vMOD_EXP_MOD]
  and mod_conv = vGEN_REWRITE_CONV vI [vMOD_MOD_REFL] in
  let rec downconv tm =
   ((addmul_conv +---> vLAND_CONV downconv) ||-->
    (mod_conv +---> downconv) ||-->
    vSUB_CONV downconv) tm
  and upconv =
    vGEN_REWRITE_CONV vDEPTH_CONV
     [vMOD_SUC_MOD; vMOD_ADD_MOD; vMOD_MULT_MOD2; vMOD_EXP_MOD; vMOD_MOD_REFL] in
  downconv +---> upconv;;

(* ------------------------------------------------------------------------- *)
(* Crude but useful conversion for cancelling down equations.                *)
(* ------------------------------------------------------------------------- *)

let vNUM_CANCEL_CONV =
  let rec minter i l1' l2' l1 l2 =
    if l1 = [] then (i,l1',l2'@l2)
    else if l2 = [] then (i,l1@l1',l2') else
    let h1 = hd l1 and h2 = hd l2 in
    if h1 = h2 then minter (h1::i) l1' l2' (tl l1) (tl l2)
    else if h1 < h2 then minter i (h1::l1') l2' (tl l1) l2
    else minter i l1' (h2::l2') l1 (tl l2) in
  let add_tm = (parse_term "(+)") and eq_tm = (parse_term "(=) :num->num->bool") in
  let vEQ_ADD_LCANCEL_0' =
    vGEN_REWRITE_RULE (funpow 2 vBINDER_CONV -| vLAND_CONV) [vEQ_SYM_EQ]
      vEQ_ADD_LCANCEL_0 in
  let vAC_RULE = vAC vADD_AC in
  fun tm ->
    let l,r = dest_eq tm in
    let lats = sort (<=) (binops (parse_term "(+)") l)
    and rats = sort (<=) (binops (parse_term "(+)") r) in
    let i,lats',rats' = minter [] [] [] lats rats in
    let l' = list_mk_binop add_tm (i @ lats')
    and r' = list_mk_binop add_tm (i @ rats') in
    let lth = vAC_RULE (mk_eq(l,l'))
    and rth = vAC_RULE (mk_eq(r,r')) in
    let eth = vMK_COMB(vAP_TERM eq_tm lth,rth) in
    vGEN_REWRITE_RULE (vRAND_CONV -| vREPEATC)
      [vEQ_ADD_LCANCEL; vEQ_ADD_LCANCEL_0; vEQ_ADD_LCANCEL_0'] eth;;

(* ------------------------------------------------------------------------- *)
(* This is handy for easing MATCH_MP on inequalities.                        *)
(* ------------------------------------------------------------------------- *)

let vLE_IMP =
  let pth = vPURE_ONCE_REWRITE_RULE[vIMP_CONJ] vLE_TRANS in
  fun th -> vGEN_ALL(vMATCH_MP pth (vSPEC_ALL th));;

(* ------------------------------------------------------------------------- *)
(* Binder for "the minimal n such that".                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_binder "minimal";;

let minimal = new_definition
  (parse_term "(minimal) (P:num->bool) = @n. P n /\\ !m. m < n ==> ~(P m)");;

let vMINIMAL = prove
 ((parse_term "!P. (?n. P n) <=> P((minimal) P) /\\ (!m. m < (minimal) P ==> ~(P m))"),
  vGEN_TAC ----> vREWRITE_TAC[minimal] ----> vCONV_TAC(vRAND_CONV vSELECT_CONV) ---->
  vREWRITE_TAC[vGSYM num_WOP]);;

let vMINIMAL_UNIQUE = prove
 ((parse_term "!P n. P n /\\ (!m. m < n ==> ~P m) ==> (minimal) P = n"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[minimal] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ----> vASM_MESON_TAC[vLT_CASES]);;

let vLE_MINIMAL = prove
 ((parse_term "!P n.\n        (?r. P r) ==> (n <= (minimal) P <=> !i. P i ==> n <= i)"),
  vREPEAT vGEN_TAC ----> vGEN_REWRITE_TAC vLAND_CONV [vMINIMAL] ---->
  vMESON_TAC[vNOT_LE; vLE_TRANS]);;

let vMINIMAL_LE = prove
 ((parse_term "!P n. (?r. P r) ==> ((minimal) P <= n <=> ?i. i <= n /\\ P i)"),
  vREWRITE_TAC[vGSYM vNOT_LT] ----> vREWRITE_TAC[vGSYM vLE_SUC_LT] ---->
  vSIMP_TAC[vLE_MINIMAL] ----> vMESON_TAC[]);;

let vMINIMAL_UBOUND = prove
 ((parse_term "!P n. P n ==> (minimal) P <= n"),
  vMESON_TAC[vMINIMAL; vNOT_LT]);;

let vMINIMAL_LBOUND = prove
 ((parse_term "!P n. (?r. P r) /\\ (!m. m < n ==> ~P m) ==> n <= (minimal) P"),
  vSIMP_TAC[vLE_MINIMAL] ----> vMESON_TAC[vNOT_LT]);;

let vMINIMAL_MONO = prove
 ((parse_term "!P Q. (?n. P n) /\\ (!n. P n ==> Q n) ==> (minimal) Q <= (minimal) P"),
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN vASSUME_TAC) ---->
  vSUBGOAL_THEN (parse_term "?n:num. Q n") vASSUME_TAC ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
  vMATCH_MP_TAC(vMESON[vLE_TRANS; vLE_REFL]
   (parse_term "(!p:num. p <= m ==> p <= n) ==> m <= n")) ---->
  vASM_SIMP_TAC[vLE_MINIMAL]);;

(* ------------------------------------------------------------------------- *)
(* A common lemma for transitive relations.                                  *)
(* ------------------------------------------------------------------------- *)

let vTRANSITIVE_STEPWISE_LT_EQ = prove
 ((parse_term "!R. (!x y z. R x y /\\ R y z ==> R x z)\n         ==> ((!m n. m < n ==> R m n) <=> (!n. R n (SUC n)))"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vASM_SIMP_TAC[vLT] ---->
  vDISCH_TAC ----> vSIMP_TAC[vLT_EXISTS; vLEFT_IMP_EXISTS_THM] ---->
  vGEN_TAC ----> vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vREWRITE_TAC[vLEFT_FORALL_IMP_THM; vEXISTS_REFL; vADD_CLAUSES] ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vADD_CLAUSES] ----> vASM_MESON_TAC[]);;

let vTRANSITIVE_STEPWISE_LT = prove
 ((parse_term "!R. (!x y z. R x y /\\ R y z ==> R x z) /\\ (!n. R n (SUC n))\n       ==> !m n. m < n ==> R m n"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC(vTAUT
   (parse_term "(a ==> (c <=> b)) ==> a /\\ b ==> c")) ---->
  vMATCH_ACCEPT_TAC vTRANSITIVE_STEPWISE_LT_EQ);;

let vTRANSITIVE_STEPWISE_LE_EQ = prove
 ((parse_term "!R. (!x. R x x) /\\ (!x y z. R x y /\\ R y z ==> R x z)\n       ==> ((!m n. m <= n ==> R m n) <=> (!n. R n (SUC n)))"),
  vREPEAT vSTRIP_TAC ----> vEQ_TAC ----> vASM_SIMP_TAC[vLE; vLE_REFL] ---->

  vDISCH_TAC ----> vSIMP_TAC[vLE_EXISTS; vLEFT_IMP_EXISTS_THM] ---->
  vGEN_TAC ----> vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ---->
  vREWRITE_TAC[vLEFT_FORALL_IMP_THM; vEXISTS_REFL; vADD_CLAUSES] ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vADD_CLAUSES] ----> vASM_MESON_TAC[]);;

let vTRANSITIVE_STEPWISE_LE = prove
 ((parse_term "!R. (!x. R x x) /\\ (!x y z. R x y /\\ R y z ==> R x z) /\\\n       (!n. R n (SUC n))\n       ==> !m n. m <= n ==> R m n"),
  vREPEAT vGEN_TAC ----> vMATCH_MP_TAC(vTAUT
   (parse_term "(a /\\ a' ==> (c <=> b)) ==> a /\\ a' /\\ b ==> c")) ---->
  vMATCH_ACCEPT_TAC vTRANSITIVE_STEPWISE_LE_EQ);;

(* ------------------------------------------------------------------------- *)
(* A couple of forms of Dependent Choice.                                    *)
(* ------------------------------------------------------------------------- *)

let vDEPENDENT_CHOICE_FIXED = prove
 ((parse_term "!P R a:A.\n        P 0 a /\\ (!n x. P n x ==> ?y. P (SUC n) y /\\ R n x y)\n        ==> ?f. f 0 = a /\\ (!n. P n (f n)) /\\ (!n. R n (f n) (f(SUC n)))"),
  vREPEAT vSTRIP_TAC ---->
  (vMP_TAC -| prove_recursive_functions_exist num_RECURSION)
    (parse_term "f 0 = (a:A) /\\ (!n. f(SUC n) = @y. P (SUC n) y /\\ R n (f n) y)") ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vGEN_TAC ----> vSTRIP_TAC ---->
  vASM_REWRITE_TAC[] ----> vGEN_REWRITE_TAC vLAND_CONV
   [vMESON[num_CASES] (parse_term "(!n. P n) <=> P 0 /\\ !n. P(SUC n)")] ---->
  vASM_REWRITE_TAC[vAND_FORALL_THM] ----> vINDUCT_TAC ----> vASM_MESON_TAC[]);;

let vDEPENDENT_CHOICE = prove
 ((parse_term "!P R:num->A->A->bool.\n        (?a. P 0 a) /\\ (!n x. P n x ==> ?y. P (SUC n) y /\\ R n x y)\n        ==> ?f. (!n. P n (f n)) /\\ (!n. R n (f n) (f(SUC n)))"),
  vMESON_TAC[vDEPENDENT_CHOICE_FIXED]);;

(* ------------------------------------------------------------------------- *)
(* Conversion that elimimates every occurrence of `NUMERAL`, `BIT0`,         *)
(* `BIT1`, `_0` that is not part of a well-formed numeral.                   *)
(* ------------------------------------------------------------------------- *)

let vBITS_ELIM_CONV : conv =
  let vNUMERAL_pth = prove((parse_term "m = n <=> NUMERAL m = n"),vREWRITE_TAC[vNUMERAL])
  and vZERO_pth = vGSYM (vREWRITE_CONV[vNUMERAL] (parse_term "0"))
  and vBIT0_pth,vBIT1_pth = vCONJ_PAIR
   (prove((parse_term "(m = n <=> BIT0 m = 2 * n) /\\\n           (m = n <=> BIT1 m = 2 * n + 1)"),
    vCONJ_TAC ----> vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vBIT0; vBIT1] ---->
    vREWRITE_TAC[vADD1; vEQ_ADD_RCANCEL; vGSYM vMULT_2] ---->
    vREWRITE_TAC[vEQ_MULT_LCANCEL] ---->
    vREWRITE_TAC[vTWO; vNOT_SUC]))
  and mvar,nvar = (parse_term "m:num"),(parse_term "n:num") in
  let rec vBITS_ELIM_CONV : conv =
    fun tm -> match tm with
      Const("_0",_) -> vZERO_pth
    | Var _ | Const _ -> vREFL tm
    | Comb(Const("NUMERAL",_),mtm) ->
        if is_numeral tm then vREFL tm else
        let th = vBITS_ELIM_CONV mtm in
        vEQ_MP (vINST[mtm,mvar;rand(concl th),nvar] vNUMERAL_pth) th
    | Comb(Const("BIT0",_),mtm) ->
        let th = vBITS_ELIM_CONV mtm in
        vEQ_MP (vINST [mtm,mvar;rand(concl th),nvar] vBIT0_pth) th
    | Comb(Const("BIT1",_),mtm) ->
        let th = vBITS_ELIM_CONV mtm in
        vEQ_MP (vINST [mtm,mvar;rand(concl th),nvar] vBIT1_pth) th
    | Comb _ -> vCOMB_CONV vBITS_ELIM_CONV tm
    | Abs _ -> vABS_CONV vBITS_ELIM_CONV tm in
  vBITS_ELIM_CONV;;
