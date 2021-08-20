(* ========================================================================= *)
(* Intuitionistic theorem prover (complete for propositional fragment).      *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Equal
open Bool
open Drule
open Tactics

(* ------------------------------------------------------------------------- *)
(* Accept a theorem modulo unification.                                      *)
(* ------------------------------------------------------------------------- *)

let vUNIFY_ACCEPT_TAC mvs th (_asl,w) =
  let insts = term_unify mvs (concl th) w in
  ([],insts),[],
  let th' = vINSTANTIATE insts th in
  fun i -> function [] -> vINSTANTIATE i th' | _ -> assert false;;

(* ------------------------------------------------------------------------- *)
(* The actual prover, as a tactic.                                           *)
(* ------------------------------------------------------------------------- *)

let vITAUT_TAC =
  let vCONJUNCTS_THEN' ttac cth =
    ttac(vCONJUNCT1 cth) ----> ttac(vCONJUNCT2 cth) in
  let vIMPLICATE t =
    let th1 = vAP_THM vNOT_DEF (dest_neg t) in
    vCONV_RULE (vRAND_CONV vBETA_CONV) th1 in
  let vRIGHT_REVERSIBLE_TAC = vFIRST
   [vCONJ_TAC;                                                     (* and     *)
    vGEN_TAC;                                                      (* forall  *)
    vDISCH_TAC;                                                    (* implies; not *)
    vEQ_TAC]                                                       (* iff     *)
  and vLEFT_REVERSIBLE_TAC th gl = tryfind (fun ttac -> ttac th gl)
   [vCONJUNCTS_THEN' vASSUME_TAC;                                   (* and    *)
    vDISJ_CASES_TAC;                                               (* or     *)
    vCHOOSE_TAC;                                                   (* exists *)
    (fun th -> vASSUME_TAC (vEQ_MP (vIMPLICATE (concl th)) th));     (* not    *)
    (vCONJUNCTS_THEN' vMP_TAC -| uncurry vCONJ  -| vEQ_IMP_RULE)]       (* iff    *)
  in
  let rec vITAUT_TAC mvs n gl =
    if n <= 0 then failwith "ITAUT_TAC: Too deep" else
    ((vFIRST_ASSUM (vUNIFY_ACCEPT_TAC mvs)) |--->
     (vACCEPT_TAC vTRUTH) |--->
     (vFIRST_ASSUM vCONTR_TAC) |--->
     (vRIGHT_REVERSIBLE_TAC ----> vTRY (vITAUT_TAC mvs n)) |--->
     (vFIRST_X_ASSUM vLEFT_REVERSIBLE_TAC ----> vTRY(vITAUT_TAC mvs n)) |--->
     (vFIRST_X_ASSUM(fun th -> vASSUME_TAC th ---->
       (let gv = genvar(type_of(fst(dest_forall(concl th)))) in
        vMETA_SPEC_TAC gv th ---->
        vITAUT_TAC (gv::mvs) (n - 2) ----> vNO_TAC))) |--->
     (vDISJ1_TAC ----> vITAUT_TAC mvs n ----> vNO_TAC) |--->
     (vDISJ2_TAC ----> vITAUT_TAC mvs n ----> vNO_TAC) |--->
     (fun gl -> let gv = genvar(type_of(fst(dest_exists(snd gl)))) in
                (vX_META_EXISTS_TAC gv ---->
                 vITAUT_TAC (gv::mvs) (n - 2) ----> vNO_TAC) gl) |--->
     (vFIRST_ASSUM(fun th -> vSUBGOAL_THEN (fst(dest_imp(concl th)))
                                      (fun ath -> vASSUME_TAC (vMP th ath)) ---->
                           vITAUT_TAC mvs (n - 1) ----> vNO_TAC))) gl in
  let rec vITAUT_ITERDEEP_TAC n gl =
    remark ("Searching with limit "^(string_of_int n));
    ((vITAUT_TAC [] n ----> vNO_TAC) |---> vITAUT_ITERDEEP_TAC (n + 1)) gl in
  vITAUT_ITERDEEP_TAC 0;;

(* ------------------------------------------------------------------------- *)
(* Alternative interface.                                                    *)
(* ------------------------------------------------------------------------- *)

let vITAUT tm = prove(tm,vITAUT_TAC);;
