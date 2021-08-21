(* ========================================================================= *)
(* Tools for defining quotient types and lifting first order theorems.       *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Parser
open Equal
open Bool
open Drule
open Tactics
open Simp
open Theorems
open Class
open Meson

(* ------------------------------------------------------------------------- *)
(* Given a type name "ty" and a curried binary relation R, this defines      *)
(* a new type "ty" of R-equivalence classes. The abstraction and             *)
(* representation functions for the new type are called "mk_ty" and          *)
(* "dest_ty". The type bijections (after beta-conversion) are returned:      *)
(*                                                                           *)
(*             |- mk_ty (dest_ty a) = a                                      *)
(*                                                                           *)
(*             |- (?x. r = R x) <=> (dest_ty (mk_ty r) = r)                  *)
(* ------------------------------------------------------------------------- *)

let define_quotient_type =
  fun tyname (absname,repname) eqv ->
    let ty = hd(snd(dest_type(type_of eqv))) in
    let pty = mk_fun_ty ty bool_ty in
    let s = mk_var("s",pty) and x = mk_var("x",ty) in
    let eqvx = mk_comb(eqv,x) in
    let pred = mk_abs(s,mk_exists(x,mk_eq(s,eqvx))) in
    let th0 = vBETA_CONV(mk_comb(pred,eqvx)) in
    let th1 = vEXISTS(rand(concl th0),x) (vREFL eqvx) in
    let th2 = vEQ_MP (vSYM th0) th1 in
    let abs,rep = new_basic_type_definition tyname (absname,repname) th2 in
    abs,vCONV_RULE(vLAND_CONV vBETA_CONV) rep;;

(* ------------------------------------------------------------------------- *)
(* Given a welldefinedness theorem for a curried function f, of the form:    *)
(*                                                                           *)
(* |- !x1 x1' .. xn xn'. (x1 == x1') /\ ... /\ (xn == xn')                   *)
(*                       ==> (f x1 .. xn == f x1' .. f nx')                  *)
(*                                                                           *)
(* where each "==" is either equality or some fixed binary relation R, a     *)
(* new operator called "opname" is introduced which lifts "f" up to the      *)
(* R-equivalence classes. Two theorems are returned: the actual definition   *)
(* and a useful consequence for lifting theorems.                            *)
(*                                                                           *)
(* The function also needs the second (more complicated) type bijection, and *)
(* the reflexivity and transitivity (not symmetry!) of the equivalence       *)
(* relation. The use also gives a name for the new function.                 *)
(* ------------------------------------------------------------------------- *)

let lift_function =
  let vSELECT_LEMMA = prove
   ((parse_term "!x:A. (@y. x = y) = x"),
    vGEN_TAC ----> vGEN_REWRITE_TAC (vLAND_CONV -| vBINDER_CONV) [vEQ_SYM_EQ] ---->
    vMATCH_ACCEPT_TAC vSELECT_REFL) in
  fun tybij2 ->
    let tybl,tybr = dest_comb(concl tybij2) in
    let eqvx = rand(body(rand(rand tybl))) in
    let eqv,xtm = dest_comb eqvx in
    let dmr,rtm = dest_eq tybr in
    let dest,mrt = dest_comb dmr in
    let mk = rator mrt in
    let ety = type_of mrt in
    fun (refl_th,trans_th) fname wth ->
      let wtm = repeat (snd -| dest_forall) (concl wth) in
      let wfvs = frees wtm in
      let hyps,con = try (conjuncts $-$ vI) (dest_imp wtm)
                     with Failure _ -> [],wtm in
      let eqs,rels = partition is_eq hyps in
      let rvs = map lhand rels in
      let qvs = map lhs eqs in
      let evs =
        variants wfvs (map (fun v -> mk_var(fst(dest_var v),ety)) rvs) in
      let mems = map2 (fun rv ev -> mk_comb(mk_comb(dest,ev),rv)) rvs evs in
      let lcon,rcon = dest_comb con in
      let u = variant (evs @ wfvs) (mk_var("u",type_of rcon)) in
      let ucon = mk_comb(lcon,u) in
      let dbod = list_mk_conj(ucon::mems) in
      let detm = list_mk_exists(rvs,dbod) in
      let datm = mk_abs(u,detm) in
      let def =
        if is_eq con then list_mk_icomb "@" [datm] else mk_comb(mk,datm) in
      let newargs = map
        (fun e -> try lhs e with Failure _ -> assoc (lhand e) (zip rvs evs)) hyps in
      let rdef = list_mk_abs(newargs,def) in
      let ldef = mk_var(fname,type_of rdef) in
      let dth = new_definition(mk_eq(ldef,rdef)) in
      let eth = rev_itlist
        (fun v th -> vCONV_RULE(vRAND_CONV vBETA_CONV) (vAP_THM th v))
        newargs dth in
      let targs = map (fun v -> mk_comb(mk,mk_comb(eqv,v))) rvs in
      let dme_th =
        let th = vINST [eqvx,rtm] tybij2 in
        vEQ_MP th (vEXISTS(lhs(concl th),xtm) (vREFL eqvx)) in
      let ith = vINST (zip targs evs) eth in
      let jth = vSUBS (map (fun v -> vINST[v,xtm] dme_th) rvs) ith in
      let apop,uxtm = dest_comb(rand(concl jth)) in
      let extm = body uxtm in
      let evs,bod = strip_exists extm in
      let th1 = vASSUME bod in
      let th2 =
        if evs = [] then th1 else
        let th2a,th2b = vCONJ_PAIR th1 in
        let ethlist = vCONJUNCTS th2b @ map vREFL qvs in
        let th2c = end_itlist vCONJ (map
          (fun v -> find ((=) (lhand v) -| lhand -| concl) ethlist) hyps) in
        let th2d = vMATCH_MP wth th2c in
        let th2e = try vTRANS th2d th2a
                   with Failure _ -> vMATCH_MP trans_th (vCONJ th2d th2a) in
        itlist vSIMPLE_CHOOSE evs th2e in
      let th3 = vASSUME(concl th2) in
      let th4 = end_itlist vCONJ (th3::(map (vC vSPEC refl_th) rvs)) in
      let th5 = itlist vSIMPLE_EXISTS evs (vASSUME bod) in
      let th6 = vMATCH_MP (vDISCH_ALL th5) th4 in
      let th7 = vIMP_ANTISYM_RULE (vDISCH_ALL th2) (vDISCH_ALL th6) in
      let th8 = vTRANS jth (vAP_TERM apop (vABS u th7)) in
      let fconv = if is_eq con then vREWR_CONV vSELECT_LEMMA
                  else vRAND_CONV vETA_CONV in
      let th9 = vCONV_RULE (vRAND_CONV fconv) th8 in
      eth,vGSYM th9;;

(* ------------------------------------------------------------------------- *)
(* Lifts a theorem. This can be done by higher order rewriting alone.        *)
(*                                                                           *)
(* NB! All and only the first order variables must be bound by quantifiers.  *)
(* ------------------------------------------------------------------------- *)

let lift_theorem =
  let pth = prove
   ((parse_term "(!x:Repty. R x x) /\\\n     (!x y. R x y <=> R y x) /\\\n     (!x y z. R x y /\\ R y z ==> R x z) /\\\n     (!a. mk(dest a) = a) /\\\n     (!r. (?x. r = R x) <=> (dest(mk r) = r))\n     ==> (!x y. R x y <=> (mk(R x) = mk(R y))) /\\\n         (!P. (!x. P(mk(R x))) <=> (!x. P x)) /\\\n         (!P. (?x. P(mk(R x))) <=> (?x. P x)) /\\\n         (!x:Absty. mk(R((@)(dest x))) = x)"),
    vSTRIP_TAC ---->
    vSUBGOAL_THEN
     (parse_term "!x y. (mk((R:Repty->Repty->bool) x):Absty = mk(R y)) <=> (R x = R y)")
    vASSUME_TAC ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
    vMATCH_MP_TAC(vTAUT (parse_term "(a /\\ b /\\ c) /\\ (b ==> a ==> d)\n                       ==> a /\\ b /\\ c /\\ d")) ---->
    vCONJ_TAC ++-->
     [vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vFUN_EQ_THM] ----> vASM_MESON_TAC[];
      vALL_TAC] ---->
    vREPEAT(vDISCH_THEN(fun th -> vREWRITE_TAC[vGSYM th])) ---->
    vX_GEN_TAC (parse_term "x:Repty") ---->
    vSUBGOAL_THEN (parse_term "dest(mk((R:Repty->Repty->bool) x):Absty) = R x")
    vSUBST1_TAC ++--> [vASM_MESON_TAC[]; vALL_TAC] ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vETA_AX] ---->
    vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vI [th]) ---->
    vCONV_TAC vSELECT_CONV ----> vASM_MESON_TAC[]) in
  fun tybij (refl_th,sym_th,trans_th) ->
    let tybij1 = vGEN_ALL (fst tybij)
    and tybij2 = vGEN_ALL (snd tybij) in
    let cth = end_itlist vCONJ [refl_th; sym_th; trans_th; tybij1; tybij2] in
    let ith = vMATCH_MP pth cth in
    fun trths ->
      vREWRITE_RULE (ith::trths);;
