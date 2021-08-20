(* ========================================================================= *)
(* Mutually inductively defined relations.                                   *)
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
open Itab
open Simp
open Theorems

(* ------------------------------------------------------------------------- *)
(* Strip off exactly n arguments from combination.                           *)
(* ------------------------------------------------------------------------- *)

let strip_ncomb =
  let rec strip(n,tm,acc) =
    if n < 1 then tm,acc else
    let l,r = dest_comb tm in
    strip(n - 1,l,r::acc) in
  fun n tm -> strip(n,tm,[]);;

(* ------------------------------------------------------------------------- *)
(* Expand lambda-term function definition with its arguments.                *)
(* ------------------------------------------------------------------------- *)

let vRIGHT_BETAS =
  rev_itlist (fun a -> vCONV_RULE (vRAND_CONV vBETA_CONV) -| vC vAP_THM a);;

(* ------------------------------------------------------------------------- *)
(*      A, x = t |- P[x]                                                     *)
(*     ------------------ EXISTS_EQUATION                                    *)
(*        A |- ?x. P[x]                                                      *)
(* ------------------------------------------------------------------------- *)

let vEXISTS_EQUATION =
  let pth = prove
   ((parse_term "!P t. (!x:A. (x = t) ==> P x) ==> (?) P"),
    vREWRITE_TAC[vEXISTS_DEF] ----> vBETA_TAC ---->
    vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vEXISTS_TAC (parse_term "t:A") ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vREFL_TAC) in
  fun tm th ->
    let l,r = dest_eq tm in
    let vP = mk_abs(l,concl th) in
    let th1 = vBETA_CONV(mk_comb(vP,l)) in
    let th2 = vISPECL [vP; r] pth in
    let th3 = vEQ_MP (vSYM th1) th in
    let th4 = vGEN l (vDISCH tm th3) in
    vMP th2 th4;;

(* ========================================================================= *)
(* Part 1: The main part of the inductive definitions package.               *)
(* This proves that a certain definition yields the requires theorems.       *)
(* ========================================================================= *)

let derive_nonschematic_inductive_relations =
  let getconcl tm =
    let bod = repeat (snd -| dest_forall) tm in
    try snd(dest_imp bod) with Failure _ -> bod
  and vCONJ_ACI_RULE = vAC vCONJ_ACI
  and vSIMPLE_DISJ_PAIR th =
    let l,r = dest_disj(hd(hyp th)) in
    vPROVE_HYP (vDISJ1 (vASSUME l) r) th,vPROVE_HYP (vDISJ2 l (vASSUME r)) th
  and vHALF_BETA_EXPAND args th = vGENL args (vRIGHT_BETAS args th) in
  let vAND_IMPS_CONV tm =
    let ths = vCONJUNCTS(vASSUME tm) in
    let avs = fst(strip_forall(concl(hd ths))) in
    let thl = map (vDISCH tm -| vUNDISCH -| vSPEC_ALL) ths in
    let th1 = end_itlist vSIMPLE_DISJ_CASES thl in
    let tm1 = hd(hyp th1) in
    let th2 = vGENL avs (vDISCH tm1 (vUNDISCH th1)) in
    let tm2 = concl th2 in
    let th3 = vDISCH tm2 (vUNDISCH (vSPEC_ALL (vASSUME tm2))) in
    let thts,tht =  nsplit vSIMPLE_DISJ_PAIR (tl ths) th3 in
    let proc_fn th =
      let t = hd(hyp th) in vGENL avs (vDISCH t (vUNDISCH th)) in
    let th4 = itlist (vCONJ -| proc_fn) thts (proc_fn tht) in
    vIMP_ANTISYM_RULE (vDISCH_ALL th2) (vDISCH_ALL th4) in
  let t_tm = (parse_term "T") in
  let calculate_simp_sequence =
    let rec getequs(avs,plis) =
      if plis = [] then [] else
      match plis with h::t ->
      let r = snd h in
      if mem r avs then
        h::(getequs(avs,filter ((<>) r -| snd) t))
      else
        getequs(avs,t) 
      | _ -> assert false in
    fun avs plis ->
      let oks = getequs(avs,plis) in
      oks,subtract plis oks
  and vFORALL_IMPS_CONV tm =
    let avs,bod = strip_forall tm in
    let th1 = vDISCH tm (vUNDISCH(vSPEC_ALL(vASSUME tm))) in
    let th2 = itlist vSIMPLE_CHOOSE avs th1 in
    let tm2 = hd(hyp th2) in
    let th3 = vDISCH tm2 (vUNDISCH th2) in
    let th4 = vASSUME (concl th3) in
    let ant = lhand bod in
    let th5 = itlist vSIMPLE_EXISTS avs (vASSUME ant) in
    let th6 = vGENL avs (vDISCH ant (vMP th4 th5)) in
    vIMP_ANTISYM_RULE (vDISCH_ALL th3) (vDISCH_ALL th6) in
  let canonicalize_clause cls args =
    let avs,bimp = strip_forall cls in
    let ant,con = try dest_imp bimp with Failure _ -> t_tm,bimp in
    let rel,xargs = strip_comb con in
    let plis = zip args xargs in
    let yes,no = calculate_simp_sequence avs plis in
    let nvs = filter (not -| vC mem (map snd yes)) avs in
    let eth =
      if is_imp bimp then
        let atm = itlist (curry mk_conj -| mk_eq) (yes@no) ant in
        let ths,tth = nsplit vCONJ_PAIR plis (vASSUME atm) in
        let thl = map (fun t -> find (fun th -> lhs(concl th) = t) ths) args in
        let th0 = vMP (vSPECL avs (vASSUME cls)) tth in
        let th1 = rev_itlist (vC (curry vMK_COMB)) thl (vREFL rel) in
        let th2 = vEQ_MP (vSYM th1) th0 in
        let th3 = vINST yes (vDISCH atm th2) in
        let tm4 = funpow (length yes) rand (lhand(concl th3)) in
        let th4 = itlist (vCONJ -| vREFL -| fst) yes (vASSUME tm4) in
        let th5 = vGENL args (vGENL nvs (vDISCH tm4 (vMP th3 th4))) in
        let th6 = vSPECL nvs (vSPECL (map snd plis) (vASSUME (concl th5))) in
        let th7 = itlist (vCONJ -| vREFL -| snd) no (vASSUME ant) in
        let th8 = vGENL avs (vDISCH ant (vMP th6 th7)) in
        vIMP_ANTISYM_RULE (vDISCH_ALL th5) (vDISCH_ALL th8)
      else
        let atm = list_mk_conj(map mk_eq (yes@no)) in
        let ths = vCONJUNCTS (vASSUME atm) in
        let thl = map (fun t -> find (fun th -> lhs(concl th) = t) ths) args in
        let th0 = vSPECL avs (vASSUME cls) in
        let th1 = rev_itlist (vC (curry vMK_COMB)) thl (vREFL rel) in
        let th2 = vEQ_MP (vSYM th1) th0 in
        let th3 = vINST yes (vDISCH atm th2) in
        let tm4 = funpow (length yes) rand (lhand(concl th3)) in
        let th4 = itlist (vCONJ -| vREFL -| fst) yes (vASSUME tm4) in
        let th5 = vGENL args (vGENL nvs (vDISCH tm4 (vMP th3 th4))) in
        let th6 = vSPECL nvs (vSPECL (map snd plis) (vASSUME (concl th5))) in
        let th7 = end_itlist vCONJ (map (vREFL -| snd) no) in
        let th8 = vGENL avs (vMP th6 th7) in
        vIMP_ANTISYM_RULE (vDISCH_ALL th5) (vDISCH_ALL th8) in
    let ftm = funpow (length args) (body -| rand) (rand(concl eth)) in
    vTRANS eth (itlist vMK_FORALL args (vFORALL_IMPS_CONV ftm)) in
  let canonicalize_clauses clauses =
    let concls = map getconcl clauses in
    let uncs = map strip_comb concls in
    let rels = itlist (insert -| fst) uncs [] in
    let xargs = map (vC assoc uncs) rels in
    let closed = list_mk_conj clauses in
    let avoids = variables closed in
    let flargs =
      make_args "a" avoids (map type_of (end_itlist (@) xargs)) in
    let zargs = zip rels (shareout xargs flargs) in
    let cargs = map (fun (r,_a) -> assoc r zargs) uncs in
    let cthms = map2 canonicalize_clause clauses cargs in
    let pclauses = map (rand -| concl) cthms in
    let collectclauses tm =
      mapfilter (fun t -> if fst t = tm then snd t else fail())
                (zip (map fst uncs) pclauses) in
    let clausell = map collectclauses rels in
    let cclausel = map list_mk_conj clausell in
    let cclauses = list_mk_conj cclausel
    and oclauses = list_mk_conj pclauses in
    let eth = vCONJ_ACI_RULE(mk_eq(oclauses,cclauses)) in
    let pth = vTRANS (end_itlist vMK_CONJ cthms) eth in
    vTRANS pth (end_itlist vMK_CONJ (map vAND_IMPS_CONV cclausel))
  and derive_canon_inductive_relations clauses =
    let closed = list_mk_conj clauses in
    let clauses = conjuncts closed in
    let vargs,bodies = unzip(map strip_forall clauses) in
    let ants,concs = unzip(map dest_imp bodies) in
    let rels = map (repeat rator) concs in
    let avoids = variables closed in
    let rels' = variants avoids rels in
    let crels = zip rels' rels in
    let prime_fn = subst crels in
    let closed' = prime_fn closed in
    let mk_def arg con =
      mk_eq(repeat rator con,
        list_mk_abs(arg,list_mk_forall(rels',mk_imp(closed',prime_fn con)))) in
    let deftms = map2 mk_def vargs concs in
    let defthms = map2 vHALF_BETA_EXPAND vargs (map vASSUME deftms) in
    let mk_ind args th =
      let th1 = fst(vEQ_IMP_RULE(vSPEC_ALL th)) in
      let ant = lhand(concl th1) in
      let th2 = vSPECL rels' (vUNDISCH th1) in
      vGENL args (vDISCH ant (vUNDISCH th2)) in
    let indthms = map2 mk_ind vargs defthms in
    let indthmr = end_itlist vCONJ indthms in
    let indthm = vGENL rels' (vDISCH closed' indthmr) in
    let mconcs = map2 (fun a t -> list_mk_forall(a,mk_imp(t,prime_fn t)))
      vargs ants in
    let monotm = mk_imp(concl indthmr,list_mk_conj mconcs) in
    let monothm = vASSUME(list_mk_forall(rels,list_mk_forall(rels',monotm))) in
    let closthm = vASSUME closed' in
    let monothms = vCONJUNCTS
      (vMP (vSPEC_ALL monothm) (vMP (vSPECL rels' indthm) closthm)) in
    let closthms = vCONJUNCTS closthm in
    let prove_rule mth (cth,dth) =
      let avs,bod = strip_forall(concl mth) in
      let th1 = vIMP_TRANS (vSPECL avs mth) (vSPECL avs cth) in
      let th2 = vGENL rels' (vDISCH closed' (vUNDISCH th1)) in
      let th3 = vEQ_MP (vSYM (vSPECL avs dth)) th2 in
      vGENL avs (vDISCH (lhand bod) th3) in
    let rulethms = map2 prove_rule monothms (zip closthms defthms) in
    let rulethm = end_itlist vCONJ rulethms in
    let dtms = map2 (curry list_mk_abs) vargs ants in
    let double_fn = subst (zip dtms rels) in
    let mk_unbetas tm dtm =
      let avs,bod = strip_forall tm in
      let il,r = dest_comb bod in
      let i,l = dest_comb il in
      let bth = vRIGHT_BETAS avs (vREFL dtm) in
      let munb = vAP_THM (vAP_TERM i bth) r in
      let iunb = vAP_TERM (mk_comb(i,double_fn l)) bth in
      let junb = vAP_TERM (mk_comb(i,r)) bth in
      let quantify = itlist vMK_FORALL avs in
      (quantify munb,(quantify iunb,quantify junb)) in
    let unths = map2 mk_unbetas clauses dtms in
    let irthm = vEQ_MP (vSYM(end_itlist vMK_CONJ (map fst unths))) rulethm in
    let mrthm = vMP (vSPECL rels (vSPECL dtms monothm)) irthm in
    let imrth = vEQ_MP (vSYM(end_itlist vMK_CONJ (map (fst -| snd) unths))) mrthm in
    let ifthm = vMP (vSPECL dtms indthm) imrth in
    let fthm = vEQ_MP (end_itlist vMK_CONJ (map (snd -| snd) unths)) ifthm in
    let mk_case th1 th2 =
      let avs = fst(strip_forall(concl th1)) in
      vGENL avs (vIMP_ANTISYM_RULE (vSPEC_ALL th1) (vSPEC_ALL th2)) in
    let casethm = end_itlist vCONJ
      (map2 mk_case (vCONJUNCTS fthm) (vCONJUNCTS rulethm)) in
    vCONJ rulethm (vCONJ indthm casethm) in
  fun tm ->
    let clauses = conjuncts tm in
    let canonthm = canonicalize_clauses clauses in
    let canonthm' = vSYM canonthm in
    let pclosed = rand(concl canonthm) in
    let pclauses = conjuncts pclosed in
    let rawthm = derive_canon_inductive_relations pclauses in
    let rulethm,otherthms = vCONJ_PAIR rawthm in
    let indthm,casethm = vCONJ_PAIR otherthms in
    let rulethm' = vEQ_MP canonthm' rulethm
    and indthm' = vCONV_RULE (vONCE_DEPTH_CONV (vREWR_CONV canonthm')) indthm in
    vCONJ rulethm' (vCONJ indthm' casethm);;

(* ========================================================================= *)
(* Part 2: Tactic-integrated tools for proving monotonicity automatically.   *)
(* ========================================================================= *)

let monotonicity_theorems = ref
 [vMONO_AND; vMONO_OR; vMONO_IMP; vMONO_NOT; vMONO_EXISTS; vMONO_FORALL];;

(* ------------------------------------------------------------------------- *)
(* Attempt to backchain through the monotonicity theorems.                   *)
(* ------------------------------------------------------------------------- *)

let vMONO_TAC =
  let imp = (parse_term "(==>)") and vIMP_REFL = vITAUT (parse_term "!p. p ==> p") in
  let vBACKCHAIN_TAC th =
    let match_fn = vPART_MATCH (snd -| dest_imp) th in
    fun (asl,w) ->
      let th1 = match_fn w in
      let ant,_con = dest_imp(concl th1) in
      null_meta,[asl,ant],fun i -> function [t] -> vMATCH_MP (vINSTANTIATE i th1) t | _ -> assert false
  and vMONO_ABS_TAC (asl,w) =
    let ant,con = dest_imp w in
    let vars = snd(strip_comb con) in
    let rnum = length vars - 1 in
    let hd1,args1 = strip_ncomb rnum ant
    and hd2,_args2 = strip_ncomb rnum con in
    let th1 = rev_itlist (vC vAP_THM) args1 (vBETA_CONV hd1)
    and th2 = rev_itlist (vC vAP_THM) args1 (vBETA_CONV hd2) in
    let th3 = vMK_COMB(vAP_TERM imp th1,th2) in
    vCONV_TAC(vREWR_CONV th3) (asl,w)
  and vAPPLY_MONOTAC tacs (asl,w) =
    let a,c = dest_imp w in
    if aconv a c then vACCEPT_TAC (vSPEC a vIMP_REFL) (asl,w) else
    let cn = try fst(dest_const(repeat rator c)) with Failure _ -> "" in
    tryfind (fun (k,t) -> if k = cn then t (asl,w) else fail()) tacs in
  fun gl ->
    let tacs = itlist
      (fun th l -> let ft = repeat rator (funpow 2 rand (concl th)) in
                   let c = try fst(dest_const ft) with Failure _ -> "" in
                   (c,vBACKCHAIN_TAC th ----> vREPEAT vCONJ_TAC)::l)
      (!monotonicity_theorems) ["",vMONO_ABS_TAC] in
    let vMONO_STEP_TAC = vREPEAT vGEN_TAC ----> vAPPLY_MONOTAC tacs in
    (vREPEAT vMONO_STEP_TAC ----> vASM_REWRITE_TAC[]) gl;;

(* ------------------------------------------------------------------------- *)
(* Attempt to dispose of the non-equational assumption(s) of a theorem.      *)
(* ------------------------------------------------------------------------- *)

let prove_monotonicity_hyps =
  let tac = vREPEAT vGEN_TAC ---->
    vDISCH_THEN(vREPEAT_TCL vCONJUNCTS_THEN vASSUME_TAC) ---->
    vREPEAT vCONJ_TAC ----> vMONO_TAC in
  let prove_mth t = prove(t,tac) in
  fun th ->
    let mths = mapfilter prove_mth (filter (not -| is_eq) (hyp th)) in
    itlist vPROVE_HYP mths th;;

(* ========================================================================= *)
(* Part 3: The final user wrapper, with schematic variables added.           *)
(* ========================================================================= *)

let the_inductive_definitions = ref [];;

let prove_inductive_relations_exist,new_inductive_definition =
  let rec pare_comb qvs tm =
    if intersect (frees tm) qvs = [] && forall is_var (snd(strip_comb tm))
    then tm
    else pare_comb qvs (rator tm) in
  let generalize_schematic_variables gflag vs =
    let generalize_def tm th =
      let l,r = dest_eq tm in
      let lname,lty = dest_var l in
      let l' = mk_var(lname,itlist (mk_fun_ty -| type_of) vs lty) in
      let r' = list_mk_abs(vs,r) in
      let tm' = mk_eq(l',r') in
      let th0 = vRIGHT_BETAS vs (vASSUME tm') in
      let th1 = vINST [lhs(concl th0),l] (vDISCH tm th) in
      vMP th1 th0 in
    fun th ->
      let defs,others = partition is_eq (hyp th) in
      let th1 = itlist generalize_def defs th in
      if gflag then
        let others' = map (fun t -> let fvs = frees t in
                                    vSPECL fvs (vASSUME (list_mk_forall(fvs,t))))
                          others in
        vGENL vs (itlist vPROVE_HYP others' th1)
      else th1
  and derive_existence th =
    let defs = filter is_eq (hyp th) in
    itlist vEXISTS_EQUATION defs th
  and make_definitions th =
    let defs = filter is_eq (hyp th) in
    let dths = map new_definition defs in
    let insts = zip (map (lhs -| concl) dths) (map lhs defs) in
    rev_itlist (vC vMP) dths (vINST insts (itlist vDISCH defs th))
  and unschematize_clauses clauses =
    let schem = map (fun cls -> let avs,bod = strip_forall cls in
                  pare_comb avs (try snd(dest_imp bod) with Failure _ -> bod))
                            clauses in
      let schems = setify schem in
      if is_var(hd schem) then (clauses,[]) else
      if not (length(setify (map (snd -| strip_comb) schems)) = 1)
      then failwith "Schematic variables not used consistently" else
      let avoids = variables (list_mk_conj clauses) in
      let hack_fn tm = mk_var(fst(dest_var(repeat rator tm)),type_of tm) in
      let grels = variants avoids (map hack_fn schems) in
      let crels = zip grels schems in
      let clauses' = map (subst crels) clauses in
      clauses',snd(strip_comb(hd schems)) in
  let find_redefinition tm (rth,_ith,_cth as trip) =
    if aconv tm (concl rth) then trip else failwith "find_redefinition" in
  let prove_inductive_properties tm =
    let clauses = conjuncts tm in
    let clauses',fvs = unschematize_clauses clauses in
    let th = derive_nonschematic_inductive_relations (list_mk_conj clauses') in
    fvs,prove_monotonicity_hyps th in
  let prove_inductive_relations_exist tm =
    let fvs,th1 = prove_inductive_properties tm in
    let th2 = generalize_schematic_variables true fvs th1 in
    derive_existence th2
  and new_inductive_definition tm =
    try let th = tryfind (find_redefinition tm) (!the_inductive_definitions) in
        warn true "Benign redefinition of inductive predicate"; th
    with Failure _ ->
    let fvs,th1 = prove_inductive_properties tm in
    let th2 = generalize_schematic_variables true fvs th1 in
    let th3 = make_definitions th2 in
    let avs = fst(strip_forall(concl th3)) in
    let r,ic = vCONJ_PAIR(vSPECL avs th3) in
    let i,c = vCONJ_PAIR ic in
    let thtr = vGENL avs r,vGENL avs i,vGENL avs c in
    the_inductive_definitions := thtr::(!the_inductive_definitions);
    thtr in
  prove_inductive_relations_exist,new_inductive_definition;;

(* ------------------------------------------------------------------------- *)
(* Derivation of "strong induction".                                         *)
(* ------------------------------------------------------------------------- *)

let derive_strong_induction =
  let dest_ibod tm =
    let avs,ibod = strip_forall tm in
    let n = length avs in
    let prator = funpow n rator in
    let ant,con = dest_imp ibod in
    n,(prator ant,prator con) in
  let rec prove_triv tm =
    if is_conj tm then vCONJ (prove_triv(lhand tm)) (prove_triv(rand tm)) else
    let avs,bod = strip_forall tm in
    let a,c = dest_imp bod in
    let ths = vCONJUNCTS(vASSUME a) in
    let th = find (aconv c -| concl) ths in
    vGENL avs (vDISCH a th) in
  let rec weaken_triv th =
    if is_conj(concl th)
    then vCONJ (weaken_triv(vCONJUNCT1 th)) (weaken_triv(vCONJUNCT2 th)) else
    let avs,_bod = strip_forall(concl th) in
    let th1 = vSPECL avs th in
    let a = fst(dest_imp(concl th1)) in
    vGENL avs (vDISCH a (vCONJUNCT2 (vUNDISCH th1))) in
  let vMATCH_IMPS = vMATCH_MP vMONO_AND in
  fun (rth,ith) ->
    let ovs,ibod = strip_forall(concl ith) in
    let iant,icon = dest_imp ibod in
    let ns,prrs = unzip (map dest_ibod (conjuncts icon)) in
    let rs,ps = unzip prrs in
    let gs = variants (variables ibod) ps in
    let svs,_tvs = chop_list (length ovs - length ns) ovs in
    let sth = vSPECL svs rth and jth = vSPECL svs ith in
    let gimps = subst (zip gs rs) icon in
    let prs = map2 (fun n (r,p) ->
      let tys,_ty = nsplit dest_fun_ty (1--n) (type_of r) in
      let gvs = map genvar tys in
      list_mk_abs(gvs,mk_conj(list_mk_comb(r,gvs),list_mk_comb(p,gvs))))
     ns prrs in
    let modify_rule rcl itm =
      let avs,bod = strip_forall itm in
      if is_imp bod then
        let a,c = dest_imp bod in
        let mgoal = mk_imp(gimps,mk_imp(vsubst(zip gs ps) a,a)) in
        let mth = vASSUME(list_mk_forall(gs@ps@avs,mgoal)) in
        let ith_r = vBETA_RULE(vSPECL (prs @ rs @ avs) mth) in
        let jth_r = vMP ith_r (prove_triv(lhand(concl ith_r))) in
        let t = lhand(concl jth_r) in
        let kth_r = vUNDISCH jth_r in
        let ntm = list_mk_forall(avs,mk_imp(t,c)) in
        let lth_r = vMP(vSPECL avs rcl) kth_r
        and lth_p = vUNDISCH(vSPECL avs (vASSUME ntm)) in
        vDISCH ntm (vGENL avs (vDISCH t (vCONJ lth_r lth_p)))
      else
        vDISCH itm (vGENL avs (vCONJ (vSPECL avs rcl) (vSPECL avs (vASSUME itm)))) in
    let mimps = map2 modify_rule (vCONJUNCTS sth) (conjuncts iant) in
    let th1 = end_itlist (fun th th' -> vMATCH_IMPS(vCONJ th th')) mimps in
    let th2 = vBETA_RULE(vSPECL prs jth) in
    let th3 = vIMP_TRANS th1 th2 in
    let nasm = lhand(concl th3) in
    let th4 = vGENL ps (vDISCH nasm (weaken_triv(vUNDISCH th3))) in
    vGENL svs (prove_monotonicity_hyps th4);;
