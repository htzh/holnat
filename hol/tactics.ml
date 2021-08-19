(* ========================================================================= *)
(* System of tactics (slightly different from any traditional LCF method).   *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2012                         *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Printer
open Parser
open Equal
open Bool
open Drule

(* ------------------------------------------------------------------------- *)
(* The common case of trivial instantiations.                                *)
(* ------------------------------------------------------------------------- *)

let null_inst = ([],[],[] :instantiation);;

let null_meta = (([]:term list),null_inst);;

(* ------------------------------------------------------------------------- *)
(* A goal has labelled assumptions, and the hyps are now thms.               *)
(* ------------------------------------------------------------------------- *)

type goal = (string * thm) list * term;;

let equals_goal ((a,w):goal) ((a',w'):goal) =
  forall2 (fun (s,th) (s',th') -> s = s' && equals_thm th th') a a' && w = w';;

(* ------------------------------------------------------------------------- *)
(* A justification function for a goalstate [A1 ?- g1; ...; An ?- gn],       *)
(* starting from an initial goal A ?- g, is a function f such that for any   *)
(* instantiation @:                                                          *)
(*                                                                           *)
(*   f(@) [A1@ |- g1@; ...; An@ |- gn@] = A@ |- g@                           *)
(* ------------------------------------------------------------------------- *)

type justification = instantiation -> thm list -> thm;;

(* ------------------------------------------------------------------------- *)
(* The goalstate stores the subgoals, justification, current instantiation,  *)
(* and a list of metavariables.                                              *)
(* ------------------------------------------------------------------------- *)

type goalstate = (term list * instantiation) * goal list * justification;;

(* ------------------------------------------------------------------------- *)
(* A goalstack is just a list of goalstates. Could go for more...            *)
(* ------------------------------------------------------------------------- *)

type goalstack = goalstate list;;

(* ------------------------------------------------------------------------- *)
(* A refinement, applied to a goalstate [A1 ?- g1; ...; An ?- gn]            *)
(* yields a new goalstate with updated justification function, to            *)
(* give a possibly-more-instantiated version of the initial goal.            *)
(* ------------------------------------------------------------------------- *)

type refinement = goalstate -> goalstate;;

(* ------------------------------------------------------------------------- *)
(* A tactic, applied to a goal A ?- g, returns:                              *)
(*                                                                           *)
(*  o A list of new metavariables introduced                                 *)
(*  o An instantiation (%)                                                   *)
(*  o A list of subgoals                                                     *)
(*  o A justification f such that for any instantiation @ we have            *)
(*    f(@) [A1@  |- g1@; ...; An@ |- gn@] = A(%;@) |- g(%;@)                 *)
(* ------------------------------------------------------------------------- *)

type tactic = goal -> goalstate;;

type thm_tactic = thm -> tactic;;

type thm_tactical = thm_tactic -> thm_tactic;;

(* ------------------------------------------------------------------------- *)
(* Apply instantiation to a goal.                                            *)
(* ------------------------------------------------------------------------- *)

let (inst_goal:instantiation->goal->goal) =
  fun p (thms,w) ->
    map (vI $-$ vINSTANTIATE_ALL p) thms,instantiate p w;;

(* ------------------------------------------------------------------------- *)
(* Perform a sequential composition (left first) of instantiations.          *)
(* ------------------------------------------------------------------------- *)

let (compose_insts :instantiation->instantiation->instantiation) =
  fun (pats1,tmin1,tyin1) ((pats2,tmin2,tyin2) as i2) ->
    let tmin = map (instantiate i2 $-$ inst tyin2) tmin1
    and tyin = map (type_subst tyin2 $-$ vI) tyin1 in
    let tmin' = filter (fun (_,x) -> not (can (rev_assoc x) tmin)) tmin2
    and tyin' = filter (fun (_,a) -> not (can (rev_assoc a) tyin)) tyin2 in
    pats1@pats2,tmin@tmin',tyin@tyin';;

(* ------------------------------------------------------------------------- *)
(* Construct A,_FALSITY_ |- p; contortion so falsity is the last element.    *)
(* ------------------------------------------------------------------------- *)

let _FALSITY_ = new_definition (parse_term "_FALSITY_ = F");;

let mk_fthm =
  let pth = vUNDISCH(fst(vEQ_IMP_RULE _FALSITY_))
  and qth = vASSUME (parse_term "_FALSITY_") in
  fun (asl,c) -> vPROVE_HYP qth (itlist vADD_ASSUM (rev asl) (vCONTR c pth));;

(* ------------------------------------------------------------------------- *)
(* Validity checking of tactics. This cannot be 100% accurate without making *)
(* arbitrary theorems, but "mk_fthm" brings us quite close.                  *)
(* ------------------------------------------------------------------------- *)

let (vVALID:tactic->tactic) =
  let fake_thm (asl,w) =
    let asms = itlist (union -| hyp -| snd) asl [] in
    mk_fthm(asms,w)
  and false_tm = (parse_term "_FALSITY_") in
  fun tac (asl,w) ->
    let ((_mvs,i),gls,just as res) = tac (asl,w) in
    let ths = map fake_thm gls in
    let asl',w' = dest_thm(just null_inst ths) in
    let asl'',w'' = inst_goal i (asl,w) in
    let maxasms =
      itlist (fun (_,th) -> union (insert (concl th) (hyp th))) asl'' [] in
    if aconv w' w'' &&
       forall (fun t -> exists (aconv t) maxasms) (subtract asl' [false_tm])
    then res else failwith "VALID: Invalid tactic";;

(* ------------------------------------------------------------------------- *)
(* Various simple combinators for tactics, identity tactic etc.              *)
(* ------------------------------------------------------------------------- *)

let (+-->),(+--->) =
  let propagate_empty _i = function [] -> [] | _ -> assert false
  and propagate_thm th i = function [] ->  vINSTANTIATE_ALL i th | _ -> assert false in
  let compose_justs n just1 just2 insts2 i ths =
    let ths1,ths2 = chop_list n ths in
    (just1 (compose_insts insts2 i) ths1)::(just2 i ths2) in
  let rec seqapply l1 l2 = match (l1,l2) with
     ([],[]) -> null_meta,[],propagate_empty
   | ((tac:tactic)::tacs),((goal:goal)::goals) ->
            let ((mvs1,insts1),gls1,just1) = tac goal in
            let goals' = map (inst_goal insts1) goals in
            let ((mvs2,insts2),gls2,just2) = seqapply tacs goals' in
            ((union mvs1 mvs2,compose_insts insts1 insts2),
             (map (inst_goal insts2) gls1)@gls2,compose_justs (length gls1) just1 just2 insts2)
   | _,_ -> failwith "seqapply: Length mismatch" in
  let justsequence just1 just2 insts2 i ths =
    just1 (compose_insts insts2 i) (just2 i ths) in
  let tacsequence ((mvs1,insts1),gls1,just1) tacl =
    let ((mvs2,insts2),gls2,just2) = seqapply tacl gls1 in
    let jst = justsequence just1 just2 insts2 in
    let just = if gls2 = [] then propagate_thm (jst null_inst []) else jst in
    ((union mvs1 mvs2,compose_insts insts1 insts2),gls2,just) in
  let (then_: tactic -> tactic -> tactic) =
    fun tac1 tac2 g ->
      let _,gls,_ as gstate = tac1 g in
      tacsequence gstate (replicate tac2 (length gls))
  and (thenl_: tactic -> tactic list -> tactic) =
    fun tac1 tac2l g ->
      let _,gls,_ as gstate = tac1 g in
      if gls = [] then tacsequence gstate []
      else tacsequence gstate tac2l in
  then_,thenl_;;

let ((|--->): tactic -> tactic -> tactic) =
  fun tac1 tac2 g ->
    try tac1 g with Failure _ -> tac2 g;;

let (vFAIL_TAC: string -> tactic) =
  fun tok _g -> failwith tok;;

let (vNO_TAC: tactic) =
  vFAIL_TAC "NO_TAC";;

let (vALL_TAC:tactic) =
  fun g -> null_meta,[g],fun _ -> function [th] -> th | _ -> assert false;;

let vTRY tac =
  tac |---> vALL_TAC;;

let rec vREPEAT tac g =
  ((tac +--> vREPEAT tac) |---> vALL_TAC) g;;

let vEVERY tacl =
  itlist (fun t1 t2 -> t1 +--> t2) tacl vALL_TAC;;

let (vFIRST: tactic list -> tactic) =
  fun tacl g -> end_itlist (fun t1 t2 -> t1 |---> t2) tacl g;;

let vMAP_EVERY tacf lst =
  vEVERY (map tacf lst);;

let vMAP_FIRST tacf lst =
  vFIRST (map tacf lst);;

let (vCHANGED_TAC: tactic -> tactic) =
  fun tac g ->
    let (meta,gl,_ as gstate) = tac g in
    if meta = null_meta && length gl = 1 && equals_goal (hd gl) g
    then failwith "CHANGED_TAC" else gstate;;

let rec vREPLICATE_TAC n tac =
  if n <= 0 then vALL_TAC else tac +--> (vREPLICATE_TAC (n - 1) tac);;

(* ------------------------------------------------------------------------- *)
(* Combinators for theorem continuations / "theorem tacticals".              *)
(* ------------------------------------------------------------------------- *)

let ((+++->): thm_tactical -> thm_tactical -> thm_tactical) =
  fun ttcl1 ttcl2 ttac -> ttcl1 (ttcl2 ttac);;

let ((|||->): thm_tactical -> thm_tactical -> thm_tactical) =
  fun ttcl1 ttcl2 ttac th ->
    try ttcl1 ttac th with Failure _ -> ttcl2 ttac th;;

let rec vREPEAT_TCL ttcl ttac th =
  ((ttcl +++-> (vREPEAT_TCL ttcl)) |||-> vI) ttac th;;

let (vREPEAT_GTCL: thm_tactical -> thm_tactical) =
  let rec vREPEAT_GTCL ttcl ttac th g =
    try ttcl (vREPEAT_GTCL ttcl ttac) th g with Failure _ -> ttac th g in
  vREPEAT_GTCL;;

let (vALL_THEN: thm_tactical) =
  vI;;

let (vNO_THEN: thm_tactical) =
  fun _ttac _th -> failwith "NO_THEN";;

let vEVERY_TCL ttcll =
  itlist (fun t1 t2 -> t1 +++-> t2) ttcll vALL_THEN;;

let vFIRST_TCL ttcll =
  end_itlist (fun t1 t2 -> t1 |||-> t2) ttcll;;

(* ------------------------------------------------------------------------- *)
(* Tactics to augment assumption list. Note that to allow "ASSUME p" for     *)
(* any assumption "p", these add a PROVE_HYP in the justification function,  *)
(* just in case.                                                             *)
(* ------------------------------------------------------------------------- *)

let (vLABEL_TAC: string -> thm_tactic) =
  fun s thm (asl,w) ->
    null_meta,[(s,thm)::asl,w],
    fun i -> function [th] -> vPROVE_HYP (vINSTANTIATE_ALL i thm) th | _ -> assert false;;

let vASSUME_TAC = vLABEL_TAC "";;

(* ------------------------------------------------------------------------- *)
(* Manipulation of assumption list.                                          *)
(* ------------------------------------------------------------------------- *)

let (vFIND_ASSUM: thm_tactic -> term -> tactic) =
  fun ttac t ((asl,_w) as g) ->
    ttac(snd(find (fun (_,th) -> concl th = t) asl)) g;;

let (vPOP_ASSUM: thm_tactic -> tactic) =
  fun ttac ->
   function (((_,th)::asl),w) -> ttac th (asl,w)
    | _ -> failwith "POP_ASSUM: No assumption to pop";;

let (vASSUM_LIST: (thm list -> tactic) -> tactic) =
    fun aslfun (asl,w) -> aslfun (map snd asl) (asl,w);;

let (vPOP_ASSUM_LIST: (thm list -> tactic) -> tactic) =
  fun asltac (asl,w) -> asltac (map snd asl) ([],w);;

let (vEVERY_ASSUM: thm_tactic -> tactic) =
  fun ttac -> vASSUM_LIST (vMAP_EVERY ttac);;

let (vFIRST_ASSUM: thm_tactic -> tactic) =
  fun ttac (asl,_w as g) -> tryfind (fun (_,th) -> ttac th g) asl;;

let (vRULE_ASSUM_TAC :(thm->thm)->tactic) =
  fun rule (asl,w) -> (vPOP_ASSUM_LIST(vK vALL_TAC) +-->
                       vMAP_EVERY (fun (s,th) -> vLABEL_TAC s (rule th))
                                 (rev asl)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Operate on assumption identified by a label.                              *)
(* ------------------------------------------------------------------------- *)

let (vUSE_THEN:string->thm_tactic->tactic) =
  fun s ttac (asl,_w as gl) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption "^s) in
    ttac th gl;;

let (vREMOVE_THEN:string->thm_tactic->tactic) =
  fun s ttac (asl,w) ->
    let th = try assoc s asl with Failure _ ->
             failwith("USE_TAC: didn't find assumption "^s) in
    let asl1,asl2 = chop_list(index s (map fst asl)) asl in
    let asl' = asl1 @ tl asl2 in
    ttac th (asl',w);;

(* ------------------------------------------------------------------------- *)
(* General tools to augment a required set of theorems with assumptions.     *)
(* Here ASM uses all current hypotheses of the goal, while HYP uses only     *)
(* those whose labels are given in the string argument.                      *)
(* ------------------------------------------------------------------------- *)

let (vASM :(thm list -> tactic)->(thm list -> tactic)) =
  fun tltac ths (asl,_w as g) -> tltac (map snd asl @ ths) g;;

let vHYP =
  let ident = function
      Ident s::rest when isalnum s -> s,rest
    | _ -> raise Noparse in
  let parse_using = many ident in
  let vHYP_LIST tac l =
    rev_itlist (fun s k l -> vUSE_THEN s (fun th -> k (th::l))) l tac in
  fun tac s ->
    let l,rest = (fix "Using pattern" parse_using -| lex -| explode) s in
    if rest=[] then vHYP_LIST tac l else failwith "Invalid using pattern";;

(* ------------------------------------------------------------------------- *)
(* Basic tactic to use a theorem equal to the goal. Does *no* matching.      *)
(* ------------------------------------------------------------------------- *)

let (vACCEPT_TAC: thm_tactic) =
  let propagate_thm th i = function [] -> vINSTANTIATE_ALL i th | _ -> assert false in
  fun th (_asl,w) ->
    if aconv (concl th) w then
      null_meta,[],propagate_thm th
    else failwith "ACCEPT_TAC";;

(* ------------------------------------------------------------------------- *)
(* Create tactic from a conversion. This allows the conversion to return     *)
(* |- p rather than |- p = T on a term "p". It also eliminates any goals of  *)
(* the form "T" automatically.                                               *)
(* ------------------------------------------------------------------------- *)

let (vCONV_TAC: conv -> tactic) =
  let t_tm = (parse_term "T") in
  fun conv ((asl,w) as g) ->
    let th = conv w in
    let tm = concl th in
    if aconv tm w then vACCEPT_TAC th g else
    let l,r = dest_eq tm in
    if not(aconv l w) then failwith "CONV_TAC: bad equation" else
    if r = t_tm then vACCEPT_TAC(vEQT_ELIM th) g else
    let th' = vSYM th in
    null_meta,[asl,r],fun i -> function [th] -> vEQ_MP (vINSTANTIATE_ALL i th') th | _ -> assert false;;

(* ------------------------------------------------------------------------- *)
(* Tactics for equality reasoning.                                           *)
(* ------------------------------------------------------------------------- *)

let (vREFL_TAC: tactic) =
  fun ((_asl,w) as g) ->
    try vACCEPT_TAC(vREFL(rand w)) g
    with Failure _ -> failwith "REFL_TAC";;

let (vABS_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_eq w in
        let lv,lb = dest_abs l
        and rv,rb = dest_abs r in
        let avoids = itlist (union -| thm_frees -| snd) asl (frees w) in
        let v = mk_primed_var avoids lv in
        null_meta,[asl,mk_eq(vsubst[v,lv] lb,vsubst[v,rv] rb)],
        fun i -> function [th] -> let ath = vABS v th in
                      vEQ_MP (vALPHA (concl ath) (instantiate i w)) ath
                | _ -> assert false
    with Failure _ -> failwith "ABS_TAC";;

let (vMK_COMB_TAC: tactic) =
  fun (asl,gl) ->
    try let l,r = dest_eq gl in
        let f,x = dest_comb l
        and g,y = dest_comb r in
        null_meta,[asl,mk_eq(f,g); asl,mk_eq(x,y)],
        fun _ -> function [th1;th2] -> vMK_COMB(th1,th2) | _ -> assert false
    with Failure _ -> failwith "MK_COMB_TAC";;

let (vAP_TERM_TAC: tactic) =
  let tac = vMK_COMB_TAC +---> [vREFL_TAC; vALL_TAC] in
  fun gl -> try tac gl with Failure _ -> failwith "AP_TERM_TAC";;

let (vAP_THM_TAC: tactic) =
  let tac = vMK_COMB_TAC +---> [vALL_TAC; vREFL_TAC] in
  fun gl -> try tac gl with Failure _ -> failwith "AP_THM_TAC";;

let (vBINOP_TAC: tactic) =
  let tac = vMK_COMB_TAC +---> [vAP_TERM_TAC; vALL_TAC] in
  fun gl -> try tac gl with Failure _ -> failwith "AP_THM_TAC";;

let (vSUBST1_TAC: thm_tactic) =
  fun th -> vCONV_TAC(vSUBS_CONV [th]);;

let vSUBST_ALL_TAC rth =
  vSUBST1_TAC rth +--> vRULE_ASSUM_TAC (vSUBS [rth]);;

let vBETA_TAC = vCONV_TAC(vREDEPTH_CONV vBETA_CONV);;

(* ------------------------------------------------------------------------- *)
(* Just use an equation to substitute if possible and uninstantiable.        *)
(* ------------------------------------------------------------------------- *)

let vSUBST_VAR_TAC th =
  try let asm,eq = dest_thm th in
      let l,r = dest_eq eq in
      if aconv l r then vALL_TAC
      else if not (subset (frees eq) (freesl asm)) then fail()
      else if (is_const l || is_var l) && not(free_in l r)
           then vSUBST_ALL_TAC th
      else if (is_const r || is_var r) && not(free_in r l)
           then vSUBST_ALL_TAC(vSYM th)
      else fail()
  with Failure _ -> failwith "SUBST_VAR_TAC";;

(* ------------------------------------------------------------------------- *)
(* Basic logical tactics.                                                    *)
(* ------------------------------------------------------------------------- *)

let (vDISCH_TAC: tactic) =
  let f_tm = (parse_term "F") in
  fun (asl,w) ->
    try let ant,c = dest_imp w in
        let th1 = vASSUME ant in
        null_meta,[("",th1)::asl,c],
        fun i -> function [th] -> vDISCH (instantiate i ant) th | _ -> assert false
    with Failure _ -> try
        let ant = dest_neg w in
        let th1 = vASSUME ant in
        null_meta,[("",th1)::asl,f_tm],
        fun i -> function [th] -> vNOT_INTRO(vDISCH (instantiate i ant) th) | _ -> assert false
    with Failure _ -> failwith "DISCH_TAC";;

let (vMP_TAC: thm_tactic) =
  fun thm (asl,w) ->
    null_meta,[asl,mk_imp(concl thm,w)],
    fun i -> function [th] -> vMP th (vINSTANTIATE_ALL i thm) | _ -> assert false;;

let (vEQ_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_eq w in
        null_meta,[asl, mk_imp(l,r); asl, mk_imp(r,l)],
        fun _ -> function [th1; th2] -> vIMP_ANTISYM_RULE th1 th2 | _ -> assert false
    with Failure _ -> failwith "EQ_TAC";;

let (vUNDISCH_TAC: term -> tactic) =
 fun tm (asl,w) ->
   try let sthm,asl' = remove (fun (_,asm) -> aconv (concl asm) tm) asl in
       let thm = snd sthm in
       null_meta,[asl',mk_imp(tm,w)],
       fun i -> function [th] -> vMP th (vINSTANTIATE_ALL i thm) | _ -> assert false
   with Failure _ -> failwith "UNDISCH_TAC";;

let (vSPEC_TAC: term * term -> tactic) =
  fun (t,x) (asl,w) ->
    try null_meta,[asl, mk_forall(x,subst[x,t] w)],
        fun i -> function [th] -> vSPEC (instantiate i t) th | _ -> assert false
    with Failure _ -> failwith "SPEC_TAC";;

let (vX_GEN_TAC: term -> tactic),
    (vX_CHOOSE_TAC: term -> thm_tactic),
    (vEXISTS_TAC: term -> tactic) =
  let tactic_type_compatibility_check pfx e g =
    let et = type_of e and gt = type_of g in
    if et = gt then ()
    else failwith(pfx ^ ": expected type :"^string_of_type et^" but got :"^
                  string_of_type gt) in
  let vX_GEN_TAC x' =
    if not(is_var x') then failwith "X_GEN_TAC: not a variable" else
    fun (asl,w) ->
        let x,bod = try dest_forall w
          with Failure _ -> failwith "X_GEN_TAC: Not universally quantified" in
        let _ = tactic_type_compatibility_check "X_GEN_TAC" x x' in
        let avoids = itlist (union -| thm_frees -| snd) asl (frees w) in
        if mem x' avoids then failwith "X_GEN_TAC: invalid variable" else
        let afn = vCONV_RULE(vGEN_ALPHA_CONV x) in
        null_meta,[asl,vsubst[x',x] bod],
        fun _i -> function [th] -> afn (vGEN x' th) | _ -> assert false
  and vX_CHOOSE_TAC x' xth =
        let xtm = concl xth in
        let x,bod = try dest_exists xtm
         with Failure _ -> failwith "X_CHOOSE_TAC: not existential" in
        let _ = tactic_type_compatibility_check "X_CHOOSE_TAC" x x' in
        let pat = vsubst[x',x] bod in
        let xth' = vASSUME pat in
        fun (asl,w) ->
          let avoids = itlist (union -| frees -| concl -| snd) asl
                              (union (frees w) (thm_frees xth)) in
          if mem x' avoids then failwith "X_CHOOSE_TAC: invalid variable" else
          null_meta,[("",xth')::asl,w],
          fun i -> function [th] -> vCHOOSE(x',vINSTANTIATE_ALL i xth) th | _ -> assert false
  and vEXISTS_TAC t (asl,w) =
    let v,bod = try dest_exists w with Failure _ ->
                failwith "EXISTS_TAC: Goal not existentially quantified" in
    let _ = tactic_type_compatibility_check "EXISTS_TAC" v t in
    null_meta,[asl,vsubst[t,v] bod],
    fun i -> function [th] -> vEXISTS (instantiate i w,instantiate i t) th | _ -> assert false in
  vX_GEN_TAC,vX_CHOOSE_TAC,vEXISTS_TAC;;

let (vGEN_TAC: tactic) =
  fun (asl,w) ->
    try let x = fst(dest_forall w) in
        let avoids = itlist (union -| thm_frees -| snd) asl (frees w) in
        let x' = mk_primed_var avoids x in
        vX_GEN_TAC x' (asl,w)
    with Failure _ -> failwith "GEN_TAC";;

let (vCHOOSE_TAC: thm_tactic) =
  fun xth ->
    try let x = fst(dest_exists(concl xth)) in
        fun (asl,w) ->
          let avoids = itlist (union -| thm_frees -| snd) asl
                              (union (frees w) (thm_frees xth)) in
          let x' = mk_primed_var avoids x in
          vX_CHOOSE_TAC x' xth (asl,w)
      with Failure _ -> failwith "CHOOSE_TAC";;

let (vCONJ_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_conj w in
        null_meta,[asl,l; asl,r],fun _ -> function [th1;th2] -> vCONJ th1 th2 | _ -> assert false
    with Failure _ -> failwith "CONJ_TAC";;

let (vDISJ1_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_disj w in
        null_meta,[asl,l],fun i -> function [th] -> vDISJ1 th (instantiate i r) | _ -> assert false
    with Failure _ -> failwith "DISJ1_TAC";;

let (vDISJ2_TAC: tactic) =
  fun (asl,w) ->
    try let l,r = dest_disj w in
          null_meta,[asl,r],fun i -> function [th] -> vDISJ2 (instantiate i l) th | _ -> assert false
    with Failure _ -> failwith "DISJ2_TAC";;

let (vDISJ_CASES_TAC: thm_tactic) =
  fun dth ->
    try let dtm = concl dth in
        let l,r = dest_disj dtm in
        let thl = vASSUME l
        and thr = vASSUME r in
        fun (asl,w) ->
          null_meta,[("",thl)::asl,w; ("",thr)::asl,w],
          fun i -> function [th1;th2] -> vDISJ_CASES (vINSTANTIATE_ALL i dth) th1 th2 | _ -> assert false
    with Failure _ -> failwith "DISJ_CASES_TAC";;

let (vCONTR_TAC: thm_tactic) =
  let propagate_thm th i = function [] -> vINSTANTIATE_ALL i th | _ -> assert false in
  fun cth (_asl,w) ->
    try let th = vCONTR w cth in
        null_meta,[],propagate_thm th
    with Failure _ -> failwith "CONTR_TAC";;

let (vMATCH_ACCEPT_TAC:thm_tactic) =
  let propagate_thm th i = function [] -> vINSTANTIATE_ALL i th | _ -> assert false in
  let rawtac th (_asl,w) =
    try let ith = vPART_MATCH vI th w in
        null_meta,[],propagate_thm ith
    with Failure _ -> failwith "ACCEPT_TAC" in
  fun th -> vREPEAT vGEN_TAC +--> rawtac th;;

let (vMATCH_MP_TAC :thm_tactic) =
  fun th ->
    let sth =
      try let tm = concl th in
          let avs,bod = strip_forall tm in
          let ant,con = dest_imp bod in
          let th1 = vSPECL avs (vASSUME tm) in
          let th2 = vUNDISCH th1 in
          let evs = filter (fun v -> vfree_in v ant && not (vfree_in v con))
                           avs in
          let th3 = itlist vSIMPLE_CHOOSE evs (vDISCH tm th2) in
          let tm3 = hd(hyp th3) in
          vMP (vDISCH tm (vGEN_ALL (vDISCH tm3 (vUNDISCH th3)))) th
      with Failure _ -> failwith "MATCH_MP_TAC: Bad theorem" in
    let match_fun = vPART_MATCH (snd -| dest_imp) sth in
    fun (asl,w) -> try let xth = match_fun w in
                       let lant = fst(dest_imp(concl xth)) in
                       null_meta,[asl,lant],
                       fun i -> function [th] -> vMP (vINSTANTIATE_ALL i xth) th | _ -> assert false
                   with Failure _ -> failwith "MATCH_MP_TAC: No match";;

let (vTRANS_TAC:thm->term->tactic) =
  fun th ->
    let ctm = snd(strip_forall(concl th)) in
    let cl,cr = dest_conj(lhand ctm) in
    let x = lhand cl and y = rand cl and z = rand cr in
    fun tm (_asl,w as gl) ->
      let lop,r = dest_comb w in
      let _op,l = dest_comb lop in
      let ilist =
        itlist2 type_match (map type_of [x;y;z])(map type_of [l;tm;r]) [] in
      let th' = vINST_TYPE ilist th in
      (vMATCH_MP_TAC th' +--> vEXISTS_TAC tm) gl;;

(* ------------------------------------------------------------------------- *)
(* Theorem continuations.                                                    *)
(* ------------------------------------------------------------------------- *)

let (vCONJUNCTS_THEN2:thm_tactic->thm_tactic->thm_tactic) =
  fun ttac1 ttac2 cth ->
      let c1,c2 = dest_conj(concl cth) in
      fun gl -> let ti,gls,jfn = (ttac1(vASSUME c1) +--> ttac2(vASSUME c2)) gl in
                let jfn' i ths =
                  let th1,th2 = vCONJ_PAIR(vINSTANTIATE_ALL i cth) in
                  vPROVE_HYP th1 (vPROVE_HYP th2 (jfn i ths)) in
                ti,gls,jfn';;

let (vCONJUNCTS_THEN: thm_tactical) =
  vW vCONJUNCTS_THEN2;;

let (vDISJ_CASES_THEN2:thm_tactic->thm_tactic->thm_tactic) =
  fun ttac1 ttac2 cth ->
    vDISJ_CASES_TAC cth +---> [vPOP_ASSUM ttac1; vPOP_ASSUM ttac2];;

let (vDISJ_CASES_THEN: thm_tactical) =
  vW vDISJ_CASES_THEN2;;

let (vDISCH_THEN: thm_tactic -> tactic) =
  fun ttac -> vDISCH_TAC +--> vPOP_ASSUM ttac;;

let (vX_CHOOSE_THEN: term -> thm_tactical) =
  fun x ttac th -> vX_CHOOSE_TAC x th +--> vPOP_ASSUM ttac;;

let (vCHOOSE_THEN: thm_tactical) =
  fun ttac th -> vCHOOSE_TAC th +--> vPOP_ASSUM ttac;;

(* ------------------------------------------------------------------------- *)
(* Various derived tactics and theorem continuations.                        *)
(* ------------------------------------------------------------------------- *)

let vSTRIP_THM_THEN =
  vFIRST_TCL [vCONJUNCTS_THEN; vDISJ_CASES_THEN; vCHOOSE_THEN];;

let (vANTE_RES_THEN: thm_tactical) =
  fun ttac ante ->
    vASSUM_LIST
     (fun asl ->
        let tacs = mapfilter (fun imp -> ttac (vMATCH_MP imp ante)) asl in
        if tacs = [] then failwith "IMP_RES_THEN"
        else vEVERY tacs);;

let (vIMP_RES_THEN: thm_tactical) =
  fun ttac imp ->
    vASSUM_LIST
     (fun asl ->
        let tacs = mapfilter (fun ante -> ttac (vMATCH_MP imp ante)) asl in
        if tacs = [] then failwith "IMP_RES_THEN"
        else vEVERY tacs);;

let vSTRIP_ASSUME_TAC =
  let vDISCARD_TAC th =
    let tm = concl th in
    fun (asl,_w as g) ->
       if exists (fun a -> aconv tm (concl(snd a))) asl then vALL_TAC g
       else failwith "DISCARD_TAC: not already present" in
  (vREPEAT_TCL vSTRIP_THM_THEN)
  (fun gth -> vFIRST [vCONTR_TAC gth; vACCEPT_TAC gth;
                     vDISCARD_TAC gth; vASSUME_TAC gth]);;

let vSTRUCT_CASES_THEN ttac = vREPEAT_TCL vSTRIP_THM_THEN ttac;;

let vSTRUCT_CASES_TAC = vSTRUCT_CASES_THEN
     (fun th -> vSUBST1_TAC th |---> vASSUME_TAC th);;

let vSTRIP_GOAL_THEN ttac =  vFIRST [vGEN_TAC; vCONJ_TAC; vDISCH_THEN ttac];;

let (vSTRIP_TAC: tactic) =
  fun g ->
    try vSTRIP_GOAL_THEN vSTRIP_ASSUME_TAC g
    with Failure _ -> failwith "STRIP_TAC";;

let (vUNDISCH_THEN:term->thm_tactic->tactic) =
  fun tm ttac (asl,w) ->
    let thp,asl' = remove (fun (_,th) -> aconv (concl th) tm) asl in
    ttac (snd thp) (asl',w);;

let vFIRST_X_ASSUM ttac =
    vFIRST_ASSUM(fun th -> vUNDISCH_THEN (concl th) ttac);;

(* ------------------------------------------------------------------------- *)
(* Subgoaling and freezing variables (latter is especially useful now).      *)
(* ------------------------------------------------------------------------- *)

let (vSUBGOAL_THEN: term -> thm_tactic -> tactic) =
  fun wa ttac (asl,w) ->
    let meta,gl,just = ttac (vASSUME wa) (asl,w) in
    meta,(asl,wa)::gl,fun i l -> vPROVE_HYP (hd l) (just i (tl l));;

let vSUBGOAL_TAC s tm prfs =
  match prfs with
   p::ps -> (warn (ps <> []) "SUBGOAL_TAC: additional subproofs ignored";
             vSUBGOAL_THEN tm (vLABEL_TAC s) +---> [p; vALL_TAC])
  | [] -> failwith "SUBGOAL_TAC: no subproof given";;

let (vFREEZE_THEN :thm_tactical) =
  fun ttac th (asl,w) ->
    let meta,gl,just = ttac (vASSUME(concl th)) (asl,w) in
    meta,gl,fun i l -> vPROVE_HYP th (just i l);;

(* ------------------------------------------------------------------------- *)
(* Metavariable tactics.                                                     *)
(* ------------------------------------------------------------------------- *)

let (vX_META_EXISTS_TAC: term -> tactic) =
  fun t (asl,w) ->
    try if not (is_var t) then fail() else
        let v,bod = dest_exists w in
        ([t],null_inst),[asl,vsubst[t,v] bod],
        fun i -> function [th] -> vEXISTS (instantiate i w,instantiate i t) th | _ -> assert false
    with Failure _ -> failwith "X_META_EXISTS_TAC";;

let vMETA_EXISTS_TAC ((asl,w) as gl) =
  let v = fst(dest_exists w) in
  let avoids = itlist (union -| frees -| concl -| snd) asl (frees w) in
  let v' = mk_primed_var avoids v in
  vX_META_EXISTS_TAC v' gl;;

let (vMETA_SPEC_TAC: term -> thm -> tactic) =
  fun t thm (asl,w) ->
    let sth = vSPEC t thm in
    ([t],null_inst),[(("",sth)::asl),w],
    fun i -> function [th] -> vPROVE_HYP (vSPEC (instantiate i t) thm) th | _ -> assert false;;

(* ------------------------------------------------------------------------- *)
(* If all else fails!                                                        *)
(* ------------------------------------------------------------------------- *)

let (vCHEAT_TAC:tactic) =
  fun (asl,w) -> vACCEPT_TAC(mk_thm([],w)) (asl,w);;

(* ------------------------------------------------------------------------- *)
(* Intended for time-consuming rules; delays evaluation till it sees goal.   *)
(* ------------------------------------------------------------------------- *)

let vRECALL_ACCEPT_TAC r a g = vACCEPT_TAC(time r a) g;;

(* ------------------------------------------------------------------------- *)
(* Split off antecedent of antecedent as a subgoal.                          *)
(* ------------------------------------------------------------------------- *)

let vANTS_TAC =
  let tm1 = (parse_term "p /\\ (q ==> r)")
  and tm2 = (parse_term "p ==> q") in
  let th1,th2 = vCONJ_PAIR(vASSUME tm1) in
  let th = itlist vDISCH [tm1;tm2] (vMP th2 (vMP(vASSUME tm2) th1)) in
  vMATCH_MP_TAC th +--> vCONJ_TAC;;

(* ------------------------------------------------------------------------- *)
(* A printer for goals etc.                                                  *)
(* ------------------------------------------------------------------------- *)

let (pp_print_goal:Format.formatter->goal->unit) =
  let string_of_int3 n =
    if n < 10 then "  "^string_of_int n
    else if n < 100 then " "^string_of_int n
    else string_of_int n in
  let print_hyp fmt n (s,th) =
    pp_open_hbox fmt ();
    Format.pp_print_string fmt (string_of_int3 n);
    Format.pp_print_string fmt " [";
    pp_open_hvbox fmt 0;
    pp_print_qterm fmt (concl th);
    pp_close_box fmt ();
    Format.pp_print_string fmt "]";
    (if not (s = "") then (Format.pp_print_string fmt (" ("^s^")")) else ());
    pp_close_box fmt ();
    Format.pp_print_newline fmt () in
  let rec print_hyps fmt n asl =
    if asl = [] then () else
    (print_hyp fmt n (hd asl);
     print_hyps fmt (n + 1) (tl asl)) in
  fun fmt (asl,w) ->
    Format.pp_print_newline fmt ();
    if asl <> [] then (print_hyps fmt 0 (rev asl); Format.pp_print_newline fmt ()) else ();
    pp_print_qterm fmt w; Format.pp_print_newline fmt ();;

let (pp_print_goalstack:Format.formatter->goalstack->unit) =
  let print_goalstate fmt k gs =
    let (_,gl,_) = gs in
    let n = length gl in
    let s = if n = 0 then "No subgoals" else
              (string_of_int k)^" subgoal"^(if k > 1 then "s" else "")
           ^" ("^(string_of_int n)^" total)" in
    Format.pp_print_string fmt s; Format.pp_print_newline fmt ();
    if gl = [] then () else
    do_list (pp_print_goal fmt -| vC el gl) (rev(0--(k-1))) in
  fun fmt l ->
    if l = [] then Format.pp_print_string fmt "Empty goalstack"
    else if tl l = [] then
      let (_,_gl,_ as gs) = hd l in
      print_goalstate fmt 1 gs
    else
      let (_,gl,_ as gs) = hd l
      and (_,gl0,_) = hd(tl l) in
      let p = length gl - length gl0 in
      let p' = if p < 1 then 1 else p + 1 in
      print_goalstate fmt p' gs;;

let print_goal = pp_print_goal Format.std_formatter;;
let print_goalstack = pp_print_goalstack Format.std_formatter;;

(* ------------------------------------------------------------------------- *)
(* Convert a tactic into a refinement on head subgoal in current state.      *)
(* ------------------------------------------------------------------------- *)

let (by:tactic->refinement) =
  fun tac ((mvs,inst),gls,just) ->
    if gls = [] then failwith "No goal set" else
    let g = hd gls
    and ogls = tl gls in
    let ((newmvs,newinst),subgls,subjust) = tac g in
    let n = length subgls in
    let mvs' = union newmvs mvs
    and inst' = compose_insts inst newinst
    and gls' = subgls @ map (inst_goal newinst) ogls in
    let just' i ths =
      let i' = compose_insts inst' i in
      let cths,oths = chop_list n ths in
      let sths = (subjust i cths) :: oths in
      just i' sths in
    (mvs',inst'),gls',just';;

(* ------------------------------------------------------------------------- *)
(* Rotate the goalstate either way.                                          *)
(* ------------------------------------------------------------------------- *)

let (rotate:int->refinement) =
  let rotate_p (meta,sgs,just) =
    let sgs' = (tl sgs)@[hd sgs] in
    let just' i ths =
      let ths' = (last ths)::(butlast ths) in
      just i ths' in
    (meta,sgs',just')
  and rotate_n (meta,sgs,just) =
    let sgs' = (last sgs)::(butlast sgs) in
    let just' i ths =
      let ths' = (tl ths)@[hd ths] in
      just i ths' in
    (meta,sgs',just') in
  fun n -> if n > 0 then funpow n rotate_p
           else funpow (-n) rotate_n;;

(* ------------------------------------------------------------------------- *)
(* Perform refinement proof, tactic proof etc.                               *)
(* ------------------------------------------------------------------------- *)

let (mk_goalstate:goal->goalstate) =
  fun (asl,w) ->
    if type_of w = bool_ty then
      null_meta,[asl,w],
      (fun inst -> function [th] -> vINSTANTIATE_ALL inst th | _ -> assert false)
    else failwith "mk_goalstate: Non-boolean goal";;

let (vTAC_PROOF : goal * tactic -> thm) =
  fun (g,tac) ->
    let gstate = mk_goalstate g in
    let _,sgs,just = by tac gstate in
    if sgs = [] then just null_inst []
    else failwith "TAC_PROOF: Unsolved goals";;

let prove(t,tac) =
  let th = vTAC_PROOF(([],t),tac) in
  let t' = concl th in
  if t' = t then th else
  try vEQ_MP (vALPHA t' t) th
  with Failure _ -> failwith "prove: justification generated wrong theorem";;

(* ------------------------------------------------------------------------- *)
(* Interactive "subgoal package" stuff.                                      *)
(* ------------------------------------------------------------------------- *)

let current_goalstack = ref ([] :goalstack);;

let (refine:refinement->goalstack) =
  fun r ->
    let l = !current_goalstack in
    if l = [] then failwith "No current goal" else
    let h = hd l in
    let res = r h :: l in
    current_goalstack := res;
    !current_goalstack;;

let flush_goalstack() =
  let l = !current_goalstack in
  current_goalstack := [hd l];;

let e tac = refine(by(vVALID tac));;

let r n = refine(rotate n);;

let set_goal(asl,w) =
  current_goalstack :=
    [mk_goalstate(map (fun t -> "",vASSUME t) asl,w)];
  !current_goalstack;;

let g t =
  let fvs = sort (<) (map (fst -| dest_var) (frees t)) in
  (if fvs <> [] then
     let errmsg = end_itlist (fun s t -> s^", "^t) fvs in
     warn true ("Free variables in goal: "^errmsg)
   else ());
   set_goal([],t);;

let b() =
  let l = !current_goalstack in
  if length l = 1 then failwith "Can't back up any more" else
  current_goalstack := tl l;
  !current_goalstack;;

let p() =
  !current_goalstack;;

let top_realgoal() =
  match !current_goalstack with (_,((asl,w)::_),_)::_ ->
  asl,w
  | _ -> assert false;;

let top_goal() =
  let asl,w = top_realgoal() in
  map (concl -| snd) asl,w;;

let top_thm() =
  match !current_goalstack with (_,[],f)::_ ->
  f null_inst []
  | _ -> assert false;;

(* ------------------------------------------------------------------------- *)
(* Install the goal-related printers.                                        *)
(* ------------------------------------------------------------------------- *)

