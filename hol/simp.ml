(* ========================================================================= *)
(* Simplification and rewriting.                                             *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Nets
open Parser
open Equal
open Bool
open Drule
open Tactics
open Itab

(* ------------------------------------------------------------------------- *)
(* Generalized conversion (conversion plus a priority).                      *)
(* ------------------------------------------------------------------------- *)

type gconv = int * conv;;

(* ------------------------------------------------------------------------- *)
(* Primitive rewriting conversions: unconditional and conditional equations. *)
(* ------------------------------------------------------------------------- *)

let vREWR_CONV = vPART_MATCH lhs;;

let vIMP_REWR_CONV = vPART_MATCH (lhs -| snd -| dest_imp);;

(* ------------------------------------------------------------------------- *)
(* Versions with ordered rewriting. We must have l' > r' for the rewrite     *)
(* |- l = r (or |- c ==> (l = r)) to apply.                                  *)
(* ------------------------------------------------------------------------- *)

let vORDERED_REWR_CONV ord th =
  let basic_conv = vREWR_CONV th in
  fun tm ->
    let thm = basic_conv tm in
    let l,r = dest_eq(concl thm) in
    if ord l r then thm
    else failwith "ORDERED_REWR_CONV: wrong orientation";;

let vORDERED_IMP_REWR_CONV ord th =
  let basic_conv = vIMP_REWR_CONV th in
  fun tm ->
    let thm = basic_conv tm in
    let l,r = dest_eq(rand(concl thm)) in
    if ord l r then thm
    else failwith "ORDERED_IMP_REWR_CONV: wrong orientation";;

(* ------------------------------------------------------------------------- *)
(* Standard AC-compatible term ordering: a "dynamic" lexicographic ordering. *)
(*                                                                           *)
(* This is a slight hack to make AC normalization work. However I *think*    *)
(* it's properly AC compatible, i.e. monotonic and total, WF on ground terms *)
(* (over necessarily finite signature) and with the properties for any       *)
(* binary operator +:                                                        *)
(*                                                                           *)
(*         (x + y) + z > x + (y + z)                                         *)
(*         x + y > y + x                   iff x > y                         *)
(*         x + (y + z) > y + (x + z)       iff x > y                         *)
(*                                                                           *)
(* The idea is that when invoking lex ordering with identical head operator  *)
(* "f", one sticks "f" at the head of an otherwise arbitrary ordering on     *)
(* subterms (the built-in CAML one). This avoids the potentially inefficient *)
(* calculation of term size in the standard orderings.                       *)
(* ------------------------------------------------------------------------- *)

let term_order =
  let rec lexify ord l1 l2 =
    if l1 = [] then false
    else if l2 = [] then true else
    let h1 = hd l1 and h2 = hd l2 in
    ord h1 h2 || (h1 = h2 && lexify ord (tl l1) (tl l2)) in
  let rec dyn_order top tm1 tm2 =
    let f1,args1 = strip_comb tm1
    and f2,args2 = strip_comb tm2 in
    if f1 = f2 then
      lexify (dyn_order f1) args1 args2
    else
      if f2 = top then false
      else if f1 = top then true
      else f1 > f2 in
  dyn_order (parse_term "T");;

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a theorem as a (cond) rewrite. The "rep" flag      *)
(* will cause any trivially looping rewrites to be modified, and any that    *)
(* are permutative to be ordered w.r.t. the standard order. The idea is that *)
(* this flag will be set iff the conversion is going to get repeated.        *)
(* This includes a completely ad hoc but useful special case for ETA_AX,     *)
(* which forces a first order match (otherwise it would loop on a lambda).   *)
(* ------------------------------------------------------------------------- *)

let net_of_thm rep th =
  let tm = concl th in
  let lconsts = freesl (hyp th) in
  let matchable = can -| term_match lconsts in
  match tm with
    Comb(Comb(Const("=",_),(Abs(x,Comb(Var(_s,_ty) as v,x')) as l)),v')
         when x' = x && v' = v && not(x = v) ->
        let conv tm =
          match tm with
            Abs(y,Comb(t,y')) when y = y' && not(free_in y t) ->
              vINSTANTIATE(term_match [] v t) th
          | _ -> failwith "REWR_CONV (ETA_AX special case)" in
        enter lconsts (l,(1,conv))
  | Comb(Comb(Const("=",_),l),r) ->
      if rep && free_in l r then
        let th' = vEQT_INTRO th in
        enter lconsts (l,(1,vREWR_CONV th'))
      else if rep && matchable l r && matchable r l then
        enter lconsts (l,(1,vORDERED_REWR_CONV term_order th))
      else enter lconsts (l,(1,vREWR_CONV th))
  | Comb(Comb(_,t),Comb(Comb(Const("=",_),l),r)) ->
        if rep && free_in l r then
          let th' = vDISCH t (vEQT_INTRO(vUNDISCH th)) in
          enter lconsts (l,(3,vIMP_REWR_CONV th'))
        else if rep && matchable l r && matchable r l then
          enter lconsts (l,(3,vORDERED_IMP_REWR_CONV term_order th))
        else enter lconsts(l,(3,vIMP_REWR_CONV th))
  | _ -> assert false;;

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a conversion with a term index.                    *)
(* ------------------------------------------------------------------------- *)

let net_of_conv tm conv sofar =
  enter [] (tm,(2,conv)) sofar;;

(* ------------------------------------------------------------------------- *)
(* Create a gconv net for a congruence rule (in canonical form!)             *)
(* ------------------------------------------------------------------------- *)

let net_of_cong th sofar =
  let conc,n = repeat (fun (tm,m) -> snd(dest_imp tm),m+1) (concl th,0) in
  if n = 0 then failwith "net_of_cong: Non-implicational congruence" else
  let pat = lhs conc in
  let conv = vGEN_PART_MATCH (lhand -| funpow n rand) th in
  enter [] (pat,(4,conv)) sofar;;

(* ------------------------------------------------------------------------- *)
(* Rewrite maker for ordinary and conditional rewrites (via "cf" flag).      *)
(*                                                                           *)
(* We follow Don in going from ~(s = t) to (s = t) = F *and* (t = s) = F.    *)
(* Well, why not? However, we don't abandon s = t where FV(t) is not a       *)
(* subset of FV(s) in favour of (s = t) = T, as he does.                     *)
(* Note: looping rewrites are not discarded here, only when netted.          *)
(* ------------------------------------------------------------------------- *)

let mk_rewrites =
  let vIMP_CONJ_CONV = vREWR_CONV(vITAUT (parse_term "p ==> q ==> r <=> p /\\ q ==> r"))
  and vIMP_EXISTS_RULE =
    let cnv = vREWR_CONV(vITAUT (parse_term "(!x. P x ==> Q) <=> (?x. P x) ==> Q")) in
    fun v th -> vCONV_RULE cnv (vGEN v th) in
  let collect_condition oldhyps th =
    let conds = subtract (hyp th) oldhyps in
    if conds = [] then th else
    let jth = itlist vDISCH conds th in
    let kth = vCONV_RULE (vREPEATC vIMP_CONJ_CONV) jth in
    let cond,eqn = dest_imp(concl kth) in
    let fvs = subtract (subtract (frees cond) (frees eqn)) (freesl oldhyps) in
    itlist vIMP_EXISTS_RULE fvs kth in
  let rec split_rewrites oldhyps cf th sofar =
    let tm = concl th in
    if is_forall tm then
      split_rewrites oldhyps cf (vSPEC_ALL th) sofar
    else if is_conj tm then
      split_rewrites oldhyps cf (vCONJUNCT1 th)
        (split_rewrites oldhyps cf (vCONJUNCT2 th) sofar)
    else if is_imp tm && cf then
      split_rewrites oldhyps cf (vUNDISCH th) sofar
    else if is_eq tm then
      (if cf then collect_condition oldhyps th else th)::sofar
    else if is_neg tm then
      let ths = split_rewrites oldhyps cf (vEQF_INTRO th) sofar in
      if is_eq (rand tm)
      then split_rewrites oldhyps cf (vEQF_INTRO (vGSYM th)) ths
      else ths
    else
      split_rewrites oldhyps cf (vEQT_INTRO th) sofar in
  fun cf th sofar -> split_rewrites (hyp th) cf th sofar;;

(* ------------------------------------------------------------------------- *)
(* Rewriting (and application of other conversions) based on a convnet.      *)
(* ------------------------------------------------------------------------- *)

let vREWRITES_CONV net tm =
  let pconvs = lookup tm net in
  try tryfind (fun (_,cnv) -> cnv tm) pconvs
  with Failure _ -> failwith "REWRITES_CONV";;

(* ------------------------------------------------------------------------- *)
(* Decision procedures may accumulate their state in different ways (e.g.    *)
(* term nets and predicate-indexed lists of Horn clauses). To allow mixing   *)
(* of arbitrary types for state storage, we use a trick due to RJB via DRS.  *)
(* ------------------------------------------------------------------------- *)

type prover = Prover of conv * (thm list -> prover);;

let mk_prover applicator augmentor =
  let rec mk_prover state =
    let apply = applicator state
    and augment thms = mk_prover (augmentor state thms) in
    Prover(apply,augment) in
  mk_prover;;

let augment(Prover(_,aug)) thms = aug thms;;

let apply_prover(Prover(conv,_)) tm = conv tm;;

(* ------------------------------------------------------------------------- *)
(* Type of simpsets. We have a convnet containing rewrites (implicational    *)
(* and otherwise), other term-indexed context-free conversions like          *)
(* BETA_CONV, and congruence rules. Then there is a list of provers that     *)
(* have their own way of storing and using context, and finally a rewrite    *)
(* maker function, to allow customization.                                   *)
(*                                                                           *)
(* We also have a type of (traversal) strategy, following Konrad.            *)
(* ------------------------------------------------------------------------- *)

type simpset =
  Simpset of gconv net                          (* Rewrites & congruences *)
           * (strategy -> strategy)             (* Prover for conditions  *)
           * prover list                        (* Subprovers for prover  *)
           * (thm -> thm list -> thm list)      (* Rewrite maker          *)

and strategy = simpset -> int -> term -> thm;;

(* ------------------------------------------------------------------------- *)
(* Very simple prover: recursively simplify then try provers.                *)
(* ------------------------------------------------------------------------- *)

let basic_prover strat (Simpset(_net,_prover,provers,_rewmaker) as ss) lev tm =
  let sth = try strat ss lev tm with Failure _ -> vREFL tm in
  try vEQT_ELIM sth
  with Failure _ ->
    let tth = tryfind (fun pr -> apply_prover pr (rand(concl sth))) provers in
    vEQ_MP (vSYM sth) tth;;

(* ------------------------------------------------------------------------- *)
(* Functions for changing or augmenting components of simpsets.              *)
(* ------------------------------------------------------------------------- *)

let ss_of_thms thms (Simpset(net,prover,provers,rewmaker)) =
  let cthms = itlist rewmaker thms [] in
  let net' = itlist (net_of_thm true) cthms net in
  Simpset(net',prover,provers,rewmaker);;

let ss_of_conv keytm conv (Simpset(net,prover,provers,rewmaker)) =
  let net' = net_of_conv keytm conv net in
  Simpset(net',prover,provers,rewmaker);;

let ss_of_congs thms (Simpset(net,prover,provers,rewmaker)) =
  let net' = itlist net_of_cong thms net in
  Simpset(net',prover,provers,rewmaker);;

let ss_of_prover newprover (Simpset(net,_,provers,rewmaker)) =
  Simpset(net,newprover,provers,rewmaker);;

let ss_of_provers newprovers (Simpset(net,prover,provers,rewmaker)) =
  Simpset(net,prover,newprovers@provers,rewmaker);;

let ss_of_maker newmaker (Simpset(net,prover,provers,_)) =
  Simpset(net,prover,provers,newmaker);;

(* ------------------------------------------------------------------------- *)
(* Perform a context-augmentation operation on a simpset.                    *)
(* ------------------------------------------------------------------------- *)

let vAUGMENT_SIMPSET cth (Simpset(net,prover,provers,rewmaker)) =
  let provers' = map (vC augment [cth]) provers in
  let cthms = rewmaker cth [] in
  let net' = itlist (net_of_thm true) cthms net in
  Simpset(net',prover,provers',rewmaker);;

(* ------------------------------------------------------------------------- *)
(* Depth conversions.                                                        *)
(* ------------------------------------------------------------------------- *)

let vONCE_DEPTH_SQCONV,vDEPTH_SQCONV,vREDEPTH_SQCONV,
    vTOP_DEPTH_SQCONV,vTOP_SWEEP_SQCONV =
  let vIMP_REWRITES_CONV strat (Simpset(_net,prover,_provers,_rewmaker) as ss) lev
                        pconvs tm =
    tryfind (fun (n,cnv) ->
      if n >= 4 then fail() else
      let th = cnv tm in
      let etm = concl th in
      if is_eq etm then th else
      if lev <= 0 then failwith "IMP_REWRITES_CONV: Too deep" else
      let cth = prover strat ss (lev-1) (lhand etm) in
      vMP th cth) pconvs in
  let rec vRUN_SUB_CONV strat ss lev triv th =
    let tm = concl th in
    if is_imp tm then
      let subtm = lhand tm in
      let avs,bod = strip_forall subtm in
      let (t,t'),ss',mk_fun =
        try dest_eq bod,ss,vI with Failure _ ->
        let cxt,deq = dest_imp bod in
        dest_eq deq,vAUGMENT_SIMPSET (vASSUME cxt) ss,vDISCH cxt in
      let eth,triv' = try strat ss' lev t,false with Failure _ -> vREFL t,triv in
      let eth' = vGENL avs (mk_fun eth) in
      let th' = if is_var t' then vINST [rand(concl eth),t'] th
                else vGEN_PART_MATCH lhand th (concl eth') in
      let th'' = vMP th' eth' in
      vRUN_SUB_CONV strat ss lev triv' th''
    else if triv then fail() else th in
  let vGEN_SUB_CONV strat ss lev pconvs tm =
    try tryfind (fun (n,cnv) ->
          if n < 4 then fail() else
          let th = cnv tm in
          vRUN_SUB_CONV strat ss lev true th) pconvs
    with Failure _ ->
        if is_comb tm then
          let l,r = dest_comb tm in
          try let th1 = strat ss lev l in
              try let th2 = strat ss lev r in vMK_COMB(th1,th2)
              with Failure _ -> vAP_THM th1 r
          with Failure _ -> vAP_TERM l (strat ss lev r)
        else if is_abs tm then
          let v,bod = dest_abs tm in
          let th = strat ss lev bod in
          try vABS v th with Failure _ ->
          let gv = genvar(type_of v) in
          let gbod = vsubst[gv,v] bod in
          let gth = vABS gv (strat ss lev gbod) in
          let gtm = concl gth in
          let l,r = dest_eq gtm in
          let v' = variant (frees gtm) v in
          let l' = alpha v' l and r' = alpha v' r in
          vEQ_MP (vALPHA gtm (mk_eq(l',r'))) gth
        else failwith "GEN_SUB_CONV" in
  let rec vONCE_DEPTH_SQCONV
       (Simpset(net,_prover,_provers,_rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    try vIMP_REWRITES_CONV vONCE_DEPTH_SQCONV ss lev pconvs tm
    with Failure _ ->
        vGEN_SUB_CONV vONCE_DEPTH_SQCONV ss lev pconvs tm in
  let rec vDEPTH_SQCONV (Simpset(net,_prover,_provers,_rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    try let th1 = vGEN_SUB_CONV vDEPTH_SQCONV ss lev pconvs tm in
        let tm1 = rand(concl th1) in
        let pconvs1 = lookup tm1 net in
        try vTRANS th1 (vIMP_REWRITES_CONV vDEPTH_SQCONV ss lev pconvs1 tm1)
        with Failure _ -> th1
    with Failure _ ->
        vIMP_REWRITES_CONV vDEPTH_SQCONV ss lev pconvs tm in
  let rec vREDEPTH_SQCONV (Simpset(net,_prover,_provers,_rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    let th =
      try let th1 = vGEN_SUB_CONV vREDEPTH_SQCONV ss lev pconvs tm in
          let tm1 = rand(concl th1) in
          let pconvs1 = lookup tm1 net in
          try vTRANS th1 (vIMP_REWRITES_CONV vREDEPTH_SQCONV ss lev pconvs1 tm1)
          with Failure _ -> th1
      with Failure _ ->
          vIMP_REWRITES_CONV vREDEPTH_SQCONV ss lev pconvs tm in
    try let th' = vREDEPTH_SQCONV ss lev (rand(concl th)) in
        vTRANS th th'
    with Failure _ -> th in
  let rec vTOP_DEPTH_SQCONV (Simpset(net,_prover,_provers,_rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    let th1 =
      try vIMP_REWRITES_CONV vTOP_DEPTH_SQCONV ss lev pconvs tm
      with Failure _ -> vGEN_SUB_CONV vTOP_DEPTH_SQCONV ss lev pconvs tm in
    try let th2 = vTOP_DEPTH_SQCONV ss lev (rand(concl th1)) in
            vTRANS th1 th2
    with Failure _ -> th1 in
  let rec vTOP_SWEEP_SQCONV (Simpset(net,_prover,_provers,_rewmaker) as ss) lev tm =
    let pconvs = lookup tm net in
    try let th1 = vIMP_REWRITES_CONV vTOP_SWEEP_SQCONV ss lev pconvs tm in
        try let th2 = vTOP_SWEEP_SQCONV ss lev (rand(concl th1)) in
            vTRANS th1 th2
        with Failure _ -> th1
    with Failure _ -> vGEN_SUB_CONV vTOP_SWEEP_SQCONV ss lev pconvs tm in
  vONCE_DEPTH_SQCONV,vDEPTH_SQCONV,vREDEPTH_SQCONV,
  vTOP_DEPTH_SQCONV,vTOP_SWEEP_SQCONV;;

(* ------------------------------------------------------------------------- *)
(* Maintenence of basic rewrites and conv nets for rewriting.                *)
(* ------------------------------------------------------------------------- *)

let set_basic_rewrites,extend_basic_rewrites,basic_rewrites,
    set_basic_convs,extend_basic_convs,basic_convs,basic_net =
  let rewrites = ref ([]:thm list)
  and conversions = ref ([]:(string*(term*conv))list)
  and conv_net = ref (empty_net: gconv net) in
  let rehash_convnet() =
    conv_net := itlist (net_of_thm true) (!rewrites)
        (itlist (fun (_,(pat,cnv)) -> net_of_conv pat cnv) (!conversions)
                empty_net) in
  let set_basic_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := canon_thl; rehash_convnet())
  and extend_basic_rewrites thl =
    let canon_thl = itlist (mk_rewrites false) thl [] in
    (rewrites := canon_thl @ !rewrites; rehash_convnet())
  and basic_rewrites() = !rewrites
  and set_basic_convs cnvs =
    (conversions := cnvs; rehash_convnet())
  and extend_basic_convs (name,patcong) =
    (conversions :=
      (name,patcong)::filter(fun (name',_) -> name <> name') (!conversions);
     rehash_convnet())
  and basic_convs() = !conversions
  and basic_net() = !conv_net in
  set_basic_rewrites,extend_basic_rewrites,basic_rewrites,
  set_basic_convs,extend_basic_convs,basic_convs,basic_net;;

(* ------------------------------------------------------------------------- *)
(* Same thing for the default congruences.                                   *)
(* ------------------------------------------------------------------------- *)

let set_basic_congs,extend_basic_congs,basic_congs =
  let congs = ref ([]:thm list) in
  (fun thl -> congs := thl),
  (fun thl -> congs := union' equals_thm thl (!congs)),
  (fun () -> !congs);;

(* ------------------------------------------------------------------------- *)
(* Main rewriting conversions.                                               *)
(* ------------------------------------------------------------------------- *)

let vGENERAL_REWRITE_CONV rep (cnvl:conv->conv) (builtin_net:gconv net) thl =
  let thl_canon = itlist (mk_rewrites false) thl [] in
  let final_net = itlist (net_of_thm rep) thl_canon builtin_net in
  cnvl (vREWRITES_CONV final_net);;

let vGEN_REWRITE_CONV (cnvl:conv->conv) thl =
  vGENERAL_REWRITE_CONV false cnvl empty_net thl;;

let vPURE_REWRITE_CONV thl =
  vGENERAL_REWRITE_CONV true vTOP_DEPTH_CONV empty_net thl;;

let vREWRITE_CONV thl =
  vGENERAL_REWRITE_CONV true vTOP_DEPTH_CONV (basic_net()) thl;;

let vPURE_ONCE_REWRITE_CONV thl =
  vGENERAL_REWRITE_CONV false vONCE_DEPTH_CONV empty_net thl;;

let vONCE_REWRITE_CONV thl =
  vGENERAL_REWRITE_CONV false vONCE_DEPTH_CONV (basic_net()) thl;;

(* ------------------------------------------------------------------------- *)
(* Rewriting rules and tactics.                                              *)
(* ------------------------------------------------------------------------- *)

let vGEN_REWRITE_RULE cnvl thl = vCONV_RULE(vGEN_REWRITE_CONV cnvl thl);;

let vPURE_REWRITE_RULE thl = vCONV_RULE(vPURE_REWRITE_CONV thl);;

let vREWRITE_RULE thl = vCONV_RULE(vREWRITE_CONV thl);;

let vPURE_ONCE_REWRITE_RULE thl = vCONV_RULE(vPURE_ONCE_REWRITE_CONV thl);;

let vONCE_REWRITE_RULE thl = vCONV_RULE(vONCE_REWRITE_CONV thl);;

let vPURE_ASM_REWRITE_RULE thl th =
    vPURE_REWRITE_RULE ((map vASSUME (hyp th)) @ thl) th;;

let vASM_REWRITE_RULE thl th =
    vREWRITE_RULE ((map vASSUME (hyp th)) @ thl) th;;

let vPURE_ONCE_ASM_REWRITE_RULE thl th =
    vPURE_ONCE_REWRITE_RULE ((map vASSUME (hyp th)) @ thl) th;;

let vONCE_ASM_REWRITE_RULE thl th =
    vONCE_REWRITE_RULE ((map vASSUME (hyp th)) @ thl) th;;

let vGEN_REWRITE_TAC cnvl thl = vCONV_TAC(vGEN_REWRITE_CONV cnvl thl);;

let vPURE_REWRITE_TAC thl = vCONV_TAC(vPURE_REWRITE_CONV thl);;

let vREWRITE_TAC thl = vCONV_TAC(vREWRITE_CONV thl);;

let vPURE_ONCE_REWRITE_TAC thl = vCONV_TAC(vPURE_ONCE_REWRITE_CONV thl);;

let vONCE_REWRITE_TAC thl = vCONV_TAC(vONCE_REWRITE_CONV thl);;

let (vPURE_ASM_REWRITE_TAC: thm list -> tactic) =
  vASM vPURE_REWRITE_TAC;;

let (vASM_REWRITE_TAC: thm list -> tactic) =
  vASM vREWRITE_TAC;;

let (vPURE_ONCE_ASM_REWRITE_TAC: thm list -> tactic) =
  vASM vPURE_ONCE_REWRITE_TAC;;

let (vONCE_ASM_REWRITE_TAC: thm list -> tactic) =
  vASM vONCE_REWRITE_TAC;;

(* ------------------------------------------------------------------------- *)
(* Simplification functions.                                                 *)
(* ------------------------------------------------------------------------- *)

let vGEN_SIMPLIFY_CONV (strat:strategy) ss lev thl =
  let ss' = itlist vAUGMENT_SIMPSET thl ss in
  vTRY_CONV (strat ss' lev);;

let vONCE_SIMPLIFY_CONV ss = vGEN_SIMPLIFY_CONV vONCE_DEPTH_SQCONV ss 1;;

let vSIMPLIFY_CONV ss = vGEN_SIMPLIFY_CONV vTOP_DEPTH_SQCONV ss 3;;

(* ------------------------------------------------------------------------- *)
(* Simple but useful default version.                                        *)
(* ------------------------------------------------------------------------- *)

let empty_ss = Simpset(empty_net,basic_prover,[],mk_rewrites true);;

let basic_ss =
  let rewmaker = mk_rewrites true in
  fun thl ->
    let cthms = itlist rewmaker thl [] in
    let net' = itlist (net_of_thm true) cthms (basic_net()) in
    let net'' = itlist net_of_cong (basic_congs()) net' in
  Simpset(net'',basic_prover,[],rewmaker);;

let vSIMP_CONV thl = vSIMPLIFY_CONV (basic_ss []) thl;;

let vPURE_SIMP_CONV thl = vSIMPLIFY_CONV empty_ss thl;;

let vONCE_SIMP_CONV thl = vONCE_SIMPLIFY_CONV (basic_ss []) thl;;

let vSIMP_RULE thl = vCONV_RULE(vSIMP_CONV thl);;

let vPURE_SIMP_RULE thl = vCONV_RULE(vPURE_SIMP_CONV thl);;

let vONCE_SIMP_RULE thl = vCONV_RULE(vONCE_SIMP_CONV thl);;

let vSIMP_TAC thl = vCONV_TAC(vSIMP_CONV thl);;

let vPURE_SIMP_TAC thl = vCONV_TAC(vPURE_SIMP_CONV thl);;

let vONCE_SIMP_TAC thl = vCONV_TAC(vONCE_SIMP_CONV thl);;

let vASM_SIMP_TAC = vASM vSIMP_TAC;;

let vPURE_ASM_SIMP_TAC = vASM vPURE_SIMP_TAC;;

let vONCE_ASM_SIMP_TAC = vASM vONCE_SIMP_TAC;;

(* ------------------------------------------------------------------------- *)
(* Abbreviation tactics.                                                     *)
(* ------------------------------------------------------------------------- *)

let vABBREV_TAC tm =
  let cvs,t = dest_eq tm in
  let v,vs = strip_comb cvs in
  let rs = list_mk_abs(vs,t) in
  let eq = mk_eq(rs,v) in
  let th1 = itlist (fun v th -> vCONV_RULE(vLAND_CONV vBETA_CONV) (vAP_THM th v))
                   (rev vs) (vASSUME eq) in
  let th2 = vSIMPLE_CHOOSE v (vSIMPLE_EXISTS v (vGENL vs th1)) in
  let th3 = vPROVE_HYP (vEXISTS(mk_exists(v,eq),rs) (vREFL rs)) th2 in
  fun (asl,w as gl) ->
    let avoids = itlist (union -| frees -| concl -| snd) asl (frees w) in
    if mem v avoids then failwith "ABBREV_TAC: variable already used" else
    vCHOOSE_THEN
     (fun th -> vRULE_ASSUM_TAC(vPURE_ONCE_REWRITE_RULE[th]) ---->
                vPURE_ONCE_REWRITE_TAC[th] ---->
                vASSUME_TAC th)
     th3 gl;;

let vEXPAND_TAC s = vFIRST_ASSUM(vSUBST1_TAC -| vSYM -|
  check((=) s -| fst -| dest_var -| rhs -| concl)) ----> vBETA_TAC;;
