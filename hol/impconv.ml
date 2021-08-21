(* ========================================================================= *)
(* Implicational conversions, implicational rewriting and target rewriting.  *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Analysis and Design of Dependable Systems                *)
(*                  fortiss GmbH, Munich, Germany                            *)
(*                                                                           *)
(*       Formerly:  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent.aravantinos@fortiss.org>                      *)
(*                                                                           *)
(*            Distributed under the same license as HOL Light.               *)
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
open Canon

let vIMP_REWRITE_TAC,vTARGET_REWRITE_TAC,vHINT_EXISTS_TAC,
    vSEQ_IMP_REWRITE_TAC,vCASE_REWRITE_TAC =

let vI = fun x -> x in

(* Same as [UNDISCH] but also returns the undischarged term *)
let vUNDISCH_TERM th =
  let p = (fst -| dest_imp -| concl) th in
  p,vUNDISCH th in

(* Same as [UNDISCH_ALL] but also returns the undischarged terms *)
let rec vUNDISCH_TERMS th =
  try
    let t,th' = vUNDISCH_TERM th in
    let ts,th'' = vUNDISCH_TERMS th' in
    t::ts,th''
  with Failure _ -> [],th in

(* Comblies the function [f] to the conclusion of an implicational theorem. *)
let vMAP_CONCLUSION f th =
  let p,th = vUNDISCH_TERM th in
  vDISCH p (f th) in

let strip_conj = binops (parse_term "(/\\)") in

(* For a list [f1;...;fk], returns the first [fi x] that succeeds. *)
let rec tryfind_fun fs x =
  match fs with
  |[] -> failwith "tryfind_fun"
  |f::fs' -> try f x with Failure _ -> tryfind_fun fs' x in

(* Same as [mapfilter] but also provides the rank of the iteration as an
 * argument to [f]. *)
let mapfilteri f =
  let rec self i = function
    |[] -> []
    |h::t ->
        let rest = self (i+1) t in
        try f i h :: rest with Failure _ -> rest
  in
  self 0 in

let list_of_option = function None -> [] | Some x -> [x] in

let try_list f x = try f x with Failure _ -> [] in

(* A few constants. *)
let vA_ = (parse_term "A:bool") and vB_ = (parse_term "B:bool") and vC_ = (parse_term "C:bool") and vD_ = (parse_term "D:bool") in
let vT_ = (parse_term "T:bool") in

(* For a term t, builds `t ==> t` *)
let vIMP_REFL =
  let lem = vTAUT (parse_term "A ==> A") in
  fun t -> vINST [t,vA_] lem in

(* Conversion version of [variant]:
 * Given variables [v1;...;vk] to avoid and a term [t],
 * returns [|- t = t'] where [t'] is the same as [t] without any use of the
 * variables [v1;...;vk].
 *)
let vVARIANT_CONV av t =
  let vs = variables t in
  let mapping = filter (fun (x,y) -> x <> y) (zip vs (variants av vs)) in
  vDEPTH_CONV (fun u -> vALPHA_CONV (assoc (bndvar u) mapping) u) t in

(* Rule version of [VARIANT_CONV] *)
let vVARIANT_RULE = vCONV_RULE -| vVARIANT_CONV in

(* Discharges the first hypothesis of a theorem. *)
let vDISCH_HD th = vDISCH (hd (hyp th)) th in

(* Rule version of [REWR_CONV] *)
let vREWR_RULE = vCONV_RULE -| vREWR_CONV in

(* Given a list [A1;...;Ak] and a theorem [th],
 * returns [|- A1 /\ ... /\ Ak ==> th].
 *)
let vDISCH_IMP_IMP =
  let f = function
    |[] -> vI
    |t::ts -> rev_itlist (fun t -> vREWR_RULE vIMP_IMP -| vDISCH t) ts -| vDISCH t
  in
  f -| rev in

(* Given a term [A /\ B] and a theorem [th], returns [|- A ==> B ==> th]. *)
let rec vDISCH_CONJ t th =
  try
    let t1,t2 = dest_conj t in
    vREWR_RULE vIMP_IMP (vDISCH_CONJ t1 (vDISCH_CONJ t2 th))
  with Failure _ -> vDISCH t th in

(* Specializes all the universally quantified variables of a theorem,
 * and returns both the theorem and the list of variables.
 *)
let rec vSPEC_VARS th =
  try
    let v,th' = vSPEC_VAR th in
    let vs,th'' = vSPEC_VARS th' in
    v::vs,th''
  with Failure _ -> [],th in

(* Comblies the function [f] to the body of a universally quantified theorem. *)
let vMAP_FORALL_BODY f th =
  let vs,th = vSPEC_VARS th in
  vGENL vs (f th) in

(* Given a theorem of the form [!xyz. P ==> !uvw. C] and a function [f],
 * return [!xyz. P ==> !uvw. f C].
 *)
let vGEN_MAP_CONCLUSION = vMAP_FORALL_BODY -| vMAP_CONCLUSION -| vMAP_FORALL_BODY in

(* Turn a theorem of the form [x ==> y /\ z] into [(x==>y) /\ (x==>z)].
 * Also deals with universal quantifications if necessary
 * (e.g., [x ==> !v. y /\ z] will be turned into
 * [(x ==> !v. y) /\ (x ==> !v. z)])
 *
 * possible improvement: apply the rewrite more locally
 *)
let vIMPLY_AND =
  let vIMPLY_AND_RDISTRIB = vTAUT (parse_term "(x ==> y /\\ z) <=> (x==>y) /\\(x==>z)") in
  vPURE_REWRITE_RULE [vGSYM vAND_FORALL_THM;vIMP_IMP;
    vRIGHT_IMP_FORALL_THM;vIMPLY_AND_RDISTRIB;vGSYM vCONJ_ASSOC] in

(* Returns the two operands of a binary combination.
 * Contrary to [dest_binary], does not check what is the operator.
 *)
let dest_binary_blind = function
  |Comb(Comb(_,l),r) -> l,r
  |_ -> failwith "dest_binary_blind" in

let spec_all = repeat (snd -| dest_forall) in

let thm_lt (th1:thm) th2 = th1 < th2 in

(* GMATCH_MP (U1 |- !x1...xn. H1 /\ ... /\ Hk ==> C) (U2 |- P)
 * = (U1 u U2 |- !y1...ym. G1' /\ ... /\ Gl' ==> C')
 * where:
 * - P matches some Hi
 * - C' is the result of applying the matching substitution to C
 * - Gj' is the result of applying the matching substitution to Hj
 * - G1',...,Gl' is the list corresponding to H1,...,Hk but without Hi
 * - y1...ym are the variables among x1,...,xn that are not instantiated
 *
 * possible improvement: make a specific conversion,
 * define a MATCH_MP that also returns the instantiated variables *)
let vGMATCH_MP =
  let swap = vCONV_RULE (vREWR_CONV (vTAUT (parse_term "(p==>q==>r) <=> (q==>p==>r)"))) in
  fun th1 ->
    let vs,th1' = vSPEC_VARS th1 in
    let hs,th1'' = vUNDISCH_TERMS (vPURE_REWRITE_RULE [vIMP_CONJ] th1') in
    fun th2 ->
      let f h hs =
        let th1''' = vDISCH h th1'' in
        let th1'''' =
          try swap (vDISCH_IMP_IMP hs th1''') with Failure _ -> th1'''
        in
        vMATCH_MP (vGENL vs th1'''') th2
      in
      let rec loop acc = function
        |[] -> []
        |h::hs ->
            (try [f h (acc @ hs)] with Failure _ -> []) @ loop (h::acc) hs
      in
      loop [] hs in

let vGMATCH_MPS ths1 ths2 =
  let insert (y:thm) = function
    |[] -> [y]
    |x::_ as xs when equals_thm x y -> xs
    |x::xs when thm_lt x y -> x :: insert y xs
    |_::_ as xs -> y::xs
  in
  let inserts ys = itlist insert ys in
  match ths1 with
  |[] -> []
  |th1::ths1' ->
    let rec self acc th1 ths1 = function
      |[] -> (match ths1 with [] -> acc | th::ths1' -> self acc th ths1' ths2)
      |th2::ths2' -> self (inserts (vGMATCH_MP th1 th2) acc) th1 ths1 ths2'
    in
    self [] th1 ths1' ths2 in

let vMP_CLOSURE ths1 ths2 =
  let ths1 = filter (is_imp -| spec_all -| concl) ths1 in
  let rec self ths2 = function
    |[] -> []
    |_::_ as ths1 ->
      let ths1'' = vGMATCH_MPS ths1 ths2 in
      self ths2 ths1'' @ ths1''
  in
  self ths2 ths1 in

(* Set of terms. Implemented as ordered lists. *)
let module Tset =
  struct
    type t = term list
    let cmp (x:term) y = Stdlib.compare x y
    let lt (x:term) y = Stdlib.compare x y < 0
    let lift f = List.sort cmp -| f
    let of_list = lift vI
    let insert ts t =
      let rec self = function
        |[] -> [t]
        |x::xs when lt x t -> x::self xs
        |x::_ as xs when x = t -> xs
        |xs -> t::xs
      in
      if t = vT_ then ts else self ts
    let remove ts t =
      let rec self = function
        |[] -> []
        |x::xs when lt x t -> x::self xs
        |x::xs when x = t -> xs
        |_::_ as xs -> xs
      in
      self ts
    let strip_conj =
      let rec self acc t =
        try
          let t1,t2 = dest_conj t in
          self (self acc t1) t2
        with Failure _ -> insert acc t
      in
      self []
    let rec union l1 l2 =
      match l1 with
      |[] -> l2
      |h1::t1 ->
          match l2 with
          |[] -> l1
          |h2::_t2 when lt h1 h2 -> h1::union t1 l2
          |h2::t2 when h1 = h2 -> h1::union t1 t2
          |h2::t2 -> h2::union l1 t2
    let rec mem x = function
      |x'::_xs when x' = x -> true
      |x'::xs when lt x' x -> mem x xs
      |_ -> false
    let subtract l1 l2 = filter (fun x -> not (mem x l2)) l1
    let empty = []
    let flat_revmap f =
      let rec self acc = function
        |[] -> acc
        |x::xs -> self (union (f x) acc) xs
      in
      self []
    let _flat_map f = flat_revmap f -| rev
    let rec frees acc = function
      |Var _ as t -> insert acc t
      |Const _ -> acc
      |Abs(v,b) -> remove (frees acc b) v
      |Comb(u,v) -> frees (frees acc u) v
    let freesl ts = itlist (vC frees) ts empty
    let frees = frees empty
  end in

let module Type_annoted_term =
  struct
    type t =
      |Var_ of string * hol_type
      |Const_ of string * hol_type * term
      |Comb_ of t * t * hol_type
      |Abs_ of t * t * hol_type

    let type_of = function
      |Var_(_,ty) -> ty
      |Const_(_,ty,_) -> ty
      |Comb_(_,_,ty) -> ty
      |Abs_(_,_,ty) -> ty

    let rec of_term = function
      |Var(s,ty) -> Var_(s,ty)
      |Const(s,ty) as t -> Const_(s,ty,t)
      |Comb(u,v) ->
          let u' = of_term u and v' = of_term v in
          Comb_(u',v',snd (dest_fun_ty (type_of u')))
      |Abs(x,b) ->
          let x' = of_term x and b' = of_term b in
          Abs_(x',b',mk_fun_ty (type_of x') (type_of b'))

    let rec equal t1 t2 =
      match t1,t2 with
      |Var_(s1,ty1),Var_(s2,ty2)
      |Const_(s1,ty1,_),Const_(s2,ty2,_) -> s1 = s2 && ty1 = ty2
      |Comb_(u1,v1,_),Comb_(u2,v2,_) -> equal u1 u2 && equal v1 v2
      |Abs_(v1,b1,_),Abs_(v2,b2,_) -> equal v1 v2 && equal b1 b2
      |_ -> false

    let rec to_term = function
      |Var_(s,ty) -> mk_var(s,ty)
      |Const_(_,_,t) -> t
      |Comb_(u,v,_) -> mk_comb(to_term u,to_term v)
      |Abs_(v,b,_) -> mk_abs(to_term v,to_term b)

    let _dummy = Var_("",aty)

    let rec _find_term p t =
      if p t then t else
        match t with
        |Abs_(_,b,_) -> _find_term p b
        |Comb_(u,v,_) -> (try _find_term p u with Failure _ -> _find_term p v)
        |_ -> failwith "Annot.find_term"
  end in

let module Annot = Type_annoted_term in

(* ------------------------------------------------------------------------- *)
(* First-order matching of terms.                                            *)
(*                                                                           *)
(* Same note as in [drule.ml]:                                               *)
(* in the event of spillover patterns, this may return false results;        *)
(* but there's usually an implicit check outside that the match worked       *)
(* anyway. A test could be put in (see if any "env" variables are left in    *)
(* the term after abstracting out the pattern instances) but it'd be slower. *)
(* ------------------------------------------------------------------------- *)

let fo_term_match lcs p t =
  let fail () = failwith "fo_term_match" in
  let rec self bnds (tenv,tyenv as env) p t =
    match p,t with
    |Comb(p1,p2),Annot.Comb_(t1,t2,_) -> self bnds (self bnds env p1 t1) p2 t2
    |Abs(v,p),Annot.Abs_(v',t,_) ->
        let tyenv' = type_match (type_of v) (Annot.type_of v') tyenv in
        self ((v',v)::bnds) (tenv,tyenv') p t
    |Const(n,ty),Annot.Const_(n',ty',_) ->
        if n <> n' then fail ()
        else
          let tyenv' = type_match ty ty' tyenv in
          tenv,tyenv'
    |Var(n,ty) as v,t ->
        (* Is [v] bound? *)
        (try if Annot.equal t (rev_assoc v bnds) then env else fail ()
        (* No *)
        with Failure _ ->
          if mem v lcs
          then
            match t with
            |Annot.Var_(n',ty') when n' = n && ty' = ty -> env
            |_ -> fail ()
          else
            let tyenv' = type_match ty (Annot.type_of t) tyenv in
            let t' = try Some (rev_assoc v tenv) with Failure _ -> None in
            match t' with
            |Some t' -> if t = t' then tenv,tyenv' else fail ()
            |None -> (t,v)::tenv,tyenv')
    |_ -> fail ()
  in
  let tenv,tyenv = self [] ([],[]) p (Annot.of_term t) in
  let inst = inst tyenv in
  List.rev_map (fun (t,v) -> Annot.to_term t,inst v) tenv,tyenv in

let vGEN_PART_MATCH_ALL =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc
  in
  fun partfn th ->
    let sth = vSPEC_ALL th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lcs = intersect (frees (concl th)) (freesl(hyp th)) in
    let fvs = subtract (subtract (frees bod) (frees pbod)) lcs in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = vEQ_MP (vALPHA bod abod) sth in
      let insts,tyinsts = fo_term_match lcs (partfn abod) tm in
      let eth = vINSTANTIATE_ALL ([],insts,tyinsts) (vGENL fvs ath) in
      let fth = itlist (fun _v th -> snd(vSPEC_VAR th)) fvs eth in
      let tm' = partfn (concl fth) in
      if Stdlib.compare tm' tm = 0 then fth else
      try vSUBS[vALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure" in

let module Fo_nets =
  struct
    type term_label =
      |Vnet of int
      |Lcnet of string * int
      |Cnet of string * int
      |Lnet of int

    type 'a t = Netnode of (term_label * 'a t) list * 'a list

    let empty_net = Netnode([],[])

    let enter =
      let label_to_store lcs t =
        let op,args = strip_comb t in
        let nargs = length args in
        match op with
        |Const(n,_) -> Cnet(n,nargs),args
        |Abs(v,b) ->
          let b' = if mem v lcs then vsubst [genvar(type_of v),v] b else b in
          Lnet nargs,b'::args
        |Var(n,_) when mem op lcs -> Lcnet(n,nargs),args
        |Var(_,_) -> Vnet nargs,args
        |_ -> assert false
      in
      let rec net_update lcs elem (Netnode(edges,tips)) = function
        |[] -> Netnode(edges,elem::tips)
        |t::rts ->
            let label,nts = label_to_store lcs t in
            let child,others =
              try (snd $-$ vI) (remove (fun (x,_y) -> x = label) edges)
              with Failure _ -> empty_net,edges in
            let new_child = net_update lcs elem child (nts@rts) in
            Netnode ((label,new_child)::others,tips)
      in
      fun lcs (t,elem) net -> net_update lcs elem net [t]

    let lookup =
      let label_for_lookup t =
        let op,args = strip_comb t in
        let nargs = length args in
        match op with
        |Const(n,_) -> Cnet(n,nargs),args
        |Abs(_,b) -> Lnet nargs,b::args
        |Var(n,_) -> Lcnet(n,nargs),args
        |Comb _ -> assert false
      in
      let rec follow (Netnode(edges,tips)) = function
        |[] -> tips
        |t::rts ->
            let label,nts = label_for_lookup t in
            let collection =
              try follow (assoc label edges) (nts@rts) with Failure _ -> []
            in
            let rec support = function
              |[] -> [0,rts]
              |t::ts ->
                  match support ts with ((k,nts')::_res') as res ->
                  (k+1,(t::nts'))::res
              | _ -> assert false
            in
            let follows =
              let f (k,nts) =
                try follow (assoc (Vnet k) edges) nts with Failure _ -> []
              in
              map f (support nts)
            in
            collection @ flat follows
      in
      fun t net -> follow net [t]

    let rec filter p (Netnode(edges,tips)) =
      Netnode(
        List.map (fun (l,n) -> l,filter p n) edges,
        List.filter p tips)
  end in

let module Variance =
  struct
    type t = Co | Contra
    let neg = function Co -> Contra | Contra -> Co
  end in

(*****************************************************************************)
(* IMPLICATIONAL RULES                                                       *)
(* i.e., rules to build propositions based on implications rather than       *)
(* equivalence.                                                              *)
(*****************************************************************************)

let module Impconv =
  struct

let vMKIMP_common lem th1 th2 =
  let a,b = dest_imp (concl th1) and c,d = dest_imp (concl th2) in
  vMP (vINST [a,vA_;b,vB_;c,vC_;d,vD_] lem) (vCONJ th1 th2)

(* Similar to [MK_CONJ] but theorems should be implicational instead of
 * equational, i.e., conjoin both sides of two implicational theorems.
 *
 * More precisely: given two theorems [A ==> B] and [C ==> D],
 * returns [A /\ C ==> B /\ D].
 *)
let _vMKIMP_CONJ = vMKIMP_common vMONO_AND

(* Similar to [MK_DISJ] but theorems should be implicational instead of
 * equational, i.e., disjoin both sides of two implicational theorems.
 *
 * More precisely: given two theorems [A ==> B] and [C ==> D],
 * returns [A \/ C ==> B \/ D].
 *)
let vMKIMP_DISJ = vMKIMP_common vMONO_OR

let vMKIMP_IFF =
  let lem =
    vTAUT (parse_term "((A ==> B) ==> (C ==> D)) /\\ ((B ==> A) ==> (D ==> C)) ==> (A <=> B)\n      ==> (C <=> D)")
  in
  fun th1 th2 ->
    let ab,cd = dest_imp (concl th1) in
    let a,b = dest_imp ab and c,d = dest_imp cd in
    vMP (vINST [a,vA_;b,vB_;c,vC_;d,vD_] lem) (vCONJ th1 th2)

(* th1 = (A ==> B) ==> C1
 * th2 = (B ==> A) ==> C2
 * output = (A <=> B) ==> (C1 /\ C2)
 *)
let vMKIMP_CONTRA_IFF =
  let lem =
    vTAUT (parse_term "((A ==> B) ==> C) /\\ ((B ==> A) ==> D) ==> (A <=> B) ==> C /\\ D")
  in
  fun th1 th2 ->
    let ab,c = dest_imp (concl th1) and _,d = dest_imp (concl th2) in
    let a,b = dest_imp ab in
    vMP (vINST [a,vA_;b,vB_;c,vC_;d,vD_] lem) (vCONJ th1 th2)

let vMKIMPL_CONTRA_IFF =
  let lem = vTAUT (parse_term "((A ==> B) ==> C) ==> (A <=> B) ==> C /\\ (B ==> A)") in
  fun th ->
    let ab,c = dest_imp (concl th) in
    let a,b = dest_imp ab in
    vMP (vINST [a,vA_;b,vB_;c,vC_] lem) th

let vMKIMPR_CONTRA_IFF =
  let lem =
    vTAUT (parse_term "((B ==> A) ==> D) ==> (A <=> B) ==> (A ==> B) /\\ D")
  in
  fun th ->
    let ba,d = dest_imp (concl th) in
    let b,a = dest_imp ba in
    vMP (vINST [a,vA_;b,vB_;d,vD_] lem) th

let vMKIMP_CO_IFF =
  let lem =
    vTAUT (parse_term "(C ==> A ==> B) /\\ (D ==> B ==> A) ==> C /\\ D ==> (A <=> B)")
  in
  fun th1 th2 ->
    let c,ab = dest_imp (concl th1) and d,_ = dest_imp (concl th2) in
    let a,b = dest_imp ab in
    vMP (vINST [a,vA_;b,vB_;c,vC_;d,vD_] lem) (vCONJ th1 th2)

let vMKIMPL_CO_IFF =
  let lem =
    vTAUT (parse_term "(C ==> A ==> B) ==> C /\\ (B ==> A) ==> (A <=> B)")
  in
  fun th ->
    let c,ab = dest_imp (concl th) in
    let a,b = dest_imp ab in
    vMP (vINST [a,vA_;b,vB_;c,vC_] lem) th

let vMKIMPR_CO_IFF =
  let lem = vTAUT (parse_term "(D ==> B ==> A) ==> (A ==> B) /\\ D ==> (A <=> B)") in
  fun th ->
    let d,ba = dest_imp (concl th) in
    let b,a = dest_imp ba in
    vMP (vINST [a,vA_;b,vB_;d,vD_] lem) th

(* Given two theorems [A ==> B] and [C ==> D],
 * returns [(B ==> C) ==> (A ==> D)].
 *)
let _vMKIMP_IMP th1 th2 =
  let b,a = dest_imp (concl th1) and c,d = dest_imp (concl th2) in
  vMP (vINST [a,vA_;b,vB_;c,vC_;d,vD_] vMONO_IMP) (vCONJ th1 th2)

let vMKIMPL_common lem =
  let lem' = vREWRITE_RULE[] (vINST [vC_,vD_] lem) in
  fun th t ->
    let a,b = dest_imp (concl th) in
    vMP (vINST [a,vA_;b,vB_;t,vC_] lem') th

(* Given a theorem [A ==> B] and a term [C],
 * returns [A /\ C ==> B /\ C].
 *)
let _vMKIMPL_CONJ = vMKIMPL_common vMONO_AND

(* Given a theorem [A ==> B] and a term [C],
 * returns [A \/ C ==> B \/ C].
 *)
let vMKIMPL_DISJ = vMKIMPL_common vMONO_OR

(* Given a theorem [A ==> B] and a term [C],
 * returns [(B ==> C) ==> (A ==> C)].
 *)
let vMKIMPL_IMP =
  let vMONO_IMP' = vREWRITE_RULE[] (vINST [vC_,vD_] vMONO_IMP) in
  fun th t ->
    let b,a = dest_imp (concl th) in
    vMP (vINST [a,vA_;b,vB_;t,vC_] vMONO_IMP') th

let vMKIMPR_common lem =
  let lem' = vREWRITE_RULE[] (vINST [vA_,vB_] lem) in
  fun t th ->
    let c,d = dest_imp (concl th) in
    vMP (vINST [c,vC_;d,vD_;t,vA_] lem') th

(* Given a term [A] and a theorem [B ==> C],
 * returns [A /\ B ==> A /\ C].
 *)
let _vMKIMPR_CONJ = vMKIMPR_common vMONO_AND

(* Given a term [A] and a theorem [B ==> C],
 * returns [A \/ B ==> A \/ C].
 *)
let vMKIMPR_DISJ = vMKIMPR_common vMONO_OR

(* Given a term [A] and a theorem [B ==> C],
 * returns [(A ==> B) ==> (A ==> C)].
 *)
let _vMKIMPR_IMP = vMKIMPR_common vMONO_IMP

(* Given a theorem [A ==> B], returns [~B ==> ~A]. *)
let vMKIMP_NOT th =
  let b,a = dest_imp (concl th) in
  vMP (vINST [a,vA_;b,vB_] vMONO_NOT) th

let vMKIMP_QUANT lem x th =
  let x_ty = type_of x and p,q = dest_imp (concl th) in
  let p' = mk_abs(x,p) and q' = mk_abs(x,q) in
  let vP = mk_var("P",mk_fun_ty x_ty bool_ty) in
  let vQ = mk_var("Q",mk_fun_ty x_ty bool_ty) in
  let lem = vINST [p',vP;q',vQ] (vINST_TYPE [x_ty,aty] lem) in
  let c = vONCE_DEPTH_CONV (vALPHA_CONV x) +---> vONCE_DEPTH_CONV vBETA_CONV in
  vMP (vCONV_RULE c lem) (vGEN x th)

(* Given a variable [x] and a theorem [A ==> B],
 * returns [(!x. A) ==> (!x. B)]. *)
let vMKIMP_FORALL = vMKIMP_QUANT vMONO_FORALL

(* Given a variable [x] and a theorem [A ==> B],
 * returns [(?x. A) ==> (?x. B)]. *)
let vMKIMP_EXISTS = vMKIMP_QUANT vMONO_EXISTS

(* Given two theorems [A ==> B] and [B ==> C ==> D],
 * returns [(B ==> C) ==> (A ==> D)],
 * i.e., similar to [MKIMP_IMP] but allows to remove the context [B]
 * since it is a consequence of [A].
 *)
let vMKIMP_IMP_CONTRA_CTXT =
  let lem = vTAUT (parse_term "(B==>A) /\\ (A==>B==>C==>D) ==> (A==>C) ==> (B==>D)") in
  fun th1 th2 ->
    let a,bcd = dest_imp (concl th2) in
    let b,cd = dest_imp bcd in
    let c,d = dest_imp cd in
    vMP (vINST [a,vA_;b,vB_;c,vC_;d,vD_] lem) (vCONJ th1 th2)

let vMKIMP_IMP_CO_CTXT =
  let lem = vTAUT (parse_term "(A==>B) /\\ (A==>B==>D==>C) ==> (B==>D) ==> (A==>C)") in
  fun th1 th2 ->
    let a,bdc = dest_imp (concl th2) in
    let b,dc = dest_imp bdc in
    let d,c = dest_imp dc in
    vMP (vINST [a,vA_;b,vB_;c,vC_;d,vD_] lem) (vCONJ th1 th2)

(* Given a theorem [B ==> C ==> D], returns [(B ==> C) ==> (B ==> D)],
 * i.e., similar to [MKIMP_IMP] but allows to remove the context [B]
 * since it is a consequence of [A].
 *)
let vMKIMPR_IMP_CTXT =
  let lem = vTAUT (parse_term "(A==>C==>D) ==> (A==>C) ==> (A==>D)") in
  fun th ->
    let a,cd = dest_imp (concl th) in
    let c,d = dest_imp cd in
    vMP (vINST [c,vC_;d,vD_;a,vA_] lem) th

(* Given two theorems [A ==> B] and [A ==> B ==> C ==> D],
 * returns [(A /\ C) ==> (B /\ D)],
 * i.e., similar to [MKIMP_CONJ] but allows to remove the contexts [A] and [B].
 *)
let vMKIMP_CONJ_CONTRA_CTXT =
  let lem = vTAUT (parse_term "(C==>A==>B) /\\ (A==>B==>C==>D) ==> (A/\\C==>B/\\D)") in
  fun th1 th2 ->
    let a,bcd = dest_imp (concl th2) in
    let b,cd = dest_imp bcd in
    let c,d = dest_imp cd in
    vMP (vINST [a,vA_;b,vB_;c,vC_;d,vD_] lem) (vCONJ th1 th2)

let vMKIMPL_CONJ_CONTRA_CTXT =
  let lem = vTAUT (parse_term "(C==>A==>B) ==> (A/\\C==>B/\\C)") in
  fun th ->
    let c,ab = dest_imp (concl th) in
    let a,b = dest_imp ab in
    vMP (vINST [a,vA_;b,vB_;c,vC_] lem) th

let vMKIMPR_CONJ_CONTRA_CTXT =
  let lem = vTAUT (parse_term "(A==>C==>D) ==> (A/\\C==>A/\\D)") in
  fun th ->
    let a,cd = dest_imp (concl th) in
    let c,d = dest_imp cd in
    vMP (vINST [a,vA_;c,vC_;d,vD_] lem) th

let vMKIMP_CONJ_CO_CTXT =
  let lem = vTAUT (parse_term "(B==>A) /\\ (B==>D==>C) ==> (B/\\D==>A/\\C)") in
  fun th1 th2 ->
    let b,a = dest_imp (concl th1) in
    let d,c = dest_imp (snd (dest_imp (concl th2))) in
    vMP (vINST [a,vA_;b,vB_;c,vC_;d,vD_] lem) (vCONJ th1 th2)

let vMKIMPL_CONJ_CO_CTXT =
  let lem = vTAUT (parse_term "(B==>A) ==> (B/\\C==>A/\\C)") in
  fun th ->
    let b,a = dest_imp (concl th) in
    fun c -> vMP (vINST [a,vA_;b,vB_;c,vC_] lem) th

let vMKIMPL_CONJ_CO2_CTXT =
  let lem = vTAUT (parse_term "(C==>B==>A) ==> (B/\\C==>A/\\C)") in
  fun th ->
    let c,ba = dest_imp (concl th) in
    let b,a = dest_imp ba in
    vMP (vINST [a,vA_;b,vB_;c,vC_] lem) th

let vMKIMPR_CONJ_CO_CTXT = vMKIMPR_CONJ_CONTRA_CTXT


(*****************************************************************************)
(* IMPLICATIONAL CONVERSIONS                                                 *)
(*****************************************************************************)

open Variance

(* An implicational conversion maps a term t to a theorem of the form:
 * t' ==> t if covariant
 * t ==> t' if contravariant
 *)
type imp_conv = Variance.t -> term -> thm

(* Trivial embedding of conversions into implicational conversions. *)
let imp_conv_of_conv:conv->imp_conv =
  fun c v t ->
    let th1,th2 = vEQ_IMP_RULE (c t) in
    match v with Co -> th2 | Contra -> th1

(* Retrieves the outcome of an implicational conversion, i.e., t'. *)
let imp_conv_outcome th v =
  let t1,t2 = dest_binary_blind (concl th) in
  match v with Co -> t1 | Contra -> t2

(* [ALL_IMPCONV _ t] returns `t==>t` *)
let vALL_IMPCONV:imp_conv = fun _ -> vIMP_REFL

(* The implicational conversion which always fails. *)
let _vNO_IMPCONV:imp_conv = fun _ _ -> failwith "NO_IMPCONV"

let bind_impconv (c:imp_conv) v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> vIMP_TRANS (c v t1) th
  |Contra -> vIMP_TRANS th (c v t2)

let vTHEN_IMPCONV (c1:imp_conv) c2 v t = bind_impconv c2 v (c1 v t)


(*****************************************************************************)
(* SOME USEFUL IMPLICATIONAL CONVERSIONS                                     *)
(*****************************************************************************)

(* Given a theorem [p ==> c], returns the implicational conversion which:
  * - in the covariant case, matches the input term [t] against [c] and returns
  *   [s(p) ==> t], where [s] is the matching substitution
  * - in the contravariant case, matches the input term [t] against [p] and returns
  *   [t ==> s(c)], where [s] is the matching substitution
  *)
let _vMATCH_MP_IMPCONV:thm->imp_conv =
  fun th -> function
    |Co -> vGEN_PART_MATCH rand th
    |Contra -> vGEN_PART_MATCH lhand th


(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* From an implicational conversion builds a rule, i.e., a function which
 * takes a theorem and returns a new theorem.
 *)
let _vIMPCONV_RULE:imp_conv->thm->thm =
  fun c th ->
    let t = concl th in
    vMATCH_MP (c Contra t) th

(* From an implicational conversion builds a tactic. *)
let vIMPCONV_TAC:imp_conv->tactic =
  fun cnv (_,c as g) ->
    (vMATCH_MP_TAC (cnv Co c) ----> vTRY (vACCEPT_TAC vTRUTH)) g


(*****************************************************************************)
(* CONTEXT HANDLING                                                          *)
(*****************************************************************************)

(* [term list] = terms to add to the context *)
type 'a with_context =
  With_context of 'a * (Tset.t -> 'a with_context) * (term -> 'a with_context)

let apply (With_context(c,_,_)) = c

(* Maybe avoid the augment if the input list is empty? *)
let augment (With_context(_,a,_)) = a
let diminish (With_context(_,_,d)) = d
let apply_with_context c ctx v t =
  vDISCH_CONJ ctx (apply (augment c (Tset.strip_conj ctx)) v t)

let imp_conv_of_ctx_imp_conv = (apply:imp_conv with_context -> imp_conv)

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Co C] returns [D ==> C],
 * then [CONJ_IMPCONV ic1 ic2 Co (A /\ C)] returns [B /\ D ==> A /\ C].
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Contra C] returns
 * [C ==> D], then [CONJ_IMPCONV ic1 ic2 Contra (A /\ B)]
 * returns [A /\ B ==> C /\ D].
 *
 * Additionally takes the context into account, i.e., if [ic2 Co C] returns
 * [A |- D ==> C],
 * then [CONJ_IMPCONV ic1 ic2 Co (A /\ B)] returns [|- C /\ D ==> A /\ B]
 * (i.e., [A] does not appear in the hypotheses).
 *)
let rec vCONJ_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_conj t in
      match v with
      |Co ->
          (try
            let th1 = apply c Co t1 in
            try
              let t1' = imp_conv_outcome th1 Co in
              vMKIMP_CONJ_CO_CTXT th1 (apply_with_context c t1' Co t2)
              with Failure _ -> vMKIMPL_CONJ_CO_CTXT th1 t2
          with Failure _ -> vMKIMPR_CONJ_CO_CTXT (apply_with_context c t1 Co t2))
      |Contra ->
          try
            (* note: we remove t1 in case it appears in t2, since otherwise,
             * t1 removes t2 and t2 removes t1
             *)
            let t2s = Tset.remove (Tset.strip_conj t2) t1 in
            let th1 = apply (augment c t2s) Contra t1 in
              try
                let t1' = imp_conv_outcome th1 Contra in
                let t1s = Tset.strip_conj t1 and t1s' = Tset.strip_conj t1' in
                let t1s'' = Tset.union t1s t1s' in
                let th2 = apply (augment c t1s'') Contra t2 in
                let th2' = vDISCH_CONJ t1 (vDISCH_CONJ t1' th2) in
                vMKIMP_CONJ_CONTRA_CTXT (vDISCH_CONJ t2 th1) th2'
              with Failure _ -> vMKIMPL_CONJ_CONTRA_CTXT (vDISCH_CONJ t2 th1)
            with Failure _ ->
              vMKIMPR_CONJ_CONTRA_CTXT (apply_with_context c t1 Contra t2))
      :imp_conv),
    vCONJ_CTXIMPCONV -| augment c,
    vCONJ_CTXIMPCONV -| diminish c)

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Co C] returns [D ==> C],
 * then [DISJ_IMPCONV ic1 ic2 Co (A \/ C)] returns [B \/ D ==> A \/ C].
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Contra C] returns
 * [C ==> D], then [DISJ_IMPCONV ic1 ic2 Contra (A \/ B)]
 * returns [A \/ B ==> C \/ D].
 *)
let rec vDISJ_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_disj t in
      try
        let th1 = apply c v t1 in
        try vMKIMP_DISJ th1 (apply c v t2) with Failure _ -> vMKIMPL_DISJ th1 t2
      with Failure _ -> vMKIMPR_DISJ t1 (apply c v t2)):imp_conv),
    vDISJ_CTXIMPCONV -| augment c,
    vDISJ_CTXIMPCONV -| diminish c)

(* Consider two implicational conversions ic1, ic2.
 * Suppose [ic1 Contra A] returns [A ==> B], and [ic2 Co C] returns [D ==> C],
 * then [IMP_IMPCONV ic1 ic2 Co (A ==> C)] returns [(B ==> D) ==> (A ==> C)].
 * Suppose [ic1 Co A] returns [B ==> A], and [ic2 Contra C] returns
 * [C ==> D], then [IMP_IMPCONV ic1 ic2 Contra (A ==> C)]
 * returns [(A ==> C) ==> (B ==> D)].
 *
 * Additionally takes the context into account, i.e., if [ic2 Co C] returns
 * [B |- D ==> C], then [IMP_IMPCONV ic1 ic2 Co (A ==> C)] returns
 * [|- (B ==> D) ==> (A ==> C)] (i.e., [B] does not appear in the hypotheses).
 *)
let rec vIMP_CTXIMPCONV (c:imp_conv with_context)  =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_imp t in
      try
        let v' = Variance.neg v in
        let th1 = apply c v' t1 in
        let t1' = imp_conv_outcome th1 v' in
        let t1s = Tset.union (Tset.strip_conj t1) (Tset.strip_conj t1') in
        let c' = augment c t1s in
        let mk =
          match v with Co -> vMKIMP_IMP_CO_CTXT | Contra -> vMKIMP_IMP_CONTRA_CTXT
        in
        try mk th1 (vDISCH_CONJ t1 (vDISCH_CONJ t1' (apply c' v t2)))
        with Failure _ -> vMKIMPL_IMP th1 t2
      with Failure _ -> vMKIMPR_IMP_CTXT (apply_with_context c t1 v t2)
      ):imp_conv),
    vIMP_CTXIMPCONV -| augment c,
    vIMP_CTXIMPCONV -| diminish c)

let rec vIFF_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_iff t in
      let lr,l,r =
        match v with
        |Co -> vMKIMP_CO_IFF,vMKIMPL_CO_IFF,vMKIMPR_CO_IFF
        |Contra -> vMKIMP_CONTRA_IFF,vMKIMPL_CONTRA_IFF,vMKIMPR_CONTRA_IFF
      in
      (try
        let th1 = apply c v (mk_imp (t1,t2)) in
        try
          let th2 = apply c v (mk_imp (t2,t1)) in
          (try vMKIMP_IFF th1 th2 with Failure _ -> lr th1 th2)
        with Failure _ -> l th1
      with Failure _ -> r (apply c v (mk_imp (t2,t1))))):imp_conv),
    vIFF_CTXIMPCONV -| augment c,
    vIFF_CTXIMPCONV -| diminish c)

(* Consider an implicational conversion ic.
 * Suppose [ic Contra A] returns [A ==> B]
 * then [NOT_IMPCONV ic Co ~A] returns [~B ==> ~A].
 * Suppose [ic Co A] returns [B ==> A]
 * then [NOT_IMPCONV ic Contra ~A] returns [~A ==> ~B].
 *)
let rec vNOT_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t -> vMKIMP_NOT (apply c (Variance.neg v) (dest_neg t))):imp_conv),
    vNOT_CTXIMPCONV -| augment c,
    vNOT_CTXIMPCONV -| diminish c)

let rec vQUANT_CTXIMPCONV mkimp sel (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let x,b = sel t in
      let c' = diminish c x in
      mkimp x (apply c' v b)):imp_conv),
    vQUANT_CTXIMPCONV mkimp sel -| augment c,
    vQUANT_CTXIMPCONV mkimp sel -| diminish c)

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [FORALL_IMPCONV ic Co (!x.A)] returns [(!x.B) ==> (!x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [FORALL_IMPCONV ic Contra (!x.A)] returns [(!x.A) ==> (!x.B)].
 *)
let vFORALL_CTXIMPCONV = vQUANT_CTXIMPCONV vMKIMP_FORALL dest_forall

(* Consider an implicational conversion ic.
 * Suppose [ic Co A] returns [B ==> A]
 * then [EXISTS_IMPCONV ic Co (?x.A)] returns [(?x.B) ==> (?x.A)].
 * Suppose [ic Contra A] returns [A ==> B]
 * then [EXISTS_IMPCONV ic Contra (?x.A)] returns [(?x.A) ==> (?x.B)].
 *)
let vEXISTS_CTXIMPCONV = vQUANT_CTXIMPCONV vMKIMP_EXISTS dest_exists

(* Applies an implicational conversion on the subformula(s) of the input term*)
let rec vSUB_CTXIMPCONV =
  let iff_ty = (parse_type "bool->bool->bool") in
  fun c ->
    With_context(
    ((fun v t ->
      let n,ty = dest_const (fst (strip_comb t)) in
      apply
        ((match n with
        |"==>" -> vIMP_CTXIMPCONV
        |"/\\" -> vCONJ_CTXIMPCONV
        |"\\/" -> vDISJ_CTXIMPCONV
        |"=" when ty = iff_ty -> vIFF_CTXIMPCONV
        |"!" -> vFORALL_CTXIMPCONV
        |"?" -> vEXISTS_CTXIMPCONV
        |"~" -> vNOT_CTXIMPCONV
        |_ -> failwith "SUB_CTXIMPCONV") c)
        v t):imp_conv),
    vSUB_CTXIMPCONV -| augment c,
    vSUB_CTXIMPCONV -| diminish c)

(* Takes a theorem which results of an implicational conversion and applies
 * another implicational conversion on the outcome.
 *)
let bind_ctximpconv (c:imp_conv with_context) v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> vIMP_TRANS (apply c v t1) th
  |Contra -> vIMP_TRANS th (apply c v t2)

let rec _vBIND_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v th -> bind_ctximpconv c v th),
    _vBIND_CTXIMPCONV -| augment c,
    _vBIND_CTXIMPCONV -| diminish c))

(* Sequential combinator. *)
let rec _vTHEN_CTXIMPCONV (c1:imp_conv with_context) (c2:imp_conv with_context) =
  With_context(
    ((fun v t -> bind_ctximpconv c2 v (apply c1 v t)):imp_conv),
    (fun x -> _vTHEN_CTXIMPCONV (augment c1 x) (augment c2 x)),
    (fun x -> _vTHEN_CTXIMPCONV (diminish c1 x) (diminish c2 x)))

(* Try combinator *)
let rec vTRY_CTXIMPCONV (c:imp_conv with_context) =
    With_context(
      ((fun v t ->
        try apply c v t
        with Failure _ | Unchanged -> vALL_IMPCONV v t):imp_conv),
      vTRY_CTXIMPCONV -| augment c,
      vTRY_CTXIMPCONV -| diminish c)


(* Applies the first of two implicational conversions that succeeds. *)
let rec _vORELSE_CTXIMPCONV
  (c1:imp_conv with_context) (c2:imp_conv with_context) =
  With_context(
    ((fun v t -> try apply c1 v t with Failure _ -> apply c2 v t):imp_conv),
    (fun x -> _vORELSE_CTXIMPCONV (augment c1 x) (augment c2 x)),
    (fun x -> _vORELSE_CTXIMPCONV (diminish c1 x) (diminish c2 x)))

(* Makes an implicational conversion fail if applying it leaves a term
 * unchanged.
 *)
let rec _vCHANGED_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t ->
      let th = apply c v t in
      let l,r = dest_imp (concl th) in
      if aconv l r then failwith "CHANGED_CTXIMPCONV" else th):imp_conv),
    _vCHANGED_CTXIMPCONV -| augment c,
    _vCHANGED_CTXIMPCONV -| diminish c)

let rec vUNCHANGED_OF_FAIL_CTXIMPCONV (c:imp_conv with_context) =
  With_context(
    ((fun v t -> try apply c v t with Failure _ -> raise Unchanged
      ):imp_conv),
    vUNCHANGED_OF_FAIL_CTXIMPCONV -| augment c,
    vUNCHANGED_OF_FAIL_CTXIMPCONV -| diminish c)

let rec vREPEAT_UNCHANGED_CTXIMPCONV =
  let rec map_all f xs x =
    match xs with
    |[] -> []
    |y::ys -> f y x :: map_all f ys x
  in
  fun (cs:imp_conv with_context list) ->
    With_context(
      ((fun v t ->
        let rec loop changed acc = function
          |[] when changed -> loop false acc cs
          |[] -> acc
          |c::cs' ->
              try
                let acc' = bind_ctximpconv c v acc in
                loop true acc' cs'
              with Unchanged -> loop changed acc cs'
        in
        loop false (vIMP_REFL t) cs):imp_conv),
      vREPEAT_UNCHANGED_CTXIMPCONV -| map_all augment cs,
      vREPEAT_UNCHANGED_CTXIMPCONV -| map_all diminish cs)


type atomic = Atomic | Non_atomic

let vDEPTH_CTXIMPCONV =
  let bind c na v th =
    let t1,t2 = dest_imp (concl th) in
    match v with
    |Co -> vIMP_TRANS (apply c na v t1) th
    |Contra -> vIMP_TRANS th (apply c na v t2)
  in
  let rec self (c:(atomic->imp_conv) with_context) =
    With_context(
      (fun v t ->
        try
          let th1 = apply (vSUB_CTXIMPCONV (self c)) v t in
          (try bind c Non_atomic v th1 with Failure _ -> th1)
        with
        | Failure msg -> if msg = "SUB_CTXIMPCONV" then
          let th1 = apply c Atomic v t in
          (try bind_ctximpconv (self c) v th1 with Failure _ -> th1)
        else apply c Non_atomic v t),
      self -| augment c,
      self -| diminish c)
  in
  vUNCHANGED_OF_FAIL_CTXIMPCONV -| self

let vTOP_DEPTH_CTXIMPCONV =
  let rec self (c:imp_conv with_context) =
    With_context(
      (fun v t ->
        try
          let th = apply c v t in
          try bind_ctximpconv (self c) v th with Failure _ -> th
        with Failure _ -> apply (vSUB_CTXIMPCONV (self c)) v t),
      self -| augment c,
      self -| diminish c)
  in
  vUNCHANGED_OF_FAIL_CTXIMPCONV -| self

let vONCE_DEPTH_CTXIMPCONV =
  let rec self (c:(atomic->imp_conv) with_context) =
    With_context(
      (fun v t ->
        try apply (vSUB_CTXIMPCONV (self c)) v t
        with
        | Failure msg -> if msg = "SUB_CTXIMPCONV" then apply c Atomic v t
        else apply c Non_atomic v t),
      self -| augment c,
      self -| diminish c)
  in
  vUNCHANGED_OF_FAIL_CTXIMPCONV -| self


let _vCTXIMPCONV_RULE (c:imp_conv with_context) th =
  vMATCH_MP (apply c Contra (concl th)) th

let vCTXIMPCONV_TAC (cnv:imp_conv with_context) : tactic =
  fun (asms,c as g) ->
    let cnv' = augment cnv (map (concl -| snd) asms) in
    (vMATCH_MP_TAC (apply cnv' Co c) ----> vTRY (vACCEPT_TAC vTRUTH)) g

(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSION                                          *)
(*****************************************************************************)

(* Given a theorem [H1,...,Hn |- P ==> l = r],
 * returns the variables that occur in [P] and [r] but not in the rest.
 * Basically represents the variables that are introduced by the implicational
 * rewrite (similar status as variables occurring in the r.h.s. of a rewrite
 * but not in the l.h.s.).
 *)
let indep_vars th =
  let hs,c = dest_thm (vSPEC_ALL th) in
  let p,c = dest_imp c in
  let all_vars = union (frees p) (frees (rhs c)) in
  let dep_vars = union (frees (lhs c)) (freesl hs) in
  subtract all_vars dep_vars

(* Given a list of variables to avoid [v1,...,vk], a theorem of the form
 * [hs |- !x1...xn. p ==> !y1...ym. l = r], and a term [t], matches [t] with
 * [l], yielding the substitution [s], and returns the theorem
 * [s(hs) |- !z1...zp. s(p) ==> s(l) = s(r)] where [z1], ..., [zp] are the
 * variables among [x1], ..., [xn], [y1], ..., [ym] that are not instantiated
 * by [s], and renamed so as to avoid [v1], ..., [vk].
 *)
let vGEN_IMPREWR_CONV avs =
  let sel = lhs -| snd -| strip_forall -| snd -| dest_imp in
  let pmatch = vGEN_PART_MATCH_ALL sel in
  fun th ->
    let pmatch' = pmatch th in
    fun t ->
      let th' = pmatch' t in
      vVARIANT_RULE avs (vGENL (indep_vars th') th')

(* A conversion which returns not only a theorem but also a list of terms
 * which is a sublist of the theorem hypotheses, and a list of terms which
 * are the variables newly introduced by the conversion.
 *
 * See [IMPREWR_CONV] for an example.
 *)
type annot_conv = term -> thm * term option * term list

(* Takes a list of variables to avoid [av], a theorem [th] of the form
 * [h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r], and a term [t]
 * and returns a conversion with hypotheses defined as follows:
 * for a term [t], if [t] matches [l] with substitution [s], then return
 * the theorem [h1,...,hk,s(p) |- t = s(r)] and the the list containing only
 * [s(p)].
 *
 * The purpose of the conversion with hypothesis is to be able to distinguish
 * which hypothesis comes from the input theorem and which is added by the
 * conversion itself.
 *)
let vIMPREWR_CONV:Tset.t->thm->annot_conv =
  fun avs th ->
    let f t = vSPEC_VARS (vGEN_IMPREWR_CONV avs th t) in
    fun t ->
      let vs,uh = f t in
      let u = fst (dest_imp (concl uh)) in
      vUNDISCH uh,Some u,Tset.of_list vs

let vREWR_ANNOTCONV _avs th t =
  let th' = vPART_MATCH lhs th t in
  let _,t' = dest_binary_blind (concl th') in
  let new_vars = Tset.frees t' in
  let old_vars = Tset.union (Tset.frees t) (Tset.freesl (hyp th')) in
  th',None,Tset.subtract new_vars old_vars

let _vORDER_ANNOTCONV cnv t =
  let th,_,_ as res = cnv t in
  let l,r = dest_binary_blind (concl th) in
  if term_order l r then res else failwith "ORDER_ANNOTCONV"

(* Takes a theorem, a net of conversions with hypotheses (which also take
 * variables to avoid), and adds to the net the conversion corresponding to
 * the theorem.
 *
 * Special cases:
 * - usual term rewriting is handled with [REWR_CONV] instead of introducing
 *   a fake premise. Might be useful though to introduce a fake premise since
 *   the conversion would benefit from a better handling of variables occurring
 *   in the r.h.s. but not in the l.h.s.
 * - a theorem of the form [p ==> c] where [c] is not equational is turned into
 *   [p ==> c = T]
 * - a theorem of the form [p ==> ~c] is turned into [p ==> c = F]
 *)
let pat_cnv_of_thm th : (term * (term list->annot_conv)) =
  let th = vSPEC_ALL th in
  let lconsts = freesl (hyp th) and c = concl th in
  match c with
  |Comb(Comb(Const("=",_),l),r) as t ->
      let matches = vC (can -| term_match lconsts) in
      if free_in l r || (matches l r && matches r l)
      then t,vC vREWR_ANNOTCONV (vMAP_FORALL_BODY vEQT_INTRO th)
      else l,vC vREWR_ANNOTCONV th
  |Comb(Comb(Const("==>",_),p),c) as t ->
      let matches = vC (can -| fo_term_match lconsts) in
      let imprewr_concl f = vC vIMPREWR_CONV (vGEN_MAP_CONCLUSION f th) in
      (match c with
      |Comb(Comb(Const("=",_),l),r) ->
          if free_in l r || (matches l r && matches r l) || is_var l
          then
            if matches p c
            then t, vC vREWR_ANNOTCONV (vEQT_INTRO th)
            else c, imprewr_concl vEQT_INTRO
          else l, vC vIMPREWR_CONV th
      |Comb(Const("~",_),l) -> l, imprewr_concl vEQF_INTRO
      |l -> l, imprewr_concl vEQT_INTRO)
  |Comb(Const("~",_),l) -> l, vC vREWR_ANNOTCONV (vEQF_INTRO th)
  |Const("T",_bool_ty) -> failwith "pat_cnv_of_thm"
  |l -> l, vC vREWR_ANNOTCONV (vEQT_INTRO th)

let impconv_net_of_thm th =
  try
    let p,c = pat_cnv_of_thm th in
    let vs = Tset.freesl (hyp th) in
    Fo_nets.enter vs (p,(c,vs,th))
  with Failure _ -> vI

let patterns_of_thm = fst -| pat_cnv_of_thm

(* Apply a conversion net to the term at the top level, taking
 * avoided variables as parameter too.
 *)
let vREWRITES_IMPCONV
  (net:((term list -> annot_conv) * Tset.t * thm) Fo_nets.t) avs t =
  tryfind (fun (c,_,_) -> c avs t) (Fo_nets.lookup t net)

let extra_basic_rewrites =
  itlist (mk_rewrites false) [vNOT_FORALL_THM;vNOT_IMP] []

let vIMPREWR_CTXCONV :thm list -> (atomic->annot_conv) with_context =
  let rec top_depth c avs t =
    let rec (++) c1 c2 avs t =
      match c1 avs t with
      |_,Some _,_ as c1t -> c1t
      |th1,None,vs1 as c1t ->
        (try
          let th2,ho2,vs2 = c2 (Tset.union vs1 avs) (rand (concl th1)) in
          vTRANS th1 th2, ho2, Tset.union vs1 vs2
        with Failure _ -> c1t)
    and (+) c1 c2 avs t = try (c1 ++ c2) avs t with Failure _ -> c2 avs t
    and vCOMB_QCONV c avs l r =
      try
        match c avs l with
        |th,(Some _ as ho),vs -> vAP_THM th r,ho,vs
        |th1,None,vs1 ->
          (try
            let th2,ho2,vs2 = c (Tset.union vs1 avs) r in
            vMK_COMB (th1,th2), ho2, Tset.union vs1 vs2
          with Failure _ -> vAP_THM th1 r,None,vs1)
      with Failure _ ->
        let th2,ho2,vs2 = c avs r in
        vAP_TERM l th2,ho2,vs2
    in
    let vSUB_QCONV c avs t =
      match t with
      |Comb(l,r) -> vCOMB_QCONV c avs l r
      |Abs(v,_) ->
          let ho = ref None and vs = ref [] in
          let c' t =
            let th,ho',vs' = c (Tset.insert avs v) t in
            ho := ho'; vs := vs'; th
          in
          let res = vABS_CONV c' t in
          res,!ho,!vs
      |_ -> failwith "SUB_QCONV"
    in
    let rec (!) c avs t = (c ++ !c) avs t in
    (!c + (vSUB_QCONV (top_depth c) ++ top_depth c)) avs t
  in
  let bigger_net() =
    itlist (net_of_thm false) extra_basic_rewrites (basic_net()) in
  let basic_cnv t = vREWRITES_CONV (bigger_net ()) t,None,[] in
  let rec self net ths =
    let avs = Tset.flat_revmap (Tset.freesl -| hyp) ths in
    let cnv avs t =
      try vREWRITES_IMPCONV net avs t with Failure _ -> basic_cnv t
    in
    With_context(
      (fun a t ->
        let f = match a with Atomic -> top_depth | Non_atomic -> vI in
        f cnv (Tset.union (Tset.frees t) avs) t),
      (fun ts ->
        let ths' = map vASSUME ts in
        (*let ths'' = ths' @ GMATCH_MPS ths ths' in*)
        let ths'' = vMP_CLOSURE ths' ths' @ ths' @ vMP_CLOSURE ths ths' in
        self (itlist impconv_net_of_thm ths'' net) (ths'' @ ths)),
      (fun v ->
        let ths = ref [] in
        let f (_,vs,th) =
          if not (Tset.mem v vs) then (ths := th :: !ths; true) else false
        in
        let net' = Fo_nets.filter f net in
        self net' !ths))
  in
  fun ths -> self (itlist impconv_net_of_thm ths Fo_nets.empty_net) ths


(*****************************************************************************)
(* SOME USEFUL IMPLICATIONAL CONVERSIONS                                     *)
(*****************************************************************************)

(* Takes a conversion with hypotheses (with context) and makes an
 * implicational conversion out of it.
 * Basically turns a rewrite with hypotheses into an implicational rewrite
 * withouth hypotheses.
 * Adds existential quantifications for variables introduced by the rewrite.
 *)
let rec vREWR_IMPCONV_OF_CONV =
  let vIMP_SYM = vREWR_RULE (vTAUT (parse_term "A==>B==>C <=> B==>A==>C")) in
  let vIMP_EXIST = vGSYM vLEFT_IMP_EXISTS_THM in
  let vTRY_GEN v th = try vGEN v th with Failure _ -> th in
  fun (c:(atomic -> annot_conv) with_context) ->
    With_context(
      ((fun a v t ->
        let th,ho,new_vars = apply c a t in
        let th1,th2 = vEQ_IMP_RULE th in
        let res =
          match v with
          |Co ->
              let p,th2' = vUNDISCH_TERM th2 in
              let rec exists_intro = function
                |[] -> vDISCH_IMP_IMP (p::list_of_option ho) th2'
                |v::vs ->
                    let th = exists_intro vs in
                    try vREWR_RULE vIMP_EXIST (vGEN v th) with Failure _ -> th
              in
              exists_intro new_vars
          |Contra ->
              let th1' =
                match ho with None -> th1 | Some h -> vIMP_SYM (vDISCH h th1)
              in
              match new_vars with
              |[] -> th1'
              |_::_ -> vMAP_CONCLUSION (itlist vTRY_GEN new_vars) th1'
        in
        let t1,t2 = dest_imp (concl res) in
        if t1 = t2 then raise Unchanged else res):atomic->imp_conv),
      vREWR_IMPCONV_OF_CONV -| augment c,
      vREWR_IMPCONV_OF_CONV -| diminish c)

(* Applies the implicational rewrite, with context simplifications. *)
let vREWRITE_CTXIMPCONV =
  vDEPTH_CTXIMPCONV -| vREWR_IMPCONV_OF_CONV -| vIMPREWR_CTXCONV


(*****************************************************************************)
(* INTERFACE                                                                 *)
(*****************************************************************************)

(* Preprocessor. For now takes a theorem of the form [p ==> c1 /\ ... /\ ck]
 * and returns the list of theorems [p ==> c1], ..., [p ==> ck].
 *)
let preprocess = vCONJUNCTS -| vIMPLY_AND

(* Tactic for implicational rewrite. *)
let vIMP_REWRITE_TAC ths =
  vCTXIMPCONV_TAC (vREWRITE_CTXIMPCONV (flat (map preprocess ths)))

let vSEQ_IMP_REWRITE_TAC ths =
  let cnv =
    match ths with
    |[] -> vREWRITE_CTXIMPCONV [vTRUTH]
    |[th] -> vREWRITE_CTXIMPCONV (preprocess th)
    |_::_ ->
        let fcnv = vREWRITE_CTXIMPCONV -| preprocess in
        vREPEAT_UNCHANGED_CTXIMPCONV (map fcnv ths)
  in
  vCTXIMPCONV_TAC cnv

(* Tactic for implicational rewrite with assumptions. *)
let _vASM_IMP_REWRITE_TAC = vASM vIMP_REWRITE_TAC

(* Cases-like conversion for implicational theorems, i.e., for a theorem of
 * the form:
 * [h1,..,hk |- !x1...xn. p ==> !y1...ym. l = r], and a term [t],
 * return [(p ==> t') /\ (~p ==> t)], where [t'] is the result of rewriting
 * [t] by [l=r].
 *)
let rec vCASE_REWR_IMPCONV_OF_CONV =
  let vMP_TAUT th = vMATCH_MP (vTAUT th) in
  let vMP_LEM1 = vMP_TAUT (parse_term "(~P ==> Q = R) ==> (Q <=> (~P ==> R) /\\ (P ==> Q))") in
  let vMP_LEM2 = vMP_TAUT (parse_term "(P ==> Q = R) ==> (Q <=> (P ==> R) /\\ (~P ==> Q))") in
  fun (c:(atomic -> annot_conv) with_context) ->
    With_context(
      (fun a v t ->
        match apply c a t with
        |_,None,_ -> failwith "CASE_REWR_IMPCONV_OF_CONV"
        |th,Some h,_ ->
            let th' = vDISCH h th in
            let th'' = try vMP_LEM1 th' with Failure _ -> vMP_LEM2 th' in
            imp_conv_of_conv (vREWR_CONV th'') v t),
      vCASE_REWR_IMPCONV_OF_CONV -| augment c,
      vCASE_REWR_IMPCONV_OF_CONV -| diminish c)

let vCASE_REWRITE_CTXIMPCONV =
  vONCE_DEPTH_CTXIMPCONV -| vCASE_REWR_IMPCONV_OF_CONV -| vIMPREWR_CTXCONV

(* Tactic version of it. *)
let vCASE_REWRITE_TAC = vCTXIMPCONV_TAC -| vCASE_REWRITE_CTXIMPCONV -| preprocess

(*****************************************************************************)
(* IMPLICATIONAL CONVERSIONS WITH MULTIPLE RESULTS                           *)
(*****************************************************************************)

(* Multiple implicational conversion. *)
type imp_mconv = Variance.t -> term -> thm list

let mapply_with_context c ctx v t =
  map (vDISCH_CONJ ctx) (apply (augment c (Tset.strip_conj ctx)) v t)

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [CONJ_IMPMCONV ic1 ic2 Co (A /\ C)] returns
 * [B1 /\ C ==> A /\ C; ...; Bk /\ C ==> A /\ C; A /\ D1 ==> A /\ C; ...; Dn
 * ==> A /\ C].
 *
 * And similarly for the contravariant case.
 *)
let rec vCONJ_CTXIMPMCONV (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let t1,t2 = dest_conj t in
      let left,right =
        match v with
        |Co -> vMKIMPL_CONJ_CO2_CTXT,vMKIMPR_CONJ_CO_CTXT
        |Contra -> vMKIMPL_CONJ_CONTRA_CTXT,vMKIMPR_CONJ_CONTRA_CTXT
      in
      let th1s = map left (mapply_with_context c t2 v t1) in
      let th2s = map right (mapply_with_context c t1 v t2) in
      th1s @ th2s),
    vCONJ_CTXIMPMCONV -| augment c,
    vCONJ_CTXIMPMCONV -| diminish c)

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [B1 \/ C ==> A \/ C; ...; Bk \/ C ==> A \/ C; A \/ D1 ==> A \/ C; ...; Dn
 * ==> A \/ C].
 *
 * And similarly for the contravariant case.
 *)
let rec vDISJ_CTXIMPMCONV (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let t1,t2 = dest_disj t in
      let th1s = map (vC vMKIMPL_DISJ t2) (apply c v t1) in
      let th2s = map (vMKIMPR_DISJ t1) (apply c v t2) in
      th1s @ th2s),
    vDISJ_CTXIMPMCONV -| augment c,
    vDISJ_CTXIMPMCONV -| diminish c)

(* Consider two multiple implicational conversions ic1, ic2.
 * Suppose [ic1 Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * and [ic2 Co C] returns [D1 ==> C; ...; Dn ==> C],
 * then [DISJ_IMPMCONV ic1 ic2 Co (A \/ C)] returns
 * [(B1 ==> C) ==> (A ==> C); ...; (Bk ==> C) ==> (A ==> C); (A ==> D1) ==> (A
 * ==> C); ...; (A ==> Dn) ==> (A ==> C)].
 *
 * And similarly for the contravariant case.
 *)
let vIMP_CTXIMPMCONV (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let t1,t2 = dest_imp t in
      let th1s = map (vC vMKIMPL_IMP t2) (apply c (Variance.neg v) t1) in
      let th2s = map vMKIMPR_IMP_CTXT (mapply_with_context c t1 v t2) in
      th1s @ th2s),
    vCONJ_CTXIMPMCONV -| augment c,
    vCONJ_CTXIMPMCONV -| diminish c)

let rec vIFF_CTXIMPCONV (c:imp_mconv with_context) =
  With_context(
    ((fun v t ->
      let t1,t2 = dest_iff t in
      let left,right =
        match v with
        |Co -> vMKIMPL_CO_IFF,vMKIMPR_CO_IFF
        |Contra -> vMKIMPL_CONTRA_IFF,vMKIMPR_CONTRA_IFF
      in
      let th1s = map left (apply c v (mk_imp(t1,t2))) in
      let th2s = map right (apply c v (mk_imp(t2,t1))) in
      th1s @ th2s):imp_mconv),
    vIFF_CTXIMPCONV -| augment c,
    vIFF_CTXIMPCONV -| diminish c)

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Contra A] returns a list [A ==> B1; ...; A ==> Bk],
 * then [NOT_IMPMCONV ic Co ~A] returns [~B1 ==> ~A; ...; ~Bk ==> ~A].
 *
 * And similarly for the contravariant case.
 *)
let rec vNOT_CTXIMPMCONV (c:imp_mconv with_context) : imp_mconv with_context =
  With_context(
    (fun v t ->
      map vMKIMP_NOT (try_list (apply c (Variance.neg v)) (dest_neg t))),
    vNOT_CTXIMPMCONV -| augment c,
    vNOT_CTXIMPMCONV -| diminish c)

let rec vQUANT_CTXIMPMCONV mkimp sel (c:imp_mconv with_context)
  : imp_mconv with_context =
  With_context(
    (fun v t ->
      let x,b = sel t in
      let c' = diminish c x in
      map (mkimp x) (try_list (apply c' v) b)),
    vQUANT_CTXIMPMCONV mkimp sel -| augment c,
    vQUANT_CTXIMPMCONV mkimp sel -| diminish c)

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [FORALL_IMPMCONV ic Co (!x.A)] returns [(!x.B1) ==> (!x.A); ...;
 * (!x.Bk) ==> (!x.A)].
 *
 * And similarly for the contravariant case.
 *)
let vFORALL_CTXIMPMCONV = vQUANT_CTXIMPMCONV vMKIMP_FORALL dest_forall

(* Consider one multiple implicational conversion ic.
 * Suppose [ic Co A] returns a list [B1 ==> A; ...; Bk ==> A],
 * then [EXISTS_IMPMCONV ic Co (?x.A)] returns [(?x.B1) ==> (?x.A); ...;
 * (?x.Bk) ==> (?x.A)].
 *
 * And similarly for the contravariant case.
 *)
let vEXISTS_CTXIMPMCONV = vQUANT_CTXIMPMCONV vMKIMP_EXISTS dest_exists

(* Applies a multiple implicational conversion on the subformula(s) of the
 * input term
 *)
let rec vSUB_CTXIMPMCONV =
  let iff_ty = (parse_type "bool->bool->bool") in
  fun c ->
  With_context(
    ((fun v t ->
      let n,ty = dest_const (fst (strip_comb t)) in
      apply
        ((match n with
        |"==>" -> vIMP_CTXIMPMCONV
        |"/\\" -> vCONJ_CTXIMPMCONV
        |"\\/" -> vDISJ_CTXIMPMCONV
        |"!" -> vFORALL_CTXIMPMCONV
        |"?" -> vEXISTS_CTXIMPMCONV
        |"~" -> vNOT_CTXIMPMCONV
        |"=" when ty = iff_ty -> vIFF_CTXIMPCONV
        |_ -> failwith "SUB_CTXIMPMCONV") c) v t):imp_mconv),
    vSUB_CTXIMPMCONV -| augment c,
    vSUB_CTXIMPMCONV -| diminish c)


(* Applies a multiple implicational conversion once to the first suitable sub-term(s)
 * encountered in bottom-up order.
 *)
let rec vDEPTH_CTXIMPMCONV (c : (atomic->imp_mconv) with_context) =
  With_context(
    (fun v t ->
      try
        let ths = apply (vSUB_CTXIMPMCONV (vDEPTH_CTXIMPMCONV c)) v t in
        apply c Non_atomic v t @ ths
      with Failure msg -> if msg = "SUB_CTXIMPMCONV" then
        (apply c Atomic v t) else failwith msg),
      vDEPTH_CTXIMPMCONV -| augment c,
      vDEPTH_CTXIMPMCONV -| diminish c)


(*****************************************************************************)
(* REWRITE IMPLICATIONAL CONVERSIONS                                         *)
(*****************************************************************************)

(* Multiple implicational conversion with hypotheses. *)
type annot_mconv = term -> (thm * term option * term list) list

(* Takes a theorem, a net of conversions with hypotheses (which also take
 * variables to avoid), and adds to the net the conversion corresponding to
 * the theorem.
 *
 * Special cases:
 * - usual term rewriting is handled with [REWR_CONV] instead of introducing
 *   a fake premise. Might be useful though to introduce a fake premise since
 *   the conversion would benefit from a better handling of variables occurring
 *   in the r.h.s. but not in the l.h.s.
 * - a theorem of the form [p ==> c] where [c] is not equational is turned into
 *   [p ==> c = T]
 * - a theorem of the form [p ==> ~c] is turned into [p ==> c = F]
 *)
let target_pat_cnv_of_thm th : (term * (term list->annot_conv)) =
  let th = vSPEC_ALL th in
  match concl th with
  |Comb(Comb(Const("=",_),l),_) -> l,vC vREWR_ANNOTCONV th
  |Comb(Comb(Const("==>",_),_),c) ->
      let pat,th' =
        match c with
        |Comb(Comb(Const("=",_),l),_) -> l, th
        |Comb(Const("~",_),l) -> l, vGEN_MAP_CONCLUSION vEQF_INTRO th
        |_l -> c, vGEN_MAP_CONCLUSION vEQT_INTRO th
      in
      pat, vC vIMPREWR_CONV th'
  |Comb(Const("~",_),l) -> l, vC vREWR_ANNOTCONV (vEQF_INTRO th)
  |Const("T",_bool_ty) -> failwith "target_pat_cnv_of_thm"
  |l -> l, vC vREWR_ANNOTCONV (vEQT_INTRO th)

let target_impconv_net_of_thm th =
  try
    let p,c = target_pat_cnv_of_thm th in
    let vs = Tset.freesl (hyp th) in
    Fo_nets.enter vs (p,(c,vs,th))
  with Failure _ -> vI

let _target_patterns_of_thm = fst -| target_pat_cnv_of_thm

(* Multiple conversion which returns all the possible rewrites (on one subterm
 * only) by one theorem.
 *)

let vDEEP_IMP_REWR_MCONV:thm list->(atomic->annot_mconv) with_context =
  let map_fst f (x,y,z) = f x,y,z in
  let vCOMB_MCONV c l r =
    map (map_fst (vC vAP_THM r)) (c l) @ map (map_fst (vAP_TERM l)) (c r)
  and vABS_MCONV c v b =
    let ths = c b in
    try map (map_fst (vABS v)) ths
    with Failure _ ->
      let gv = genvar(type_of v) in
      let f (gth,ho,vs) =
        let gtm = concl gth in
        let l,r = dest_eq gtm in
        let v' = variant (frees gtm) v in
        let l' = alpha v' l and r' = alpha v' r in
        vEQ_MP (vALPHA gtm (mk_eq(l',r'))) gth,ho,vs
      in
      let b' = vsubst[gv,v] b in
      map f (map (map_fst (vABS gv)) (c b'))
  in
  let vSUB_MCONV c = function
    |Comb(l,r) -> vCOMB_MCONV c l r
    |Abs(v,b) -> vABS_MCONV c v b
    |Const _ | Var _ -> []
  in
  let rec top_depth c t = vSUB_MCONV (top_depth c) t @ c t in
  let vREWRITES_IMPCONV (net:((term list -> annot_conv) * Tset.t * thm) Fo_nets.t) avs t =
    mapfilter (fun (c,_,_) -> c avs t) (Fo_nets.lookup t net)
  in
  let rec self net ths =
    let avs = Tset.flat_revmap (Tset.freesl -| hyp) ths in
    With_context(
      (fun a t ->
        let avs' = Tset.union (Tset.frees t) avs in
        let cnv t = vREWRITES_IMPCONV net avs' t in
        let f =
          match a with
          |Atomic -> top_depth
          |Non_atomic -> (fun cnv avs -> cnv avs)
        in
        f cnv t),
      (fun _ -> self net ths),
      (fun v ->
        let ths = ref [] in
        let f (_,vs,th) =
          if not (Tset.mem v vs) then (ths := th :: !ths; true) else false
        in
        let net' = Fo_nets.filter f net in
        self net' !ths))
  in
  fun ths ->
    self (itlist target_impconv_net_of_thm ths Fo_nets.empty_net) ths

(* Takes a multiple conversion with hypotheses (which also takes a context as
 * parameter) and makes a multiple implicational conversion out of it.
 *
 * Basically extends [GENERAL_REWRITE_IMPCONV] to the multiple conversion
 * case.
 *)
let rec vREWR_IMPMCONV_OF_MCONV =
  let vIMP_SYM = vREWR_RULE (vTAUT (parse_term "A==>B==>C <=> B==>A==>C")) in
  let vIMP_EXIST = vGSYM vLEFT_IMP_EXISTS_THM in
  let vTRY_GEN v th = try vGEN v th with Failure _ -> th in
  fun (c:(atomic -> annot_mconv) with_context) ->
    With_context(
      ((fun a v t ->
        let f (th,ho,new_vars) =
          let th1,th2 = vEQ_IMP_RULE th in
          match v with
          |Co ->
              let p,th2' = vUNDISCH_TERM th2 in
              let rec exists_intro = function
                |[] -> vDISCH_IMP_IMP (p::list_of_option ho) th2'
                |v::vs ->
                    let th = exists_intro vs in
                    try vREWR_RULE vIMP_EXIST (vGEN v th) with Failure _ -> th
              in
              exists_intro new_vars
          |Contra ->
              let th1' =
                match ho with None -> th1 | Some h -> vIMP_SYM (vDISCH h th1)
              in
              match new_vars with
              |[] -> th1'
              |_::_ -> vMAP_CONCLUSION (itlist vTRY_GEN new_vars) th1'
        in
        map f (apply c a t)):atomic->imp_mconv),
      vREWR_IMPMCONV_OF_MCONV -| augment c,
      vREWR_IMPMCONV_OF_MCONV -| diminish c)


(*****************************************************************************)
(* TARGET REWRITING                                                          *)
(*****************************************************************************)

let vEXISTS_CTXIMPCONV:imp_conv with_context =
  let vEXISTSs i p =
    let codom,dom = unzip i in
    let f i ps = vsubst [i] (snd (dest_exists (hd ps))) :: ps in
    match rev_itlist f i [list_mk_exists(dom,p)] with h::ps ->
    rev_itlist vEXISTS (zip ps (rev codom)) (vASSUME h) | _ -> assert false
  in
  let vLEFT_FORALL_IMP = vREWR_RULE vLEFT_FORALL_IMP_THM in
  let rec self ts =
    With_context
    ((fun v t ->
      match v,t with
      |Co,Comb(Const("?",_),_) ->
          let vs,b = strip_exists t in
          let bs = strip_conj b in
          let hmatch (n,b) =
            match partition (vC mem vs) (variables b) with
            |[],_ -> failwith "EXISTS_CTXIMPCONV"
            |_::_ as lvs,lcs ->
                fun h ->
                  match term_match lcs b h with
                  |_,i,j when filter (uncurry (<>)) j = [] ->
                      (if i = [] then zip lvs lvs else i),n
                  |_ -> failwith "EXISTS_CTXIMPCONV"
          in
          let s,n = tryfind_fun (mapfilteri (curry (tryfind -| hmatch)) bs) ts in
          let th = vEXISTSs (map (fun v -> rev_assocd v s v,v) vs) b in
          let th' = vDISCH_HD th in
          let h = fst (dest_imp (concl th')) in
          (match strip_conj h with
          |[] -> assert false
          |[_h] -> vDISCH vT_ th
          |_::_ as hs ->
            match chop_list n hs with 
            | hs1,h'::hs2 ->
            let hs_th = vCONJ_ACI_RULE (mk_eq(h,list_mk_conj (h'::(hs1@hs2)))) in
            let th1 = vCONV_RULE (vLAND_CONV (vREWR_CONV hs_th)) th' in
            let th2 = vUNDISCH (vCONV_RULE (vREWR_CONV vIMP_CONJ) th1) in
            let vs' = subtract vs (map snd s) in
            let f v th = try vLEFT_FORALL_IMP (vGEN v th) with Failure _ -> th in
            itlist f vs' th2 
            | _ -> assert false)
      |_ -> failwith "EXISTS_CTXIMPCONV"),
      (fun ts' -> self (Tset.union ts' ts)),
      (fun _ -> self ts))
  in
  self []

(* Takes a theorem which results of an implicational conversion and applies a
 * multiple implicational conversion on the outcome.
 *)
let bind_impmconv (c:imp_mconv) v th =
  let t1,t2 = dest_imp (concl th) in
  match v with
  |Co -> map (vC vIMP_TRANS th) (c v t1)
  |Contra -> map (vIMP_TRANS th) (c v t2)


(* Target rewrite implicational conversion:
 * [TARGET_REWRITE_IMPCONV sths ts] is an implicational conversion which
 * applies all the possible implicational rewrites on the input term until
 * one of the resulting terms matches one of the terms in [ts].
 *
 * Note that we allow several target terms and not just one. See
 * TARGET_REWRITE_TAC for a justification.
 *)
let vTARGET_REWRITE_IMPCONV : thm list -> term list -> imp_conv =
  let vPRE = apply (vTRY_CTXIMPCONV (vREWRITE_CTXIMPCONV [])) in
  let vPOST = vTRY_CTXIMPCONV (vTOP_DEPTH_CTXIMPCONV vEXISTS_CTXIMPCONV) in
  fun sths ->
    let one_step_sths v uh =
      let pre v th = try bind_impconv vPRE v th with Unchanged -> th in
      let post v = bind_ctximpconv vPOST v in
      let f =
        vDEPTH_CTXIMPMCONV -| vREWR_IMPMCONV_OF_MCONV -| vDEEP_IMP_REWR_MCONV
      in
      map (post v) (bind_impmconv (apply (f sths)) v (pre v uh))
    in
    let flat l = uniq (itlist (merge thm_lt) l []) in
    fun ts v t ->
      let rec self ths =
        let pool = flat (map (mergesort thm_lt -| one_step_sths v) ths) in
        let sel th = imp_conv_outcome th v in
        let is_one_sol g = (can -| find_term -| can -| fo_term_match []) g -| sel in
        let is_sol th = tryfind is_one_sol ts th in
        try bind_ctximpconv vPOST v (find is_sol pool)
        with _ ->
          match pool with
          |[] -> failwith "TARGET_REWRITE_IMPCONV: no path found"
          |_::_ -> self (map (bind_ctximpconv vPOST v) pool)
      in
      self [vIMP_REFL t]

(* Tactic version of it.
 *
 * Since the target theorem is preprocessed, it can yield several theorems.
 * Therefore, there is not just one possible target pattern but several.
 *)
let vTARGET_REWRITE_TAC sths th =
  let sths' = flat (map preprocess sths) in
  let ths = preprocess th and (+) = vTHEN_IMPCONV in
  vIMPCONV_TAC
  (vTARGET_REWRITE_IMPCONV sths' (map patterns_of_thm ths)
    + imp_conv_of_ctx_imp_conv (vREWRITE_CTXIMPCONV ths))

let vHINT_EXISTS_TAC = vCTXIMPCONV_TAC (vTOP_DEPTH_CTXIMPCONV vEXISTS_CTXIMPCONV)

end in

Impconv.vIMP_REWRITE_TAC,
Impconv.vTARGET_REWRITE_TAC,
Impconv.vHINT_EXISTS_TAC,
Impconv.vSEQ_IMP_REWRITE_TAC,
Impconv.vCASE_REWRITE_TAC;;
