(* ========================================================================= *)
(* Version of the MESON procedure a la PTTP. Various search options.         *)
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
open Canon

(* ------------------------------------------------------------------------- *)
(* Some parameters controlling MESON behaviour.                              *)
(* ------------------------------------------------------------------------- *)

let meson_depth = ref false;;   (* Use depth not inference bound.            *)

let meson_prefine = ref true;;  (* Use Plaisted's positive refinement.       *)

let meson_dcutin = ref 1;;      (* Min size for d-and-c optimization cut-in. *)

let meson_skew = ref 3;;        (* Skew proof bias (one side is <= n / skew) *)

let meson_brand = ref false;;   (* Use Brand transformation                  *)

let meson_split_limit = ref 8;; (* Limit of case splits before MESON proper  *)

let meson_chatty = ref false;;  (* Old-style verbose MESON output            *)

(* ------------------------------------------------------------------------- *)
(* Prolog exception.                                                         *)
(* ------------------------------------------------------------------------- *)

exception Cut;;

(* ------------------------------------------------------------------------- *)
(* Shadow syntax for FOL terms in NNF. Functions and predicates have         *)
(* numeric codes, and negation is done by negating the predicate code.       *)
(* ------------------------------------------------------------------------- *)

type fol_term = Fvar of int
              | Fnapp of int * fol_term list;;

type fol_atom = int * fol_term list;;

type fol_form = Atom of fol_atom
               | Conj of fol_form * fol_form
               | Disj of fol_form * fol_form
               | Forallq of int * fol_form;;

(* ------------------------------------------------------------------------- *)
(* Type for recording a MESON proof tree.                                    *)
(* ------------------------------------------------------------------------- *)

type fol_goal =
  Subgoal of fol_atom * fol_goal list * (int * thm) *
             int * (fol_term * int)list;;

(* ------------------------------------------------------------------------- *)
(* General MESON procedure, using assumptions and with settable limits.      *)
(* ------------------------------------------------------------------------- *)

module Meson = struct

  let offinc = 10000
  and inferences = ref 0

  (* ----------------------------------------------------------------------- *)
  (* Negate a clause.                                                        *)
  (* ----------------------------------------------------------------------- *)

    let mk_negated (p,a) = -p,a

  (* ----------------------------------------------------------------------- *)
  (* Like partition, but with short-circuiting for special situation.        *)
  (* ----------------------------------------------------------------------- *)

  let qpartition p m =
    let rec qpartition l =
      if l == m then raise Unchanged else
      match l with
        [] -> raise Unchanged
      | (h::t) -> if p h then
                    try let yes,no = qpartition t in h::yes,no
                    with Unchanged -> [h],t
                  else
                    let yes,no = qpartition t in yes,h::no in
    function l -> try qpartition l
                  with Unchanged -> [],l

  (* ----------------------------------------------------------------------- *)
  (* Translate a term (in NNF) into the shadow syntax.                       *)
  (* ----------------------------------------------------------------------- *)

  let reset_vars,fol_of_var,hol_of_var =
    let vstore = ref []
    and gstore = ref []
    and vcounter = ref 0 in
    let inc_vcounter() =
      let n = !vcounter in
      let m = n + 1 in
      if m >= offinc then failwith "inc_vcounter: too many variables" else
      (vcounter := m; n) in
    let reset_vars() = vstore := []; gstore := []; vcounter := 0 in
    let fol_of_var v =
      let currentvars = !vstore in
      try assoc v currentvars with Failure _ ->
      let n = inc_vcounter() in
      vstore := (v,n)::currentvars; n in
    let hol_of_var v =
      try rev_assoc v (!vstore)
      with Failure _ -> rev_assoc v (!gstore) in
    let hol_of_bumped_var v =
      try hol_of_var v with Failure _ ->
      let v' = v mod offinc in
      let hv' = hol_of_var v' in
      let gv = genvar(type_of hv') in
      gstore := (gv,v)::(!gstore); gv in
    reset_vars,fol_of_var,hol_of_bumped_var

  let reset_consts,fol_of_const,hol_of_const =
    let false_tm = (parse_term "F") in
    let cstore = ref ([]:(term * int)list)
    and ccounter = ref 2 in
    let reset_consts() = cstore := [false_tm,1]; ccounter := 2 in
    let fol_of_const c =
      let currentconsts = !cstore in
      try assoc c currentconsts with Failure _ ->
      let n = !ccounter in
      ccounter := n + 1; cstore := (c,n)::currentconsts; n in
    let hol_of_const c = rev_assoc c (!cstore) in
    reset_consts,fol_of_const,hol_of_const

  let rec fol_of_term env consts tm =
    if is_var tm && not (mem tm consts) then
      Fvar(fol_of_var tm)
    else
      let f,args = strip_comb tm in
      if mem f env then failwith "fol_of_term: higher order" else
      let ff = fol_of_const f in
      Fnapp(ff,map (fol_of_term env consts) args)

  let fol_of_atom env consts tm =
    let f,args = strip_comb tm in
    if mem f env then failwith "fol_of_atom: higher order" else
    let ff = fol_of_const f in
    ff,map (fol_of_term env consts) args

  let fol_of_literal env consts tm =
    try let tm' = dest_neg tm in
        let p,a = fol_of_atom env consts tm' in
        -p,a
    with Failure _ -> fol_of_atom env consts tm

  let rec fol_of_form env consts tm =
    try let v,bod = dest_forall tm in
        let fv = fol_of_var v in
        let fbod = fol_of_form (v::env) (subtract consts [v]) bod in
        Forallq(fv,fbod)
    with Failure _ -> try
        let l,r = dest_conj tm in
        let fl = fol_of_form env consts l
        and fr = fol_of_form env consts r in
        Conj(fl,fr)
    with Failure _ -> try
        let l,r = dest_disj tm in
        let fl = fol_of_form env consts l
        and fr = fol_of_form env consts r in
        Disj(fl,fr)
    with Failure _ ->
        Atom(fol_of_literal env consts tm)

  (* ----------------------------------------------------------------------- *)
  (* Further translation functions for HOL formulas.                         *)
  (* ----------------------------------------------------------------------- *)

  let rec hol_of_term tm =
    match tm with
      Fvar v -> hol_of_var v
    | Fnapp(f,args) -> list_mk_comb(hol_of_const f,map hol_of_term args)

  let hol_of_atom (p,args) =
    list_mk_comb(hol_of_const p,map hol_of_term args)

  let hol_of_literal (p,args) =
    if p < 0 then mk_neg(hol_of_atom(-p,args))
    else hol_of_atom (p,args)

  (* ----------------------------------------------------------------------- *)
  (* Versions of shadow syntax operations with variable bumping.             *)
  (* ----------------------------------------------------------------------- *)

  let rec fol_free_in v tm =
    match tm with
      Fvar x -> x = v
    | Fnapp(_,lis) -> exists (fol_free_in v) lis

  let rec fol_subst theta tm =
    match tm with
      Fvar v -> rev_assocd v theta tm
    | Fnapp(f,args) ->
          let args' = qmap (fol_subst theta) args in
          if args' == args then tm else Fnapp(f,args')

  let fol_inst theta ((p,args) as at:fol_atom) =
    let args' = qmap (fol_subst theta) args in
    if args' == args then at else p,args'

  let rec fol_subst_bump offset theta tm =
    match tm with
      Fvar v -> if v < offinc then
                 let v' = v + offset in
                 rev_assocd v' theta (Fvar(v'))
               else
                 rev_assocd v theta tm
    | Fnapp(f,args) ->
          let args' = qmap (fol_subst_bump offset theta) args in
          if args' == args then tm else Fnapp(f,args')

  let fol_inst_bump offset theta ((p,args) as at:fol_atom) =
    let args' = qmap (fol_subst_bump offset theta) args in
    if args' == args then at else p,args'

  (* ----------------------------------------------------------------------- *)
  (* Main unification function, maintaining a "graph" instantiation.         *)
  (* We implicitly apply an offset to variables in the second term, so this  *)
  (* is not symmetric between the arguments.                                 *)
  (* ----------------------------------------------------------------------- *)

  let rec istriv env x t =
    match t with
      Fvar y -> y = x ||
                (try let t' = rev_assoc y env in istriv env x t'
                 with Failure msg -> if msg = "find" then false else failwith msg)
    | Fnapp(_f,args) -> exists (istriv env x) args && failwith "cyclic"

  let rec fol_unify offset tm1 tm2 sofar =
    match tm1,tm2 with
      Fnapp(f,fargs),Fnapp(g,gargs) ->
          if f <> g then failwith "" else
          itlist2 (fol_unify offset) fargs gargs sofar
    | _,Fvar(x) ->
         (let x' = x + offset in
          try let tm2' = rev_assoc x' sofar in
              fol_unify 0 tm1 tm2' sofar
          with Failure msg -> if msg = "find" then
              if istriv sofar x' tm1 then sofar
              else (tm1,x')::sofar
          else failwith msg)
    | Fvar(x),_ ->
         (try let tm1' = rev_assoc x sofar in
              fol_unify offset tm1' tm2 sofar
          with Failure msg -> if msg = "find" then
              let tm2' = fol_subst_bump offset [] tm2 in
              if istriv sofar x tm2' then sofar
              else (tm2',x)::sofar
          else failwith msg)

  (* ----------------------------------------------------------------------- *)
  (* Test for equality under the pending instantiations.                     *)
  (* ----------------------------------------------------------------------- *)

  let rec fol_eq insts tm1 tm2 =
    tm1 == tm2 ||
    match tm1,tm2 with
      Fnapp(f,fargs),Fnapp(g,gargs) ->
          f = g && forall2 (fol_eq insts) fargs gargs
    | _,Fvar(x) ->
         (try let tm2' = rev_assoc x insts in
              fol_eq insts tm1 tm2'
          with Failure msg -> if msg = "find" then
          try istriv insts x tm1 with Failure _ -> false else failwith msg)
    | Fvar(x),_ ->
         (try let tm1' = rev_assoc x insts in
              fol_eq insts tm1' tm2
          with Failure msg -> if msg = "find" then
          try istriv insts x tm2 with Failure _ -> false else failwith msg)

  let fol_atom_eq insts (p1,args1) (p2,args2) =
    p1 = p2 && forall2 (fol_eq insts) args1 args2

  (* ----------------------------------------------------------------------- *)
  (* Cacheing continuations. Very crude, but it works remarkably well.       *)
  (* ----------------------------------------------------------------------- *)

  let cacheconts f =
    let memory = ref [] in
    fun (_gg,(insts,_offset,size) as input) ->
      if exists (fun (_,(insts',_,size')) ->
                     insts = insts' && (size <= size' || !meson_depth))
          (!memory)
      then failwith "cachecont"
      else memory := input::(!memory); f input

  (* ----------------------------------------------------------------------- *)
  (* Check ancestor list for repetition.                                     *)
  (* ----------------------------------------------------------------------- *)

  let checkan insts (p,a) ancestors =
    let p' = -p in
    let t' = (p',a) in
    try let ours = assoc p' ancestors in
        if exists (fun u -> fol_atom_eq insts t' (snd(fst u))) ours
        then failwith "checkan"
        else ancestors
    with Failure msg -> if msg = "find" then ancestors else failwith msg

  (* ----------------------------------------------------------------------- *)
  (* Insert new goal's negation in ancestor clause, given refinement.        *)
  (* ----------------------------------------------------------------------- *)

  let insertan insts (p,a) ancestors =
    let p' = -p in
    let t' = (p',a) in
    let ourancp,otheranc =
      try remove (fun (pr,_) -> pr = p') ancestors
      with Failure _ -> (p',[]),ancestors in
    let ouranc = snd ourancp in
    if exists (fun u -> fol_atom_eq insts t' (snd(fst u))) ouranc
    then failwith "insertan: loop"
    else (p',(([],t'),(0,vTRUTH))::ouranc)::otheranc

  (* ----------------------------------------------------------------------- *)
  (* Apply a multi-level "graph" instantiation.                              *)
  (* ----------------------------------------------------------------------- *)

  let rec fol_subst_partial insts tm =
    match tm with
      Fvar(v) -> (try let t = rev_assoc v insts in
                      fol_subst_partial insts t
                  with Failure msg -> if msg ="find" then tm else failwith msg)
    | Fnapp(f,args) -> Fnapp(f,map (fol_subst_partial insts) args)

  (* ----------------------------------------------------------------------- *)
  (* Tease apart local and global instantiations.                            *)
  (* At the moment we also force a full evaluation; should eliminate this.   *)
  (* ----------------------------------------------------------------------- *)

  let separate_insts offset oldinsts newinsts =
    let locins,globins =
      qpartition (fun (_,v) -> offset <= v) oldinsts newinsts in
    if globins = oldinsts then
      map (fun (t,x) -> fol_subst_partial newinsts t,x) locins,oldinsts
    else
      map (fun (t,x) -> fol_subst_partial newinsts t,x) locins,
      map (fun (t,x) -> fol_subst_partial newinsts t,x) globins

  (* ----------------------------------------------------------------------- *)
  (* Perform basic MESON expansion.                                          *)
  (* ----------------------------------------------------------------------- *)

  let meson_single_expand loffset rule ((g,ancestors),(insts,offset,size)) =
    let (hyps,conc),_tag = rule in
    let allins = rev_itlist2 (fol_unify loffset) (snd g) (snd conc) insts in
    let locin,globin = separate_insts offset insts allins in
    let mk_ihyp h =
      let h' = fol_inst_bump offset locin h in
      h',checkan insts h' ancestors in
    let newhyps =  map mk_ihyp hyps in
    inferences := !inferences + 1;
    newhyps,(globin,offset+offinc,size-length hyps)

  (* ----------------------------------------------------------------------- *)
  (* Perform first basic expansion which allows continuation call.           *)
  (* ----------------------------------------------------------------------- *)

  let meson_expand_cont loffset rules state cont =
    tryfind
     (fun r -> cont (snd r) (meson_single_expand loffset r state)) rules

  (* ----------------------------------------------------------------------- *)
  (* Try expansion and continuation call with ancestor or initial rule.      *)
  (* ----------------------------------------------------------------------- *)

  let meson_expand rules ((g,ancestors),((insts,offset,size) as tup)) cont =
    let pr = fst g in
    let newancestors = insertan insts g ancestors in
    let newstate = (g,newancestors),tup in
    try if !meson_prefine && pr > 0 then failwith "meson_expand" else
        let arules = assoc pr ancestors in
        meson_expand_cont 0 arules newstate cont
    with Cut -> failwith "meson_expand" | Failure _ ->
        try let crules =
              filter (fun ((h,_),_) -> length h <= size) (assoc pr rules) in
            meson_expand_cont offset crules newstate cont
        with Cut -> failwith "meson_expand"
           | Failure _ -> failwith "meson_expand"

  (* ----------------------------------------------------------------------- *)
  (* Simple Prolog engine organizing search and backtracking.                *)
  (* ----------------------------------------------------------------------- *)

  let expand_goal rules =
    let rec expand_goal depth ((g,_),(insts,offset,size) as state) cont =
      if depth < 0 then failwith "expand_goal: too deep" else
      meson_expand rules state
        (fun apprule (_,(pinsts,_,_) as newstate) ->
            expand_goals (depth-1) newstate
              (cacheconts(fun (gs,(newinsts,newoffset,newsize)) ->
                 let locin,globin = separate_insts offset pinsts newinsts in
                 let g' = Subgoal(g,gs,apprule,offset,locin) in
                 if globin = insts && gs = [] then
                   try cont(g',(globin,newoffset,size))
                   with Failure _ -> raise Cut
                 else
                   try cont(g',(globin,newoffset,newsize))
                   with Cut -> failwith "expand_goal"
                      | Failure _ -> failwith "expand_goal")))

    and expand_goals depth (gl,(insts,offset,size as tup)) cont =
      match gl with
        [] -> cont ([],tup)

      | [g] -> expand_goal depth (g,tup) (fun (g',stup) -> cont([g'],stup))

      | gl -> if size >= !meson_dcutin then
                let lsize = size / (!meson_skew) in
                let rsize = size - lsize in
                let lgoals,rgoals = chop_list (length gl / 2) gl in
                try expand_goals depth (lgoals,(insts,offset,lsize))
                     (cacheconts(fun (lg',(i,off,n)) ->
                         expand_goals depth (rgoals,(i,off,n + rsize))
                           (cacheconts(fun (rg',ztup) -> cont (lg'@rg',ztup)))))
                with Failure _ ->
                    expand_goals depth (rgoals,(insts,offset,lsize))
                      (cacheconts(fun (rg',(i,off,n)) ->
                         expand_goals depth (lgoals,(i,off,n + rsize))
                           (cacheconts (fun (lg',((_,_,fsize) as ztup)) ->
                              if n + rsize <= lsize + fsize
                              then failwith "repetition of demigoal pair"
                              else cont (lg'@rg',ztup)))))
              else
                match gl with g::gs ->
                expand_goal depth (g,tup)
                  (cacheconts(fun (g',stup) ->
                      expand_goals depth (gs,stup)
                        (cacheconts(fun (gs',ftup) -> cont(g'::gs',ftup))))) | _ -> assert false in

    fun g maxdep maxinf cont ->
      expand_goal maxdep (g,([],2 * offinc,maxinf)) cont

  (* ----------------------------------------------------------------------- *)
  (* With iterative deepening of inferences or depth.                        *)
  (* ----------------------------------------------------------------------- *)

  let solve_goal rules incdepth min max incsize =
    let rec solve n g =
      if n > max then failwith "solve_goal: Too deep" else
      (if !meson_chatty && !verbose then
        (Format.print_string
          ((string_of_int (!inferences))^" inferences so far. "^
              "Searching with maximum size "^(string_of_int n)^".");
         Format.print_newline())
       else if !verbose then
        (Format.print_string(string_of_int (!inferences)^"..");
         Format.print_flush())
       else ());
      try let gi =
            if incdepth then expand_goal rules g n 100000 (fun x -> x)
            else expand_goal rules g 100000 n (fun x -> x) in
          (if !meson_chatty && !verbose then
            (Format.print_string
              ("Goal solved with "^(string_of_int (!inferences))^
               " inferences.");
             Format.print_newline())
           else if !verbose then
            (Format.print_string("solved at "^string_of_int (!inferences));
             Format.print_newline())
           else ());
          gi
      with Failure _ -> solve (n + incsize) g in
    fun g -> solve min (g,[])

  (* ----------------------------------------------------------------------- *)
  (* Creation of tagged contrapositives from a HOL clause.                   *)
  (* This includes any possible support clauses (1 = falsity).               *)
  (* The rules are partitioned into association lists.                       *)
  (* ----------------------------------------------------------------------- *)

  let fol_of_hol_clauses =
    let eqt (a1,(b1,c1)) (a2, (b2,c2)) =
     ((a1 = a2) && (b1 = b2) && (equals_thm c1 c2)) in
    let rec mk_contraposes n th used unused sofar =
      match unused with
        [] -> sofar
      | h::t -> let nw = (map mk_negated (used @ t),h),(n,th) in
                mk_contraposes (n + 1) th (used@[h]) t (nw::sofar) in
    let fol_of_hol_clause th =
      let lconsts = freesl (hyp th) in
      let tm = concl th in
      let hlits = disjuncts tm in
      let flits = map (fol_of_literal [] lconsts) hlits in
      let basics = mk_contraposes 0 th [] flits [] in
      if forall (fun (p,_) -> p < 0) flits then
        ((map mk_negated flits,(1,[])),(-1,th))::basics
      else basics in
    fun thms ->
      let rawrules = itlist (union' eqt -| fol_of_hol_clause) thms [] in
      let prs = setify (map (fst -| snd -| fst) rawrules) in
      let prules =
        map (fun t -> t,filter ((=) t -| fst -| snd -| fst) rawrules) prs in
      let srules = sort (fun (p,_) (q,_) -> abs(p) <= abs(q)) prules in
      srules

  (* ----------------------------------------------------------------------- *)
  (* Optimize set of clauses; changing literal order complicates HOL stuff.  *)
  (* ----------------------------------------------------------------------- *)

  let optimize_rules =
    let optimize_clause_order cls =
      sort (fun ((l1,_),_) ((l2,_),_) -> length l1 <= length l2) cls in
    map (fun (a,b) -> a,optimize_clause_order b)

  (* ----------------------------------------------------------------------- *)
  (* Create a HOL contrapositive on demand, with a cache.                    *)
  (* ----------------------------------------------------------------------- *)

  let clear_contrapos_cache,make_hol_contrapos =
    let vDISJ_AC = vAC vDISJ_ACI
    and imp_CONV = vREWR_CONV(vTAUT (parse_term "a \\/ b <=> ~b ==> a"))
    and push_CONV =
      vGEN_REWRITE_CONV vTOP_SWEEP_CONV
       [vTAUT (parse_term "~(a \\/ b) <=> ~a /\\ ~b"); vTAUT (parse_term "~(~a) <=> a")]
    and pull_CONV = vGEN_REWRITE_CONV vDEPTH_CONV
       [vTAUT (parse_term "~a \\/ ~b <=> ~(a /\\ b)")]
    and imf_CONV = vREWR_CONV(vTAUT (parse_term "~p <=> p ==> F")) in
    let memory = ref [] in
    let clear_contrapos_cache() = memory := [] in
    let make_hol_contrapos (n,th) =
      let tm = concl th in
      let key = (n,tm) in
      try assoc key (!memory) with Failure _ ->
      if n < 0 then
        vCONV_RULE (pull_CONV +---> imf_CONV) th
      else
        let djs = disjuncts tm in
        let acth =
          if n = 0 then th else
          let ldjs,rdjs = chop_list n djs in
          let ndjs = (hd rdjs)::(ldjs@(tl rdjs)) in
          vEQ_MP (vDISJ_AC(mk_eq(tm,list_mk_disj ndjs))) th in
        let fth =
          if length djs = 1 then acth
          else vCONV_RULE (imp_CONV +---> push_CONV) acth in
        (memory := (key,fth)::(!memory); fth) in
    clear_contrapos_cache,make_hol_contrapos

  (* ---------------------------------------------------------------------- *)
  (* Handle trivial start/finish stuff.                                     *)
  (* ---------------------------------------------------------------------- *)

  let finish_RULE =
      vGEN_REWRITE_RULE vI
       [vTAUT (parse_term "(~p ==> p) <=> p"); vTAUT (parse_term "(p ==> ~p) <=> ~p")]

  (* ----------------------------------------------------------------------- *)
  (* Translate back the saved proof into HOL.                                *)
  (* ----------------------------------------------------------------------- *)

  let meson_to_hol =
    let hol_negate tm =
      try dest_neg tm with Failure _ -> mk_neg tm in
    let merge_inst (t,x) current =
      (fol_subst current t,x)::current in
    let rec meson_to_hol insts (Subgoal(g,gs,(n,th),_offset,locin)) =
      let newins = itlist merge_inst locin insts in
      let g' = fol_inst newins g in
      let hol_g = hol_of_literal g' in
      let ths = map (meson_to_hol newins) gs in
      let hth =
        if equals_thm th vTRUTH then vASSUME hol_g else
        let cth = make_hol_contrapos(n,th) in
        if ths = [] then cth else vMATCH_MP cth (end_itlist vCONJ ths) in
      let ith = vPART_MATCH vI hth hol_g in
      finish_RULE (vDISCH (hol_negate(concl ith)) ith) in
    meson_to_hol

  (* ----------------------------------------------------------------------- *)
  (* Create equality axioms for all the function and predicate symbols in    *)
  (* a HOL term. Not very efficient (but then neither is throwing them into  *)
  (* automated proof search!)                                                *)
  (* ----------------------------------------------------------------------- *)

  let create_equality_axioms =
    let eq_thms = (vCONJUNCTS -| prove)
     ((parse_term "(x:A = x) /\\\n       (~(x:A = y) \\/ ~(x = z) \\/ (y = z))"),
      vREWRITE_TAC[] ----> vASM_CASES_TAC (parse_term "x:A = y") ---->
      vASM_REWRITE_TAC[] ----> vCONV_TAC vTAUT) in
    let imp_elim_CONV = vREWR_CONV
      (vTAUT (parse_term "(a ==> b) <=> ~a \\/ b")) in
    let eq_elim_RULE =
      vMATCH_MP(vTAUT (parse_term "(a <=> b) ==> b \\/ ~a")) in
    let veq_tm = rator(rator(concl(hd eq_thms))) in
    let create_equivalence_axioms (eq,_) =
      let tyins = type_match (type_of veq_tm) (type_of eq) [] in
      map (vINST_TYPE tyins) eq_thms in
    let rec tm_consts tm acc =
      let fn,args = strip_comb tm in
      if args = [] then acc
      else itlist tm_consts args (insert (fn,length args) acc) in
    let rec fm_consts tm ((preds,funs) as acc) =
      try fm_consts(snd(dest_forall tm)) acc with Failure _ ->
      try fm_consts(snd(dest_exists tm)) acc with Failure _ ->
      try let l,r = dest_conj tm in fm_consts l (fm_consts r acc)
      with Failure _ -> try
          let l,r = dest_disj tm in fm_consts l (fm_consts r acc)
      with Failure _ -> try
          let l,r = dest_imp tm in fm_consts l (fm_consts r acc)
      with Failure _ -> try
           fm_consts (dest_neg tm) acc with Failure _ ->
      try let l,r = dest_eq tm in
          if type_of l = bool_ty
          then fm_consts r (fm_consts l acc)
          else failwith "atomic equality"
      with Failure _ ->
      let pred,args = strip_comb tm in
      if args = [] then acc else
      insert (pred,length args) preds,itlist tm_consts args funs in
    let create_congruence_axiom pflag (tm,len) =
      let atys,_rty = splitlist (fun ty -> let op,l = dest_type ty in
                                          if op = "fun" then hd l,hd(tl l)
                                          else fail())
                               (type_of tm) in
      let ctys = fst(chop_list len atys) in
      let largs = map genvar ctys
      and rargs = map genvar ctys in
      let th1 = rev_itlist (vC (curry vMK_COMB)) (map (vASSUME -| mk_eq)
          (zip largs rargs)) (vREFL tm) in
      let th2 = if pflag then eq_elim_RULE th1 else th1 in
      itlist (fun e th -> vCONV_RULE imp_elim_CONV (vDISCH e th)) (hyp th2) th2 in
    fun tms -> let preds,funs = itlist fm_consts tms ([],[]) in
               let eqs0,noneqs = partition
                  (fun (t,_) -> is_const t && fst(dest_const t) = "=") preds in
               if eqs0 = [] then [] else
               let pcongs = map (create_congruence_axiom true) noneqs
               and fcongs = map (create_congruence_axiom false) funs in
               let preds1,_ =
                 itlist fm_consts (map concl (pcongs @ fcongs)) ([],[]) in
               let eqs1 = filter
                 (fun (t,_) -> is_const t && fst(dest_const t) = "=") preds1 in
               let eqs = union eqs0 eqs1 in
               let equivs =
                 itlist (union' equals_thm -| create_equivalence_axioms)
                        eqs [] in
               equivs@pcongs@fcongs

  (* ----------------------------------------------------------------------- *)
  (* Brand's transformation.                                                 *)
  (* ----------------------------------------------------------------------- *)

  let perform_brand_modification =
    let rec subterms_irrefl lconsts tm acc =
      if is_var tm || is_const tm then acc else
      let _fn,args = strip_comb tm in
      itlist (subterms_refl lconsts) args acc
    and subterms_refl lconsts tm acc =
      if is_var tm then if mem tm lconsts then insert tm acc else acc
      else if is_const tm then insert tm acc else
      let _fn,args = strip_comb tm in
      itlist (subterms_refl lconsts) args (insert tm acc) in
    let vCLAUSIFY = vCONV_RULE(vREWR_CONV(vTAUT (parse_term "a ==> b <=> ~a \\/ b"))) in
    let rec vBRAND tms th =
      if tms = [] then th else
      let tm = hd tms in
      let gv = genvar (type_of tm) in
      let eq = mk_eq(gv,tm) in
      let th' = vCLAUSIFY (vDISCH eq (vSUBS [vSYM (vASSUME eq)] th))
      and tms' = map (subst [gv,tm]) (tl tms) in
      vBRAND  tms' th' in
    let vBRAND_CONGS th =
      let lconsts = freesl (hyp th) in
      let lits = disjuncts (concl th) in
      let atoms = map (fun t -> try dest_neg t with Failure _ -> t) lits in
      let eqs,noneqs = partition
        (fun t -> try fst(dest_const(fst(strip_comb t))) = "="
                  with Failure _ -> false) atoms in
      let acc = itlist (subterms_irrefl lconsts) noneqs [] in
      let uts = itlist
        (itlist (subterms_irrefl lconsts) -| snd -| strip_comb) eqs acc in
      let sts = sort (fun s t -> not(free_in s t)) uts in
      vBRAND sts th in
    let vBRANDE th =
      let tm = concl th in
      let l,r = dest_eq tm in
      let gv = genvar(type_of l) in
      let eq = mk_eq(r,gv) in
      vCLAUSIFY(vDISCH eq (vEQ_MP (vAP_TERM (rator tm) (vASSUME eq)) th)) in
    let vLDISJ_CASES th lth rth =
      vDISJ_CASES th (vDISJ1 lth (concl rth)) (vDISJ2 (concl lth) rth) in
    let vASSOCIATE = vCONV_RULE(vREWR_CONV(vGSYM vDISJ_ASSOC)) in
    let rec vBRAND_TRANS th =
      let tm = concl th in
      try let l,r = dest_disj tm in
          if is_eq l then
            let lth = vASSUME l in
            let lth1 = vBRANDE lth
            and lth2 = vBRANDE (vSYM lth)
            and rth = vBRAND_TRANS (vASSUME r) in
            map (vASSOCIATE -| vLDISJ_CASES th lth1) rth @
            map (vASSOCIATE -| vLDISJ_CASES th lth2) rth
          else
            let rth = vBRAND_TRANS (vASSUME r) in
            map (vLDISJ_CASES th (vASSUME l)) rth
      with Failure _ ->
          if is_eq tm then [vBRANDE th; vBRANDE (vSYM th)]
          else [th] in
    let find_eqs =
      find_terms (fun t -> try fst(dest_const t) = "="
                           with Failure _ -> false) in
    let vREFLEXATE ths =
      let eqs = itlist (union -| find_eqs -| concl) ths [] in
      let tys = map (hd -| snd -| dest_type -| snd -| dest_const) eqs in
      let gvs = map genvar tys in
      itlist (fun v acc -> (vREFL v)::acc) gvs ths in
    fun ths ->
      if exists (can (find_term is_eq -| concl)) ths then
        let ths' = map vBRAND_CONGS ths in
        let ths'' = itlist (union' equals_thm -| vBRAND_TRANS) ths' [] in
        vREFLEXATE ths''
      else ths

  (* ----------------------------------------------------------------------- *)
  (* Push duplicated copies of poly theorems to match existing assumptions.  *)
  (* ----------------------------------------------------------------------- *)

  let vPOLY_ASSUME_TAC =
    let rec uniq' eq =
      fun l ->
        match l with
          x::(y::_ as t) -> let t' = uniq' eq t in
                              if eq x y then t' else
                              if t'==t then l else x::t'
        | _ -> l in
    let setify' le eq s = uniq' eq (sort le s) in
    let rec grab_constants tm acc =
      if is_forall tm || is_exists tm then grab_constants (body(rand tm)) acc
      else if is_iff tm || is_imp tm || is_conj tm || is_disj tm then
        grab_constants (rand tm) (grab_constants (lhand tm) acc)
      else if is_neg tm then grab_constants (rand tm) acc
      else union (find_terms is_const tm) acc in
    let match_consts (tm1,tm2) =
      let s1,ty1 = dest_const tm1
      and s2,ty2 = dest_const tm2 in
      if s1 = s2 then type_match ty1 ty2 []
      else failwith "match_consts" in
    let polymorph mconsts th =
      let tvs = subtract (type_vars_in_term (concl th))
                         (unions (map type_vars_in_term (hyp th))) in
      if tvs = [] then [th] else
      let pconsts = grab_constants (concl th) [] in
      let tyins = mapfilter match_consts
        (allpairs (fun x y -> x,y) pconsts mconsts) in
      let ths' =
        setify' (fun th th' -> dest_thm th <= dest_thm th')
                equals_thm (mapfilter (vC vINST_TYPE th) tyins) in
      if ths' = [] then
        (warn true "No useful-looking instantiations of lemma"; [th])
      else ths' in
    let rec polymorph_all mconsts ths acc =
      if ths = [] then acc else
      let ths' = polymorph mconsts (hd ths) in
      let mconsts' = itlist grab_constants (map concl ths') mconsts in
      polymorph_all mconsts' (tl ths) (union' equals_thm ths' acc) in
    fun ths (asl,_w as gl) ->
      let mconsts = itlist (grab_constants -| concl -| snd) asl [] in
      let ths' = polymorph_all mconsts ths [] in
      vMAP_EVERY vASSUME_TAC ths' gl

  (* ----------------------------------------------------------------------- *)
  (* Basic HOL MESON procedure.                                              *)
  (* ----------------------------------------------------------------------- *)

  let vSIMPLE_MESON_REFUTE min max inc ths =
    clear_contrapos_cache();
    inferences := 0;
    let old_dcutin = !meson_dcutin in
    if !meson_depth then meson_dcutin := 100001 else ();
    let ths' = if !meson_brand then perform_brand_modification ths
               else ths @ create_equality_axioms (map concl ths) in
    let rules = optimize_rules(fol_of_hol_clauses ths') in
    let proof,(insts,_,_) =
      solve_goal rules (!meson_depth) min max inc (1,[]) in
    meson_dcutin := old_dcutin;
    meson_to_hol insts proof

  let vCONJUNCTS_THEN' ttac cth =
    ttac(vCONJUNCT1 cth) ----> ttac(vCONJUNCT2 cth)

  let vPURE_MESON_TAC min max inc gl =
    reset_vars(); reset_consts();
    (vFIRST_ASSUM vCONTR_TAC |--->
     vW(vACCEPT_TAC -| vSIMPLE_MESON_REFUTE min max inc -| map snd -| fst)) gl

  let vQUANT_BOOL_CONV =
    vPURE_REWRITE_CONV[vFORALL_BOOL_THM; vEXISTS_BOOL_THM; vCOND_CLAUSES;
                      vNOT_CLAUSES; vIMP_CLAUSES; vAND_CLAUSES; vOR_CLAUSES;
                      vEQ_CLAUSES; vFORALL_SIMP; vEXISTS_SIMP]

  let rec vSPLIT_TAC n g =
    ((vFIRST_X_ASSUM(vCONJUNCTS_THEN' vASSUME_TAC) ----> vSPLIT_TAC n) |--->
     (if n > 0 then vFIRST_X_ASSUM vDISJ_CASES_TAC ----> vSPLIT_TAC (n - 1)
      else vNO_TAC) |--->
     vALL_TAC) g

end;;

(* ------------------------------------------------------------------------- *)
(* Basic MESON tactic with settable parameters.                              *)
(* ------------------------------------------------------------------------- *)

let vGEN_MESON_TAC min max step ths =
  vREFUTE_THEN vASSUME_TAC ---->
  Meson.vPOLY_ASSUME_TAC (map vGEN_ALL ths) ---->
  vW(vMAP_EVERY(vUNDISCH_TAC -| concl -| snd) -| fst) ---->
  vSELECT_ELIM_TAC ---->
  vW(fun (_asl,w) -> vMAP_EVERY (fun v -> vSPEC_TAC(v,v)) (frees w)) ---->
  vCONV_TAC(vPRESIMP_CONV +--->
           vTOP_DEPTH_CONV vBETA_CONV +--->
           vLAMBDA_ELIM_CONV +--->
           vCONDS_CELIM_CONV +--->
           Meson.vQUANT_BOOL_CONV) ---->
  vREPEAT(vGEN_TAC |---> vDISCH_TAC) ---->
  vREFUTE_THEN vASSUME_TAC ---->
  vRULE_ASSUM_TAC(vCONV_RULE(vNNF_CONV +---> vSKOLEM_CONV)) ---->
  vREPEAT (vFIRST_X_ASSUM vCHOOSE_TAC) ---->
  vASM_FOL_TAC ---->
  Meson.vSPLIT_TAC (!meson_split_limit) ---->
  vRULE_ASSUM_TAC(vCONV_RULE(vPRENEX_CONV +---> vWEAK_CNF_CONV)) ---->
  vRULE_ASSUM_TAC(repeat
   (fun th -> vSPEC(genvar(type_of(fst(dest_forall(concl th))))) th)) ---->
  vREPEAT (vFIRST_X_ASSUM (Meson.vCONJUNCTS_THEN' vASSUME_TAC)) ---->
  vRULE_ASSUM_TAC(vCONV_RULE(vASSOC_CONV vDISJ_ASSOC)) ---->
  vREPEAT (vFIRST_X_ASSUM vSUBST_VAR_TAC) ---->
  Meson.vPURE_MESON_TAC min max step;;

(* ------------------------------------------------------------------------- *)
(* Common cases.                                                             *)
(* ------------------------------------------------------------------------- *)

let vASM_MESON_TAC = vGEN_MESON_TAC 0 50 1;;

let vMESON_TAC ths = vPOP_ASSUM_LIST(vK vALL_TAC) ----> vASM_MESON_TAC ths;;

(* ------------------------------------------------------------------------- *)
(* Also introduce a rule.                                                  *)
(* ------------------------------------------------------------------------- *)

let vMESON ths tm = prove(tm,vMESON_TAC ths);;
