(* ========================================================================== *)
(*       Call-by-value reduction of terms similar to ML computation.          *)
(*                  Translated from HOL4 computeLib                           *)
(*                                                                            *)
(*                 (c) Copyright Alexey Solovyev 2018                         *)
(*                   (c) Copyright Bruno Barras 2000                          *)
(*                                                                            *)
(*        Distributed under the same license as HOL Light.                    *)
(* ========================================================================== *)

open Lib
open Fusion
open Basics
open Printer
open Parser
open Equal
open Bool
open Drule
open Tactics
open Simp
open Theorems
open Class
open Pair

module type Compute_sig = sig
  type compset

  val monitoring : (term -> bool) option ref
  val stoppers : (term -> bool) option ref

  val new_compset : thm list -> compset
  val bool_compset : unit -> compset

  val add_thms : thm list -> compset -> unit
  val add_conv : term * int * conv -> compset -> unit
  val set_skip : compset -> term -> int option -> unit

  val scrub_const : compset -> term -> unit
  val scrub_thms : thm list -> compset -> unit

  val lazyfy_thm : thm -> thm
  val strictify_thm : thm -> thm

  val vCBV_CONV : compset -> term -> thm
  val vWEAK_CBV_CONV : compset -> term -> thm

  val the_compset : compset
  val add_funs : thm list -> unit
  val add_convs : (term * int * conv) list -> unit

  val del_consts : term list -> unit
  val del_funs : thm list -> unit

  val vEVAL_CONV : conv
  val vEVAL_RULE : thm -> thm
  val vEVAL_TAC : tactic

  val vRESTR_EVAL_CONV : term list -> conv
  val vRESTR_EVAL_RULE : term list -> thm -> thm
  val vRESTR_EVAL_TAC : term list -> tactic

  val vOR : term list -> term -> bool

  type 'a fterm
  type db
  type transform = private Conversion of (term -> thm * db fterm) | Rrules of thm list

  val listItems : compset -> (string * transform list) list
end;;

module Compute : Compute_sig = struct

let with_flag (flag, b) f x =
  let fval = !flag in
  let () = flag := b in
  let res = try f x with e -> (flag := fval; raise e) in
  flag := fval; res;;

let vRIGHT_BETA th =
  try vTRANS th (vBETA_CONV (rhs (concl th)))
  with _ -> failwith "RIGHT_BETA";;

let vRIGHT_ETA thm =
  try vTRANS thm (vETA_CONV (rhs (concl thm)))
  with _ -> failwith "RIGHT_ETA";;

let vMK_comb th =
  let rator, rand = dest_comb (rhs (concl th)) in
  let mka th1 th2 = vTRANS th (vMK_COMB (th1, th2)) in
  (vREFL rator, vREFL rand, mka);;

let vMK_abs th =
  let bvar, body = dest_abs (rhs (concl th)) in
  (bvar, vREFL body, fun th1 -> vTRANS th (vABS bvar th1));;

let rec vBODY_CONJUNCTS th =
  if is_forall (concl th) then
    vBODY_CONJUNCTS (vSPEC_ALL th)
  else if is_conj (concl th) then
    vBODY_CONJUNCTS (vCONJUNCT1 th) @ vBODY_CONJUNCTS (vCONJUNCT2 th)
  else [th];;

(*** compute_rules.sml ***)

type ('a, 'b, 'c) stack =
    Ztop
  | Zrator of 'a * ('a, 'b, 'c) stack
  | Zrand of 'b * ('a, 'b, 'c) stack
  | Zabs of 'c * ('a, 'b, 'c) stack;;

exception Dead_code of string;;

let rhs_concl = rand -| concl;;
let refl_thm = vREFL;;
let trans_thm = vTRANS;;
let beta_thm = vRIGHT_BETA;;
let evaluate th = th;;

let try_eta thm = try vRIGHT_ETA thm with _ -> thm;;

(*---------------------------------------------------------------------------
 * Precondition: f(arg) is a closure corresponding to b.
 * Given   (arg,(|- M = (a b), Stk)),
 * returns (|- a = a, (<fun>,(|- b = b, f(arg)))::Stk)
 * where   <fun> =  (|- a = a' , |- b = b') |-> |- M = (a' b')
 *---------------------------------------------------------------------------*)

let push_in_stk f arg (th, stk) =
  let (tha, thb, mka) = vMK_comb th in
  (tha, Zrator ((mka, (thb, f arg)), stk));;

let push_skip_stk f arg (th, stk) =
  let (tha, thb, mka) = vMK_comb th in
  (tha, Zrand ((vC mka, true, (thb, f arg)), stk));;

let push_lam_in_stk (th, stk) =
  let (_, thb, mkl) = vMK_abs th in
  (thb, Zabs (try_eta -| mkl, stk));;

(*---------------------------------------------------------------------------
  Does conversions between
                              FUNIFY
    |- (c t_1 .. t_n x) = M    --->   |- (c t_1 .. t_n) = \x. M
                               <---
                             UNFUNIFY
   In UNFUNIFY, we must avoid choosing an x that appears free in t_1..t_n.
 ---------------------------------------------------------------------------*)

let vFUNIFY thm =
  try
    let x = rand (lhs (concl thm)) in
    vCONV_RULE (vRATOR_CONV (vRAND_CONV (vCHANGED_CONV (vPURE_REWRITE_CONV[vETA_AX])))) (vABS x thm)
  with _ -> failwith "FUNIFY";;

let vUNFUNIFY thm =
  try
    let lhs, rhs = dest_eq (concl thm) in
    let x = variant (frees lhs) (fst (dest_abs rhs)) in
    vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM thm x)
  with _ -> failwith "UNFUNIFY";;

let repeat_on_conj f thm =
  let rec iter th = try iter (f th) with _ -> th in
  end_itlist vCONJ (List.map iter (vBODY_CONJUNCTS thm));;

let lazyfy_thm = repeat_on_conj vFUNIFY;;
let strictify_thm = repeat_on_conj vUNFUNIFY;;

(* Ensures a theorem is an equality. *)
let eq_intro thm =
  if is_eq (concl thm) then thm else
  if is_neg (concl thm) then vEQF_INTRO thm
  else vEQT_INTRO thm;;

(*** clauses.sml ***)

(*---------------------------------------------------------------------------
 * Checking that a given thm is a reduction rule we can handle:
 *         (c p1...pn) = rhs
 * with p1...pn  either a const applied to patterns or a free variable.
 *---------------------------------------------------------------------------*)

type pattern =
    Pvar of int
  | Papp of term * pattern list;;

let check_arg_form trm =
  let rec chk t stk free =
    if is_comb t then
      let rator, rand = dest_comb t in
      let free', pat1 = chk rand [] free in
      chk rator (pat1 :: stk) free'
    else if is_var t then
      if stk = [] then
        let newi = List.length free in
        try (free, Pvar (newi - index t free - 1))
        with _ -> (t :: free, Pvar newi)
      else
        failwith ("check_arg_form: " ^ fst (dest_var t) ^ " occurs as a variable on lhs")
    else if is_const t then
      (free, Papp (t, List.rev stk))
    else
      failwith ("check_arg_form: lambda abstraction not allowed on lhs")
  in
  match chk trm [] [] with
    | (fv, Papp (head, args)) -> (List.rev fv, head, args)
    | _ -> failwith "check_arg_form: ill-formed lhs";;

(*---------------------------------------------------------------------------
 * CLOS denotes a delayed substitution (closure).
 * CST denotes an applied constant. Its first argument is the head constant;
 *   the second is the list of its arguments (we keep both the term and its
 *   abstract representation); the last one is the set of rewrites that
 *   still have a chance to be used, ie. those with a lhs wider than the
 *   number of applied args.
 * NEUTR is a slight improvement of CST with an empty list of rewrites, so
 *   that arguments of a variable are immediatly strongly reduced.
 *---------------------------------------------------------------------------*)

type 'a cst_rec = {
  head: term;
  args: (term * 'a fterm) list;
  rws: 'a;
  skip: int option
}
and 'a clos_rec = {
  env: 'a fterm list;
  term: 'a dterm
}
and 'a fterm =
    Const of 'a cst_rec
  | Neutr
  | Clos of 'a clos_rec

(*---------------------------------------------------------------------------
 * An alternative representation of terms, with all information needed:
 * - they are real de Bruijn terms, so that abstraction destruction is in
 *   constant time.
 * - application is n-ary (slight optimization)
 * - we forget the names of variables
 * - constants are tagged with the set of rewrites that apply to it.
 *   It's a reference since dterm is used to represent rhs of rewrites,
 *   and fixpoints equations add rewrites for a constant that appear in the
 *   rhs.
 *---------------------------------------------------------------------------*)

and 'a dterm =
    Bv of int
  | Fv
  | Cst of term * ('a * int option) ref
  | App of 'a dterm * 'a dterm list  (* order: outermost ahead *)
  | Abs of 'a dterm;;

(* Invariant: the first arg of App never is an App. *)

let appl = function
  | App (a, l1), arg -> App (a, arg :: l1)
  | t, arg -> App (t, [arg]);;

(*---------------------------------------------------------------------------
 * Type variable instantiation in dterm. Make it tail-recursive ?
 *---------------------------------------------------------------------------*)

let inst_type_dterm = function
  | [], v -> v
  | tysub, v ->
    let rec tyi_dt = function
      | Cst (c, dbsk) -> Cst (inst tysub c, dbsk)
      | App (h, l) -> App (tyi_dt h, map tyi_dt l)
      | Abs v -> Abs (tyi_dt v)
      | v -> v in
    tyi_dt v;;


type action =
    Rewrite of rewrite list
  | Conv of (term -> thm * db fterm)

and try_rec = {
  hcst: term;
  rws: action;
  tail: db
}

and db =
    End_db
  | Try of try_rec
  | Need_arg of db

and rewrite_rec = {
  cst: term;          (* constant which the rule applies to *)
  lhs: pattern list;  (* patterns = constant args in lhs of thm *)
  npv: int;           (* number of distinct pat vars in lhs *)
  rhs: db dterm;
  thm: thm            (* thm we use for rewriting *)
}

and rewrite =
    Rw of rewrite_rec;;

let rec add_in_db = function
  | (n, cst, act, End_db) ->
      funpow n (fun a -> Need_arg a) (Try { hcst = cst; rws = act; tail = End_db })
  | (0, cst, (Rewrite nrws as act), Try { hcst = hcst; rws = Rewrite rws as rw; tail = tail }) ->
    if cst = hcst then Try { hcst = hcst; rws = Rewrite (nrws @ rws); tail = tail }
    else Try { hcst = hcst; rws = rw; tail = add_in_db (0, cst, act, tail) }
  | (n, cst, act, Try { hcst = hcst; rws = rws; tail = tail }) ->
    Try { hcst = hcst; rws = rws; tail = add_in_db(n, cst, act, tail) }
  | (0, cst, act, db) ->
    Try { hcst = cst; rws = act; tail = db }
  | (n, cst, act, Need_arg tail) ->
    Need_arg (add_in_db(n - 1, cst, act, tail));;

let key_of (Rw {cst = cst; lhs = lhs; _}) =
  let name, _ = dest_const cst in
  (name, length lhs, cst);;

let is_skip = function
  | (_, Const {skip = Some n; args = args; _}) -> n <= List.length args
  | _ -> false;;

let partition_skip skip args =
  match skip with
  | Some n ->
    let len = List.length args in
    if n <= len then
      chop_list (len - n) args
    else
      ([], args)
  | None -> ([], args);;

(*---------------------------------------------------------------------------
 * equation database
 * We should try to factorize the rules (cf discrimination nets)
 * Rules are packed according to their head constant, and then sorted
 * according to the width of their lhs.
 *---------------------------------------------------------------------------*)

type compset =
    Rws of (string, (db * int option) ref) Hashtbl.t;;

let empty_rws () = Rws (Hashtbl.create 100);;

let assoc_clause (Rws rws) cst =
  try Hashtbl.find rws cst
  with Not_found ->
    let mt = ref (End_db, None) in
    Hashtbl.add rws cst mt;
    mt;;

let add_in_db_upd rws (name, arity, hcst) act =
  let { contents = db, sk } as rl = assoc_clause rws name in
  rl := add_in_db (arity, hcst, act, db), sk;;

let set_skip_name (Rws _htbl as rws) p sk =
  let { contents = db, _ } as rl = assoc_clause rws p in
  rl := db, sk;;

let scrub_const (Rws htbl) c =
  let name, _ = dest_const c in
  Hashtbl.remove htbl name;;

let from_term (rws, env, t) =
  let rec down (env, t, c) =
    match t with
    | Var _ -> up ((try Bv (index t env) with _ -> Fv), c)
    | Const (name, _) -> up (Cst (t, assoc_clause rws name), c)
    | Comb (rator, rand) -> down (env, rator, Zrator ((env, rand), c))
    | Abs (bvar, body) -> down (bvar :: env, body, Zabs ((), c))

  and up = function
    | dt, Ztop -> dt
    | dt, Zrator ((env, arg), c) -> down (env, arg, Zrand(dt, c))
    | dt, Zrand (dr, c) -> up (appl (dr, dt), c)
    | dt, Zabs (_, c) -> up (Abs dt, c)
  in
  down (env, t, Ztop);;

(*---------------------------------------------------------------------------
 * Note: if the list of free variables of the lhs was empty, we could
 * evaluate (weak reduction) the rhs now. This implies that the
 * theorems must be added in dependencies order.
 *---------------------------------------------------------------------------*)

let mk_rewrite rws eq_thm =
  let lhs, rhs = dest_eq (concl eq_thm) in
  let fv, cst, pats = check_arg_form lhs in
  let gen_thm = itlist vGEN fv eq_thm in
  let rhsc = from_term (rws, rev fv, rhs) in
  Rw {
    cst = cst;
    lhs = pats;
    rhs = rhsc;
    npv = length fv;
    thm = gen_thm
  };;

let unsuitable th =
  let l, r = dest_eq (concl th) in
  can (term_match [] l) r;;

let enter_thm rws thm0 =
  let thm = eq_intro thm0 in
  if unsuitable thm then ()
  else
    let rw = mk_rewrite rws thm in
    add_in_db_upd rws (key_of rw) (Rewrite [rw]);;

let add_thms lthm rws =
  List.iter (List.iter (enter_thm rws) -| vBODY_CONJUNCTS) lthm;;

let add_extern (cst, arity, fconv) rws =
  let name, _ = dest_const cst in
  add_in_db_upd rws (name, arity, cst) (Conv fconv);;

let new_rws () =
  let rws = empty_rws () in
  add_thms [vREFL_CLAUSE] rws;
  rws;;

let from_list lthm =
  let rws = new_rws() in
  add_thms lthm rws;
  rws;;

let scrub_thms lthm rws =
  let tmlist = map (concl -| hd -| vBODY_CONJUNCTS) lthm in
  let clist = map (fst -| strip_comb -| lhs -| snd -| strip_forall) tmlist in
  List.iter (scrub_const rws) clist;;


(*---------------------------------------------------------------------------*)
(* Support for analysis of compsets                                          *)
(*---------------------------------------------------------------------------*)

let _rws_of (Rws htbl) =
  let dblist = Hashtbl.fold (fun _ {contents = (db, _)} r -> db :: r) htbl [] in
  let rec get_actions db =
    match db with
    | End_db -> []
    | Need_arg db' -> get_actions db'
    | Try {hcst = hcst; rws = rws; tail = tail} ->
      (hcst, rws) :: get_actions tail in
  let actionlist = List.concat (List.map get_actions dblist) in
  let dest (Rw {thm = thm; _}) = thm in
  let dest_action = function
    | hcst, Rewrite rws -> (hcst, map dest rws)
    | hcst, Conv _ -> (hcst, []) in
  let rwlist = List.map dest_action actionlist in
  rwlist;;

type transform =
    Conversion of (term -> thm * db fterm)
  | Rrules of thm list;;

(*---------------------------------------------------------------------------*)
(* Compute the "attachments" for each element of the compset. Fortunately,   *)
(* it seems that the insertion of an attachment into a compset also makes    *)
(* insertions for the constants mentioned in the rhs of the rewrite.         *)
(* Otherwise, one would have to do a transitive closure sort of construction *)
(* to make all the dependencies explicit.                                    *)
(*---------------------------------------------------------------------------*)

let deplist (Rws htbl) =
  let dblist = Hashtbl.fold (fun s {contents = (db, _)} r -> (s, db) :: r) htbl [] in
  let rec get_actions db =
    match db with
    | End_db -> []
    | Need_arg db' -> get_actions db'
    | Try {hcst = _hcst; rws = rws; tail = tail} ->
      rws :: get_actions tail in
  let actionlist = List.map (fun (s, db) -> s, get_actions db) dblist in
  let dest (Rw {thm = thm; _}) = thm in
  let dest_action = function
    | Rewrite rws -> Rrules (map dest rws)
    | Conv ecnv -> Conversion ecnv in
  let rwlist = List.map (fun (s, act) -> s, map dest_action act) actionlist in
  rwlist;;


(*** equations.sml ***)

(*---------------------------------------------------------------------------
 * The First order matching functions.
 *
 * We do not consider general non-linear patterns. We could try (requires a
 * more elaborate conversion algorithm, and it makes matching and reduction
 * mutually dependent).
 *---------------------------------------------------------------------------*)
exception No_match;;

let match_const (bds, tbds) pc c =
  let name, ty = dest_const pc in
  let name', ty' = dest_const c in
  if name = name' then
    try bds, type_match ty ty' tbds with _ -> raise No_match
  else raise No_match;;

(*---------------------------------------------------------------------------
 * Match pattern variable number var with term arg.
 * We do not need to match types, because pattern variables appear as argument
 * of a constant which has already been matched succesfully.
 *---------------------------------------------------------------------------*)

let match_var (bds, tbds) var arg =
  let _ = match bds.(var) with
  | Some (tm, _) -> if aconv tm (fst arg) then () else raise No_match
  | None -> bds.(var) <- Some arg in
  (bds, tbds);;

(*---------------------------------------------------------------------------
 * Tries to match a list of pattern to a list of arguments.
 * We assume that we already checked the lengths (probably a good short-cut)
 *
 * Returns a list of bindings that extend the ones given as
 * argument (bds), or a No_match exception.
 *---------------------------------------------------------------------------*)

let rec match_list bds pats args =
  match (pats, args) with
    | pat :: pats, arg :: args ->
      match_list (match_solve bds pat arg) pats args
    | [], [] -> bds
    | _ -> raise (Dead_code "match_list")

and match_solve bds pat arg =
  match (pat, arg) with
  | Pvar var, arg -> match_var bds var arg
  | Papp (phead, pargs), (_, Const {head = head; args = args; _}) ->
    if length pargs = length args then
      match_list (match_const bds phead head) pargs args
    else
      raise No_match
  | _ -> raise No_match;;

(*---------------------------------------------------------------------------
 * Try a sequence of rewrite rules. No attempt to factorize patterns!
 *---------------------------------------------------------------------------*)

type 'a rule_inst = {
  rule: rewrite;
  inst: (term * 'a fterm) option array * (hol_type * hol_type) list
};;

let try_rwn ibds lt =
  let rec try_rec = function
    | [] -> raise No_match
    | (Rw {lhs = lhs; npv = npv; _} as rw) :: rwn ->
      let env = Array.make npv None in
      try { rule = rw; inst = match_list (env, ibds) lhs lt }
      with No_match -> try_rec rwn
  in
  try_rec;;

(*---------------------------------------------------------------------------
 * Instantiating the rule according to the output of the matching.
 *---------------------------------------------------------------------------*)

let comb_ct cst arg =
  match cst with
  | { head = head; args = args; rws = Need_arg tail; skip = skip } ->
    Const { head = head; args = arg :: args; rws = tail; skip = skip }
  | { head = head; args = args; rws = End_db; skip = skip } ->
    Const { head = head; args = arg :: args; rws = End_db; skip = skip }
  | { rws = Try _ ; _} ->
    raise (Dead_code "comb_ct: yet rules to try");;

let mk_clos (env, t) =
  match t with
  | Cst (hc, { contents = (db, b) }) -> Const {head = hc; args = []; rws = db; skip = b}
  | Bv i -> List.nth env i
  | Fv -> Neutr
  | _ -> Clos {env = env; term = t};;

(*---------------------------------------------------------------------------
 * It is probably this code that can be improved the most
 *---------------------------------------------------------------------------*)

let inst_one_var (thm, lv) = function
  | Some (tm, v) -> vSPEC tm thm, v :: lv
  | None -> raise (Dead_code "inst_rw");;

let inst_rw (th, monitoring, {rule = Rw {thm = thm; rhs = rhs; _}; inst = (bds, tysub)}) =
  let tirhs = inst_type_dterm (tysub, rhs) in
  let tithm = vINST_TYPE tysub thm in
  let spec_thm, venv = Array.fold_left inst_one_var (tithm, []) bds in
  let () = if monitoring then print_term (concl spec_thm) in
  trans_thm th spec_thm, mk_clos (venv, tirhs);;

let monitoring = ref (None: (term -> bool) option);;
let stoppers = ref (None: (term -> bool) option);;

(*---------------------------------------------------------------------------
 * Reducing a constant
 *---------------------------------------------------------------------------*)

let rec reduce_cst = function
  | th, {head = head; args = args; rws = Try {hcst = hcst; rws = Rewrite rls; tail = tail}; skip = skip} ->
   (try
      let () = match !stoppers with None -> () | Some p -> if p head then raise No_match else () in
      let _, _, tytheta = try term_match [] hcst head with _ -> raise No_match in
      let rule_inst = try_rwn tytheta args rls in
      let mon = match !monitoring with None -> false | Some f -> f head in
      let insted = inst_rw (th, mon, rule_inst) in
        (true, insted)
    with No_match ->
      reduce_cst (th, {head = head; args = args; rws = tail; skip = skip}))
  | th, {head = head; args = args; rws = Try {hcst = _hcst; rws = Conv fconv; tail = tail}; skip = skip} ->
   (try
      let thm, ft = fconv (rhs_concl th) in
        (true, (trans_thm th thm, ft))
    with _ ->
      reduce_cst (th, {head = head; args = args; rws = tail; skip = skip}))
  | th, cst -> (false, (th, Const cst));;


(*** computeLib.sml ***)

let _auto_import_definitions = ref true;;

(* re-exporting types from clauses *)

let new_compset = from_list;;
let listItems = deplist;;

type cbv_stack =
  ((thm->thm->thm) * (thm * db fterm),
   (thm->thm->thm) * bool * (thm * db fterm),
   (thm->thm)) stack;;

let rec stack_out = function
  | th, Ztop -> th
  | th, Zrator ((mka, (thb, _)), ctx) -> stack_out (mka th thb, ctx)
  | th, Zrand ((mka, _, (tha, _)), ctx) -> stack_out (mka tha th, ctx)
  | th, Zabs (mkl, ctx) -> stack_out (mkl th, ctx);;

let initial_state rws t =
  ((refl_thm t, mk_clos ([], from_term (rws, [], t))), (Ztop: cbv_stack));;

(*---------------------------------------------------------------------------
 * [cbv_wk (rws,(th,cl),stk)] puts the closure cl (useful information about
 * the rhs of th) in head normal form (weak reduction). It returns either
 * a closure which term is an abstraction, in a context other than Zappl,
 * a variable applied to strongly reduced arguments, or a constant
 * applied to weakly reduced arguments which does not match any rewriting
 * rule.
 *
 * - substitution is propagated through applications.
 * - if the rhs is an abstraction and there is one arg on the stack,
 *   this means we found a beta redex. mka rebuilds the application of
 *   the function to its argument, and Beta does the actual beta step.
 * - for an applied constant, we look for a rewrite matching it.
 *   If we found one, then we apply the instantiated rule, and go on.
 *   Otherwise, we try to rebuild the thm.
 * - for an already strongly normalized term or an unapplied abstraction,
 *   we try to rebuild the thm.
 *---------------------------------------------------------------------------*)

let rec cbv_wk = function
  | (th, Clos {env = env; term = App (a, args)}), stk ->
    let tha, stka = rev_itlist (push_in_stk (curry mk_clos env)) args (th, stk) in
    cbv_wk ((tha, mk_clos (env, a)), stka)
  | (th, Clos {env = env; term = Abs body}), Zrator ((mka, (thb, cl)), s') ->
    cbv_wk ((beta_thm (mka th thb), mk_clos (cl :: env, body)), s')
  | (th, Const cargs), stk ->
    let reduced, clos = reduce_cst (th, cargs) in
    if reduced then cbv_wk (clos, stk) else cbv_up (clos, stk)
  | clos, stk -> cbv_up (clos, stk)

(*---------------------------------------------------------------------------
 * Tries to rebuild the thm, knowing that the closure has been weakly
 * normalized, until it finds term still to reduce, or if a strong reduction
 * may be required.
 *  - if we are done with a Rator, we start reducing the Rand
 *  - if we are done with the Rand of a const, we rebuild the application
 *    and look if it created a redex
 *  - an application to a NEUTR can be rebuilt only if the argument has been
 *    strongly reduced, which we now for sure only if itself is a NEUTR.
 *---------------------------------------------------------------------------*)

and cbv_up = function
  | hcl, Zrator ((mka, clos), ctx) ->
    let new_state = clos, Zrand ((mka, false, hcl), ctx) in
    if is_skip hcl then cbv_up new_state else cbv_wk new_state
  | (thb, v), Zrand ((mka, false, (th, Const cargs)), stk) ->
    cbv_wk ((mka th thb, comb_ct cargs (rhs_concl thb, v)), stk)
  | (thb, Neutr), Zrand ((mka, false, (th, Neutr)), stk) ->
    cbv_up ((mka th thb, Neutr), stk)
  | clos, stk -> clos, stk;;

(*---------------------------------------------------------------------------
 * [strong] continues the reduction of a term in head normal form under
 * abstractions, and in the arguments of non reduced constant.
 * precondition: the closure should be the output of cbv_wk
 *---------------------------------------------------------------------------*)

let rec strong = function
  | (th, Clos {env = env; term = Abs t}), stk ->
    let thb, stk' = push_lam_in_stk (th, stk) in
    strong (cbv_wk ((thb, mk_clos (Neutr :: env, t)), stk'))
  | (_, Clos _), _stk ->
    raise (Dead_code "strong")
  | (th, Const {skip = skip; args = args; _}), stk ->
    let argssk, argsrd = partition_skip skip args in
    let th', stk' = rev_itlist (push_skip_stk snd) argssk (th, stk) in
    let th'', stk'' = rev_itlist (push_in_stk snd) argsrd (th', stk') in
    strong_up (th'', stk'')
  | (th, Neutr), stk -> strong_up (th, stk)

and strong_up = function
  | th, Ztop -> th
  | th, Zrand ((mka, false, (tha, Neutr)), ctx) ->
    strong (cbv_wk ((mka tha th, Neutr), ctx))
  | _th, Zrand ((_mka, false, _clos), _ctx) ->
    raise (Dead_code "strong_up")
  | th, Zrator ((mka, clos), ctx) ->
    strong (cbv_wk (clos, Zrand ((mka, true, (th, Neutr)), ctx)))
  | th, Zrand ((mka, true, (tha, _)), ctx) ->
    strong_up (mka tha th, ctx)
  | th, Zabs (mkl, ctx) ->
    strong_up (mkl th, ctx);;

(*---------------------------------------------------------------------------
 * [CBV_CONV rws t] is a conversion that does the full normalization of t,
 * using rewrites rws.
 *---------------------------------------------------------------------------*)

let vCBV_CONV rws = evaluate -| strong -| cbv_wk -| initial_state rws;;

(*---------------------------------------------------------------------------
 * WEAK_CBV_CONV is the same as CBV_CONV except that it does not reduce
 * under abstractions, and reduce weakly the arguments of constants.
 * Reduction whenever we reach a state where a strong reduction is needed.
 *---------------------------------------------------------------------------*)

let vWEAK_CBV_CONV rws =
  evaluate
  -| (fun ((th, _), stk) -> stack_out (th, stk))
  -| cbv_wk
  -| initial_state rws;;

(*---------------------------------------------------------------------------
 * Adding an arbitrary conv
 *---------------------------------------------------------------------------*)

let extern_of_conv rws conv tm =
  let thm = conv tm in
  thm, mk_clos ([], from_term (rws, [], rhs (concl thm)));;

let add_conv (cst, arity, conv) rws =
  add_extern (cst, arity, extern_of_conv rws conv) rws;;

let set_skip compset c opt =
  try
    let name, _ = dest_const c in
    set_skip_name compset name opt
  with _ -> failwith "set_skip";;


(*---------------------------------------------------------------------------
       Support for a global compset.
 ---------------------------------------------------------------------------*)

let bool_redns =
  strictify_thm vLET_DEF
  :: List.map lazyfy_thm
    [vCOND_CLAUSES; vCOND_ID; vNOT_CLAUSES;
     vAND_CLAUSES; vOR_CLAUSES; vIMP_CLAUSES; vEQ_CLAUSES];;

let bool_compset () =
  let base = from_list bool_redns in
  let () = set_skip base (parse_term "COND: bool -> A -> A -> A") None in
          (* change last parameter to SOME 1 to stop CBV_CONV looking at
             conditionals' branches before the guard is fully true or false *)
  base;;

let the_compset = bool_compset();;

let add_funs = vC add_thms the_compset;;
let add_convs = List.iter (vC add_conv the_compset);;

let del_consts = List.iter (scrub_const the_compset);;
let del_funs = vC scrub_thms the_compset;;

let vEVAL_CONV = vCBV_CONV the_compset;;
let vEVAL_RULE = vCONV_RULE vEVAL_CONV;;
let vEVAL_TAC = vCONV_TAC vEVAL_CONV;;

let same_const c1 c2 = fst (dest_const c1) = fst (dest_const c2);;

let rec vOR = function
  | [] -> vK false
  | [x] -> same_const x
  | h :: t -> fun x -> same_const h x || vOR t x;;

let vRESTR_EVAL_CONV clist =
  with_flag (stoppers, Some (vOR clist)) vEVAL_CONV;;

let vRESTR_EVAL_TAC = vCONV_TAC -| vRESTR_EVAL_CONV;;
let vRESTR_EVAL_RULE = vCONV_RULE -| vRESTR_EVAL_CONV;;

end;;
