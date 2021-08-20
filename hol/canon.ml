(* ========================================================================= *)
(* Reasonably efficient conversions for various canonical forms.             *)
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
open Ind_defs
open Class
open Trivia

(* ------------------------------------------------------------------------- *)
(* Pre-simplification.                                                       *)
(* ------------------------------------------------------------------------- *)

let vPRESIMP_CONV =
  vGEN_REWRITE_CONV vTOP_DEPTH_CONV
   [vNOT_CLAUSES; vAND_CLAUSES; vOR_CLAUSES; vIMP_CLAUSES; vEQ_CLAUSES;
    vFORALL_SIMP; vEXISTS_SIMP; vEXISTS_OR_THM; vFORALL_AND_THM;
    vLEFT_EXISTS_AND_THM; vRIGHT_EXISTS_AND_THM;
    vLEFT_FORALL_OR_THM; vRIGHT_FORALL_OR_THM];;

(* ------------------------------------------------------------------------- *)
(* ACI rearrangements of conjunctions and disjunctions. This is much faster  *)
(* than AC xxx_ACI on large problems, as well as being more controlled.      *)
(* ------------------------------------------------------------------------- *)

let vCONJ_ACI_RULE =
  let rec mk_fun th fn =
    let tm = concl th in
    if is_conj tm then
      let th1,th2 = vCONJ_PAIR th in
      mk_fun th1 (mk_fun th2 fn)
    else (tm |-> th) fn
  and use_fun fn tm =
    if is_conj tm then
      let l,r = dest_conj tm in vCONJ (use_fun fn l) (use_fun fn r)
    else apply fn tm in
  fun fm ->
    let p,p' = dest_eq fm in
    if p = p' then vREFL p else
    let th = use_fun (mk_fun (vASSUME p) undefined) p'
    and th' = use_fun (mk_fun (vASSUME p') undefined) p in
    vIMP_ANTISYM_RULE (vDISCH_ALL th) (vDISCH_ALL th');;

let vDISJ_ACI_RULE =
  let pth_left = vUNDISCH(vTAUT (parse_term "~(a \\/ b) ==> ~a"))
  and pth_right = vUNDISCH(vTAUT (parse_term "~(a \\/ b) ==> ~b"))
  and pth = repeat vUNDISCH (vTAUT (parse_term "~a ==> ~b ==> ~(a \\/ b)"))
  and pth_neg = vUNDISCH(vTAUT (parse_term "(~a <=> ~b) ==> (a <=> b)"))
  and a_tm = (parse_term "a:bool") and b_tm = (parse_term "b:bool") in
  let vNOT_DISJ_PAIR th =
    let p,q = dest_disj(rand(concl th)) in
    let ilist = [p,a_tm; q,b_tm] in
    vPROVE_HYP th (vINST ilist pth_left),
    vPROVE_HYP th (vINST ilist pth_right)
  and vNOT_DISJ th1 th2 =
    let th3 = vINST [rand(concl th1),a_tm; rand(concl th2),b_tm] pth in
    vPROVE_HYP th1 (vPROVE_HYP th2 th3) in
  let rec mk_fun th fn =
    let tm = rand(concl th) in
    if is_disj tm then
      let th1,th2 = vNOT_DISJ_PAIR th in
      mk_fun th1 (mk_fun th2 fn)
    else (tm |-> th) fn
  and use_fun fn tm =
    if is_disj tm then
      let l,r = dest_disj tm in vNOT_DISJ (use_fun fn l) (use_fun fn r)
    else apply fn tm in
  fun fm ->
    let p,p' = dest_eq fm in
    if p = p' then vREFL p else
    let th = use_fun (mk_fun (vASSUME(mk_neg p)) undefined) p'
    and th' = use_fun (mk_fun (vASSUME(mk_neg p')) undefined) p in
    let th1 = vIMP_ANTISYM_RULE (vDISCH_ALL th) (vDISCH_ALL th') in
    vPROVE_HYP th1 (vINST [p,a_tm; p',b_tm] pth_neg);;

(* ------------------------------------------------------------------------- *)
(* Order canonically, right-associate and remove duplicates.                 *)
(* ------------------------------------------------------------------------- *)

let vCONJ_CANON_CONV tm =
  let tm' = list_mk_conj(setify(conjuncts tm)) in
  vCONJ_ACI_RULE(mk_eq(tm,tm'));;

let vDISJ_CANON_CONV tm =
  let tm' = list_mk_disj(setify(disjuncts tm)) in
  vDISJ_ACI_RULE(mk_eq(tm,tm'));;

(* ------------------------------------------------------------------------- *)
(* General NNF conversion. The user supplies some conversion to be applied   *)
(* to atomic formulas.                                                       *)
(*                                                                           *)
(* "Iff"s are split conjunctively or disjunctively according to the flag     *)
(* argument (conjuctively = true) until a universal quantifier (modulo       *)
(* current parity) is passed; after that they are split conjunctively. This  *)
(* is appropriate when the result is passed to a disjunctive splitter        *)
(* followed by a clausal form inner core, such as MESON.                     *)
(*                                                                           *)
(* To avoid some duplicate computation, this function will in general        *)
(* enter a recursion where it simultaneously computes NNF representations    *)
(* for "p" and "~p", so the user needs to supply an atomic "conversion"      *)
(* that does the same.                                                       *)
(* ------------------------------------------------------------------------- *)

let (vGEN_NNF_CONV:bool->conv*(term->thm*thm)->conv) =
  let and_tm = (parse_term "(/\\)") and or_tm = (parse_term "(\\/)") and not_tm = (parse_term "(~)")
  and pth_not_not = vTAUT (parse_term "~ ~ p = p")
  and pth_not_and = vTAUT (parse_term "~(p /\\ q) <=> ~p \\/ ~q")
  and pth_not_or = vTAUT (parse_term "~(p \\/ q) <=> ~p /\\ ~q")
  and pth_imp = vTAUT (parse_term "p ==> q <=> ~p \\/ q")
  and pth_not_imp = vTAUT (parse_term "~(p ==> q) <=> p /\\ ~q")
  and pth_eq = vTAUT (parse_term "(p <=> q) <=> p /\\ q \\/ ~p /\\ ~q")
  and pth_not_eq = vTAUT (parse_term "~(p <=> q) <=> p /\\ ~q \\/ ~p /\\ q")
  and pth_eq' = vTAUT (parse_term "(p <=> q) <=> (p \\/ ~q) /\\ (~p \\/ q)")
  and pth_not_eq' = vTAUT (parse_term "~(p <=> q) <=> (p \\/ q) /\\ (~p \\/ ~q)")
  and pth_not_forall, pth_not_exists, pth_not_exu = match
   (vCONJUNCTS -| prove)
   ((parse_term "(~((!) P) <=> ?x:A. ~(P x)) /\\\n     (~((?) P) <=> !x:A. ~(P x)) /\\\n     (~((?!) P) <=> (!x:A. ~(P x)) \\/ ?x y. P x /\\ P y /\\ ~(y = x))"),
    vREPEAT vCONJ_TAC ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| funpow 2 vRAND_CONV) [vGSYM vETA_AX] ---->
    vREWRITE_TAC[vNOT_EXISTS_THM; vNOT_FORALL_THM; vEXISTS_UNIQUE_DEF;
                vDE_MORGAN_THM; vNOT_IMP] ---->
    vREWRITE_TAC[vCONJ_ASSOC; vEQ_SYM_EQ])
  with [a;b;c] -> a,b,c | _ -> assert false
  and pth_exu = prove
   ((parse_term "((?!) P) <=> (?x:A. P x) /\\ !x y. ~(P x) \\/ ~(P y) \\/ (y = x)"),
    vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vETA_AX] ---->
    vREWRITE_TAC[vEXISTS_UNIQUE_DEF; vTAUT (parse_term "a /\\ b ==> c <=> ~a \\/ ~b \\/ c")] ---->
    vREWRITE_TAC[vEQ_SYM_EQ])
  and p_tm = (parse_term "p:bool") and q_tm = (parse_term "q:bool") in
  let rec vNNF_DCONV cf baseconvs tm =
    match tm with
      Comb(Comb(Const("/\\",_),l),r) ->
          let th_lp,th_ln = vNNF_DCONV cf baseconvs l
          and th_rp,th_rn = vNNF_DCONV cf baseconvs r in
          vMK_COMB(vAP_TERM and_tm th_lp,th_rp),
          vTRANS (vINST [l,p_tm; r,q_tm] pth_not_and)
                (vMK_COMB(vAP_TERM or_tm th_ln,th_rn))
    | Comb(Comb(Const("\\/",_),l),r) ->
          let th_lp,th_ln = vNNF_DCONV cf baseconvs l
          and th_rp,th_rn = vNNF_DCONV cf baseconvs r in
          vMK_COMB(vAP_TERM or_tm th_lp,th_rp),
          vTRANS (vINST [l,p_tm; r,q_tm] pth_not_or)
                (vMK_COMB(vAP_TERM and_tm th_ln,th_rn))
    | Comb(Comb(Const("==>",_),l),r) ->
          let th_lp,th_ln = vNNF_DCONV cf baseconvs l
          and th_rp,th_rn = vNNF_DCONV cf baseconvs r in
          vTRANS (vINST [l,p_tm; r,q_tm] pth_imp)
                (vMK_COMB(vAP_TERM or_tm th_ln,th_rp)),
          vTRANS (vINST [l,p_tm; r,q_tm] pth_not_imp)
                (vMK_COMB(vAP_TERM and_tm th_lp,th_rn))
    | Comb(Comb(Const("=",Tyapp("fun",Tyapp("bool",_)::_)),l),r) ->
          let th_lp,th_ln = vNNF_DCONV cf baseconvs l
          and th_rp,th_rn = vNNF_DCONV cf baseconvs r in
          if cf then
            vTRANS (vINST [l,p_tm; r,q_tm] pth_eq')
                  (vMK_COMB(vAP_TERM and_tm (vMK_COMB(vAP_TERM or_tm th_lp,th_rn)),
                           vMK_COMB(vAP_TERM or_tm th_ln,th_rp))),
            vTRANS (vINST [l,p_tm; r,q_tm] pth_not_eq')
                  (vMK_COMB(vAP_TERM and_tm (vMK_COMB(vAP_TERM or_tm th_lp,th_rp)),
                           vMK_COMB(vAP_TERM or_tm th_ln,th_rn)))
          else
            vTRANS (vINST [l,p_tm; r,q_tm] pth_eq)
                  (vMK_COMB(vAP_TERM or_tm (vMK_COMB(vAP_TERM and_tm th_lp,th_rp)),
                           vMK_COMB(vAP_TERM and_tm th_ln,th_rn))),
            vTRANS (vINST [l,p_tm; r,q_tm] pth_not_eq)
                  (vMK_COMB(vAP_TERM or_tm (vMK_COMB(vAP_TERM and_tm th_lp,th_rn)),
                           vMK_COMB(vAP_TERM and_tm th_ln,th_rp)))
    | Comb(Const("!",Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t) as bod)) ->
          let th_p,th_n = vNNF_DCONV true baseconvs t in
          vAP_TERM q (vABS x th_p),
          let th1 = vINST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (vINST_TYPE [ty,aty] pth_not_forall)
          and th2 = vTRANS (vAP_TERM not_tm (vBETA(mk_comb(bod,x)))) th_n in
          vTRANS th1 (vMK_EXISTS x th2)
    | Comb(Const("?",Tyapp("fun",Tyapp("fun",ty::_)::_)) as q,
           (Abs(x,t) as bod)) ->
          let th_p,th_n = vNNF_DCONV cf baseconvs t in
          vAP_TERM q (vABS x th_p),
          let th1 = vINST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (vINST_TYPE [ty,aty] pth_not_exists)
          and th2 = vTRANS (vAP_TERM not_tm (vBETA(mk_comb(bod,x)))) th_n in
          vTRANS th1 (vMK_FORALL x th2)
    | Comb(Const("?!",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let y = variant (x::frees t) x
          and th_p,th_n = vNNF_DCONV cf baseconvs t in
          let eq = mk_eq(y,x) in
          let eth_p,eth_n = baseconvs eq
          and bth = vBETA (mk_comb(bod,x))
          and bth' = vBETA_CONV(mk_comb(bod,y)) in
          let th_p' = vINST [y,x] th_p and th_n' = vINST [y,x] th_n in
          let th1 = vINST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (vINST_TYPE [ty,aty] pth_exu)
          and th1' = vINST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                          (vINST_TYPE [ty,aty] pth_not_exu)
          and th2 =
            vMK_COMB(vAP_TERM and_tm
                        (vMK_EXISTS x (vTRANS bth th_p)),
                    vMK_FORALL x (vMK_FORALL y
                     (vMK_COMB(vAP_TERM or_tm (vTRANS (vAP_TERM not_tm bth) th_n),
                              vMK_COMB(vAP_TERM or_tm
                                    (vTRANS (vAP_TERM not_tm bth') th_n'),
                                      eth_p)))))
          and th2' =
            vMK_COMB(vAP_TERM or_tm
                        (vMK_FORALL x (vTRANS (vAP_TERM not_tm bth) th_n)),
                    vMK_EXISTS x (vMK_EXISTS y
                     (vMK_COMB(vAP_TERM and_tm (vTRANS bth th_p),
                              vMK_COMB(vAP_TERM and_tm (vTRANS bth' th_p'),
                                      eth_n))))) in
          vTRANS th1 th2,vTRANS th1' th2'
    | Comb(Const("~",_),t) ->
          let th1,th2 = vNNF_DCONV cf baseconvs t in
          th2,vTRANS (vINST [t,p_tm] pth_not_not) th1
    | _ -> try baseconvs tm
           with Failure _ -> vREFL tm,vREFL(mk_neg tm) in
  let rec vNNF_CONV cf (base1,base2 as baseconvs) tm =
    match tm with
      Comb(Comb(Const("/\\",_),l),r) ->
          let th_lp = vNNF_CONV cf baseconvs l
          and th_rp = vNNF_CONV cf baseconvs r in
          vMK_COMB(vAP_TERM and_tm th_lp,th_rp)
    | Comb(Comb(Const("\\/",_),l),r) ->
          let th_lp = vNNF_CONV cf baseconvs l
          and th_rp = vNNF_CONV cf baseconvs r in
          vMK_COMB(vAP_TERM or_tm th_lp,th_rp)
    | Comb(Comb(Const("==>",_),l),r) ->
          let th_ln = vNNF_CONV' cf baseconvs l
          and th_rp = vNNF_CONV cf baseconvs r in
          vTRANS (vINST [l,p_tm; r,q_tm] pth_imp)
                (vMK_COMB(vAP_TERM or_tm th_ln,th_rp))
    | Comb(Comb(Const("=",Tyapp("fun",Tyapp("bool",_)::_)),l),r) ->
          let th_lp,th_ln = vNNF_DCONV cf base2 l
          and th_rp,th_rn = vNNF_DCONV cf base2 r in
          if cf then
            vTRANS (vINST [l,p_tm; r,q_tm] pth_eq')
                  (vMK_COMB(vAP_TERM and_tm (vMK_COMB(vAP_TERM or_tm th_lp,th_rn)),
                           vMK_COMB(vAP_TERM or_tm th_ln,th_rp)))
          else
            vTRANS (vINST [l,p_tm; r,q_tm] pth_eq)
                  (vMK_COMB(vAP_TERM or_tm (vMK_COMB(vAP_TERM and_tm th_lp,th_rp)),
                           vMK_COMB(vAP_TERM and_tm th_ln,th_rn)))
    | Comb(Const("!",Tyapp("fun",Tyapp("fun",_ty::_)::_)) as q,
           (Abs(x,t))) ->
          let th_p = vNNF_CONV true baseconvs t in
          vAP_TERM q (vABS x th_p)
    | Comb(Const("?",Tyapp("fun",Tyapp("fun",_ty::_)::_)) as q,
           (Abs(x,t))) ->
          let th_p = vNNF_CONV cf baseconvs t in
          vAP_TERM q (vABS x th_p)
    | Comb(Const("?!",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let y = variant (x::frees t) x
          and th_p,th_n = vNNF_DCONV cf base2 t in
          let eq = mk_eq(y,x) in
          let eth_p,_eth_n = base2 eq
          and bth = vBETA (mk_comb(bod,x))
          and bth' = vBETA_CONV(mk_comb(bod,y)) in
          let th_n' = vINST [y,x] th_n in
          let th1 = vINST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (vINST_TYPE [ty,aty] pth_exu)
          and th2 =
            vMK_COMB(vAP_TERM and_tm
                        (vMK_EXISTS x (vTRANS bth th_p)),
                    vMK_FORALL x (vMK_FORALL y
                     (vMK_COMB(vAP_TERM or_tm (vTRANS (vAP_TERM not_tm bth) th_n),
                              vMK_COMB(vAP_TERM or_tm
                                    (vTRANS (vAP_TERM not_tm bth') th_n'),
                                      eth_p))))) in
          vTRANS th1 th2
    | Comb(Const("~",_),t) -> vNNF_CONV' cf baseconvs t
    | _ -> try base1 tm with Failure _ -> vREFL tm
  and vNNF_CONV' cf (base1,base2 as baseconvs) tm =
    match tm with
      Comb(Comb(Const("/\\",_),l),r) ->
          let th_ln = vNNF_CONV' cf baseconvs l
          and th_rn = vNNF_CONV' cf baseconvs r in
          vTRANS (vINST [l,p_tm; r,q_tm] pth_not_and)
                (vMK_COMB(vAP_TERM or_tm th_ln,th_rn))
    | Comb(Comb(Const("\\/",_),l),r) ->
          let th_ln = vNNF_CONV' cf baseconvs l
          and th_rn = vNNF_CONV' cf baseconvs r in
          vTRANS (vINST [l,p_tm; r,q_tm] pth_not_or)
                (vMK_COMB(vAP_TERM and_tm th_ln,th_rn))
    | Comb(Comb(Const("==>",_),l),r) ->
          let th_lp = vNNF_CONV cf baseconvs l
          and th_rn = vNNF_CONV' cf baseconvs r in
          vTRANS (vINST [l,p_tm; r,q_tm] pth_not_imp)
                (vMK_COMB(vAP_TERM and_tm th_lp,th_rn))
    | Comb(Comb(Const("=",Tyapp("fun",Tyapp("bool",_)::_)),l),r) ->
          let th_lp,th_ln = vNNF_DCONV cf base2 l
          and th_rp,th_rn = vNNF_DCONV cf base2 r in
          if cf then
            vTRANS (vINST [l,p_tm; r,q_tm] pth_not_eq')
                  (vMK_COMB(vAP_TERM and_tm (vMK_COMB(vAP_TERM or_tm th_lp,th_rp)),
                           vMK_COMB(vAP_TERM or_tm th_ln,th_rn)))
          else
            vTRANS (vINST [l,p_tm; r,q_tm] pth_not_eq)
                  (vMK_COMB(vAP_TERM or_tm (vMK_COMB(vAP_TERM and_tm th_lp,th_rn)),
                           vMK_COMB(vAP_TERM and_tm th_ln,th_rp)))
    | Comb(Const("!",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let th_n = vNNF_CONV' cf baseconvs t in
          let th1 = vINST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (vINST_TYPE [ty,aty] pth_not_forall)
          and th2 = vTRANS (vAP_TERM not_tm (vBETA(mk_comb(bod,x)))) th_n in
          vTRANS th1 (vMK_EXISTS x th2)
    | Comb(Const("?",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let th_n = vNNF_CONV' true baseconvs t in
          let th1 = vINST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                         (vINST_TYPE [ty,aty] pth_not_exists)
          and th2 = vTRANS (vAP_TERM not_tm (vBETA(mk_comb(bod,x)))) th_n in
          vTRANS th1 (vMK_FORALL x th2)
    | Comb(Const("?!",Tyapp("fun",Tyapp("fun",ty::_)::_)),
           (Abs(x,t) as bod)) ->
          let y = variant (x::frees t) x
          and th_p,th_n = vNNF_DCONV cf base2 t in
          let eq = mk_eq(y,x) in
          let _eth_p,eth_n = base2 eq
          and bth = vBETA (mk_comb(bod,x))
          and bth' = vBETA_CONV(mk_comb(bod,y)) in
          let th_p' = vINST [y,x] th_p in
          let th1' = vINST [bod,mk_var("P",mk_fun_ty ty bool_ty)]
                          (vINST_TYPE [ty,aty] pth_not_exu)
          and th2' =
            vMK_COMB(vAP_TERM or_tm
                        (vMK_FORALL x (vTRANS (vAP_TERM not_tm bth) th_n)),
                    vMK_EXISTS x (vMK_EXISTS y
                     (vMK_COMB(vAP_TERM and_tm (vTRANS bth th_p),
                              vMK_COMB(vAP_TERM and_tm (vTRANS bth' th_p'),
                                      eth_n))))) in
          vTRANS th1' th2'
    | Comb(Const("~",_),t) ->
          let th1 = vNNF_CONV cf baseconvs t in
          vTRANS (vINST [t,p_tm] pth_not_not) th1
    | _ -> let tm' = mk_neg tm in try base1 tm' with Failure _ -> vREFL tm' in
  vNNF_CONV;;

(* ------------------------------------------------------------------------- *)
(* Some common special cases.                                                *)
(* ------------------------------------------------------------------------- *)

let vNNF_CONV =
  (vGEN_NNF_CONV false (vALL_CONV,fun t -> vREFL t,vREFL(mk_neg t)) :conv);;

let vNNFC_CONV =
  (vGEN_NNF_CONV true (vALL_CONV,fun t -> vREFL t,vREFL(mk_neg t)) :conv);;

(* ------------------------------------------------------------------------- *)
(* Skolemize a term already in NNF (doesn't matter if it's not prenex).      *)
(* ------------------------------------------------------------------------- *)

let vSKOLEM_CONV =
  vGEN_REWRITE_CONV vTOP_DEPTH_CONV
   [vEXISTS_OR_THM; vLEFT_EXISTS_AND_THM; vRIGHT_EXISTS_AND_THM;
    vFORALL_AND_THM; vLEFT_FORALL_OR_THM; vRIGHT_FORALL_OR_THM;
    vFORALL_SIMP; vEXISTS_SIMP] +--->
  vGEN_REWRITE_CONV vREDEPTH_CONV
   [vRIGHT_AND_EXISTS_THM;
    vLEFT_AND_EXISTS_THM;
    vOR_EXISTS_THM;
    vRIGHT_OR_EXISTS_THM;
    vLEFT_OR_EXISTS_THM;
    vSKOLEM_THM];;

(* ------------------------------------------------------------------------- *)
(* Put a term already in NNF into prenex form.                               *)
(* ------------------------------------------------------------------------- *)

let vPRENEX_CONV =
  vGEN_REWRITE_CONV vREDEPTH_CONV
   [vAND_FORALL_THM; vLEFT_AND_FORALL_THM; vRIGHT_AND_FORALL_THM;
    vLEFT_OR_FORALL_THM; vRIGHT_OR_FORALL_THM;
    vOR_EXISTS_THM; vLEFT_OR_EXISTS_THM; vRIGHT_OR_EXISTS_THM;
    vLEFT_AND_EXISTS_THM; vRIGHT_AND_EXISTS_THM];;

(* ------------------------------------------------------------------------- *)
(* Weak and normal DNF conversion. The "weak" form gives a disjunction of    *)
(* conjunctions, but has no particular associativity at either level and     *)
(* may contain duplicates. The regular forms give canonical right-associate  *)
(* lists without duplicates, but do not remove subsumed disjuncts.           *)
(*                                                                           *)
(* In both cases the input term is supposed to be in NNF already. We do go   *)
(* inside quantifiers and transform their body, but don't move them.         *)
(* ------------------------------------------------------------------------- *)

let vWEAK_DNF_CONV,vDNF_CONV =
  let pth1 = vTAUT (parse_term "a /\\ (b \\/ c) <=> a /\\ b \\/ a /\\ c")
  and pth2 = vTAUT (parse_term "(a \\/ b) /\\ c <=> a /\\ c \\/ b /\\ c")
  and a_tm = (parse_term "a:bool") and b_tm = (parse_term "b:bool") and c_tm = (parse_term "c:bool") in
  let rec distribute tm =
    match tm with
      Comb(Comb(Const("/\\",_),a),Comb(Comb(Const("\\/",_),b),c)) ->
          let th = vINST [a,a_tm; b,b_tm; c,c_tm] pth1 in
          vTRANS th (vBINOP_CONV distribute (rand(concl th)))
    | Comb(Comb(Const("/\\",_),Comb(Comb(Const("\\/",_),a),b)),c) ->
          let th = vINST [a,a_tm; b,b_tm; c,c_tm] pth2 in
          vTRANS th (vBINOP_CONV distribute (rand(concl th)))
    | _ -> vREFL tm in
  let strengthen =
    vDEPTH_BINOP_CONV (parse_term "(\\/)") vCONJ_CANON_CONV +---> vDISJ_CANON_CONV in
  let rec weakdnf tm =
    match tm with
      Comb(Const("!",_),Abs(_,_))
    | Comb(Const("?",_),Abs(_,_)) -> vBINDER_CONV weakdnf tm
    | Comb(Comb(Const("\\/",_),_),_) -> vBINOP_CONV weakdnf tm
    | Comb(Comb(Const("/\\",_) as op,l),r) ->
          let th = vMK_COMB(vAP_TERM op (weakdnf l),weakdnf r) in
          vTRANS th (distribute(rand(concl th)))
    | _ -> vREFL tm
  and substrongdnf tm =
    match tm with
      Comb(Const("!",_),Abs(_,_))
    | Comb(Const("?",_),Abs(_,_)) -> vBINDER_CONV strongdnf tm
    | Comb(Comb(Const("\\/",_),_),_) -> vBINOP_CONV substrongdnf tm
    | Comb(Comb(Const("/\\",_) as op,l),r) ->
          let th = vMK_COMB(vAP_TERM op (substrongdnf l),substrongdnf r) in
          vTRANS th (distribute(rand(concl th)))
    | _ -> vREFL tm
  and strongdnf tm =
    let th = substrongdnf tm in
    vTRANS th (strengthen(rand(concl th))) in
  weakdnf,strongdnf;;

(* ------------------------------------------------------------------------- *)
(* Likewise for CNF.                                                         *)
(* ------------------------------------------------------------------------- *)

let vWEAK_CNF_CONV,vCNF_CONV =
  let pth1 = vTAUT (parse_term "a \\/ (b /\\ c) <=> (a \\/ b) /\\ (a \\/ c)")
  and pth2 = vTAUT (parse_term "(a /\\ b) \\/ c <=> (a \\/ c) /\\ (b \\/ c)")
  and a_tm = (parse_term "a:bool") and b_tm = (parse_term "b:bool") and c_tm = (parse_term "c:bool") in
  let rec distribute tm =
    match tm with
      Comb(Comb(Const("\\/",_),a),Comb(Comb(Const("/\\",_),b),c)) ->
          let th = vINST [a,a_tm; b,b_tm; c,c_tm] pth1 in
          vTRANS th (vBINOP_CONV distribute (rand(concl th)))
    | Comb(Comb(Const("\\/",_),Comb(Comb(Const("/\\",_),a),b)),c) ->
          let th = vINST [a,a_tm; b,b_tm; c,c_tm] pth2 in
          vTRANS th (vBINOP_CONV distribute (rand(concl th)))
    | _ -> vREFL tm in
  let strengthen =
    vDEPTH_BINOP_CONV (parse_term "(/\\)") vDISJ_CANON_CONV +---> vCONJ_CANON_CONV in
  let rec weakcnf tm =
    match tm with
      Comb(Const("!",_),Abs(_,_))
    | Comb(Const("?",_),Abs(_,_)) -> vBINDER_CONV weakcnf tm
    | Comb(Comb(Const("/\\",_),_),_) -> vBINOP_CONV weakcnf tm
    | Comb(Comb(Const("\\/",_) as op,l),r) ->
          let th = vMK_COMB(vAP_TERM op (weakcnf l),weakcnf r) in
          vTRANS th (distribute(rand(concl th)))
    | _ -> vREFL tm
  and substrongcnf tm =
    match tm with
      Comb(Const("!",_),Abs(_,_))
    | Comb(Const("?",_),Abs(_,_)) -> vBINDER_CONV strongcnf tm
    | Comb(Comb(Const("/\\",_),_),_) -> vBINOP_CONV substrongcnf tm
    | Comb(Comb(Const("\\/",_) as op,l),r) ->
          let th = vMK_COMB(vAP_TERM op (substrongcnf l),substrongcnf r) in
          vTRANS th (distribute(rand(concl th)))
    | _ -> vREFL tm
  and strongcnf tm =
    let th = substrongcnf tm in
    vTRANS th (strengthen(rand(concl th))) in
  weakcnf,strongcnf;;

(* ------------------------------------------------------------------------- *)
(* Simply right-associate w.r.t. a binary operator.                          *)
(* ------------------------------------------------------------------------- *)

let vASSOC_CONV th =
  let th' = vSYM(vSPEC_ALL th) in
  let opx,yopz = dest_comb(rhs(concl th')) in
  let op,x = dest_comb opx in
  let y = lhand yopz and z = rand yopz in
  let rec distrib tm =
    match tm with
      Comb(Comb(op',Comb(Comb(op'',p),q)),r) when op' = op && op'' = op ->
          let th1 = vINST [p,x; q,y; r,z] th' in
          let l,r' = dest_comb(rand(concl th1)) in
          let th2 = vAP_TERM l (distrib r') in
          let th3 = distrib(rand(concl th2)) in
          vTRANS th1 (vTRANS th2 th3)
    | _ -> vREFL tm in
  let rec assoc tm =
    match tm with
      Comb(Comb(op',_p) as l,q) when op' = op ->
          let th = vAP_TERM l (assoc q) in
          vTRANS th (distrib(rand(concl th)))
    | _ -> vREFL tm in
  assoc;;

(* ------------------------------------------------------------------------- *)
(* Eliminate select terms from a goal.                                       *)
(* ------------------------------------------------------------------------- *)

let vSELECT_ELIM_TAC =
  let vSELECT_ELIM_CONV =
    let vSELECT_ELIM_THM =
      let pth = prove
       ((parse_term "(P:A->bool)((@) P) <=> (?) P"),
        vREWRITE_TAC[vEXISTS_THM] ----> vBETA_TAC ----> vREFL_TAC)
      and ptm = (parse_term "P:A->bool") in
      fun tm -> let stm,atm = dest_comb tm in
                if is_const stm && fst(dest_const stm) = "@" then
                 vCONV_RULE(vLAND_CONV vBETA_CONV)
                   (vPINST [type_of(bndvar atm),aty] [atm,ptm] pth)
                else failwith "SELECT_ELIM_THM: not a select-term" in
    fun tm ->
      vPURE_REWRITE_CONV (map vSELECT_ELIM_THM (find_terms is_select tm)) tm in
  let vSELECT_ELIM_ICONV =
    let vSELECT_AX_THM =
      let pth = vISPEC (parse_term "P:A->bool") vSELECT_AX
      and ptm = (parse_term "P:A->bool") in
      fun tm -> let stm,atm = dest_comb tm in
                if is_const stm && fst(dest_const stm) = "@" then
                  let fvs = frees atm in
                  let th1 = vPINST [type_of(bndvar atm),aty] [atm,ptm] pth in
                  let th2 = vCONV_RULE(vBINDER_CONV (vBINOP_CONV vBETA_CONV)) th1 in
                  vGENL fvs th2
                else failwith "SELECT_AX_THM: not a select-term" in
    let vSELECT_ELIM_ICONV tm =
      let t = find_term is_select tm in
      let th1 = vSELECT_AX_THM t in
      let itm = mk_imp(concl th1,tm) in
      let th2 = vDISCH_ALL (vMP (vASSUME itm) th1) in
      let fvs = frees t in
      let fty = itlist (mk_fun_ty -| type_of) fvs (type_of t) in
      let fn = genvar fty
      and atm = list_mk_abs(fvs,t) in
      let rawdef = mk_eq(fn,atm) in
      let def = vGENL fvs (vSYM(vRIGHT_BETAS fvs (vASSUME rawdef))) in
      let th3 = vPURE_REWRITE_CONV[def] (lhand(concl th2)) in
      let gtm = mk_forall(fn,rand(concl th3)) in
      let th4 = vEQ_MP (vSYM th3) (vSPEC fn (vASSUME gtm)) in
      let th5 = vIMP_TRANS (vDISCH gtm th4) th2 in
      vMP (vINST [atm,fn] (vDISCH rawdef th5)) (vREFL atm) in
    let rec vSELECT_ELIMS_ICONV tm =
      try let th = vSELECT_ELIM_ICONV tm in
          let tm' = lhand(concl th) in
          vIMP_TRANS (vSELECT_ELIMS_ICONV tm') th
      with Failure _ -> vDISCH tm (vASSUME tm) in
    vSELECT_ELIMS_ICONV in
  vCONV_TAC vSELECT_ELIM_CONV ----> vW(vMATCH_MP_TAC -| vSELECT_ELIM_ICONV -| snd);;

(* ------------------------------------------------------------------------- *)
(* Eliminate all lambda-terms except those part of quantifiers.              *)
(* ------------------------------------------------------------------------- *)

let vLAMBDA_ELIM_CONV =
  let vHALF_MK_ABS_CONV =
    let pth = prove
     ((parse_term "(s = \\x. t x) <=> (!x. s x = t x)"),
      vREWRITE_TAC[vFUN_EQ_THM]) in
    let rec conv vs tm =
      if vs = [] then vREFL tm else
      (vGEN_REWRITE_CONV vI [pth] +---> vBINDER_CONV(conv (tl vs))) tm in
    conv in
  let rec find_lambda tm =
    if is_abs tm then tm
    else if is_var tm || is_const tm then failwith "find_lambda"
    else if is_abs tm then tm else
    if is_forall tm || is_exists tm || is_uexists tm
    then find_lambda (body(rand tm)) else
    let l,r = dest_comb tm in
    try find_lambda l with Failure _ -> find_lambda r in
  let rec vELIM_LAMBDA conv tm =
    try conv tm with Failure _ ->
    if is_abs tm then vABS_CONV (vELIM_LAMBDA conv) tm
    else if is_var tm || is_const tm then vREFL tm else
    if is_forall tm || is_exists tm || is_uexists tm
    then vBINDER_CONV (vELIM_LAMBDA conv) tm
    else vCOMB_CONV (vELIM_LAMBDA conv) tm in
  let vAPPLY_PTH =
    let pth = prove
     ((parse_term "(!a. (a = c) ==> (P = Q a)) ==> (P <=> !a. (a = c) ==> Q a)"),
      vSIMP_TAC[vLEFT_FORALL_IMP_THM; vEXISTS_REFL]) in
    vMATCH_MP pth in
  let vLAMB1_CONV tm =
    let atm = find_lambda tm in
    let v,_bod = dest_abs atm in
    let vs = frees atm in
    let vs' = vs @ [v] in
    let aatm = list_mk_abs(vs,atm) in
    let f = genvar(type_of aatm) in
    let eq = mk_eq(f,aatm) in
    let th1 = vSYM(vRIGHT_BETAS vs (vASSUME eq)) in
    let th2 = vELIM_LAMBDA(vGEN_REWRITE_CONV vI [th1]) tm in
    let th3 = vAPPLY_PTH (vGEN f (vDISCH_ALL th2)) in
    vCONV_RULE(vRAND_CONV(vBINDER_CONV(vLAND_CONV (vHALF_MK_ABS_CONV vs')))) th3 in
  let rec conv tm =
    try (vLAMB1_CONV +---> conv) tm with Failure _ -> vREFL tm in
  conv;;

(* ------------------------------------------------------------------------- *)
(* Eliminate conditionals; CONDS_ELIM_CONV aims for disjunctive splitting,   *)
(* for refutation procedures, and CONDS_CELIM_CONV for conjunctive.          *)
(* Both switch modes "sensibly" when going through a quantifier.             *)
(* ------------------------------------------------------------------------- *)

let vCONDS_ELIM_CONV,vCONDS_CELIM_CONV =
  let th_cond = prove
   ((parse_term "((b <=> F) ==> x = x0) /\\ ((b <=> T) ==> x = x1)\n     ==> x = (b /\\ x1 \\/ ~b /\\ x0)"),
    vBOOL_CASES_TAC (parse_term "b:bool") ----> vASM_REWRITE_TAC[])
  and th_cond' = prove
   ((parse_term "((b <=> F) ==> x = x0) /\\ ((b <=> T) ==> x = x1)\n     ==> x = ((~b \\/ x1) /\\ (b \\/ x0))"),
    vBOOL_CASES_TAC (parse_term "b:bool") ----> vASM_REWRITE_TAC[])
  and propsimps = basic_net()
  and false_tm = (parse_term "F") and true_tm = (parse_term "T") in
  let match_th = vMATCH_MP th_cond and match_th' = vMATCH_MP th_cond'
  and propsimp_conv = vDEPTH_CONV(vREWRITES_CONV propsimps)
  and proptsimp_conv =
    let cnv = vTRY_CONV(vREWRITES_CONV propsimps) in
    vBINOP_CONV cnv +---> cnv in
  let rec find_conditional fvs tm =
    match tm with
      Comb(s,t) ->
        if is_cond tm && intersect (frees(lhand s)) fvs = [] then tm
        else (try (find_conditional fvs s)
              with Failure _ -> find_conditional fvs t)
    | Abs(x,t) -> find_conditional (x::fvs) t
    | _ -> failwith "find_conditional" in
  let rec vCONDS_ELIM_CONV dfl tm =
    try let t = find_conditional [] tm in
        let p = lhand(rator t) in
        let th_new =
          if p = false_tm || p = true_tm then propsimp_conv tm else
          let asm_0 = mk_eq(p,false_tm) and asm_1 = mk_eq(p,true_tm) in
          let simp_0 = net_of_thm false (vASSUME asm_0) propsimps
          and simp_1 = net_of_thm false (vASSUME asm_1) propsimps in
          let th_0 = vDISCH asm_0 (vDEPTH_CONV(vREWRITES_CONV simp_0) tm)
          and th_1 = vDISCH asm_1 (vDEPTH_CONV(vREWRITES_CONV simp_1) tm) in
          let th_2 = vCONJ th_0 th_1 in
          let th_3 = if dfl then match_th th_2 else match_th' th_2 in
          vTRANS th_3 (proptsimp_conv(rand(concl th_3))) in
        vCONV_RULE (vRAND_CONV (vCONDS_ELIM_CONV dfl)) th_new
    with Failure _ ->
    if is_neg tm then
       vRAND_CONV (vCONDS_ELIM_CONV (not dfl)) tm
    else if is_conj tm || is_disj tm then
       vBINOP_CONV (vCONDS_ELIM_CONV dfl) tm
    else if is_imp tm || is_iff tm then
       vCOMB2_CONV (vRAND_CONV (vCONDS_ELIM_CONV (not dfl)))
                  (vCONDS_ELIM_CONV dfl) tm
    else if is_forall tm then
         vBINDER_CONV (vCONDS_ELIM_CONV false) tm
    else if is_exists tm || is_uexists tm then
         vBINDER_CONV (vCONDS_ELIM_CONV true) tm
    else vREFL tm in
  vCONDS_ELIM_CONV true,vCONDS_ELIM_CONV false;;

(* ------------------------------------------------------------------------- *)
(* Fix up all head arities to be consistent, in "first order logic" style.   *)
(* Applied to the assumptions (not conclusion) in a goal.                    *)
(* ------------------------------------------------------------------------- *)

let vASM_FOL_TAC =
  let rec get_heads lconsts tm (cheads,vheads as sofar) =
    try let v,bod = dest_forall tm in
        get_heads (subtract lconsts [v]) bod sofar
    with Failure _ -> try
        let l,r = try dest_conj tm with Failure _ -> dest_disj tm in
        get_heads lconsts l (get_heads lconsts r sofar)
    with Failure _ -> try
        let tm' = dest_neg tm in
        get_heads lconsts tm' sofar
    with Failure _ ->
        let hop,args = strip_comb tm in
        let len = length args in
        let newheads =
          if is_const hop || mem hop lconsts
          then (insert (hop,len) cheads,vheads)
          else if len > 0 then (cheads,insert (hop,len) vheads) else sofar in
        itlist (get_heads lconsts) args newheads in
  let get_thm_heads th sofar =
    get_heads (freesl(hyp th)) (concl th) sofar in
  let vAPP_CONV =
    let th = prove
     ((parse_term "!(f:A->B) x. f x = I f x"),
      vREWRITE_TAC[vI_THM]) in
    vREWR_CONV th in
  let rec vAPP_N_CONV n tm =
    if n = 1 then vAPP_CONV tm
    else (vRATOR_CONV (vAPP_N_CONV (n - 1)) +---> vAPP_CONV) tm in
  let rec vFOL_CONV hddata tm =
    if is_forall tm then vBINDER_CONV (vFOL_CONV hddata) tm
    else if is_conj tm || is_disj tm then vBINOP_CONV (vFOL_CONV hddata) tm else
    let op,args = strip_comb tm in
    let th = rev_itlist (vC (curry vMK_COMB))
                        (map (vFOL_CONV hddata) args) (vREFL op) in
    let tm' = rand(concl th) in
    let n = try length args - assoc op hddata with Failure _ -> 0 in
    if n = 0 then th
    else vTRANS th (vAPP_N_CONV n tm') in
  let vGEN_FOL_CONV (cheads,vheads) =
    let hddata =
      if vheads = [] then
        let hops = setify (map fst cheads) in
        let getmin h =
          let ns = mapfilter
            (fun (k,n) -> if k = h then n else fail()) cheads in
          if length ns < 2 then fail() else h,end_itlist min ns in
        mapfilter getmin hops
      else
        map (fun t -> if is_const t && fst(dest_const t) = "="
                      then t,2 else t,0)
            (setify (map fst (vheads @ cheads))) in
    vFOL_CONV hddata in
  fun (asl,_w as gl) ->
    let headsp = itlist (get_thm_heads -| snd) asl ([],[]) in
    vRULE_ASSUM_TAC(vCONV_RULE(vGEN_FOL_CONV headsp)) gl;;

(* ------------------------------------------------------------------------- *)
(* Depth conversion to apply at "atomic" formulas in "first-order" term.     *)
(* ------------------------------------------------------------------------- *)

let rec vPROP_ATOM_CONV conv tm =
  match tm with
    Comb((Const("!",_) | Const("?",_) | Const("?!",_)),Abs(_,_))
      -> vBINDER_CONV (vPROP_ATOM_CONV conv) tm
  | Comb(Comb
     ((Const("/\\",_) | Const("\\/",_) | Const("==>",_) |
       (Const("=",Tyapp("fun",[Tyapp("bool",[]);_])))),_),_)
        -> vBINOP_CONV (vPROP_ATOM_CONV conv) tm
  | Comb(Const("~",_),_) -> vRAND_CONV (vPROP_ATOM_CONV conv) tm
  | _ -> vTRY_CONV conv tm;;
