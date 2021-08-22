(* ========================================================================= *)
(* Boolean theory including (intuitionistic) defs of logical connectives.    *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Preterm
open Printer
open Parser
open Equal

(* ------------------------------------------------------------------------- *)
(* Set up parse status of basic and derived logical constants.               *)
(* ------------------------------------------------------------------------- *)

let () = parse_as_prefix "~";;

parse_as_binder "\\";;
parse_as_binder "!";;
parse_as_binder "?";;
parse_as_binder "?!";;

parse_as_infix ("==>",(4,"right"));;
parse_as_infix ("\\/",(6,"right"));;
parse_as_infix ("/\\",(8,"right"));;

(* ------------------------------------------------------------------------- *)
(* Set up more orthodox notation for equations and equivalence.              *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("<=>",(2,"right"));;
override_interface ("<=>",(parse_term "(=):bool->bool->bool"));;
parse_as_infix("=",(12,"right"));;

(* ------------------------------------------------------------------------- *)
(* Special syntax for Boolean equations (IFF).                               *)
(* ------------------------------------------------------------------------- *)

let is_iff tm =
  match tm with
    Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),_l),_r) -> true
  | _ -> false;;

let dest_iff tm =
  match tm with
    Comb(Comb(Const("=",Tyapp("fun",[Tyapp("bool",[]);_])),l),r) -> (l,r)
  | _ -> failwith "dest_iff";;

let mk_iff =
  let eq_tm = (parse_term "(<=>)") in
  fun (l,r) -> mk_comb(mk_comb(eq_tm,l),r);;

(* ------------------------------------------------------------------------- *)
(* Rule allowing easy instantiation of polymorphic proformas.                *)
(* ------------------------------------------------------------------------- *)

let vPINST tyin tmin =
  let iterm_fn = vINST (map (vI $-$ (inst tyin)) tmin)
  and itype_fn = vINST_TYPE tyin in
  fun th -> try iterm_fn (itype_fn th)
            with Failure _ -> failwith "PINST";;

(* ------------------------------------------------------------------------- *)
(* Useful derived deductive rule.                                            *)
(* ------------------------------------------------------------------------- *)

let vPROVE_HYP ath bth =
  if exists (aconv (concl ath)) (hyp bth)
  then vEQ_MP (vDEDUCT_ANTISYM_RULE ath bth) ath
  else bth;;

(* ------------------------------------------------------------------------- *)
(* Rules for T                                                               *)
(* ------------------------------------------------------------------------- *)

let vT_DEF = new_basic_definition
 (parse_term "T = ((\\p:bool. p) = (\\p:bool. p))");;

let vTRUTH = vEQ_MP (vSYM vT_DEF) (vREFL (parse_term "\\p:bool. p"));;

let vEQT_ELIM th =
  try vEQ_MP (vSYM th) vTRUTH
  with Failure _ -> failwith "EQT_ELIM";;

let vEQT_INTRO =
  let t = (parse_term "t:bool") in
  let pth =
    let th1 = vDEDUCT_ANTISYM_RULE (vASSUME t) vTRUTH in
    let th2 = vEQT_ELIM(vASSUME(concl th1)) in
    vDEDUCT_ANTISYM_RULE th2 th1 in
  fun th -> vEQ_MP (vINST[concl th,t] pth) th;;

(* ------------------------------------------------------------------------- *)
(* Rules for /\                                                              *)
(* ------------------------------------------------------------------------- *)

let vAND_DEF = new_basic_definition
 (parse_term "(/\\) = \\p q. (\\f:bool->bool->bool. f p q) = (\\f. f T T)");;

let mk_conj = mk_binary "/\\";;
let list_mk_conj = end_itlist (curry mk_conj);;

let vCONJ =
  let f = (parse_term "f:bool->bool->bool")
  and p = (parse_term "p:bool")
  and q = (parse_term "q:bool") in
  let pth1 =
    let th1 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM vAND_DEF p) in
    let th2 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM th1 q) in
    let th3 = vEQ_MP th2 (vASSUME(mk_conj(p,q))) in
    vEQT_ELIM(vBETA_RULE (vAP_THM th3 (parse_term "\\(p:bool) (q:bool). q")))
  and pth2 =
    let pth = vASSUME p
    and qth = vASSUME q in
    let th1 = vMK_COMB(vAP_TERM f (vEQT_INTRO pth),vEQT_INTRO qth) in
    let th2 = vABS f th1 in
    let th3 = vBETA_RULE (vAP_THM (vAP_THM vAND_DEF p) q) in
    vEQ_MP (vSYM th3) th2 in
  let pth = vDEDUCT_ANTISYM_RULE pth1 pth2 in
  fun th1 th2 ->
    let th = vINST [concl th1,p; concl th2,q] pth in
    vEQ_MP (vPROVE_HYP th1 th) th2;;

let vCONJUNCT1 =
  let vP = (parse_term "P:bool") and vQ = (parse_term "Q:bool") in
  let pth =
    let th1 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM vAND_DEF vP) in
    let th2 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM th1 vQ) in
    let th3 = vEQ_MP th2 (vASSUME(mk_conj(vP,vQ))) in
    vEQT_ELIM(vBETA_RULE (vAP_THM th3 (parse_term "\\(p:bool) (q:bool). p"))) in
  fun th ->
    try let l,r = dest_conj(concl th) in
        vPROVE_HYP th (vINST [l,vP; r,vQ] pth)
    with Failure _ -> failwith "CONJUNCT1";;

let vCONJUNCT2 =
  let vP = (parse_term "P:bool") and vQ = (parse_term "Q:bool") in
  let pth =
    let th1 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM vAND_DEF vP) in
    let th2 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM th1 vQ) in
    let th3 = vEQ_MP th2 (vASSUME(mk_conj(vP,vQ))) in
    vEQT_ELIM(vBETA_RULE (vAP_THM th3 (parse_term "\\(p:bool) (q:bool). q"))) in
  fun th ->
    try let l,r = dest_conj(concl th) in
        vPROVE_HYP th (vINST [l,vP; r,vQ] pth)
    with Failure _ -> failwith "CONJUNCT2";;

let vCONJ_PAIR th =
  try vCONJUNCT1 th,vCONJUNCT2 th
  with Failure _ -> failwith "CONJ_PAIR: Not a conjunction";;

let vCONJUNCTS = striplist vCONJ_PAIR;;

(* ------------------------------------------------------------------------- *)
(* Rules for ==>                                                             *)
(* ------------------------------------------------------------------------- *)

let vIMP_DEF = new_basic_definition
  (parse_term "(==>) = \\p q. p /\\ q <=> p");;

let mk_imp = mk_binary "==>";;

let vMP =
  let p = (parse_term "p:bool") and q = (parse_term "q:bool") in
  let pth =
    let th1 = vBETA_RULE (vAP_THM (vAP_THM vIMP_DEF p) q)
    and th2 = vCONJ (vASSUME p) (vASSUME q)
    and th3 = vCONJUNCT1(vASSUME(mk_conj(p,q))) in
    vEQ_MP (vSYM th1) (vDEDUCT_ANTISYM_RULE th2 th3)
  and qth =
    let th1 = vBETA_RULE (vAP_THM (vAP_THM vIMP_DEF p) q) in
    let th2 = vEQ_MP th1 (vASSUME(mk_imp(p,q))) in
    vCONJUNCT2 (vEQ_MP (vSYM th2) (vASSUME p)) in
  let rth = vDEDUCT_ANTISYM_RULE pth qth in
  fun ith th ->
    let ant,con = dest_imp (concl ith) in
    if aconv ant (concl th) then
      vEQ_MP (vPROVE_HYP th (vINST [ant,p; con,q] rth)) ith
    else failwith "MP: theorems do not agree";;

let vDISCH =
  let p = (parse_term "p:bool")
  and q = (parse_term "q:bool") in
  let pth = vSYM(vBETA_RULE (vAP_THM (vAP_THM vIMP_DEF p) q)) in
  fun a th ->
    let th1 = vCONJ (vASSUME a) th in
    let th2 = vCONJUNCT1 (vASSUME (concl th1)) in
    let th3 = vDEDUCT_ANTISYM_RULE th1 th2 in
    let th4 = vINST [a,p; concl th,q] pth in
    vEQ_MP th4 th3;;

let rec vDISCH_ALL th =
  try vDISCH_ALL (vDISCH (hd (hyp th)) th)
  with Failure _ -> th;;

let vUNDISCH th =
  try vMP th (vASSUME(rand(rator(concl th))))
  with Failure _ -> failwith "UNDISCH";;

let rec vUNDISCH_ALL th =
  if is_imp (concl th) then vUNDISCH_ALL (vUNDISCH th)
  else th;;

let vIMP_ANTISYM_RULE =
  let p = (parse_term "p:bool") and q = (parse_term "q:bool") and imp_tm = (parse_term "(==>)") in
  let pq = mk_imp(p,q) and qp = mk_imp(q,p) in
  let pth1,pth2 = vCONJ_PAIR(vASSUME(mk_conj(pq,qp))) in
  let pth3 = vDEDUCT_ANTISYM_RULE (vUNDISCH pth2) (vUNDISCH pth1) in
  let pth4 = vDISCH_ALL(vASSUME q) and pth5 = vASSUME(mk_eq(p,q)) in
  let pth6 = vCONJ (vEQ_MP (vSYM(vAP_THM (vAP_TERM imp_tm pth5) q)) pth4)
                  (vEQ_MP (vSYM(vAP_TERM (mk_comb(imp_tm,q)) pth5)) pth4) in
  let pth = vDEDUCT_ANTISYM_RULE pth6 pth3 in
  fun th1 th2 ->
    let p1,q1 = dest_imp(concl th1) in
    vEQ_MP (vINST [p1,p; q1,q] pth) (vCONJ th1 th2);;

let vADD_ASSUM tm th = vMP (vDISCH tm th) (vASSUME tm);;

let vEQ_IMP_RULE =
  let peq = (parse_term "p <=> q") in
  let p,q = dest_iff peq in
  let pth1 = vDISCH peq (vDISCH p (vEQ_MP (vASSUME peq) (vASSUME p)))
  and pth2 = vDISCH peq (vDISCH q (vEQ_MP (vSYM(vASSUME peq)) (vASSUME q))) in
  fun th -> let l,r = dest_iff(concl th) in
            vMP (vINST [l,p; r,q] pth1) th,vMP (vINST [l,p; r,q] pth2) th;;

let vIMP_TRANS =
  let pq = (parse_term "p ==> q")
  and qr = (parse_term "q ==> r") in
  let p,q = dest_imp pq and r = rand qr in
  let pth =
    itlist vDISCH [pq; qr; p] (vMP (vASSUME qr) (vMP (vASSUME pq) (vASSUME p))) in
  fun th1 th2 ->
        let x,y = dest_imp(concl th1)
        and y',z = dest_imp(concl th2) in
        if y <> y' then failwith "IMP_TRANS" else
        vMP (vMP (vINST [x,p; y,q; z,r] pth) th1) th2;;

(* ------------------------------------------------------------------------- *)
(* Rules for !                                                               *)
(* ------------------------------------------------------------------------- *)

let vFORALL_DEF = new_basic_definition
 (parse_term "(!) = \\P:A->bool. P = \\x. T");;

let mk_forall = mk_binder "!";;
let list_mk_forall(vs,bod) = itlist (curry mk_forall) vs bod;;

let vSPEC =
  let vP = (parse_term "P:A->bool")
  and x = (parse_term "x:A") in
  let pth =
    let th1 = vEQ_MP(vAP_THM vFORALL_DEF (parse_term "P:A->bool")) (vASSUME (parse_term "(!)(P:A->bool)")) in
    let th2 = vAP_THM (vCONV_RULE vBETA_CONV th1) (parse_term "x:A") in
    let th3 = vCONV_RULE (vRAND_CONV vBETA_CONV) th2 in
    vDISCH_ALL (vEQT_ELIM th3) in
  fun tm th ->
    try let abs = rand(concl th) in
        vCONV_RULE vBETA_CONV
         (vMP (vPINST [snd(dest_var(bndvar abs)),aty] [abs,vP; tm,x] pth) th)
    with Failure _ -> failwith "SPEC";;

let vSPECL tms th =
  try rev_itlist vSPEC tms th
  with Failure _ -> failwith "SPECL";;

let vSPEC_VAR th =
  let bv = variant (thm_frees th) (bndvar(rand(concl th))) in
  bv,vSPEC bv th;;

let rec vSPEC_ALL th =
  if is_forall(concl th) then vSPEC_ALL(snd(vSPEC_VAR th)) else th;;

let vISPEC t th =
  let x,_ = try dest_forall(concl th) with Failure _ ->
    failwith "ISPEC: input theorem not universally quantified" in
  let tyins = try type_match (snd(dest_var x)) (type_of t) [] with Failure _ ->
    failwith "ISPEC can't type-instantiate input theorem" in
  try vSPEC t (vINST_TYPE tyins th)
  with Failure _ -> failwith "ISPEC: type variable(s) free in assumptions";;

let vISPECL tms th =
  try if tms = [] then th else
      let avs = fst (chop_list (length tms) (fst(strip_forall(concl th)))) in
      let tyins = itlist2 type_match (map (snd -| dest_var) avs)
                          (map type_of tms) [] in
      vSPECL tms (vINST_TYPE tyins th)
  with Failure _ -> failwith "ISPECL";;

let vGEN =
  let pth = vSYM(vCONV_RULE (vRAND_CONV vBETA_CONV)
                          (vAP_THM vFORALL_DEF (parse_term "P:A->bool"))) in
  fun x ->
    let qth = vINST_TYPE[snd(dest_var x),aty] pth in
    let ptm = rand(rand(concl qth)) in
    fun th ->
        let th' = vABS x (vEQT_INTRO th) in
        let phi = lhand(concl th') in
        let rth = vINST[phi,ptm] qth in
        vEQ_MP rth th';;

let vGENL = itlist vGEN;;

let vGEN_ALL th =
  let asl,c = dest_thm th in
  let vars = subtract (frees c) (freesl asl) in
  vGENL vars th;;

(* ------------------------------------------------------------------------- *)
(* Rules for ?                                                               *)
(* ------------------------------------------------------------------------- *)

let vEXISTS_DEF = new_basic_definition
 (parse_term "(?) = \\P:A->bool. !q. (!x. P x ==> q) ==> q");;

let mk_exists =  mk_binder "?";;
let list_mk_exists(vs,bod) =  itlist (curry mk_exists) vs bod;;

let vEXISTS =
  let vP = (parse_term "P:A->bool") and x = (parse_term "x:A") in
  let pth =
    let th1 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM vEXISTS_DEF vP) in
    let th2 = vSPEC (parse_term "x:A") (vASSUME (parse_term "!x:A. P x ==> Q")) in
    let th3 = vDISCH (parse_term "!x:A. P x ==> Q") (vMP th2 (vASSUME (parse_term "(P:A->bool) x"))) in
    vEQ_MP (vSYM th1) (vGEN (parse_term "Q:bool") th3) in
  fun (etm,stm) th ->
    try let _qf,abs = dest_comb etm in
        let bth = vBETA_CONV(mk_comb(abs,stm)) in
        let cth = vPINST [type_of stm,aty] [abs,vP; stm,x] pth in
        vPROVE_HYP (vEQ_MP (vSYM bth) th) cth
    with Failure _ -> failwith "EXISTS";;

let vSIMPLE_EXISTS v th =
  vEXISTS (mk_exists(v,concl th),v) th;;

let vCHOOSE =
  let vP = (parse_term "P:A->bool") and vQ = (parse_term "Q:bool") in
  let pth =
    let th1 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM vEXISTS_DEF vP) in
    let th2 = vSPEC (parse_term "Q:bool") (vUNDISCH(fst(vEQ_IMP_RULE th1))) in
    vDISCH_ALL (vDISCH (parse_term "(?) (P:A->bool)") (vUNDISCH th2)) in
  fun (v,th1) th2 ->
    try let abs = rand(concl th1) in
        let bv,bod = dest_abs abs in
        let cmb = mk_comb(abs,v) in
        let pat = vsubst[v,bv] bod in
        let th3 = vCONV_RULE vBETA_CONV (vASSUME cmb) in
        let th4 = vGEN v (vDISCH cmb (vMP (vDISCH pat th2) th3)) in
        let th5 = vPINST [snd(dest_var v),aty] [abs,vP; concl th2,vQ] pth in
        vMP (vMP th5 th4) th1
    with Failure _ -> failwith "CHOOSE";;

let vSIMPLE_CHOOSE v th =
  vCHOOSE(v,vASSUME (mk_exists(v,hd(hyp th)))) th;;

(* ------------------------------------------------------------------------- *)
(* Rules for \/                                                              *)
(* ------------------------------------------------------------------------- *)

let vOR_DEF = new_basic_definition
 (parse_term "(\\/) = \\p q. !r. (p ==> r) ==> (q ==> r) ==> r");;

let mk_disj = mk_binary "\\/";;
let list_mk_disj = end_itlist (curry mk_disj);;

let vDISJ1 =
  let vP = (parse_term "P:bool") and vQ = (parse_term "Q:bool") in
  let pth =
    let th1 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM vOR_DEF (parse_term "P:bool")) in
    let th2 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM th1 (parse_term "Q:bool")) in
    let th3 = vMP (vASSUME (parse_term "P ==> t")) (vASSUME (parse_term "P:bool")) in
    let th4 = vGEN (parse_term "t:bool") (vDISCH (parse_term "P ==> t") (vDISCH (parse_term "Q ==> t") th3)) in
    vEQ_MP (vSYM th2) th4 in
  fun th tm ->
    try vPROVE_HYP th (vINST [concl th,vP; tm,vQ] pth)
    with Failure _ -> failwith "DISJ1";;

let vDISJ2 =
  let vP = (parse_term "P:bool") and vQ = (parse_term "Q:bool") in
  let pth =
    let th1 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM vOR_DEF (parse_term "P:bool")) in
    let th2 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM th1 (parse_term "Q:bool")) in
    let th3 = vMP (vASSUME (parse_term "Q ==> t")) (vASSUME (parse_term "Q:bool")) in
    let th4 = vGEN (parse_term "t:bool") (vDISCH (parse_term "P ==> t") (vDISCH (parse_term "Q ==> t") th3)) in
    vEQ_MP (vSYM th2) th4 in
  fun tm th ->
    try vPROVE_HYP th (vINST [tm,vP; concl th,vQ] pth)
    with Failure _ -> failwith "DISJ2";;

let vDISJ_CASES =
  let vP = (parse_term "P:bool") and vQ = (parse_term "Q:bool") and vR = (parse_term "R:bool") in
  let pth =
    let th1 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM vOR_DEF (parse_term "P:bool")) in
    let th2 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM th1 (parse_term "Q:bool")) in
    let th3 = vSPEC (parse_term "R:bool") (vEQ_MP th2 (vASSUME (parse_term "P \\/ Q"))) in
    vUNDISCH (vUNDISCH th3) in
  fun th0 th1 th2 ->
    try let c1 = concl th1 and c2 = concl th2 in
        if not (aconv c1 c2) then failwith "DISJ_CASES" else
        let l,r = dest_disj (concl th0) in
        let th = vINST [l,vP; r,vQ; c1,vR] pth in
        vPROVE_HYP (vDISCH r th2) (vPROVE_HYP (vDISCH l th1) (vPROVE_HYP th0 th))
    with Failure _ -> failwith "DISJ_CASES";;

let vSIMPLE_DISJ_CASES th1 th2 =
  vDISJ_CASES (vASSUME(mk_disj(hd(hyp th1),hd(hyp th2)))) th1 th2;;

(* ------------------------------------------------------------------------- *)
(* Rules for negation and falsity.                                           *)
(* ------------------------------------------------------------------------- *)

let vF_DEF = new_basic_definition
 (parse_term "F = !p:bool. p");;

let vNOT_DEF = new_basic_definition
 (parse_term "(~) = \\p. p ==> F");;

let mk_neg =
  let neg_tm = (parse_term "(~)") in
  fun tm -> try mk_comb(neg_tm,tm)
            with Failure _ -> failwith "mk_neg";;

let vNOT_ELIM =
  let vP = (parse_term "P:bool") in
  let pth = vCONV_RULE(vRAND_CONV vBETA_CONV) (vAP_THM vNOT_DEF vP) in
  fun th ->
    try vEQ_MP (vINST [rand(concl th),vP] pth) th
    with Failure _ -> failwith "NOT_ELIM";;

let vNOT_INTRO =
  let vP = (parse_term "P:bool") in
  let pth = vSYM(vCONV_RULE(vRAND_CONV vBETA_CONV) (vAP_THM vNOT_DEF vP)) in
  fun th ->
    try vEQ_MP (vINST [rand(rator(concl th)),vP] pth) th
    with Failure _ -> failwith "NOT_INTRO";;

let vEQF_INTRO =
  let vP = (parse_term "P:bool") in
  let pth =
    let th1 = vNOT_ELIM (vASSUME (parse_term "~ P"))
    and th2 = vDISCH (parse_term "F") (vSPEC vP (vEQ_MP vF_DEF (vASSUME (parse_term "F")))) in
    vDISCH_ALL (vIMP_ANTISYM_RULE th1 th2) in
  fun th ->
    try vMP (vINST [rand(concl th),vP] pth) th
    with Failure _ -> failwith "EQF_INTRO";;

let vEQF_ELIM =
  let vP = (parse_term "P:bool") in
  let pth =
    let th1 = vEQ_MP (vASSUME (parse_term "P = F")) (vASSUME (parse_term "P:bool")) in
    let th2 = vDISCH vP (vSPEC (parse_term "F") (vEQ_MP vF_DEF th1)) in
    vDISCH_ALL (vNOT_INTRO th2) in
  fun th ->
    try vMP (vINST [rand(rator(concl th)),vP] pth) th
    with Failure _ -> failwith "EQF_ELIM";;

let vCONTR =
  let vP = (parse_term "P:bool") and f_tm = (parse_term "F") in
  let pth = vSPEC vP (vEQ_MP vF_DEF (vASSUME (parse_term "F"))) in
  fun tm th ->
    if concl th <> f_tm then failwith "CONTR"
    else vPROVE_HYP th (vINST [tm,vP] pth);;

(* ------------------------------------------------------------------------- *)
(* Rules for unique existence.                                               *)
(* ------------------------------------------------------------------------- *)

let vEXISTS_UNIQUE_DEF = new_basic_definition
 (parse_term "(?!) = \\P:A->bool. ((?) P) /\\ (!x y. P x /\\ P y ==> x = y)");;

let mk_uexists = mk_binder "?!";;

let vEXISTENCE =
  let vP = (parse_term "P:A->bool") in
  let pth =
    let th1 = vCONV_RULE (vRAND_CONV vBETA_CONV) (vAP_THM vEXISTS_UNIQUE_DEF vP) in
    let th2 = vUNDISCH (fst(vEQ_IMP_RULE th1)) in
    vDISCH_ALL (vCONJUNCT1 th2) in
  fun th ->
    try let abs = rand(concl th) in
        let ty = snd(dest_var(bndvar abs)) in
        vMP (vPINST [ty,aty] [abs,vP] pth) th
    with Failure _ -> failwith "EXISTENCE";;
