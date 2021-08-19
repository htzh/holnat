(* ========================================================================= *)
(* Basic equality reasoning including conversionals.                         *)
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

(* ------------------------------------------------------------------------- *)
(* Type abbreviation for conversions.                                        *)
(* ------------------------------------------------------------------------- *)

type conv = term->thm;;

(* ------------------------------------------------------------------------- *)
(* A bit more syntax.                                                        *)
(* ------------------------------------------------------------------------- *)

let lhand = rand -| rator;;

let lhs = fst -| dest_eq;;

let rhs = snd -| dest_eq;;

(* ------------------------------------------------------------------------- *)
(* Similar to variant, but even avoids constants, and ignores types.         *)
(* ------------------------------------------------------------------------- *)

let mk_primed_var =
  let rec svariant avoid s =
    if mem s avoid || (can get_const_type s && not(is_hidden s)) then
      svariant avoid (s^"'")
    else s in
  fun avoid v ->
    let s,ty = dest_var v in
    let s' = svariant (mapfilter (fst -| dest_var) avoid) s in
    mk_var(s',ty);;

(* ------------------------------------------------------------------------- *)
(* General case of beta-conversion.                                          *)
(* ------------------------------------------------------------------------- *)

let vBETA_CONV tm =
  try vBETA tm with Failure _ ->
  try let f,arg = dest_comb tm in
      let v = bndvar f in
      vINST [arg,v] (vBETA (mk_comb(f,v)))
  with Failure _ -> failwith "BETA_CONV: Not a beta-redex";;

(* ------------------------------------------------------------------------- *)
(* A few very basic derived equality rules.                                  *)
(* ------------------------------------------------------------------------- *)

let vAP_TERM tm =
  let rth = vREFL tm in
  fun th -> try vMK_COMB(rth,th)
            with Failure _ -> failwith "AP_TERM";;

let vAP_THM th tm =
  try vMK_COMB(th,vREFL tm)
  with Failure _ -> failwith "AP_THM";;

let vSYM th =
  let tm = concl th in
  let l,_r = dest_eq tm in
  let lth = vREFL l in
  vEQ_MP (vMK_COMB(vAP_TERM (rator (rator tm)) th,lth)) lth;;

let vALPHA tm1 tm2 =
  try vTRANS (vREFL tm1) (vREFL tm2)
  with Failure _ -> failwith "ALPHA";;

let vALPHA_CONV v tm =
  let res = alpha v tm in
  vALPHA tm res;;

let vGEN_ALPHA_CONV v tm =
  if is_abs tm then vALPHA_CONV v tm else
  let b,abs = dest_comb tm in
  vAP_TERM b (vALPHA_CONV v abs);;

let vMK_BINOP op =
  let afn = vAP_TERM op in
  fun (lth,rth) -> vMK_COMB(afn lth,rth);;

(* ------------------------------------------------------------------------- *)
(* Terminal conversion combinators.                                          *)
(* ------------------------------------------------------------------------- *)

let (vNO_CONV:conv) = fun _tm -> failwith "NO_CONV";;

let (vALL_CONV:conv) = vREFL;;

(* ------------------------------------------------------------------------- *)
(* Combinators for sequencing, trying, repeating etc. conversions.           *)
(* ------------------------------------------------------------------------- *)

let ((*THENC*)(---->):conv -> conv -> conv) =
  fun conv1 conv2 t ->
    let th1 = conv1 t in
    let th2 = conv2 (rand(concl th1)) in
    vTRANS th1 th2;;

let ((*ORELSEC*)(||-->):conv -> conv -> conv) =
  fun conv1 conv2 t ->
    try conv1 t with Failure _ -> conv2 t;;

let (vFIRST_CONV:conv list -> conv) = end_itlist (fun c1 c2 -> c1 ||--> c2);;

let (vEVERY_CONV:conv list -> conv) =
  fun l -> itlist (fun c1 c2 -> c1 ----> c2) l vALL_CONV;;

let vREPEATC =
  let rec vREPEATC conv t =
    ((conv ----> (vREPEATC conv)) ||--> vALL_CONV) t in
  (vREPEATC:conv->conv);;

let (vCHANGED_CONV:conv->conv) =
  fun conv tm ->
    let th = conv tm in
    let l,r = dest_eq (concl th) in
    if aconv l r then failwith "CHANGED_CONV" else th;;

let vTRY_CONV conv = conv ||--> vALL_CONV;;

(* ------------------------------------------------------------------------- *)
(* Subterm conversions.                                                      *)
(* ------------------------------------------------------------------------- *)

let (vRATOR_CONV:conv->conv) =
  fun conv tm ->
    match tm with
      Comb(l,r) -> vAP_THM (conv l) r
    | _ -> failwith "RATOR_CONV: Not a combination";;

let (vRAND_CONV:conv->conv) =
  fun conv tm ->
   match tm with
     Comb(l,r) -> vMK_COMB(vREFL l,conv r)
   |  _ -> failwith "RAND_CONV: Not a combination";;

let vLAND_CONV = vRATOR_CONV -| vRAND_CONV;;

let (vCOMB2_CONV: conv->conv->conv) =
  fun lconv rconv tm ->
   match tm with
     Comb(l,r) -> vMK_COMB(lconv l,rconv r)
  | _ -> failwith "COMB2_CONV: Not a combination";;

let vCOMB_CONV = vW vCOMB2_CONV;;

let (vABS_CONV:conv->conv) =
  fun conv tm ->
    let v,bod = dest_abs tm in
    let th = conv bod in
    try vABS v th with Failure _ ->
    let gv = genvar(type_of v) in
    let gbod = vsubst[gv,v] bod in
    let gth = vABS gv (conv gbod) in
    let gtm = concl gth in
    let l,r = dest_eq gtm in
    let v' = variant (frees gtm) v in
    let l' = alpha v' l and r' = alpha v' r in
    vEQ_MP (vALPHA gtm (mk_eq(l',r'))) gth;;

let vBINDER_CONV conv tm =
  if is_abs tm then vABS_CONV conv tm
  else vRAND_CONV(vABS_CONV conv) tm;;

let vSUB_CONV conv tm =
  match tm with
    Comb(_,_) -> vCOMB_CONV conv tm
  | Abs(_,_) -> vABS_CONV conv tm
  | _ -> vREFL tm;;

let (vBINOP_CONV:conv->conv) =
  fun conv tm ->
    let lop,r = dest_comb tm in
    let op,l = dest_comb lop in
    vMK_COMB(vAP_TERM op (conv l),conv r);;

let (vBINOP2_CONV:conv->conv->conv) =
  fun conv1 conv2 tm ->
    let lop,r = dest_comb tm in
    let op,l = dest_comb lop in
    vMK_COMB(vAP_TERM op (conv1 l),conv2 r);;

(* ------------------------------------------------------------------------- *)
(* Depth conversions; internal use of a failure-propagating `Boultonized'    *)
(* version to avoid a great deal of reuilding of terms.                      *)
(* ------------------------------------------------------------------------- *)

let (vONCE_DEPTH_CONV: conv->conv),
    (vDEPTH_CONV: conv->conv),
    (vREDEPTH_CONV: conv->conv),
    (vTOP_DEPTH_CONV: conv->conv),
    (vTOP_SWEEP_CONV: conv->conv) =
  let vTHENQC conv1 conv2 tm =
    try let th1 = conv1 tm in
        try let th2 = conv2(rand(concl th1)) in vTRANS th1 th2
        with Failure _ -> th1
    with Failure _ -> conv2 tm
  and vTHENCQC conv1 conv2 tm =
    let th1 = conv1 tm in
    try let th2 = conv2(rand(concl th1)) in vTRANS th1 th2
    with Failure _ -> th1
  and vCOMB_QCONV conv tm =
    match tm with
      Comb(l,r) ->
        (try let th1 = conv l in
             try let th2 = conv r in vMK_COMB(th1,th2)
             with Failure _ -> vAP_THM th1 r
         with Failure _ -> vAP_TERM l (conv r))
    | _ -> failwith "COMB_QCONV: Not a combination" in
  let rec vREPEATQC conv tm = vTHENCQC conv (vREPEATQC conv) tm in
  let vSUB_QCONV conv tm =
    match tm with
      Abs(_,_) -> vABS_CONV conv tm
    | _ -> vCOMB_QCONV conv tm in
  let rec vONCE_DEPTH_QCONV conv tm =
      (conv ||--> (vSUB_QCONV (vONCE_DEPTH_QCONV conv))) tm
  and vDEPTH_QCONV conv tm =
    vTHENQC (vSUB_QCONV (vDEPTH_QCONV conv))
           (vREPEATQC conv) tm
  and vREDEPTH_QCONV conv tm =
    vTHENQC (vSUB_QCONV (vREDEPTH_QCONV conv))
           (vTHENCQC conv (vREDEPTH_QCONV conv)) tm
  and vTOP_DEPTH_QCONV conv tm =
    vTHENQC (vREPEATQC conv)
           (vTHENCQC (vSUB_QCONV (vTOP_DEPTH_QCONV conv))
                    (vTHENCQC conv (vTOP_DEPTH_QCONV conv))) tm
  and vTOP_SWEEP_QCONV conv tm =
    vTHENQC (vREPEATQC conv)
           (vSUB_QCONV (vTOP_SWEEP_QCONV conv)) tm in
  (fun c -> vTRY_CONV (vONCE_DEPTH_QCONV c)),
  (fun c -> vTRY_CONV (vDEPTH_QCONV c)),
  (fun c -> vTRY_CONV (vREDEPTH_QCONV c)),
  (fun c -> vTRY_CONV (vTOP_DEPTH_QCONV c)),
  (fun c -> vTRY_CONV (vTOP_SWEEP_QCONV c));;

(* ------------------------------------------------------------------------- *)
(* Apply at leaves of op-tree; NB any failures at leaves cause failure.      *)
(* ------------------------------------------------------------------------- *)

let rec vDEPTH_BINOP_CONV op conv tm =
  match tm with
    Comb(Comb(op',_l),_r) when Stdlib.compare op' op = 0 ->
      let l,r = dest_binop op tm in
      let lth = vDEPTH_BINOP_CONV op conv l
      and rth = vDEPTH_BINOP_CONV op conv r in
      vMK_COMB(vAP_TERM op' lth,rth)
  | _ -> conv tm;;

(* ------------------------------------------------------------------------- *)
(* Follow a path.                                                            *)
(* ------------------------------------------------------------------------- *)

let vPATH_CONV =
  let rec path_conv s cnv =
    match s with
      [] -> cnv
    | "l"::t -> vRATOR_CONV (path_conv t cnv)
    | "r"::t -> vRAND_CONV (path_conv t cnv)
    | _::t -> vABS_CONV (path_conv t cnv) in
  fun s cnv -> path_conv (explode s) cnv;;

(* ------------------------------------------------------------------------- *)
(* Follow a pattern                                                          *)
(* ------------------------------------------------------------------------- *)

let vPAT_CONV =
  let rec vPCONV xs pat conv =
    if mem pat xs then conv
    else if not(exists (fun x -> free_in x pat) xs) then vALL_CONV
    else if is_comb pat then
      vCOMB2_CONV (vPCONV xs (rator pat) conv) (vPCONV xs (rand pat) conv)
    else
      vABS_CONV (vPCONV xs (body pat) conv) in
  fun pat -> let xs,pbod = strip_abs pat in vPCONV xs pbod;;

(* ------------------------------------------------------------------------- *)
(* Symmetry conversion.                                                      *)
(* ------------------------------------------------------------------------- *)

let vSYM_CONV tm =
  try let th1 = vSYM(vASSUME tm) in
      let tm' = concl th1 in
      let th2 = vSYM(vASSUME tm') in
      vDEDUCT_ANTISYM_RULE th2 th1
  with Failure _ -> failwith "SYM_CONV";;

(* ------------------------------------------------------------------------- *)
(* Conversion to a rule.                                                     *)
(* ------------------------------------------------------------------------- *)

let vCONV_RULE (conv:conv) th =
  vEQ_MP (conv(concl th)) th;;

(* ------------------------------------------------------------------------- *)
(* Substitution conversion.                                                  *)
(* ------------------------------------------------------------------------- *)

let vSUBS_CONV ths tm =
  try if ths = [] then vREFL tm else
      let lefts = map (lhand -| concl) ths in
      let gvs = map (genvar -| type_of) lefts in
      let pat = subst (zip gvs lefts) tm in
      let abs = list_mk_abs(gvs,pat) in
      let th = rev_itlist
        (fun y x -> vCONV_RULE (vRAND_CONV vBETA_CONV ----> vLAND_CONV vBETA_CONV)
                              (vMK_COMB(x,y))) ths (vREFL abs) in
      if rand(concl th) = tm then vREFL tm else th
  with Failure _ -> failwith "SUBS_CONV";;

(* ------------------------------------------------------------------------- *)
(* Get a few rules.                                                          *)
(* ------------------------------------------------------------------------- *)

let vBETA_RULE = vCONV_RULE(vREDEPTH_CONV vBETA_CONV);;

let vGSYM = vCONV_RULE(vONCE_DEPTH_CONV vSYM_CONV);;

let vSUBS ths = vCONV_RULE (vSUBS_CONV ths);;

(* ------------------------------------------------------------------------- *)
(* A cacher for conversions.                                                 *)
(* ------------------------------------------------------------------------- *)

let vCACHE_CONV =
  let open Nets in
  let vALPHA_HACK th =
    let tm' = lhand(concl th) in
    fun tm -> if tm' = tm then th else vTRANS (vALPHA tm tm') th in
  fun conv ->
    let net = ref empty_net in
    fun tm -> try tryfind (fun f -> f tm) (lookup tm (!net))
              with Failure _ ->
                  let th = conv tm in
                  (net := enter [] (tm,vALPHA_HACK th) (!net); th);;
