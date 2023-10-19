[@@@warning "-33-27-8"]
open Hol.All
open Hol.Accept
(* ========================================================================= *)
(* Elementary real analysis, with some supporting HOL88 compatibility stuff. *)
(* ========================================================================= *)

let dest_neg_imp tm =
  try dest_imp tm with Failure _ ->
  try (dest_neg tm,mk_const("F",[]))
  with Failure _ -> failwith "dest_neg_imp";;

(* ------------------------------------------------------------------------- *)
(* The quantifier movement conversions.                                      *)
(* ------------------------------------------------------------------------- *)

let (vCONV_OF_RCONV: conv -> conv) =
  let rec get_bv tm =
    if is_abs tm then bndvar tm
    else if is_comb tm then try get_bv (rand tm)
            with Failure _ -> get_bv (rator tm)
    else failwith "" in
  fun conv tm ->
  let v = get_bv tm in
  let th1 = conv tm in
  let th2 = vONCE_DEPTH_CONV (vGEN_ALPHA_CONV v) (rhs(concl th1)) in
  vTRANS th1 th2;;

let (vCONV_OF_THM: thm -> conv) =
  vCONV_OF_RCONV -| vREWR_CONV;;

let (vX_FUN_EQ_CONV:term->conv) =
  fun v -> (vREWR_CONV vFUN_EQ_THM) +---> vGEN_ALPHA_CONV v;;

let (vFUN_EQ_CONV:conv) =
  fun tm ->
    let vars = frees tm in
    let op,[ty1;ty2] = dest_type(type_of (lhs tm)) in
    if op = "fun"
       then let varnm =
                if (is_vartype ty1) then "x" else
                   hd(explode(fst(dest_type ty1))) in
            let x = variant vars (mk_var(varnm,ty1)) in
            vX_FUN_EQ_CONV x tm
       else failwith "FUN_EQ_CONV";;

let (vSINGLE_DEPTH_CONV:conv->conv) =
  let rec vSINGLE_DEPTH_CONV conv tm =
    try conv tm with Failure _ ->
    (vSUB_CONV (vSINGLE_DEPTH_CONV conv) +---> (vTRY_CONV conv)) tm in
  vSINGLE_DEPTH_CONV;;

let (vOLD_SKOLEM_CONV:conv) =
  vSINGLE_DEPTH_CONV (vREWR_CONV vSKOLEM_THM);;

let (vX_SKOLEM_CONV:term->conv) =
  fun v -> vOLD_SKOLEM_CONV +---> vGEN_ALPHA_CONV v;;

let vEXISTS_UNIQUE_CONV tm =
  let v = bndvar(rand tm) in
  let th1 = vREWR_CONV vEXISTS_UNIQUE_THM tm in
  let tm1 = rhs(concl th1) in
  let vars = frees tm1 in
  let v = variant vars v in
  let v' = variant (v::vars) v in
  let th2 =
   (vLAND_CONV(vGEN_ALPHA_CONV v) +--->
    vRAND_CONV(vBINDER_CONV(vGEN_ALPHA_CONV v') +--->
              vGEN_ALPHA_CONV v)) tm1 in
  vTRANS th1 th2;;

let vNOT_FORALL_CONV = vCONV_OF_THM vNOT_FORALL_THM;;

let vNOT_EXISTS_CONV = vCONV_OF_THM vNOT_EXISTS_THM;;

let vRIGHT_IMP_EXISTS_CONV = vCONV_OF_THM vRIGHT_IMP_EXISTS_THM;;

let vFORALL_IMP_CONV = vCONV_OF_RCONV
  (vREWR_CONV vTRIV_FORALL_IMP_THM ||-->
   vREWR_CONV vRIGHT_FORALL_IMP_THM ||-->
   vREWR_CONV vLEFT_FORALL_IMP_THM);;

let vEXISTS_AND_CONV = vCONV_OF_RCONV
  (vREWR_CONV vTRIV_EXISTS_AND_THM ||-->
   vREWR_CONV vLEFT_EXISTS_AND_THM ||-->
   vREWR_CONV vRIGHT_EXISTS_AND_THM);;

let vLEFT_IMP_EXISTS_CONV = vCONV_OF_THM vLEFT_IMP_EXISTS_THM;;

let vLEFT_AND_EXISTS_CONV tm =
  let v = bndvar(rand(rand(rator tm))) in
  (vREWR_CONV vLEFT_AND_EXISTS_THM +---> vTRY_CONV (vGEN_ALPHA_CONV v)) tm;;

let vRIGHT_AND_EXISTS_CONV =
  vCONV_OF_THM vRIGHT_AND_EXISTS_THM;;

let vAND_FORALL_CONV = vCONV_OF_THM vAND_FORALL_THM;;

(* ------------------------------------------------------------------------- *)
(* The slew of named tautologies.                                            *)
(* ------------------------------------------------------------------------- *)

let vF_IMP = vTAUT [%q {|!t. ~t ==> t ==> F|} ];;

let vLEFT_AND_OVER_OR = vTAUT
  [%q {|!t1 t2 t3. t1 /\ (t2 \/ t3) <=> t1 /\ t2 \/ t1 /\ t3|} ];;

let vRIGHT_AND_OVER_OR = vTAUT
  [%q {|!t1 t2 t3. (t2 \/ t3) /\ t1 <=> t2 /\ t1 \/ t3 /\ t1|} ];;

(* ------------------------------------------------------------------------- *)
(* Something trivial and useless.                                            *)
(* ------------------------------------------------------------------------- *)

let vINST_TY_TERM(substl,insttyl) th = vINST substl (vINST_TYPE insttyl th);;

(* ------------------------------------------------------------------------- *)
(* Derived rules.                                                            *)
(* ------------------------------------------------------------------------- *)

let vNOT_MP thi th =
  try vMP thi th with Failure _ ->
  try let t = dest_neg (concl thi) in
      vMP(vMP (vSPEC t vF_IMP) thi) th
  with Failure _ -> failwith "NOT_MP";;

(* ------------------------------------------------------------------------- *)
(* Creating half abstractions.                                               *)
(* ------------------------------------------------------------------------- *)

let vMK_ABS qth =
  try let ov = bndvar(rand(concl qth)) in
      let bv,rth = vSPEC_VAR qth in
      let sth = vABS bv rth in
      let cnv = vALPHA_CONV ov in
      vCONV_RULE(vBINOP_CONV cnv) sth
  with Failure _ -> failwith "MK_ABS";;

let vHALF_MK_ABS th =
  try let th1 = vMK_ABS th in
      vCONV_RULE(vLAND_CONV vETA_CONV) th1
  with Failure _ -> failwith "HALF_MK_ABS";;

(* ------------------------------------------------------------------------- *)
(* Old substitution primitive, now a (not very efficient) derived rule.      *)
(* ------------------------------------------------------------------------- *)

let vSUBST thl pat th =
  let eqs,vs = unzip thl in
  let gvs = map (genvar -| type_of) vs in
  let gpat = subst (zip gvs vs) pat in
  let ls,rs = unzip (map (dest_eq -| concl) eqs) in
  let ths = map (vASSUME -| mk_eq) (zip gvs rs) in
  let th1 = vASSUME gpat in
  let th2 = vSUBS ths th1 in
  let th3 = itlist vDISCH (map concl ths) (vDISCH gpat th2) in
  let th4 = vINST (zip ls gvs) th3 in
  vMP (rev_itlist (vC vMP) eqs th4) th;;

(* ------------------------------------------------------------------------- *)
(* Various theorems have different names.                                    *)
(* ------------------------------------------------------------------------- *)

prioritize_num();;

let vLESS_EQUAL_ANTISYM = vGEN_ALL(fst(vEQ_IMP_RULE(vSPEC_ALL vLE_ANTISYM)));;
let vNOT_LESS_0 = vGEN_ALL(vEQF_ELIM(vSPEC_ALL(vCONJUNCT1 vLT)));;
let vLESS_LEMMA1 = vGEN_ALL(fst(vEQ_IMP_RULE(vSPEC_ALL(vCONJUNCT2 vLT))));;
let%a vLESS_SUC_REFL = vARITH_RULE [%q {|!n. n < SUC n|} ];;
let%a vLESS_EQ_SUC_REFL = vARITH_RULE [%q {|!n. n <= SUC n|} ];;
let vLESS_EQUAL_ADD = vGEN_ALL(fst(vEQ_IMP_RULE(vSPEC_ALL vLE_EXISTS)));;
let vLESS_EQ_IMP_LESS_SUC = vGEN_ALL(snd(vEQ_IMP_RULE(vSPEC_ALL vLT_SUC_LE)));;
let vLESS_MONO_ADD = vGEN_ALL(snd(vEQ_IMP_RULE(vSPEC_ALL vLT_ADD_RCANCEL)));;
let%a vLESS_SUC = vARITH_RULE [%q {|!m n. m < n ==> m < (SUC n)|} ];;
let vLESS_ADD_1 = vGEN_ALL(fst(vEQ_IMP_RULE(vSPEC_ALL
  (vREWRITE_RULE[vADD1] vLT_EXISTS))));;
let%a vSUC_SUB1 = vARITH_RULE [%q {|!m. SUC m - 1 = m|} ];;
let%a vLESS_ADD_SUC = vARITH_RULE [%q {|!m n. m < m + SUC n|} ];;
let vOR_LESS = vGEN_ALL(fst(vEQ_IMP_RULE(vSPEC_ALL vLE_SUC_LT)));;
let%a vNOT_SUC_LESS_EQ = vARITH_RULE [%q {|!n m. ~(SUC n <= m) <=> m <= n|} ];;
let%a vLESS_LESS_CASES = vARITH_RULE [%q {|!m n. (m = n) \/ m < n \/ n < m|} ];;
let%a vSUB_SUB = prove
 ([%q {|!b c. c <= b ==> (!a. a - (b - c) = (a + c) - b)|} ],
  vREWRITE_TAC[vRIGHT_IMP_FORALL_THM] ----> vARITH_TAC);;
let%a vLESS_CASES_IMP = vARITH_RULE [%q {|!m n. ~(m < n) /\ ~(m = n) ==> n < m|} ];;
let%a vSUB_LESS_EQ = vARITH_RULE [%q {|!n m. (n - m) <= n|} ];;
let%a vSUB_EQ_EQ_0 = vARITH_RULE [%q {|!m n. (m - n = m) <=> (m = 0) \/ (n = 0)|} ];;
let%a vSUB_LEFT_LESS_EQ =
  vARITH_RULE [%q {|!m n p. m <= (n - p) <=> (m + p) <= n \/ m <= 0|} ];;
let%a vSUB_LEFT_GREATER_EQ = vARITH_RULE [%q {|!m n p. m >= (n - p) <=> (m + p) >= n|} ];;
let%a vLESS_0_CASES = vARITH_RULE [%q {|!m. (0 = m) \/ 0 < m|} ];;
let%a vLESS_OR = vARITH_RULE [%q {|!m n. m < n ==> (SUC m) <= n|} ];;
let%a vSUB_OLD = prove([%q {|(!m. 0 - m = 0) /\
                 (!m n. (SUC m) - n = (if m < n then 0 else SUC(m - n)))|} ],
                vREPEAT vSTRIP_TAC ----> vTRY vCOND_CASES_TAC ---->
                vASM_REWRITE_TAC[] ----> vTRY (vPOP_ASSUM vMP_TAC) ---->
                vARITH_TAC);;

(*============================================================================*)
(* Various useful tactics, conversions etc.                                   *)
(*============================================================================*)

(*----------------------------------------------------------------------------*)
(* SYM_CANON_CONV - Canonicalizes single application of symmetric operator    *)
(* Rewrites `so as to make fn true`, e.g. fn = $<< or fn = curry$= `1` o fst  *)
(*----------------------------------------------------------------------------*)

let vSYM_CANON_CONV sym fn =
  vREWR_CONV sym -|
  check (not -| fn -| ((snd -| dest_comb) $-$ vI) -| dest_comb);;

(*----------------------------------------------------------------------------*)
(* IMP_SUBST_TAC - Implicational substitution for deepest matchable term      *)
(*----------------------------------------------------------------------------*)

let (vIMP_SUBST_TAC:thm_tactic) =
  fun th (asl,w) ->
    let tms = find_terms (can (vPART_MATCH (lhs -| snd -| dest_imp) th)) w in
    let tm1 = hd (sort free_in tms) in
    let th1 = vPART_MATCH (lhs -| snd -| dest_imp) th tm1 in
    let (a,(l,r)) = (vI $-$ dest_eq) (dest_imp (concl th1)) in
    let gv = genvar (type_of l) in
    let pat = subst[gv,l] w in
    null_meta,
    [(asl,a); (asl,subst[(r,gv)] pat)],
    fun i [t1;t2] -> vSUBST[(vSYM(vMP th1 t1),gv)] pat t2;;

(*---------------------------------------------------------------*)
(* EXT_CONV `!x. f x = g x` = |- (!x. f x = g x) = (f = g)       *)
(*---------------------------------------------------------------*)

let vEXT_CONV =  vSYM -| uncurry vX_FUN_EQ_CONV -|
      (vI $-$ (mk_eq -| (rator $-$ rator) -| dest_eq)) -| dest_forall;;

(*----------------------------------------------------------------------------*)
(* EQUAL_TAC - Strip down to unequal core (usually too enthusiastic)          *)
(*----------------------------------------------------------------------------*)

let vEQUAL_TAC = vREPEAT(vFIRST [vAP_TERM_TAC; vAP_THM_TAC; vABS_TAC]);;

(*----------------------------------------------------------------------------*)
(* X_BETA_CONV `v` `tm[v]` = |- tm[v] = (\v. tm[v]) v                         *)
(*----------------------------------------------------------------------------*)

let vX_BETA_CONV v tm =
  vSYM(vBETA_CONV(mk_comb(mk_abs(v,tm),v)));;

(*----------------------------------------------------------------------------*)
(* EXACT_CONV - Rewrite with theorem matching exactly one in a list           *)
(*----------------------------------------------------------------------------*)

let vEXACT_CONV =
  vONCE_DEPTH_CONV -| vFIRST_CONV -|
  map (fun t -> vK t -| check((=)(lhs(concl t))));;

(*----------------------------------------------------------------------------*)
(* Rather ad-hoc higher-order fiddling conversion                             *)
(* |- (\x. f t1[x] ... tn[x]) = (\x. f ((\x. t1[x]) x) ... ((\x. tn[x]) x))   *)
(*----------------------------------------------------------------------------*)

let vHABS_CONV tm =
  let v,bod = dest_abs tm in
  let hop,pl = strip_comb bod in
  let eql = rev(map (vX_BETA_CONV v) pl) in
  vABS v (itlist (vC(curry vMK_COMB)) eql (vREFL hop));;

(*----------------------------------------------------------------------------*)
(* Expand an abbreviation                                                     *)
(*----------------------------------------------------------------------------*)

let vEXPAND_TAC s = vFIRST_ASSUM(vSUBST1_TAC -| vSYM -|
  check((=) s -| fst -| dest_var -| rhs -| concl)) ----> vBETA_TAC;;

(* ------------------------------------------------------------------------- *)
(* Set up the reals.                                                         *)
(* ------------------------------------------------------------------------- *)

prioritize_real();;

let%a real_le = prove
 ([%q {|!x y. x <= y <=> ~(y < x)|} ],
  vREWRITE_TAC[vREAL_NOT_LT]);;

(* ------------------------------------------------------------------------- *)
(* Link a few theorems.                                                      *)
(* ------------------------------------------------------------------------- *)

let%a vREAL_10 = vREAL_ARITH [%q {|~(&1 = &0)|} ];;

let vREAL_LDISTRIB = vREAL_ADD_LDISTRIB;;

let%a  vREAL_LT_IADD = vREAL_ARITH [%q {|!x y z. y < z ==> x + y < x + z|} ];;

(*----------------------------------------------------------------------------*)
(* Prove lots of boring field theorems                                        *)
(*----------------------------------------------------------------------------*)

let%a vREAL_MUL_RID = prove(
  [%q {|!x. x * &1 = x|} ],
  vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_MUL_LID);;

let%a vREAL_MUL_RINV = prove(
  [%q {|!x. ~(x = &0) ==> (x * (inv x) = &1)|} ],
  vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_MUL_LINV);;

let%a vREAL_RDISTRIB = prove(
  [%q {|!x y z. (x + y) * z = (x * z) + (y * z)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_LDISTRIB);;

let%a vREAL_EQ_LADD = prove(
  [%q {|!x y z. (x + y = x + z) <=> (y = z)|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|(+) (-- x)|} ]) ---->
    vREWRITE_TAC[vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_LID];
    vDISCH_THEN vSUBST1_TAC ----> vREFL_TAC]);;

let%a vREAL_EQ_RADD = prove(
  [%q {|!x y z. (x + z = y + z) <=> (x = y)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_EQ_LADD);;

let%a vREAL_ADD_LID_UNIQ = prove(
  [%q {|!x y. (x + y = y) <=> (x = &0)|} ],
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vREAL_ADD_LID]
  ----> vMATCH_ACCEPT_TAC vREAL_EQ_RADD);;

let%a vREAL_ADD_RID_UNIQ = prove(
  [%q {|!x y. (x + y = x) <=> (y = &0)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_ADD_LID_UNIQ);;

let%a vREAL_LNEG_UNIQ = prove(
  [%q {|!x y. (x + y = &0) <=> (x = --y)|} ],
  vREPEAT vGEN_TAC ----> vSUBST1_TAC (vSYM(vSPEC [%q {|y:real|} ] vREAL_ADD_LINV)) ---->
  vMATCH_ACCEPT_TAC vREAL_EQ_RADD);;

let%a vREAL_RNEG_UNIQ = prove(
  [%q {|!x y. (x + y = &0) <=> (y = --x)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_LNEG_UNIQ);;

let%a vREAL_NEG_ADD = prove(
  [%q {|!x y. --(x + y) = (--x) + (--y)|} ],
  vREPEAT vGEN_TAC ----> vCONV_TAC vSYM_CONV ---->
  vREWRITE_TAC[vGSYM vREAL_LNEG_UNIQ] ---->
  vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
    [%q {|(a + b) + (c + d) = (a + c) + (b + d)|} ]] ---->
  vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID]);;

let%a vREAL_MUL_LZERO = prove(
  [%q {|!x. &0 * x = &0|} ],
  vGEN_TAC ----> vSUBST1_TAC(vSYM(vSPECL [[%q {|&0 * x|} ]; [%q {|&0 * x|} ]] vREAL_ADD_LID_UNIQ))
  ----> vREWRITE_TAC[vGSYM vREAL_RDISTRIB; vREAL_ADD_LID]);;

let%a vREAL_MUL_RZERO = prove(
  [%q {|!x. x * &0 = &0|} ],
  vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_MUL_LZERO);;

let%a vREAL_NEG_LMUL = prove(
  [%q {|!x y. --(x * y) = (--x) * y|} ],
  vREPEAT vGEN_TAC ----> vCONV_TAC vSYM_CONV ---->
  vREWRITE_TAC[vGSYM vREAL_LNEG_UNIQ; vGSYM vREAL_RDISTRIB;
              vREAL_ADD_LINV; vREAL_MUL_LZERO]);;

let%a vREAL_NEG_RMUL = prove(
  [%q {|!x y. --(x * y) = x * (--y)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_NEG_LMUL);;

let%a vREAL_NEG_NEG = prove(
  [%q {|!x. --(--x) = x|} ],
  vGEN_TAC ----> vCONV_TAC vSYM_CONV ---->
  vREWRITE_TAC[vGSYM vREAL_LNEG_UNIQ; vREAL_ADD_RINV]);;

let%a vREAL_NEG_MUL2 = prove(
  [%q {|!x y. (--x) * (--y) = x * y|} ],
  vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL; vREAL_NEG_NEG]);;

let%a vREAL_LT_LADD = prove(
  [%q {|!x y z. (x + y) < (x + z) <=> y < z|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vSPEC [%q {|--x|} ] -| vMATCH_MP vREAL_LT_IADD) ---->
    vREWRITE_TAC[vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_LID];
    vMATCH_ACCEPT_TAC vREAL_LT_IADD]);;

let%a vREAL_LT_RADD = prove(
  [%q {|!x y z. (x + z) < (y + z) <=> x < y|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_LT_LADD);;

let%a vREAL_NOT_LT = prove(
  [%q {|!x y. ~(x < y) <=> y <= x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_le]);;

let%a vREAL_LT_ANTISYM = prove(
  [%q {|!x y. ~(x < y /\ y < x)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_TRANS) ---->
  vREWRITE_TAC[vREAL_LT_REFL]);;

let%a vREAL_LT_GT = prove(
  [%q {|!x y. x < y ==> ~(y < x)|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(fun th -> vDISCH_THEN(vMP_TAC -| vCONJ th)) ---->
  vREWRITE_TAC[vREAL_LT_ANTISYM]);;

let%a vREAL_NOT_LE = prove(
  [%q {|!x y. ~(x <= y) <=> y < x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_le]);;

let%a vREAL_LE_TOTAL = prove(
  [%q {|!x y. x <= y \/ y <= x|} ],
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[real_le; vGSYM vDE_MORGAN_THM; vREAL_LT_ANTISYM]);;

let%a vREAL_LE_REFL = prove(
  [%q {|!x. x <= x|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_le; vREAL_LT_REFL]);;

let%a vREAL_LE_LT = prove(
  [%q {|!x y. x <= y <=> x < y \/ (x = y)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_le] ----> vEQ_TAC ++-->
   [vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC
     (vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vREAL_LT_TOTAL) ----> vASM_REWRITE_TAC[];
    vDISCH_THEN(vDISJ_CASES_THEN2
     ((---->) (vMATCH_MP_TAC vREAL_LT_GT) -| vACCEPT_TAC) vSUBST1_TAC) ---->
    vMATCH_ACCEPT_TAC vREAL_LT_REFL]);;

let%a vREAL_LT_LE = prove(
  [%q {|!x y. x < y <=> x <= y /\ ~(x = y)|} ],
  let lemma = vTAUT [%q {|~(a /\ ~a)|} ] in
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_LE_LT; vRIGHT_AND_OVER_OR; lemma]
  ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM vMP_TAC ----> vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[] ---->
  vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vREAL_LT_REFL]);;

let%a vREAL_LT_IMP_LE = prove(
  [%q {|!x y. x < y ==> x <= y|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vASM_REWRITE_TAC[vREAL_LE_LT]);;

let%a vREAL_LTE_TRANS = prove(
  [%q {|!x y z. x < y /\ y <= z ==> x < z|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_LE_LT; vLEFT_AND_OVER_OR] ---->
  vDISCH_THEN(vDISJ_CASES_THEN2 (vACCEPT_TAC -| vMATCH_MP vREAL_LT_TRANS)
    (vCONJUNCTS_THEN2 vMP_TAC vSUBST1_TAC)) ----> vREWRITE_TAC[]);;

let%a vREAL_LE_TRANS = prove(
  [%q {|!x y z. x <= y /\ y <= z ==> x <= z|} ],
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vREAL_LE_LT] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC (vDISJ_CASES_THEN2 vASSUME_TAC vSUBST1_TAC))
  ----> vREWRITE_TAC[] ----> vDISCH_THEN(vMP_TAC -| vC vCONJ (vASSUME [%q {|y < z|} ])) ---->
  vDISCH_THEN(vACCEPT_TAC -| vMATCH_MP vREAL_LT_IMP_LE -| vMATCH_MP vREAL_LET_TRANS));;

let%a vREAL_NEG_LT0 = prove(
  [%q {|!x. (--x) < &0 <=> &0 < x|} ],
  vGEN_TAC ----> vSUBST1_TAC(vSYM(vSPECL [[%q {|--x|} ]; [%q {|&0|} ]; [%q {|x:real|} ]] vREAL_LT_RADD)) ---->
  vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID]);;

let%a vREAL_NEG_GT0 = prove(
  [%q {|!x. &0 < (--x) <=> x < &0|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_NEG_LT0; vREAL_NEG_NEG]);;

let%a vREAL_NEG_LE0 = prove(
  [%q {|!x. (--x) <= &0 <=> &0 <= x|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_le] ---->
  vREWRITE_TAC[vREAL_NEG_GT0]);;

let%a vREAL_NEG_GE0 = prove(
  [%q {|!x. &0 <= (--x) <=> x <= &0|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_le] ---->
  vREWRITE_TAC[vREAL_NEG_LT0]);;

let%a vREAL_LT_NEGTOTAL = prove(
  [%q {|!x. (x = &0) \/ (&0 < x) \/ (&0 < --x)|} ],
  vGEN_TAC ----> vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC
   (vSPECL [[%q {|x:real|} ]; [%q {|&0|} ]] vREAL_LT_TOTAL) ---->
  vASM_REWRITE_TAC[vSYM(vREWRITE_RULE[vREAL_NEG_NEG] (vSPEC [%q {|--x|} ] vREAL_NEG_LT0))]);;

let%a vREAL_LE_NEGTOTAL = prove(
  [%q {|!x. &0 <= x \/ &0 <= --x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vREAL_LE_LT] ---->
  vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC (vSPEC [%q {|x:real|} ] vREAL_LT_NEGTOTAL) ---->
  vASM_REWRITE_TAC[]);;

let%a vREAL_LE_MUL = prove(
  [%q {|!x y. &0 <= x /\ &0 <= y ==> &0 <= (x * y)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_LE_LT] ---->
  vMAP_EVERY vASM_CASES_TAC [[%q {|&0 = x|} ]; [%q {|&0 = y|} ]] ---->
  vASM_REWRITE_TAC[] ----> vTRY(vFIRST_ASSUM(vSUBST1_TAC -| vSYM)) ---->
  vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_MUL_RZERO] ---->
  vDISCH_TAC ----> vDISJ1_TAC ----> vMATCH_MP_TAC vREAL_LT_MUL ---->
  vASM_REWRITE_TAC[]);;

let%a vREAL_LE_SQUARE = prove(
  [%q {|!x. &0 <= x * x|} ],
  vGEN_TAC ----> vDISJ_CASES_TAC (vSPEC [%q {|x:real|} ] vREAL_LE_NEGTOTAL) ---->
  vPOP_ASSUM(vMP_TAC -| vMATCH_MP vREAL_LE_MUL -| vW vCONJ) ---->
  vREWRITE_TAC[vGSYM vREAL_NEG_RMUL; vGSYM vREAL_NEG_LMUL; vREAL_NEG_NEG]);;

let%a vREAL_LT_01 = prove(
  [%q {|&0 < &1|} ],
  vREWRITE_TAC[vREAL_LT_LE; vREAL_LE_01] ---->
  vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
  vREWRITE_TAC[vREAL_10]);;

let%a vREAL_LE_LADD = prove(
  [%q {|!x y z. (x + y) <= (x + z) <=> y <= z|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_le] ---->
  vAP_TERM_TAC ----> vMATCH_ACCEPT_TAC vREAL_LT_LADD);;

let%a vREAL_LE_RADD = prove(
  [%q {|!x y z. (x + z) <= (y + z) <=> x <= y|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_le] ---->
  vAP_TERM_TAC ----> vMATCH_ACCEPT_TAC vREAL_LT_RADD);;

let%a vREAL_LT_ADD2 = prove(
  [%q {|!w x y z. w < x /\ y < z ==> (w + y) < (x + z)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|w + z|} ] ---->
  vASM_REWRITE_TAC[vREAL_LT_LADD; vREAL_LT_RADD]);;

let%a vREAL_LT_ADD = prove(
  [%q {|!x y. &0 < x /\ &0 < y ==> &0 < (x + y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_ADD2) ---->
  vREWRITE_TAC[vREAL_ADD_LID]);;

let%a vREAL_LT_ADDNEG = prove(
  [%q {|!x y z. y < (x + (--z)) <=> (y + z) < x|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPECL [[%q {|y:real|} ]; [%q {|x + (--z)|} ]; [%q {|z:real|} ]] vREAL_LT_RADD)) ---->
  vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_RID]);;

let%a vREAL_LT_ADDNEG2 = prove(
  [%q {|!x y z. (x + (--y)) < z <=> x < (z + y)|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPECL [[%q {|x + (-- y)|} ]; [%q {|z:real|} ]; [%q {|y:real|} ]] vREAL_LT_RADD)) ---->
  vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_RID]);;

let%a vREAL_LT_ADD1 = prove(
  [%q {|!x y. x <= y ==> x < (y + &1)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_LE_LT] ---->
  vDISCH_THEN vDISJ_CASES_TAC ++-->
   [vPOP_ASSUM(vMP_TAC -| vMATCH_MP vREAL_LT_ADD2 -| vC vCONJ vREAL_LT_01) ---->
    vREWRITE_TAC[vREAL_ADD_RID];
    vPOP_ASSUM vSUBST1_TAC ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_ADD_RID] ---->
    vREWRITE_TAC[vREAL_LT_LADD; vREAL_LT_01]]);;

let%a vREAL_SUB_ADD = prove(
  [%q {|!x y. (x - y) + y = x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub; vGSYM vREAL_ADD_ASSOC;
    vREAL_ADD_LINV; vREAL_ADD_RID]);;

let%a vREAL_SUB_ADD2 = prove(
  [%q {|!x y. y + (x - y) = x|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_SUB_ADD);;

let%a vREAL_SUB_REFL = prove(
  [%q {|!x. x - x = &0|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_sub; vREAL_ADD_RINV]);;

let%a vREAL_SUB_0 = prove(
  [%q {|!x y. (x - y = &0) <=> (x = y)|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vC vAP_THM [%q {|y:real|} ] -| vAP_TERM [%q {|(+)|} ]) ---->
    vREWRITE_TAC[vREAL_SUB_ADD; vREAL_ADD_LID];
    vDISCH_THEN vSUBST1_TAC ----> vMATCH_ACCEPT_TAC vREAL_SUB_REFL]);;

let%a vREAL_LE_DOUBLE = prove(
  [%q {|!x. &0 <= x + x <=> &0 <= x|} ],
  vGEN_TAC ----> vEQ_TAC ++-->
   [vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vREAL_NOT_LE] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_ADD2 -| vW vCONJ);
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LE_ADD2 -| vW vCONJ)] ---->
  vREWRITE_TAC[vREAL_ADD_LID]);;

let%a vREAL_LE_NEGL = prove(
  [%q {|!x. (--x <= x) <=> (&0 <= x)|} ],
  vGEN_TAC ----> vSUBST1_TAC (vSYM(vSPECL [[%q {|x:real|} ]; [%q {|--x|} ]; [%q {|x:real|} ]] vREAL_LE_LADD))
  ----> vREWRITE_TAC[vREAL_ADD_RINV; vREAL_LE_DOUBLE]);;

let%a vREAL_LE_NEGR = prove(
  [%q {|!x. (x <= --x) <=> (x <= &0)|} ],
  vGEN_TAC ----> vSUBST1_TAC(vSYM(vSPEC [%q {|x:real|} ] vREAL_NEG_NEG)) ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_LE_NEGL] ----> vREWRITE_TAC[vREAL_NEG_GE0] ---->
  vREWRITE_TAC[vREAL_NEG_NEG]);;

let%a vREAL_NEG_EQ0 = prove(
  [%q {|!x. (--x = &0) <=> (x = &0)|} ],
  vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|(+) x|} ]);
    vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|(+) (--x)|} ])] ---->
  vREWRITE_TAC[vREAL_ADD_RINV; vREAL_ADD_LINV; vREAL_ADD_RID] ---->
  vDISCH_THEN vSUBST1_TAC ----> vREFL_TAC);;

let%a vREAL_NEG_0 = prove(
  [%q {|--(&0) = &0|} ],
  vREWRITE_TAC[vREAL_NEG_EQ0]);;

let%a vREAL_NEG_SUB = prove(
  [%q {|!x y. --(x - y) = y - x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub; vREAL_NEG_ADD; vREAL_NEG_NEG] ---->
  vMATCH_ACCEPT_TAC vREAL_ADD_SYM);;

let%a vREAL_SUB_LT = prove(
  [%q {|!x y. &0 < x - y <=> y < x|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPECL [[%q {|&0|} ]; [%q {|x - y|} ]; [%q {|y:real|} ]] vREAL_LT_RADD)) ---->
  vREWRITE_TAC[vREAL_SUB_ADD; vREAL_ADD_LID]);;

let%a vREAL_SUB_LE = prove(
  [%q {|!x y. &0 <= (x - y) <=> y <= x|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPECL [[%q {|&0|} ]; [%q {|x - y|} ]; [%q {|y:real|} ]] vREAL_LE_RADD)) ---->
  vREWRITE_TAC[vREAL_SUB_ADD; vREAL_ADD_LID]);;

let%a vREAL_EQ_LMUL = prove(
  [%q {|!x y z. (x * y = x * z) <=> (x = &0) \/ (y = z)|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|(*) (inv x)|} ]) ---->
    vASM_CASES_TAC [%q {|x = &0|} ] ----> vASM_REWRITE_TAC[] ---->
    vPOP_ASSUM(fun th -> vREWRITE_TAC
      [vREAL_MUL_ASSOC; vMATCH_MP vREAL_MUL_LINV th]) ---->
    vREWRITE_TAC[vREAL_MUL_LID];
    vDISCH_THEN(vDISJ_CASES_THEN vSUBST1_TAC) ---->
    vREWRITE_TAC[vREAL_MUL_LZERO]]);;

let%a vREAL_EQ_RMUL = prove(
  [%q {|!x y z. (x * z = y * z) <=> (z = &0) \/ (x = y)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_EQ_LMUL);;

let%a vREAL_SUB_LDISTRIB = prove(
  [%q {|!x y z. x * (y - z) = (x * y) - (x * z)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub; vREAL_LDISTRIB; vREAL_NEG_RMUL]);;

let%a vREAL_SUB_RDISTRIB = prove(
  [%q {|!x y z. (x - y) * z = (x * z) - (y * z)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_SUB_LDISTRIB);;

let%a vREAL_NEG_EQ = prove(
  [%q {|!x y. (--x = y) <=> (x = --y)|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vSUBST1_TAC -| vSYM); vDISCH_THEN vSUBST1_TAC] ---->
  vREWRITE_TAC[vREAL_NEG_NEG]);;

let%a vREAL_NEG_MINUS1 = prove(
  [%q {|!x. --x = (--(&1)) * x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_NEG_LMUL] ---->
  vREWRITE_TAC[vREAL_MUL_LID]);;

let%a vREAL_INV_NZ = prove(
  [%q {|!x. ~(x = &0) ==> ~(inv x = &0)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vDISCH_THEN(vMP_TAC -| vC vAP_THM [%q {|x:real|} ] -| vAP_TERM [%q {|(*)|} ]) ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV th]) ---->
  vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_10]);;

let%a vREAL_INVINV = prove(
  [%q {|!x. ~(x = &0) ==> (inv (inv x) = x)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vREAL_MUL_RINV) ---->
  vASM_CASES_TAC [%q {|inv x = &0|} ] ---->
  vASM_REWRITE_TAC[vREAL_MUL_RZERO; vGSYM vREAL_10] ---->
  vMP_TAC(vSPECL [[%q {|inv(inv x)|} ]; [%q {|x:real|} ]; [%q {|inv x|} ]] vREAL_EQ_RMUL)
  ----> vASM_REWRITE_TAC[] ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vDISCH_THEN vSUBST1_TAC ----> vMATCH_MP_TAC vREAL_MUL_LINV ---->
  vFIRST_ASSUM vACCEPT_TAC);;

let%a vREAL_LT_IMP_NE = prove(
  [%q {|!x y. x < y ==> ~(x = y)|} ],
  vREPEAT vGEN_TAC ----> vCONV_TAC vCONTRAPOS_CONV ---->
  vREWRITE_TAC[] ----> vDISCH_THEN vSUBST1_TAC ---->
  vREWRITE_TAC[vREAL_LT_REFL]);;

let%a vREAL_INV_POS = prove(
  [%q {|!x. &0 < x ==> &0 < inv x|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREPEAT_TCL vDISJ_CASES_THEN
   vMP_TAC (vSPECL [[%q {|inv x|} ]; [%q {|&0|} ]] vREAL_LT_TOTAL) ++-->
   [vPOP_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_INV_NZ -|
              vGSYM -| vMATCH_MP vREAL_LT_IMP_NE) ----> vASM_REWRITE_TAC[];
    vONCE_REWRITE_TAC[vGSYM vREAL_NEG_GT0] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_MUL -| vC vCONJ (vASSUME [%q {|&0 < x|} ])) ---->
    vREWRITE_TAC[vGSYM vREAL_NEG_LMUL] ---->
    vPOP_ASSUM(fun th -> vREWRITE_TAC
     [vMATCH_MP vREAL_MUL_LINV (vGSYM (vMATCH_MP vREAL_LT_IMP_NE th))]) ---->
    vREWRITE_TAC[vREAL_NEG_GT0] ----> vDISCH_THEN(vMP_TAC -| vCONJ vREAL_LT_01) ---->
    vREWRITE_TAC[vREAL_LT_ANTISYM];
    vREWRITE_TAC[]]);;

let%a vREAL_LT_LMUL_0 = prove(
  [%q {|!x y. &0 < x ==> (&0 < (x * y) <=> &0 < y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vEQ_TAC ++-->
   [vFIRST_ASSUM(fun th ->
      vDISCH_THEN(vMP_TAC -| vCONJ (vMATCH_MP vREAL_INV_POS th))) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_MUL) ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC
      [vMATCH_MP vREAL_MUL_LINV (vGSYM (vMATCH_MP vREAL_LT_IMP_NE th))]) ---->
    vREWRITE_TAC[vREAL_MUL_LID];
    vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LT_MUL ----> vASM_REWRITE_TAC[]]);;

let%a vREAL_LT_RMUL_0 = prove(
  [%q {|!x y. &0 < y ==> (&0 < (x * y) <=> &0 < x)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_LT_LMUL_0);;

let%a vREAL_LT_LMUL_EQ = prove(
  [%q {|!x y z. &0 < x ==> ((x * y) < (x * z) <=> y < z)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ---->
  vREWRITE_TAC[vGSYM vREAL_SUB_LDISTRIB] ---->
  vPOP_ASSUM vMP_TAC ----> vMATCH_ACCEPT_TAC vREAL_LT_LMUL_0);;

let%a vREAL_LT_RMUL_EQ = prove(
  [%q {|!x y z. &0 < z ==> ((x * z) < (y * z) <=> x < y)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_LT_LMUL_EQ);;

let%a vREAL_LT_RMUL_IMP = prove(
  [%q {|!x y z. x < y /\ &0 < z ==> (x * z) < (y * z)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vPOP_ASSUM(fun th -> vREWRITE_TAC[vGEN_ALL(vMATCH_MP vREAL_LT_RMUL_EQ th)]));;

let%a vREAL_LT_LMUL_IMP = prove(
  [%q {|!x y z. y < z  /\ &0 < x ==> (x * y) < (x * z)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vPOP_ASSUM(fun th -> vREWRITE_TAC[vGEN_ALL(vMATCH_MP vREAL_LT_LMUL_EQ th)]));;

let%a vREAL_LINV_UNIQ = prove(
  [%q {|!x y. (x * y = &1) ==> (x = inv y)|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|x = &0|} ] ---->
  vASM_REWRITE_TAC[vREAL_MUL_LZERO; vGSYM vREAL_10] ---->
  vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|(*) (inv x)|} ]) ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV th]) ---->
  vREWRITE_TAC[vREAL_MUL_LID; vREAL_MUL_RID] ---->
  vDISCH_THEN vSUBST1_TAC ----> vCONV_TAC vSYM_CONV ---->
  vPOP_ASSUM vMP_TAC ----> vMATCH_ACCEPT_TAC vREAL_INVINV);;

let%a vREAL_RINV_UNIQ = prove(
  [%q {|!x y. (x * y = &1) ==> (y = inv x)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_LINV_UNIQ);;

let%a vREAL_NEG_INV = prove(
  [%q {|!x. ~(x = &0) ==> (--(inv x) = inv(--x))|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LINV_UNIQ ---->
  vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL] ---->
  vPOP_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV th]) ---->
  vREWRITE_TAC[vREAL_NEG_NEG]);;

let%a vREAL_INV_1OVER = prove(
  [%q {|!x. inv x = &1 / x|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_div; vREAL_MUL_LID]);;

(*----------------------------------------------------------------------------*)
(* Prove homomorphisms for the inclusion map                                  *)
(*----------------------------------------------------------------------------*)

let%a vREAL = prove(
  [%q {|!n. &(SUC n) = &n + &1|} ],
  vREWRITE_TAC[vADD1; vREAL_OF_NUM_ADD]);;

let%a vREAL_POS = prove(
  [%q {|!n. &0 <= &n|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[vREAL_LE_REFL] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|&n|} ] ----> vASM_REWRITE_TAC[vREAL] ---->
  vREWRITE_TAC[vREAL_LE_ADDR; vREAL_LE_01]);;

let%a vREAL_LE = prove(
  [%q {|!m n. &m <= &n <=> m <= n|} ],
  vREPEAT vINDUCT_TAC ----> vASM_REWRITE_TAC
   [vREAL; vREAL_LE_RADD; vLE_0; vLE_SUC; vREAL_LE_REFL] ---->
  vREWRITE_TAC[vGSYM vNOT_LT; vLT_0] ++-->
   [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|&n|} ] ---->
    vASM_REWRITE_TAC[vLE_0; vREAL_LE_ADDR; vREAL_LE_01];
    vDISCH_THEN(vMP_TAC -| vC vCONJ (vSPEC [%q {|m:num|} ] vREAL_POS)) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LE_TRANS) ---->
    vREWRITE_TAC[vREAL_NOT_LE; vREAL_LT_ADDR; vREAL_LT_01]]);;

let%a vREAL_LT = prove(
  [%q {|!m n. &m < &n <=> m < n|} ],
  vREPEAT vGEN_TAC ----> vMATCH_ACCEPT_TAC ((vREWRITE_RULE[] -| vAP_TERM [%q {|(~)|} ] -|
    vREWRITE_RULE[vGSYM vNOT_LT; vGSYM vREAL_NOT_LT]) (vSPEC_ALL vREAL_LE)));;

let%a vREAL_INJ = prove(
  [%q {|!m n. (&m = &n) <=> (m = n)|} ],
  let th = prove([%q {|(m = n) <=> m:num <= n /\ n <= m|} ],
                 vEQ_TAC ++-->
                  [vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vLE_REFL];
                   vMATCH_ACCEPT_TAC vLESS_EQUAL_ANTISYM]) in
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[th; vGSYM vREAL_LE_ANTISYM; vREAL_LE]);;

let%a vREAL_ADD = prove(
  [%q {|!m n. &m + &n = &(m + n)|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[vREAL; vADD; vREAL_ADD_LID] ---->
  vRULE_ASSUM_TAC vGSYM ----> vGEN_TAC ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vREAL_ADD_AC]);;

let%a vREAL_MUL = prove(
  [%q {|!m n. &m * &n = &(m * n)|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[vREAL_MUL_LZERO; vMULT_CLAUSES; vREAL;
    vGSYM vREAL_ADD; vREAL_RDISTRIB] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vGSYM th]) ---->
  vREWRITE_TAC[vREAL_MUL_LID]);;

(*----------------------------------------------------------------------------*)
(* Now more theorems                                                          *)
(*----------------------------------------------------------------------------*)

let%a vREAL_INV1 = prove(
  [%q {|inv(&1) = &1|} ],
  vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_LINV_UNIQ ---->
  vREWRITE_TAC[vREAL_MUL_LID]);;

let%a vREAL_DIV_LZERO = prove(
  [%q {|!x. &0 / x = &0|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_div; vREAL_MUL_LZERO]);;

let%a vREAL_LT_NZ = prove(
  [%q {|!n. ~(&n = &0) <=> (&0 < &n)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vREAL_LT_LE] ---->
  vCONV_TAC(vRAND_CONV(vONCE_DEPTH_CONV vSYM_CONV)) ---->
  vASM_CASES_TAC [%q {|&n = &0|} ] ----> vASM_REWRITE_TAC[vREAL_LE_REFL; vREAL_POS]);;

let%a vREAL_NZ_IMP_LT = prove(
  [%q {|!n. ~(n = 0) ==> &0 < &n|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_INJ; vREAL_LT_NZ]);;

let%a vREAL_LT_RDIV_0 = prove(
  [%q {|!y z. &0 < z ==> (&0 < (y / z) <=> &0 < y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[real_div] ----> vMATCH_MP_TAC vREAL_LT_RMUL_0 ---->
  vMATCH_MP_TAC vREAL_INV_POS ----> vPOP_ASSUM vACCEPT_TAC);;

let%a vREAL_LT_RDIV = prove(
  [%q {|!x y z. &0 < z ==> ((x / z) < (y / z) <=> x < y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[real_div] ----> vMATCH_MP_TAC vREAL_LT_RMUL_EQ ---->
  vMATCH_MP_TAC vREAL_INV_POS ----> vPOP_ASSUM vACCEPT_TAC);;

let%a vREAL_LT_FRACTION_0 = prove(
  [%q {|!n d. ~(n = 0) ==> (&0 < (d / &n) <=> &0 < d)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LT_RDIV_0 ---->
  vASM_REWRITE_TAC[vGSYM vREAL_LT_NZ; vREAL_INJ]);;

let%a vREAL_LT_MULTIPLE = prove(
  [%q {|!n d. 1 < n ==> (d < (&n * d) <=> &0 < d)|} ],
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vINDUCT_TAC ++-->
   [vREWRITE_TAC[num_CONV [%q {|1|} ]; vNOT_LESS_0];
    vPOP_ASSUM vMP_TAC ----> vASM_CASES_TAC [%q {|1 < n|} ] ---->
    vASM_REWRITE_TAC[] ++-->
     [vDISCH_TAC ----> vGEN_TAC ----> vDISCH_THEN(vK vALL_TAC) ---->
      vREWRITE_TAC[vREAL; vREAL_LDISTRIB; vREAL_MUL_RID; vREAL_LT_ADDL] ---->
      vMATCH_MP_TAC vREAL_LT_RMUL_0 ----> vREWRITE_TAC[vREAL_LT] ---->
      vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|1|} ] ---->
      vASM_REWRITE_TAC[] ----> vREWRITE_TAC[num_CONV [%q {|1|} ]; vLT_0];
      vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vLESS_LEMMA1) ---->
      vASM_REWRITE_TAC[] ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
      vREWRITE_TAC[vREAL; vREAL_LDISTRIB; vREAL_MUL_RID] ---->
      vREWRITE_TAC[vREAL_LT_ADDL]]]);;

let%a vREAL_LT_FRACTION = prove(
  [%q {|!n d. (1 < n) ==> ((d / &n) < d <=> &0 < d)|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|n = 0|} ] ---->
  vASM_REWRITE_TAC[vNOT_LESS_0] ----> vDISCH_TAC ---->
  vUNDISCH_TAC [%q {|1 < n|} ] ---->
  vFIRST_ASSUM(fun th -> let th1 = vREWRITE_RULE[vGSYM vREAL_INJ] th in
    vMAP_EVERY vASSUME_TAC [th1; vREWRITE_RULE[vREAL_LT_NZ] th1]) ---->
  vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV)
                     [vGSYM(vMATCH_MP vREAL_LT_RMUL_EQ th)]) ---->
  vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV th]) ---->
  vREWRITE_TAC[vREAL_MUL_RID] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_LT_MULTIPLE);;

let%a vREAL_LT_HALF1 = prove(
  [%q {|!d. &0 < (d / &2) <=> &0 < d|} ],
  vGEN_TAC ----> vMATCH_MP_TAC vREAL_LT_FRACTION_0 ---->
  vREWRITE_TAC[num_CONV [%q {|2|} ]; vNOT_SUC]);;

let%a vREAL_LT_HALF2 = prove(
  [%q {|!d. (d / &2) < d <=> &0 < d|} ],
  vGEN_TAC ----> vMATCH_MP_TAC vREAL_LT_FRACTION ---->
  vCONV_TAC(vRAND_CONV num_CONV) ---->
  vREWRITE_TAC[vLESS_SUC_REFL]);;

let%a vREAL_DOUBLE = prove(
  [%q {|!x. x + x = &2 * x|} ],
  vGEN_TAC ----> vREWRITE_TAC[num_CONV [%q {|2|} ]; vREAL] ---->
  vREWRITE_TAC[vREAL_RDISTRIB; vREAL_MUL_LID]);;

let%a vREAL_HALF_DOUBLE = prove(
  [%q {|!x. (x / &2) + (x / &2) = x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vREAL_DOUBLE] ---->
  vMATCH_MP_TAC vREAL_DIV_LMUL ----> vREWRITE_TAC[vREAL_INJ] ---->
  vREWRITE_TAC[num_CONV [%q {|2|} ]; vNOT_SUC]);;

let%a vREAL_SUB_SUB = prove(
  [%q {|!x y. (x - y) - x = --y|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub] ---->
  vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
    [%q {|(a + b) + c = (c + a) + b|} ]] ---->
  vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID]);;

let%a vREAL_LT_ADD_SUB = prove(
  [%q {|!x y z. (x + y) < z <=> x < (z - y)|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPECL [[%q {|x:real|} ]; [%q {|z - y|} ]; [%q {|y:real|} ]] vREAL_LT_RADD)) ---->
  vREWRITE_TAC[vREAL_SUB_ADD]);;

let%a vREAL_LT_SUB_RADD = prove(
  [%q {|!x y z. (x - y) < z <=> x < z + y|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPECL [[%q {|x - y|} ]; [%q {|z:real|} ]; [%q {|y:real|} ]] vREAL_LT_RADD)) ---->
  vREWRITE_TAC[vREAL_SUB_ADD]);;

let%a vREAL_LT_SUB_LADD = prove(
  [%q {|!x y z. x < (y - z) <=> (x + z) < y|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPECL [[%q {|x + z|} ]; [%q {|y:real|} ]; [%q {|--z|} ]] vREAL_LT_RADD)) ---->
  vREWRITE_TAC[real_sub; vGSYM vREAL_ADD_ASSOC; vREAL_ADD_RINV; vREAL_ADD_RID]);;

let%a vREAL_LE_SUB_LADD = prove(
  [%q {|!x y z. x <= (y - z) <=> (x + z) <= y|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_NOT_LT; vREAL_LT_SUB_RADD]);;

let%a vREAL_LE_SUB_RADD = prove(
  [%q {|!x y z. (x - y) <= z <=> x <= z + y|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_NOT_LT; vREAL_LT_SUB_LADD]);;

let%a vREAL_LT_NEG2 = prove(
  [%q {|!x y. --x < --y <=> y < x|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPECL[[%q {|--x|} ]; [%q {|--y|} ]; [%q {|x + y|} ]] vREAL_LT_RADD)) ---->
  vREWRITE_TAC[vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_LID] ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vREWRITE_TAC[vREAL_ADD_ASSOC; vREAL_ADD_RINV; vREAL_ADD_LID]);;

let%a vREAL_LE_NEG2 = prove(
  [%q {|!x y. --x <= --y <=> y <= x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_NOT_LT] ---->
  vREWRITE_TAC[vREAL_LT_NEG2]);;

let%a vREAL_SUB_LZERO = prove(
  [%q {|!x. &0 - x = --x|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_sub; vREAL_ADD_LID]);;

let%a vREAL_SUB_RZERO = prove(
  [%q {|!x. x - &0 = x|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_sub; vREAL_NEG_0; vREAL_ADD_RID]);;

let%a vREAL_LTE_ADD2 = prove(
  [%q {|!w x y z. w < x /\ y <= z ==> (w + y) < (x + z)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vCONJ_SYM] ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vMATCH_ACCEPT_TAC vREAL_LET_ADD2);;

let%a vREAL_LTE_ADD = prove(
  [%q {|!x y. &0 < x /\ &0 <= y ==> &0 < (x + y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vSUBST1_TAC(vSYM(vSPEC [%q {|&0|} ] vREAL_ADD_LID)) ---->
  vMATCH_MP_TAC vREAL_LTE_ADD2 ---->
  vASM_REWRITE_TAC[]);;

let%a vREAL_LT_MUL2_ALT = prove(
  [%q {|!x1 x2 y1 y2. &0 <= x1 /\ &0 <= y1 /\ x1 < x2 /\ y1 < y2 ==>
        (x1 * y1) < (x2 * y2)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ---->
  vREWRITE_TAC[vREAL_SUB_RZERO] ---->
  vSUBGOAL_THEN [%q {|!a b c d.
    (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))|} ]
  vMP_TAC ++-->
   [vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub] ---->
    vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
      [%q {|(a + b) + (c + d) = (b + c) + (a + d)|} ]] ---->
    vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID];
    vDISCH_THEN(fun th -> vONCE_REWRITE_TAC[th]) ---->
    vREWRITE_TAC[vGSYM vREAL_SUB_LDISTRIB; vGSYM vREAL_SUB_RDISTRIB] ---->
    vDISCH_THEN vSTRIP_ASSUME_TAC ---->
    vMATCH_MP_TAC vREAL_LTE_ADD ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_LT_MUL ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x1:real|} ] ---->
      vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ---->
      vASM_REWRITE_TAC[];
      vMATCH_MP_TAC vREAL_LE_MUL ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]]]);;

let%a vREAL_SUB_LNEG = prove(
  [%q {|!x y. (--x) - y = --(x + y)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub; vREAL_NEG_ADD]);;

let%a vREAL_SUB_RNEG = prove(
  [%q {|!x y. x - (--y) = x + y|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub; vREAL_NEG_NEG]);;

let%a vREAL_SUB_NEG2 = prove(
  [%q {|!x y. (--x) - (--y) = y - x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_SUB_LNEG] ---->
  vREWRITE_TAC[real_sub; vREAL_NEG_ADD; vREAL_NEG_NEG] ---->
  vMATCH_ACCEPT_TAC vREAL_ADD_SYM);;

let%a vREAL_SUB_TRIANGLE = prove(
  [%q {|!a b c. (a - b) + (b - c) = a - c|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub] ---->
  vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
    [%q {|(a + b) + (c + d) = (b + c) + (a + d)|} ]] ---->
  vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID]);;

let%a vREAL_INV_MUL_WEAK = prove(
  [%q {|!x y. ~(x = &0) /\ ~(y = &0) ==>
             (inv(x * y) = inv(x) * inv(y))|} ],
  vREWRITE_TAC[vREAL_INV_MUL]);;

let%a vREAL_LE_LMUL_LOCAL = prove(
  [%q {|!x y z. &0 < x ==> ((x * y) <= (x * z) <=> y <= z)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_NOT_LT] ---->
  vAP_TERM_TAC ----> vMATCH_MP_TAC vREAL_LT_LMUL_EQ ----> vASM_REWRITE_TAC[]);;

let%a vREAL_LE_RMUL_EQ = prove(
  [%q {|!x y z. &0 < z ==> ((x * z) <= (y * z) <=> x <= y)|} ],
   vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
   vMATCH_ACCEPT_TAC vREAL_LE_LMUL_LOCAL);;

let%a vREAL_SUB_INV2 = prove(
  [%q {|!x y. ~(x = &0) /\ ~(y = &0) ==>
                (inv(x) - inv(y) = (y - x) / (x * y))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN vSTRIP_ASSUME_TAC ---->
  vREWRITE_TAC[real_div; vREAL_SUB_RDISTRIB] ---->
  vSUBGOAL_THEN [%q {|inv(x * y) = inv(x) * inv(y)|} ] vSUBST1_TAC ++-->
   [vMATCH_MP_TAC vREAL_INV_MUL_WEAK ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vEVERY_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_RINV th]) ---->
  vREWRITE_TAC[vREAL_MUL_LID] ----> vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
  vEVERY_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV th]) ---->
  vREWRITE_TAC[vREAL_MUL_LID]);;

let%a vREAL_SUB_SUB2 = prove(
  [%q {|!x y. x - (x - y) = y|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_NEG_NEG] ---->
  vAP_TERM_TAC ----> vREWRITE_TAC[vREAL_NEG_SUB; vREAL_SUB_SUB]);;

let%a vREAL_MEAN = prove(
  [%q {|!x y. x < y ==> ?z. x < z /\ z < y|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_DOWN -| vONCE_REWRITE_RULE[vGSYM vREAL_SUB_LT])
  ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|x + d|} ] ----> vASM_REWRITE_TAC[vREAL_LT_ADDR] ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vASM_REWRITE_TAC[vGSYM vREAL_LT_SUB_LADD]);;

let%a vREAL_EQ_LMUL2 = prove(
  [%q {|!x y z. ~(x = &0) ==> ((y = z) <=> (x * y = x * z))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]; [%q {|z:real|} ]] vREAL_EQ_LMUL) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN vSUBST_ALL_TAC ----> vREFL_TAC);;

let%a vREAL_LE_MUL2V = prove(
  [%q {|!x1 x2 y1 y2.
    (& 0) <= x1 /\ (& 0) <= y1 /\ x1 <= x2 /\ y1 <= y2 ==>
    (x1 * y1) <= (x2 * y2)|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSPECL [[%q {|x1:real|} ]; [%q {|x2:real|} ]] vREAL_LE_LT) ---->
  vASM_CASES_TAC [%q {|x1:real = x2|} ] ----> vASM_REWRITE_TAC[] ----> vSTRIP_TAC ++-->
   [vUNDISCH_TAC [%q {|&0 <= x2|} ] ---->
    vDISCH_THEN(vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
     [vFIRST_ASSUM(fun th -> vASM_REWRITE_TAC[vMATCH_MP vREAL_LE_LMUL_LOCAL th]);
      vSUBST1_TAC(vSYM(vASSUME [%q {|&0 = x2|} ])) ---->
      vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_LE_REFL]]; vALL_TAC] ---->
  vUNDISCH_TAC [%q {|y1 <= y2|} ] ---->
  vDISCH_THEN(vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
   [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vMATCH_MP_TAC vREAL_LT_MUL2_ALT ---->
    vASM_REWRITE_TAC[];
    vASM_REWRITE_TAC[]] ---->
  vUNDISCH_TAC [%q {|&0 <= y1|} ] ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
   [vFIRST_ASSUM(fun th -> vASM_REWRITE_TAC[vMATCH_MP vREAL_LE_RMUL_EQ th]) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
    vSUBST1_TAC(vSYM(vASSUME [%q {|&0 = y2|} ])) ---->
    vREWRITE_TAC[vREAL_MUL_RZERO; vREAL_LE_REFL]]);;

let%a vREAL_LE_LDIV = prove(
  [%q {|!x y z. &0 < x /\ y <= (z * x) ==> (y / x) <= z|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vMATCH_MP_TAC(vTAUT [%q {|(a = b) ==> a ==> b|} ]) ---->
  vSUBGOAL_THEN [%q {|y = (y / x) * x|} ] vMP_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_RMUL ---->
    vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vPOP_ASSUM vACCEPT_TAC;
    vDISCH_THEN(fun t -> vGEN_REWRITE_TAC (funpow 2 vLAND_CONV) [t])
    ----> vMATCH_MP_TAC vREAL_LE_RMUL_EQ ----> vPOP_ASSUM vACCEPT_TAC]);;

let%a vREAL_LE_RDIV = prove(
  [%q {|!x y z. &0 < x /\ (y * x) <= z ==> y <= (z / x)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vMATCH_MP_TAC vEQ_IMP ---->
  vSUBGOAL_THEN [%q {|z = (z / x) * x|} ] vMP_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_RMUL ---->
    vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vPOP_ASSUM vACCEPT_TAC;
    vDISCH_THEN(fun t -> vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [t])
    ----> vMATCH_MP_TAC vREAL_LE_RMUL_EQ ----> vPOP_ASSUM vACCEPT_TAC]);;

let%a vREAL_LT_1 = prove(
  [%q {|!x y. &0 <= x /\ x < y ==> (x / y) < &1|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|(x / y) < &1 <=> ((x / y) * y) < (&1 * y)|} ] vSUBST1_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_LT_RMUL_EQ ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
    vASM_REWRITE_TAC[];
    vSUBGOAL_THEN [%q {|(x / y) * y = x|} ] vSUBST1_TAC ++-->
     [vMATCH_MP_TAC vREAL_DIV_RMUL ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
      vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
      vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[];
      vASM_REWRITE_TAC[vREAL_MUL_LID]]]);;

let%a vREAL_LE_LMUL_IMP = prove(
  [%q {|!x y z. &0 <= x /\ y <= z ==> (x * y) <= (x * z)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vDISCH_THEN(vDISJ_CASES_TAC -| vREWRITE_RULE[vREAL_LE_LT]) ++-->
   [vFIRST_ASSUM(fun th -> vASM_REWRITE_TAC[vMATCH_MP vREAL_LE_LMUL_LOCAL th]);
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vREAL_MUL_LZERO] ---->
    vMATCH_ACCEPT_TAC vREAL_LE_REFL]);;

let%a vREAL_LE_RMUL_IMP = prove(
  [%q {|!x y z. &0 <= x /\ y <= z ==> (y * x) <= (z * x)|} ],
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vMATCH_ACCEPT_TAC vREAL_LE_LMUL_IMP);;

let%a vREAL_INV_LT1 = prove(
  [%q {|!x. &0 < x /\ x < &1 ==> &1 < inv(x)|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_INV_POS) ---->
  vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
  vPURE_REWRITE_TAC[vREAL_NOT_LT] ----> vREWRITE_TAC[vREAL_LE_LT] ---->
  vDISCH_THEN(vDISJ_CASES_THEN vMP_TAC) ++-->
   [vDISCH_TAC ---->
    vMP_TAC(vSPECL [[%q {|inv(x)|} ]; [%q {|&1|} ]; [%q {|x:real|} ]; [%q {|&1|} ]] vREAL_LT_MUL2_ALT) ---->
    vASM_REWRITE_TAC[vNOT_IMP] ----> vREPEAT vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
      vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
      vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_IMP_NE) ---->
      vREWRITE_TAC[vREAL_MUL_LID] ----> vMATCH_MP_TAC vREAL_MUL_LINV ---->
      vDISCH_THEN vSUBST_ALL_TAC ----> vUNDISCH_TAC [%q {|&0 < &0|} ] ---->
      vREWRITE_TAC[vREAL_LT_REFL]];
    vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|inv|} ]) ----> vREWRITE_TAC[vREAL_INV1] ---->
    vSUBGOAL_THEN [%q {|inv(inv x) = x|} ] vSUBST1_TAC ++-->
     [vMATCH_MP_TAC vREAL_INVINV ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
      vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vFIRST_ASSUM vACCEPT_TAC;
      vDISCH_THEN vSUBST_ALL_TAC ----> vUNDISCH_TAC [%q {|&1 < &1|} ] ---->
      vREWRITE_TAC[vREAL_LT_REFL]]]);;

let%a vREAL_LT_IMP_NZ = prove(
  [%q {|!x. &0 < x ==> ~(x = &0)|} ],
  vGEN_TAC ----> vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_NE) ---->
  vCONV_TAC(vRAND_CONV vSYM_CONV) ----> vPOP_ASSUM vACCEPT_TAC);;

let%a vREAL_EQ_RMUL_IMP = prove(
  [%q {|!x y z. ~(z = &0) /\ (x * z = y * z) ==> (x = y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vASM_REWRITE_TAC[vREAL_EQ_RMUL]);;

let%a vREAL_EQ_LMUL_IMP = prove(
  [%q {|!x y z. ~(x = &0) /\ (x * y = x * z) ==> (y = z)|} ],
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vMATCH_ACCEPT_TAC vREAL_EQ_RMUL_IMP);;

let%a vREAL_FACT_NZ = prove(
  [%q {|!n. ~(&(FACT n) = &0)|} ],
  vGEN_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ---->
  vREWRITE_TAC[vREAL_LT; vFACT_LT]);;

let%a vREAL_POSSQ = prove(
  [%q {|!x. &0 < (x * x) <=> ~(x = &0)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_NOT_LE] ----> vAP_TERM_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vC vCONJ (vSPEC [%q {|x:real|} ] vREAL_LE_SQUARE)) ---->
    vREWRITE_TAC[vREAL_LE_ANTISYM; vREAL_ENTIRE];
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_LE_REFL]]);;

let%a vREAL_SUMSQ = prove(
  [%q {|!x y. ((x * x) + (y * y) = &0) <=> (x = &0) /\ (y = &0)|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vDE_MORGAN_THM] ---->
    vDISCH_THEN vDISJ_CASES_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_NZ ++-->
     [vMATCH_MP_TAC vREAL_LTE_ADD; vMATCH_MP_TAC vREAL_LET_ADD] ---->
    vASM_REWRITE_TAC[vREAL_POSSQ; vREAL_LE_SQUARE];
    vDISCH_TAC ----> vASM_REWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_LID]]);;

let%a vREAL_EQ_NEG = prove(
  [%q {|!x y. (--x = --y) <=> (x = y)|} ],
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM; vREAL_LE_NEG2] ---->
  vMATCH_ACCEPT_TAC vCONJ_SYM);;

let%a vREAL_DIV_MUL2 = prove(
  [%q {|!x z. ~(x = &0) /\ ~(z = &0) ==> !y. y / z = (x * y) / (x * z)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ---->
  vREWRITE_TAC[real_div] ----> vIMP_SUBST_TAC vREAL_INV_MUL_WEAK ---->
  vASM_REWRITE_TAC[] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
    [%q {|(a * b) * (c * d) = (c * a) * (b * d)|} ]] ---->
  vIMP_SUBST_TAC vREAL_MUL_LINV ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vREAL_MUL_LID]);;

let%a vREAL_MIDDLE1 = prove(
  [%q {|!a b. a <= b ==> a <= (a + b) / &2|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vREAL_LE_RDIV ---->
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_DOUBLE] ---->
  vASM_REWRITE_TAC[vGSYM vREAL_DOUBLE; vREAL_LE_LADD] ---->
  vREWRITE_TAC[num_CONV [%q {|2|} ]; vREAL_LT; vLT_0]);;

let%a vREAL_MIDDLE2 = prove(
  [%q {|!a b. a <= b ==> ((a + b) / &2) <= b|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vREAL_LE_LDIV ---->
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vREWRITE_TAC[vGSYM vREAL_DOUBLE] ---->
  vASM_REWRITE_TAC[vGSYM vREAL_DOUBLE; vREAL_LE_RADD] ---->
  vREWRITE_TAC[num_CONV [%q {|2|} ]; vREAL_LT; vLT_0]);;

(*----------------------------------------------------------------------------*)
(* Define usual norm (absolute distance) on the real line                     *)
(*----------------------------------------------------------------------------*)

let%a vABS_ZERO = prove(
  [%q {|!x. (abs(x) = &0) <=> (x = &0)|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_abs] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_NEG_EQ0]);;

let%a vABS_0 = prove(
  [%q {|abs(&0) = &0|} ],
  vREWRITE_TAC[vABS_ZERO]);;

let%a vABS_1 = prove(
  [%q {|abs(&1) = &1|} ],
  vREWRITE_TAC[real_abs; vREAL_LE; vLE_0]);;

let%a vABS_NEG = prove(
  [%q {|!x. abs(--x) = abs(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_abs; vREAL_NEG_NEG; vREAL_NEG_GE0] ---->
  vREPEAT vCOND_CASES_TAC ----> vREWRITE_TAC[] ++-->
   [vMP_TAC(vCONJ (vASSUME [%q {|&0 <= x|} ]) (vASSUME [%q {|x <= &0|} ])) ---->
    vREWRITE_TAC[vREAL_LE_ANTISYM] ---->
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vREAL_NEG_0];
    vRULE_ASSUM_TAC(vREWRITE_RULE[vREAL_NOT_LE]) ---->
    vW(vMP_TAC -| end_itlist vCONJ -| map snd -| fst) ---->
    vREWRITE_TAC[vREAL_LT_ANTISYM]]);;

let%a vABS_TRIANGLE = prove(
  [%q {|!x y. abs(x + y) <= abs(x) + abs(y)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_abs] ---->
  vREPEAT vCOND_CASES_TAC ---->
  vREWRITE_TAC[vREAL_NEG_ADD; vREAL_LE_REFL; vREAL_LE_LADD; vREAL_LE_RADD] ---->
  vASM_REWRITE_TAC[vGSYM vREAL_NEG_ADD; vREAL_LE_NEGL; vREAL_LE_NEGR] ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vREAL_NOT_LE]) ---->
  vTRY(vMATCH_MP_TAC vREAL_LT_IMP_LE) ----> vTRY(vFIRST_ASSUM vACCEPT_TAC) ---->
  vTRY(vUNDISCH_TAC [%q {|(x + y) < &0|} ]) ----> vSUBST1_TAC(vSYM(vSPEC [%q {|&0|} ] vREAL_ADD_LID))
  ----> vREWRITE_TAC[vREAL_NOT_LT] ---->
  vMAP_FIRST vMATCH_MP_TAC [vREAL_LT_ADD2; vREAL_LE_ADD2] ---->
  vASM_REWRITE_TAC[]);;

let%a vABS_POS = prove(
  [%q {|!x. &0 <= abs(x)|} ],
  vGEN_TAC ----> vASM_CASES_TAC [%q {|&0 <= x|} ] ++-->
   [vALL_TAC;
    vMP_TAC(vSPEC [%q {|x:real|} ] vREAL_LE_NEGTOTAL) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC] ---->
  vASM_REWRITE_TAC[real_abs]);;

let%a vABS_MUL = prove(
  [%q {|!x y. abs(x * y) = abs(x) * abs(y)|} ],
  vREPEAT vGEN_TAC ----> vASM_CASES_TAC [%q {|&0 <= x|} ] ++-->
   [vALL_TAC;
    vMP_TAC(vSPEC [%q {|x:real|} ] vREAL_LE_NEGTOTAL) ----> vASM_REWRITE_TAC[] ---->
    vPOP_ASSUM(vK vALL_TAC) ----> vDISCH_TAC ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vABS_NEG] ---->
    vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vGSYM vABS_NEG]
    ----> vREWRITE_TAC[vREAL_NEG_LMUL]] ---->
  (vASM_CASES_TAC [%q {|&0 <= y|} ] ++-->
    [vALL_TAC;
     vMP_TAC(vSPEC [%q {|y:real|} ] vREAL_LE_NEGTOTAL) ----> vASM_REWRITE_TAC[] ---->
     vPOP_ASSUM(vK vALL_TAC) ----> vDISCH_TAC ---->
     vGEN_REWRITE_TAC vLAND_CONV [vGSYM vABS_NEG] ---->
     vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vGSYM vABS_NEG] ---->
     vREWRITE_TAC[vREAL_NEG_RMUL]]) ---->
  vASSUM_LIST(vASSUME_TAC -| vMATCH_MP vREAL_LE_MUL -| end_itlist vCONJ -| rev) ---->
  vASM_REWRITE_TAC[real_abs]);;

let%a vABS_LT_MUL2 = prove(
  [%q {|!w x y z. abs(w) < y /\ abs(x) < z ==> abs(w * x) < (y * z)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[vABS_MUL] ----> vMATCH_MP_TAC vREAL_LT_MUL2_ALT ---->
  vASM_REWRITE_TAC[vABS_POS]);;

let%a vABS_SUB = prove(
  [%q {|!x y. abs(x - y) = abs(y - x)|} ],
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vGSYM vREAL_NEG_SUB] ---->
  vREWRITE_TAC[vABS_NEG]);;

let%a vABS_NZ = prove(
  [%q {|!x. ~(x = &0) <=> &0 < abs(x)|} ],
  vGEN_TAC ----> vEQ_TAC ++-->
   [vONCE_REWRITE_TAC[vGSYM vABS_ZERO] ---->
    vREWRITE_TAC[vTAUT [%q {|~a ==> b <=> b \/ a|} ]] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ---->
    vREWRITE_TAC[vGSYM vREAL_LE_LT; vABS_POS];
    vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[] ---->
    vDISCH_THEN vSUBST1_TAC ---->
    vREWRITE_TAC[real_abs; vREAL_LT_REFL; vREAL_LE_REFL]]);;

let%a vABS_INV = prove(
  [%q {|!x. ~(x = &0) ==> (abs(inv x) = inv(abs(x)))|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LINV_UNIQ ---->
  vREWRITE_TAC[vGSYM vABS_MUL] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV th]) ---->
  vREWRITE_TAC[real_abs; vREAL_LE] ---->
  vREWRITE_TAC[num_CONV [%q {|1|} ]; vGSYM vNOT_LT; vNOT_LESS_0]);;

let%a vABS_ABS = prove(
  [%q {|!x. abs(abs(x)) = abs(x)|} ],
  vGEN_TAC ---->
  vGEN_REWRITE_TAC vLAND_CONV [real_abs] ---->
  vREWRITE_TAC[vABS_POS]);;

let%a vABS_LE = prove(
  [%q {|!x. x <= abs(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_abs] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_LE_REFL] ---->
  vREWRITE_TAC[vREAL_LE_NEGR] ---->
  vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vREAL_NOT_LE]);;

let%a vABS_REFL = prove(
  [%q {|!x. (abs(x) = x) <=> &0 <= x|} ],
  vGEN_TAC ----> vREWRITE_TAC[real_abs] ---->
  vASM_CASES_TAC [%q {|&0 <= x|} ] ----> vASM_REWRITE_TAC[] ---->
  vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_RNEG_UNIQ] ---->
  vREWRITE_TAC[vREAL_DOUBLE; vREAL_ENTIRE; vREAL_INJ] ---->
  vREWRITE_TAC[num_CONV [%q {|2|} ]; vNOT_SUC] ---->
  vDISCH_THEN vSUBST_ALL_TAC ----> vPOP_ASSUM vMP_TAC ---->
  vREWRITE_TAC[vREAL_LE_REFL]);;

let%a vABS_N = prove(
  [%q {|!n. abs(&n) = &n|} ],
  vGEN_TAC ----> vREWRITE_TAC[vABS_REFL; vREAL_LE; vLE_0]);;

let%a vABS_BETWEEN = prove(
  [%q {|!x y d. &0 < d /\ ((x - d) < y) /\ (y < (x + d)) <=> abs(y - x) < d|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_abs] ---->
  vREWRITE_TAC[vREAL_SUB_LE] ----> vREWRITE_TAC[vREAL_NEG_SUB] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_LT_SUB_RADD] ---->
  vGEN_REWRITE_TAC (funpow 2 vRAND_CONV) [vREAL_ADD_SYM] ---->
  vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ++-->
   [vSUBGOAL_THEN [%q {|x < (x + d)|} ] vMP_TAC ++-->
     [vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|y:real|} ] ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vREWRITE_TAC[vREAL_LT_ADDR] ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|y:real|} ] ---->
    vASM_REWRITE_TAC[vREAL_LT_ADDR];
    vRULE_ASSUM_TAC(vREWRITE_RULE[vREAL_NOT_LE]) ---->
    vSUBGOAL_THEN [%q {|y < (y + d)|} ] vMP_TAC ++-->
     [vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vREWRITE_TAC[vREAL_LT_ADDR] ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
    vASM_REWRITE_TAC[vREAL_LT_ADDR]]);;

let%a vABS_BOUND = prove(
  [%q {|!x y d. abs(x - y) < d ==> y < (x + d)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vABS_SUB] ---->
  vONCE_REWRITE_TAC[vGSYM vABS_BETWEEN] ---->
  vDISCH_TAC ----> vASM_REWRITE_TAC[]);;

let%a vABS_STILLNZ = prove(
  [%q {|!x y. abs(x - y) < abs(y) ==> ~(x = &0)|} ],
  vREPEAT vGEN_TAC ----> vCONV_TAC vCONTRAPOS_CONV ---->
  vREWRITE_TAC[] ----> vDISCH_THEN vSUBST1_TAC ---->
  vREWRITE_TAC[vREAL_SUB_LZERO; vABS_NEG; vREAL_LT_REFL]);;

let%a vABS_CASES = prove(
  [%q {|!x. (x = &0) \/ &0 < abs(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM vABS_NZ] ---->
  vBOOL_CASES_TAC [%q {|x = &0|} ] ----> vASM_REWRITE_TAC[]);;

let%a vABS_BETWEEN1 = prove(
  [%q {|!x y z. x < z /\ (abs(y - x)) < (z - x) ==> y < z|} ],
  vREPEAT vGEN_TAC ---->
  vDISJ_CASES_TAC (vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vREAL_LET_TOTAL) ++-->
   [vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
    vREWRITE_TAC[real_sub; vREAL_LT_RADD] ---->
    vDISCH_THEN(vACCEPT_TAC -| vCONJUNCT2);
    vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LT_TRANS ---->
    vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[]]);;

let%a vABS_SIGN = prove(
  [%q {|!x y. abs(x - y) < y ==> &0 < x|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vABS_BOUND) ---->
  vREWRITE_TAC[vREAL_LT_ADDL]);;

let%a vABS_SIGN2 = prove(
  [%q {|!x y. abs(x - y) < --y ==> x < &0|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|--x|} ]; [%q {|--y|} ]] vABS_SIGN) ---->
  vREWRITE_TAC[vREAL_SUB_NEG2] ---->
  vONCE_REWRITE_TAC[vABS_SUB] ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vMATCH_MP th)) ---->
  vREWRITE_TAC[vGSYM vREAL_NEG_LT0; vREAL_NEG_NEG]);;

let%a vABS_DIV = prove(
  [%q {|!y. ~(y = &0) ==> !x. abs(x / y) = abs(x) / abs(y)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ----> vREWRITE_TAC[real_div] ---->
  vREWRITE_TAC[vABS_MUL] ---->
  vPOP_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vABS_INV th]));;

let%a vABS_CIRCLE = prove(
  [%q {|!x y h. abs(h) < (abs(y) - abs(x)) ==> abs(x + h) < abs(y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|abs(x) + abs(h)|} ] ---->
  vREWRITE_TAC[vABS_TRIANGLE] ---->
  vPOP_ASSUM(vMP_TAC -| vCONJ (vSPEC [%q {|abs(x)|} ] vREAL_LE_REFL)) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LET_ADD2) ---->
  vREWRITE_TAC[vREAL_SUB_ADD2]);;

let%a vREAL_SUB_ABS = prove(
  [%q {|!x y. (abs(x) - abs(y)) <= abs(x - y)|} ],
  vREPEAT vGEN_TAC ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|(abs(x - y) + abs(y)) - abs(y)|} ] ----> vCONJ_TAC ++-->
   [vONCE_REWRITE_TAC[real_sub] ----> vREWRITE_TAC[vREAL_LE_RADD] ---->
    vSUBST1_TAC(vSYM(vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vREAL_SUB_ADD)) ---->
    vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vREAL_SUB_ADD] ---->
    vMATCH_ACCEPT_TAC vABS_TRIANGLE;
    vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
    vREWRITE_TAC[vREAL_ADD_SUB; vREAL_LE_REFL]]);;

let%a vABS_SUB_ABS = prove(
  [%q {|!x y. abs(abs(x) - abs(y)) <= abs(x - y)|} ],
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vRATOR_CONV -| vONCE_DEPTH_CONV) [real_abs] ---->
  vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_SUB_ABS] ---->
  vREWRITE_TAC[vREAL_NEG_SUB] ---->
  vONCE_REWRITE_TAC[vABS_SUB] ---->
  vREWRITE_TAC[vREAL_SUB_ABS]);;

let%a vABS_BETWEEN2 = prove(
  [%q {|!x0 x y0 y. x0 < y0 /\ abs(x - x0) < (y0 - x0) / &2 /\
                          abs(y - y0) < (y0 - x0) / &2
        ==> x < y|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|x < y0 /\ x0 < y|} ] vSTRIP_ASSUME_TAC ++-->
   [vCONJ_TAC ++-->
     [vMP_TAC(vSPECL [[%q {|x0:real|} ]; [%q {|x:real|} ]; [%q {|y0 - x0|} ]] vABS_BOUND) ---->
      vREWRITE_TAC[vREAL_SUB_ADD2] ----> vDISCH_THEN vMATCH_MP_TAC ---->
      vONCE_REWRITE_TAC[vABS_SUB] ---->
      vMATCH_MP_TAC vREAL_LT_TRANS ---->
      vEXISTS_TAC [%q {|(y0 - x0) / &2|} ] ----> vASM_REWRITE_TAC[vREAL_LT_HALF2] ---->
      vASM_REWRITE_TAC[vREAL_SUB_LT];
      vGEN_REWRITE_TAC vI [vTAUT [%q {|a = ~ ~a|} ]] ---->
      vPURE_REWRITE_TAC[vREAL_NOT_LT] ----> vDISCH_TAC ---->
      vMP_TAC(vAC vREAL_ADD_AC
       [%q {|(y0 + --x0) + (x0 + --y) = (--x0 + x0) + (y0 + --y)|} ]) ---->
      vREWRITE_TAC[vGSYM real_sub; vREAL_ADD_LINV; vREAL_ADD_LID] ---->
      vDISCH_TAC ---->
      vMP_TAC(vSPECL [[%q {|y0 - x0|} ]; [%q {|x0 - y|} ]] vREAL_LE_ADDR) ---->
      vASM_REWRITE_TAC[vREAL_SUB_LE] ----> vDISCH_TAC ---->
      vSUBGOAL_THEN [%q {|~(y0 <= y)|} ] vASSUME_TAC ++-->
       [vREWRITE_TAC[vREAL_NOT_LE] ----> vONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ---->
        vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|y0 - x0|} ] ---->
        vASM_REWRITE_TAC[] ----> vASM_REWRITE_TAC[vREAL_SUB_LT]; vALL_TAC] ---->
      vUNDISCH_TAC [%q {|abs(y - y0) < (y0 - x0) / &2|} ] ---->
      vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
      vREWRITE_TAC[vREAL_NEG_SUB] ----> vDISCH_TAC ---->
      vSUBGOAL_THEN [%q {|(y0 - x0) < (y0 - x0) / &2|} ] vMP_TAC ++-->
       [vMATCH_MP_TAC vREAL_LET_TRANS ---->
        vEXISTS_TAC [%q {|y0 - y|} ] ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
      vREWRITE_TAC[vREAL_NOT_LT] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
      vREWRITE_TAC[vREAL_LT_HALF2] ----> vASM_REWRITE_TAC[vREAL_SUB_LT]];
    vALL_TAC] ---->
  vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
  vPURE_REWRITE_TAC[vREAL_NOT_LT] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|abs(x0 - y) < (y0 - x0) / &2|} ] vASSUME_TAC ++-->
   [vREWRITE_TAC[real_abs; vREAL_SUB_LE] ----> vASM_REWRITE_TAC[vGSYM vREAL_NOT_LT] ---->
    vREWRITE_TAC[vREAL_NEG_SUB] ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|x - x0|} ] ----> vREWRITE_TAC[real_sub; vREAL_LE_RADD] ---->
    vASM_REWRITE_TAC[vGSYM real_sub] ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|abs(x - x0)|} ] ----> vASM_REWRITE_TAC[vABS_LE]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|abs(y0 - x0) < ((y0 - x0) / &2) + ((y0 - x0) / &2)|} ]
  vMP_TAC ++-->
   [vALL_TAC;
    vREWRITE_TAC[vREAL_HALF_DOUBLE; vREAL_NOT_LT; vABS_LE]] ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|abs(y0 - y) + abs(y - x0)|} ] ----> vCONJ_TAC ++-->
   [vALL_TAC;
    vMATCH_MP_TAC vREAL_LT_ADD2 ----> vONCE_REWRITE_TAC[vABS_SUB] ---->
    vASM_REWRITE_TAC[]] ---->
  vSUBGOAL_THEN [%q {|y0 - x0 = (y0 - y) + (y - x0)|} ] vSUBST1_TAC ---->
  vREWRITE_TAC[vABS_TRIANGLE] ---->
  vREWRITE_TAC[real_sub] ---->
  vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
    [%q {|(a + b) + (c + d) = (b + c) + (a + d)|} ]] ---->
  vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID]);;

let%a vABS_BOUNDS = prove(
  [%q {|!x k. abs(x) <= k <=> --k <= x /\ x <= k|} ],
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vGSYM vREAL_LE_NEG2] ---->
  vREWRITE_TAC[vREAL_NEG_NEG] ----> vREWRITE_TAC[real_abs] ---->
  vCOND_CASES_TAC ++-->
   [vREWRITE_TAC[vTAUT [%q {|(a <=> b /\ a) <=> a ==> b|} ]] ---->
    vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
    vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[vREAL_LE_NEGL];
    vREWRITE_TAC[vTAUT [%q {|(a <=> a /\ b) <=> a ==> b|} ]] ---->
    vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
    vEXISTS_TAC [%q {|--x|} ] ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vREAL_LE_NEGR] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
    vASM_REWRITE_TAC[vGSYM vREAL_NOT_LE]]);;

(*----------------------------------------------------------------------------*)
(* Define integer powers                                                      *)
(*----------------------------------------------------------------------------*)

let pow = real_pow;;

let%a vPOW_0 = prove(
  [%q {|!n. &0 pow (SUC n) = &0|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[pow; vREAL_MUL_LZERO]);;

let%a vPOW_NZ = prove(
  [%q {|!c n. ~(c = &0) ==> ~(c pow n = &0)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ---->
  vINDUCT_TAC ----> vASM_REWRITE_TAC[pow; vREAL_10; vREAL_ENTIRE]);;

let%a vPOW_INV = prove(
  [%q {|!c n. ~(c = &0) ==> (inv(c pow n) = (inv c) pow n)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vDISCH_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[pow; vREAL_INV1] ---->
  vMP_TAC(vSPECL [[%q {|c:real|} ]; [%q {|c pow n|} ]] vREAL_INV_MUL_WEAK) ---->
  vASM_REWRITE_TAC[] ----> vSUBGOAL_THEN [%q {|~(c pow n = &0)|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vPOW_NZ ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vASM_REWRITE_TAC[]);;

let%a vPOW_ABS = prove(
  [%q {|!c n. abs(c) pow n = abs(c pow n)|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[pow; vABS_1; vABS_MUL]);;

let%a vPOW_PLUS1 = prove(
  [%q {|!e n. &0 < e ==> (&1 + (&n * e)) <= (&1 + e) pow n|} ],
  vGEN_TAC ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vDISCH_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[pow; vREAL_MUL_LZERO; vREAL_ADD_RID; vREAL_LE_REFL] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|(&1 + e) * (&1 + (&n * e))|} ] ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vREAL_RDISTRIB; vREAL; vREAL_MUL_LID] ---->
    vREWRITE_TAC[vREAL_LDISTRIB;vREAL_MUL_RID; vREAL_ADD_ASSOC; vREAL_LE_ADDR] ---->
    vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
    vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
    vMATCH_MP_TAC vREAL_LE_MUL ---->
    vREWRITE_TAC[vREAL_LE_SQUARE; vREAL_LE; vLE_0];
    vSUBGOAL_THEN [%q {|&0 < (&1 + e)|} ]
      (fun th -> vASM_REWRITE_TAC[vMATCH_MP vREAL_LE_LMUL_LOCAL th]) ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_ADD_LID] ---->
    vMATCH_MP_TAC vREAL_LT_ADD2 ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vREAL_LT] ----> vREWRITE_TAC[num_CONV [%q {|1|} ]; vLT_0]]);;

let%a vPOW_ADD = prove(
  [%q {|!c m n. c pow (m + n) = (c pow m) * (c pow n)|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[pow; vADD_CLAUSES; vREAL_MUL_RID] ---->
  vREWRITE_TAC[vREAL_MUL_AC]);;

let%a vPOW_1 = prove(
  [%q {|!x. x pow 1 = x|} ],
  vGEN_TAC ----> vREWRITE_TAC[num_CONV [%q {|1|} ]] ---->
  vREWRITE_TAC[pow; vREAL_MUL_RID]);;

let%a vPOW_2 = prove(
  [%q {|!x. x pow 2 = x * x|} ],
  vGEN_TAC ----> vREWRITE_TAC[num_CONV [%q {|2|} ]] ---->
  vREWRITE_TAC[pow; vPOW_1]);;

let%a vPOW_POS = prove(
  [%q {|!x n. &0 <= x ==> &0 <= (x pow n)|} ],
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vGEN_TAC ----> vDISCH_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[pow; vREAL_LE_01] ---->
  vMATCH_MP_TAC vREAL_LE_MUL ----> vASM_REWRITE_TAC[]);;

let%a vPOW_LE = prove(
  [%q {|!n x y. &0 <= x /\ x <= y ==> (x pow n) <= (y pow n)|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[pow; vREAL_LE_REFL] ---->
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMATCH_MP_TAC vREAL_LE_MUL2V ----> vASM_REWRITE_TAC[] ---->
  vASM_MESON_TAC[vPOW_POS]);;

let%a vPOW_M1 = prove(
  [%q {|!n. abs((--(&1)) pow n) = &1|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[pow; vABS_NEG; vABS_1] ---->
  vASM_REWRITE_TAC[vABS_MUL; vABS_NEG; vABS_1; vREAL_MUL_LID]);;

let%a vPOW_MUL = prove(
  [%q {|!n x y. (x * y) pow n = (x pow n) * (y pow n)|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[pow; vREAL_MUL_LID] ---->
  vREPEAT vGEN_TAC ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vREAL_MUL_AC]);;

let%a vREAL_LE_SQUARE_POW = prove(
  [%q {|!x. &0 <= x pow 2|} ],
  vGEN_TAC ----> vREWRITE_TAC[vPOW_2; vREAL_LE_SQUARE]);;

let%a vABS_POW2 = prove(
  [%q {|!x. abs(x pow 2) = x pow 2|} ],
  vGEN_TAC ----> vREWRITE_TAC[vABS_REFL; vREAL_LE_SQUARE_POW]);;

let%a vREAL_LE1_POW2 = prove(
  [%q {|!x. &1 <= x ==> &1 <= (x pow 2)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vPOW_2] ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_LID] ---->
  vMATCH_MP_TAC vREAL_LE_MUL2V ----> vASM_REWRITE_TAC[vREAL_LE_01]);;

let%a vREAL_LT1_POW2 = prove(
  [%q {|!x. &1 < x ==> &1 < (x pow 2)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vPOW_2] ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_LID] ---->
  vMATCH_MP_TAC vREAL_LT_MUL2_ALT ----> vASM_REWRITE_TAC[vREAL_LE_01]);;

let%a vPOW_POS_LT = prove(
  [%q {|!x n. &0 < x ==> &0 < (x pow (SUC n))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_LT_LE] ---->
  vDISCH_TAC ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vPOW_POS ----> vASM_REWRITE_TAC[];
    vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vPOW_NZ ---->
    vCONV_TAC(vRAND_CONV vSYM_CONV) ----> vASM_REWRITE_TAC[]]);;

let%a vPOW_2_LE1 = prove(
  [%q {|!n. &1 <= &2 pow n|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[pow; vREAL_LE_REFL] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_LID] ---->
  vMATCH_MP_TAC vREAL_LE_MUL2V ----> vASM_REWRITE_TAC[vREAL_LE] ---->
  vREWRITE_TAC[vLE_0; num_CONV [%q {|2|} ]; vLESS_EQ_SUC_REFL]);;

let%a vPOW_2_LT = prove(
  [%q {|!n. &n < &2 pow n|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[pow; vREAL_LT_01] ---->
  vREWRITE_TAC[vADD1; vGSYM vREAL_ADD; vGSYM vREAL_DOUBLE] ---->
  vMATCH_MP_TAC vREAL_LTE_ADD2 ----> vASM_REWRITE_TAC[vPOW_2_LE1]);;

let%a vPOW_MINUS1 = prove(
  [%q {|!n. (--(&1)) pow (2 * n) = &1|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[vMULT_CLAUSES; pow] ---->
  vREWRITE_TAC[num_CONV [%q {|2|} ]; num_CONV [%q {|1|} ]; vADD_CLAUSES] ---->
  vREWRITE_TAC[pow] ---->
  vREWRITE_TAC[vSYM(num_CONV [%q {|2|} ]); vSYM(num_CONV [%q {|1|} ])] ---->
  vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL] ---->
  vREWRITE_TAC[vREAL_MUL_LID; vREAL_NEG_NEG]);;

(*----------------------------------------------------------------------------*)
(* Derive the supremum property for an arbitrary bounded nonempty set         *)
(*----------------------------------------------------------------------------*)

let%a vREAL_SUP_EXISTS = prove(
  [%q {|!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
     (?s. !y. (?x. P x /\ y < x) <=> y < s)|} ],
  vGEN_TAC ----> vMP_TAC(vSPEC [%q {|P:real->bool|} ] vREAL_COMPLETE) ---->
  vMESON_TAC[vREAL_LT_IMP_LE; vREAL_LTE_TRANS; vREAL_NOT_LT]);;

let sup_def = new_definition
 [%q {|sup s = @a. (!x. x IN s ==> x <= a) /\
              (!b. (!x. x IN s ==> x <= b) ==> a <= b)|} ];;

let%a sup = prove
 ([%q {|sup P = @s. !y. (?x. P x /\ y < x) <=> y < s|} ],
  vREWRITE_TAC[sup_def; vIN] ----> vAP_TERM_TAC ----> vREWRITE_TAC[vFUN_EQ_THM] ---->
  vASM_MESON_TAC[vREAL_LTE_TRANS; vREAL_NOT_LT; vREAL_LE_REFL]);;

let%a vREAL_SUP = prove(
  [%q {|!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. (?x. P x /\ y < x) <=> y < sup P)|} ],
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vSELECT_RULE -| vMATCH_MP vREAL_SUP_EXISTS)
  ----> vREWRITE_TAC[vGSYM sup]);;

let%a vREAL_SUP_UBOUND = prove(
  [%q {|!P. (?x. P x) /\ (?z. !x. P x ==> x < z) ==>
          (!y. P y ==> y <= sup P)|} ],
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|sup P|} ] -| vMATCH_MP vREAL_SUP) ---->
  vREWRITE_TAC[vREAL_LT_REFL] ---->
  vDISCH_THEN(vASSUME_TAC -| vCONV_RULE vNOT_EXISTS_CONV) ---->
  vX_GEN_TAC [%q {|x:real|} ] ----> vRULE_ASSUM_TAC(vSPEC [%q {|x:real|} ]) ---->
  vDISCH_THEN (vSUBST_ALL_TAC -| vEQT_INTRO) ----> vPOP_ASSUM vMP_TAC ---->
  vREWRITE_TAC[vREAL_NOT_LT]);;

let%a vSETOK_LE_LT = prove(
  [%q {|!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) <=>
       (?x. P x) /\ (?z. !x. P x ==> x < z)|} ],
  vGEN_TAC ----> vAP_TERM_TAC ----> vEQ_TAC ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|z:real|} ])
  ++--> (map vEXISTS_TAC [[%q {|z + &1|} ]; [%q {|z:real|} ]]) ----> vGEN_TAC ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
  vREWRITE_TAC[vREAL_LT_ADD1; vREAL_LT_IMP_LE]);;

let%a vREAL_SUP_LE = prove(
  [%q {|!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
           (!y. (?x. P x /\ y < x) <=> y < sup P)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vSETOK_LE_LT; vREAL_SUP]);;

let%a vREAL_SUP_UBOUND_LE = prove(
  [%q {|!P. (?x. P x) /\ (?z. !x. P x ==> x <= z) ==>
          (!y. P y ==> y <= sup P)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vSETOK_LE_LT; vREAL_SUP_UBOUND]);;

(*----------------------------------------------------------------------------*)
(* Prove the Archimedean property                                             *)
(*----------------------------------------------------------------------------*)

let%a vREAL_ARCH_SIMPLE = prove
 ([%q {|!x. ?n. x <= &n|} ],
  let lemma = prove([%q {|(!x. (?n. x = &n) ==> P x) <=> !n. P(&n)|} ],vMESON_TAC[]) in
  vMP_TAC(vSPEC [%q {|\y. ?n. y = &n|} ] vREAL_COMPLETE) ----> vREWRITE_TAC[lemma] ---->
  vMESON_TAC[vREAL_LE_SUB_LADD; vREAL_OF_NUM_ADD; vREAL_LE_TOTAL;
            vREAL_ARITH [%q {|~(M <= M - &1)|} ]]);;

let%a vREAL_ARCH = prove(
  [%q {|!x. &0 < x ==> !y. ?n. y < &n * x|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ---->
  vONCE_REWRITE_TAC[vTAUT [%q {|a <=> ~(~a)|} ]] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vNOT_EXISTS_CONV) ---->
  vREWRITE_TAC[vREAL_NOT_LT] ----> vDISCH_TAC ---->
  vMP_TAC(vSPEC [%q {|\z. ?n. z = &n * x|} ] vREAL_SUP_LE) ----> vBETA_TAC ---->
  vW(vC vSUBGOAL_THEN (fun th -> vREWRITE_TAC[th]) -|
       funpow 2 (fst -| dest_imp) -| snd)
  ++--> [vCONJ_TAC ++-->
   [vMAP_EVERY vEXISTS_TAC [[%q {|&n * x|} ]; [%q {|n:num|} ]] ----> vREFL_TAC;
    vEXISTS_TAC [%q {|y:real|} ] ----> vGEN_TAC ---->
    vDISCH_THEN(vCHOOSE_THEN vSUBST1_TAC) ----> vASM_REWRITE_TAC[]]; vALL_TAC] ---->
  vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|sup(\z. ?n. z = &n * x) - x|} ]) ---->
  vREWRITE_TAC[vREAL_LT_SUB_RADD; vREAL_LT_ADDR] ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC [%q {|n:num|} ]) vMP_TAC) ---->
  vASM_REWRITE_TAC[] ---->
  vGEN_REWRITE_TAC (funpow 3 vRAND_CONV) [vGSYM vREAL_MUL_LID] ---->
  vREWRITE_TAC[vGSYM vREAL_RDISTRIB] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|sup(\z. ?n. z = &n * x)|} ]) ---->
  vREWRITE_TAC[vREAL_LT_REFL] ----> vEXISTS_TAC [%q {|(&n + &1) * x|} ] ---->
  vASM_REWRITE_TAC[] ----> vEXISTS_TAC [%q {|n + 1|} ] ---->
  vREWRITE_TAC[vREAL_ADD]);;

let%a vREAL_ARCH_LEAST = prove(
  [%q {|!y. &0 < y ==> !x. &0 <= x ==>
                        ?n. (&n * y) <= x /\ x < (&(SUC n) * y)|} ],
  vGEN_TAC ----> vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vREAL_ARCH) ---->
  vGEN_TAC ----> vPOP_ASSUM(vASSUME_TAC -| vSPEC [%q {|x:real|} ]) ---->
  vPOP_ASSUM(vX_CHOOSE_THEN [%q {|n:num|} ] vMP_TAC -|
        vONCE_REWRITE_RULE[num_WOP]) ---->
  vREWRITE_TAC[vREAL_NOT_LT] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vASSUME_TAC -| vSPEC [%q {|PRE n|} ])) ---->
  vDISCH_TAC ----> vEXISTS_TAC [%q {|PRE n|} ] ---->
  vSUBGOAL_THEN [%q {|SUC(PRE n) = n|} ] vASSUME_TAC ++-->
   [vDISJ_CASES_THEN2 vSUBST_ALL_TAC (vCHOOSE_THEN vSUBST_ALL_TAC)
        (vSPEC [%q {|n:num|} ] num_CASES) ++-->
     [vUNDISCH_TAC [%q {|x < &0 * y|} ] ---->
      vASM_REWRITE_TAC[vREAL_MUL_LZERO; vGSYM vREAL_NOT_LE];
      vREWRITE_TAC[vPRE]];
    vASM_REWRITE_TAC[] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vPRE; vLESS_SUC_REFL]]);;

let%a vREAL_POW_LBOUND = prove
 ([%q {|!x n. &0 <= x ==> &1 + &n * x <= (&1 + x) pow n|} ],
  vGEN_TAC ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ----> vDISCH_TAC ---->
  vINDUCT_TAC ---->
  vREWRITE_TAC[real_pow; vREAL_MUL_LZERO; vREAL_ADD_RID; vREAL_LE_REFL] ---->
  vREWRITE_TAC[vGSYM vREAL_OF_NUM_SUC] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|(&1 + x) * (&1 + &n * x)|} ] ---->
  vASM_SIMP_TAC[vREAL_LE_LMUL; vREAL_ARITH [%q {|&0 <= x ==> &0 <= &1 + x|} ]] ---->
  vASM_SIMP_TAC[vREAL_LE_MUL; vREAL_POS; vREAL_ARITH
   [%q {|&1 + (n + &1) * x <= (&1 + x) * (&1 + n * x) <=> &0 <= n * x * x|} ]]);;

let%a vREAL_ARCH_POW = prove
 ([%q {|!x y. &1 < x ==> ?n. y < x pow n|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|x - &1|} ] vREAL_ARCH) ----> vASM_REWRITE_TAC[vREAL_SUB_LT] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|y:real|} ]) ----> vMATCH_MP_TAC vMONO_EXISTS ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LTE_TRANS ---->
  vEXISTS_TAC [%q {|&1 + &n * (x - &1)|} ] ---->
  vASM_SIMP_TAC[vREAL_ARITH [%q {|x < y ==> x < &1 + y|} ]] ---->
  vASM_MESON_TAC[vREAL_POW_LBOUND; vREAL_SUB_ADD2; vREAL_ARITH
    [%q {|&1 < x ==> &0 <= x - &1|} ]]);;

let%a vREAL_ARCH_POW2 = prove
 ([%q {|!x. ?n. x < &2 pow n|} ],
  vSIMP_TAC[vREAL_ARCH_POW; vREAL_OF_NUM_LT; vARITH]);;

(* ========================================================================= *)
(* Finite sums. NB: sum(m,n) f = f(m) + f(m+1) + ... + f(m+n-1)              *)
(* ========================================================================= *)

prioritize_real();;

make_overloadable "sum" [%q {|:A->(B->real)->real|} ];;

overload_interface("sum",[%q {|sum:(A->bool)->(A->real)->real|} ]);;
overload_interface("sum",[%q {|psum:(num#num)->(num->real)->real|} ]);;

let%a sum_EXISTS = prove
 ([%q {|?sum. (!f n. sum(n,0) f = &0) /\
         (!f m n. sum(n,SUC m) f = sum(n,m) f + f(n + m))|} ],
  (vCHOOSE_TAC -| prove_recursive_functions_exist num_RECURSION)
    [%q {|(!f n. sm n 0 f = &0) /\
     (!f m n. sm  n (SUC m) f = sm n m f + f(n + m))|} ] ---->
  vEXISTS_TAC [%q {|\(n,m) f. (sm:num->num->(num->real)->real) n m f|} ] ---->
  vCONV_TAC(vDEPTH_CONV vGEN_BETA_CONV) ----> vASM_REWRITE_TAC[]);;

let sum_DEF = new_specification ["psum"] sum_EXISTS;;

let%a sum = prove
 ([%q {|(sum(n,0) f = &0) /\
   (sum(n,SUC m) f = sum(n,m) f + f(n + m))|} ],
  vREWRITE_TAC[sum_DEF]);;

(* ------------------------------------------------------------------------- *)
(* Relation to the standard notion.                                          *)
(* ------------------------------------------------------------------------- *)

let%a vPSUM_SUM = prove
 ([%q {|!f m n. sum(m,n) f = sum {i | m <= i /\ i < m + n} f|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[sum] ++-->
   [vSUBGOAL_THEN [%q {|{i | m <= i /\ i < m + 0} = {}|} ]
     (fun th -> vSIMP_TAC[th; vSUM_CLAUSES]) ---->
    vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vNOT_IN_EMPTY] ----> vARITH_TAC;
    vALL_TAC] ---->
  vSUBGOAL_THEN
    [%q {|FINITE {i | m <= i /\ i < m + n} /\
     {i | m <= i /\ i < m + SUC n} =
                (m + n) INSERT {i | m <= i /\ i < m + n}|} ]
    (fun th -> vASM_SIMP_TAC[th; vSUM_CLAUSES; vIN_ELIM_THM;
                            vLT_REFL; vREAL_ADD_AC]) ---->
  vCONJ_TAC ++-->
   [vMATCH_MP_TAC vFINITE_SUBSET ----> vEXISTS_TAC [%q {|m..m+n|} ] ---->
    vREWRITE_TAC[vFINITE_NUMSEG; vSUBSET; vIN_NUMSEG; vIN_ELIM_THM];
    vREWRITE_TAC[vEXTENSION; vIN_ELIM_THM; vIN_INSERT]] ---->
  vARITH_TAC);;

let%a vPSUM_SUM_NUMSEG = prove
 ([%q {|!f m n. ~(m = 0 /\ n = 0) ==> sum(m,n) f = sum(m..(m+n)-1) f|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vPSUM_SUM] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vREWRITE_TAC[vEXTENSION; vIN_NUMSEG; vIN_ELIM_THM] ---->
  vPOP_ASSUM vMP_TAC ----> vARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Stuff about sums.                                                         *)
(* ------------------------------------------------------------------------- *)

let%a vSUM_TWO = prove
 ([%q {|!f n p. sum(0,n) f + sum(n,p) f = sum(0,n + p) f|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[sum; vREAL_ADD_RID; vADD_CLAUSES] ---->
  vASM_REWRITE_TAC[vREAL_ADD_ASSOC]);;

let%a vSUM_DIFF = prove
 ([%q {|!f m n. sum(m,n) f = sum(0,m + n) f - sum(0,m) f|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vREAL_EQ_SUB_LADD] ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vMATCH_ACCEPT_TAC vSUM_TWO);;

let%a vABS_SUM = prove
 ([%q {|!f m n. abs(sum(m,n) f) <= sum(m,n) (\n. abs(f n))|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[sum; vREAL_ABS_0; vREAL_LE_REFL] ----> vBETA_TAC ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|abs(sum(m,n) f) + abs(f(m + n))|} ] ---->
  vASM_REWRITE_TAC[vREAL_ABS_TRIANGLE; vREAL_LE_RADD]);;

let%a vSUM_LE = prove
 ([%q {|!f g m n. (!r. m <= r /\ r < n + m ==> f(r) <= g(r))
        ==> (sum(m,n) f <= sum(m,n) g)|} ],
  vEVERY(replicate vGEN_TAC 3) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[sum; vREAL_LE_REFL] ---->
  vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LE_ADD2 ----> vCONJ_TAC ---->
  vFIRST_ASSUM vMATCH_MP_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[vADD_CLAUSES] ---->
    vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|(n:num) + m|} ];
    vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vADD_SYM]] ---->
  vASM_REWRITE_TAC[vADD_CLAUSES; vLE_ADD; vLT]);;

let%a vSUM_EQ = prove
 ([%q {|!f g m n. (!r. m <= r /\ r < (n + m) ==> (f(r) = g(r)))
        ==> (sum(m,n) f = sum(m,n) g)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
  vCONJ_TAC ----> vMATCH_MP_TAC vSUM_LE ----> vGEN_TAC ---->
  vDISCH_THEN(fun th -> vMATCH_MP_TAC vREAL_EQ_IMP_LE ---->
    vFIRST_ASSUM(vSUBST1_TAC -| vC vMATCH_MP th)) ----> vREFL_TAC);;

let%a vSUM_POS = prove
 ([%q {|!f. (!n. &0 <= f(n)) ==> !m n. &0 <= sum(m,n) f|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[sum; vREAL_LE_REFL] ---->
  vMATCH_MP_TAC vREAL_LE_ADD ----> vASM_REWRITE_TAC[]);;

let%a vSUM_POS_GEN = prove
 ([%q {|!f m n.
     (!n. m <= n ==> &0 <= f(n))
     ==> &0 <= sum(m,n) f|} ],
  vREPEAT vSTRIP_TAC ----> vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vINDUCT_TAC ---->
  vREWRITE_TAC[sum; vREAL_LE_REFL] ---->
  vMATCH_MP_TAC vREAL_LE_ADD ---->
  vASM_REWRITE_TAC[] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vMATCH_ACCEPT_TAC vLE_ADD);;

let%a vSUM_ABS = prove
 ([%q {|!f m n. abs(sum(m,n) (\m. abs(f m))) = sum(m,n) (\m. abs(f m))|} ],
  vGEN_TAC ----> vGEN_TAC ----> vREWRITE_TAC[vREAL_ABS_REFL] ---->
  vSPEC_TAC([%q {|m:num|} ],[%q {|m:num|} ]) ----> vMATCH_MP_TAC vSUM_POS ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_ABS_POS]);;

let%a vSUM_ABS_LE = prove
 ([%q {|!f m n. abs(sum(m,n) f) <= sum(m,n)(\n. abs(f n))|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[sum; vREAL_ABS_0; vREAL_LE_REFL] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|abs(sum(m,n) f) + abs(f(m + n))|} ] ---->
  vREWRITE_TAC[vREAL_ABS_TRIANGLE] ----> vBETA_TAC ---->
  vASM_REWRITE_TAC[vREAL_LE_RADD]);;

let%a vSUM_ZERO = prove
 ([%q {|!f N. (!n. n >= N ==> (f(n) = &0)) ==>
         (!m n. m >= N ==> (sum(m,n) f = &0))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|m:num|} ]; [%q {|n:num|} ]] ----> vREWRITE_TAC[vGE] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC -| vREWRITE_RULE[vLE_EXISTS]) ---->
  vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vINDUCT_TAC ----> vREWRITE_TAC[sum] ---->
  vASM_REWRITE_TAC[vREAL_ADD_LID] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vREWRITE_TAC[vGE; vGSYM vADD_ASSOC; vLE_ADD]);;

let%a vSUM_ADD = prove
 ([%q {|!f g m n. sum(m,n) (\n. f(n) + g(n)) = sum(m,n) f + sum(m,n) g|} ],
  vEVERY(replicate vGEN_TAC 3) ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[sum; vREAL_ADD_LID; vREAL_ADD_AC]);;

let%a vSUM_CMUL = prove
 ([%q {|!f c m n. sum(m,n) (\n. c * f(n)) = c * sum(m,n) f|} ],
  vEVERY(replicate vGEN_TAC 3) ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[sum; vREAL_MUL_RZERO] ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_ADD_LDISTRIB]);;

let%a vSUM_NEG = prove
 ([%q {|!f n d. sum(n,d) (\n. --(f n)) = --(sum(n,d) f)|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[sum; vREAL_NEG_0] ---->
  vBETA_TAC ----> vREWRITE_TAC[vREAL_NEG_ADD]);;

let%a vSUM_SUB = prove
 ([%q {|!f g m n. sum(m,n)(\n. (f n) - (g n)) = sum(m,n) f - sum(m,n) g|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub; vGSYM vSUM_NEG; vGSYM vSUM_ADD]);;

let%a vSUM_SUBST = prove
 ([%q {|!f g m n. (!p. m <= p /\ p < (m + n) ==> (f p = g p))
        ==> (sum(m,n) f = sum(m,n) g)|} ],
  vEVERY (replicate vGEN_TAC 3) ----> vINDUCT_TAC ----> vREWRITE_TAC[sum] ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ----> vBINOP_TAC ---->
  vFIRST_ASSUM vMATCH_MP_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[vADD_CLAUSES; vLT_SUC_LE] ---->
    vMATCH_MP_TAC vLT_IMP_LE ----> vASM_REWRITE_TAC[];
    vREWRITE_TAC[vLE_ADD] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
    vREWRITE_TAC[vLT_SUC_LE; vLE_REFL; vADD_CLAUSES]]);;

let%a vSUM_NSUB = prove
 ([%q {|!n f c. sum(0,n) f - (&n * c) = sum(0,n)(\p. f(p) - c)|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[sum; vREAL_MUL_LZERO; vREAL_SUB_REFL] ---->
  vREWRITE_TAC[vADD_CLAUSES; vGSYM vREAL_OF_NUM_SUC; vREAL_ADD_RDISTRIB] ---->
  vREPEAT vGEN_TAC ----> vPOP_ASSUM(fun th -> vREWRITE_TAC[vGSYM th]) ---->
  vREWRITE_TAC[real_sub; vREAL_NEG_ADD; vREAL_MUL_LID; vREAL_ADD_AC]);;

let%a vSUM_BOUND = prove
 ([%q {|!f K m n. (!p. m <= p /\ p < (m + n) ==> (f(p) <= K))
        ==> (sum(m,n) f <= (&n * K))|} ],
  vEVERY (replicate vGEN_TAC 3) ----> vINDUCT_TAC ---->
  vREWRITE_TAC[sum; vREAL_MUL_LZERO; vREAL_LE_REFL] ---->
  vDISCH_TAC ----> vREWRITE_TAC[vGSYM vREAL_OF_NUM_SUC; vREAL_ADD_RDISTRIB] ---->
  vMATCH_MP_TAC vREAL_LE_ADD2 ----> vCONJ_TAC ++-->
   [vFIRST_ASSUM vMATCH_MP_TAC ----> vGEN_TAC ----> vDISCH_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vADD_CLAUSES; vLT_SUC_LE; vLE_REFL] ---->
    vMATCH_MP_TAC vLT_IMP_LE ----> vASM_REWRITE_TAC[];
    vREWRITE_TAC[vREAL_MUL_LID] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vREWRITE_TAC[vADD_CLAUSES; vLE_ADD; vLT_SUC_LE; vLE_REFL]]);;

let%a vSUM_GROUP = prove
 ([%q {|!n k f. sum(0,n)(\m. sum(m * k,k) f) = sum(0,n * k) f|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[sum; vMULT_CLAUSES] ---->
  vREPEAT vGEN_TAC ----> vBETA_TAC ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vADD_CLAUSES; vSUM_TWO]);;

let%a vSUM_1 = prove
 ([%q {|!f n. sum(n,1) f = f(n)|} ],
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[num_CONV [%q {|1|} ]; sum; vADD_CLAUSES; vREAL_ADD_LID]);;

let%a vSUM_2 = prove
 ([%q {|!f n. sum(n,2) f = f(n) + f(n + 1)|} ],
  vREPEAT vGEN_TAC ----> vCONV_TAC(vREDEPTH_CONV num_CONV) ---->
  vREWRITE_TAC[sum; vADD_CLAUSES; vREAL_ADD_LID]);;

let%a vSUM_OFFSET = prove
 ([%q {|!f n k. sum(0,n)(\m. f(m + k)) = sum(0,n + k) f - sum(0,k) f|} ],
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vADD_SYM] ---->
  vREWRITE_TAC[vGSYM vSUM_TWO; vREAL_ADD_SUB] ---->
  vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ----> vINDUCT_TAC ----> vREWRITE_TAC[sum] ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES] ----> vAP_TERM_TAC ---->
  vAP_TERM_TAC ----> vMATCH_ACCEPT_TAC vADD_SYM);;

let%a vSUM_REINDEX = prove
 ([%q {|!f m k n. sum(m + k,n) f = sum(m,n)(\r. f(r + k))|} ],
  vEVERY(replicate vGEN_TAC 3) ----> vINDUCT_TAC ----> vREWRITE_TAC[sum] ---->
  vASM_REWRITE_TAC[vREAL_EQ_ADD_LCANCEL] ----> vREWRITE_TAC[vADD_AC]);;

let%a vSUM_0 = prove
 ([%q {|!m n. sum(m,n)(\r. &0) = &0|} ],
  vGEN_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[sum] ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[vREAL_ADD_LID]);;

let%a vSUM_CANCEL = prove
 ([%q {|!f n d. sum(n,d) (\n. f(SUC n) - f(n)) = f(n + d) - f(n)|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[sum; vADD_CLAUSES; vREAL_SUB_REFL] ---->
  vBETA_TAC ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vREWRITE_TAC[real_sub; vREAL_NEG_ADD; vREAL_ADD_ASSOC] ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ---->
  vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_RID]);;

let%a vSUM_HORNER = prove
 ([%q {|!f n x. sum(0,SUC n)(\i. f(i) * x pow i) =
           f(0) + x * sum(0,n)(\i. f(SUC i) * x pow i)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vSUM_CMUL] ---->
  vONCE_REWRITE_TAC[vREAL_ARITH [%q {|a * b * c = b * (a * c)|} ]] ---->
  vREWRITE_TAC[vGSYM real_pow] ---->
  vMP_TAC(vGEN [%q {|f:num->real|} ]
   (vSPECL [[%q {|f:num->real|} ]; [%q {|n:num|} ]; [%q {|1|} ]] vSUM_OFFSET)) ---->
  vREWRITE_TAC[vGSYM vADD1] ----> vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
  vREWRITE_TAC[vSUM_1] ----> vREWRITE_TAC[real_pow; vREAL_MUL_RID] ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vREWRITE_TAC[vREAL_SUB_ADD]);;

let%a vSUM_CONST = prove
 ([%q {|!c n. sum(0,n) (\m. c) = &n * c|} ],
  vGEN_TAC ----> vINDUCT_TAC ---->
  vASM_REWRITE_TAC[sum; vGSYM vREAL_OF_NUM_SUC; vREAL_MUL_LZERO] ---->
  vREWRITE_TAC[vREAL_ADD_RDISTRIB; vREAL_MUL_LID]);;

let%a vSUM_SPLIT = prove
 ([%q {|!f n p. sum(m,n) f + sum(m + n,p) f = sum(m,n + p) f|} ],
  vREPEAT vGEN_TAC ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV) [vSUM_DIFF] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vSUM_DIFF] ---->
  vREWRITE_TAC[vADD_ASSOC] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vGSYM vSUM_TWO] ---->
  vREAL_ARITH_TAC);;

let%a vSUM_SWAP = prove
 ([%q {|!f m1 n1 m2 n2.
        sum(m1,n1) (\a. sum(m2,n2) (\b. f a b)) =
        sum(m2,n2) (\b. sum(m1,n1) (\a. f a b))|} ],
  vGEN_TAC ----> vGEN_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[sum; vSUM_0] ----> vASM_REWRITE_TAC[vSUM_ADD]);;

let%a vSUM_EQ_0 = prove
 ([%q {|(!r. m <= r /\ r < m + n ==> (f(r) = &0)) ==> (sum(m,n) f = &0)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vEQ_TRANS ---->
  vEXISTS_TAC [%q {|sum(m,n) (\r. &0)|} ] ---->
  vCONJ_TAC ++--> [vALL_TAC; vREWRITE_TAC[vSUM_0]] ---->
  vMATCH_MP_TAC vSUM_EQ ----> vASM_REWRITE_TAC[] ---->
  vONCE_REWRITE_TAC[vADD_SYM] ----> vASM_REWRITE_TAC[]);;

let%a vSUM_MORETERMS_EQ = prove
 ([%q {|!m n p.
      n <= p /\ (!r. m + n <= r /\ r < m + p ==> (f(r) = &0))
      ==> (sum(m,p) f = sum(m,n) f)|} ],
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vGSYM -| vMATCH_MP vSUB_ADD) ---->
  vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vGSYM vSUM_SPLIT] ---->
  vSUBGOAL_THEN [%q {|sum (m + n,p - n) f = &0|} ]
   (fun th -> vREWRITE_TAC[vREAL_ADD_RID; th]) ----> vMATCH_MP_TAC vSUM_EQ_0 ---->
  vREPEAT vSTRIP_TAC ----> vFIRST_X_ASSUM vMATCH_MP_TAC ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vLTE_TRANS ---->
  vEXISTS_TAC [%q {|(m + n) + p - n:num|} ] ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vGSYM vADD_ASSOC; vLE_ADD_LCANCEL] ----> vMATCH_MP_TAC vEQ_IMP_LE ---->
  vONCE_REWRITE_TAC[vADD_SYM] ----> vASM_SIMP_TAC[vSUB_ADD]);;

let%a vSUM_DIFFERENCES_EQ = prove
 ([%q {|!m n p.
      n <= p /\ (!r. m + n <= r /\ r < m + p ==> (f(r) = g(r)))
      ==> (sum(m,p) f - sum(m,n) f = sum(m,p) g - sum(m,n) g)|} ],
  vONCE_REWRITE_TAC[vREAL_ARITH [%q {|(a - b = c - d) <=> (a - c = b - d)|} ]] ---->
  vSIMP_TAC[vGSYM vSUM_SUB; vSUM_MORETERMS_EQ; vREAL_SUB_0]);;

(* ------------------------------------------------------------------------- *)
(* A conversion to evaluate summations (not clear it belongs here...)        *)
(* ------------------------------------------------------------------------- *)

let vREAL_SUM_CONV =
  let sum_tm = [%q {|sum|} ] in
  let pth = prove
   ([%q {|sum(0,1) f = f 0|} ],
    vREWRITE_TAC[num_CONV [%q {|1|} ]; sum; vREAL_ADD_LID; vADD_CLAUSES]) in
  let conv0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 sum; pth]
  and conv1 = vREWR_CONV(vCONJUNCT2 sum) in
  let rec sum_conv tm =
    try conv0 tm
    with Failure _ ->
      (vLAND_CONV(vRAND_CONV num_CONV) +--->
       conv1 +---> vLAND_CONV sum_conv) tm in
  fun tm ->
    let sn,bod = dest_comb tm in
    let s,ntm = dest_comb sn in
    let _,htm = dest_pair ntm in
    if s = sum_tm && is_numeral htm
    then sum_conv tm
    else failwith "REAL_SUM_CONV";;

let vREAL_HORNER_SUM_CONV =
  let sum_tm = [%q {|sum|} ] in
  let pth = prove
   ([%q {|sum(0,1) f = f 0|} ],
    vREWRITE_TAC[num_CONV [%q {|1|} ]; sum; vREAL_ADD_LID; vADD_CLAUSES]) in
  let conv0 = vGEN_REWRITE_CONV vI [vCONJUNCT1 sum; pth]
  and conv1 = vREWR_CONV vSUM_HORNER in
  let rec sum_conv tm =
    try conv0 tm
    with Failure _ ->
      (vLAND_CONV(vRAND_CONV num_CONV) +--->
       conv1 +---> vRAND_CONV (vRAND_CONV sum_conv)) tm in
  fun tm ->
    let sn,bod = dest_comb tm in
    let s,ntm = dest_comb sn in
    let _,htm = dest_pair ntm in
    if s = sum_tm && is_numeral htm
    then sum_conv tm
    else failwith "REAL_HORNER_SUM_CONV";;

(*============================================================================*)
(* Topologies and metric spaces, including metric on real line                *)
(*============================================================================*)

parse_as_infix("re_union",(15,"right"));;
parse_as_infix("re_intersect",(17,"right"));;
parse_as_infix("re_subset",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Minimal amount of set notation is convenient                               *)
(*----------------------------------------------------------------------------*)

let re_Union = new_definition(
  [%q {|re_Union S = \x:A. ?s. S s /\ s x|} ]);;

let re_union = new_definition(
  [%q {|P re_union Q = \x:A. P x \/ Q x|} ]);;

let re_intersect = new_definition
  [%q {|P re_intersect Q = \x:A. P x /\ Q x|} ];;

let re_null = new_definition(
  [%q {|re_null = \x:A. F|} ]);;

let re_universe = new_definition(
  [%q {|re_universe = \x:A. T|} ]);;

let re_subset = new_definition(
  [%q {|P re_subset Q <=> !x:A. P x ==> Q x|} ]);;

let re_compl = new_definition(
  [%q {|re_compl S = \x:A. ~(S x)|} ]);;

let%a vSUBSETA_REFL = prove(
  [%q {|!S:A->bool. S re_subset S|} ],
  vGEN_TAC ----> vREWRITE_TAC[re_subset]);;

let%a vCOMPL_MEM = prove(
  [%q {|!S:A->bool. !x. S x <=> ~(re_compl S x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[re_compl] ---->
  vBETA_TAC ----> vREWRITE_TAC[]);;

let%a vSUBSETA_ANTISYM = prove(
  [%q {|!P:A->bool. !Q. P re_subset Q /\ Q re_subset P <=> (P = Q)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[re_subset] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vAND_FORALL_CONV) ---->
  vREWRITE_TAC[vTAUT [%q {|(a ==> b) /\ (b ==> a) <=> (a <=> b)|} ]] ---->
  vCONV_TAC(vRAND_CONV vFUN_EQ_CONV) ----> vREFL_TAC);;

let%a vSUBSETA_TRANS = prove(
  [%q {|!P:A->bool. !Q R. P re_subset Q /\ Q re_subset R ==> P re_subset R|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[re_subset] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vAND_FORALL_CONV) ---->
  vDISCH_THEN(vMATCH_ACCEPT_TAC -| vGEN [%q {|x:A|} ] -| end_itlist vIMP_TRANS -|
    vCONJUNCTS -| vSPEC [%q {|x:A|} ]));;

(*----------------------------------------------------------------------------*)
(* Characterize an (A)topology                                                *)
(*----------------------------------------------------------------------------*)

let istopology = new_definition(
  [%q {|!L:(A->bool)->bool. istopology L <=>
            L re_null /\
            L re_universe /\
     (!a b. L a /\ L b ==> L (a re_intersect b)) /\
       (!P. P re_subset L ==> L (re_Union P))|} ]);;

let topology_tybij = new_type_definition "topology" ("topology","open")
 (prove([%q {|?t:(A->bool)->bool. istopology t|} ],
        vEXISTS_TAC [%q {|re_universe:(A->bool)->bool|} ] ---->
        vREWRITE_TAC[istopology; re_universe]));;

let%a vTOPOLOGY = prove(
  [%q {|!L:(A)topology. open(L) re_null /\
                   open(L) re_universe /\
            (!x y. open(L) x /\ open(L) y ==> open(L) (x re_intersect y)) /\
              (!P. P re_subset (open L) ==> open(L) (re_Union P))|} ],
  vGEN_TAC ----> vREWRITE_TAC[vGSYM istopology] ---->
  vREWRITE_TAC[topology_tybij]);;

let%a vTOPOLOGY_UNION = prove(
  [%q {|!L:(A)topology. !P. P re_subset (open L) ==> open(L) (re_Union P)|} ],
  vREWRITE_TAC[vTOPOLOGY]);;

(*----------------------------------------------------------------------------*)
(* Characterize a neighbourhood of a point relative to a topology             *)
(*----------------------------------------------------------------------------*)

let neigh = new_definition(
  [%q {|neigh(top)(N,(x:A)) = ?P. open(top) P /\ P re_subset N /\ P x|} ]);;

(*----------------------------------------------------------------------------*)
(* Prove various properties / characterizations of open sets                  *)
(*----------------------------------------------------------------------------*)

let%a vOPEN_OWN_NEIGH = prove(
  [%q {|!S top. !x:A. open(top) S /\ S x ==> neigh(top)(S,x)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[neigh] ---->
  vEXISTS_TAC [%q {|S:A->bool|} ] ----> vASM_REWRITE_TAC[vSUBSETA_REFL]);;

let%a vOPEN_UNOPEN = prove(
  [%q {|!S top. open(top) S <=>
           (re_Union (\P:A->bool. open(top) P /\ P re_subset S) = S)|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vONCE_REWRITE_TAC[vGSYM vSUBSETA_ANTISYM] ---->
    vREWRITE_TAC[re_Union; re_subset] ---->
    vBETA_TAC ----> vCONJ_TAC ----> vGEN_TAC ++-->
     [vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:A->bool|} ] vSTRIP_ASSUME_TAC) ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vFIRST_ASSUM vACCEPT_TAC;
      vDISCH_TAC ----> vEXISTS_TAC [%q {|S:A->bool|} ] ----> vASM_REWRITE_TAC[]];
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
    vMATCH_MP_TAC vTOPOLOGY_UNION ---->
    vREWRITE_TAC[re_subset] ----> vBETA_TAC ---->
    vGEN_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[]]);;

let%a vOPEN_SUBOPEN = prove(
  [%q {|!S top. open(top) S <=>
           !x:A. S x ==> ?P. P x /\ open(top) P /\ P re_subset S|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vGEN_TAC ----> vDISCH_TAC ---->
    vEXISTS_TAC [%q {|S:A->bool|} ] ----> vASM_REWRITE_TAC[vSUBSETA_REFL];
    vDISCH_TAC ----> vC vSUBGOAL_THEN vSUBST1_TAC
     [%q {|S = re_Union (\P:A->bool. open(top) P /\ P re_subset S)|} ] ++-->
     [vONCE_REWRITE_TAC[vGSYM vSUBSETA_ANTISYM] ----> vCONJ_TAC ++-->
       [vONCE_REWRITE_TAC[re_subset] ----> vREWRITE_TAC [re_Union] ---->
        vBETA_TAC ----> vGEN_TAC ---->
        vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
        vDISCH_THEN(vX_CHOOSE_TAC [%q {|P:A->bool|} ]) ----> vEXISTS_TAC [%q {|P:A->bool|} ] ---->
        vASM_REWRITE_TAC[];
        vREWRITE_TAC[re_subset; re_Union] ----> vBETA_TAC ----> vGEN_TAC ---->
        vDISCH_THEN(vCHOOSE_THEN vSTRIP_ASSUME_TAC) ---->
        vFIRST_ASSUM vMATCH_MP_TAC ----> vFIRST_ASSUM vACCEPT_TAC];
      vMATCH_MP_TAC vTOPOLOGY_UNION ----> vONCE_REWRITE_TAC[re_subset] ---->
      vGEN_TAC ----> vBETA_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[]]]);;

let%a vOPEN_NEIGH = prove(
  [%q {|!S top. open(top) S = !x:A. S x ==> ?N. neigh(top)(N,x) /\ N re_subset S|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vGEN_TAC ----> vDISCH_TAC ----> vEXISTS_TAC [%q {|S:A->bool|} ] ---->
    vREWRITE_TAC[vSUBSETA_REFL; neigh] ---->
    vEXISTS_TAC [%q {|S:A->bool|} ] ----> vASM_REWRITE_TAC[vSUBSETA_REFL];
    vDISCH_TAC ----> vONCE_REWRITE_TAC[vOPEN_SUBOPEN] ---->
    vGEN_TAC ----> vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A->bool|} ] (vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC))
    ----> vREWRITE_TAC[neigh] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|P:A->bool|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|P:A->bool|} ] ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vSUBSETA_TRANS ----> vEXISTS_TAC [%q {|N:A->bool|} ] ---->
    vASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Characterize closed sets in a topological space                            *)
(*----------------------------------------------------------------------------*)

let closed = new_definition(
  [%q {|closed(L:(A)topology) S = open(L)(re_compl S)|} ]);;

(*----------------------------------------------------------------------------*)
(* Define limit point in topological space                                    *)
(*----------------------------------------------------------------------------*)

let limpt = new_definition(
  [%q {|limpt(top) x S <=>
      !N:A->bool. neigh(top)(N,x) ==> ?y. ~(x = y) /\ S y /\ N y|} ]);;

(*----------------------------------------------------------------------------*)
(* Prove that a set is closed iff it contains all its limit points            *)
(*----------------------------------------------------------------------------*)

let%a vCLOSED_LIMPT = prove(
  [%q {|!top S. closed(top) S <=> (!x:A. limpt(top) x S ==> S x)|} ],
  vREPEAT vGEN_TAC ----> vCONV_TAC(vONCE_DEPTH_CONV vCONTRAPOS_CONV) ---->
  vREWRITE_TAC[closed; limpt] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vNOT_FORALL_CONV) ---->
  vFREEZE_THEN (fun th -> vONCE_REWRITE_TAC[th])
    (vSPEC [%q {|S:A->bool|} ] vCOMPL_MEM) ---->
  vREWRITE_TAC[] ---->
  vSPEC_TAC([%q {|re_compl(S:A->bool)|} ],[%q {|S:A->bool|} ]) ---->
  vGEN_TAC ----> vREWRITE_TAC[vNOT_IMP] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vNOT_EXISTS_CONV) ---->
  vREWRITE_TAC[vDE_MORGAN_THM] ---->
  vREWRITE_TAC[vOPEN_NEIGH; re_subset] ---->
  vAP_TERM_TAC ----> vABS_TAC ---->
  vASM_CASES_TAC [%q {|(S:A->bool) x|} ] ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vTAUT [%q {|a \/ b \/ ~c <=> c ==> a \/ b|} ]] ---->
  vEQUAL_TAC ---->
  vREWRITE_TAC[vTAUT [%q {|(a <=> b \/ a) <=> b ==> a|} ]] ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vPOP_ASSUM vACCEPT_TAC);;

(*----------------------------------------------------------------------------*)
(* Characterize an (A)metric                                                  *)
(*----------------------------------------------------------------------------*)

let ismet = new_definition(
  [%q {|ismet (m:A#A->real) <=> (!x y. (m(x,y) = &0) <=> (x = y)) /\
                           (!x y z. m(y,z) <= m(x,y) + m(x,z))|} ]);;

let metric_tybij = new_type_definition "metric" ("metric","mdist")
      (prove([%q {|?m:(A#A->real). ismet m|} ],
        vEXISTS_TAC [%q {|\((x:A),(y:A)). if x = y then &0 else &1|} ] ---->
        vREWRITE_TAC[ismet] ---->
        vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ---->
        vCONJ_TAC ----> vREPEAT vGEN_TAC ++-->
         [vBOOL_CASES_TAC [%q {|x:A = y|} ] ----> vREWRITE_TAC[vREAL_10];
          vREPEAT vCOND_CASES_TAC ---->
          vASM_REWRITE_TAC[vREAL_ADD_LID; vREAL_ADD_RID; vREAL_LE_REFL; vREAL_LE_01]
          ----> vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_ADD_LID] ---->
          vTRY(vMATCH_MP_TAC vREAL_LE_ADD2) ---->
          vREWRITE_TAC[vREAL_LE_01; vREAL_LE_REFL] ---->
          vFIRST_ASSUM(vUNDISCH_TAC -| check is_neg -| concl) ---->
          vEVERY_ASSUM(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[]]));;

(*----------------------------------------------------------------------------*)
(* Derive the metric properties                                               *)
(*----------------------------------------------------------------------------*)

let%a vMETRIC_ISMET = prove(
  [%q {|!m:(A)metric. ismet (mdist m)|} ],
  vGEN_TAC ----> vREWRITE_TAC[metric_tybij]);;

let%a vMETRIC_ZERO = prove(
  [%q {|!m:(A)metric. !x y. ((mdist m)(x,y) = &0) <=> (x = y)|} ],
  vREPEAT vGEN_TAC ----> vASSUME_TAC(vSPEC [%q {|m:(A)metric|} ] vMETRIC_ISMET) ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[ismet]) ----> vASM_REWRITE_TAC[]);;

let%a vMETRIC_SAME = prove(
  [%q {|!m:(A)metric. !x. (mdist m)(x,x) = &0|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMETRIC_ZERO]);;

let%a vMETRIC_POS = prove(
  [%q {|!m:(A)metric. !x y. &0 <= (mdist m)(x,y)|} ],
  vREPEAT vGEN_TAC ----> vASSUME_TAC(vSPEC [%q {|m:(A)metric|} ] vMETRIC_ISMET) ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[ismet]) ---->
  vFIRST_ASSUM(vMP_TAC -| vSPECL [[%q {|x:A|} ]; [%q {|y:A|} ]; [%q {|y:A|} ]] -| vCONJUNCT2) ---->
  vREWRITE_TAC[vREWRITE_RULE[] (vSPECL [[%q {|m:(A)metric|} ]; [%q {|y:A|} ]; [%q {|y:A|} ]] vMETRIC_ZERO)]
  ----> vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vREAL_NOT_LE] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_ADD2 -| vW vCONJ) ---->
  vREWRITE_TAC[vREAL_ADD_LID]);;

let%a vMETRIC_SYM = prove(
  [%q {|!m:(A)metric. !x y. (mdist m)(x,y) = (mdist m)(y,x)|} ],
  vREPEAT vGEN_TAC ----> vASSUME_TAC(vSPEC [%q {|m:(A)metric|} ] vMETRIC_ISMET) ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[ismet]) ----> vFIRST_ASSUM
   (vMP_TAC -| vGENL [[%q {|y:A|} ]; [%q {|z:A|} ]] -| vSPECL [[%q {|z:A|} ]; [%q {|y:A|} ]; [%q {|z:A|} ]] -| vCONJUNCT2)
  ----> vREWRITE_TAC[vMETRIC_SAME; vREAL_ADD_RID] ---->
  vDISCH_TAC ----> vASM_REWRITE_TAC[vGSYM vREAL_LE_ANTISYM]);;

let%a vMETRIC_TRIANGLE = prove(
  [%q {|!m:(A)metric. !x y z. (mdist m)(x,z) <= (mdist m)(x,y) + (mdist m)(y,z)|} ],
  vREPEAT vGEN_TAC ----> vASSUME_TAC(vSPEC [%q {|m:(A)metric|} ] vMETRIC_ISMET) ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[ismet]) ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vMETRIC_SYM] ---->
  vASM_REWRITE_TAC[]);;

let%a vMETRIC_NZ = prove(
  [%q {|!m:(A)metric. !x y. ~(x = y) ==> &0 < (mdist m)(x,y)|} ],
  vREPEAT vGEN_TAC ---->
  vSUBST1_TAC(vSYM(vSPECL [[%q {|m:(A)metric|} ]; [%q {|x:A|} ]; [%q {|y:A|} ]] vMETRIC_ZERO)) ---->
  vONCE_REWRITE_TAC[vTAUT [%q {|~a ==> b <=> b \/ a|} ]] ---->
  vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
  vREWRITE_TAC[vGSYM vREAL_LE_LT; vMETRIC_POS]);;

(*----------------------------------------------------------------------------*)
(* Now define metric topology and prove equivalent definition of `open`       *)
(*----------------------------------------------------------------------------*)

let mtop = new_definition(
  [%q {|!m:(A)metric. mtop m =
    topology(\S. !x. S x ==> ?e. &0 < e /\ (!y. (mdist m)(x,y) < e ==> S y))|} ]);;

let%a mtop_istopology = prove(
  [%q {|!m:(A)metric. istopology
    (\S. !x. S x ==> ?e. &0 < e /\ (!y. (mdist m)(x,y) < e ==> S y))|} ],
  vGEN_TAC ---->
  vREWRITE_TAC[istopology; re_null; re_universe; re_Union;
              re_intersect; re_subset] ---->
  vCONV_TAC(vREDEPTH_CONV vBETA_CONV) ---->
  vREWRITE_TAC[] ----> vREPEAT vCONJ_TAC ++-->
   [vEXISTS_TAC [%q {|&1|} ] ----> vMATCH_ACCEPT_TAC vREAL_LT_01;
        vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ---->
    vDISCH_THEN(fun th -> vPOP_ASSUM(vCONJUNCTS_THEN(vMP_TAC -| vSPEC [%q {|x:A|} ]))
                    ----> vREWRITE_TAC[th]) ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|e1:real|} ]) ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|e2:real|} ]) ---->
    vREPEAT_TCL vDISJ_CASES_THEN vMP_TAC
        (vSPECL [[%q {|e1:real|} ]; [%q {|e2:real|} ]] vREAL_LT_TOTAL) ++-->
     [vDISCH_THEN vSUBST_ALL_TAC ----> vEXISTS_TAC [%q {|e2:real|} ] ---->
      vASM_REWRITE_TAC[] ----> vGEN_TAC ---->
      vDISCH_THEN(fun th -> vEVERY_ASSUM(vASSUME_TAC -| vC vMATCH_MP th -| vCONJUNCT2))
      ----> vASM_REWRITE_TAC[];
      vDISCH_THEN((---->) (vEXISTS_TAC [%q {|e1:real|} ]) -| vMP_TAC);
      vDISCH_THEN((---->) (vEXISTS_TAC [%q {|e2:real|} ]) -| vMP_TAC)] ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(fun th2 -> vGEN_TAC ----> vDISCH_THEN(fun th1 ->
      vASSUME_TAC th1 ----> vASSUME_TAC (vMATCH_MP vREAL_LT_TRANS (vCONJ th1 th2))))
    ----> vCONJ_TAC ----> vFIRST_ASSUM (vMATCH_MP_TAC -| vCONJUNCT2)
    ----> vFIRST_ASSUM vACCEPT_TAC;
    vGEN_TAC ----> vDISCH_TAC ----> vGEN_TAC ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|y:A->bool|} ]
     (fun th -> vPOP_ASSUM(vX_CHOOSE_TAC [%q {|e:real|} ] -| vC vMATCH_MP (vCONJUNCT2 th) -|
                     vC vMATCH_MP (vCONJUNCT1 th)) ----> vASSUME_TAC th)) ---->
    vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|z:A|} ] ---->
    vDISCH_THEN
      (fun th -> vFIRST_ASSUM(vASSUME_TAC -| vC vMATCH_MP th -| vCONJUNCT2)) ---->
    vEXISTS_TAC [%q {|y:A->bool|} ] ----> vASM_REWRITE_TAC[]]);;

let%a vMTOP_OPEN = prove(
  [%q {|!m:(A)metric. open(mtop m) S <=>
      (!x. S x ==> ?e. &0 < e /\ (!y. (mdist m(x,y)) < e ==> S y))|} ],
  vGEN_TAC ----> vREWRITE_TAC[mtop] ---->
  vREWRITE_TAC[vREWRITE_RULE[topology_tybij] mtop_istopology] ---->
  vBETA_TAC ----> vREFL_TAC);;

(*----------------------------------------------------------------------------*)
(* Define open ball in metric space + prove basic properties                  *)
(*----------------------------------------------------------------------------*)

let ball = new_definition(
  [%q {|!m:(A)metric. !x e. ball(m)(x,e) = \y. (mdist m)(x,y) < e|} ]);;

let%a vBALL_OPEN = prove(
  [%q {|!m:(A)metric. !x e. &0 < e ==> open(mtop(m))(ball(m)(x,e))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vMTOP_OPEN] ---->
  vX_GEN_TAC [%q {|z:A|} ] ----> vREWRITE_TAC[ball] ----> vBETA_TAC ---->
  vDISCH_THEN(vASSUME_TAC -| vONCE_REWRITE_RULE[vGSYM vREAL_SUB_LT]) ---->
  vEXISTS_TAC [%q {|e - mdist(m:(A)metric)(x,z)|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|y:A|} ] ----> vREWRITE_TAC[vREAL_LT_SUB_LADD] ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|mdist(m)((x:A),z) + mdist(m)(z,y)|} ] ---->
  vASM_REWRITE_TAC[vMETRIC_TRIANGLE]);;

let%a vBALL_NEIGH = prove(
  [%q {|!m:(A)metric. !x e. &0 < e ==> neigh(mtop(m))(ball(m)(x,e),x)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[neigh] ----> vEXISTS_TAC [%q {|ball(m)((x:A),e)|} ] ---->
  vREWRITE_TAC[vSUBSETA_REFL] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vBALL_OPEN;
    vREWRITE_TAC[ball] ----> vBETA_TAC ----> vREWRITE_TAC[vMETRIC_SAME]] ---->
  vPOP_ASSUM vACCEPT_TAC);;

(*----------------------------------------------------------------------------*)
(* Characterize limit point in a metric topology                              *)
(*----------------------------------------------------------------------------*)

let%a vMTOP_LIMPT = prove(
  [%q {|!m:(A)metric. !x S. limpt(mtop m) x S <=>
      !e. &0 < e ==> ?y. ~(x = y) /\ S y /\ (mdist m)(x,y) < e|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[limpt] ----> vEQ_TAC ++-->
   [vDISCH_THEN((---->) (vGEN_TAC ----> vDISCH_TAC) -|
      vMP_TAC -| vSPEC [%q {|ball(m)((x:A),e)|} ]) ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vBALL_NEIGH th]) ---->
    vREWRITE_TAC[ball] ----> vBETA_TAC ----> vDISCH_THEN vACCEPT_TAC;
    vDISCH_TAC ----> vGEN_TAC ----> vREWRITE_TAC[neigh] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|P:A->bool|} ]
      (vCONJUNCTS_THEN2 vMP_TAC vSTRIP_ASSUME_TAC)) ---->
    vREWRITE_TAC[vMTOP_OPEN] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x:A|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
    vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e:real|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|y:A|} ] vSTRIP_ASSUME_TAC) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|y:A|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC ----> vEXISTS_TAC [%q {|y:A|} ] ----> vASM_REWRITE_TAC[] ---->
    vUNDISCH_TAC [%q {|(P:A->bool) re_subset N|} ] ---->
    vREWRITE_TAC[re_subset] ----> vDISCH_THEN vMATCH_MP_TAC ---->
    vFIRST_ASSUM vACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Define the usual metric on the real line                                   *)
(*----------------------------------------------------------------------------*)

let%a vISMET_R1 = prove(
  [%q {|ismet (\(x,y). abs(y - x))|} ],
  vREWRITE_TAC[ismet] ----> vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ---->
  vCONJ_TAC ----> vREPEAT vGEN_TAC ++-->
   [vREWRITE_TAC[vABS_ZERO; vREAL_SUB_0] ---->
    vCONV_TAC(vRAND_CONV vSYM_CONV) ----> vREFL_TAC;
    vSUBST1_TAC(vSYM(vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vREAL_NEG_SUB)) ---->
    vREWRITE_TAC[vABS_NEG] ----> vSUBGOAL_THEN [%q {|z - y = (x - y) + (z - x)|} ]
      (fun th -> vSUBST1_TAC th ----> vMATCH_ACCEPT_TAC vABS_TRIANGLE) ---->
    vREWRITE_TAC[real_sub] ---->
    vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
      [%q {|(a + b) + (c + d) = (d + a) + (c + b)|} ]] ---->
    vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID]]);;

let mr1 = new_definition(
  [%q {|mr1 = metric(\(x,y). abs(y - x))|} ]);;

let%a vMR1_DEF = prove(
  [%q {|!x y. (mdist mr1)(x,y) = abs(y - x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[mr1; vREWRITE_RULE[metric_tybij] vISMET_R1]
  ----> vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ----> vREFL_TAC);;

let%a vMR1_ADD = prove(
  [%q {|!x d. (mdist mr1)(x,x+d) = abs(d)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMR1_DEF; vREAL_ADD_SUB]);;

let%a vMR1_SUB = prove(
  [%q {|!x d. (mdist mr1)(x,x-d) = abs(d)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMR1_DEF; vREAL_SUB_SUB; vABS_NEG]);;

let%a vMR1_ADD_LE = prove(
  [%q {|!x d. &0 <= d ==> ((mdist mr1)(x,x+d) = d)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[vMR1_ADD; real_abs]);;

let%a vMR1_SUB_LE = prove(
  [%q {|!x d. &0 <= d ==> ((mdist mr1)(x,x-d) = d)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[vMR1_SUB; real_abs]);;

let%a vMR1_ADD_LT = prove(
  [%q {|!x d. &0 < d ==> ((mdist mr1)(x,x+d) = d)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
  vMATCH_ACCEPT_TAC vMR1_ADD_LE);;

let%a vMR1_SUB_LT = prove(
  [%q {|!x d. &0 < d ==> ((mdist mr1)(x,x-d) = d)|} ],
   vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
  vMATCH_ACCEPT_TAC vMR1_SUB_LE);;

let%a vMR1_BETWEEN1 = prove(
  [%q {|!x y z. x < z /\ (mdist mr1)(x,y) < (z - x) ==> y < z|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMR1_DEF; vABS_BETWEEN1]);;

(*----------------------------------------------------------------------------*)
(* Every real is a limit point of the real line                               *)
(*----------------------------------------------------------------------------*)

let%a vMR1_LIMPT = prove(
  [%q {|!x. limpt(mtop mr1) x re_universe|} ],
  vGEN_TAC ----> vREWRITE_TAC[vMTOP_LIMPT; re_universe] ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vEXISTS_TAC [%q {|x + (e / &2)|} ] ---->
  vREWRITE_TAC[vMR1_ADD] ---->
  vSUBGOAL_THEN [%q {|&0 <= (e / &2)|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
    vASM_REWRITE_TAC[vREAL_LT_HALF1]; vALL_TAC] ---->
  vASM_REWRITE_TAC[real_abs; vREAL_LT_HALF2] ---->
  vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
  vREWRITE_TAC[vREAL_ADD_RID_UNIQ] ---->
  vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
  vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
  vASM_REWRITE_TAC[vREAL_LT_HALF1]);;

(*============================================================================*)
(* Theory of Moore-Smith covergence nets, and special cases like sequences    *)
(*============================================================================*)

parse_as_infix ("tends",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Basic definitions: directed set, net, bounded net, pointwise limit         *)
(*----------------------------------------------------------------------------*)

let dorder = new_definition(
  [%q {|dorder (g:A->A->bool) <=>
     !x y. g x x /\ g y y ==> ?z. g z z /\ (!w. g w z ==> g w x /\ g w y)|} ]);;

let tends = new_definition
  [%q {|(s tends l)(top,g) <=>
      !N:A->bool. neigh(top)(N,l) ==>
            ?n:B. g n n /\ !m:B. g m n ==> N(s m)|} ];;

let bounded = new_definition(
  [%q {|bounded((m:(A)metric),(g:B->B->bool)) f <=>
      ?k x N. g N N /\ (!n. g n N ==> (mdist m)(f(n),x) < k)|} ]);;

let tendsto = new_definition(
  [%q {|tendsto((m:(A)metric),x) y z <=>
      &0 < (mdist m)(x,y) /\ (mdist m)(x,y) <= (mdist m)(x,z)|} ]);;

parse_as_infix("-->",(12,"right"));;

override_interface ("-->",[%q {|(tends)|} ]);;

let%a vDORDER_LEMMA = prove(
  [%q {|!g:A->A->bool.
      dorder g ==>
        !P Q. (?n. g n n /\ (!m. g m n ==> P m)) /\
              (?n. g n n /\ (!m. g m n ==> Q m))
                  ==> (?n. g n n /\ (!m. g m n ==> P m /\ Q m))|} ],
  vGEN_TAC ----> vREWRITE_TAC[dorder] ----> vDISCH_TAC ----> vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_THEN [%q {|N1:A|} ] vSTRIP_ASSUME_TAC)
                             (vX_CHOOSE_THEN [%q {|N2:A|} ] vSTRIP_ASSUME_TAC)) ---->
  vFIRST_ASSUM(vMP_TAC -| vSPECL [[%q {|N1:A|} ]; [%q {|N2:A|} ]]) ---->
  vREWRITE_TAC[vASSUME [%q {|(g:A->A->bool) N1 N1|} ];vASSUME [%q {|(g:A->A->bool) N2 N2|} ]] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:A|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|n:A|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|m:A|} ] ----> vDISCH_TAC ---->
  vCONJ_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vFIRST_ASSUM(vUNDISCH_TAC -|
    check(is_conj -| snd -| dest_imp -| snd -| dest_forall) -| concl) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|m:A|} ]) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_TAC ----> vASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Following tactic is useful in the following proofs                         *)
(*----------------------------------------------------------------------------*)

let vDORDER_THEN tac th =
  let [t1;t2] = map (rand -| rand -| body -| rand) (conjuncts(concl th)) in
  let dog = (rator -| rator -| rand -| rator -| body) t1 in
  let thl = map ((uncurry vX_BETA_CONV) -| (vI $-$ rand) -| dest_abs) [t1;t2] in
  let th1 = vCONV_RULE(vEXACT_CONV thl) th in
  let th2 = vMATCH_MP vDORDER_LEMMA (vASSUME (list_mk_icomb "dorder" [dog])) in
  let th3 = vMATCH_MP th2 th1 in
  let th4 = vCONV_RULE(vEXACT_CONV(map vSYM thl)) th3 in
  tac th4;;

(*----------------------------------------------------------------------------*)
(* Show that sequences and pointwise limits in a metric space are directed    *)
(*----------------------------------------------------------------------------*)

let%a vDORDER_NGE = prove(
  [%q {|dorder ((>=) :num->num->bool)|} ],
  vREWRITE_TAC[dorder; vGE; vLE_REFL] ---->
  vREPEAT vGEN_TAC ---->
  vDISJ_CASES_TAC(vSPECL [[%q {|x:num|} ]; [%q {|y:num|} ]] vLE_CASES) ++-->
    [vEXISTS_TAC [%q {|y:num|} ]; vEXISTS_TAC [%q {|x:num|} ]] ---->
  vGEN_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vLE_TRANS ++-->
    [vEXISTS_TAC [%q {|y:num|} ]; vEXISTS_TAC [%q {|x:num|} ]] ---->
  vASM_REWRITE_TAC[]);;

let%a vDORDER_TENDSTO = prove(
  [%q {|!m:(A)metric. !x. dorder(tendsto(m,x))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[dorder; tendsto] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|u:A|} ]; [%q {|v:A|} ]] ---->
  vREWRITE_TAC[vREAL_LE_REFL] ---->
  vDISCH_THEN vSTRIP_ASSUME_TAC ----> vASM_REWRITE_TAC[] ---->
  vDISJ_CASES_TAC(vSPECL [[%q {|(mdist m)((x:A),v)|} ]; [%q {|(mdist m)((x:A),u)|} ]]
    vREAL_LE_TOTAL)
  ++--> [vEXISTS_TAC [%q {|v:A|} ]; vEXISTS_TAC [%q {|u:A|} ]] ----> vASM_REWRITE_TAC[] ---->
  vGEN_TAC ----> vDISCH_THEN vSTRIP_ASSUME_TAC ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ----> vFIRST_ASSUM (fun th ->
   (vEXISTS_TAC -| rand -| concl) th ----> vASM_REWRITE_TAC[] ----> vNO_TAC));;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of limit in a metric topology                     *)
(*----------------------------------------------------------------------------*)

let%a vMTOP_TENDS = prove(
  [%q {|!d g. !x:B->A. !x0. (x --> x0)(mtop(d),g) <=>
     !e. &0 < e ==> ?n. g n n /\ !m. g m n ==> mdist(d)(x(m),x0) < e|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends] ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ---->
    vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|ball(d)((x0:A),e)|} ]) ---->
    vW(vC vSUBGOAL_THEN vMP_TAC -| funpow 2 (rand -| rator) -| snd) ++-->
     [vMATCH_MP_TAC vBALL_NEIGH ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ----> vREWRITE_TAC[ball] ---->
    vBETA_TAC ----> vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV)
     [vMETRIC_SYM] ----> vREWRITE_TAC[];
    vGEN_TAC ----> vREWRITE_TAC[neigh] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|P:A->bool|} ] vSTRIP_ASSUME_TAC) ---->
    vUNDISCH_TAC [%q {|open(mtop(d)) (P:A->bool)|} ] ---->
    vREWRITE_TAC[vMTOP_OPEN] ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x0:A|} ]) ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
    vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|d:real|} ]) ---->
    vREWRITE_TAC[vASSUME [%q {|&0 < d|} ]] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:B|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|n:B|} ] ----> vASM_REWRITE_TAC[] ---->
    vGEN_TAC ----> vDISCH_TAC ---->
    vUNDISCH_TAC [%q {|(P:A->bool) re_subset N|} ] ---->
    vREWRITE_TAC[re_subset] ----> vDISCH_TAC ---->
    vREPEAT(vFIRST_ASSUM vMATCH_MP_TAC) ---->
    vONCE_REWRITE_TAC[vMETRIC_SYM] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vFIRST_ASSUM vACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Prove that a net in a metric topology cannot converge to different limits  *)
(*----------------------------------------------------------------------------*)

let%a vMTOP_TENDS_UNIQ = prove(
  [%q {|!g d. dorder (g:B->B->bool) ==>
      (x --> x0)(mtop(d),g) /\ (x --> x1)(mtop(d),g) ==> (x0:A = x1)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[vMTOP_TENDS] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vAND_FORALL_CONV) ---->
  vREWRITE_TAC[vTAUT [%q {|(a ==> b) /\ (a ==> c) <=> a ==> b /\ c|} ]] ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_TAC ---->
  vCONV_TAC vNOT_FORALL_CONV ---->
  vEXISTS_TAC [%q {|mdist(d:(A)metric)(x0,x1) / &2|} ] ---->
  vW(vC vSUBGOAL_THEN vASSUME_TAC -| rand -| rator -| rand -| snd) ++-->
   [vREWRITE_TAC[vREAL_LT_HALF1] ----> vMATCH_MP_TAC vMETRIC_NZ ---->
    vFIRST_ASSUM vACCEPT_TAC; vALL_TAC] ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN(vDORDER_THEN vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:B|} ] (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|N:B|} ]) ----> vASM_REWRITE_TAC[] ---->
  vBETA_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_ADD2) ---->
  vREWRITE_TAC[vREAL_HALF_DOUBLE; vREAL_NOT_LT] ---->
  vGEN_REWRITE_TAC(vRAND_CONV -| vLAND_CONV) [vMETRIC_SYM] ---->
  vMATCH_ACCEPT_TAC vMETRIC_TRIANGLE);;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of limit of a sequence in a metric topology       *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_TENDS = prove(
  [%q {|!d:(A)metric. !x x0. (x --> x0)(mtop(d), (>=) :num->num->bool) <=>
     !e. &0 < e ==> ?N. !n. n >= N ==> mdist(d)(x(n),x0) < e|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMTOP_TENDS; vGE; vLE_REFL]);;

(*----------------------------------------------------------------------------*)
(* And of limit of function between metric spaces                             *)
(*----------------------------------------------------------------------------*)

let%a vLIM_TENDS = prove(
  [%q {|!m1:(A)metric. !m2:(B)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f --> y0)(mtop(m2),tendsto(m1,x0)) <=>
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (mdist m1)(x,x0) /\ (mdist m1)(x,x0) <= d
                ==> (mdist m2)(f(x),y0) < e)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[vMTOP_TENDS; tendsto] ---->
  vAP_TERM_TAC ----> vABS_TAC ---->
  vASM_CASES_TAC [%q {|&0 < e|} ] ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vREAL_LE_REFL] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:A|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|(mdist m1)((x0:A),z)|} ] ----> vASM_REWRITE_TAC[] ---->
    vGEN_TAC ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[] ---->
    vSUBST1_TAC(vISPECL [[%q {|m1:(A)metric|} ]; [%q {|x0:A|} ]; [%q {|x:A|} ]] vMETRIC_SYM) ---->
    vASM_REWRITE_TAC[];
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
    vUNDISCH_TAC [%q {|limpt(mtop m1) (x0:A) re_universe|} ] ---->
    vREWRITE_TAC[vMTOP_LIMPT] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|d:real|} ]) ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[re_universe] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|y:A|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|y:A|} ] ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vMETRIC_NZ ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vX_GEN_TAC [%q {|x:A|} ] ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vONCE_REWRITE_TAC[vMETRIC_SYM] ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|(mdist m1)((x0:A),y)|} ] ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
    vFIRST_ASSUM vACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Similar, more conventional version, is also true at a limit point          *)
(*----------------------------------------------------------------------------*)

let%a vLIM_TENDS2 = prove(
  [%q {|!m1:(A)metric. !m2:(B)metric. !f x0 y0.
      limpt(mtop m1) x0 re_universe ==>
        ((f --> y0)(mtop(m2),tendsto(m1,x0)) <=>
          !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < (mdist m1)(x,x0) /\ (mdist m1)(x,x0) < d ==>
              (mdist m2)(f(x),y0) < e)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vLIM_TENDS th]) ---->
  vAP_TERM_TAC ----> vABS_TAC ----> vAP_TERM_TAC ---->
  vEQ_TAC ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ++-->
   [vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vGEN_TAC ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[];
    vEXISTS_TAC [%q {|d / &2|} ] ----> vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
    vGEN_TAC ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|d / &2|} ] ----> vASM_REWRITE_TAC[vREAL_LT_HALF2]]);;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of boundedness for the real line                  *)
(*----------------------------------------------------------------------------*)

let%a vMR1_BOUNDED = prove(
  [%q {|!(g:A->A->bool) f. bounded(mr1,g) f <=>
        ?k N. g N N /\ (!n. g n N ==> abs(f n) < k)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[bounded; vMR1_DEF] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV -| vABS_CONV)
   [vSWAP_EXISTS_THM] ---->
  vONCE_REWRITE_TAC[vSWAP_EXISTS_THM] ---->
  vAP_TERM_TAC ----> vABS_TAC ---->
  vCONV_TAC(vREDEPTH_CONV vEXISTS_AND_CONV) ---->
  vAP_TERM_TAC ----> vEQ_TAC ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:real|} ] vMP_TAC) ++-->
   [vDISCH_THEN(vX_CHOOSE_TAC [%q {|x:real|} ]) ---->
    vEXISTS_TAC [%q {|abs(x) + k|} ] ----> vGEN_TAC ----> vDISCH_TAC ---->
    vSUBST1_TAC(vSYM(vSPECL [[%q {|(f:A->real) n|} ]; [%q {|x:real|} ]] vREAL_SUB_ADD)) ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|abs((f:A->real) n - x) + abs(x)|} ] ---->
    vREWRITE_TAC[vABS_TRIANGLE] ---->
    vGEN_REWRITE_TAC vRAND_CONV [vREAL_ADD_SYM] ---->
    vREWRITE_TAC[vREAL_LT_RADD] ---->
    vONCE_REWRITE_TAC[vABS_SUB] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vFIRST_ASSUM vACCEPT_TAC;
    vDISCH_TAC ----> vMAP_EVERY vEXISTS_TAC [[%q {|k:real|} ]; [%q {|&0|} ]] ---->
    vASM_REWRITE_TAC[vREAL_SUB_LZERO; vABS_NEG]]);;

(*----------------------------------------------------------------------------*)
(* Firstly, prove useful forms of null and bounded nets                       *)
(*----------------------------------------------------------------------------*)

let%a vNET_NULL = prove(
  [%q {|!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) <=> ((\n. x(n) - x0) --> &0)(mtop(mr1),g)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMTOP_TENDS] ----> vBETA_TAC ---->
  vREWRITE_TAC[vMR1_DEF; vREAL_SUB_LZERO] ----> vEQUAL_TAC ---->
  vREWRITE_TAC[vREAL_NEG_SUB]);;

let%a vNET_CONV_BOUNDED = prove(
  [%q {|!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) ==> bounded(mr1,g) x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMTOP_TENDS; bounded] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|&1|} ]) ---->
  vREWRITE_TAC[vREAL_LT; num_CONV [%q {|1|} ]; vLT_0] ---->
  vREWRITE_TAC[vGSYM(num_CONV [%q {|1|} ])] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] vSTRIP_ASSUME_TAC) ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|&1|} ]; [%q {|x0:real|} ]; [%q {|N:A|} ]] ---->
  vASM_REWRITE_TAC[]);;

let%a vNET_CONV_NZ = prove(
  [%q {|!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        ?N. g N N /\ (!n. g n N ==> ~(x n = &0))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMTOP_TENDS; bounded] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vMP_TAC -| vSPEC [%q {|abs(x0)|} ]) vASSUME_TAC) ---->
  vASM_REWRITE_TAC[vGSYM vABS_NZ] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vDISCH_TAC ----> vEXISTS_TAC [%q {|N:A|} ] ----> vASM_REWRITE_TAC[] ---->
  vGEN_TAC ----> vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[] ---->
  vDISCH_THEN vSUBST1_TAC ---->
  vREWRITE_TAC[vMR1_DEF; vREAL_SUB_RZERO; vREAL_LT_REFL]);;

let%a vNET_CONV_IBOUNDED = prove(
  [%q {|!g:A->A->bool. !x x0.
      (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0) ==>
        bounded(mr1,g) (\n. inv(x n))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMTOP_TENDS; vMR1_BOUNDED; vMR1_DEF] ---->
  vBETA_TAC ----> vREWRITE_TAC[vABS_NZ] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|abs(x0) / &2|} ]) ---->
  vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] vSTRIP_ASSUME_TAC) ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|&2 / abs(x0)|} ]; [%q {|N:A|} ]] ---->
  vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|n:A|} ] ---->
  vDISCH_THEN(vANTE_RES_THEN vASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|(abs(x0) / &2) < abs(x(n:A))|} ] vASSUME_TAC ++-->
   [vSUBST1_TAC(vSYM(vSPECL [[%q {|abs(x0) / &2|} ]; [%q {|abs(x0) / &2|} ]; [%q {|abs(x(n:A))|} ]]
      vREAL_LT_LADD)) ---->
    vREWRITE_TAC[vREAL_HALF_DOUBLE] ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|abs(x0 - x(n:A)) + abs(x(n))|} ] ---->
    vASM_REWRITE_TAC[vREAL_LT_RADD] ---->
    vSUBST1_TAC(vSYM(vAP_TERM [%q {|abs|} ]
      (vSPECL [[%q {|x0:real|} ]; [%q {|x(n:A):real|} ]] vREAL_SUB_ADD))) ---->
    vMATCH_ACCEPT_TAC vABS_TRIANGLE; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|&0 < abs(x(n:A))|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|abs(x0) / &2|} ] ---->
    vASM_REWRITE_TAC[vREAL_LT_HALF1]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|&2 / abs(x0) = inv(abs(x0) / &2)|} ] vSUBST1_TAC ++-->
   [vMATCH_MP_TAC vREAL_RINV_UNIQ ----> vREWRITE_TAC[real_div] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
        [%q {|(a * b) * (c * d) = (d * a) * (b * c)|} ]] ---->
    vSUBGOAL_THEN [%q {|~(abs(x0) = &0) /\ ~(&2 = &0)|} ]
      (fun th -> vCONJUNCTS_THEN(vSUBST1_TAC -| vMATCH_MP vREAL_MUL_LINV) th
            ----> vREWRITE_TAC[vREAL_MUL_LID]) ---->
    vCONJ_TAC ++-->
     [vASM_REWRITE_TAC[vABS_NZ; vABS_ABS];
      vREWRITE_TAC[vREAL_INJ; num_CONV [%q {|2|} ]; vNOT_SUC]]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|~(x(n:A) = &0)|} ] (vSUBST1_TAC -| vMATCH_MP vABS_INV) ++-->
   [vASM_REWRITE_TAC[vABS_NZ]; vALL_TAC] ---->
  vMATCH_MP_TAC vREAL_LT_INV2 ----> vASM_REWRITE_TAC[vREAL_LT_HALF1]);;

(*----------------------------------------------------------------------------*)
(* Now combining theorems for null nets                                       *)
(*----------------------------------------------------------------------------*)

let%a vNET_NULL_ADD = prove(
  [%q {|!g:A->A->bool. dorder g ==>
        !x y. (x --> &0)(mtop(mr1),g) /\ (y --> &0)(mtop(mr1),g) ==>
                ((\n. x(n) + y(n)) --> &0)(mtop(mr1),g)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vMTOP_TENDS; vMR1_DEF; vREAL_SUB_LZERO; vABS_NEG] ---->
  vDISCH_THEN((---->) (vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC) -|
    vMP_TAC -| end_itlist vCONJ -| map (vSPEC [%q {|e / &2|} ]) -| vCONJUNCTS) ---->
  vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
  vDISCH_THEN(vDORDER_THEN (vX_CHOOSE_THEN [%q {|N:A|} ] vSTRIP_ASSUME_TAC)) ---->
  vEXISTS_TAC [%q {|N:A|} ] ----> vASM_REWRITE_TAC[] ---->
  vGEN_TAC ----> vDISCH_THEN(vANTE_RES_THEN vASSUME_TAC) ---->
  vBETA_TAC ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|abs(x(m:A)) + abs(y(m:A))|} ] ---->
  vREWRITE_TAC[vABS_TRIANGLE] ----> vRULE_ASSUM_TAC vBETA_RULE ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_HALF_DOUBLE] ---->
  vMATCH_MP_TAC vREAL_LT_ADD2 ----> vASM_REWRITE_TAC[]);;

let%a vNET_NULL_MUL = prove(
  [%q {|!g:A->A->bool. dorder g ==>
      !x y. bounded(mr1,g) x /\ (y --> &0)(mtop(mr1),g) ==>
              ((\n. x(n) * y(n)) --> &0)(mtop(mr1),g)|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMR1_BOUNDED] ---->
  vREWRITE_TAC[vMTOP_TENDS; vMR1_DEF; vREAL_SUB_LZERO; vABS_NEG] ---->
  vDISCH_THEN((---->) (vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC) -| vMP_TAC) ---->
  vCONV_TAC(vLAND_CONV vLEFT_AND_EXISTS_CONV) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:real|} ] vMP_TAC) ---->
  vDISCH_THEN(vASSUME_TAC -| uncurry vCONJ -| (vI $-$ vSPEC [%q {|e / k|} ]) -| vCONJ_PAIR) ---->
  vSUBGOAL_THEN [%q {|&0 < k|} ] vASSUME_TAC ++-->
   [vFIRST_ASSUM(vX_CHOOSE_THEN [%q {|N:A|} ]
      (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) -| vCONJUNCT1) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|N:A|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|abs(x(N:A))|} ] ----> vASM_REWRITE_TAC[vABS_POS]; vALL_TAC] ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_conj -| concl) ---->
  vSUBGOAL_THEN [%q {|&0 < e / k|} ] vASSUME_TAC ++-->
   [vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_LT_RDIV_0 th] ---->
    vASM_REWRITE_TAC[] ----> vNO_TAC); vALL_TAC] ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vDORDER_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] vSTRIP_ASSUME_TAC)) ---->
  vEXISTS_TAC [%q {|N:A|} ] ----> vASM_REWRITE_TAC[] ---->
  vGEN_TAC ----> vDISCH_THEN(vANTE_RES_THEN (vASSUME_TAC -| vBETA_RULE)) ---->
  vSUBGOAL_THEN [%q {|e = k * (e / k)|} ] vSUBST1_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_LMUL ---->
    vDISCH_THEN vSUBST_ALL_TAC ----> vUNDISCH_TAC [%q {|&0 < &0|} ] ---->
    vREWRITE_TAC[vREAL_LT_REFL]; vALL_TAC] ----> vBETA_TAC ---->
  vREWRITE_TAC[vABS_MUL] ----> vMATCH_MP_TAC vREAL_LT_MUL2_ALT ---->
  vASM_REWRITE_TAC[vABS_POS]);;

let%a vNET_NULL_CMUL = prove(
  [%q {|!g:A->A->bool. !k x.
      (x --> &0)(mtop(mr1),g) ==> ((\n. k * x(n)) --> &0)(mtop(mr1),g)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMTOP_TENDS; vMR1_DEF] ---->
  vBETA_TAC ----> vREWRITE_TAC[vREAL_SUB_LZERO; vABS_NEG] ---->
  vDISCH_THEN((---->) (vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC) -| vMP_TAC) ---->
  vASM_CASES_TAC [%q {|k = &0|} ] ++-->
   [vDISCH_THEN(vMP_TAC -| vSPEC [%q {|&1|} ]) ---->
    vREWRITE_TAC[vREAL_LT; num_CONV [%q {|1|} ]; vLESS_SUC_REFL] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|N:A|} ] ---->
    vASM_REWRITE_TAC[vREAL_MUL_LZERO; real_abs; vREAL_LE_REFL];
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / abs(k)|} ]) ---->
    vSUBGOAL_THEN [%q {|&0 < e / abs(k)|} ] vASSUME_TAC ++-->
     [vREWRITE_TAC[real_div] ----> vMATCH_MP_TAC vREAL_LT_MUL ---->
      vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_INV_POS ---->
      vASM_REWRITE_TAC[vGSYM vABS_NZ]; vALL_TAC] ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|N:A|} ] ----> vASM_REWRITE_TAC[] ---->
    vGEN_TAC ----> vDISCH_THEN(vANTE_RES_THEN vASSUME_TAC) ---->
    vSUBGOAL_THEN [%q {|e = abs(k) * (e / abs(k))|} ] vSUBST1_TAC ++-->
     [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_LMUL ---->
      vASM_REWRITE_TAC[vABS_ZERO]; vALL_TAC] ---->
    vREWRITE_TAC[vABS_MUL] ---->
    vSUBGOAL_THEN [%q {|&0 < abs k|} ] (fun th -> vREWRITE_TAC[vMATCH_MP vREAL_LT_LMUL_EQ th])
    ----> vASM_REWRITE_TAC[vGSYM vABS_NZ]]);;

(*----------------------------------------------------------------------------*)
(* Now real arithmetic theorems for convergent nets                           *)
(*----------------------------------------------------------------------------*)

let%a vNET_ADD = prove(
  [%q {|!g:A->A->bool x x0 y y0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g)
            ==> ((\n. x(n) + y(n)) --> (x0 + y0))(mtop(mr1),g)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREPEAT vGEN_TAC ---->
  vONCE_REWRITE_TAC[vNET_NULL] ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM
    (vMP_TAC -| vC vMATCH_MP th -| vMATCH_MP vNET_NULL_ADD))
  ----> vMATCH_MP_TAC vEQ_IMP ----> vEQUAL_TAC ---->
  vBETA_TAC ----> vREWRITE_TAC[real_sub; vREAL_NEG_ADD] ---->
  vREWRITE_TAC[vREAL_ADD_AC]);;

let%a vNET_NEG = prove(
  [%q {|!g:A->A->bool x x0.
        dorder g
        ==> ((x --> x0)(mtop(mr1),g) <=>
            ((\n. --(x n)) --> --x0)(mtop(mr1),g))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[vMTOP_TENDS; vMR1_DEF] ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_SUB_NEG2] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vABS_SUB] ---->
  vREFL_TAC);;

let%a vNET_SUB = prove(
  [%q {|!g:A->A->bool x x0 y y0.
      dorder g
      ==> (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g)
          ==> ((\n. x(n) - y(n)) --> (x0 - y0))(mtop(mr1),g)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[real_sub] ---->
  vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|n:A|} ] [%q {|--(y(n:A))|} ]]) ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vNET_ADD) ---->
  vASM_REWRITE_TAC[] ---->
  vFIRST_ASSUM(fun th -> vONCE_REWRITE_TAC[vGSYM(vMATCH_MP vNET_NEG th)]) ---->
  vASM_REWRITE_TAC[]);;

let%a vNET_MUL = prove(
  [%q {|!g:A->A->bool x y x0 y0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\ (y --> y0)(mtop(mr1),g)
            ==> ((\n. x(n) * y(n)) --> (x0 * y0))(mtop(mr1),g)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vNET_NULL] ---->
  vDISCH_TAC ----> vBETA_TAC ---->
  vSUBGOAL_THEN [%q {|!a b c d. (a * b) - (c * d) = (a * (b - d)) + ((a - c) * d)|} ]
  (fun th -> vONCE_REWRITE_TAC[th]) ++-->
   [vREPEAT vGEN_TAC ---->
    vREWRITE_TAC[real_sub; vREAL_LDISTRIB; vREAL_RDISTRIB; vGSYM vREAL_ADD_ASSOC]
    ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL] ---->
    vREWRITE_TAC[vREAL_ADD_ASSOC; vREAL_ADD_LINV; vREAL_ADD_LID]; vALL_TAC] ---->
  vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|n:A|} ] [%q {|x(n:A) * (y(n) - y0)|} ]]) ---->
  vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|n:A|} ] [%q {|(x(n:A) - x0) * y0|} ]]) ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vNET_NULL_ADD) ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vREAL_MUL_SYM] ---->
  (vCONV_TAC -| vEXACT_CONV -| map (vX_BETA_CONV [%q {|n:A|} ]))
   [[%q {|y(n:A) - y0|} ]; [%q {|x(n:A) - x0|} ]] ---->
  vCONJ_TAC ++-->
   [vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vNET_NULL_MUL) ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vNET_CONV_BOUNDED ---->
    vEXISTS_TAC [%q {|x0:real|} ] ----> vONCE_REWRITE_TAC[vNET_NULL] ---->
    vASM_REWRITE_TAC[];
    vMATCH_MP_TAC vNET_NULL_CMUL ----> vASM_REWRITE_TAC[]]);;

let%a vNET_INV = prove(
  [%q {|!g:A->A->bool x x0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\ ~(x0 = &0)
            ==> ((\n. inv(x(n))) --> inv x0)(mtop(mr1),g)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREPEAT vGEN_TAC ---->
  vDISCH_THEN(fun th -> vSTRIP_ASSUME_TAC th ---->
    vMP_TAC(vCONJ (vMATCH_MP vNET_CONV_IBOUNDED th)
                    (vMATCH_MP vNET_CONV_NZ th))) ---->
  vREWRITE_TAC[vMR1_BOUNDED] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vLEFT_AND_EXISTS_CONV) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:real|} ] vMP_TAC) ---->
  vDISCH_THEN(vDORDER_THEN vMP_TAC) ----> vBETA_TAC ---->
  vDISCH_THEN(vMP_TAC -| vC vCONJ
   (vASSUME [%q {|(x --> x0)(mtop mr1,(g:A->A->bool))|} ])) ---->
  vONCE_REWRITE_TAC[vNET_NULL] ---->
  vREWRITE_TAC[vMTOP_TENDS; vMR1_DEF; vREAL_SUB_LZERO; vABS_NEG] ----> vBETA_TAC
  ----> vDISCH_THEN((---->)
   (vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC) -| vMP_TAC) ---->
  vONCE_REWRITE_TAC[vRIGHT_AND_FORALL_THM] ---->
  vDISCH_THEN(vASSUME_TAC -| vSPEC [%q {|e * abs(x0) * (inv k)|} ]) ---->
  vSUBGOAL_THEN [%q {|&0 < k|} ] vASSUME_TAC ++-->
   [vFIRST_ASSUM(vMP_TAC -| vCONJUNCT1) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|N:A|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vASSUME_TAC -| vCONJUNCT1) ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|abs(inv(x(N:A)))|} ] ---->
    vASM_REWRITE_TAC[vABS_POS]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|&0 < e * abs(x0) * inv k|} ] vASSUME_TAC ++-->
   [vREPEAT(vMATCH_MP_TAC vREAL_LT_MUL ----> vCONJ_TAC) ---->
    vASM_REWRITE_TAC[vGSYM vABS_NZ] ---->
    vMATCH_MP_TAC vREAL_INV_POS ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_conj -| concl) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN(vDORDER_THEN vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] (vCONJUNCTS_THEN vASSUME_TAC)) ---->
  vEXISTS_TAC [%q {|N:A|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|n:A|} ] ----> vDISCH_THEN(vANTE_RES_THEN vSTRIP_ASSUME_TAC) ---->
  vRULE_ASSUM_TAC vBETA_RULE ----> vPOP_ASSUM_LIST(vMAP_EVERY vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|inv(x n) - inv x0 =
                inv(x n) * inv x0 * (x0 - x(n:A))|} ] vSUBST1_TAC ++-->
   [vREWRITE_TAC[vREAL_SUB_LDISTRIB] ---->
    vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV (vASSUME [%q {|~(x0 = &0)|} ])] ---->
    vREWRITE_TAC[vREAL_MUL_RID] ----> vREPEAT vAP_TERM_TAC ---->
    vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ---->
    vREWRITE_TAC[vMATCH_MP vREAL_MUL_RINV (vASSUME [%q {|~(x(n:A) = &0)|} ])] ---->
    vREWRITE_TAC[vREAL_MUL_RID]; vALL_TAC] ---->
  vREWRITE_TAC[vABS_MUL] ----> vONCE_REWRITE_TAC[vABS_SUB] ---->
  vSUBGOAL_THEN [%q {|e = e * (abs(inv x0) * abs(x0)) * (inv k * k)|} ]
  vSUBST1_TAC ++-->
   [vREWRITE_TAC[vGSYM vABS_MUL] ---->
    vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV (vASSUME [%q {|~(x0 = &0)|} ])] ---->
    vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV
      (vGSYM(vMATCH_MP vREAL_LT_IMP_NE (vASSUME [%q {|&0 < k|} ])))] ---->
    vREWRITE_TAC[vREAL_MUL_RID] ---->
    vREWRITE_TAC[real_abs; vREAL_LE; vLE_LT; num_CONV [%q {|1|} ]; vLESS_SUC_REFL] ---->
    vREWRITE_TAC[vSYM(num_CONV [%q {|1|} ]); vREAL_MUL_RID]; vALL_TAC] ---->
  vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
    [%q {|a * (b * c) * (d * e) = e * b * (a * c * d)|} ]] ---->
  vREWRITE_TAC[vGSYM vABS_MUL] ---->
  vMATCH_MP_TAC vABS_LT_MUL2 ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vABS_MUL] ----> vSUBGOAL_THEN [%q {|&0 < abs(inv x0)|} ]
    (fun th -> vASM_REWRITE_TAC[vMATCH_MP vREAL_LT_LMUL_EQ th]) ---->
  vREWRITE_TAC[vGSYM vABS_NZ] ---->
  vMATCH_MP_TAC vREAL_INV_NZ ----> vASM_REWRITE_TAC[]);;

let%a vNET_DIV = prove(
  [%q {|!g:A->A->bool x x0 y y0.
       dorder g
       ==> (x --> x0)(mtop(mr1),g) /\
           (y --> y0)(mtop(mr1),g) /\ ~(y0 = &0)
           ==> ((\n. x(n) / y(n)) --> (x0 / y0))(mtop(mr1),g)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[real_div] ---->
  vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|n:A|} ] [%q {|inv(y(n:A))|} ]]) ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vNET_MUL) ---->
  vASM_REWRITE_TAC[] ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vNET_INV) ---->
  vASM_REWRITE_TAC[]);;

let%a vNET_ABS = prove(
  [%q {|!x x0. (x --> x0)(mtop(mr1),g) ==>
               ((\n:A. abs(x n)) --> abs(x0))(mtop(mr1),g)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vMTOP_TENDS] ---->
  vDISCH_TAC ----> vX_GEN_TAC [%q {|e:real|} ] ---->
  vDISCH_THEN(fun th -> vPOP_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|N:A|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|n:A|} ] ----> vDISCH_TAC ----> vBETA_TAC ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|mdist(mr1)(x(n:A),x0)|} ] ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vMR1_DEF; vABS_SUB_ABS];
    vFIRST_ASSUM vMATCH_MP_TAC ----> vFIRST_ASSUM vACCEPT_TAC]);;

let%a vNET_SUM = prove
 ([%q {|!g. dorder g /\
       ((\x. &0) --> &0)(mtop(mr1),g)
       ==> !m n. (!r. m <= r /\ r < m + n ==> (f r --> l r)(mtop(mr1),g))
                 ==> ((\x. sum(m,n) (\r. f r x)) --> sum(m,n) l)
                     (mtop(mr1),g)|} ],
  vGEN_TAC ----> vSTRIP_TAC ---->
  vONCE_REWRITE_TAC[vSWAP_FORALL_THM] ----> vINDUCT_TAC ---->
  vASM_SIMP_TAC[sum] ----> vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP vNET_ADD) ----> vCONJ_TAC ++-->
   [vFIRST_ASSUM vMATCH_MP_TAC ---->
    vX_GEN_TAC [%q {|r:num|} ] ----> vREPEAT vSTRIP_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_SIMP_TAC[vARITH_RULE [%q {|a < b + c ==> a < b + SUC c|} ]];
    vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vARITH_TAC]);;

(*----------------------------------------------------------------------------*)
(* Comparison between limits                                                  *)
(*----------------------------------------------------------------------------*)

let%a vNET_LE = prove(
  [%q {|!g:A->A->bool x x0 y y0.
        dorder g
        ==> (x --> x0)(mtop(mr1),g) /\
            (y --> y0)(mtop(mr1),g) /\
            (?N. g N N /\ !n. g n N ==> x(n) <= y(n))
            ==> x0 <= y0|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
  vPURE_ONCE_REWRITE_TAC[vREAL_NOT_LE] ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_conj -| concl) ---->
  vREWRITE_TAC[vCONJ_ASSOC] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vREWRITE_TAC[vMTOP_TENDS] ---->
  vDISCH_THEN(vMP_TAC -| end_itlist vCONJ -|
    map (vSPEC [%q {|(x0 - y0) / &2|} ]) -| vCONJUNCTS) ---->
  vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
  vDISCH_THEN(vDORDER_THEN vMP_TAC) ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_exists -| concl) ---->
  vDISCH_THEN(fun th1 -> vDISCH_THEN (fun th2 -> vMP_TAC(vCONJ th1 th2))) ---->
  vDISCH_THEN(vDORDER_THEN vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:A|} ] (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vBETA_TAC ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|N:A|} ]) ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vMR1_DEF] ----> vONCE_REWRITE_TAC[vABS_SUB] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vREWRITE_TAC[vREAL_NOT_LE] ----> vMATCH_MP_TAC vABS_BETWEEN2 ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|y0:real|} ]; [%q {|x0:real|} ]] ---->
  vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ---->
  vFIRST_ASSUM vACCEPT_TAC);;

(*============================================================================*)
(* Theory of sequences and series of real numbers                             *)
(*============================================================================*)

parse_as_infix ("tends_num_real",(12,"right"));;

parse_as_infix ("sums",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Specialize net theorems to sequences:num->real                             *)
(*----------------------------------------------------------------------------*)

let tends_num_real = new_definition(
  [%q {|x tends_num_real x0 <=> (x tends x0)(mtop(mr1), (>=) :num->num->bool)|} ]);;

override_interface ("-->",[%q {|(tends_num_real)|} ]);;

let%a vSEQ = prove(
  [%q {|!x x0. (x --> x0) <=>
          !e. &0 < e ==> ?N. !n. n >= N ==> abs(x(n) - x0) < e|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real; vSEQ_TENDS; vMR1_DEF] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vABS_SUB] ---->
  vREFL_TAC);;

let%a vSEQ_CONST = prove(
  [%q {|!k. (\x. k) --> k|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vSEQ; vREAL_SUB_REFL; vABS_0] ---->
  vGEN_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[]);;

let%a vSEQ_ADD = prove(
  [%q {|!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) + y(n)) --> (x0 + y0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_MP_TAC vNET_ADD ---->
  vMATCH_ACCEPT_TAC vDORDER_NGE);;

let%a vSEQ_MUL = prove(
  [%q {|!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) * y(n)) --> (x0 * y0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_MP_TAC vNET_MUL ---->
  vMATCH_ACCEPT_TAC vDORDER_NGE);;

let%a vSEQ_NEG = prove(
  [%q {|!x x0. x --> x0 <=> (\n. --(x n)) --> --x0|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_MP_TAC vNET_NEG ---->
  vMATCH_ACCEPT_TAC vDORDER_NGE);;

let%a vSEQ_INV = prove(
  [%q {|!x x0. x --> x0 /\ ~(x0 = &0) ==> (\n. inv(x n)) --> inv x0|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_MP_TAC vNET_INV ---->
  vMATCH_ACCEPT_TAC vDORDER_NGE);;

let%a vSEQ_SUB = prove(
  [%q {|!x x0 y y0. x --> x0 /\ y --> y0 ==> (\n. x(n) - y(n)) --> (x0 - y0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_MP_TAC vNET_SUB ---->
  vMATCH_ACCEPT_TAC vDORDER_NGE);;

let%a vSEQ_DIV = prove(
  [%q {|!x x0 y y0. x --> x0 /\ y --> y0 /\ ~(y0 = &0) ==>
                  (\n. x(n) / y(n)) --> (x0 / y0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_MP_TAC vNET_DIV ---->
  vMATCH_ACCEPT_TAC vDORDER_NGE);;

let%a vSEQ_UNIQ = prove(
  [%q {|!x x1 x2. x --> x1 /\ x --> x2 ==> (x1 = x2)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_MP_TAC vMTOP_TENDS_UNIQ ---->
  vMATCH_ACCEPT_TAC vDORDER_NGE);;

let%a vSEQ_NULL = prove(
  [%q {|!s l. s --> l <=> (\n. s(n) - l) --> &0|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_ACCEPT_TAC vNET_NULL);;

let%a vSEQ_SUM = prove
 ([%q {|!f l m n.
      (!r. m <= r /\ r < m + n ==> f r --> l r)
      ==> (\k. sum(m,n) (\r. f r k)) --> sum(m,n) l|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_MP_TAC(vREWRITE_RULE[vRIGHT_IMP_FORALL_THM] vNET_SUM) ---->
  vREWRITE_TAC[vSEQ_CONST; vDORDER_NGE; vGSYM tends_num_real]);;

let%a vSEQ_TRANSFORM = prove
 ([%q {|!s t l N. (!n. N <= n ==> (s n = t n)) /\ s --> l ==> t --> l|} ],
  vREWRITE_TAC[vSEQ; vGE] ---->
  vMESON_TAC[vARITH_RULE [%q {|M + N <= n:num ==> M <= n /\ N <= n|} ]]);;

(*----------------------------------------------------------------------------*)
(* Define convergence and Cauchy-ness                                         *)
(*----------------------------------------------------------------------------*)

let convergent = new_definition(
  [%q {|convergent f <=> ?l. f --> l|} ]);;

let cauchy = new_definition(
  [%q {|cauchy f <=> !e. &0 < e ==>
        ?N:num. !m n. m >= N /\ n >= N ==> abs(f(m) - f(n)) < e|} ]);;

let lim = new_definition(
  [%q {|lim f = @l. f --> l|} ]);;

let%a vSEQ_LIM = prove(
  [%q {|!f. convergent f <=> (f --> lim f)|} ],
  vGEN_TAC ----> vREWRITE_TAC[convergent] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vSELECT_RULE) ----> vREWRITE_TAC[lim];
    vDISCH_TAC ----> vEXISTS_TAC [%q {|lim f|} ] ----> vPOP_ASSUM vACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Define a subsequence                                                       *)
(*----------------------------------------------------------------------------*)

let subseq = new_definition(
  [%q {|subseq (f:num->num) <=> !m n. m < n ==> (f m) < (f n)|} ]);;

let%a vSUBSEQ_SUC = prove(
  [%q {|!f. subseq f <=> !n. f(n) < f(SUC n)|} ],
  vGEN_TAC ----> vREWRITE_TAC[subseq] ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vX_GEN_TAC [%q {|n:num|} ] ----> vPOP_ASSUM vMATCH_MP_TAC ---->
    vREWRITE_TAC[vLESS_SUC_REFL];
    vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vLESS_ADD_1) ---->
    vREWRITE_TAC[vGSYM vADD1] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|p:num|} ] vSUBST1_TAC) ---->
    vSPEC_TAC([%q {|p:num|} ],[%q {|p:num|} ]) ----> vINDUCT_TAC ++-->
     [vALL_TAC;
      vMATCH_MP_TAC vLT_TRANS ----> vEXISTS_TAC [%q {|f(m + (SUC p)):num|} ]] ---->
    vASM_REWRITE_TAC[vADD_CLAUSES]]);;

(*----------------------------------------------------------------------------*)
(* Define monotonicity                                                        *)
(*----------------------------------------------------------------------------*)

let mono = new_definition(
  [%q {|mono (f:num->real) <=>
            (!m n. m <= n ==> f(m) <= f(n)) \/
            (!m n. m <= n ==> f(m) >= f(n))|} ]);;

let%a vMONO_SUC = prove(
  [%q {|!f. mono f <=> (!n. f(SUC n) >= f(n)) \/ (!n. f(SUC n) <= f(n))|} ],
  vGEN_TAC ----> vREWRITE_TAC[mono; real_ge] ---->
  vMATCH_MP_TAC(vTAUT [%q {|(a <=> c) /\ (b <=> d) ==> (a \/ b <=> c \/ d)|} ]) ---->
  vCONJ_TAC ----> (vEQ_TAC ++-->
    [vDISCH_THEN(vMP_TAC -| vGEN [%q {|n:num|} ] -| vSPECL [[%q {|n:num|} ]; [%q {|SUC n|} ]]) ---->
     vREWRITE_TAC[vLESS_EQ_SUC_REFL];
     vDISCH_TAC ----> vREPEAT vGEN_TAC ---->
     vDISCH_THEN(vX_CHOOSE_THEN [%q {|p:num|} ] vSUBST1_TAC -| vMATCH_MP vLESS_EQUAL_ADD) ---->
     vSPEC_TAC([%q {|p:num|} ],[%q {|p:num|} ]) ----> vINDUCT_TAC ---->
     vASM_REWRITE_TAC[vADD_CLAUSES; vREAL_LE_REFL] ---->
     vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|f(m + p:num):real|} ] ---->
     vASM_REWRITE_TAC[]]));;

(*----------------------------------------------------------------------------*)
(* Simpler characterization of bounded sequence                               *)
(*----------------------------------------------------------------------------*)

let%a vMAX_LEMMA = prove(
  [%q {|!s N. ?k. !n:num. n < N ==> abs(s n) < k|} ],
  vGEN_TAC ----> vINDUCT_TAC ----> vREWRITE_TAC[vNOT_LESS_0] ---->
  vPOP_ASSUM(vX_CHOOSE_TAC [%q {|k:real|} ]) ---->
  vDISJ_CASES_TAC (vSPECL [[%q {|k:real|} ]; [%q {|abs(s(N:num))|} ]] vREAL_LET_TOTAL) ++-->
   [vEXISTS_TAC [%q {|abs(s(N:num)) + &1|} ]; vEXISTS_TAC [%q {|k:real|} ]] ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vCONJUNCT2 vLT] ---->
  vDISCH_THEN(vDISJ_CASES_THEN2 vSUBST1_TAC vMP_TAC) ---->
  vTRY(vMATCH_MP_TAC vREAL_LT_ADD1) ----> vASM_REWRITE_TAC[vREAL_LE_REFL] ---->
  vDISCH_THEN(vANTE_RES_THEN vASSUME_TAC) ---->
  vMATCH_MP_TAC vREAL_LT_ADD1 ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|k:real|} ] ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
  vASM_REWRITE_TAC[]);;

let%a vSEQ_BOUNDED = prove(
  [%q {|!s. bounded(mr1, (>=)) s <=> ?k. !n:num. abs(s n) < k|} ],
  vGEN_TAC ----> vREWRITE_TAC[vMR1_BOUNDED] ---->
  vREWRITE_TAC[vGE; vLE_REFL] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:real|} ] (vX_CHOOSE_TAC [%q {|N:num|} ])) ---->
    vMP_TAC(vSPECL [[%q {|s:num->real|} ]; [%q {|N:num|} ]] vMAX_LEMMA) ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|l:real|} ]) ---->
    vDISJ_CASES_TAC (vSPECL [[%q {|k:real|} ]; [%q {|l:real|} ]] vREAL_LE_TOTAL) ++-->
     [vEXISTS_TAC [%q {|l:real|} ]; vEXISTS_TAC [%q {|k:real|} ]] ---->
    vX_GEN_TAC [%q {|n:num|} ] ----> vMP_TAC(vSPECL [[%q {|n:num|} ]; [%q {|N:num|} ]] vLTE_CASES) ---->
    vDISCH_THEN(vDISJ_CASES_THEN(vANTE_RES_THEN vASSUME_TAC)) ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LTE_TRANS ---->
    vFIRST_ASSUM(fun th -> vEXISTS_TAC(rand(concl th)) ---->
      vASM_REWRITE_TAC[] ----> vNO_TAC);
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|k:real|} ]) ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|k:real|} ]; [%q {|0|} ]] ---->
    vGEN_TAC ----> vASM_REWRITE_TAC[]]);;

let%a vSEQ_BOUNDED_2 = prove(
  [%q {|!f k K. (!n:num. k <= f(n) /\ f(n) <= K) ==> bounded(mr1, (>=)) f|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vSEQ_BOUNDED] ---->
  vEXISTS_TAC [%q {|(abs(k) + abs(K)) + &1|} ] ----> vGEN_TAC ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|abs(k) + abs(K)|} ] ---->
  vREWRITE_TAC[vREAL_LT_ADDR; vREAL_LT_01] ---->
  vGEN_REWRITE_TAC vLAND_CONV [real_abs] ----> vCOND_CASES_TAC ++-->
   [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|abs(K)|} ] ---->
    vREWRITE_TAC[vREAL_LE_ADDL; vABS_POS] ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|K:real|} ] ---->
    vASM_REWRITE_TAC[vABS_LE];
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|abs(k)|} ] ---->
    vREWRITE_TAC[vREAL_LE_ADDR; vABS_POS] ---->
    vREWRITE_TAC[real_abs] ---->
    vCOND_CASES_TAC ----> vASM_REWRITE_TAC[vREAL_LE_NEG2] ---->
    vSUBGOAL_THEN [%q {|&0 <= f(n:num)|} ] vMP_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ---->
      vEXISTS_TAC [%q {|k:real|} ] ----> vASM_REWRITE_TAC[];
      vASM_REWRITE_TAC[]]]);;

(*----------------------------------------------------------------------------*)
(* Show that every Cauchy sequence is bounded                                 *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_CBOUNDED = prove(
  [%q {|!f. cauchy f ==> bounded(mr1, (>=)) f|} ],
  vGEN_TAC ----> vREWRITE_TAC[bounded; cauchy] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|&1|} ]) ----> vREWRITE_TAC[vREAL_LT_01] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|N:num|} ]) ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|&1|} ]; [%q {|(f:num->real) N|} ]; [%q {|N:num|} ]] ---->
  vREWRITE_TAC[vGE; vLE_REFL] ---->
  vPOP_ASSUM(vMP_TAC -| vSPEC [%q {|N:num|} ]) ---->
  vREWRITE_TAC[vGE; vLE_REFL; vMR1_DEF]);;

(*----------------------------------------------------------------------------*)
(* Show that a bounded and monotonic sequence converges                       *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_ICONV = prove(
  [%q {|!f. bounded(mr1, (>=)) f /\ (!m n. m >= n ==> f(m) >= f(n))
           ==> convergent f|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC (vSPEC [%q {|\x:real. ?n:num. x = f(n)|} ] vREAL_SUP) ----> vBETA_TAC ---->
  vW(vC vSUBGOAL_THEN vMP_TAC -| funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vCONJ_TAC ++-->
     [vMAP_EVERY vEXISTS_TAC [[%q {|f(0):real|} ]; [%q {|0|} ]] ----> vREFL_TAC;
      vPOP_ASSUM(vMP_TAC -| vREWRITE_RULE[vSEQ_BOUNDED] -| vCONJUNCT1) ---->
      vDISCH_THEN(vX_CHOOSE_TAC [%q {|k:real|} ]) ----> vEXISTS_TAC [%q {|k:real|} ] ---->
      vGEN_TAC ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:num|} ] vSUBST1_TAC) ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|abs(f(n:num))|} ] ---->
      vASM_REWRITE_TAC[vABS_LE]]; vALL_TAC] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ----> vDISCH_TAC ---->
  vREWRITE_TAC[convergent] ----> vEXISTS_TAC [%q {|sup(\x. ?n:num. x = f(n))|} ] ---->
  vREWRITE_TAC[vSEQ] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| check(is_forall -| concl)) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|sup(\x. ?n:num. x = f(n)) - e|} ]) ---->
  vREWRITE_TAC[vREAL_LT_SUB_RADD; vREAL_LT_ADDR] ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vMP_TAC) ---->
  vONCE_REWRITE_TAC[vCONJ_SYM] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC (vX_CHOOSE_THEN [%q {|n:num|} ] vSUBST1_TAC)) ---->
  vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vREWRITE_TAC[vGSYM vREAL_LT_SUB_RADD] ---->
  vDISCH_TAC ----> vSUBGOAL_THEN [%q {|!n. f(n) <= sup(\x. ?n:num. x = f(n))|} ]
  vASSUME_TAC ++-->
   [vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|sup(\x. ?n:num. x = f(n))|} ]) ---->
    vREWRITE_TAC[vREAL_LT_REFL] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vNOT_EXISTS_CONV) ---->
    vREWRITE_TAC[vTAUT [%q {|~(a /\ b) <=> a ==> ~b|} ]] ---->
    vREWRITE_TAC[vREAL_NOT_LT] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vLEFT_IMP_EXISTS_CONV) ---->
    vDISCH_THEN(vMP_TAC -| vGEN [%q {|n:num|} ] -| vSPECL [[%q {|(f:num->real) n|} ]; [%q {|n:num|} ]]) ---->
    vREWRITE_TAC[]; vALL_TAC] ---->
  vEXISTS_TAC [%q {|n:num|} ] ----> vX_GEN_TAC [%q {|m:num|} ] ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_conj -| concl) ---->
  vDISCH_THEN(vASSUME_TAC -| vCONJUNCT2) ---->
  vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vREAL_LT_SUB_RADD]) ---->
  vRULE_ASSUM_TAC(vONCE_REWRITE_RULE[vREAL_ADD_SYM]) ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vGSYM vREAL_LT_SUB_RADD]) ---->
  vREWRITE_TAC[real_ge] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|(sup(\x. ?m:num. x = f(m)) - e) < f(m)|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|(f:num->real) n|} ] ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[real_abs] ----> vCOND_CASES_TAC ---->
  vASM_REWRITE_TAC[vREAL_NEG_SUB] ++-->
   [vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|&0|} ] ---->
    vASM_REWRITE_TAC[] ----> vREWRITE_TAC[real_sub] ---->
    (vSUBST1_TAC -| vREWRITE_RULE[vREAL_ADD_RINV] -| vC vSPECL vREAL_LE_RADD)
      [[%q {|(f:num->real) m|} ]; [%q {|(sup(\x. ?n:num. x = f(n)))|} ];
       [%q {|--(sup(\x. ?n:num. x = f(n)))|} ]] ---->
    vASM_REWRITE_TAC[];
    vREWRITE_TAC[vREAL_LT_SUB_RADD] ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
    vREWRITE_TAC[vGSYM vREAL_LT_SUB_RADD] ----> vASM_REWRITE_TAC[]]);;

let%a vSEQ_NEG_CONV = prove(
  [%q {|!f. convergent f <=> convergent (\n. --(f n))|} ],
  vGEN_TAC ----> vREWRITE_TAC[convergent] ----> vEQ_TAC ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|l:real|} ]) ---->
  vEXISTS_TAC [%q {|--l|} ] ----> vPOP_ASSUM vMP_TAC ---->
  vSUBST1_TAC(vSYM(vSPEC [%q {|l:real|} ] vREAL_NEG_NEG)) ---->
  vREWRITE_TAC[vGSYM vSEQ_NEG] ----> vREWRITE_TAC[vREAL_NEG_NEG]);;

let%a vSEQ_NEG_BOUNDED = prove(
  [%q {|!f. bounded(mr1, (>=))(\n:num. --(f n)) <=> bounded(mr1, (>=)) f|} ],
  vGEN_TAC ----> vREWRITE_TAC[vSEQ_BOUNDED] ----> vBETA_TAC ---->
  vREWRITE_TAC[vABS_NEG]);;

let%a vSEQ_BCONV = prove(
  [%q {|!f. bounded(mr1, (>=)) f /\ mono f ==> convergent f|} ],
  vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vREWRITE_TAC[mono] ----> vDISCH_THEN vDISJ_CASES_TAC ++-->
   [vMATCH_MP_TAC vSEQ_ICONV ----> vASM_REWRITE_TAC[vGE; real_ge];
    vONCE_REWRITE_TAC[vSEQ_NEG_CONV] ----> vMATCH_MP_TAC vSEQ_ICONV ---->
    vASM_REWRITE_TAC[vSEQ_NEG_BOUNDED] ----> vBETA_TAC ---->
    vREWRITE_TAC[vGE; real_ge; vREAL_LE_NEG2] ---->
    vONCE_REWRITE_TAC[vGSYM real_ge] ----> vASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Show that every sequence contains a monotonic subsequence                  *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_MONOSUB = prove(
  [%q {|!s:num->real. ?f. subseq f /\ mono(\n.s(f n))|} ],
  vGEN_TAC ---->
  vASM_CASES_TAC [%q {|!n:num. ?p. p > n /\ !m. m >= p ==> s(m) <= s(p)|} ] ++-->
   [(vX_CHOOSE_THEN [%q {|f:num->num|} ] vMP_TAC -| vEXISTENCE -| vC vISPECL num_Axiom)
     [[%q {|@p. p > 0 /\ (!m. m >= p ==> (s m) <= (s p))|} ];
      [%q {|\x. \n:num. @p:num. p > x /\
                       (!m. m >= p ==> (s m) <= (s p))|} ]] ---->
    vBETA_TAC ----> vRULE_ASSUM_TAC(vGEN [%q {|n:num|} ] -| vSELECT_RULE -| vSPEC [%q {|n:num|} ]) ---->
    vPOP_ASSUM(fun th -> vDISCH_THEN(vASSUME_TAC -| vGSYM) ---->
    vMP_TAC(vSPEC [%q {|0|} ] th) ---->
    vMP_TAC(vGEN [%q {|n:num|} ] (vSPEC [%q {|(f:num->num) n|} ] th))) ---->
    vASM_REWRITE_TAC[] ----> vPOP_ASSUM(vK vALL_TAC) ----> vREPEAT vSTRIP_TAC ---->
    vEXISTS_TAC [%q {|f:num->num|} ] ----> vASM_REWRITE_TAC[vSUBSEQ_SUC; vGSYM vGT] ---->
    vSUBGOAL_THEN [%q {|!p q. p:num >= (f q) ==> s(p) <= s(f(q:num))|} ] vMP_TAC ++-->
     [vREPEAT vGEN_TAC ----> vSTRUCT_CASES_TAC(vSPEC [%q {|q:num|} ] num_CASES) ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vDISCH_THEN(vMP_TAC -| vGEN [%q {|q:num|} ] -| vSPECL [[%q {|f(SUC q):num|} ]; [%q {|q:num|} ]]) ---->
    vSUBGOAL_THEN [%q {|!q. f(SUC q):num >= f(q)|} ] (fun th -> vREWRITE_TAC[th]) ++-->
     [vGEN_TAC ----> vREWRITE_TAC[vGE] ---->
      vMATCH_MP_TAC vLT_IMP_LE
      ----> vASM_REWRITE_TAC[vGSYM vGT]; vALL_TAC] ---->
    vDISCH_TAC ----> vREWRITE_TAC[vMONO_SUC] ----> vDISJ2_TAC ---->
    vBETA_TAC ----> vASM_REWRITE_TAC[];
    vPOP_ASSUM(vX_CHOOSE_TAC [%q {|N:num|} ] -| vCONV_RULE vNOT_FORALL_CONV) ---->
    vPOP_ASSUM(vMP_TAC -| vCONV_RULE vNOT_EXISTS_CONV) ---->
    vREWRITE_TAC[vTAUT [%q {|~(a /\ b) <=> a ==> ~b|} ]] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vNOT_FORALL_CONV) ---->
    vREWRITE_TAC[vNOT_IMP; vREAL_NOT_LE] ----> vDISCH_TAC ---->
    vSUBGOAL_THEN [%q {|!p. p >= SUC N ==> (?m. m > p /\ s(p) < s(m))|} ]
    vMP_TAC ++-->
     [vGEN_TAC ----> vREWRITE_TAC[vGE; vLE_SUC_LT] ---->
      vREWRITE_TAC[vGSYM vGT] ----> vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
      vREWRITE_TAC[vGE; vLE_LT; vRIGHT_AND_OVER_OR; vGT] ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:num|} ] vDISJ_CASES_TAC) ++-->
       [vEXISTS_TAC [%q {|m:num|} ] ----> vASM_REWRITE_TAC[];
        vFIRST_ASSUM(vUNDISCH_TAC -| check is_conj -| concl) ---->
        vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
        vASM_REWRITE_TAC[vREAL_LT_REFL]]; vALL_TAC] ---->
    vPOP_ASSUM(vK vALL_TAC) ----> vDISCH_TAC ---->
    (vX_CHOOSE_THEN [%q {|f:num->num|} ] vMP_TAC -| vEXISTENCE -| vC vISPECL num_Axiom)
     [[%q {|@m. m > (SUC N) /\ s(SUC N) < s(m)|} ];
      [%q {|\x. \n:num. @m:num. m > x /\ s(x) < s(m)|} ]] ---->
    vBETA_TAC ----> vDISCH_THEN vASSUME_TAC ----> vSUBGOAL_THEN
      [%q {|!n. f(n) >= (SUC N) /\
           f(SUC n) > f(n) /\ s(f n) < s(f(SUC n):num)|} ] vMP_TAC ++-->
     [vINDUCT_TAC ++-->
       [vSUBGOAL_THEN [%q {|f(0) >= (SUC N)|} ] vMP_TAC ++-->
         [vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|SUC N|} ]) ---->
          vREWRITE_TAC[vGE; vLE_REFL] ---->
          vDISCH_THEN(vMP_TAC -| vSELECT_RULE) ----> vASM_REWRITE_TAC[] ---->
          vDISCH_THEN(vASSUME_TAC -| vCONJUNCT1) ---->
          vMATCH_MP_TAC vLT_IMP_LE ---->
          vASM_REWRITE_TAC[vGSYM vGT]; vALL_TAC] ---->
        vDISCH_THEN(fun th -> vASSUME_TAC th ----> vREWRITE_TAC[th]) ---->
        vFIRST_ASSUM(fun th -> vREWRITE_TAC[vCONJUNCT2 th]) ---->
        vCONV_TAC vSELECT_CONV ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
        vFIRST_ASSUM vACCEPT_TAC;
        vFIRST_ASSUM(vUNDISCH_TAC -|
          check((=)3 -| length -| conjuncts) -| concl) ---->
        vDISCH_THEN vSTRIP_ASSUME_TAC ----> vCONJ_TAC ++-->
         [vREWRITE_TAC[vGE] ----> vMATCH_MP_TAC vLE_TRANS ---->
          vEXISTS_TAC [%q {|(f:num->num) n|} ] ----> vREWRITE_TAC[vGSYM vGE] ---->
          vCONJ_TAC ----> vTRY(vFIRST_ASSUM vACCEPT_TAC) ---->
          vREWRITE_TAC[vGE] ----> vMATCH_MP_TAC vLT_IMP_LE ---->
          vREWRITE_TAC[vGSYM vGT] ----> vFIRST_ASSUM vACCEPT_TAC;
          vFIRST_ASSUM(vSUBST1_TAC -| vSPEC [%q {|SUC n|} ] -| vCONJUNCT2) ---->
          vCONV_TAC vSELECT_CONV ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
          vREWRITE_TAC[vGE] ----> vMATCH_MP_TAC vLE_TRANS ---->
          vEXISTS_TAC [%q {|(f:num->num) n|} ] ---->
          vREWRITE_TAC[vGSYM vGE] ----> vCONJ_TAC ---->
          vTRY(vFIRST_ASSUM vACCEPT_TAC) ---->
          vREWRITE_TAC[vGE] ----> vMATCH_MP_TAC vLT_IMP_LE ---->
          vREWRITE_TAC[vGSYM vGT] ---->
          vFIRST_ASSUM vACCEPT_TAC]]; vALL_TAC] ---->
    vPOP_ASSUM_LIST(vK vALL_TAC) ----> vDISCH_TAC ---->
    vEXISTS_TAC [%q {|f:num->num|} ] ----> vREWRITE_TAC[vSUBSEQ_SUC; vMONO_SUC] ---->
    vASM_REWRITE_TAC[vGSYM vGT] ----> vDISJ1_TAC ----> vBETA_TAC ---->
    vGEN_TAC ----> vREWRITE_TAC[real_ge] ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Show that a subsequence of a bounded sequence is bounded                   *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_SBOUNDED = prove(
  [%q {|!s (f:num->num). bounded(mr1, (>=)) s ==> bounded(mr1, (>=)) (\n. s(f n))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vSEQ_BOUNDED] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|k:real|} ]) ----> vEXISTS_TAC [%q {|k:real|} ] ---->
  vGEN_TAC ----> vBETA_TAC ----> vASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Show we can take subsequential terms arbitrarily far up a sequence         *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_SUBLE = prove(
  [%q {|!f n. subseq f ==> n <= f(n)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vDISCH_TAC ----> vINDUCT_TAC ++-->
   [vREWRITE_TAC[vGSYM vNOT_LT; vNOT_LESS_0];
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC [%q {|SUC(f(n:num))|} ] ---->
    vASM_REWRITE_TAC[vLE_SUC] ---->
    vREWRITE_TAC[vLE_SUC_LT] ---->
    vUNDISCH_TAC [%q {|subseq f|} ] ----> vREWRITE_TAC[vSUBSEQ_SUC] ---->
    vDISCH_THEN vMATCH_ACCEPT_TAC]);;

let%a vSEQ_DIRECT = prove(
  [%q {|!f. subseq f ==> !N1 N2. ?n. n >= N1 /\ f(n) >= N2|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREPEAT vGEN_TAC ---->
  vDISJ_CASES_TAC (vSPECL [[%q {|N1:num|} ]; [%q {|N2:num|} ]] vLE_CASES) ++-->
   [vEXISTS_TAC [%q {|N2:num|} ] ----> vASM_REWRITE_TAC[vGE] ---->
    vMATCH_MP_TAC vSEQ_SUBLE ---->
    vFIRST_ASSUM vACCEPT_TAC;
    vEXISTS_TAC [%q {|N1:num|} ] ----> vREWRITE_TAC[vGE; vLE_REFL] ---->
    vREWRITE_TAC[vGE] ----> vMATCH_MP_TAC vLE_TRANS ---->
    vEXISTS_TAC [%q {|N1:num|} ] ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vSEQ_SUBLE ---->
    vFIRST_ASSUM vACCEPT_TAC]);;

(*----------------------------------------------------------------------------*)
(* Now show that every Cauchy sequence converges                              *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_CAUCHY = prove(
  [%q {|!f. cauchy f <=> convergent f|} ],
  vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_TAC ----> vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vSEQ_CBOUNDED) ---->
    vMP_TAC(vSPEC [%q {|f:num->real|} ] vSEQ_MONOSUB) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|g:num->num|} ] vSTRIP_ASSUME_TAC) ---->
    vSUBGOAL_THEN [%q {|bounded(mr1, (>=) :num->num->bool)(\n. f(g(n):num))|} ]
    vASSUME_TAC ++-->
     [vMATCH_MP_TAC vSEQ_SBOUNDED ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|convergent (\n. f(g(n):num))|} ] vMP_TAC ++-->
     [vMATCH_MP_TAC vSEQ_BCONV ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vREWRITE_TAC[convergent] ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|l:real|} ]) ---->
    vEXISTS_TAC [%q {|l:real|} ] ----> vREWRITE_TAC[vSEQ] ---->
    vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
    vUNDISCH_TAC [%q {|(\n. f(g(n):num)) --> l|} ] ----> vREWRITE_TAC[vSEQ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ----> vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
    vBETA_TAC ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|N1:num|} ]) ---->
    vUNDISCH_TAC [%q {|cauchy f|} ] ----> vREWRITE_TAC[cauchy] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ----> vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|N2:num|} ] vASSUME_TAC) ---->
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vSEQ_DIRECT) ---->
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|N1:num|} ]; [%q {|N2:num|} ]]) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|n:num|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|N2:num|} ] ----> vX_GEN_TAC [%q {|m:num|} ] ----> vDISCH_TAC ---->
    vUNDISCH_TAC [%q {|!n:num. n >= N1 ==> abs(f(g n:num) - l) < (e / &2)|} ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|n:num|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC ----> vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|g(n:num):num|} ]; [%q {|m:num|} ]]) ---->
    vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vSUBGOAL_THEN [%q {|f(m:num) - l = (f(m) - f(g(n:num))) + (f(g n) - l)|} ]
    vSUBST1_TAC ++--> [vREWRITE_TAC[vREAL_SUB_TRIANGLE]; vALL_TAC] ---->
    vEXISTS_TAC [%q {|abs(f(m:num) - f(g(n:num))) + abs(f(g n) - l)|} ] ---->
    vREWRITE_TAC[vABS_TRIANGLE] ---->
    vSUBST1_TAC(vSYM(vSPEC [%q {|e:real|} ] vREAL_HALF_DOUBLE)) ---->
    vMATCH_MP_TAC vREAL_LT_ADD2 ----> vASM_REWRITE_TAC[] ---->
    vONCE_REWRITE_TAC[vABS_SUB] ----> vASM_REWRITE_TAC[];

    vREWRITE_TAC[convergent] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|l:real|} ] vMP_TAC) ---->
    vREWRITE_TAC[vSEQ; cauchy] ----> vDISCH_TAC ---->
    vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
    vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
    vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|N:num|} ]) ---->
    vEXISTS_TAC [%q {|N:num|} ] ----> vREPEAT vGEN_TAC ---->
    vDISCH_THEN(vCONJUNCTS_THEN (vANTE_RES_THEN vASSUME_TAC)) ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vSUBGOAL_THEN [%q {|f(m:num) - f(n) = (f(m) - l) + (l - f(n))|} ]
    vSUBST1_TAC ++--> [vREWRITE_TAC[vREAL_SUB_TRIANGLE]; vALL_TAC] ---->
    vEXISTS_TAC [%q {|abs(f(m:num) - l) + abs(l - f(n))|} ] ---->
    vREWRITE_TAC[vABS_TRIANGLE] ---->
    vSUBST1_TAC(vSYM(vSPEC [%q {|e:real|} ] vREAL_HALF_DOUBLE)) ---->
    vMATCH_MP_TAC vREAL_LT_ADD2 ----> vASM_REWRITE_TAC[] ---->
    vONCE_REWRITE_TAC[vABS_SUB] ----> vASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* The limit comparison property for sequences                                *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_LE = prove(
  [%q {|!f g l m. f --> l /\ g --> m /\ (?N. !n. n >= N ==> f(n) <= g(n))
        ==> l <= m|} ],
  vREPEAT vGEN_TAC ---->
  vMP_TAC(vISPEC [%q {|(>=) :num->num->bool|} ] vNET_LE) ---->
  vREWRITE_TAC[vDORDER_NGE; tends_num_real; vGE; vLE_REFL] ---->
  vDISCH_THEN vMATCH_ACCEPT_TAC);;

(* ------------------------------------------------------------------------- *)
(* When a sequence tends to zero.                                            *)
(* ------------------------------------------------------------------------- *)

let%a vSEQ_LE_0 = prove
 ([%q {|!f g. f --> &0 /\ (?N. !n. n >= N ==> abs(g n) <= abs(f n))
         ==> g --> &0|} ],
  vREWRITE_TAC[vSEQ; vREAL_SUB_RZERO; vGE] ---->
  vMESON_TAC[vLE_CASES; vLE_TRANS; vREAL_LET_TRANS]);;

(*----------------------------------------------------------------------------*)
(* We can displace a convergent series by 1                                   *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_SUC = prove(
  [%q {|!f l. f --> l <=> (\n. f(SUC n)) --> l|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vSEQ; vGE] ----> vEQ_TAC ---->
  vDISCH_THEN(fun th -> vX_GEN_TAC [%q {|e:real|} ] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP th)) ----> vBETA_TAC ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|N:num|} ]) ++-->
   [vEXISTS_TAC [%q {|N:num|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
    vEXISTS_TAC [%q {|SUC N|} ] ----> vASM_REWRITE_TAC[vLE_SUC; vLESS_EQ_SUC_REFL];
    vEXISTS_TAC [%q {|SUC N|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
    vSTRUCT_CASES_TAC (vSPEC [%q {|n:num|} ] num_CASES) ++-->
     [vREWRITE_TAC[vGSYM vNOT_LT; vLT_0];
      vREWRITE_TAC[vLE_SUC] ----> vDISCH_TAC ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]]);;

(*----------------------------------------------------------------------------*)
(* Prove a sequence tends to zero iff its abs does                            *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_ABS = prove(
  [%q {|!f. (\n. abs(f n)) --> &0 <=> f --> &0|} ],
  vGEN_TAC ----> vREWRITE_TAC[vSEQ] ---->
  vBETA_TAC ----> vREWRITE_TAC[vREAL_SUB_RZERO; vABS_ABS]);;

(*----------------------------------------------------------------------------*)
(* Half this is true for a general limit                                      *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_ABS_IMP = prove(
  [%q {|!f l. f --> l ==> (\n. abs(f n)) --> abs(l)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_num_real] ---->
  vMATCH_ACCEPT_TAC vNET_ABS);;

(*----------------------------------------------------------------------------*)
(* Prove that an unbounded sequence's inverse tends to 0                      *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_INV0 = prove(
  [%q {|!f. (!y. ?N. !n. n >= N ==> f(n) > y)
        ==> (\n. inv(f n)) --> &0|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vSEQ; vREAL_SUB_RZERO] ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vX_CHOOSE_TAC [%q {|N:num|} ] -| vSPEC [%q {|inv e|} ]) ---->
  vEXISTS_TAC [%q {|N:num|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
  vDISCH_THEN(fun th -> vASSUME_TAC th ----> vANTE_RES_THEN vMP_TAC th) ---->
  vREWRITE_TAC[real_gt] ----> vBETA_TAC ---->
  vIMP_RES_THEN vASSUME_TAC vREAL_INV_POS ---->
  vSUBGOAL_THEN [%q {|&0 < f(n:num)|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|inv e|} ] ---->
    vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vGSYM real_gt] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|&0 < inv(f(n:num))|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vREAL_INV_POS ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|~(f(n:num) = &0)|} ] vASSUME_TAC ++-->
   [vCONV_TAC(vRAND_CONV vSYM_CONV) ----> vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vABS_INV th]) ---->
  vSUBGOAL_THEN [%q {|e = inv(inv e)|} ] vSUBST1_TAC ++-->
   [vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_INVINV ---->
    vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
    vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vMATCH_MP_TAC vREAL_LT_INV2 ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|(f:num->real) n|} ] ---->
  vASM_REWRITE_TAC[vABS_LE]);;

(*----------------------------------------------------------------------------*)
(* Important limit of c^n for |c| < 1                                         *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_POWER_ABS = prove(
  [%q {|!c. abs(c) < &1 ==> (\n. abs(c) pow n) --> &0|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vMP_TAC(vSPEC [%q {|c:real|} ] vABS_POS) ---->
  vREWRITE_TAC[vREAL_LE_LT] ----> vDISCH_THEN vDISJ_CASES_TAC ++-->
   [vSUBGOAL_THEN [%q {|!n. abs(c) pow n = inv(inv(abs(c) pow n))|} ]
      (fun th -> vONCE_REWRITE_TAC[th]) ++-->
     [vGEN_TAC ----> vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_INVINV ---->
      vMATCH_MP_TAC vPOW_NZ ---->
      vASM_REWRITE_TAC[vABS_NZ; vABS_ABS]; vALL_TAC] ---->
    vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|n:num|} ] [%q {|inv(abs(c) pow n)|} ]]) ---->
    vMATCH_MP_TAC vSEQ_INV0 ----> vBETA_TAC ----> vX_GEN_TAC [%q {|y:real|} ] ---->
    vSUBGOAL_THEN [%q {|~(abs(c) = &0)|} ]
         (fun th -> vREWRITE_TAC[vMATCH_MP vPOW_INV th]) ++-->
     [vCONV_TAC(vRAND_CONV vSYM_CONV) ----> vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ----> vREWRITE_TAC[real_gt] ---->
    vSUBGOAL_THEN [%q {|&0 < inv(abs c) - &1|} ] vASSUME_TAC ++-->
     [vREWRITE_TAC[vREAL_LT_SUB_LADD] ----> vREWRITE_TAC[vREAL_ADD_LID] ---->
      vONCE_REWRITE_TAC[vGSYM vREAL_INV1] ----> vMATCH_MP_TAC vREAL_LT_INV2 ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vMP_TAC(vSPEC [%q {|inv(abs c) - &1|} ] vREAL_ARCH) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|N:num|} ] -| vSPEC [%q {|y:real|} ]) ---->
    vEXISTS_TAC [%q {|N:num|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vGE] ---->
    vDISCH_TAC ----> vSUBGOAL_THEN [%q {|y < (&n * (inv(abs c) - &1))|} ]
    vASSUME_TAC ++-->
     [vMATCH_MP_TAC vREAL_LTE_TRANS ---->
      vEXISTS_TAC [%q {|&N * (inv(abs c) - &1)|} ] ----> vASM_REWRITE_TAC[] ---->
      vFIRST_ASSUM(fun th ->
        vGEN_REWRITE_TAC vI [vMATCH_MP vREAL_LE_RMUL_EQ th]) ---->
      vASM_REWRITE_TAC[vREAL_LE]; vALL_TAC] ---->
    vMATCH_MP_TAC vREAL_LT_TRANS ---->
    vEXISTS_TAC [%q {|&n * (inv(abs c) - &1)|} ] ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vREAL_LTE_TRANS ---->
    vEXISTS_TAC [%q {|&1 + (&n * (inv(abs c) - &1))|} ] ---->
    vREWRITE_TAC[vREAL_LT_ADDL; vREAL_LT_01] ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ---->
    vEXISTS_TAC [%q {|(&1 + (inv(abs c) - &1)) pow n|} ] ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vPOW_PLUS1 ----> vASM_REWRITE_TAC[];
      vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vREWRITE_TAC[vREAL_SUB_ADD] ---->
      vREWRITE_TAC[vREAL_LE_REFL]];
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM) ----> vREWRITE_TAC[vSEQ] ---->
    vGEN_TAC ----> vDISCH_TAC ----> vEXISTS_TAC [%q {|1|} ] ---->
    vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vGE] ----> vBETA_TAC ---->
    vSTRUCT_CASES_TAC(vSPEC [%q {|n:num|} ] num_CASES) ++-->
     [vREWRITE_TAC[vGSYM vNOT_LT; num_CONV [%q {|1|} ]; vLT_0];
      vREWRITE_TAC[vPOW_0; vREAL_SUB_RZERO; vABS_0] ---->
      vREWRITE_TAC[vASSUME [%q {|&0 < e|} ]]]]);;

(*----------------------------------------------------------------------------*)
(* Similar version without the abs                                            *)
(*----------------------------------------------------------------------------*)

let%a vSEQ_POWER = prove(
  [%q {|!c. abs(c) < &1 ==> (\n. c pow n) --> &0|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vSEQ_ABS] ----> vBETA_TAC ---->
  vREWRITE_TAC[vGSYM vPOW_ABS] ---->
  vPOP_ASSUM(vACCEPT_TAC -| vMATCH_MP vSEQ_POWER_ABS));;

(* ------------------------------------------------------------------------- *)
(* Convergence to 0 of harmonic sequence (not series of course).             *)
(* ------------------------------------------------------------------------- *)

let%a vSEQ_HARMONIC = prove
 ([%q {|!a. (\n. a / &n) --> &0|} ],
  vGEN_TAC ----> vREWRITE_TAC[vSEQ] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|abs a|} ] -| vMATCH_MP vREAL_ARCH) ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|N:num|} ]) ----> vEXISTS_TAC [%q {|N + 1|} ] ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vGE] ----> vDISCH_TAC ---->
  vREWRITE_TAC[vREAL_SUB_RZERO; vREAL_ABS_DIV; vREAL_ABS_NUM] ---->
  vSUBGOAL_THEN [%q {|&0 < &n|} ] (fun th -> vSIMP_TAC[vREAL_LT_LDIV_EQ; th]) ++-->
   [vREWRITE_TAC[vREAL_OF_NUM_LT] ----> vUNDISCH_TAC [%q {|N + 1 <= n|} ] ----> vARITH_TAC;
    vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|&N * e|} ]] ---->
  vASM_REWRITE_TAC[] ----> vGEN_REWRITE_TAC vRAND_CONV [vREAL_MUL_SYM] ---->
  vMATCH_MP_TAC vREAL_LE_RMUL ---->
  vASM_SIMP_TAC[vREAL_LT_IMP_LE; vREAL_OF_NUM_LE] ---->
  vUNDISCH_TAC [%q {|N + 1 <= n|} ] ----> vARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* Other basic lemmas about sequences.                                       *)
(* ------------------------------------------------------------------------- *)

let%a vSEQ_SUBSEQ = prove
 ([%q {|!f l. f --> l ==> !a b. ~(a = 0) ==> (\n. f(a * n + b)) --> l|} ],
  vREWRITE_TAC[vRIGHT_IMP_FORALL_THM; vSEQ; vGE] ----> vREPEAT vGEN_TAC ---->
  vSUBGOAL_THEN [%q {|!a b n. ~(a = 0) ==> n <= a * n + b|} ]
   (fun th -> vMESON_TAC[th; vLE_TRANS]) ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC(vARITH_RULE
   [%q {|1 * n <= a * n ==> n <= a * n + b|} ]) ---->
  vREWRITE_TAC[vLE_MULT_RCANCEL] ----> vPOP_ASSUM vMP_TAC ----> vARITH_TAC);;

let%a vSEQ_POW = prove
 ([%q {|!f l. (f --> l) ==> !n. (\i. f(i) pow n) --> l pow n|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vINDUCT_TAC ---->
  vREWRITE_TAC[real_pow; vSEQ_CONST] ----> vMATCH_MP_TAC vSEQ_MUL ---->
  vASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Useful lemmas about nested intervals and proof by bisection                *)
(*----------------------------------------------------------------------------*)

let%a vNEST_LEMMA = prove(
  [%q {|!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) ==>
                ?l m. l <= m /\ ((!n. f(n) <= l) /\ f --> l) /\
                                ((!n. m <= g(n)) /\ g --> m)|} ],
  vREPEAT vSTRIP_TAC ----> vMP_TAC(vSPEC [%q {|f:num->real|} ] vMONO_SUC) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vMP_TAC(vSPEC [%q {|g:num->real|} ] vMONO_SUC) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_TAC ----> vSUBGOAL_THEN [%q {|bounded((mr1), (>=) :num->num->bool) f|} ]
  vASSUME_TAC ++-->
   [vMATCH_MP_TAC vSEQ_BOUNDED_2 ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|(f:num->real) 0|} ]; [%q {|(g:num->real) 0|} ]] ---->
    vINDUCT_TAC ----> vASM_REWRITE_TAC[vREAL_LE_REFL] ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|(f:num->real) n|} ] ---->
      vRULE_ASSUM_TAC(vREWRITE_RULE[real_ge]) ----> vASM_REWRITE_TAC[];
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|g(SUC n):real|} ] ---->
      vASM_REWRITE_TAC[] ----> vSPEC_TAC([%q {|SUC n|} ],[%q {|m:num|} ]) ---->
      vINDUCT_TAC ----> vREWRITE_TAC[vREAL_LE_REFL] ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|g(m:num):real|} ] ---->
      vASM_REWRITE_TAC[]]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|bounded((mr1), (>=) :num->num->bool) g|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vSEQ_BOUNDED_2 ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|(f:num->real) 0|} ]; [%q {|(g:num->real) 0|} ]] ---->
    vINDUCT_TAC ----> vASM_REWRITE_TAC[vREAL_LE_REFL] ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|(f:num->real) (SUC n)|} ] ---->
      vASM_REWRITE_TAC[] ----> vSPEC_TAC([%q {|SUC n|} ],[%q {|m:num|} ]) ---->
      vINDUCT_TAC ----> vREWRITE_TAC[vREAL_LE_REFL] ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|(f:num->real) m|} ] ---->
      vRULE_ASSUM_TAC(vREWRITE_RULE[real_ge]) ----> vASM_REWRITE_TAC[];
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|(g:num->real) n|} ] ---->
      vASM_REWRITE_TAC[]]; vALL_TAC] ---->
  vMP_TAC(vSPEC [%q {|f:num->real|} ] vSEQ_BCONV) ----> vASM_REWRITE_TAC[vSEQ_LIM] ---->
  vDISCH_TAC ----> vMP_TAC(vSPEC [%q {|g:num->real|} ] vSEQ_BCONV) ---->
  vASM_REWRITE_TAC[vSEQ_LIM] ----> vDISCH_TAC ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|lim f|} ]; [%q {|lim g|} ]] ----> vASM_REWRITE_TAC[] ---->
  vREPEAT vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSEQ_LE ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|f:num->real|} ]; [%q {|g:num->real|} ]] ----> vASM_REWRITE_TAC[];
    vX_GEN_TAC [%q {|m:num|} ] ----> vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
    vPURE_REWRITE_TAC[vREAL_NOT_LE] ----> vDISCH_TAC ---->
    vUNDISCH_TAC [%q {|f --> lim f|} ] ----> vREWRITE_TAC[vSEQ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|f(m) - lim f|} ]) ---->
    vASM_REWRITE_TAC[vREAL_SUB_LT] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|p:num|} ] vMP_TAC) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|p + m:num|} ]) ---->
    vREWRITE_TAC[vGE; vLE_ADD] ----> vREWRITE_TAC[real_abs] ---->
    vSUBGOAL_THEN [%q {|!p. lim f <= f(p + m:num)|} ] vASSUME_TAC ++-->
     [vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES] ++-->
       [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vFIRST_ASSUM vACCEPT_TAC;
        vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|f(p + m:num):real|} ] ---->
        vRULE_ASSUM_TAC(vREWRITE_RULE[real_ge]) ----> vASM_REWRITE_TAC[]];
      vASM_REWRITE_TAC[vREAL_SUB_LE] ---->
      vREWRITE_TAC[vREAL_NOT_LT; real_sub; vREAL_LE_RADD] ---->
      vSPEC_TAC([%q {|p:num|} ],[%q {|p:num|} ]) ----> vINDUCT_TAC ---->
      vREWRITE_TAC[vREAL_LE_REFL; vADD_CLAUSES] ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|f(p + m:num):real|} ] ---->
      vRULE_ASSUM_TAC(vREWRITE_RULE[real_ge]) ----> vASM_REWRITE_TAC[]];
    vX_GEN_TAC [%q {|m:num|} ] ----> vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
    vPURE_REWRITE_TAC[vREAL_NOT_LE] ----> vDISCH_TAC ---->
    vUNDISCH_TAC [%q {|g --> lim g|} ] ----> vREWRITE_TAC[vSEQ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|lim g - g(m)|} ]) ---->
    vASM_REWRITE_TAC[vREAL_SUB_LT] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|p:num|} ] vMP_TAC) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|p + m:num|} ]) ---->
    vREWRITE_TAC[vGE; vLE_ADD] ----> vREWRITE_TAC[real_abs] ---->
    vSUBGOAL_THEN [%q {|!p. g(p + m:num) < lim g|} ] vASSUME_TAC ++-->
     [vINDUCT_TAC ----> vASM_REWRITE_TAC[vADD_CLAUSES] ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ---->
      vEXISTS_TAC [%q {|g(p + m:num):real|} ] ----> vASM_REWRITE_TAC[];
      vREWRITE_TAC[vREAL_SUB_LE] ----> vASM_REWRITE_TAC[vGSYM vREAL_NOT_LT] ---->
      vREWRITE_TAC[vREAL_NOT_LT; vREAL_NEG_SUB] ---->
      vREWRITE_TAC[real_sub; vREAL_LE_LADD; vREAL_LE_NEG2] ---->
      vSPEC_TAC([%q {|p:num|} ],[%q {|p:num|} ]) ----> vINDUCT_TAC ---->
      vREWRITE_TAC[vREAL_LE_REFL; vADD_CLAUSES] ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|g(p + m:num):real|} ] ---->
      vASM_REWRITE_TAC[]]]);;

let%a vNEST_LEMMA_UNIQ = prove(
  [%q {|!f g. (!n. f(SUC n) >= f(n)) /\
         (!n. g(SUC n) <= g(n)) /\
         (!n. f(n) <= g(n)) /\
         (\n. f(n) - g(n)) --> &0 ==>
                ?l. ((!n. f(n) <= l) /\ f --> l) /\
                    ((!n. l <= g(n)) /\ g --> l)|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(fun th -> vSTRIP_ASSUME_TAC th ----> vMP_TAC th) ---->
  vREWRITE_TAC[vCONJ_ASSOC] ----> vDISCH_THEN(vMP_TAC -| vCONJUNCT1) ---->
  vREWRITE_TAC[vGSYM vCONJ_ASSOC] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vNEST_LEMMA) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|l:real|} ] vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|l:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vSUBGOAL_THEN [%q {|l:real = m|} ] (fun th -> vASM_REWRITE_TAC[th]) ---->
  vMP_TAC(vSPECL [[%q {|f:num->real|} ]; [%q {|l:real|} ]; [%q {|g:num->real|} ]; [%q {|m:real|} ]] vSEQ_SUB) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vMP_TAC -| vCONJ(vASSUME [%q {|(\n. f(n) - g(n)) --> &0|} ])) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSEQ_UNIQ) ---->
  vCONV_TAC(vLAND_CONV vSYM_CONV) ---->
  vREWRITE_TAC[vREAL_SUB_0]);;

let%a vBOLZANO_LEMMA = prove(
  [%q {|!P. (!a b c. a <= b /\ b <= c /\ P(a,b) /\ P(b,c) ==> P(a,c)) /\
       (!x. ?d. &0 < d /\ !a b. a <= x /\ x <= b /\ (b - a) < d ==> P(a,b))
      ==> !a b. a <= b ==> P(a,b)|} ],
  vREPEAT vSTRIP_TAC ---->
  vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ----> vDISCH_TAC ---->
  (vX_CHOOSE_THEN [%q {|f:num->real#real|} ] vSTRIP_ASSUME_TAC -|
   vEXISTENCE -| vBETA_RULE -| vC vISPECL num_Axiom)
    [[%q {|(a:real,(b:real))|} ];
     [%q {|\fn (n:num). if P(FST fn,(FST fn + SND fn)/ &2) then
                        ((FST fn + SND fn)/ &2,SND fn) else
                        (FST fn,(FST fn + SND fn)/ &2)|} ]] ---->
  vMP_TAC(vSPECL
    [[%q {|\n:num. FST(f(n) :real#real)|} ]; [%q {|\n:num. SND(f(n) :real#real)|} ]]
    vNEST_LEMMA_UNIQ) ----> vBETA_TAC ---->
  vSUBGOAL_THEN [%q {|!n:num. FST(f n) <= SND(f n)|} ] vASSUME_TAC ++-->
   [vINDUCT_TAC ----> vASM_REWRITE_TAC[] ---->
    vCOND_CASES_TAC ----> vREWRITE_TAC[] ++-->
     [vMATCH_MP_TAC vREAL_MIDDLE2; vMATCH_MP_TAC vREAL_MIDDLE1] ---->
    vFIRST_ASSUM vACCEPT_TAC; vALL_TAC] ----> vREWRITE_TAC[real_ge] ---->
  vSUBGOAL_THEN [%q {|!n. FST(f n :real#real) <= FST(f(SUC n))|} ]
  vASSUME_TAC ++-->
   [vREWRITE_TAC[real_ge] ----> vINDUCT_TAC ---->
    vFIRST_ASSUM
     (fun th -> vGEN_REWRITE_TAC (funpow 2 vRAND_CONV) [th]) ---->
    vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_LE_REFL] ---->
    vMATCH_MP_TAC vREAL_MIDDLE1 ----> vFIRST_ASSUM vMATCH_ACCEPT_TAC; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!n. ~P(FST((f:num->real#real) n),SND(f n))|} ] vASSUME_TAC ++-->
   [vINDUCT_TAC ----> vASM_REWRITE_TAC[] ---->
    vCOND_CASES_TAC ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC ----> vUNDISCH_TAC [%q {|~P(FST((f:num->real#real) n),SND(f n))|} ] ---->
    vPURE_REWRITE_TAC[vIMP_CLAUSES; vNOT_CLAUSES] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ---->
    vEXISTS_TAC [%q {|(FST(f(n:num)) + SND(f(n))) / &2|} ] ---->
    vASM_REWRITE_TAC[] ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_MIDDLE1; vMATCH_MP_TAC vREAL_MIDDLE2] ---->
    vFIRST_ASSUM vMATCH_ACCEPT_TAC; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!n. SND(f(SUC n) :real#real) <= SND(f n)|} ] vASSUME_TAC ++-->
   [vBETA_TAC ----> vINDUCT_TAC ---->
    vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC
      (vLAND_CONV -| vRAND_CONV) [th]) ---->
    vCOND_CASES_TAC ----> vREWRITE_TAC[vREAL_LE_REFL] ---->
    vMATCH_MP_TAC vREAL_MIDDLE2 ----> vFIRST_ASSUM vMATCH_ACCEPT_TAC; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!n. SND(f n) - FST(f n) = (b - a) / (&2 pow n)|} ]
  vASSUME_TAC ++-->
   [vINDUCT_TAC ++-->
     [vASM_REWRITE_TAC[pow; real_div; vREAL_INV1; vREAL_MUL_RID]; vALL_TAC] ---->
    vASM_REWRITE_TAC[] ----> vCOND_CASES_TAC ----> vREWRITE_TAC[] ---->
    vMATCH_MP_TAC vREAL_EQ_LMUL_IMP ----> vEXISTS_TAC [%q {|&2|} ] ---->
    vREWRITE_TAC[vREAL_SUB_LDISTRIB] ---->
    (vSUBGOAL_THEN [%q {|~(&2 = &0)|} ] (fun th -> vREWRITE_TAC[th] ---->
     vREWRITE_TAC[vMATCH_MP vREAL_DIV_LMUL th]) ++-->
      [vREWRITE_TAC[vREAL_INJ; num_CONV [%q {|2|} ]; vNOT_SUC]; vALL_TAC]) ---->
    vREWRITE_TAC[vGSYM vREAL_DOUBLE] ---->
    vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vREAL_ADD_SYM] ---->
    (vSUBGOAL_THEN [%q {|!x y z. (x + y) - (x + z) = y - z|} ]
     (fun th -> vREWRITE_TAC[th])
     ++-->
      [vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_sub; vREAL_NEG_ADD] ---->
       vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_ADD_RID] ---->
       vSUBST1_TAC(vSYM(vSPEC [%q {|x:real|} ] vREAL_ADD_LINV)) ---->
       vREWRITE_TAC[vREAL_ADD_AC]; vALL_TAC]) ---->
    vASM_REWRITE_TAC[vREAL_DOUBLE] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
    vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[pow] ---->
    (vSUBGOAL_THEN [%q {|~(&2 = &0) /\ ~(&2 pow n = &0)|} ]
       (fun th -> vREWRITE_TAC[vMATCH_MP vREAL_INV_MUL_WEAK th]) ++-->
      [vCONJ_TAC ++--> [vALL_TAC; vMATCH_MP_TAC vPOW_NZ] ---->
       vREWRITE_TAC[vREAL_INJ] ---->
       vREWRITE_TAC[num_CONV [%q {|2|} ]; vNOT_SUC];
       vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
       vGEN_REWRITE_TAC (vRATOR_CONV -| vRAND_CONV)
         [vGSYM vREAL_MUL_LID] ---->
       vAP_THM_TAC ----> vAP_TERM_TAC ----> vCONV_TAC vSYM_CONV ---->
       vMATCH_MP_TAC vREAL_MUL_RINV ----> vREWRITE_TAC[vREAL_INJ] ---->
       vREWRITE_TAC[num_CONV [%q {|2|} ]; vNOT_SUC]]);
    vALL_TAC] ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check (can (find_term is_cond)) -| concl) ---->
  vDISCH_THEN(vK vALL_TAC) ----> vASM_REWRITE_TAC[] ---->
  vW(vC vSUBGOAL_THEN
    (fun t -> vREWRITE_TAC[t]) -| fst -| dest_imp -| rand -| snd) ++-->
   [vONCE_REWRITE_TAC[vSEQ_NEG] ----> vBETA_TAC ---->
    vASM_REWRITE_TAC[vREAL_NEG_SUB; vREAL_NEG_0] ---->
    vREWRITE_TAC[real_div] ----> vSUBGOAL_THEN [%q {|~(&2 = &0)|} ] vASSUME_TAC ++-->
     [vREWRITE_TAC[vREAL_INJ; num_CONV [%q {|2|} ]; vNOT_SUC]; vALL_TAC] ---->
    (vMP_TAC -| vC vSPECL vSEQ_MUL)
      [[%q {|\n:num. b - a|} ]; [%q {|b - a|} ]; [%q {|\n. (inv (&2 pow n))|} ]; [%q {|&0|} ]] ---->
    vREWRITE_TAC[vSEQ_CONST; vREAL_MUL_RZERO] ----> vBETA_TAC ---->
    vDISCH_THEN vMATCH_MP_TAC ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vPOW_INV th]) ---->
    vONCE_REWRITE_TAC[vGSYM vSEQ_ABS] ----> vBETA_TAC ---->
    vREWRITE_TAC[vGSYM vPOW_ABS] ----> vMATCH_MP_TAC vSEQ_POWER_ABS ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vABS_INV th]) ---->
    vREWRITE_TAC[vABS_N] ----> vSUBGOAL_THEN [%q {|&0 < &2|} ]
    (fun th -> vONCE_REWRITE_TAC [vGSYM (vMATCH_MP vREAL_LT_RMUL_EQ th)]) ++-->
     [vREWRITE_TAC[vREAL_LT; num_CONV [%q {|2|} ]; vLT_0]; vALL_TAC] ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV th]) ---->
    vREWRITE_TAC[vREAL_MUL_LID] ----> vREWRITE_TAC[vREAL_LT] ---->
    vREWRITE_TAC[num_CONV [%q {|2|} ]; vLESS_SUC_REFL];
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|l:real|} ] vSTRIP_ASSUME_TAC) ---->
    vFIRST_ASSUM(vX_CHOOSE_THEN [%q {|d:real|} ] vMP_TAC -| vSPEC [%q {|l:real|} ]) ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vUNDISCH_TAC [%q {|(\n:num. SND(f n :real#real)) --> l|} ] ---->
    vUNDISCH_TAC [%q {|(\n:num. FST(f n :real#real)) --> l|} ] ---->
    vREWRITE_TAC[vSEQ] ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|d / &2|} ]) ---->
    vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|N1:num|} ] (vASSUME_TAC -| vBETA_RULE)) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|d / &2|} ]) ----> vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|N2:num|} ] (vASSUME_TAC -| vBETA_RULE)) ---->
    vDISCH_THEN(vMP_TAC -|
      vSPECL [[%q {|FST((f:num->real#real) (N1 + N2))|} ];
             [%q {|SND((f:num->real#real) (N1 + N2))|} ]]) ---->
    vUNDISCH_TAC [%q {|!n. (SND(f n)) - (FST(f n)) = (b - a) / ((& 2) pow n)|} ] ---->
    vDISCH_THEN(vK vALL_TAC) ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|abs(FST(f(N1 + N2:num)) - l) +
                abs(SND(f(N1 + N2:num)) - l)|} ] ---->
    vGEN_REWRITE_TAC (funpow 2 vRAND_CONV) [vGSYM vREAL_HALF_DOUBLE] ---->
    vCONJ_TAC ++-->
     [vGEN_REWRITE_TAC (vRAND_CONV -| vLAND_CONV) [vABS_SUB] ---->
      vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
      vREWRITE_TAC[real_sub; vGSYM vREAL_ADD_ASSOC] ---->
      vREWRITE_TAC[vAC vREAL_ADD_AC [%q {|a + b + c + d = (d + a) + (c + b)|} ]] ---->
      vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID; vREAL_LE_REFL];
      vMATCH_MP_TAC vREAL_LT_ADD2 ---->
      vCONJ_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vREWRITE_TAC[vGE; vLE_ADD] ---->
      vONCE_REWRITE_TAC[vADD_SYM] ----> vREWRITE_TAC[vLE_ADD]]]);;

(* ------------------------------------------------------------------------- *)
(* This one is better for higher-order matching.                             *)
(* ------------------------------------------------------------------------- *)

let%a vBOLZANO_LEMMA_ALT = prove
 ([%q {|!P. (!a b c. a <= b /\ b <= c /\ P a b /\ P b c ==> P a c) /\
       (!x. ?d. &0 < d /\ (!a b. a <= x /\ x <= b /\ b - a < d ==> P a b))
       ==> !a b. a <= b ==> P a b|} ],
  vGEN_TAC ----> vMP_TAC(vSPEC [%q {|\(x:real,y:real). P x y :bool|} ] vBOLZANO_LEMMA) ---->
  vREWRITE_TAC[] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ----> vREWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Define infinite sums                                                       *)
(*----------------------------------------------------------------------------*)

let sums = new_definition
  [%q {|f sums s <=> (\n. sum(0,n) f) --> s|} ];;

let summable = new_definition(
  [%q {|summable f <=> ?s. f sums s|} ]);;

let suminf = new_definition(
  [%q {|suminf f = @s. f sums s|} ]);;

(*----------------------------------------------------------------------------*)
(* If summable then it sums to the sum (!)                                    *)
(*----------------------------------------------------------------------------*)

let%a vSUM_SUMMABLE = prove(
  [%q {|!f l. f sums l ==> summable f|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[summable] ---->
  vEXISTS_TAC [%q {|l:real|} ] ----> vPOP_ASSUM vACCEPT_TAC);;

let%a vSUMMABLE_SUM = prove(
  [%q {|!f. summable f ==> f sums (suminf f)|} ],
  vGEN_TAC ----> vREWRITE_TAC[summable; suminf] ---->
  vDISCH_THEN(vCHOOSE_THEN vMP_TAC) ---->
  vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ---->
  vMATCH_ACCEPT_TAC vSELECT_AX);;

(*----------------------------------------------------------------------------*)
(* And the sum is unique                                                      *)
(*----------------------------------------------------------------------------*)

let%a vSUM_UNIQ = prove(
  [%q {|!f x. f sums x ==> (x = suminf f)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|summable f|} ] vMP_TAC ++-->
   [vREWRITE_TAC[summable] ----> vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[];
    vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vSUMMABLE_SUM) ---->
    vMATCH_MP_TAC vSEQ_UNIQ ---->
    vEXISTS_TAC [%q {|\n. sum(0,n) f|} ] ----> vASM_REWRITE_TAC[vGSYM sums]]);;

let%a vSER_UNIQ = prove
 ([%q {|!f x y. f sums x /\ f sums y ==> (x = y)|} ],
  vMESON_TAC[vSUM_UNIQ]);;

(*----------------------------------------------------------------------------*)
(* Series which is zero beyond a certain point                                *)
(*----------------------------------------------------------------------------*)

let%a vSER_0 = prove(
  [%q {|!f n. (!m. n <= m ==> (f(m) = &0)) ==>
        f sums (sum(0,n) f)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[sums; vSEQ] ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ----> vEXISTS_TAC [%q {|n:num|} ] ---->
  vX_GEN_TAC [%q {|m:num|} ] ----> vREWRITE_TAC[vGE] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC -| vMATCH_MP vLESS_EQUAL_ADD) ---->
  vW(vC vSUBGOAL_THEN vSUBST1_TAC -| vC (curry mk_eq) [%q {|&0|} ] -| rand -| rator -| snd) ---->
  vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vABS_ZERO; vREAL_SUB_0] ---->
  vBETA_TAC ----> vREWRITE_TAC[vGSYM vSUM_TWO; vREAL_ADD_RID_UNIQ] ---->
  vFIRST_ASSUM(vMATCH_MP_TAC -| vMATCH_MP(vREWRITE_RULE[vGE] vSUM_ZERO)) ---->
  vMATCH_ACCEPT_TAC vLE_REFL);;

(*----------------------------------------------------------------------------*)
(* summable series of positive terms has limit >(=) any partial sum           *)
(*----------------------------------------------------------------------------*)

let%a vSER_POS_LE = prove(
  [%q {|!f n. summable f /\ (!m. n <= m ==> &0 <= f(m))
        ==> sum(0,n) f <= suminf f|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vSUMMABLE_SUM) ----> vREWRITE_TAC[sums] ---->
  vMP_TAC(vSPEC [%q {|sum(0,n) f|} ] vSEQ_CONST) ---->
  vGEN_REWRITE_TAC vI [vIMP_IMP] ---->
  vMATCH_MP_TAC(vREWRITE_RULE[vTAUT [%q {|a /\ b /\ c ==> d <=> c ==> a /\ b ==> d|} ]]
    vSEQ_LE) ----> vBETA_TAC ---->
  vEXISTS_TAC [%q {|n:num|} ] ----> vX_GEN_TAC [%q {|m:num|} ] ----> vREWRITE_TAC[vGE] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC -| vMATCH_MP vLESS_EQUAL_ADD) ---->
  vREWRITE_TAC[vGSYM vSUM_TWO; vREAL_LE_ADDR] ---->
  vMATCH_MP_TAC vSUM_POS_GEN ----> vFIRST_ASSUM vMATCH_ACCEPT_TAC);;

let%a vSER_POS_LT = prove(
  [%q {|!f n. summable f /\ (!m. n <= m ==> &0 < f(m))
        ==> sum(0,n) f < suminf f|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|sum(0,n + 1) f|} ] ---->
  vCONJ_TAC ++-->
   [vREWRITE_TAC[vGSYM vSUM_TWO; vREAL_LT_ADDR] ---->
    vREWRITE_TAC[num_CONV [%q {|1|} ]; sum; vREAL_ADD_LID; vADD_CLAUSES] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vMATCH_ACCEPT_TAC vLE_REFL;
    vMATCH_MP_TAC vSER_POS_LE ----> vASM_REWRITE_TAC[] ---->
    vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
    vFIRST_ASSUM vMATCH_MP_TAC ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC [%q {|SUC n|} ] ---->
    vREWRITE_TAC[vLESS_EQ_SUC_REFL] ----> vASM_REWRITE_TAC[vADD1]]);;

(*----------------------------------------------------------------------------*)
(* Theorems about grouping and offsetting, *not* permuting, terms             *)
(*----------------------------------------------------------------------------*)

let%a vSER_GROUP = prove(
  [%q {|!f k. summable f /\ 0 < k ==>
          (\n. sum(n * k,k) f) sums (suminf f)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUMMABLE_SUM) ---->
  vREWRITE_TAC[sums; vSEQ] ----> vBETA_TAC ---->
  vDISCH_THEN(fun t -> vX_GEN_TAC [%q {|e:real|} ] ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP t)) ---->
  vREWRITE_TAC[vGE] ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|N:num|} ]) ---->
  vREWRITE_TAC[vSUM_GROUP] ----> vEXISTS_TAC [%q {|N:num|} ] ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC [%q {|n:num|} ] ---->
  vASM_REWRITE_TAC[] ----> vUNDISCH_TAC [%q {|0 < k|} ] ---->
  vSTRUCT_CASES_TAC(vSPEC [%q {|k:num|} ] num_CASES) ---->
  vREWRITE_TAC[vMULT_CLAUSES; vLE_ADD; vCONJUNCT1 vLE] ---->
  vREWRITE_TAC[vLT_REFL]);;

let%a vSER_PAIR = prove(
  [%q {|!f. summable f ==> (\n. sum(2 * n,2) f) sums (suminf f)|} ],
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vC vCONJ (vSPEC [%q {|1:num|} ] vLT_0)) ---->
  vREWRITE_TAC[vSYM(num_CONV [%q {|2|} ])] ----> vONCE_REWRITE_TAC[vMULT_SYM] ---->
  vMATCH_ACCEPT_TAC vSER_GROUP);;

let%a vSER_OFFSET = prove(
  [%q {|!f. summable f ==> !k. (\n. f(n + k)) sums (suminf f - sum(0,k) f)|} ],
  vGEN_TAC ---->
  vDISCH_THEN((---->) vGEN_TAC -| vMP_TAC -| vMATCH_MP vSUMMABLE_SUM) ---->
  vREWRITE_TAC[sums; vSEQ] ---->
  vDISCH_THEN(fun th -> vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP th)) ---->
  vBETA_TAC ----> vREWRITE_TAC[vGE] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|N:num|} ]) ---->
  vEXISTS_TAC [%q {|N:num|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ----> vDISCH_TAC ---->
  vREWRITE_TAC[vSUM_OFFSET] ---->
  vREWRITE_TAC[real_sub; vREAL_NEG_ADD; vREAL_NEG_NEG] ---->
  vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
    [%q {|(a + b) + (c + d) = (b + d) + (a + c)|} ]] ---->
  vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID] ----> vREWRITE_TAC[vGSYM real_sub] ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vMATCH_MP_TAC vLE_TRANS ---->
  vEXISTS_TAC [%q {|n:num|} ] ----> vASM_REWRITE_TAC[vLE_ADD]);;

let%a vSER_OFFSET_REV = prove
 ([%q {|!f k. summable(\n. f(n + k)) ==>
         f sums (sum(0,k) f) + suminf (\n. f(n + k))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUMMABLE_SUM) ---->
  vREWRITE_TAC[sums; vSEQ] ----> vREWRITE_TAC[vSUM_OFFSET] ---->
  vMATCH_MP_TAC vMONO_FORALL ----> vGEN_TAC ---->
  vMATCH_MP_TAC(vTAUT [%q {|(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)|} ]) ---->
  vDISCH_TAC ----> vREWRITE_TAC[vGSYM(vONCE_REWRITE_RULE[vADD_SYM] vSUM_DIFF)] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:num|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|N + k:num|} ] ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vREWRITE_TAC[vGE; vLE_EXISTS] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC) ---->
  vONCE_REWRITE_TAC[vARITH_RULE [%q {|(N + k) + d = k + N + d:num|} ]] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|a - (b + c) = a - b - c|} ]] ---->
  vREWRITE_TAC[vGSYM vSUM_DIFF] ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vARITH_TAC);;

(*----------------------------------------------------------------------------*)
(* Similar version for pairing up terms                                       *)
(*----------------------------------------------------------------------------*)

let%a vSER_POS_LT_PAIR = prove(
  [%q {|!f n. summable f /\
         (!d. &0 < (f(n + (2 * d))) +
               f(n + ((2 * d) + 1)))
        ==> sum(0,n) f < suminf f|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vSUMMABLE_SUM) ---->
  vREWRITE_TAC[sums; vSEQ] ----> vBETA_TAC ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vREAL_NOT_LT] ----> vDISCH_TAC ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|f(n) + f(n + 1)|} ]) ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC [%q {|0|} ]) ---->
  vREWRITE_TAC[vADD_CLAUSES; vMULT_CLAUSES] ---->
  vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:num|} ] vMP_TAC) ---->
  vSUBGOAL_THEN [%q {|sum(0,n + 2) f <= sum(0,(2 * (SUC N)) + n) f|} ]
  vASSUME_TAC ++-->
   [vSPEC_TAC([%q {|N:num|} ],[%q {|N:num|} ]) ----> vINDUCT_TAC ++-->
     [vREWRITE_TAC[vMULT_CLAUSES; vADD_CLAUSES] ---->
      vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vADD_SYM] ---->
      vMATCH_ACCEPT_TAC vREAL_LE_REFL;
      vABBREV_TAC [%q {|M = SUC N|} ] ---->
      vREWRITE_TAC[vMULT_CLAUSES] ---->
      vREWRITE_TAC[num_CONV [%q {|2|} ]; vADD_CLAUSES] ---->
      vREWRITE_TAC[vGSYM(vONCE_REWRITE_RULE[vADD_SYM] vADD1)] ---->
      vREWRITE_TAC[vSYM(num_CONV [%q {|2|} ])] ----> vREWRITE_TAC[vADD_CLAUSES] ---->
      vGEN_REWRITE_TAC (vRATOR_CONV -| vONCE_DEPTH_CONV) [vADD1] ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC] ---->
      vREWRITE_TAC[vGSYM vADD1; vSYM(num_CONV [%q {|2|} ])] ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ---->
      vEXISTS_TAC [%q {|sum(0,(2 * M) + n) f|} ] ---->
      vASM_REWRITE_TAC[] ----> vREWRITE_TAC[sum] ---->
      vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC; vREAL_LE_ADDR] ---->
      vREWRITE_TAC[vADD_CLAUSES] ----> vREWRITE_TAC[vADD1] ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
      vREWRITE_TAC[vGSYM vADD_ASSOC] ---->
      vONCE_REWRITE_TAC[vSPEC [%q {|1|} ] vADD_SYM] ---->
      vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]];
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|(2 * (SUC N)) + n|} ]) ---->
    vW(vC vSUBGOAL_THEN (fun th -> vREWRITE_TAC[th]) -|
      funpow 2(fst -| dest_imp) -| snd) ++-->
     [vREWRITE_TAC[num_CONV [%q {|2|} ]; vMULT_CLAUSES] ---->
      vONCE_REWRITE_TAC[vAC vADD_AC
       [%q {|(a + (b + c)) + d:num = b + (a + (c + d))|} ]] ---->
      vREWRITE_TAC[vGE; vLE_ADD]; vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|(suminf f + (f(n) + f(n + 1))) <=
                              sum(0,(2 * (SUC N)) + n) f|} ]
    vASSUME_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ---->
      vEXISTS_TAC [%q {|sum(0,n + 2) f|} ] ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ---->
      vEXISTS_TAC [%q {|sum(0,n) f + (f(n) + f(n + 1))|} ] ---->
      vASM_REWRITE_TAC[vREAL_LE_RADD] ---->
      vMATCH_MP_TAC vREAL_EQ_IMP_LE ---->
      vCONV_TAC(vREDEPTH_CONV num_CONV) ---->
      vREWRITE_TAC[vADD_CLAUSES; sum; vREAL_ADD_ASSOC]; vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|suminf f <= sum(0,(2 * (SUC N)) + n) f|} ]
    vASSUME_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ---->
      vEXISTS_TAC [%q {|suminf f + (f(n) + f(n + 1))|} ] ---->
      vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vREAL_LE_ADDR] ---->
      vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vFIRST_ASSUM vACCEPT_TAC; vALL_TAC] ---->
    vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
    vREWRITE_TAC[vREAL_LT_SUB_RADD] ---->
    vGEN_REWRITE_TAC (funpow 2 vRAND_CONV) [vREAL_ADD_SYM] ---->
    vASM_REWRITE_TAC[vREAL_NOT_LT]]);;

(*----------------------------------------------------------------------------*)
(* Prove a few composition formulas for series                                *)
(*----------------------------------------------------------------------------*)

let%a vSER_ADD = prove(
  [%q {|!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) + y(n)) sums (x0 + y0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[sums; vSUM_ADD] ---->
  vCONV_TAC((vRAND_CONV -| vEXACT_CONV)[vX_BETA_CONV [%q {|n:num|} ] [%q {|sum(0,n) x|} ]]) ---->
  vCONV_TAC((vRAND_CONV -| vEXACT_CONV)[vX_BETA_CONV [%q {|n:num|} ] [%q {|sum(0,n) y|} ]]) ---->
  vMATCH_ACCEPT_TAC vSEQ_ADD);;

let%a vSER_CMUL = prove(
  [%q {|!x x0 c. x sums x0 ==> (\n. c * x(n)) sums (c * x0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[sums; vSUM_CMUL] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|(\n. (\n. c) n * (\n. sum(0,n) x) n) --> c * x0|} ] vMP_TAC ++-->
   [vMATCH_MP_TAC vSEQ_MUL ----> vASM_REWRITE_TAC[vSEQ_CONST];
    vREWRITE_TAC[vBETA_THM]]);;

let%a vSER_NEG = prove(
  [%q {|!x x0. x sums x0 ==> (\n. --(x n)) sums --x0|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_NEG_MINUS1] ---->
  vMATCH_ACCEPT_TAC vSER_CMUL);;

let%a vSER_SUB = prove(
  [%q {|!x x0 y y0. x sums x0 /\ y sums y0 ==> (\n. x(n) - y(n)) sums (x0 - y0)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(fun th -> vMP_TAC (vMATCH_MP vSER_ADD
      (vCONJ (vCONJUNCT1 th) (vMATCH_MP vSER_NEG (vCONJUNCT2 th))))) ---->
  vBETA_TAC ----> vREWRITE_TAC[real_sub]);;

let%a vSER_CDIV = prove(
  [%q {|!x x0 c. x sums x0 ==> (\n. x(n) / c) sums (x0 / c)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_div] ---->
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vMATCH_ACCEPT_TAC vSER_CMUL);;

(*----------------------------------------------------------------------------*)
(* Prove Cauchy-type criterion for convergence of series                      *)
(*----------------------------------------------------------------------------*)

let%a vSER_CAUCHY = prove(
  [%q {|!f. summable f <=>
          !e. &0 < e ==> ?N. !m n. m >= N ==> abs(sum(m,n) f) < e|} ],
  vGEN_TAC ----> vREWRITE_TAC[summable; sums] ---->
  vREWRITE_TAC[vGSYM convergent] ---->
  vREWRITE_TAC[vGSYM vSEQ_CAUCHY] ----> vREWRITE_TAC[cauchy] ---->
  vAP_TERM_TAC ----> vABS_TAC ----> vREWRITE_TAC[vGE] ----> vBETA_TAC ---->
  vREWRITE_TAC[vTAUT [%q {|((a ==> b) <=> (a ==> c)) <=> a ==> (b <=> c)|} ]] ---->
  vDISCH_TAC ----> vEQ_TAC ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|N:num|} ]) ---->
  vEXISTS_TAC [%q {|N:num|} ] ----> vREPEAT vGEN_TAC ----> vDISCH_TAC ++-->
   [vONCE_REWRITE_TAC[vSUM_DIFF] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC [%q {|m:num|} ] ---->
    vASM_REWRITE_TAC[vLE_ADD];
    vDISJ_CASES_THEN vMP_TAC (vSPECL [[%q {|m:num|} ]; [%q {|n:num|} ]] vLE_CASES) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|p:num|} ] vSUBST1_TAC -|
      vMATCH_MP vLESS_EQUAL_ADD) ++-->
     [vONCE_REWRITE_TAC[vABS_SUB]; vALL_TAC] ---->
    vREWRITE_TAC[vGSYM vSUM_DIFF] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Show that if a series converges, the terms tend to 0                       *)
(*----------------------------------------------------------------------------*)

let%a vSER_ZERO = prove(
  [%q {|!f. summable f ==> f --> &0|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vSEQ] ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vUNDISCH_TAC [%q {|summable f|} ] ----> vREWRITE_TAC[vSER_CAUCHY] ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vMATCH_MP th)) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|N:num|} ] vMP_TAC) ---->
  vDISCH_THEN((---->) (vEXISTS_TAC [%q {|N:num|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
  vDISCH_TAC) -| vMP_TAC) ----> vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|n:num|} ]; [%q {|SUC 0|} ]]) ---->
  vASM_REWRITE_TAC[sum; vREAL_SUB_RZERO; vREAL_ADD_LID; vADD_CLAUSES]);;

(*----------------------------------------------------------------------------*)
(* Now prove the comparison test                                              *)
(*----------------------------------------------------------------------------*)

let%a vSER_COMPAR = prove(
  [%q {|!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable f|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vSER_CAUCHY; vGE] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 (vX_CHOOSE_TAC [%q {|N1:num|} ]) vMP_TAC) ---->
  vREWRITE_TAC[vSER_CAUCHY; vGE] ----> vDISCH_TAC ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|N2:num|} ]) ----> vEXISTS_TAC [%q {|N1 + N2:num|} ] ---->
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|sum(m,n)(\k. abs(f k))|} ] ----> vREWRITE_TAC[vABS_SUM] ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|sum(m,n) g|} ] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSUM_LE ----> vBETA_TAC ---->
    vX_GEN_TAC [%q {|p:num|} ] ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC [%q {|m:num|} ] ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vLE_TRANS ---->
    vEXISTS_TAC [%q {|N1 + N2:num|} ] ----> vASM_REWRITE_TAC[vLE_ADD]; vALL_TAC] ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|abs(sum(m,n) g)|} ] ---->
  vREWRITE_TAC[vABS_LE] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vMATCH_MP_TAC vLE_TRANS ----> vEXISTS_TAC [%q {|N1 + N2:num|} ] ---->
  vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
  vREWRITE_TAC[vLE_ADD]);;

(*----------------------------------------------------------------------------*)
(* And a similar version for absolute convergence                             *)
(*----------------------------------------------------------------------------*)

let%a vSER_COMPARA = prove(
  [%q {|!f g. (?N. !n. n >= N ==> abs(f(n)) <= g(n)) /\ summable g ==>
            summable (\k. abs(f k))|} ],
  vREPEAT vGEN_TAC ----> vSUBGOAL_THEN [%q {|!n. abs(f(n)) = abs((\k:num. abs(f k)) n)|} ]
  (fun th -> vGEN_REWRITE_TAC (vRATOR_CONV -| vONCE_DEPTH_CONV) [th])
  ++-->
   [vGEN_TAC ----> vBETA_TAC ----> vREWRITE_TAC[vABS_ABS];
    vMATCH_ACCEPT_TAC vSER_COMPAR]);;

(*----------------------------------------------------------------------------*)
(* Limit comparison property for series                                       *)
(*----------------------------------------------------------------------------*)

let%a vSER_LE = prove(
  [%q {|!f g. (!n. f(n) <= g(n)) /\ summable f /\ summable g
        ==> suminf f <= suminf g|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN (fun th -> vASSUME_TAC th ----> vASSUME_TAC
    (vREWRITE_RULE[sums] (vMATCH_MP vSUMMABLE_SUM th)))) ---->
  vMATCH_MP_TAC vSEQ_LE ----> vREWRITE_TAC[vCONJ_ASSOC] ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|\n. sum(0,n) f|} ]; [%q {|\n. sum(0,n) g|} ]] ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vGSYM sums] ----> vCONJ_TAC ---->
    vMATCH_MP_TAC vSUMMABLE_SUM ----> vFIRST_ASSUM vACCEPT_TAC;
    vEXISTS_TAC [%q {|0|} ] ----> vREWRITE_TAC[vGE; vLE_0] ---->
    vGEN_TAC ----> vBETA_TAC ----> vMATCH_MP_TAC vSUM_LE ---->
    vGEN_TAC ----> vASM_REWRITE_TAC[vLE_0]]);;

let%a vSER_LE2 = prove(
  [%q {|!f g. (!n. abs(f n) <= g(n)) /\ summable g ==>
                summable f /\ suminf f <= suminf g|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|summable f|} ] vASSUME_TAC ++-->
   [vMATCH_MP_TAC vSER_COMPAR ----> vEXISTS_TAC [%q {|g:num->real|} ] ---->
    vASM_REWRITE_TAC[]; vASM_REWRITE_TAC[]] ---->
  vMATCH_MP_TAC vSER_LE ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|n:num|} ] ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|abs(f(n:num))|} ] ----> vASM_REWRITE_TAC[vABS_LE]);;

(*----------------------------------------------------------------------------*)
(* Show that absolute convergence implies normal convergence                  *)
(*----------------------------------------------------------------------------*)

let%a vSER_ACONV = prove(
  [%q {|!f. summable (\n. abs(f n)) ==> summable f|} ],
  vGEN_TAC ----> vREWRITE_TAC[vSER_CAUCHY] ----> vREWRITE_TAC[vSUM_ABS] ---->
  vDISCH_THEN((---->) (vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC) -| vMP_TAC) ---->
  vDISCH_THEN(vIMP_RES_THEN (vX_CHOOSE_TAC [%q {|N:num|} ])) ---->
  vEXISTS_TAC [%q {|N:num|} ] ----> vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vANTE_RES_THEN vASSUME_TAC) ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|sum(m,n)(\m. abs(f m))|} ] ----> vASM_REWRITE_TAC[vABS_SUM]);;

(*----------------------------------------------------------------------------*)
(* Absolute value of series                                                   *)
(*----------------------------------------------------------------------------*)

let%a vSER_ABS = prove(
  [%q {|!f. summable(\n. abs(f n)) ==> abs(suminf f) <= suminf(\n. abs(f n))|} ],
  vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vSUMMABLE_SUM -| vMATCH_MP vSER_ACONV) ---->
  vPOP_ASSUM(vMP_TAC -| vMATCH_MP vSUMMABLE_SUM) ---->
  vREWRITE_TAC[sums] ----> vDISCH_TAC ---->
  vDISCH_THEN(vASSUME_TAC -| vBETA_RULE -| vMATCH_MP vSEQ_ABS_IMP) ---->
  vMATCH_MP_TAC vSEQ_LE ----> vMAP_EVERY vEXISTS_TAC
   [[%q {|\n. abs(sum(0,n)f)|} ]; [%q {|\n. sum(0,n)(\n. abs(f n))|} ]] ---->
  vASM_REWRITE_TAC[] ----> vEXISTS_TAC [%q {|0|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
  vDISCH_THEN(vK vALL_TAC) ----> vBETA_TAC ----> vMATCH_ACCEPT_TAC vSUM_ABS_LE);;

(*----------------------------------------------------------------------------*)
(* Prove sum of geometric progression (useful for comparison)                 *)
(*----------------------------------------------------------------------------*)

let%a vGP_FINITE = prove(
  [%q {|!x. ~(x = &1) ==>
        !n. (sum(0,n) (\n. x pow n) = ((x pow n) - &1) / (x - &1))|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vINDUCT_TAC ++-->
   [vREWRITE_TAC[sum; pow; vREAL_SUB_REFL; vREAL_DIV_LZERO];
    vREWRITE_TAC[sum; pow] ----> vBETA_TAC ---->
    vASM_REWRITE_TAC[vADD_CLAUSES] ---->
    vSUBGOAL_THEN [%q {|~(x - &1 = &0)|} ] vASSUME_TAC ---->
    vASM_REWRITE_TAC[vREAL_SUB_0] ---->
    vMP_TAC(vGENL [[%q {|p:real|} ]; [%q {|q:real|} ]]
     (vSPECL [[%q {|p:real|} ]; [%q {|q:real|} ]; [%q {|x - &1|} ]] vREAL_EQ_RMUL)) ---->
    vASM_REWRITE_TAC[] ----> vDISCH_THEN(fun th -> vONCE_REWRITE_TAC[vGSYM th]) ---->
    vREWRITE_TAC[vREAL_RDISTRIB] ----> vSUBGOAL_THEN
      [%q {|!p. (p / (x - &1)) * (x - &1) = p|} ] (fun th -> vREWRITE_TAC[th]) ++-->
      [vGEN_TAC ----> vMATCH_MP_TAC vREAL_DIV_RMUL ----> vASM_REWRITE_TAC[]; vALL_TAC]
    ----> vREWRITE_TAC[vREAL_SUB_LDISTRIB] ----> vREWRITE_TAC[real_sub] ---->
    vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
      [%q {|(a + b) + (c + d) = (c + b) + (d + a)|} ]] ---->
    vREWRITE_TAC[vREAL_MUL_RID; vREAL_ADD_LINV; vREAL_ADD_RID] ---->
    vAP_THM_TAC ----> vAP_TERM_TAC ----> vMATCH_ACCEPT_TAC vREAL_MUL_SYM]);;

let%a vGP = prove(
  [%q {|!x. abs(x) < &1 ==> (\n. x pow n) sums inv(&1 - x)|} ],
  vGEN_TAC ----> vASM_CASES_TAC [%q {|x = &1|} ] ---->
  vASM_REWRITE_TAC[vABS_1; vREAL_LT_REFL] ----> vDISCH_TAC ---->
  vREWRITE_TAC[sums] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vGP_FINITE th]) ---->
  vREWRITE_TAC[vREAL_INV_1OVER] ----> vREWRITE_TAC[real_div] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vABS_CONV) [vGSYM vREAL_NEG_MUL2] ---->
  vSUBGOAL_THEN [%q {|~(x - &1 = &0)|} ]
    (fun t -> vREWRITE_TAC[vMATCH_MP vREAL_NEG_INV t]) ++-->
    [vASM_REWRITE_TAC[vREAL_SUB_0]; vALL_TAC] ---->
  vREWRITE_TAC[vREAL_NEG_SUB; vGSYM real_div] ---->
  vSUBGOAL_THEN [%q {|(\n. (\n. &1 - x pow n) n / (\n. &1 - x) n) --> &1 / (&1 - x)|} ]
  vMP_TAC ++--> [vALL_TAC; vREWRITE_TAC[vBETA_THM]] ---->
  vMATCH_MP_TAC vSEQ_DIV ----> vBETA_TAC ----> vREWRITE_TAC[vSEQ_CONST] ---->
  vREWRITE_TAC[vREAL_SUB_0] ----> vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ---->
  vASM_REWRITE_TAC[] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_SUB_RZERO] ---->
  vSUBGOAL_THEN [%q {|(\n. (\n. &1) n - (\n. x pow n) n) --> &1 - &0|} ]
  vMP_TAC ++--> [vALL_TAC; vREWRITE_TAC[vBETA_THM]] ---->
  vMATCH_MP_TAC vSEQ_SUB ----> vBETA_TAC ----> vREWRITE_TAC[vSEQ_CONST] ---->
  vMATCH_MP_TAC vSEQ_POWER ----> vFIRST_ASSUM vACCEPT_TAC);;

(*----------------------------------------------------------------------------*)
(* Now prove the ratio test                                                   *)
(*----------------------------------------------------------------------------*)

let%a vABS_NEG_LEMMA = prove(
  [%q {|!c x y. c <= &0 ==> abs(x) <= c * abs(y) ==> (x = &0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vGSYM vREAL_NEG_GE0] ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|--c|} ]; [%q {|abs(y)|} ]] vREAL_LE_MUL) ---->
  vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vABS_POS; vGSYM vREAL_NEG_LMUL; vREAL_NEG_GE0] ---->
  vDISCH_THEN(fun th -> vDISCH_THEN(vMP_TAC -| vC vCONJ th)) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LE_TRANS) ----> vCONV_TAC vCONTRAPOS_CONV ---->
  vREWRITE_TAC[vABS_NZ; vREAL_NOT_LE]);;

let%a vSER_RATIO = prove(
  [%q {|!f c N. c < &1 /\
           (!n. n >= N ==> abs(f(SUC n)) <= c * abs(f(n))) ==>
       summable f|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN vSTRIP_ASSUME_TAC ---->
  vDISJ_CASES_TAC (vSPECL [[%q {|c:real|} ]; [%q {|&0|} ]] vREAL_LET_TOTAL) ++-->
   [vREWRITE_TAC[vSER_CAUCHY] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
    vSUBGOAL_THEN [%q {|!n. n >= N ==> (f(SUC n) = &0)|} ] vASSUME_TAC ++-->
     [vGEN_TAC ----> vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
      vMATCH_MP_TAC vABS_NEG_LEMMA ----> vFIRST_ASSUM vACCEPT_TAC; vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|!n. n >= (SUC N) ==> (f(n) = &0)|} ] vASSUME_TAC ++-->
     [vGEN_TAC ----> vSTRUCT_CASES_TAC(vSPEC [%q {|n:num|} ] num_CASES) ++-->
       [vREWRITE_TAC[vGE] ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vOR_LESS) ---->
        vREWRITE_TAC[vNOT_LESS_0];
        vREWRITE_TAC[vGE; vLE_SUC] ---->
        vASM_REWRITE_TAC[vGSYM vGE]]; vALL_TAC] ---->
    vEXISTS_TAC [%q {|SUC N|} ] ----> vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vSUM_ZERO) ---->
    vREPEAT vGEN_TAC ---->
    vDISCH_THEN(vANTE_RES_THEN (fun th -> vREWRITE_TAC[th])) ---->
    vASM_REWRITE_TAC[vABS_0];

    vMATCH_MP_TAC vSER_COMPAR ---->
    vEXISTS_TAC [%q {|\n. (abs(f N) / c pow N) * (c pow n)|} ] ----> vCONJ_TAC ++-->
     [vEXISTS_TAC [%q {|N:num|} ] ----> vX_GEN_TAC [%q {|n:num|} ] ---->
      vREWRITE_TAC[vGE] ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:num|} ] vSUBST1_TAC -| vMATCH_MP vLESS_EQUAL_ADD)
      ----> vBETA_TAC ----> vREWRITE_TAC[vPOW_ADD] ----> vREWRITE_TAC[real_div] ---->
      vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
        [%q {|(a * b) * (c * d) = (a * d) * (b * c)|} ]] ---->
      vSUBGOAL_THEN [%q {|~(c pow N = &0)|} ]
        (fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV th; vREAL_MUL_RID]) ++-->
       [vMATCH_MP_TAC vPOW_NZ ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
        vMATCH_MP_TAC vREAL_LT_IMP_NE ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
      vSPEC_TAC([%q {|d:num|} ],[%q {|d:num|} ]) ----> vINDUCT_TAC ---->
      vREWRITE_TAC[pow; vADD_CLAUSES; vREAL_MUL_RID; vREAL_LE_REFL] ---->
      vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|c * abs(f(N + d:num))|} ] ---->
      vCONJ_TAC ++-->
       [vFIRST_ASSUM vMATCH_MP_TAC ----> vREWRITE_TAC[vGE; vLE_ADD];
        vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
          [%q {|a * (b * c) = b * (a * c)|} ]] ---->
        vFIRST_ASSUM(fun th -> vASM_REWRITE_TAC[vMATCH_MP vREAL_LE_LMUL_LOCAL th])];

      vREWRITE_TAC[summable] ---->
      vEXISTS_TAC [%q {|(abs(f(N:num)) / (c pow N)) * inv(&1 - c)|} ] ---->
      vMATCH_MP_TAC vSER_CMUL ----> vMATCH_MP_TAC vGP ---->
      vASSUME_TAC(vMATCH_MP vREAL_LT_IMP_LE (vASSUME [%q {|&0 < c|} ])) ---->
      vASM_REWRITE_TAC[real_abs]]]);;

(* ------------------------------------------------------------------------- *)
(* The error in truncating a convergent series is bounded by partial sums.   *)
(* ------------------------------------------------------------------------- *)

let%a vSEQ_TRUNCATION = prove
 ([%q {|!f l n b.
        f sums l /\ (!m. abs(sum(n,m) f) <= b)
        ==> abs(l - sum(0,n) f) <= b|} ],
  vREPEAT vSTRIP_TAC ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vSUM_SUMMABLE) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|n:num|} ] -| vMATCH_MP vSER_OFFSET) ---->
  vREWRITE_TAC[sums] ---->
  vFIRST_ASSUM(vSUBST1_TAC -| vSYM -| vMATCH_MP vSUM_UNIQ) ---->
  vDISCH_THEN(vASSUME_TAC -| vMATCH_MP vSEQ_ABS_IMP) ---->
  vMATCH_MP_TAC vSEQ_LE ---->
  vREWRITE_TAC[vRIGHT_EXISTS_AND_THM] ---->
  vFIRST_ASSUM(fun th -> vEXISTS_TAC (lhand(concl th)) ---->
                        vCONJ_TAC ++--> [vACCEPT_TAC th; vALL_TAC]) ---->
  vEXISTS_TAC [%q {|\r:num. b:real|} ] ----> vREWRITE_TAC[vSEQ_CONST] ---->
  vASM_REWRITE_TAC[vGSYM vSUM_REINDEX; vADD_CLAUSES]);;

(*============================================================================*)
(* Theory of limits, continuity and differentiation of real->real functions   *)
(*============================================================================*)

parse_as_infix ("tends_real_real",(12,"right"));;

parse_as_infix ("diffl",(12,"right"));;
parse_as_infix ("contl",(12,"right"));;
parse_as_infix ("differentiable",(12,"right"));;

(*----------------------------------------------------------------------------*)
(* Specialize nets theorems to the pointwise limit of real->real functions    *)
(*----------------------------------------------------------------------------*)

let tends_real_real = new_definition
  [%q {|(f tends_real_real l)(x0) <=>
        (f tends l)(mtop(mr1),tendsto(mr1,x0))|} ];;

override_interface ("-->",[%q {|(tends_real_real)|} ]);;

let%a vLIM = prove(
  [%q {|!f y0 x0. (f --> y0)(x0) <=>
        !e. &0 < e ==>
            ?d. &0 < d /\ !x. &0 < abs(x - x0) /\ abs(x - x0) < d ==>
                abs(f(x) - y0) < e|} ],
  vREPEAT vGEN_TAC ---->
  vREWRITE_TAC[tends_real_real; vMATCH_MP vLIM_TENDS2 (vSPEC [%q {|x0:real|} ] vMR1_LIMPT)]
  ----> vREWRITE_TAC[vMR1_DEF] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vABS_SUB] ---->
  vREFL_TAC);;

let%a vLIM_CONST = prove(
  [%q {|!k x. ((\x. k) --> k)(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real; vMTOP_TENDS] ---->
  vGEN_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[vMETRIC_SAME] ---->
  vREWRITE_TAC[tendsto; vREAL_LE_REFL] ---->
  vMP_TAC(vREWRITE_RULE[vMTOP_LIMPT] (vSPEC [%q {|x:real|} ] vMR1_LIMPT)) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e:real|} ]) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] (vASSUME_TAC -| vCONJUNCT1)) ---->
  vEXISTS_TAC [%q {|z:real|} ] ----> vREWRITE_TAC[vMR1_DEF; vGSYM vABS_NZ] ---->
  vREWRITE_TAC[vREAL_SUB_0] ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
  vASM_REWRITE_TAC[]);;

let%a vLIM_ADD = prove(
  [%q {|!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) + g(x)) --> (l + m))(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real] ---->
  vMATCH_MP_TAC vNET_ADD ----> vMATCH_ACCEPT_TAC vDORDER_TENDSTO);;

let%a vLIM_MUL = prove(
  [%q {|!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) * g(x)) --> (l * m))(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real] ---->
  vMATCH_MP_TAC vNET_MUL ----> vMATCH_ACCEPT_TAC vDORDER_TENDSTO);;

let%a vLIM_NEG = prove(
  [%q {|!f l. (f --> l)(x) <=> ((\x. --(f(x))) --> --l)(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real] ---->
  vMATCH_MP_TAC vNET_NEG ----> vMATCH_ACCEPT_TAC vDORDER_TENDSTO);;

let%a vLIM_INV = prove(
  [%q {|!f l. (f --> l)(x) /\ ~(l = &0) ==>
        ((\x. inv(f(x))) --> inv l)(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real] ---->
  vMATCH_MP_TAC vNET_INV ----> vMATCH_ACCEPT_TAC vDORDER_TENDSTO);;

let%a vLIM_SUB = prove(
  [%q {|!f g l m. (f --> l)(x) /\ (g --> m)(x) ==>
      ((\x. f(x) - g(x)) --> (l - m))(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real] ---->
  vMATCH_MP_TAC vNET_SUB ----> vMATCH_ACCEPT_TAC vDORDER_TENDSTO);;

let%a vLIM_DIV = prove(
  [%q {|!f g l m. (f --> l)(x) /\ (g --> m)(x) /\ ~(m = &0) ==>
      ((\x. f(x) / g(x)) --> (l / m))(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real] ---->
  vMATCH_MP_TAC vNET_DIV ----> vMATCH_ACCEPT_TAC vDORDER_TENDSTO);;

let%a vLIM_NULL = prove(
  [%q {|!f l x. (f --> l)(x) <=> ((\x. f(x) - l) --> &0)(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real] ---->
  vMATCH_ACCEPT_TAC vNET_NULL);;

let%a vLIM_SUM = prove
 ([%q {|!f l m n x.
      (!r. m <= r /\ r < m + n ==> (f r --> l r)(x))
      ==> ((\x. sum(m,n) (\r. f r x)) --> sum(m,n) l)(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real] ---->
  vMATCH_MP_TAC(vREWRITE_RULE[vRIGHT_IMP_FORALL_THM] vNET_SUM) ---->
  vREWRITE_TAC[vLIM_CONST; vDORDER_TENDSTO; vGSYM tends_real_real]);;

(*----------------------------------------------------------------------------*)
(* One extra theorem is handy                                                 *)
(*----------------------------------------------------------------------------*)

let%a vLIM_X = prove(
  [%q {|!x0. ((\x. x) --> x0)(x0)|} ],
  vGEN_TAC ----> vREWRITE_TAC[vLIM] ----> vX_GEN_TAC [%q {|e:real|} ] ---->
  vDISCH_TAC ----> vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vBETA_TAC ----> vGEN_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Uniqueness of limit                                                        *)
(*----------------------------------------------------------------------------*)

let%a vLIM_UNIQ = prove(
  [%q {|!f l m x. (f --> l)(x) /\ (f --> m)(x) ==> (l = m)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[tends_real_real] ---->
  vMATCH_MP_TAC vMTOP_TENDS_UNIQ ---->
  vMATCH_ACCEPT_TAC vDORDER_TENDSTO);;

(*----------------------------------------------------------------------------*)
(* Show that limits are equal when functions are equal except at limit point  *)
(*----------------------------------------------------------------------------*)

let%a vLIM_EQUAL = prove(
  [%q {|!f g l x0. (!x. ~(x = x0) ==> (f x = g x)) ==>
        ((f --> l)(x0) <=> (g --> l)(x0))|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLIM] ----> vDISCH_TAC ---->
  vAP_TERM_TAC ----> vABS_TAC ----> vAP_TERM_TAC ---->
  vAP_TERM_TAC ----> vABS_TAC ----> vAP_TERM_TAC ---->
  vAP_TERM_TAC ----> vABS_TAC ---->
  vONCE_REWRITE_TAC[vTAUT [%q {|(a ==> b <=> a ==> c) <=> a ==> (b <=> c)|} ]] ---->
  vDISCH_THEN(vASSUME_TAC -| vCONJUNCT1) ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vAP_TERM_TAC ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_SUB_0] ---->
  vASM_REWRITE_TAC[vABS_NZ]);;

(*----------------------------------------------------------------------------*)
(* A more general theorem about rearranging the body of a limit               *)
(*----------------------------------------------------------------------------*)

let%a vLIM_TRANSFORM = prove(
  [%q {|!f g x0 l. ((\x. f(x) - g(x)) --> &0)(x0) /\ (g --> l)(x0)
        ==> (f --> l)(x0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vLIM] ---->
  vDISCH_THEN((---->) (vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC) -| vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN (vMP_TAC -| vSPEC [%q {|e / &2|} ])) ---->
  vASM_REWRITE_TAC[vREAL_LT_HALF1] ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_SUB_RZERO] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|c:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|c:real|} ]; [%q {|d:real|} ]] vREAL_DOWN2) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|b:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|b:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|x:real|} ] ----> vDISCH_THEN vSTRIP_ASSUME_TAC ---->
  vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|(e / &2) + (e / &2)|} ] ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vONCE_DEPTH_CONV) [vREAL_HALF_DOUBLE] ---->
  vREWRITE_TAC[vREAL_LE_REFL] ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|abs(f(x:real) - g(x)) + abs(g(x) - l)|} ] ---->
  vSUBST1_TAC(vSYM(vSPECL
    [[%q {|(f:real->real) x|} ]; [%q {|(g:real->real) x|} ]; [%q {|l:real|} ]] vREAL_SUB_TRIANGLE)) ---->
  vREWRITE_TAC[vABS_TRIANGLE] ----> vMATCH_MP_TAC vREAL_LT_ADD2 ---->
  vCONJ_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|b:real|} ] ---->
  vASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Define differentiation and continuity                                      *)
(*----------------------------------------------------------------------------*)

let diffl = new_definition
  [%q {|(f diffl l)(x) <=> ((\h. (f(x+h) - f(x)) / h) --> l)(&0)|} ];;

let contl = new_definition
  [%q {|f contl x <=> ((\h. f(x + h)) --> f(x))(&0)|} ];;

let differentiable = new_definition
  [%q {|f differentiable x <=> ?l. (f diffl l)(x)|} ];;

(*----------------------------------------------------------------------------*)
(* Derivative is unique                                                       *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_UNIQ = prove(
  [%q {|!f l m x. (f diffl l)(x) /\ (f diffl m)(x) ==> (l = m)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[diffl] ---->
  vMATCH_ACCEPT_TAC vLIM_UNIQ);;

(*----------------------------------------------------------------------------*)
(* Differentiability implies continuity                                       *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_CONT = prove(
  [%q {|!f l x. (f diffl l)(x) ==> f contl x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[diffl; contl] ----> vDISCH_TAC ---->
  vREWRITE_TAC[tends_real_real] ----> vONCE_REWRITE_TAC[vNET_NULL] ---->
  vREWRITE_TAC[vGSYM tends_real_real] ----> vBETA_TAC ---->
  vSUBGOAL_THEN [%q {|((\h. f(x + h) - f(x)) --> &0)(&0) <=>
                ((\h. ((f(x + h) - f(x)) / h) * h) --> &0)(&0)|} ] vSUBST1_TAC
  ++-->
   [vMATCH_MP_TAC vLIM_EQUAL ---->
    vX_GEN_TAC [%q {|z:real|} ] ----> vBETA_TAC ---->
    vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_DIV_RMUL th]); vALL_TAC] ---->
  vGEN_REWRITE_TAC (vRATOR_CONV -| vLAND_CONV -| vABS_CONV -| vRAND_CONV)
    [vSYM(vBETA_CONV [%q {|(\h:real. h) h|} ])] ---->
  vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|h:real|} ] [%q {|(f(x + h) - f(x)) / h|} ]]) ---->
  vSUBST1_TAC(vSYM(vSPEC [%q {|l:real|} ] vREAL_MUL_RZERO)) ---->
  vMATCH_MP_TAC vLIM_MUL ----> vBETA_TAC ----> vREWRITE_TAC[vREAL_MUL_RZERO] ---->
  vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vLIM] ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_SUB_RZERO] ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ----> vEXISTS_TAC [%q {|e:real|} ] ---->
  vASM_REWRITE_TAC[] ----> vGEN_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Alternative definition of continuity                                       *)
(*----------------------------------------------------------------------------*)

let%a vCONTL_LIM = prove(
  [%q {|!f x. f contl x <=> (f --> f(x))(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[contl; vLIM] ---->
  vAP_TERM_TAC ----> vABS_TAC ---->
  vONCE_REWRITE_TAC[vTAUT [%q {|(a ==> b <=> a ==> c) <=> a ==> (b <=> c)|} ]] ---->
  vDISCH_TAC ----> vBETA_TAC ----> vREWRITE_TAC[vREAL_SUB_RZERO] ---->
  vEQ_TAC ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|k:real|} ] ++-->
   [vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ----> vREWRITE_TAC[vREAL_SUB_ADD2];
    vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[vREAL_ADD_SUB]]);;

(*----------------------------------------------------------------------------*)
(* Simple combining theorems for continuity                                   *)
(*----------------------------------------------------------------------------*)

let%a vCONT_X = prove
 ([%q {|!x. (\x. x) contl x|} ],
  vREWRITE_TAC[vCONTL_LIM; vLIM_X]);;

let%a vCONT_CONST = prove(
  [%q {|!x. (\x. k) contl x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vCONTL_LIM] ---->
  vMATCH_ACCEPT_TAC vLIM_CONST);;

let%a vCONT_ADD = prove(
  [%q {|!x. f contl x /\ g contl x ==> (\x. f(x) + g(x)) contl x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vCONTL_LIM] ----> vBETA_TAC ---->
  vMATCH_ACCEPT_TAC vLIM_ADD);;

let%a vCONT_MUL = prove(
  [%q {|!x. f contl x /\ g contl x ==> (\x. f(x) * g(x)) contl x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vCONTL_LIM] ----> vBETA_TAC ---->
  vMATCH_ACCEPT_TAC vLIM_MUL);;

let%a vCONT_NEG = prove(
  [%q {|!x. f contl x ==> (\x. --(f(x))) contl x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vCONTL_LIM] ----> vBETA_TAC ---->
  vREWRITE_TAC[vGSYM vLIM_NEG]);;

let%a vCONT_INV = prove(
  [%q {|!x. f contl x /\ ~(f x = &0) ==> (\x. inv(f(x))) contl x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vCONTL_LIM] ----> vBETA_TAC ---->
  vMATCH_ACCEPT_TAC vLIM_INV);;

let%a vCONT_SUB = prove(
  [%q {|!x. f contl x /\ g contl x ==> (\x. f(x) - g(x)) contl x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vCONTL_LIM] ----> vBETA_TAC ---->
  vMATCH_ACCEPT_TAC vLIM_SUB);;

let%a vCONT_DIV = prove(
  [%q {|!x. f contl x /\ g contl x /\ ~(g x = &0) ==>
        (\x. f(x) / g(x)) contl x|} ],
  vGEN_TAC ----> vREWRITE_TAC[vCONTL_LIM] ----> vBETA_TAC ---->
  vMATCH_ACCEPT_TAC vLIM_DIV);;

let%a vCONT_ABS = prove
 ([%q {|!f x. f contl x ==> (\x. abs(f x)) contl x|} ],
  vREWRITE_TAC[vCONTL_LIM; vLIM] ---->
  vMESON_TAC[vREAL_ARITH [%q {|abs(a - b) < e ==> abs(abs a - abs b) < e|} ]]);;

(* ------------------------------------------------------------------------- *)
(* Composition of continuous functions is continuous.                        *)
(* ------------------------------------------------------------------------- *)

let%a vCONT_COMPOSE = prove(
  [%q {|!f g x. f contl x /\ g contl (f x) ==> (\x. g(f x)) contl x|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[contl; vLIM; vREAL_SUB_RZERO] ---->
  vBETA_TAC ----> vDISCH_TAC ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_conj -| concl) ---->
  vDISCH_THEN(vCONJUNCTS_THEN vMP_TAC) ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vMATCH_MP th)) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|d:real|} ]) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|c:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|c:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|h:real|} ] ----> vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ---->
  vASM_CASES_TAC [%q {|&0 < abs(f(x + h) - f(x))|} ] ++-->
   [vUNDISCH_TAC [%q {|&0 < abs(f(x + h) - f(x))|} ] ---->
    vDISCH_THEN(fun th -> vDISCH_THEN(vMP_TAC -| vCONJ th)) ---->
    vDISCH_THEN(vANTE_RES_THEN vMP_TAC) ----> vREWRITE_TAC[vREAL_SUB_ADD2];
    vUNDISCH_TAC [%q {|~(&0 < abs(f(x + h) - f(x)))|} ] ---->
    vREWRITE_TAC[vGSYM vABS_NZ; vREAL_SUB_0] ----> vDISCH_THEN vSUBST1_TAC ---->
    vASM_REWRITE_TAC[vREAL_SUB_REFL; vABS_0]]);;

(*----------------------------------------------------------------------------*)
(* Intermediate Value Theorem (we prove contrapositive by bisection)          *)
(*----------------------------------------------------------------------------*)

let%a vIVT = prove(
  [%q {|!f a b y. a <= b /\
             (f(a) <= y /\ y <= f(b)) /\
             (!x. a <= x /\ x <= b ==> f contl x)
        ==> (?x. a <= x /\ x <= b /\ (f(x) = y))|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC
   (vCONJUNCTS_THEN2 vMP_TAC vSTRIP_ASSUME_TAC)) ---->
  vCONV_TAC vCONTRAPOS_CONV ---->
  vDISCH_THEN(vASSUME_TAC -| vCONV_RULE vNOT_EXISTS_CONV) ---->
  (vMP_TAC -| vC vSPEC vBOLZANO_LEMMA)
    [%q {|\(u,v). a <= u /\ u <= v /\ v <= b ==> ~(f(u) <= y /\ y <= f(v))|} ] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ---->
  vW(vC vSUBGOAL_THEN (fun t -> vREWRITE_TAC[t]) -|
  funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vALL_TAC;
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ]]) ---->
    vASM_REWRITE_TAC[vREAL_LE_REFL]] ---->
  vCONJ_TAC ++-->
   [vMAP_EVERY vX_GEN_TAC [[%q {|u:real|} ]; [%q {|v:real|} ]; [%q {|w:real|} ]] ---->
    vCONV_TAC vCONTRAPOS_CONV ----> vREWRITE_TAC[vDE_MORGAN_THM; vNOT_IMP] ---->
    vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
    vMAP_EVERY vASM_CASES_TAC [[%q {|u <= v|} ]; [%q {|v <= w|} ]] ----> vASM_REWRITE_TAC[] ---->
    vDISJ_CASES_TAC(vSPECL [[%q {|y:real|} ]; [%q {|(f:real->real) v|} ]] vREAL_LE_TOTAL) ---->
    vASM_REWRITE_TAC[] ++--> [vDISJ1_TAC; vDISJ2_TAC] ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ++-->
     [vEXISTS_TAC [%q {|w:real|} ]; vEXISTS_TAC [%q {|u:real|} ]] ----> vASM_REWRITE_TAC[];
    vALL_TAC] ---->
  vX_GEN_TAC [%q {|x:real|} ] ----> vASM_CASES_TAC [%q {|a <= x /\ x <= b|} ] ++-->
   [vALL_TAC;
    vEXISTS_TAC [%q {|&1|} ] ----> vREWRITE_TAC[vREAL_LT_01] ---->
    vMAP_EVERY vX_GEN_TAC [[%q {|u:real|} ]; [%q {|v:real|} ]] ---->
    vREPEAT vSTRIP_TAC ----> vUNDISCH_TAC [%q {|~(a <= x /\ x <= b)|} ] ---->
    vREWRITE_TAC[] ----> vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ++-->
     [vEXISTS_TAC [%q {|u:real|} ]; vEXISTS_TAC [%q {|v:real|} ]] ---->
    vASM_REWRITE_TAC[]] ---->
  vUNDISCH_TAC [%q {|!x. ~(a <= x /\ x <= b /\ (f(x) = (y:real)))|} ] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x:real|} ]) ----> vASM_REWRITE_TAC[] ----> vDISCH_TAC ---->
  vUNDISCH_TAC [%q {|!x. a <= x /\ x <= b ==> f contl x|} ] ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vMATCH_MP th)) ---->
  vREWRITE_TAC[contl; vLIM] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|abs(y - f(x:real))|} ]) ---->
  vGEN_REWRITE_TAC (funpow 2 vLAND_CONV) [vGSYM vABS_NZ] ---->
  vREWRITE_TAC[vREAL_SUB_0; vREAL_SUB_RZERO] ----> vBETA_TAC ---->
  vASSUM_LIST(fun thl -> vREWRITE_TAC(map vGSYM thl)) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|u:real|} ]; [%q {|v:real|} ]] ---->
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|(f:real->real) x|} ]; [%q {|y:real|} ]] vREAL_LT_TOTAL) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN vDISJ_CASES_TAC ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ++-->
   [vDISCH_THEN(vMP_TAC -| vSPEC [%q {|v - x|} ]) ----> vREWRITE_TAC[vNOT_IMP] ---->
    vREPEAT vCONJ_TAC ++-->
     [vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE; vREAL_SUB_LT] ---->
      vASM_REWRITE_TAC[vREAL_LT_LE] ----> vDISCH_THEN vSUBST_ALL_TAC ---->
      vUNDISCH_TAC [%q {|f(v:real) < y|} ] ----> vASM_REWRITE_TAC[vGSYM vREAL_NOT_LE];
      vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|v - u|} ] ---->
      vASM_REWRITE_TAC[real_sub; vREAL_LE_LADD; vREAL_LE_NEG2; vREAL_LE_RADD];
      vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vREWRITE_TAC[vREAL_SUB_ADD] ---->
      vREWRITE_TAC[vREAL_NOT_LT; real_abs; vREAL_SUB_LE] ---->
      vSUBGOAL_THEN [%q {|f(x:real) <= y|} ] vASSUME_TAC ++-->
       [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vFIRST_ASSUM vACCEPT_TAC; vALL_TAC] ---->
      vSUBGOAL_THEN [%q {|f(x:real) <= f(v)|} ] vASSUME_TAC ++-->
       [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|y:real|} ]; vALL_TAC] ---->
      vASM_REWRITE_TAC[real_sub; vREAL_LE_RADD]];
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|u - x|} ]) ----> vREWRITE_TAC[vNOT_IMP] ---->
    vREPEAT vCONJ_TAC ++-->
     [vONCE_REWRITE_TAC[vABS_SUB] ---->
      vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE; vREAL_SUB_LT] ---->
      vASM_REWRITE_TAC[vREAL_LT_LE] ----> vDISCH_THEN vSUBST_ALL_TAC ---->
      vUNDISCH_TAC [%q {|y < f(x:real)|} ] ----> vASM_REWRITE_TAC[vGSYM vREAL_NOT_LE];
      vONCE_REWRITE_TAC[vABS_SUB] ----> vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|v - u|} ] ---->
      vASM_REWRITE_TAC[real_sub; vREAL_LE_LADD; vREAL_LE_NEG2; vREAL_LE_RADD];
      vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vREWRITE_TAC[vREAL_SUB_ADD] ---->
      vREWRITE_TAC[vREAL_NOT_LT; real_abs; vREAL_SUB_LE] ---->
      vSUBGOAL_THEN [%q {|f(u:real) < f(x)|} ] vASSUME_TAC ++-->
       [vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|y:real|} ] ---->
        vASM_REWRITE_TAC[]; vALL_TAC] ---->
      vASM_REWRITE_TAC[vGSYM vREAL_NOT_LT] ---->
      vASM_REWRITE_TAC[vREAL_NOT_LT; vREAL_LE_NEG2; real_sub; vREAL_LE_RADD]]]);;

(*----------------------------------------------------------------------------*)
(* Intermediate value theorem where value at the left end is bigger           *)
(*----------------------------------------------------------------------------*)

let%a vIVT2 = prove(
  [%q {|!f a b y. (a <= b) /\ (f(b) <= y /\ y <= f(a)) /\
             (!x. a <= x /\ x <= b ==> f contl x) ==>
        ?x. a <= x /\ x <= b /\ (f(x) = y)|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|\x:real. --(f x)|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|--y|} ]] vIVT) ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[vREAL_LE_NEG2; vREAL_NEG_EQ; vREAL_NEG_NEG] ---->
  vDISCH_THEN vMATCH_MP_TAC ----> vGEN_TAC ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vCONT_NEG ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Prove the simple combining theorems for differentiation                    *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_CONST = prove(
  [%q {|!k x. ((\x. k) diffl &0)(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[diffl] ---->
  vREWRITE_TAC[vREAL_SUB_REFL; real_div; vREAL_MUL_LZERO] ---->
  vMATCH_ACCEPT_TAC vLIM_CONST);;

let%a vDIFF_ADD = prove(
  [%q {|!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) + g(x)) diffl (l + m))(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[diffl] ---->
  vDISCH_TAC ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_ADD2_SUB2] ---->
  vREWRITE_TAC[real_div; vREAL_RDISTRIB] ---->
  vREWRITE_TAC[vGSYM real_div] ---->
  vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|h:real|} ] [%q {|(f(x + h) - f(x)) / h|} ]]) ---->
  vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|h:real|} ] [%q {|(g(x + h) - g(x)) / h|} ]]) ---->
  vMATCH_MP_TAC vLIM_ADD ----> vASM_REWRITE_TAC[]);;

let%a vDIFF_MUL = prove(
  [%q {|!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                  ((\x. f(x) * g(x)) diffl ((l * g(x)) + (m * f(x))))(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[diffl] ---->
  vDISCH_TAC ----> vBETA_TAC ----> vSUBGOAL_THEN
    [%q {|!a b c d. (a * b) - (c * d) = ((a * b) - (a * d)) + ((a * d) - (c * d))|} ]
  (fun th -> vONCE_REWRITE_TAC[vGEN_ALL th]) ++-->
   [vREWRITE_TAC[real_sub] ---->
    vONCE_REWRITE_TAC[vAC vREAL_ADD_AC
      [%q {|(a + b) + (c + d) = (b + c) + (a + d)|} ]] ---->
    vREWRITE_TAC[vREAL_ADD_LINV; vREAL_ADD_LID]; vALL_TAC] ---->
  vREWRITE_TAC[vGSYM vREAL_SUB_LDISTRIB; vGSYM vREAL_SUB_RDISTRIB] ----> vSUBGOAL_THEN
    [%q {|!a b c d e. ((a * b) + (c * d)) / e = ((b / e) * a) + ((c / e) * d)|} ]
    (fun th -> vONCE_REWRITE_TAC[th]) ++-->
   [vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_div] ---->
    vREWRITE_TAC[vREAL_RDISTRIB] ----> vBINOP_TAC ---->
    vREWRITE_TAC[vREAL_MUL_AC]; vALL_TAC] ---->
  vGEN_REWRITE_TAC vLAND_CONV [vREAL_ADD_SYM] ---->
  vCONV_TAC(vEXACT_CONV(map (vX_BETA_CONV [%q {|h:real|} ])
    [[%q {|((g(x + h) - g(x)) / h) * f(x + h)|} ];
     [%q {|((f(x + h) - f(x)) / h) * g(x)|} ]])) ---->
  vMATCH_MP_TAC vLIM_ADD ---->
  vCONV_TAC(vEXACT_CONV(map (vX_BETA_CONV [%q {|h:real|} ])
    [[%q {|(g(x + h) - g(x)) / h|} ]; [%q {|f(x + h):real|} ];
     [%q {|(f(x + h) - f(x)) / h|} ]; [%q {|g(x:real):real|} ]])) ---->
  vCONJ_TAC ----> vMATCH_MP_TAC vLIM_MUL ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[vLIM_CONST] ---->
  vREWRITE_TAC[vGSYM contl] ---->
  vMATCH_MP_TAC vDIFF_CONT ----> vEXISTS_TAC [%q {|l:real|} ] ---->
  vASM_REWRITE_TAC[diffl]);;

let%a vDIFF_CMUL = prove(
  [%q {|!f c l x. (f diffl l)(x) ==> ((\x. c * f(x)) diffl (c * l))(x)|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vCONJ (vSPECL [[%q {|c:real|} ]; [%q {|x:real|} ]] vDIFF_CONST)) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_MUL) ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_MUL_LZERO; vREAL_ADD_LID] ---->
  vMATCH_MP_TAC(vTAUT([%q {|(a <=> b) ==> a ==> b|} ])) ----> vAP_THM_TAC ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vREAL_MUL_SYM] ---->
  vREWRITE_TAC[]);;

let%a vDIFF_NEG = prove(
  [%q {|!f l x. (f diffl l)(x) ==> ((\x. --(f x)) diffl --l)(x)|} ],
  vREPEAT vGEN_TAC ----> vONCE_REWRITE_TAC[vREAL_NEG_MINUS1] ---->
  vMATCH_ACCEPT_TAC vDIFF_CMUL);;

let%a vDIFF_SUB = prove(
  [%q {|!f g l m x. (f diffl l)(x) /\ (g diffl m)(x) ==>
                   ((\x. f(x) - g(x)) diffl (l - m))(x)|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_ADD -| (uncurry vCONJ) -|
              (vI $-$ vMATCH_MP vDIFF_NEG) -| vCONJ_PAIR) ---->
  vBETA_TAC ----> vREWRITE_TAC[real_sub]);;

(* ------------------------------------------------------------------------- *)
(* Carathe'odory definition makes the chain rule proof much easier.          *)
(* ------------------------------------------------------------------------- *)

let%a vDIFF_CARAT = prove(
  [%q {|!f l x. (f diffl l)(x) <=>
      ?g. (!z. f(z) - f(x) = g(z) * (z - x)) /\ g contl x /\ (g(x) = l)|} ],
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ++-->
   [vEXISTS_TAC [%q {|\z. if z = x then l else (f(z) - f(x)) / (z - x)|} ] ---->
    vBETA_TAC ----> vREWRITE_TAC[] ----> vCONJ_TAC ++-->
     [vX_GEN_TAC [%q {|z:real|} ] ----> vCOND_CASES_TAC ---->
      vASM_REWRITE_TAC[vREAL_SUB_REFL; vREAL_MUL_RZERO] ---->
      vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_RMUL ---->
      vASM_REWRITE_TAC[vREAL_SUB_0];
      vPOP_ASSUM vMP_TAC ----> vMATCH_MP_TAC vEQ_IMP ---->
      vREWRITE_TAC[diffl; contl] ----> vBETA_TAC ----> vREWRITE_TAC[] ---->
      vMATCH_MP_TAC vLIM_EQUAL ----> vGEN_TAC ----> vDISCH_TAC ----> vBETA_TAC ---->
      vASM_REWRITE_TAC[vREAL_ADD_RID_UNIQ; vREAL_ADD_SUB]];
    vPOP_ASSUM(vX_CHOOSE_THEN [%q {|g:real->real|} ] vSTRIP_ASSUME_TAC) ---->
    vFIRST_ASSUM(vUNDISCH_TAC -| check is_eq -| concl) ---->
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vUNDISCH_TAC [%q {|g contl x|} ] ---->
    vASM_REWRITE_TAC[contl; diffl; vREAL_ADD_SUB] ---->
    vMATCH_MP_TAC vEQ_IMP ---->
    vMATCH_MP_TAC vLIM_EQUAL ----> vGEN_TAC ----> vDISCH_TAC ----> vBETA_TAC ---->
    vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC] ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_RINV th]) ---->
    vREWRITE_TAC[vREAL_MUL_RID]]);;

(*----------------------------------------------------------------------------*)
(* Now the chain rule                                                         *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_CHAIN = prove(
  [%q {|!f g l m x.
     (f diffl l)(g x) /\ (g diffl m)(x) ==> ((\x. f(g x)) diffl (l * m))(x)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN vMP_TAC) ---->
  vDISCH_THEN(fun th -> vMP_TAC th ----> vASSUME_TAC(vMATCH_MP vDIFF_CONT th)) ---->
  vREWRITE_TAC[vDIFF_CARAT] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|g':real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|f':real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC
   [%q {|\z. if z = x then l * m else (f(g(z):real) - f(g(x))) / (z - x)|} ] ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[] ----> vCONJ_TAC ++-->
   [vGEN_TAC ----> vCOND_CASES_TAC ---->
    vASM_REWRITE_TAC[vREAL_SUB_REFL; vREAL_MUL_RZERO] ---->
    vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_RMUL ---->
    vASM_REWRITE_TAC[vREAL_SUB_0];
    vMP_TAC(vCONJ (vASSUME [%q {|g contl x|} ]) (vASSUME [%q {|f' contl (g(x:real))|} ])) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vCONT_COMPOSE) ---->
    vDISCH_THEN(vMP_TAC -| vC vCONJ (vASSUME [%q {|g' contl x|} ])) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vCONT_MUL) ----> vBETA_TAC ---->
    vASM_REWRITE_TAC[contl] ----> vBETA_TAC ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vEQ_IMP ---->
    vMATCH_MP_TAC vLIM_EQUAL ----> vX_GEN_TAC [%q {|z:real|} ] ---->
    vDISCH_TAC ----> vBETA_TAC ----> vASM_REWRITE_TAC[vREAL_ADD_RID_UNIQ] ---->
    vREWRITE_TAC[real_div; vGSYM vREAL_MUL_ASSOC; vREAL_ADD_SUB] ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_RINV th]) ---->
    vREWRITE_TAC[vREAL_MUL_RID]]);;

(*----------------------------------------------------------------------------*)
(* Differentiation of natural number powers                                   *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_X = prove(
  [%q {|!x. ((\x. x) diffl &1)(x)|} ],
  vGEN_TAC ----> vREWRITE_TAC[diffl] ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_ADD_SUB] ----> vREWRITE_TAC[vLIM; vREAL_SUB_RZERO] ---->
  vBETA_TAC ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vEXISTS_TAC [%q {|&1|} ] ----> vREWRITE_TAC[vREAL_LT_01] ---->
  vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vCONJUNCT1) ---->
  vREWRITE_TAC[vGSYM vABS_NZ] ---->
  vDISCH_THEN(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_DIV_REFL th]) ---->
  vASM_REWRITE_TAC[vREAL_SUB_REFL; vABS_0]);;

let%a vDIFF_POW = prove(
  [%q {|!n x. ((\x. x pow n) diffl (&n * (x pow (n - 1))))(x)|} ],
  vINDUCT_TAC ----> vREWRITE_TAC[pow; vDIFF_CONST; vREAL_MUL_LZERO] ---->
  vX_GEN_TAC [%q {|x:real|} ] ---->
  vPOP_ASSUM(vMP_TAC -| vCONJ(vSPEC [%q {|x:real|} ] vDIFF_X) -| vSPEC [%q {|x:real|} ]) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_MUL) ----> vBETA_TAC ---->
  vMATCH_MP_TAC vEQ_IMP ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vREWRITE_TAC[vREAL_MUL_LID] ---->
  vREWRITE_TAC[vREAL; vREAL_RDISTRIB; vREAL_MUL_LID] ---->
  vGEN_REWRITE_TAC vRAND_CONV [vREAL_ADD_SYM] ----> vBINOP_TAC ++-->
   [vREWRITE_TAC[vADD1; vADD_SUB];
    vSTRUCT_CASES_TAC (vSPEC [%q {|n:num|} ] num_CASES) ---->
    vREWRITE_TAC[vREAL_MUL_LZERO] ---->
    vREWRITE_TAC[vADD1; vADD_SUB; vPOW_ADD] ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[num_CONV [%q {|1|} ]; pow] ---->
    vREWRITE_TAC[vSYM(num_CONV [%q {|1|} ]); vREAL_MUL_RID]]);;

(*----------------------------------------------------------------------------*)
(* Now power of -1 (then differentiation of inverses follows from chain rule) *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_XM1 = prove(
  [%q {|!x. ~(x = &0) ==> ((\x. inv(x)) diffl (--(inv(x) pow 2)))(x)|} ],
  vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[diffl] ----> vBETA_TAC ---->
  vMATCH_MP_TAC vLIM_TRANSFORM ---->
  vEXISTS_TAC [%q {|\h. --(inv(x + h) * inv(x))|} ] ---->
  vBETA_TAC ----> vCONJ_TAC ++-->
   [vREWRITE_TAC[vLIM] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
    vEXISTS_TAC [%q {|abs(x)|} ] ---->
    vEVERY_ASSUM(fun th -> vREWRITE_TAC[vREWRITE_RULE[vABS_NZ] th]) ---->
    vX_GEN_TAC [%q {|h:real|} ] ----> vREWRITE_TAC[vREAL_SUB_RZERO] ---->
    vDISCH_THEN vSTRIP_ASSUME_TAC ----> vBETA_TAC ---->
    vW(vC vSUBGOAL_THEN vSUBST1_TAC -| vC (curry mk_eq) [%q {|&0|} ] -|
      rand -| rator -| snd) ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vABS_ZERO; vREAL_SUB_0] ---->
    vSUBGOAL_THEN [%q {|~(x + h = &0)|} ] vASSUME_TAC ++-->
     [vREWRITE_TAC[vREAL_LNEG_UNIQ] ----> vDISCH_THEN vSUBST_ALL_TAC ---->
      vUNDISCH_TAC [%q {|abs(h) < abs(--h)|} ] ---->
      vREWRITE_TAC[vABS_NEG; vREAL_LT_REFL]; vALL_TAC] ---->
    vW(fun (asl,w) -> vMP_TAC
        (vSPECL [[%q {|x * (x + h)|} ]; lhs w; rhs w] vREAL_EQ_LMUL)) ---->
    vASM_REWRITE_TAC[vREAL_ENTIRE] ----> vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
    vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL] ---->
    vREWRITE_TAC[real_div; vREAL_SUB_LDISTRIB; vREAL_SUB_RDISTRIB] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
      [%q {|(a * b) * (c * d) = (c * b) * (d * a)|} ]] ---->
    vREWRITE_TAC(map (vMATCH_MP vREAL_MUL_LINV -| vASSUME)
     [[%q {|~(x = &0)|} ]; [%q {|~(x + h = &0)|} ]]) ----> vREWRITE_TAC[vREAL_MUL_LID] ---->
    vONCE_REWRITE_TAC[vAC vREAL_MUL_AC
      [%q {|(a * b) * (c * d) = (a * d) * (c * b)|} ]] ---->
    vREWRITE_TAC[vMATCH_MP vREAL_MUL_LINV (vASSUME [%q {|~(x = &0)|} ])] ---->
    vREWRITE_TAC[vREAL_MUL_LID; vGSYM vREAL_SUB_LDISTRIB] ---->
    vREWRITE_TAC[vREWRITE_RULE[vREAL_NEG_SUB]
      (vAP_TERM [%q {|(--)|} ] (vSPEC_ALL vREAL_ADD_SUB))] ---->
    vREWRITE_TAC[vGSYM vREAL_NEG_RMUL] ----> vAP_TERM_TAC ---->
    vMATCH_MP_TAC vREAL_MUL_LINV ----> vASM_REWRITE_TAC[vABS_NZ];

    vREWRITE_TAC[vPOW_2] ---->
    vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|h:real|} ] [%q {|inv(x + h) * inv(x)|} ]]) ---->
    vREWRITE_TAC[vGSYM vLIM_NEG] ---->
    vCONV_TAC(vEXACT_CONV(map (vX_BETA_CONV [%q {|h:real|} ]) [[%q {|inv(x + h)|} ]; [%q {|inv(x)|} ]]))
    ----> vMATCH_MP_TAC vLIM_MUL ----> vBETA_TAC ---->
    vREWRITE_TAC[vLIM_CONST] ---->
    vCONV_TAC(vEXACT_CONV[vX_BETA_CONV [%q {|h:real|} ] [%q {|x + h|} ]]) ---->
    vMATCH_MP_TAC vLIM_INV ----> vASM_REWRITE_TAC[] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_ADD_RID] ---->
    vCONV_TAC(vEXACT_CONV(map (vX_BETA_CONV [%q {|h:real|} ]) [[%q {|x:real|} ]; [%q {|h:real|} ]])) ---->
    vMATCH_MP_TAC vLIM_ADD ----> vBETA_TAC ----> vREWRITE_TAC[vLIM_CONST] ---->
    vMATCH_ACCEPT_TAC vLIM_X]);;

(*----------------------------------------------------------------------------*)
(* Now differentiation of inverse and quotient                                *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_INV = prove(
  [%q {|!f l x. (f diffl l)(x) /\ ~(f(x) = &0) ==>
        ((\x. inv(f x)) diffl --(l / (f(x) pow 2)))(x)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_div; vREAL_NEG_RMUL] ---->
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ----> vDISCH_TAC ---->
  vMATCH_MP_TAC vDIFF_CHAIN ----> vASM_REWRITE_TAC[] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vPOW_INV (vCONJUNCT2 th)]) ---->
  vMATCH_MP_TAC(vCONV_RULE(vONCE_DEPTH_CONV vETA_CONV) vDIFF_XM1) ---->
  vASM_REWRITE_TAC[]);;

let%a vDIFF_DIV = prove(
  [%q {|!f g l m. (f diffl l)(x) /\ (g diffl m)(x) /\ ~(g(x) = &0) ==>
    ((\x. f(x) / g(x)) diffl (((l * g(x)) - (m * f(x))) / (g(x) pow 2)))(x)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN vSTRIP_ASSUME_TAC ---->
  vREWRITE_TAC[real_div] ---->
  vMP_TAC(vSPECL [[%q {|g:real->real|} ]; [%q {|m:real|} ]; [%q {|x:real|} ]] vDIFF_INV) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vMP_TAC -| vCONJ(vASSUME [%q {|(f diffl l)(x)|} ])) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_MUL) ----> vBETA_TAC ---->
  vW(vC vSUBGOAL_THEN vSUBST1_TAC -| mk_eq -|
      ((rand -| rator) $-$ (rand -| rator)) -| dest_imp -| snd) ---->
  vREWRITE_TAC[] ----> vREWRITE_TAC[real_sub] ---->
  vREWRITE_TAC[vREAL_LDISTRIB; vREAL_RDISTRIB] ----> vBINOP_TAC ++-->
   [vREWRITE_TAC[vGSYM vREAL_MUL_ASSOC] ----> vAP_TERM_TAC ---->
    vREWRITE_TAC[vPOW_2] ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_INV_MUL_WEAK (vW vCONJ th)]) ---->
    vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
    vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_MUL_RINV th]) ---->
    vREWRITE_TAC[vREAL_MUL_LID];
    vREWRITE_TAC[real_div; vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL] ---->
    vAP_TERM_TAC ----> vREWRITE_TAC[vREAL_MUL_AC]]);;

(*----------------------------------------------------------------------------*)
(* Differentiation of finite sum                                              *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_SUM = prove(
  [%q {|!f f' m n x. (!r. m <= r /\ r < (m + n)
                 ==> ((\x. f r x) diffl (f' r x))(x))
     ==> ((\x. sum(m,n)(\n. f n x)) diffl (sum(m,n) (\r. f' r x)))(x)|} ],
  vREPEAT vGEN_TAC ----> vSPEC_TAC([%q {|n:num|} ],[%q {|n:num|} ]) ---->
  vINDUCT_TAC ----> vREWRITE_TAC[sum; vDIFF_CONST] ----> vDISCH_TAC ---->
  vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ----> vMATCH_MP_TAC vDIFF_ADD ---->
  vBETA_TAC ----> vCONJ_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vLT_TRANS ---->
    vEXISTS_TAC [%q {|m + n:num|} ] ----> vASM_REWRITE_TAC[vADD_CLAUSES; vLESS_SUC_REFL];
    vREWRITE_TAC[vLE_ADD; vADD_CLAUSES; vLESS_SUC_REFL]]);;

(*----------------------------------------------------------------------------*)
(* By bisection, function continuous on closed interval is bounded above      *)
(*----------------------------------------------------------------------------*)

let%a vCONT_BOUNDED = prove(
  [%q {|!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. !x. a <= x /\ x <= b ==> f(x) <= M|} ],
  vREPEAT vSTRIP_TAC ---->
  (vMP_TAC -| vC vSPEC vBOLZANO_LEMMA)
    [%q {|\(u,v). a <= u /\ u <= v /\ v <= b ==>
               ?M. !x. u <= x /\ x <= v ==> f x <= M|} ] ---->
  vCONV_TAC(vONCE_DEPTH_CONV vGEN_BETA_CONV) ---->
  vW(vC vSUBGOAL_THEN (fun t -> vREWRITE_TAC[t]) -|
  funpow 2(fst -| dest_imp) -| snd) ++-->
   [vALL_TAC;
    vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ]]) ---->
    vASM_REWRITE_TAC[vREAL_LE_REFL]] ---->
  vCONJ_TAC ++-->
   [vMAP_EVERY vX_GEN_TAC [[%q {|u:real|} ]; [%q {|v:real|} ]; [%q {|w:real|} ]] ---->
    vDISCH_THEN(vREPEAT_TCL vCONJUNCTS_THEN vASSUME_TAC) ---->
    vDISCH_TAC ---->
    vREPEAT(vFIRST_ASSUM(vUNDISCH_TAC -| check is_imp -| concl)) ---->
    vASM_REWRITE_TAC[] ---->
    vSUBGOAL_THEN [%q {|v <= b|} ] vASSUME_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|w:real|} ] ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|a <= v|} ] vASSUME_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|u:real|} ] ---->
      vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|M1:real|} ]) ---->
    vDISCH_THEN(vX_CHOOSE_TAC [%q {|M2:real|} ]) ---->
    vDISJ_CASES_TAC(vSPECL [[%q {|M1:real|} ]; [%q {|M2:real|} ]] vREAL_LE_TOTAL) ++-->
     [vEXISTS_TAC [%q {|M2:real|} ] ----> vX_GEN_TAC [%q {|x:real|} ] ----> vSTRIP_TAC ---->
      vDISJ_CASES_TAC(vSPECL [[%q {|x:real|} ]; [%q {|v:real|} ]] vREAL_LE_TOTAL) ++-->
       [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|M1:real|} ] ---->
        vASM_REWRITE_TAC[]; vALL_TAC] ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
      vEXISTS_TAC [%q {|M1:real|} ] ----> vX_GEN_TAC [%q {|x:real|} ] ----> vSTRIP_TAC ---->
      vDISJ_CASES_TAC(vSPECL [[%q {|x:real|} ]; [%q {|v:real|} ]] vREAL_LE_TOTAL) ++-->
       [vALL_TAC; vMATCH_MP_TAC vREAL_LE_TRANS ---->
        vEXISTS_TAC [%q {|M2:real|} ] ----> vASM_REWRITE_TAC[]] ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]];
    vALL_TAC] ---->
  vX_GEN_TAC [%q {|x:real|} ] ----> vASM_CASES_TAC [%q {|a <= x /\ x <= b|} ] ++-->
   [vALL_TAC;
    vEXISTS_TAC [%q {|&1|} ] ----> vREWRITE_TAC[vREAL_LT_01] ---->
    vMAP_EVERY vX_GEN_TAC [[%q {|u:real|} ]; [%q {|v:real|} ]] ---->
    vREPEAT vSTRIP_TAC ----> vUNDISCH_TAC [%q {|~(a <= x /\ x <= b)|} ] ---->
    vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_THEN(vK vALL_TAC) ---->
    vREWRITE_TAC[] ----> vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ++-->
     [vEXISTS_TAC [%q {|u:real|} ]; vEXISTS_TAC [%q {|v:real|} ]] ---->
    vASM_REWRITE_TAC[]] ---->
  vUNDISCH_TAC [%q {|!x. a <= x /\ x <= b ==> f contl x|} ] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x:real|} ]) ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[contl; vLIM] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|&1|} ]) ----> vREWRITE_TAC[vREAL_LT_01] ---->
  vASM_REWRITE_TAC[vREAL_SUB_RZERO] ----> vBETA_TAC ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|u:real|} ]; [%q {|v:real|} ]] ----> vREPEAT vSTRIP_TAC ---->
  vEXISTS_TAC [%q {|abs(f(x:real)) + &1|} ] ---->
  vX_GEN_TAC [%q {|z:real|} ] ----> vSTRIP_TAC ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|z - x|} ]) ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vONCE_DEPTH_CONV) [vREAL_ADD_SYM] ---->
  vREWRITE_TAC[vREAL_SUB_ADD] ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|f(z:real) - f(x)|} ]; [%q {|(f:real->real) x|} ]] vABS_TRIANGLE) ---->
  vREWRITE_TAC[vREAL_SUB_ADD] ---->
  vDISCH_THEN(vASSUME_TAC -| vONCE_REWRITE_RULE[vREAL_ADD_SYM]) ---->
  vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|abs(f(z:real))|} ] ---->
  vREWRITE_TAC[vABS_LE] ----> vMATCH_MP_TAC vREAL_LE_TRANS ---->
  vEXISTS_TAC [%q {|abs(f(x:real)) + (abs(f(z) - f(x)))|} ] ---->
  vASM_REWRITE_TAC[vREAL_LE_LADD] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
  vASM_CASES_TAC [%q {|z:real = x|} ] ++-->
   [vASM_REWRITE_TAC[vREAL_SUB_REFL; vABS_0; vREAL_LT_01];
    vFIRST_ASSUM vMATCH_MP_TAC ----> vREWRITE_TAC[vGSYM vABS_NZ] ---->
    vASM_REWRITE_TAC[vREAL_SUB_0; real_abs; vREAL_SUB_LE] ---->
    vREWRITE_TAC[vREAL_NEG_SUB] ----> vCOND_CASES_TAC ---->
    vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|v - u|} ] ---->
    vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LE_TRANS ++-->
     [vEXISTS_TAC [%q {|v - x|} ]; vEXISTS_TAC [%q {|v - z|} ]] ---->
    vASM_REWRITE_TAC[real_sub; vREAL_LE_RADD; vREAL_LE_LADD; vREAL_LE_NEG2]]);;

let%a vCONT_BOUNDED_ABS = prove
 ([%q {|!f a b. (!x. a <= x /\ x <= b ==> f contl x)
           ==> ?M. !x. a <= x /\ x <= b ==> abs(f(x)) <= M|} ],
  vREPEAT vSTRIP_TAC ---->
  vASM_CASES_TAC [%q {|a <= b|} ] ++-->
   [vALL_TAC;
    vASM_SIMP_TAC[vREAL_ARITH [%q {|~(a <= b) ==> ~(a <= x /\ x <= b)|} ]]] ---->
  vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]] vCONT_BOUNDED) ---->
  vMP_TAC(vSPECL [[%q {|\x:real. --(f x)|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]] vCONT_BOUNDED) ---->
  vASM_SIMP_TAC[vCONT_NEG] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|M1:real|} ]) ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|M2:real|} ]) ---->
  vEXISTS_TAC [%q {|abs(M1) + abs(M2)|} ] ---->
  vASM_SIMP_TAC[vREAL_ARITH
   [%q {|x <= m1 /\ --x <= m2 ==> abs(x) <= abs(m2) + abs(m1)|} ]]);;

(*----------------------------------------------------------------------------*)
(* Refine the above to existence of least upper bound                         *)
(*----------------------------------------------------------------------------*)

let%a vCONT_HASSUP = prove(
  [%q {|!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (!N. N < M ==> ?x. a <= x /\ x <= b /\ N < f(x))|} ],
  let tm = [%q {|\y:real. ?x. a <= x /\ x <= b /\ (y = f(x))|} ] in
  vREPEAT vGEN_TAC ----> vDISCH_TAC ----> vMP_TAC(vSPEC tm vREAL_SUP_LE) ---->
  vBETA_TAC ---->
  vW(vC vSUBGOAL_THEN (fun t -> vREWRITE_TAC[t]) -| funpow 2 (fst -| dest_imp) -| snd)
  ++-->
   [vCONJ_TAC ++-->
     [vMAP_EVERY vEXISTS_TAC [[%q {|(f:real->real) a|} ]; [%q {|a:real|} ]] ---->
      vASM_REWRITE_TAC[vREAL_LE_REFL; vREAL_LE_LT];
      vPOP_ASSUM(vX_CHOOSE_TAC [%q {|M:real|} ] -| vMATCH_MP vCONT_BOUNDED) ---->
      vEXISTS_TAC [%q {|M:real|} ] ----> vX_GEN_TAC [%q {|y:real|} ] ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vMP_TAC) ---->
      vREWRITE_TAC[vCONJ_ASSOC] ---->
      vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vSUBST1_TAC) ---->
      vPOP_ASSUM vMATCH_ACCEPT_TAC];
    vDISCH_TAC ----> vEXISTS_TAC (mk_comb([%q {|sup|} ],tm)) ----> vCONJ_TAC ++-->
     [vX_GEN_TAC [%q {|x:real|} ] ----> vDISCH_TAC ---->
      vFIRST_ASSUM(vMP_TAC -| vSPEC (mk_comb([%q {|sup|} ],tm))) ---->
      vREWRITE_TAC[vREAL_LT_REFL] ---->
      vCONV_TAC(vONCE_DEPTH_CONV vNOT_EXISTS_CONV) ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|(f:real->real) x|} ]) ---->
      vREWRITE_TAC[vDE_MORGAN_THM; vREAL_NOT_LT] ---->
      vCONV_TAC(vONCE_DEPTH_CONV vNOT_EXISTS_CONV) ---->
      vDISCH_THEN(vDISJ_CASES_THEN vMP_TAC) ----> vREWRITE_TAC[] ---->
      vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x:real|} ]) ----> vASM_REWRITE_TAC[];
      vGEN_TAC ----> vFIRST_ASSUM(vSUBST1_TAC -| vSYM -| vSPEC [%q {|N:real|} ]) ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|y:real|} ] vMP_TAC) ---->
      vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vMP_TAC) ---->
      vREWRITE_TAC[vCONJ_ASSOC] ---->
      vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vSUBST_ALL_TAC) ---->
      vDISCH_TAC ----> vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[]]]);;

(*----------------------------------------------------------------------------*)
(* Now show that it attains its upper bound                                   *)
(*----------------------------------------------------------------------------*)

let%a vCONT_ATTAINS = prove(
  [%q {|!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> f(x) <= M) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vX_CHOOSE_THEN [%q {|M:real|} ] vSTRIP_ASSUME_TAC -| vMATCH_MP vCONT_HASSUP)
  ----> vEXISTS_TAC [%q {|M:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vGEN_REWRITE_TAC vI [vTAUT [%q {|a <=> ~ ~a|} ]] ---->
  vCONV_TAC(vRAND_CONV vNOT_EXISTS_CONV) ---->
  vREWRITE_TAC[vTAUT [%q {|~(a /\ b /\ c) <=> a /\ b ==> ~c|} ]] ---->
  vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|!x. a <= x /\ x <= b ==> f(x) < M|} ] vMP_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vREAL_LT_LE] ---->
    vCONJ_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vFIRST_ASSUM vACCEPT_TAC; vALL_TAC] ---->
  vPURE_ONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|!x. a <= x /\ x <= b ==> (\x. inv(M - f(x))) contl x|} ]
  vASSUME_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ---->
    vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ---->
    vMATCH_MP_TAC vCONT_INV ----> vBETA_TAC ---->
    vREWRITE_TAC[vREAL_SUB_0] ----> vCONV_TAC(vONCE_DEPTH_CONV vSYM_CONV) ---->
    vCONJ_TAC ++-->
     [vALL_TAC;
      vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
      vONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ---->
    vMATCH_MP_TAC vCONT_SUB ----> vBETA_TAC ---->
    vREWRITE_TAC[vCONT_CONST] ---->
    vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ---->
    vFIRST_ASSUM(vMATCH_MP_TAC -| vCONJUNCT2) ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|?k. !x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x <= k|} ]
  vMP_TAC ++-->
   [vMATCH_MP_TAC vCONT_BOUNDED ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vBETA_TAC ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|k:real|} ]) ---->
  vSUBGOAL_THEN [%q {|!x. a <= x /\ x <= b ==> &0 < inv(M - f(x))|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_INV_POS ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!x. a <= x /\ x <= b ==> (\x. inv(M - (f x))) x < (k + &1)|} ]
  vASSUME_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|k:real|} ] ----> vREWRITE_TAC[vREAL_LT_ADDR; vREAL_LT_01] ---->
    vBETA_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!x. a <= x /\ x <= b ==>
         inv(k + &1) < inv((\x. inv(M - (f x))) x)|} ] vMP_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vREAL_LT_INV2 ---->
    vCONJ_TAC ++-->
     [vBETA_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]; vALL_TAC] ---->
  vBETA_TAC ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|!x. a <= x /\ x <= b ==> inv(k + &1) < (M - (f x))|} ]
  vMP_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ---->
    vSUBGOAL_THEN [%q {|~(M - f(x:real) = &0)|} ]
      (vSUBST1_TAC -| vSYM -| vMATCH_MP vREAL_INVINV) ++-->
     [vCONV_TAC(vRAND_CONV vSYM_CONV) ----> vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
      vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]; vALL_TAC] ---->
  vREWRITE_TAC[vREAL_LT_SUB_LADD] ----> vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_LT_SUB_LADD] ----> vDISCH_TAC ---->
  vUNDISCH_TAC [%q {|!N. N < M ==> (?x. a <= x /\ x <= b /\ N < (f x))|} ] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|M - inv(k + &1)|} ]) ---->
  vREWRITE_TAC[vREAL_LT_SUB_RADD; vREAL_LT_ADDR] ---->
  vREWRITE_TAC[vNOT_IMP] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vREAL_INV_POS ----> vMATCH_MP_TAC vREAL_LT_TRANS ---->
    vEXISTS_TAC [%q {|k:real|} ] ----> vREWRITE_TAC[vREAL_LT_ADDR; vREAL_LT_01] ---->
    vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|inv(M - f(a:real))|} ] ---->
    vCONJ_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[vREAL_LE_REFL];
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vMP_TAC) ----> vREWRITE_TAC[vCONJ_ASSOC] ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vREWRITE_TAC[vREAL_NOT_LT] ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ---->
    vONCE_REWRITE_TAC[vGSYM vREAL_LT_SUB_LADD] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]);;

(*----------------------------------------------------------------------------*)
(* Same theorem for lower bound                                               *)
(*----------------------------------------------------------------------------*)

let%a vCONT_ATTAINS2 = prove(
  [%q {|!f a b. (a <= b /\ !x. a <= x /\ x <= b ==> f contl x)
        ==> ?M. (!x. a <= x /\ x <= b ==> M <= f(x)) /\
                (?x. a <= x /\ x <= b /\ (f(x) = M))|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN vSTRIP_ASSUME_TAC ---->
  vSUBGOAL_THEN [%q {|!x. a <= x /\ x <= b ==> (\x. --(f x)) contl x|} ] vMP_TAC ++-->
   [vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vCONT_NEG ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vCONJ (vASSUME [%q {|a <= b|} ])) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|M:real|} ] vMP_TAC -| vMATCH_MP vCONT_ATTAINS) ---->
  vBETA_TAC ----> vDISCH_TAC ----> vEXISTS_TAC [%q {|--M|} ] ----> vCONJ_TAC ++-->
   [vGEN_TAC ----> vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_LE_NEG2] ---->
    vASM_REWRITE_TAC[vREAL_NEG_NEG];
    vASM_REWRITE_TAC[vGSYM vREAL_NEG_EQ]]);;

(* ------------------------------------------------------------------------- *)
(* Another version.                                                          *)
(* ------------------------------------------------------------------------- *)

let%a vCONT_ATTAINS_ALL = prove(
  [%q {|!f a b. (a <= b /\ !x. a <= x /\ x <= b ==>  f contl x)
        ==> ?L M. (!x. a <= x /\ x <= b ==> L <= f(x) /\ f(x) <= M) /\
                  !y. L <= y /\ y <= M ==> ?x. a <= x /\ x <= b /\ (f(x) = y)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vFIRST_ASSUM(vX_CHOOSE_THEN [%q {|L:real|} ] vMP_TAC -| vMATCH_MP vCONT_ATTAINS2) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|x1:real|} ] vSTRIP_ASSUME_TAC) ---->
  vFIRST_ASSUM(vX_CHOOSE_THEN [%q {|M:real|} ] vMP_TAC -| vMATCH_MP vCONT_ATTAINS) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|x2:real|} ] vSTRIP_ASSUME_TAC) ---->
   vMAP_EVERY vEXISTS_TAC [[%q {|L:real|} ]; [%q {|M:real|} ]] ----> vCONJ_TAC ++-->
   [vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
    vALL_TAC] ---->
  vDISJ_CASES_TAC(vSPECL [[%q {|x1:real|} ]; [%q {|x2:real|} ]] vREAL_LE_TOTAL) ---->
  vREPEAT vSTRIP_TAC ++-->
   [vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|x1:real|} ]; [%q {|x2:real|} ]; [%q {|y:real|} ]] vIVT) ---->
    vASM_REWRITE_TAC[] ----> vW(vC vSUBGOAL_THEN
    (fun t -> vREWRITE_TAC[t]) -| funpow 2 (fst -| dest_imp) -| snd) ++-->
     [vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM(vMATCH_MP_TAC -| vCONJUNCT2);
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vSTRIP_ASSUME_TAC) ---->

      vASM_REWRITE_TAC[] ----> vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[]] ---->
    (vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ++-->
      [vEXISTS_TAC [%q {|x1:real|} ]; vEXISTS_TAC [%q {|x2:real|} ]] ---->
     vASM_REWRITE_TAC[]);
    vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|x2:real|} ]; [%q {|x1:real|} ]; [%q {|y:real|} ]] vIVT2) ---->
    vASM_REWRITE_TAC[] ----> vW(vC vSUBGOAL_THEN
    (fun t -> vREWRITE_TAC[t]) -| funpow 2 (fst -| dest_imp) -| snd) ++-->
     [vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM(vMATCH_MP_TAC -| vCONJUNCT2);
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|x:real|} ] vSTRIP_ASSUME_TAC) ---->
     vASM_REWRITE_TAC[] ----> vEXISTS_TAC [%q {|x:real|} ] ----> vASM_REWRITE_TAC[]] ---->
    (vCONJ_TAC ----> vMATCH_MP_TAC vREAL_LE_TRANS ++-->
      [vEXISTS_TAC [%q {|x2:real|} ]; vEXISTS_TAC [%q {|x1:real|} ]] ---->
     vASM_REWRITE_TAC[])]);;

(*----------------------------------------------------------------------------*)
(* If f'(x) > 0 then x is locally strictly increasing at the right            *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_LINC = prove(
  [%q {|!f x l. (f diffl l)(x) /\ &0 < l ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x + h)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vREWRITE_TAC[diffl; vLIM; vREAL_SUB_RZERO] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|l:real|} ]) ----> vASM_REWRITE_TAC[] ----> vBETA_TAC ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vGEN_TAC ---->
  vDISCH_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vREAL_INV_POS -| vCONJUNCT1) ---->
  vDISCH_THEN(fun th -> vONCE_REWRITE_TAC[vGSYM(vMATCH_MP vREAL_LT_RMUL_EQ th)]) ---->
  vREWRITE_TAC[vREAL_MUL_LZERO] ----> vREWRITE_TAC[vGSYM real_div] ---->
  vMATCH_MP_TAC vABS_SIGN ----> vEXISTS_TAC [%q {|l:real|} ] ---->
  vFIRST_ASSUM vMATCH_MP_TAC ---->
  vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_LE -| vCONJUNCT1) ---->
  vASM_REWRITE_TAC[real_abs]);;

(*----------------------------------------------------------------------------*)
(* If f'(x) < 0 then x is locally strictly increasing at the left             *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_LDEC = prove(
  [%q {|!f x l. (f diffl l)(x) /\ l < &0 ==>
      ?d. &0 < d /\ !h. &0 < h /\ h < d ==> f(x) < f(x - h)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
  vREWRITE_TAC[diffl; vLIM; vREAL_SUB_RZERO] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|--l|} ]) ---->
  vONCE_REWRITE_TAC[vGSYM vREAL_NEG_LT0] ----> vASM_REWRITE_TAC[vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vREAL_NEG_LT0] ----> vBETA_TAC ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vGEN_TAC ---->
  vDISCH_TAC ----> vONCE_REWRITE_TAC[vGSYM vREAL_SUB_LT] ---->
  vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vREAL_INV_POS -| vCONJUNCT1) ---->
  vDISCH_THEN(fun th -> vONCE_REWRITE_TAC[vGSYM(vMATCH_MP vREAL_LT_RMUL_EQ th)]) ---->
  vREWRITE_TAC[vREAL_MUL_LZERO] ---->
  vREWRITE_TAC[vGSYM vREAL_NEG_LT0; vREAL_NEG_RMUL] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_NEG_INV
   (vGSYM (vMATCH_MP vREAL_LT_IMP_NE (vCONJUNCT1 th)))]) ---->
  vMATCH_MP_TAC vABS_SIGN2 ----> vEXISTS_TAC [%q {|l:real|} ] ---->
  vREWRITE_TAC[vGSYM real_div] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV -| funpow 3 vLAND_CONV -| vRAND_CONV)
    [real_sub] ---->
  vFIRST_ASSUM vMATCH_MP_TAC ---->
  vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_LE -| vCONJUNCT1) ---->
  vREWRITE_TAC[real_abs; vGSYM vREAL_NEG_LE0; vREAL_NEG_NEG] ---->
  vASM_REWRITE_TAC[vGSYM vREAL_NOT_LT]);;

(*----------------------------------------------------------------------------*)
(* If f is differentiable at a local maximum x, f'(x) = 0                     *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_LMAX = prove(
  [%q {|!f x l. (f diffl l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(y) <= f(x))) ==> (l = &0)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN
   (vCONJUNCTS_THEN2 vMP_TAC (vX_CHOOSE_THEN [%q {|k:real|} ] vSTRIP_ASSUME_TAC)) ---->
  vREPEAT_TCL vDISJ_CASES_THEN vASSUME_TAC
   (vSPECL [[%q {|l:real|} ]; [%q {|&0|} ]] vREAL_LT_TOTAL) ---->
  vASM_REWRITE_TAC[] ++-->
   [vDISCH_THEN(vMP_TAC -| vC vCONJ(vASSUME [%q {|l < &0|} ])) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_LDEC) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vMP_TAC) ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vMP_TAC(vSPECL [[%q {|k:real|} ]; [%q {|e:real|} ]] vREAL_DOWN2) ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|d:real|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC ----> vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x - d|} ]) ----> vREWRITE_TAC[vREAL_SUB_SUB2] ---->
    vSUBGOAL_THEN [%q {|&0 <= d|} ] vASSUME_TAC ++-->
     [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vASM_REWRITE_TAC[real_abs] ----> vASM_REWRITE_TAC[vGSYM vREAL_NOT_LT];
    vDISCH_THEN(vMP_TAC -| vC vCONJ(vASSUME [%q {|&0 < l|} ])) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_LINC) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vMP_TAC) ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vMP_TAC(vSPECL [[%q {|k:real|} ]; [%q {|e:real|} ]] vREAL_DOWN2) ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|d:real|} ]) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_TAC ----> vFIRST_ASSUM(vUNDISCH_TAC -| check is_forall -| concl) ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|x + d|} ]) ----> vREWRITE_TAC[vREAL_ADD_SUB2] ---->
    vSUBGOAL_THEN [%q {|&0 <= d|} ] vASSUME_TAC ++-->
     [vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
    vREWRITE_TAC[vABS_NEG] ---->
    vASM_REWRITE_TAC[real_abs] ----> vASM_REWRITE_TAC[vGSYM vREAL_NOT_LT]]);;

(*----------------------------------------------------------------------------*)
(* Similar theorem for a local minimum                                        *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_LMIN = prove(
  [%q {|!f x l. (f diffl l)(x) /\
           (?d. &0 < d /\ (!y. abs(x - y) < d ==> f(x) <= f(y))) ==> (l = &0)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|\x:real. --(f x)|} ]; [%q {|x:real|} ]; [%q {|--l|} ]] vDIFF_LMAX) ---->
  vBETA_TAC ----> vREWRITE_TAC[vREAL_LE_NEG2; vREAL_NEG_EQ0] ---->
  vDISCH_THEN vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vDIFF_NEG ----> vASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* In particular if a function is locally flat                                *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_LCONST = prove(
  [%q {|!f x l. (f diffl l)(x) /\
         (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x)))) ==> (l = &0)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMATCH_MP_TAC vDIFF_LMAX ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|f:real->real|} ]; [%q {|x:real|} ]] ----> vASM_REWRITE_TAC[] ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vGEN_TAC ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vSUBST1_TAC -| vC vMATCH_MP th)) ---->
  vMATCH_ACCEPT_TAC vREAL_LE_REFL);;

(*----------------------------------------------------------------------------*)
(* Lemma about introducing open ball in open interval                         *)
(*----------------------------------------------------------------------------*)

let%a vINTERVAL_LEMMA_LT = prove(
  [%q {|!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a < y /\ y < b|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vGSYM vABS_BETWEEN] ---->
  vDISJ_CASES_TAC(vSPECL [[%q {|x - a|} ]; [%q {|b - x|} ]] vREAL_LE_TOTAL) ++-->
   [vEXISTS_TAC [%q {|x - a|} ]; vEXISTS_TAC [%q {|b - x|} ]] ---->
  vASM_REWRITE_TAC[vREAL_SUB_LT] ----> vGEN_TAC ---->
  vREWRITE_TAC[vREAL_LT_SUB_LADD; vREAL_LT_SUB_RADD] ---->
  vREWRITE_TAC[real_sub; vREAL_ADD_ASSOC] ---->
  vREWRITE_TAC[vGSYM real_sub; vREAL_LT_SUB_LADD; vREAL_LT_SUB_RADD] ---->
  vFREEZE_THEN(fun th -> vONCE_REWRITE_TAC[th]) (vSPEC [%q {|x:real|} ] vREAL_ADD_SYM) ---->
  vREWRITE_TAC[vREAL_LT_RADD] ----> vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  (vMATCH_MP_TAC -| vGEN_ALL -| fst -| vEQ_IMP_RULE -| vSPEC_ALL) vREAL_LT_RADD ++-->
   [vEXISTS_TAC [%q {|a:real|} ] ----> vMATCH_MP_TAC vREAL_LTE_TRANS ---->
    vEXISTS_TAC [%q {|x + x|} ] ----> vASM_REWRITE_TAC[] ---->
    vUNDISCH_TAC [%q {|(x - a) <= (b - x)|} ];
     vEXISTS_TAC [%q {|b:real|} ] ----> vMATCH_MP_TAC vREAL_LET_TRANS ---->
    vEXISTS_TAC [%q {|x + x|} ] ----> vASM_REWRITE_TAC[] ---->
    vUNDISCH_TAC [%q {|(b - x) <= (x - a)|} ]] ---->
  vREWRITE_TAC[vREAL_LE_SUB_LADD; vGSYM vREAL_LE_SUB_RADD] ---->
  vMATCH_MP_TAC vEQ_IMP ---->
  vAP_THM_TAC ----> vAP_TERM_TAC ----> vREWRITE_TAC[real_sub] ---->
  vREWRITE_TAC[vREAL_ADD_AC]);;

let%a vINTERVAL_LEMMA = prove(
  [%q {|!a b x. a < x /\ x < b ==>
        ?d. &0 < d /\ !y. abs(x - y) < d ==> a <= y /\ y <= b|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|d:real|} ] -| vMATCH_MP vINTERVAL_LEMMA_LT) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vGEN_TAC ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th -| vCONJUNCT2)) ---->
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]);;

(*----------------------------------------------------------------------------*)
(* Now Rolle's theorem                                                        *)
(*----------------------------------------------------------------------------*)

let%a vROLLE = prove(
  [%q {|!f a b. a < b /\
           (f(a) = f(b)) /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?z. a < z /\ z < b /\ (f diffl &0)(z)|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN vSTRIP_ASSUME_TAC ---->
  vFIRST_ASSUM(vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
  vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]] vCONT_ATTAINS) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|M:real|} ] vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vX_CHOOSE_TAC [%q {|x1:real|} ])) ---->
  vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]] vCONT_ATTAINS2) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:real|} ] vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vX_CHOOSE_TAC [%q {|x2:real|} ])) ---->
  vASM_CASES_TAC [%q {|a < x1 /\ x1 < b|} ] ++-->
   [vFIRST_ASSUM(vX_CHOOSE_THEN [%q {|d:real|} ] vMP_TAC -| vMATCH_MP vINTERVAL_LEMMA) ---->
    vDISCH_THEN vSTRIP_ASSUME_TAC ----> vEXISTS_TAC [%q {|x1:real|} ] ---->
    vASM_REWRITE_TAC[] ----> vSUBGOAL_THEN
     [%q {|?l. (f diffl l)(x1) /\
          ?d. &0 < d /\ (!y. abs(x1 - y) < d ==> f(y) <= f(x1))|} ] vMP_TAC ++-->
     [vCONV_TAC vEXISTS_AND_CONV ----> vCONJ_TAC ++-->
       [vREWRITE_TAC[vGSYM differentiable] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
        vASM_REWRITE_TAC[];
        vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|y:real|} ] ---->
        vDISCH_TAC ----> vREPEAT(vFIRST_ASSUM vMATCH_MP_TAC) ---->
        vASM_REWRITE_TAC[]]; vALL_TAC] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|l:real|} ] vMP_TAC) ---->
    vDISCH_THEN(fun th -> vASSUME_TAC th ---->
                         vSUBST_ALL_TAC(vMATCH_MP vDIFF_LMAX th))
    ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vASM_CASES_TAC [%q {|a < x2 /\ x2 < b|} ] ++-->
   [vFIRST_ASSUM(vX_CHOOSE_THEN [%q {|d:real|} ] vMP_TAC -| vMATCH_MP vINTERVAL_LEMMA) ---->
    vDISCH_THEN vSTRIP_ASSUME_TAC ----> vEXISTS_TAC [%q {|x2:real|} ] ---->
    vASM_REWRITE_TAC[] ----> vSUBGOAL_THEN
     [%q {|?l. (f diffl l)(x2) /\
          ?d. &0 < d /\ (!y. abs(x2 - y) < d ==> f(x2) <= f(y))|} ] vMP_TAC ++-->
     [vCONV_TAC vEXISTS_AND_CONV ----> vCONJ_TAC ++-->
       [vREWRITE_TAC[vGSYM differentiable] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
        vASM_REWRITE_TAC[];
        vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|y:real|} ] ---->
        vDISCH_TAC ----> vREPEAT(vFIRST_ASSUM vMATCH_MP_TAC) ---->
        vASM_REWRITE_TAC[]]; vALL_TAC] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|l:real|} ] vMP_TAC) ---->
    vDISCH_THEN(fun th -> vASSUME_TAC th ---->
                         vSUBST_ALL_TAC(vMATCH_MP vDIFF_LMIN th)) ---->
  vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!x. a <= x /\ x <= b ==> (f(x):real = f(b))|} ] vMP_TAC ++-->
   [vREPEAT(vFIRST_ASSUM(vUNDISCH_TAC -| check is_neg -| concl)) ---->
    vASM_REWRITE_TAC[vREAL_LT_LE] ----> vREWRITE_TAC[vDE_MORGAN_THM] ---->
    vREPEAT (vDISCH_THEN(vDISJ_CASES_THEN2 (vMP_TAC -| vSYM) vMP_TAC) ---->
            vDISCH_THEN(vSUBST_ALL_TAC -| vAP_TERM [%q {|f:real->real|} ])) ---->
    vUNDISCH_TAC [%q {|(f:real->real) a = f b|} ] ---->
    vDISCH_THEN(fun th -> vSUBST_ALL_TAC th ----> vASSUME_TAC th) ---->
    vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vGSYM vREAL_LE_ANTISYM] ---->
    (vCONJ_TAC ++-->
      [vSUBGOAL_THEN [%q {|(f:real->real) b = M|} ] vSUBST1_TAC ++-->
        [vFIRST_ASSUM(vACCEPT_TAC -| el 2 -| vCONJUNCTS);
         vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]];
       vSUBGOAL_THEN [%q {|(f:real->real) b = m|} ] vSUBST1_TAC ++-->
        [vFIRST_ASSUM(vACCEPT_TAC -| el 2 -| vCONJUNCTS);
         vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]]]);
    vX_CHOOSE_TAC [%q {|x:real|} ] (vMATCH_MP vREAL_MEAN (vASSUME [%q {|a < b|} ])) ---->
    vDISCH_TAC ----> vEXISTS_TAC [%q {|x:real|} ] ---->
    vREWRITE_TAC[vASSUME [%q {|a < x /\ x < b|} ]] ---->
    vFIRST_ASSUM(vMP_TAC -| vMATCH_MP vINTERVAL_LEMMA) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
    vSUBGOAL_THEN [%q {|?l. (f diffl l)(x) /\
        (?d. &0 < d /\ (!y. abs(x - y) < d ==> (f(y) = f(x))))|} ] vMP_TAC ++-->
     [vCONV_TAC(vONCE_DEPTH_CONV vEXISTS_AND_CONV) ----> vCONJ_TAC ++-->
       [vREWRITE_TAC[vGSYM differentiable] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
        vASM_REWRITE_TAC[];
        vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ----> vGEN_TAC ---->
        vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
        vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
        vDISCH_THEN vSUBST1_TAC ----> vCONV_TAC vSYM_CONV ---->
        vFIRST_ASSUM vMATCH_MP_TAC ----> vCONJ_TAC ---->
        vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]];
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|l:real|} ] (fun th ->
       vASSUME_TAC th ----> vSUBST_ALL_TAC(vMATCH_MP vDIFF_LCONST th))) ---->
      vASM_REWRITE_TAC[]]]);;

(*----------------------------------------------------------------------------*)
(* Mean value theorem                                                         *)
(*----------------------------------------------------------------------------*)

let%a vMVT_LEMMA = prove(
  [%q {|!(f:real->real) a b.
        (\x. f(x) - (((f(b) - f(a)) / (b - a)) * x))(a) =
        (\x. f(x) - (((f(b) - f(a)) / (b - a)) * x))(b)|} ],
  vREPEAT vGEN_TAC ----> vBETA_TAC ---->
  vASM_CASES_TAC [%q {|b:real = a|} ] ----> vASM_REWRITE_TAC[] ---->
  vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
  vRULE_ASSUM_TAC(vONCE_REWRITE_RULE[vGSYM vREAL_SUB_0]) ---->
  vMP_TAC(vGENL [[%q {|x:real|} ]; [%q {|y:real|} ]]
   (vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]; [%q {|b - a|} ]] vREAL_EQ_RMUL)) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(fun th -> vGEN_REWRITE_TAC vI [vGSYM th]) ---->
  vREWRITE_TAC[vREAL_SUB_RDISTRIB; vGSYM vREAL_MUL_ASSOC] ---->
  vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP vREAL_DIV_RMUL th]) ---->
  vGEN_REWRITE_TAC (vRAND_CONV -| vRAND_CONV) [vREAL_MUL_SYM] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vREAL_MUL_SYM] ---->
  vREWRITE_TAC[real_sub; vREAL_LDISTRIB; vREAL_RDISTRIB] ---->
  vREWRITE_TAC[vGSYM vREAL_NEG_LMUL; vGSYM vREAL_NEG_RMUL;
              vREAL_NEG_ADD; vREAL_NEG_NEG] ---->
  vREWRITE_TAC[vGSYM vREAL_ADD_ASSOC] ---->
  vREWRITE_TAC[vAC vREAL_ADD_AC
    [%q {|w + x + y + z = (y + w) + (x + z)|} ]; vREAL_ADD_LINV; vREAL_ADD_LID] ---->
  vREWRITE_TAC[vREAL_ADD_RID]);;

let%a vMVT = prove(
  [%q {|!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> f differentiable x)
        ==> ?l z. a < z /\ z < b /\ (f diffl l)(z) /\
            (f(b) - f(a) = (b - a) * l)|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|\x. f(x) - (((f(b) - f(a)) / (b - a)) * x)|} ];
                [%q {|a:real|} ]; [%q {|b:real|} ]] vROLLE) ---->
  vW(vC vSUBGOAL_THEN (fun t ->vREWRITE_TAC[t]) -|
  funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vASM_REWRITE_TAC[vMVT_LEMMA] ----> vBETA_TAC ---->
    vCONJ_TAC ----> vX_GEN_TAC [%q {|x:real|} ] ++-->
     [vDISCH_TAC ----> vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ---->
      vMATCH_MP_TAC vCONT_SUB ----> vCONJ_TAC ++-->
       [vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ---->
        vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[];
        vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ----> vMATCH_MP_TAC vCONT_MUL ---->
        vREWRITE_TAC[vCONT_CONST] ----> vMATCH_MP_TAC vDIFF_CONT ---->
        vEXISTS_TAC [%q {|&1|} ] ----> vMATCH_ACCEPT_TAC vDIFF_X];
      vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
      vREWRITE_TAC[differentiable] ----> vDISCH_THEN(vX_CHOOSE_TAC [%q {|l:real|} ]) ---->
      vEXISTS_TAC [%q {|l - ((f(b) - f(a)) / (b - a))|} ] ---->
      vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ----> vMATCH_MP_TAC vDIFF_SUB ---->
      vCONJ_TAC ++-->
       [vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ----> vFIRST_ASSUM vACCEPT_TAC;
        vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ----> vREWRITE_TAC[] ---->
        vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_RID] ---->
        vMATCH_MP_TAC vDIFF_CMUL ----> vMATCH_ACCEPT_TAC vDIFF_X]];
    vALL_TAC] ---->
  vREWRITE_TAC[vCONJ_ASSOC] ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vMP_TAC) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
  vDISCH_THEN((---->) (vMAP_EVERY vEXISTS_TAC
   [[%q {|((f(b) - f(a)) / (b - a))|} ]; [%q {|z:real|} ]]) -| vMP_TAC) ---->
  vASM_REWRITE_TAC[] ----> vDISCH_THEN((---->) vCONJ_TAC -| vMP_TAC) ++-->
   [vALL_TAC; vDISCH_THEN(vK vALL_TAC) ----> vCONV_TAC vSYM_CONV ---->
    vMATCH_MP_TAC vREAL_DIV_LMUL ----> vREWRITE_TAC[vREAL_SUB_0] ---->
    vDISCH_THEN vSUBST_ALL_TAC ----> vUNDISCH_TAC [%q {|a < a|} ] ---->
    vREWRITE_TAC[vREAL_LT_REFL]] ---->
  vSUBGOAL_THEN [%q {|((\x. ((f(b) - f(a)) / (b - a)) * x ) diffl
                      ((f(b) - f(a)) / (b - a)))(z)|} ]
  (fun th -> vDISCH_THEN(vMP_TAC -| vC vCONJ th)) ++-->
   [vCONV_TAC(vONCE_DEPTH_CONV vHABS_CONV) ----> vREWRITE_TAC[] ---->
    vGEN_REWRITE_TAC vLAND_CONV [vGSYM vREAL_MUL_RID] ---->
    vMATCH_MP_TAC vDIFF_CMUL ----> vREWRITE_TAC[vDIFF_X]; vALL_TAC] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vDIFF_ADD) ----> vBETA_TAC ---->
  vREWRITE_TAC[vREAL_SUB_ADD] ----> vCONV_TAC(vONCE_DEPTH_CONV vETA_CONV) ---->
  vREWRITE_TAC[vREAL_ADD_LID]);;

(* ------------------------------------------------------------------------- *)
(* Simple version with pure differentiability assumption.                    *)
(* ------------------------------------------------------------------------- *)

let%a vMVT_ALT = prove
 ([%q {|!f f' a b.
        a < b /\ (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x))
        ==> ?z. a < z /\ z < b /\ (f b - f a = (b - a) * f'(z))|} ],
  vREPEAT vSTRIP_TAC ----> vSUBGOAL_THEN
   [%q {|?l z. a < z /\ z < b /\ (f diffl l) z /\ (f b - f a = (b - a) * l)|} ]
  vMP_TAC ++-->
   [vMATCH_MP_TAC vMVT ----> vREWRITE_TAC[differentiable] ---->
    vASM_MESON_TAC[vDIFF_CONT; vREAL_LT_IMP_LE];
    vASM_MESON_TAC[vDIFF_UNIQ; vREAL_LT_IMP_LE]]);;

(*----------------------------------------------------------------------------*)
(* Theorem that function is constant if its derivative is 0 over an interval. *)
(*                                                                            *)
(* We could have proved this directly by bisection; consider instantiating    *)
(* BOLZANO_LEMMA with                                                         *)
(*                                                                            *)
(*     \(x,y). f(y) - f(x) <= C * (y - x)                                     *)
(*                                                                            *)
(* However the Rolle and Mean Value theorems are useful to have anyway        *)
(*----------------------------------------------------------------------------*)

let%a vDIFF_ISCONST_END = prove(
  [%q {|!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> (f b = f a)|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]] vMVT) ---->
  vASM_REWRITE_TAC[] ---->
  vW(vC vSUBGOAL_THEN vMP_TAC -| funpow 2 (fst -| dest_imp) -| snd) ++-->
   [vGEN_TAC ----> vREWRITE_TAC[differentiable] ---->
    vDISCH_THEN((---->) (vEXISTS_TAC [%q {|&0|} ]) -| vMP_TAC) ---->
    vASM_REWRITE_TAC[];
    vDISCH_THEN(fun th -> vREWRITE_TAC[th])] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|l:real|} ] (vX_CHOOSE_THEN [%q {|x:real|} ] vMP_TAC)) ---->
  vONCE_REWRITE_TAC[vTAUT [%q {|a /\ b /\ c /\ d <=> (a /\ b) /\ (c /\ d)|} ]] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vSTRIP_ASSUME_TAC) ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
  vDISCH_THEN(vMP_TAC -| vCONJ (vASSUME [%q {|(f diffl l)(x)|} ])) ---->
  vDISCH_THEN(vSUBST_ALL_TAC -| vMATCH_MP vDIFF_UNIQ) ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vREAL_MUL_RZERO; vREAL_SUB_0]) ---->
  vFIRST_ASSUM vACCEPT_TAC);;

let%a vDIFF_ISCONST = prove(
  [%q {|!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> f contl x) /\
           (!x. a < x /\ x < b ==> (f diffl &0)(x))
        ==> !x. a <= x /\ x <= b ==> (f x = f a)|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ----> vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|a:real|} ]; [%q {|x:real|} ]] vDIFF_ISCONST_END) ---->
  vDISJ_CASES_THEN vMP_TAC (vREWRITE_RULE[vREAL_LE_LT] (vASSUME [%q {|a <= x|} ])) ++-->
   [vDISCH_TAC ----> vASM_REWRITE_TAC[] ----> vDISCH_THEN vMATCH_MP_TAC ---->
    vCONJ_TAC ----> vX_GEN_TAC [%q {|z:real|} ] ----> vSTRIP_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|x:real|} ];
      vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|x:real|} ]] ---->
    vASM_REWRITE_TAC[];
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[]]);;

let%a vDIFF_ISCONST_END_SIMPLE = prove
 ([%q {|!f a b. a < b /\
           (!x. a <= x /\ x <= b ==> (f diffl &0)(x))
        ==> (f b = f a)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDIFF_ISCONST_END ---->
  vASM_MESON_TAC[vDIFF_CONT; vREAL_LT_IMP_LE]);;

let%a vDIFF_ISCONST_ALL = prove(
  [%q {|!f x y. (!x. (f diffl &0)(x)) ==> (f(x) = f(y))|} ],
  vREWRITE_TAC[vRIGHT_FORALL_IMP_THM] ---->
  vGEN_TAC ----> vDISCH_TAC ---->
  vSUBGOAL_THEN [%q {|!x. f contl x|} ] vASSUME_TAC ++-->
   [vGEN_TAC ----> vMATCH_MP_TAC vDIFF_CONT ---->
    vEXISTS_TAC [%q {|&0|} ] ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vREPEAT vGEN_TAC ----> vREPEAT_TCL vDISJ_CASES_THEN vMP_TAC
   (vSPECL [[%q {|x:real|} ]; [%q {|y:real|} ]] vREAL_LT_TOTAL) ++-->
   [vDISCH_THEN vSUBST1_TAC ----> vREFL_TAC;
    vCONV_TAC(vRAND_CONV vSYM_CONV);
    vALL_TAC] ---->
  vDISCH_TAC ----> vMATCH_MP_TAC vDIFF_ISCONST_END ---->
  vASM_REWRITE_TAC[]);;

(* ------------------------------------------------------------------------ *)
(* Boring lemma about distances                                             *)
(* ------------------------------------------------------------------------ *)

let%a vINTERVAL_ABS = vREAL_ARITH
  [%q {|!x z d. (x - d) <= z /\ z <= (x + d) <=> abs(z - x) <= d|} ];;

(* ------------------------------------------------------------------------ *)
(* Dull lemma that an continuous injection on an interval must have a strict*)
(* maximum at an end point, not in the middle.                              *)
(* ------------------------------------------------------------------------ *)

let%a vCONT_INJ_LEMMA = prove(
  [%q {|!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(z) <= f(x))|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vIMP_RES_THEN vASSUME_TAC vREAL_LT_IMP_LE ---->
  vDISCH_THEN(fun th -> vMAP_EVERY (vMP_TAC -| vC vSPEC th) [[%q {|x - d|} ]; [%q {|x + d|} ]]) ---->
  vREWRITE_TAC[vREAL_ADD_SUB; vREAL_SUB_SUB; vABS_NEG] ---->
  vASM_REWRITE_TAC[real_abs; vREAL_LE_REFL] ---->
  vDISCH_TAC ----> vDISCH_TAC ----> vDISJ_CASES_TAC
    (vSPECL [[%q {|f(x - d):real|} ]; [%q {|f(x + d):real|} ]] vREAL_LE_TOTAL) ++-->
   [vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|x - d|} ]; [%q {|x:real|} ]; [%q {|f(x + d):real|} ]] vIVT) ---->
    vASM_REWRITE_TAC[vREAL_LE_SUB_RADD; vREAL_LE_ADDR] ---->
    vW(vC vSUBGOAL_THEN vMP_TAC -| fst -| dest_imp -| dest_neg -| snd) ++-->
     [vX_GEN_TAC [%q {|z:real|} ] ----> vSTRIP_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vONCE_REWRITE_TAC[vGSYM vABS_NEG] ---->
      vREWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
      vASM_REWRITE_TAC[vREAL_NEG_SUB; vREAL_SUB_LE; vREAL_LE_SUB_RADD] ---->
      vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vASM_REWRITE_TAC[];
      vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vSTRIP_ASSUME_TAC) ---->
      vFIRST_ASSUM(vMP_TAC -| vAP_TERM [%q {|g:real->real|} ]) ---->
      vSUBGOAL_THEN [%q {|g((f:real->real) z) = z|} ] vSUBST1_TAC ++-->
       [vFIRST_ASSUM vMATCH_MP_TAC ---->
        vONCE_REWRITE_TAC[vGSYM vABS_NEG] ---->
        vREWRITE_TAC[real_abs; vREAL_SUB_LE] ---->
        vASM_REWRITE_TAC[vREAL_NEG_SUB; vREAL_SUB_LE; vREAL_LE_SUB_RADD] ---->
        vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
      vSUBGOAL_THEN [%q {|g(f(x + d):real) = x + d|} ] vSUBST1_TAC ++-->
       [vFIRST_ASSUM vMATCH_MP_TAC ----> vREWRITE_TAC[vREAL_ADD_SUB] ---->
        vASM_REWRITE_TAC[real_abs; vREAL_LE_REFL]; vALL_TAC] ---->
      vREWRITE_TAC[] ----> vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
      vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
      vASM_REWRITE_TAC[vREAL_LT_ADDR]];
    vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|x:real|} ]; [%q {|x + d|} ]; [%q {|f(x - d):real|} ]] vIVT2) ---->
    vASM_REWRITE_TAC[vREAL_LE_SUB_RADD; vREAL_LE_ADDR] ---->
    vW(vC vSUBGOAL_THEN vMP_TAC -| fst -| dest_imp -| dest_neg -| snd) ++-->
     [vX_GEN_TAC [%q {|z:real|} ] ----> vSTRIP_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
      vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE; vREAL_LE_SUB_RADD] ---->
      vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vASM_REWRITE_TAC[];
      vDISCH_THEN(fun th -> vREWRITE_TAC[th]) ---->
      vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vSTRIP_ASSUME_TAC) ---->
      vFIRST_ASSUM(vMP_TAC -| vAP_TERM [%q {|g:real->real|} ]) ---->
      vSUBGOAL_THEN [%q {|g((f:real->real) z) = z|} ] vSUBST1_TAC ++-->
       [vFIRST_ASSUM vMATCH_MP_TAC ---->
        vASM_REWRITE_TAC[real_abs; vREAL_SUB_LE; vREAL_LE_SUB_RADD] ---->
        vONCE_REWRITE_TAC[vREAL_ADD_SYM] ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
      vSUBGOAL_THEN [%q {|g(f(x - d):real) = x - d|} ] vSUBST1_TAC ++-->
       [vFIRST_ASSUM vMATCH_MP_TAC ---->
        vREWRITE_TAC[vREAL_SUB_SUB; vABS_NEG] ---->
        vASM_REWRITE_TAC[real_abs; vREAL_LE_REFL]; vALL_TAC] ---->
      vREWRITE_TAC[] ----> vCONV_TAC(vRAND_CONV vSYM_CONV) ---->
      vMATCH_MP_TAC vREAL_LT_IMP_NE ---->
      vMATCH_MP_TAC vREAL_LTE_TRANS ----> vEXISTS_TAC [%q {|x:real|} ] ---->
      vASM_REWRITE_TAC[vREAL_LT_SUB_RADD; vREAL_LT_ADDR]]]);;

(* ------------------------------------------------------------------------ *)
(* Similar version for lower bound                                          *)
(* ------------------------------------------------------------------------ *)

let%a vCONT_INJ_LEMMA2 = prove(
  [%q {|!f g x d. &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
     ~(!z. abs(z - x) <= d ==> f(x) <= f(z))|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|\x:real. --(f x)|} ]; [%q {|\y. (g(--y):real)|} ]; [%q {|x:real|} ]; [%q {|d:real|} ]]
    vCONT_INJ_LEMMA) ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[vREAL_NEG_NEG; vREAL_LE_NEG2] ---->
  vDISCH_THEN vMATCH_MP_TAC ---->
  vGEN_TAC ----> vDISCH_TAC ----> vMATCH_MP_TAC vCONT_NEG ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vFIRST_ASSUM vACCEPT_TAC);;

(* ------------------------------------------------------------------------ *)
(* Show there's an interval surrounding f(x) in f[[x - d, x + d]]           *)
(* ------------------------------------------------------------------------ *)

let%a vCONT_INJ_RANGE = prove(
  [%q {|!f g x d.  &0 < d /\
            (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
            (!z. abs(z - x) <= d ==> f contl z) ==>
        ?e. &0 < e /\
            (!y. abs(y - f(x)) <= e ==> ?z. abs(z - x) <= d /\ (f z = y))|} ],
  vREPEAT vGEN_TAC ----> vSTRIP_TAC ---->
  vIMP_RES_THEN vASSUME_TAC vREAL_LT_IMP_LE ---->
  vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|x - d|} ]; [%q {|x + d|} ]] vCONT_ATTAINS_ALL) ---->
  vASM_REWRITE_TAC[vINTERVAL_ABS; vREAL_LE_SUB_RADD] ---->
  vASM_REWRITE_TAC[vGSYM vREAL_ADD_ASSOC; vREAL_LE_ADDR; vREAL_LE_DOUBLE] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|L:real|} ] (vX_CHOOSE_THEN [%q {|M:real|} ] vMP_TAC)) ---->
  vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|L <= f(x:real) /\ f(x) <= M|} ] vSTRIP_ASSUME_TAC ++-->
   [vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_REWRITE_TAC[vREAL_SUB_REFL; vABS_0]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|L < f(x:real) /\ f(x:real) < M|} ] vSTRIP_ASSUME_TAC ++-->
   [vCONJ_TAC ----> vASM_REWRITE_TAC[vREAL_LT_LE] ++-->
     [vDISCH_THEN vSUBST_ALL_TAC ----> (vMP_TAC -| vC vSPECL vCONT_INJ_LEMMA2)
        [[%q {|f:real->real|} ]; [%q {|g:real->real|} ]; [%q {|x:real|} ]; [%q {|d:real|} ]];
      vDISCH_THEN(vSUBST_ALL_TAC -| vSYM) ----> (vMP_TAC -| vC vSPECL vCONT_INJ_LEMMA)
        [[%q {|f:real->real|} ]; [%q {|g:real->real|} ]; [%q {|x:real|} ]; [%q {|d:real|} ]]] ---->
    vASM_REWRITE_TAC[] ----> vGEN_TAC ---->
    vDISCH_THEN(fun t -> vFIRST_ASSUM(fun th -> vREWRITE_TAC[vMATCH_MP th t] ---->
      vNO_TAC));
    vMP_TAC(vSPECL [[%q {|f(x:real) - L|} ]; [%q {|M - f(x:real)|} ]] vREAL_DOWN2) ---->
    vASM_REWRITE_TAC[vREAL_SUB_LT] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vGEN_TAC ----> vDISCH_TAC ----> vREWRITE_TAC[vGSYM vINTERVAL_ABS] ---->
    vREWRITE_TAC[vREAL_LE_SUB_RADD] ----> vONCE_REWRITE_TAC[vGSYM vCONJ_ASSOC] ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vUNDISCH_TAC [%q {|abs(y - f(x:real)) <= e|} ] ---->
    vREWRITE_TAC[vGSYM vINTERVAL_ABS] ----> vSTRIP_TAC ----> vCONJ_TAC ++-->
     [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|f(x:real) - e|} ] ---->
      vASM_REWRITE_TAC[] ----> vONCE_REWRITE_TAC[vREAL_LE_SUB_LADD] ---->
      vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
      vREWRITE_TAC[vGSYM vREAL_LE_SUB_LADD];
      vMATCH_MP_TAC vREAL_LE_TRANS ---->
      vEXISTS_TAC [%q {|f(x:real) + (M - f(x))|} ] ----> vCONJ_TAC ++-->
       [vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|f(x:real) + e|} ] ---->
        vASM_REWRITE_TAC[vREAL_LE_LADD];
        vREWRITE_TAC[vREAL_SUB_ADD2; vREAL_LE_REFL]]] ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]]);;

(* ------------------------------------------------------------------------ *)
(* Continuity of inverse function                                           *)
(* ------------------------------------------------------------------------ *)

let%a vCONT_INVERSE = prove(
  [%q {|!f g x d. &0 < d /\
             (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
             (!z. abs(z - x) <= d ==> f contl z)
        ==> g contl (f x)|} ],
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[contl; vLIM] ---->
  vX_GEN_TAC [%q {|a:real|} ] ----> vDISCH_TAC ---->
  vMP_TAC(vSPECL [[%q {|a:real|} ]; [%q {|d:real|} ]] vREAL_DOWN2) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vSTRIP_ASSUME_TAC) ---->
  vIMP_RES_THEN vASSUME_TAC vREAL_LT_IMP_LE ---->
  vSUBGOAL_THEN [%q {|!z. abs(z - x) <= e ==> (g(f z :real) = z)|} ] vASSUME_TAC ++-->
   [vX_GEN_TAC [%q {|z:real|} ] ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[];
    vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|!z. abs(z - x) <= e ==> (f contl z)|} ] vASSUME_TAC ++-->
   [vX_GEN_TAC [%q {|z:real|} ] ----> vDISCH_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vMATCH_MP_TAC vREAL_LE_TRANS ----> vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[];
    vALL_TAC] ---->
  vUNDISCH_TAC [%q {|!z. abs(z - x) <= d ==> (g(f z :real) = z)|} ] ---->
  vUNDISCH_TAC [%q {|!z. abs(z - x) <= d ==> (f contl z)|} ] ---->
  vDISCH_THEN(vK vALL_TAC) ----> vDISCH_THEN(vK vALL_TAC) ---->
  (vMP_TAC -| vC vSPECL vCONT_INJ_RANGE)
    [[%q {|f:real->real|} ]; [%q {|g:real->real|} ]; [%q {|x:real|} ]; [%q {|e:real|} ]] ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|k:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|k:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|h:real|} ] ----> vBETA_TAC ----> vREWRITE_TAC[vREAL_SUB_RZERO] ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC
    (vASSUME_TAC -| vMATCH_MP vREAL_LT_IMP_LE)) ---->
  vREWRITE_TAC[vGSYM vABS_NZ] ----> vDISCH_TAC ---->
  vFIRST_ASSUM(fun th -> vMP_TAC(vSPEC [%q {|f(x:real) + h|} ] th) ---->
    vREWRITE_TAC[vREAL_ADD_SUB; vASSUME [%q {|abs(h) <= k|} ]] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vSTRIP_ASSUME_TAC)) ---->
  vFIRST_ASSUM(vUNDISCH_TAC -| check is_eq -| concl) ---->
  vDISCH_THEN(vSUBST1_TAC -| vSYM) ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|e:real|} ] ---->
  vSUBGOAL_THEN [%q {|(g((f:real->real)(z)) = z) /\ (g(f(x)) = x)|} ]
    (fun t -> vASM_REWRITE_TAC[t]) ----> vCONJ_TAC ---->
  vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[vREAL_SUB_REFL; vABS_0]);;

(* ------------------------------------------------------------------------ *)
(* Differentiability of inverse function                                    *)
(* ------------------------------------------------------------------------ *)

let%a vDIFF_INVERSE = prove(
  [%q {|!f g l x d. &0 < d /\
               (!z. abs(z - x) <= d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) <= d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)|} ],
  vREPEAT vSTRIP_TAC ----> vUNDISCH_TAC [%q {|(f diffl l)(x)|} ] ---->
  vDISCH_THEN(fun th -> vASSUME_TAC(vMATCH_MP vDIFF_CONT th) ----> vMP_TAC th) ---->
  vREWRITE_TAC[vDIFF_CARAT] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|h:real->real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|\y. if y = f(x) then
    inv(h(g y)) else (g(y) - g(f(x:real))) / (y - f(x))|} ] ----> vBETA_TAC ---->
  vASM_REWRITE_TAC[] ----> vREPEAT vCONJ_TAC ++-->
   [vX_GEN_TAC [%q {|z:real|} ] ----> vCOND_CASES_TAC ---->
    vASM_REWRITE_TAC[vREAL_SUB_REFL; vREAL_MUL_RZERO] ---->
    vCONV_TAC vSYM_CONV ----> vMATCH_MP_TAC vREAL_DIV_RMUL ---->
    vASM_REWRITE_TAC[vREAL_SUB_0];
    vALL_TAC;
    vFIRST_ASSUM(vSUBST1_TAC -| vSYM) ----> vREPEAT vAP_TERM_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ---->
    vREWRITE_TAC[vREAL_SUB_REFL; vABS_0] ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE ----> vASM_REWRITE_TAC[]] ---->
  vREWRITE_TAC[vCONTL_LIM] ----> vBETA_TAC ----> vREWRITE_TAC[] ---->
  vSUBGOAL_THEN [%q {|g((f:real->real)(x)) = x|} ] vASSUME_TAC ++-->
   [vFIRST_ASSUM vMATCH_MP_TAC ----> vREWRITE_TAC[vREAL_SUB_REFL; vABS_0] ---->
    vMATCH_MP_TAC vREAL_LT_IMP_LE; vALL_TAC] ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vLIM_TRANSFORM ----> vEXISTS_TAC [%q {|\y:real. inv(h(g(y):real))|} ] ---->
  vBETA_TAC ----> vCONJ_TAC ++-->
   [vALL_TAC;
    (vSUBST1_TAC -| vSYM -| vONCE_DEPTH_CONV vBETA_CONV)
      [%q {|\y. inv((\y:real. h(g(y):real)) y)|} ] ---->
    vMATCH_MP_TAC vLIM_INV ----> vASM_REWRITE_TAC[] ---->
    vSUBGOAL_THEN [%q {|(\y:real. h(g(y):real)) contl (f(x:real))|} ] vMP_TAC ++-->
     [vMATCH_MP_TAC vCONT_COMPOSE ----> vASM_REWRITE_TAC[] ---->
      vMATCH_MP_TAC vCONT_INVERSE ----> vEXISTS_TAC [%q {|d:real|} ];
      vREWRITE_TAC[vCONTL_LIM] ----> vBETA_TAC] ---->
    vASM_REWRITE_TAC[]] ---->
  vSUBGOAL_THEN [%q {|?e. &0 < e /\
                    !y. &0 < abs(y - f(x:real)) /\
                        abs(y - f(x:real)) < e ==>
                            (f(g(y)) = y) /\ ~(h(g(y)) = &0)|} ]
  vSTRIP_ASSUME_TAC ++-->
   [vALL_TAC;
    vREWRITE_TAC[vLIM] ----> vX_GEN_TAC [%q {|k:real|} ] ----> vDISCH_TAC ---->
    vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|y:real|} ] ---->
    vDISCH_THEN(fun th -> vFIRST_ASSUM(vSTRIP_ASSUME_TAC -| vC vMATCH_MP th) ---->
      vASSUME_TAC(vREWRITE_RULE[vGSYM vABS_NZ; vREAL_SUB_0] (vCONJUNCT1 th))) ---->
    vBETA_TAC ----> vASM_REWRITE_TAC[vREAL_SUB_RZERO] ---->
    vSUBGOAL_THEN [%q {|y - f(x) = h(g(y)) * (g(y) - x)|} ] vSUBST1_TAC ++-->
     [vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vRAND_CONV [vGSYM th]) ---->
      vREWRITE_TAC[vASSUME [%q {|f((g:real->real)(y)) = y|} ]];
      vUNDISCH_TAC [%q {|&0 < k|} ] ---->
      vMATCH_MP_TAC vEQ_IMP ---->
      vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vCONV_TAC vSYM_CONV ----> vREWRITE_TAC[vABS_ZERO; vREAL_SUB_0]] ---->
    vSUBGOAL_THEN [%q {|~(g(y:real) - x = &0)|} ] vASSUME_TAC ++-->
     [vREWRITE_TAC[vREAL_SUB_0] ---->
      vDISCH_THEN(vMP_TAC -| vAP_TERM [%q {|f:real->real|} ]) ---->
      vASM_REWRITE_TAC[]; vREWRITE_TAC[real_div]] ---->
    vSUBGOAL_THEN [%q {|inv((h(g(y))) * (g(y:real) - x)) =
      inv(h(g(y))) * inv(g(y) - x)|} ] vSUBST1_TAC ++-->
     [vMATCH_MP_TAC vREAL_INV_MUL_WEAK ----> vASM_REWRITE_TAC[];
      vREWRITE_TAC[vREAL_MUL_ASSOC] ----> vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
      vREWRITE_TAC[vREAL_MUL_ASSOC] ---->
      vGEN_REWRITE_TAC vRAND_CONV [vGSYM vREAL_MUL_LID] ---->
      vAP_THM_TAC ----> vAP_TERM_TAC ---->
      vMATCH_MP_TAC vREAL_MUL_LINV ----> vASM_REWRITE_TAC[]]] ---->
  vSUBGOAL_THEN
    [%q {|?e. &0 < e /\
         !y. &0 < abs(y - f(x:real)) /\ abs(y - f(x)) < e ==> (f(g(y)) = y)|} ]
  (vX_CHOOSE_THEN [%q {|c:real|} ] vSTRIP_ASSUME_TAC) ++-->
   [vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|g:real->real|} ]; [%q {|x:real|} ]; [%q {|d:real|} ]]
      vCONT_INJ_RANGE) ----> vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vX_GEN_TAC [%q {|y:real|} ] ----> vDISCH_THEN(vMP_TAC -| vCONJUNCT2) ---->
    vDISCH_THEN(vMP_TAC -| vMATCH_MP vREAL_LT_IMP_LE) ---->
    vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vSTRIP_ASSUME_TAC) ---->
    vUNDISCH_TAC [%q {|(f:real->real)(z) = y|} ] ---->
    vDISCH_THEN(vSUBST1_TAC -| vSYM) ----> vAP_TERM_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vSUBGOAL_THEN
    [%q {|?e. &0 < e /\
         !y. &0 < abs(y - f(x:real)) /\ abs(y - f(x)) < e
                    ==> ~((h:real->real)(g(y)) = &0)|} ]
  (vX_CHOOSE_THEN [%q {|b:real|} ] vSTRIP_ASSUME_TAC) ++-->
   [vALL_TAC;
    vMP_TAC(vSPECL [[%q {|b:real|} ]; [%q {|c:real|} ]] vREAL_DOWN2) ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vX_GEN_TAC [%q {|y:real|} ] ----> vSTRIP_TAC ----> vCONJ_TAC ---->
    vFIRST_ASSUM vMATCH_MP_TAC ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vREAL_LT_TRANS ----> vEXISTS_TAC [%q {|e:real|} ] ---->
    vASM_REWRITE_TAC[]] ---->
  vSUBGOAL_THEN [%q {|(\y. h(g(y:real):real)) contl (f(x:real))|} ] vMP_TAC ++-->
   [vMATCH_MP_TAC vCONT_COMPOSE ----> vASM_REWRITE_TAC[] ---->
    vMATCH_MP_TAC vCONT_INVERSE ----> vEXISTS_TAC [%q {|d:real|} ] ---->
    vASM_REWRITE_TAC[]; vALL_TAC] ---->
  vREWRITE_TAC[vCONTL_LIM; vLIM] ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|abs(l)|} ]) ---->
  vASM_REWRITE_TAC[vGSYM vABS_NZ] ----> vBETA_TAC ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[vABS_NZ] ----> vX_GEN_TAC [%q {|y:real|} ] ---->
  vRULE_ASSUM_TAC(vREWRITE_RULE[vABS_NZ]) ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM(vMP_TAC -| vC vMATCH_MP th)) ---->
  vREWRITE_TAC[vGSYM vABS_NZ] ---->
  vCONV_TAC vCONTRAPOS_CONV ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN vSUBST1_TAC ---->
  vREWRITE_TAC[vREAL_SUB_LZERO; vABS_NEG; vREAL_LT_REFL]);;

let%a vDIFF_INVERSE_LT = prove(
  [%q {|!f g l x d. &0 < d /\
               (!z. abs(z - x) < d ==> (g(f(z)) = z)) /\
               (!z. abs(z - x) < d ==> f contl z) /\
               (f diffl l)(x) /\
               ~(l = &0)
        ==> (g diffl (inv l))(f x)|} ],
  vREPEAT vSTRIP_TAC ----> vMATCH_MP_TAC vDIFF_INVERSE ---->
  vEXISTS_TAC [%q {|d / &2|} ] ----> vASM_REWRITE_TAC[vREAL_LT_HALF1] ---->
  vREPEAT vSTRIP_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|d / &2|} ] ---->
  vASM_REWRITE_TAC[vREAL_LT_HALF2]);;

(* ------------------------------------------------------------------------- *)
(* Every derivative is Darboux continuous.                                   *)
(* ------------------------------------------------------------------------- *)

let%a vIVT_DERIVATIVE_0 = prove
 ([%q {|!f f' a b.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > &0 /\ f'(b) < &0
        ==> ?z. a < z /\ z < b /\ (f'(z) = &0)|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[real_gt] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vLAND_CONV) [vREAL_LE_LT] ---->
  vSTRIP_TAC ++--> [vALL_TAC; vASM_MESON_TAC[vREAL_LT_ANTISYM]] ---->
  vSUBGOAL_THEN [%q {|?w. (!x. a <= x /\ x <= b ==> f x <= w) /\
                    (?x. a <= x /\ x <= b /\ (f x = w))|} ]
  vMP_TAC ++-->
   [vMATCH_MP_TAC vCONT_ATTAINS ---->
    vASM_MESON_TAC[vREAL_LT_IMP_LE; vDIFF_CONT]; vALL_TAC] ---->
  vDISCH_THEN(vCHOOSE_THEN (vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC)) ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|z:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|z:real|} ] ----> vASM_CASES_TAC [%q {|z:real = a|} ] ++-->
   [vUNDISCH_THEN [%q {|z:real = a|} ] vSUBST_ALL_TAC  ---->
    vMP_TAC(vSPECL[[%q {|f:real->real|} ]; [%q {|a:real|} ]; [%q {|(f':real->real) a|} ]] vDIFF_LINC) ---->
    vASM_SIMP_TAC[vREAL_LE_REFL; vREAL_LT_IMP_LE] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
    vMP_TAC(vSPECL [[%q {|d:real|} ]; [%q {|b - a|} ]] vREAL_DOWN2) ---->
    vASM_REWRITE_TAC[vREAL_LT_SUB_LADD; vREAL_ADD_LID] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vSTRIP_ASSUME_TAC) ---->
    vUNDISCH_TAC [%q {|!h. &0 < h /\ h < d ==> w < f (a + h)|} ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e:real|} ]) ----> vASM_REWRITE_TAC[] ---->
    vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_THEN(vK vALL_TAC) ---->
    vREWRITE_TAC[vREAL_NOT_LT] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
    vASM_SIMP_TAC[vREAL_LE_ADDL; vREAL_LT_IMP_LE]; vALL_TAC] ---->
  vASM_CASES_TAC [%q {|z:real = b|} ] ++-->
   [vUNDISCH_THEN [%q {|z:real = b|} ] vSUBST_ALL_TAC  ---->
    vMP_TAC(vSPECL[[%q {|f:real->real|} ]; [%q {|b:real|} ]; [%q {|(f':real->real) b|} ]] vDIFF_LDEC) ---->
    vASM_SIMP_TAC[vREAL_LE_REFL; vREAL_LT_IMP_LE] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
    vMP_TAC(vSPECL [[%q {|d:real|} ]; [%q {|b - a|} ]] vREAL_DOWN2) ---->
    vASM_REWRITE_TAC[vREAL_LT_SUB_LADD; vREAL_ADD_LID] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vSTRIP_ASSUME_TAC) ---->
    vUNDISCH_TAC [%q {|!h. &0 < h /\ h < d ==> w < f (b - h)|} ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e:real|} ]) ----> vASM_REWRITE_TAC[] ---->
    vCONV_TAC vCONTRAPOS_CONV ----> vDISCH_THEN(vK vALL_TAC) ---->
    vREWRITE_TAC[vREAL_NOT_LT] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vREWRITE_TAC[vREAL_LE_SUB_LADD; vREAL_LE_SUB_RADD] ---->
    vONCE_REWRITE_TAC[vREAL_ADD_SYM] ---->
    vASM_SIMP_TAC[vREAL_LE_ADDL; vREAL_LT_IMP_LE]; vALL_TAC] ---->
  vSUBGOAL_THEN [%q {|a < z /\ z < b|} ] vSTRIP_ASSUME_TAC ++-->
   [vASM_REWRITE_TAC[vREAL_LT_LE]; vALL_TAC] ---->
  vASM_REWRITE_TAC[] ----> vMATCH_MP_TAC vDIFF_LMAX ---->
  vMP_TAC(vSPECL [[%q {|z - a|} ]; [%q {|b - z|} ]] vREAL_DOWN2) ---->
  vASM_REWRITE_TAC[vREAL_LT_SUB_LADD; vREAL_ADD_LID] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|e:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMAP_EVERY vEXISTS_TAC [[%q {|f:real->real|} ]; [%q {|z:real|} ]] ---->
  vASM_SIMP_TAC[vREAL_LT_IMP_LE] ---->
  vEXISTS_TAC [%q {|e:real|} ] ----> vASM_REWRITE_TAC[] ----> vGEN_TAC ---->
  vDISCH_THEN(fun th -> vFIRST_ASSUM vMATCH_MP_TAC ----> vMP_TAC th) ---->
  vMAP_EVERY vUNDISCH_TAC [[%q {|e + z < b|} ]; [%q {|e + a < z|} ]] ---->
  vREAL_ARITH_TAC);;

let%a vIVT_DERIVATIVE_POS = prove
 ([%q {|!f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) > y /\ f'(b) < y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)|} ],
  vREWRITE_TAC[real_gt] ----> vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|\x. f(x) - y * x|} ]; [%q {|\x:real. f'(x) - y|} ];
                [%q {|a:real|} ]; [%q {|b:real|} ]] vIVT_DERIVATIVE_0) ---->
  vASM_REWRITE_TAC[real_gt] ---->
  vASM_REWRITE_TAC[vREAL_LT_SUB_LADD; vREAL_LT_SUB_RADD] ---->
  vASM_REWRITE_TAC[vREAL_EQ_SUB_RADD; vREAL_ADD_LID] ---->
  vGEN_REWRITE_TAC (funpow 2 vLAND_CONV -| vBINDER_CONV -| vRAND_CONV -|
                   vLAND_CONV -| vRAND_CONV) [vGSYM vREAL_MUL_RID] ---->
  vASM_SIMP_TAC[vDIFF_SUB; vDIFF_X; vDIFF_CMUL]);;

let%a vIVT_DERIVATIVE_NEG = prove
 ([%q {|!f f' a b y.
        a <= b /\
        (!x. a <= x /\ x <= b ==> (f diffl f'(x))(x)) /\
        f'(a) < y /\ f'(b) > y
        ==> ?z. a < z /\ z < b /\ (f'(z) = y)|} ],
  vREWRITE_TAC[real_gt] ----> vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPECL [[%q {|\x:real. --(f x)|} ]; [%q {|\x:real. --(f' x)|} ];
                [%q {|a:real|} ]; [%q {|b:real|} ]; [%q {|--y|} ]] vIVT_DERIVATIVE_POS) ---->
  vASM_REWRITE_TAC[real_gt; vREAL_LT_NEG2; vREAL_EQ_NEG2] ---->
  vASM_SIMP_TAC[vDIFF_NEG]);;

(* ------------------------------------------------------------------------- *)
(* Uniformly convergent sequence of continuous functions is continuous.      *)
(* (Continuity at a point; uniformity in some neighbourhood of that point.)  *)
(* ------------------------------------------------------------------------- *)

let%a vSEQ_CONT_UNIFORM = prove
 ([%q {|!s f x0. (!e. &0 < e
                 ==> ?N d. &0 < d /\
                           !x n. abs(x - x0) < d /\ n >= N
                                 ==> abs(s n x - f(x)) < e) /\
            (?N:num. !n. n >= N ==> (s n) contl x0)
            ==> f contl x0|} ],
  vREPEAT vGEN_TAC ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vX_CHOOSE_TAC [%q {|M:num|} ])) ---->
  vREWRITE_TAC[vCONTL_LIM; vLIM] ----> vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|e / &3|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH; vLEFT_IMP_EXISTS_THM] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|N:num|} ]; [%q {|d1:real|} ]] ----> vSTRIP_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|M + N:num|} ]) ----> vREWRITE_TAC[vGE; vLE_ADD] ---->
  vREWRITE_TAC[vCONTL_LIM; vLIM] ----> vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &3|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d2:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|d1:real|} ]; [%q {|d2:real|} ]] vREAL_DOWN2) ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|d:real|} ] ----> vSTRIP_TAC ---->
  vASM_REWRITE_TAC[] ----> vX_GEN_TAC [%q {|x:real|} ] ----> vSTRIP_TAC ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|!fx sx fx0 sx0 e3.
        abs(sx - fx) < e3 /\ abs(sx0 - fx0) < e3 /\ abs(sx - sx0) < e3 /\
        (&3 * e3 = e)
        ==> abs(fx - fx0) < e|} ]) ---->
  vMAP_EVERY vEXISTS_TAC
   [[%q {|(s:num->real->real) (M + N) x|} ];
    [%q {|(s:num->real->real) (M + N) x0|} ];
    [%q {|e / &3|} ]] ---->
  vASM_SIMP_TAC[vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH] ---->
  vASM_MESON_TAC[vREAL_SUB_REFL; vREAL_ABS_NUM; vREAL_LT_TRANS;
                vARITH_RULE [%q {|M + N >= N:num|} ]]);;

(* ------------------------------------------------------------------------- *)
(* Comparison test gives uniform convergence of sum in a neighbourhood.      *)
(* ------------------------------------------------------------------------- *)

let%a vSER_COMPARA_UNIFORM = prove
 ([%q {|!s x0 g.
        (?N d. &0 < d /\
               !n x. abs(x - x0) < d /\ n >= N
                     ==> abs(s x n) <= g n) /\ summable g
        ==> ?f d. &0 < d /\
                  !e. &0 < e
                      ==> ?N. !x n. abs(x - x0) < d /\ n >= N
                                    ==> abs(sum(0,n) (s x) - f(x)) < e|} ],
  vREPEAT vSTRIP_TAC ---->
  vSUBGOAL_THEN [%q {|!x. abs(x - x0) < d ==> ?y. (s x) sums y|} ] vMP_TAC ++-->
   [vASM_MESON_TAC[summable; vSER_COMPAR]; vALL_TAC] ---->
  vGEN_REWRITE_TAC (vLAND_CONV -| vTOP_DEPTH_CONV)
      [vRIGHT_IMP_EXISTS_THM; vSKOLEM_THM] ---->
  vMATCH_MP_TAC vMONO_EXISTS ----> vX_GEN_TAC [%q {|f:real->real|} ] ----> vDISCH_TAC ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vX_GEN_TAC [%q {|e:real|} ] ----> vDISCH_TAC ---->
  vFIRST_X_ASSUM(vMP_TAC -| vGEN_REWRITE_RULE vI [vSER_CAUCHY]) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vX_CHOOSE_TAC [%q {|M:num|} ]) ---->
  vEXISTS_TAC [%q {|M + N:num|} ] ----> vASM_REWRITE_TAC[] ---->
  vMAP_EVERY vX_GEN_TAC [[%q {|x:real|} ]; [%q {|n:num|} ]] ----> vSTRIP_TAC ---->
  vFIRST_ASSUM(vSTRIP_ASSUME_TAC -| vMATCH_MP (vARITH_RULE
   [%q {|n >= M + N ==> n >= M /\ n >= N:num|} ])) ---->
  vFIRST_X_ASSUM(vMP_TAC -| vSPEC [%q {|x:real|} ]) ----> vASM_REWRITE_TAC[sums; vSEQ] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|m:num|} ] (vMP_TAC -| vSPEC [%q {|m + n:num|} ])) ---->
  vREWRITE_TAC[vGE; vLE_ADD] ----> vONCE_REWRITE_TAC[vADD_SYM] ---->
  vONCE_REWRITE_TAC[vGSYM vSUM_TWO] ---->
  vMATCH_MP_TAC(vREAL_ARITH
   [%q {|abs(snm) < e2 /\ (&2 * e2 = e)
    ==> abs((sn + snm) - fx) < e2 ==> abs(sn - fx) < e|} ]) ---->
  vSIMP_TAC[vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH] ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ---->
  vEXISTS_TAC [%q {|sum(n,m) (\n. abs(s (x:real) n))|} ] ---->
  vREWRITE_TAC[vSUM_ABS_LE] ---->
  vMATCH_MP_TAC vREAL_LET_TRANS ----> vEXISTS_TAC [%q {|sum(n,m) g|} ] ----> vCONJ_TAC ++-->
   [vMATCH_MP_TAC vSUM_LE ----> vX_GEN_TAC [%q {|r:num|} ] ----> vSTRIP_TAC ---->
    vREWRITE_TAC[] ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
    vASM_MESON_TAC[vGE; vLE_TRANS]; vALL_TAC] ---->
  vMATCH_MP_TAC(vREAL_ARITH [%q {|abs(x) < a ==> x < a|} ]) ----> vASM_SIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* A weaker variant matching the requirement for continuity of limit.        *)
(* ------------------------------------------------------------------------- *)

let%a vSER_COMPARA_UNIFORM_WEAK = prove
 ([%q {|!s x0 g.
        (?N d. &0 < d /\
               !n x. abs(x - x0) < d /\ n >= N
                     ==> abs(s x n) <= g n) /\ summable g
        ==> ?f. !e. &0 < e
                    ==> ?N d. &0 < d /\
                              !x n. abs(x - x0) < d /\ n >= N
                                    ==> abs(sum(0,n) (s x) - f(x)) < e|} ],
  vREPEAT vGEN_TAC ----> vDISCH_THEN(vMP_TAC -| vMATCH_MP vSER_COMPARA_UNIFORM) ---->
  vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* More convenient formulation of continuity.                                *)
(* ------------------------------------------------------------------------- *)

let%a vCONTL = prove
 ([%q {|!f x. f contl x <=>
         !e. &0 < e ==> ?d. &0 < d /\ !x'. abs(x' - x) < d
                            ==> abs(f(x') - f(x)) < e|} ],
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vCONTL_LIM; vLIM] ---->
  vREWRITE_TAC[vREAL_ARITH [%q {|&0 < abs(x - y) <=> ~(x = y)|} ]] ---->
  vAP_TERM_TAC ----> vABS_TAC ---->
  vMATCH_MP_TAC(vTAUT [%q {|(a ==> (b <=> c)) ==> ((a ==> b) <=> (a ==> c))|} ]) ---->
  vDISCH_TAC ----> vAP_TERM_TAC ----> vABS_TAC ---->
  vAP_TERM_TAC ----> vAP_TERM_TAC ----> vABS_TAC ---->
  vASM_MESON_TAC[vREAL_ARITH [%q {|abs(x - x) = &0|} ]]);;

(* ------------------------------------------------------------------------- *)
(* Of course we also have this and similar results for sequences.            *)
(* ------------------------------------------------------------------------- *)

let%a vCONTL_SEQ = prove
 ([%q {|!f x l. f contl l /\ x tends_num_real l

           ==> (\n. f(x n)) tends_num_real f(l)|} ],
  vREWRITE_TAC[vCONTL; vSEQ] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Uniformity of continuity over closed interval.                            *)
(* ------------------------------------------------------------------------- *)

let%a vSUP_INTERVAL = prove
 ([%q {|!P a b.
        (?x. a <= x /\ x <= b /\ P x)
        ==> ?s. a <= s /\ s <= b /\
                !y. y < s <=> (?x. a <= x /\ x <= b /\ P x /\ y < x)|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|\x. a <= x /\ x <= b /\ P x|} ] vREAL_SUP) ----> vANTS_TAC ++-->
   [vASM_REWRITE_TAC[] ---->
    vASM_MESON_TAC[vARITH_RULE [%q {|x <= b ==> x < b + &1|} ]];
    vALL_TAC] ---->
  vABBREV_TAC [%q {|s = sup (\x. a <= x /\ x <= b /\ P x)|} ] ---->
  vREWRITE_TAC[] ----> vDISCH_TAC ----> vEXISTS_TAC [%q {|s:real|} ] ---->
  vASM_REWRITE_TAC[] ---->
  vASM_MESON_TAC[vREAL_LTE_TRANS; vREAL_NOT_LE; vREAL_LT_ANTISYM]);;

let%a vCONT_UNIFORM = prove
 ([%q {|!f a b. a <= b /\ (!x. a <= x /\ x <= b ==> f contl x)
           ==> !e. &0 < e ==> ?d. &0 < d /\
                                  !x y. a <= x /\ x <= b /\
                                        a <= y /\ y <= b /\
                                        abs(x - y) < d
                                        ==> abs(f(x) - f(y)) < e|} ],
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC [%q {|\c. ?d. &0 < d /\
                       !x y. a <= x /\ x <= c /\
                             a <= y /\ y <= c /\
                             abs(x - y) < d
                             ==> abs(f(x) - f(y)) < e|} ]
         vSUP_INTERVAL) ---->
  vDISCH_THEN(vMP_TAC -| vSPECL [[%q {|a:real|} ]; [%q {|b:real|} ]]) ----> vANTS_TAC ++-->
   [vEXISTS_TAC [%q {|a:real|} ] ----> vASM_REWRITE_TAC[vREAL_LE_REFL] ---->
    vREPEAT vSTRIP_TAC ----> vEXISTS_TAC [%q {|&1|} ] ---->
    vREWRITE_TAC[vREAL_OF_NUM_LT; vARITH] ---->
    vASM_MESON_TAC[vREAL_LE_ANTISYM; vREAL_ARITH [%q {|abs(x - x) = &0|} ]];
    vALL_TAC] ---->
  vREWRITE_TAC[] ----> vDISCH_THEN(vX_CHOOSE_THEN [%q {|s:real|} ] vSTRIP_ASSUME_TAC) ---->
  vSUBGOAL_THEN [%q {|?t. s < t /\ ?d. &0 < d /\
                                 !x y. a <= x /\ x <= t /\ a <= y /\ y <= t /\
                                       abs(x - y) < d ==> abs(f(x) - f(y)) < e|} ]
  vMP_TAC ++-->
   [vUNDISCH_TAC [%q {|!x. a <= x /\ x <= b ==> f contl x|} ] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|s:real|} ]) ----> vASM_REWRITE_TAC[] ---->
    vREWRITE_TAC[vCONTL_LIM; vLIM] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
    vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d1:real|} ] vSTRIP_ASSUME_TAC) ---->
    vSUBGOAL_THEN [%q {|&0 < d1 / &2 /\ d1 / &2 < d1|} ] vSTRIP_ASSUME_TAC ++-->
     [vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH; vREAL_LT_LDIV_EQ;
                   vREAL_ARITH [%q {|d < d * &2 <=> &0 < d|} ]];
      vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|!x y. abs(x - s) < d1 /\ abs(y - s) < d1
                        ==> abs(f(x) - f(y)) < e|} ]
    vASSUME_TAC ++-->
     [vREPEAT vSTRIP_TAC ---->
      vMATCH_MP_TAC(vREAL_ARITH
       [%q {|!a. abs(x - a) < e / &2 /\ abs(y - a) < e / &2 /\ (&2 * e / &2 = e)
            ==> abs(x - y) < e|} ]) ---->
      vEXISTS_TAC [%q {|(f:real->real) s|} ] ---->
      vSIMP_TAC[vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH] ---->
      vSUBGOAL_THEN [%q {|!x. abs(x - s) < d1 ==> abs(f x - f s) < e / &2|} ]
       (fun th -> vASM_MESON_TAC[th]) ---->
      vX_GEN_TAC [%q {|u:real|} ] ---->
      vREPEAT vSTRIP_TAC ----> vASM_CASES_TAC [%q {|u:real = s|} ] ++-->
       [vASM_SIMP_TAC[vREAL_SUB_REFL; vREAL_ABS_NUM; vREAL_LT_DIV;
                     vREAL_OF_NUM_LT; vARITH];
        vALL_TAC] ---->
      vASM_MESON_TAC[vREAL_ARITH [%q {|&0 < abs(x - s) <=> ~(x = s)|} ]];
      vALL_TAC] ---->
    vSUBGOAL_THEN [%q {|s - d1 / &2 < s|} ] vMP_TAC ++-->
     [vASM_REWRITE_TAC[vREAL_ARITH [%q {|x - y < x <=> &0 < y|} ]];
      vALL_TAC] ---->
    vDISCH_THEN(fun th -> vFIRST_ASSUM(fun th' ->
      vMP_TAC(vGEN_REWRITE_RULE vI [th'] th))) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|r:real|} ] vMP_TAC) ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC vMP_TAC) ---->
    vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d2:real|} ] vSTRIP_ASSUME_TAC) ---->
    vMP_TAC(vSPECL [[%q {|d2:real|} ]; [%q {|d1 / &2|} ]] vREAL_DOWN2) ---->
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
    vEXISTS_TAC [%q {|s + d / &2|} ] ---->
    vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH;
                 vREAL_ARITH [%q {|s < s + d <=> &0 < d|} ]] ---->
    vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ---->
    vMAP_EVERY vX_GEN_TAC [[%q {|x:real|} ]; [%q {|y:real|} ]] ----> vSTRIP_TAC ---->
    vASM_CASES_TAC [%q {|x <= r /\ y <= r|} ] ++-->
     [vASM_MESON_TAC[vREAL_LT_TRANS]; vALL_TAC] ---->
    vMATCH_MP_TAC(vASSUME
     [%q {|!x y. abs(x - s) < d1 /\ abs(y - s) < d1 ==> abs(f x - f y) < e|} ]) ---->
    vMATCH_MP_TAC(vREAL_ARITH
     [%q {|!r t d d12.
       ~(x <= r /\ y <= r) /\
      abs(x - y) < d /\
      s - d12 < r /\ t <= s + d /\
      x <= t /\ y <= t /\ &2 * d12 <= e /\
      &2 * d < e ==> abs(x - s) < e /\ abs(y - s) < e|} ]) ---->
    vMAP_EVERY vEXISTS_TAC [[%q {|r:real|} ]; [%q {|s + d / &2|} ]; [%q {|d:real|} ]; [%q {|d1 / &2|} ]] ---->
    vASM_REWRITE_TAC[vREAL_LE_LADD] ---->
    vSIMP_TAC[vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH] ---->
    vONCE_REWRITE_TAC[vREAL_MUL_SYM] ---->
    vSIMP_TAC[vREAL_LE_LDIV_EQ; vGSYM vREAL_LT_RDIV_EQ; vREAL_OF_NUM_LT; vARITH] ---->
    vASM_SIMP_TAC[vREAL_ARITH [%q {|&0 < d ==> d <= d * &2|} ]; vREAL_LE_REFL];
    vALL_TAC] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|t:real|} ] (vCONJUNCTS_THEN vASSUME_TAC)) ---->
  vSUBGOAL_THEN [%q {|b <= t|} ] (fun th -> vASM_MESON_TAC[vREAL_LE_TRANS; th]) ---->
  vFIRST_X_ASSUM(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vUNDISCH_THEN [%q {|!x. a <= x /\ x <= b ==> f contl x|} ] (vK vALL_TAC) ---->
  vFIRST_X_ASSUM(vMP_TAC -| check(is_eq -| concl) -| vSPEC [%q {|s:real|} ]) ---->
  vREWRITE_TAC[vREAL_LT_REFL] ---->
  vONCE_REWRITE_TAC[vGSYM vCONTRAPOS_THM] ----> vREWRITE_TAC[vREAL_NOT_LE] ---->
  vDISCH_TAC ----> vEXISTS_TAC [%q {|t:real|} ] ---->
  vASM_MESON_TAC[vREAL_LT_IMP_LE; vREAL_LE_TRANS]);;

(* ------------------------------------------------------------------------- *)
(* Slightly stronger version exploiting 2-sided continuity at ends.          *)
(* ------------------------------------------------------------------------- *)

let%a vCONT_UNIFORM_STRONG = prove
 ([%q {|!f a b. (!x. a <= x /\ x <= b ==> f contl x)
           ==> !e. &0 < e
                   ==> ?d. &0 < d /\
                           !x y. (a <= x /\ x <= b \/ a <= y /\ y <= b) /\
                                 abs(x - y) < d
                                 ==> abs(f(x) - f(y)) < e|} ],
  vREPEAT vSTRIP_TAC ---->
  vASM_CASES_TAC [%q {|a <= b|} ] ++-->
   [vALL_TAC; vASM_MESON_TAC[vREAL_LE_TRANS; vREAL_LT_01]] ---->
  vFIRST_ASSUM(fun th ->
    vMP_TAC(vSPEC [%q {|a:real|} ] th) ----> vMP_TAC(vSPEC [%q {|b:real|} ] th)) ---->
  vREWRITE_TAC[vCONTL; vREAL_LE_REFL] ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d1:real|} ] vSTRIP_ASSUME_TAC) ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e / &2|} ]) ---->
  vASM_SIMP_TAC[vREAL_LT_DIV; vREAL_OF_NUM_LT; vARITH] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d2:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|d1:real|} ]; [%q {|d2:real|} ]] vREAL_DOWN2) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d0:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|f:real->real|} ]; [%q {|a:real|} ]; [%q {|b:real|} ]] vCONT_UNIFORM) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vMP_TAC -| vSPEC [%q {|e:real|} ]) ----> vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d3:real|} ] vSTRIP_ASSUME_TAC) ---->
  vMP_TAC(vSPECL [[%q {|d0:real|} ]; [%q {|d3:real|} ]] vREAL_DOWN2) ---->
  vASM_REWRITE_TAC[] ---->
  vDISCH_THEN(vX_CHOOSE_THEN [%q {|d:real|} ] vSTRIP_ASSUME_TAC) ---->
  vEXISTS_TAC [%q {|d:real|} ] ----> vASM_REWRITE_TAC[] ---->
  vMATCH_MP_TAC vREAL_WLOG_LE ----> vCONJ_TAC ++-->
   [vMESON_TAC[vREAL_ABS_SUB]; vALL_TAC] ---->
  vREPEAT vSTRIP_TAC ++-->
   [vASM_CASES_TAC [%q {|y <= b|} ] ++-->
     [vASM_MESON_TAC[vREAL_LT_TRANS; vREAL_LE_TRANS]; vALL_TAC] ---->
    vMATCH_MP_TAC(vREAL_ARITH
     [%q {|!a. abs(x - a) < e / &2 /\ abs(y - a) < e / &2 /\ (&2 * e / &2 = e)
          ==> abs(x - y) < e|} ]) ---->
    vEXISTS_TAC [%q {|(f:real->real) b|} ] ---->
    vSIMP_TAC[vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH_EQ] ---->
    vASM_MESON_TAC[vREAL_LT_TRANS; vREAL_ARITH
     [%q {|x <= b /\ ~(y <= b) /\ abs(x - y) < d /\ d < d1
      ==> abs(x - b) < d1 /\ abs(y - b) < d1|} ]];
    vASM_CASES_TAC [%q {|a <= x|} ] ++-->
     [vASM_MESON_TAC[vREAL_LT_TRANS; vREAL_LE_TRANS]; vALL_TAC] ---->
    vMATCH_MP_TAC(vREAL_ARITH
     [%q {|!a. abs(x - a) < e / &2 /\ abs(y - a) < e / &2 /\ (&2 * e / &2 = e)
          ==> abs(x - y) < e|} ]) ---->
    vEXISTS_TAC [%q {|(f:real->real) a|} ] ---->
    vSIMP_TAC[vREAL_DIV_LMUL; vREAL_OF_NUM_EQ; vARITH_EQ] ---->
    vASM_MESON_TAC[vREAL_LT_TRANS; vREAL_ARITH
     [%q {|~(a <= x) /\ a <= y /\ abs(x - y) < d /\ d < d1
      ==> abs(x - a) < d1 /\ abs(y - a) < d1|} ]]]);;

(* ------------------------------------------------------------------------- *)
(* Get rid of special syntax status of '-->'.                                *)
(* ------------------------------------------------------------------------- *)

remove_interface "-->";;
