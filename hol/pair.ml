(* ========================================================================= *)
(* Syntax sugaring; theory of pairing, with a bit of support.                *)
(*                                                                           *)
(*       John Harrison, University of Cambridge Computer Laboratory          *)
(*                                                                           *)
(*            (c) Copyright, University of Cambridge 1998                    *)
(*              (c) Copyright, John Harrison 1998-2007                       *)
(*                 (c) Copyright, Marco Maggesi 2015                         *)
(* ========================================================================= *)

open Lib
open Fusion
open Basics
open Printer
open Parser
open Equal
open Boolean
open Drule
open Tactics
open Simp
open Theorems
open Class
open Trivia
open Canon
open Meson

(* ------------------------------------------------------------------------- *)
(* Constants implementing (or at least tagging) syntactic sugar.             *)
(* ------------------------------------------------------------------------- *)

let vLET_DEF = new_definition
 (parse_term "LET (f:A->B) x = f x");;

let vLET_END_DEF = new_definition
 (parse_term "LET_END (t:A) = t");;

let vGABS_DEF = new_definition
 (parse_term "GABS (P:A->bool) = (@) P");;

let vGEQ_DEF = new_definition
 (parse_term "GEQ a b = (a:A = b)");;

let _SEQPATTERN = new_definition
 (parse_term "_SEQPATTERN = \\r s x. if ?y. r x y then r x else s x");;

let _UNGUARDED_PATTERN = new_definition
 (parse_term "_UNGUARDED_PATTERN = \\p r. p /\\ r");;

let _GUARDED_PATTERN = new_definition
 (parse_term "_GUARDED_PATTERN = \\p g r. p /\\ g /\\ r");;

let _MATCH = new_definition
 (parse_term "_MATCH =  \\e r. if (?!) (r e) then (@) (r e) else @z. F");;

let _FUNCTION = new_definition
 (parse_term "_FUNCTION = \\r x. if (?!) (r x) then (@) (r x) else @z. F");;

(* ------------------------------------------------------------------------- *)
(* Pair type.                                                                *)
(* ------------------------------------------------------------------------- *)

let mk_pair_def = new_definition
  (parse_term "mk_pair (x:A) (y:B) = \\a b. (a = x) /\\ (b = y)");;

let vPAIR_EXISTS_THM = try Cache.lookup_thm "PAIR_EXISTS_THM" with _ ->  prove
 ((parse_term "?x. ?(a:A) (b:B). x = mk_pair a b"),
  vMESON_TAC[]);;

let prod_tybij = new_type_definition
  "prod" ("ABS_prod","REP_prod") vPAIR_EXISTS_THM;;

let vREP_ABS_PAIR = try Cache.lookup_thm "REP_ABS_PAIR" with _ ->  prove
 ((parse_term "!(x:A) (y:B). REP_prod (ABS_prod (mk_pair x y)) = mk_pair x y"),
  vMESON_TAC[prod_tybij]);;

parse_as_infix (",",(14,"right"));;

let vCOMMA_DEF = new_definition
 (parse_term "(x:A),(y:B) = ABS_prod(mk_pair x y)");;

let vFST_DEF = new_definition
 (parse_term "FST (p:A#B) = @x. ?y. p = x,y");;

let vSND_DEF = new_definition
 (parse_term "SND (p:A#B) = @y. ?x. p = x,y");;

let vPAIR_EQ = try Cache.lookup_thm "PAIR_EQ" with _ ->  prove
 ((parse_term "!(x:A) (y:B) a b. (x,y = a,b) <=> (x = a) /\\ (y = b)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vREWRITE_TAC[vCOMMA_DEF] ---->
    vDISCH_THEN(vMP_TAC -| vAP_TERM (parse_term "REP_prod:A#B->A->B->bool")) ---->
    vREWRITE_TAC[vREP_ABS_PAIR] ----> vREWRITE_TAC[mk_pair_def; vFUN_EQ_THM];
    vALL_TAC] ---->
  vMESON_TAC[]);;

let vPAIR_SURJECTIVE = try Cache.lookup_thm "PAIR_SURJECTIVE" with _ ->  prove
 ((parse_term "!p:A#B. ?x y. p = x,y"),
  vGEN_TAC ----> vREWRITE_TAC[vCOMMA_DEF] ---->
  vMP_TAC(vSPEC (parse_term "REP_prod p :A->B->bool") (vCONJUNCT2 prod_tybij)) ---->
  vREWRITE_TAC[vCONJUNCT1 prod_tybij] ---->
  vDISCH_THEN(vX_CHOOSE_THEN (parse_term "a:A") (vX_CHOOSE_THEN (parse_term "b:B") vMP_TAC)) ---->
  vDISCH_THEN(vMP_TAC -| vAP_TERM (parse_term "ABS_prod:(A->B->bool)->A#B")) ---->
  vREWRITE_TAC[vCONJUNCT1 prod_tybij] ----> vDISCH_THEN vSUBST1_TAC ---->
  vMAP_EVERY vEXISTS_TAC [(parse_term "a:A"); (parse_term "b:B")] ----> vREFL_TAC);;

let vFST = try Cache.lookup_thm "FST" with _ ->  prove
 ((parse_term "!(x:A) (y:B). FST(x,y) = x"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vFST_DEF] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ----> vGEN_TAC ----> vBETA_TAC ---->
  vREWRITE_TAC[vPAIR_EQ] ----> vEQ_TAC ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "y:B") ----> vASM_REWRITE_TAC[]);;

let vSND = try Cache.lookup_thm "SND" with _ ->  prove
 ((parse_term "!(x:A) (y:B). SND(x,y) = y"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vSND_DEF] ---->
  vMATCH_MP_TAC vSELECT_UNIQUE ----> vGEN_TAC ----> vBETA_TAC ---->
  vREWRITE_TAC[vPAIR_EQ] ----> vEQ_TAC ---->
  vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vEXISTS_TAC (parse_term "x:A") ----> vASM_REWRITE_TAC[]);;

let vPAIR = try Cache.lookup_thm "PAIR" with _ ->  prove
 ((parse_term "!x:A#B. FST x,SND x = x"),
  vGEN_TAC ---->
  (vX_CHOOSE_THEN (parse_term "a:A") (vX_CHOOSE_THEN (parse_term "b:B") vSUBST1_TAC)
     (vSPEC (parse_term "x:A#B") vPAIR_SURJECTIVE)) ---->
  vREWRITE_TAC[vFST; vSND]);;

let pair_INDUCT = try Cache.lookup_thm "pair_INDUCT" with _ ->  prove
 ((parse_term "!P. (!x y. P (x,y)) ==> !p. P p"),
  vREPEAT vSTRIP_TAC ---->
  vGEN_REWRITE_TAC vRAND_CONV [vGSYM vPAIR] ---->
  vFIRST_ASSUM vMATCH_ACCEPT_TAC);;

let pair_RECURSION = try Cache.lookup_thm "pair_RECURSION" with _ ->  prove
 ((parse_term "!PAIR'. ?fn:A#B->C. !a0 a1. fn (a0,a1) = PAIR' a0 a1"),
  vGEN_TAC ----> vEXISTS_TAC (parse_term "\\p. (PAIR':A->B->C) (FST p) (SND p)") ---->
  vREWRITE_TAC[vFST; vSND]);;

(* ------------------------------------------------------------------------- *)
(* Syntax operations.                                                        *)
(* ------------------------------------------------------------------------- *)

let is_pair = is_binary ",";;

let dest_pair = dest_binary ",";;

let mk_pair =
  let ptm = mk_const(",",[]) in
  fun (l,r) -> mk_comb(mk_comb(inst [type_of l,aty; type_of r,bty] ptm,l),r);;

(* ------------------------------------------------------------------------- *)
(* Extend basic rewrites; extend new_definition to allow paired varstructs.  *)
(* ------------------------------------------------------------------------- *)

extend_basic_rewrites [vFST; vSND; vPAIR];;

(* ------------------------------------------------------------------------- *)
(* Extend definitions to paired varstructs with benignity checking.          *)
(* ------------------------------------------------------------------------- *)

let the_definitions = ref
 [vSND_DEF; vFST_DEF; vCOMMA_DEF; mk_pair_def; vGEQ_DEF; vGABS_DEF;
  vLET_END_DEF; vLET_DEF; one_DEF; vI_DEF; o_DEF; vCOND_DEF; _FALSITY_;
  vEXISTS_UNIQUE_DEF; vNOT_DEF; vF_DEF; vOR_DEF; vEXISTS_DEF; vFORALL_DEF; vIMP_DEF;
  vAND_DEF; vT_DEF];;

let new_definition =
  let depair =
    let rec depair gv arg =
      try let l,r = dest_pair arg in
          (depair (list_mk_icomb "FST" [gv]) l) @
          (depair (list_mk_icomb "SND" [gv]) r)
      with Failure _ -> [gv,arg] in
    fun arg -> let gv = genvar(type_of arg) in
               gv,depair gv arg in
  fun tm ->
    let avs,def = strip_forall tm in
    try let th,th' = tryfind (fun th -> th,vPART_MATCH vI th def)
                             (!the_definitions) in
        ignore(vPART_MATCH vI th' (snd(strip_forall(concl th))));
        warn true "Benign redefinition"; vGEN_ALL (vGENL avs th')
    with Failure _ ->
        let l,r = dest_eq def in
        let fn,args = strip_comb l in
        let gargs,reps = (vI $-$ unions) (unzip(map depair args)) in
        let l' = list_mk_comb(fn,gargs) and r' = subst reps r in
        let th1 = new_definition (mk_eq(l',r')) in
        let slist = zip args gargs in
        let th2 = vINST slist (vSPEC_ALL th1) in
        let xreps = map (subst slist -| fst) reps in
        let threps = map (vSYM -| vPURE_REWRITE_CONV[vFST; vSND]) xreps in
        let th3 = vTRANS th2 (vSYM(vSUBS_CONV threps r)) in
        let th4 = vGEN_ALL (vGENL avs th3) in
        the_definitions := th4::(!the_definitions); th4;;

(* ------------------------------------------------------------------------- *)
(* A few more useful definitions.                                            *)
(* ------------------------------------------------------------------------- *)

let vCURRY_DEF = new_definition
 (parse_term "CURRY(f:A#B->C) x y = f(x,y)");;

let vUNCURRY_DEF = new_definition
 (parse_term "!f x y. UNCURRY(f:A->B->C)(x,y) = f x y");;

let vPASSOC_DEF = new_definition
 (parse_term "!f x y z. PASSOC (f:(A#B)#C->D) (x,y,z) = f ((x,y),z)");;

(* ------------------------------------------------------------------------- *)
(* Analog of ABS_CONV for generalized abstraction.                           *)
(* ------------------------------------------------------------------------- *)

let vGABS_CONV conv tm =
  if is_abs tm then vABS_CONV conv tm else
  let gabs,bod = dest_comb tm in
  let f,qtm = dest_abs bod in
  let xs,bod = strip_forall qtm in
  vAP_TERM gabs (vABS f (itlist vMK_FORALL xs (vRAND_CONV conv bod)));;

(* ------------------------------------------------------------------------- *)
(* General beta-conversion over linear pattern of nested constructors.       *)
(* ------------------------------------------------------------------------- *)

let vGEN_BETA_CONV =
  let projection_cache = ref [] in
  let create_projections conname =
    try assoc conname (!projection_cache) with Failure _ ->
    let genty = get_const_type conname in
    let conty = fst(dest_type(repeat (snd -| dest_fun_ty) genty)) in
    let _,_,rth = assoc conty (!inductive_type_store) in
    let sth = vSPEC_ALL rth in
    let evs,bod = strip_exists(concl sth) in
    let cjs = conjuncts bod in
    let ourcj = find ((=)conname -| fst -| dest_const -| fst -| strip_comb -|
                      rand -| lhand -| snd -| strip_forall) cjs in
    let n = index ourcj cjs in
    let avs,eqn = strip_forall ourcj in
    let con',args = strip_comb(rand eqn) in
    let aargs,zargs = chop_list (length avs) args in
    let gargs = map (genvar -| type_of) zargs in
    let gcon = genvar(itlist (mk_fun_ty -| type_of) avs (type_of(rand eqn))) in
    let bth =
      vINST [list_mk_abs(aargs @ gargs,list_mk_comb(gcon,avs)),con'] sth in
    let cth = el n (vCONJUNCTS(vASSUME(snd(strip_exists(concl bth))))) in
    let dth = vCONV_RULE (funpow (length avs) vBINDER_CONV
      (vRAND_CONV(vBETAS_CONV))) cth in
    let eth = vSIMPLE_EXISTS (rator(lhand(snd(strip_forall(concl dth))))) dth in
    let fth = vPROVE_HYP bth (itlist vSIMPLE_CHOOSE evs eth) in
    let zty = type_of (rand(snd(strip_forall(concl dth)))) in
    let mk_projector a =
      let ity = type_of a in
      let th = vBETA_RULE(vPINST [ity,zty] [list_mk_abs(avs,a),gcon] fth) in
      vSYM(vSPEC_ALL(vSELECT_RULE th)) in
    let ths = map mk_projector avs in
    (projection_cache := (conname,ths)::(!projection_cache); ths) in
  let vGEQ_CONV = vREWR_CONV(vGSYM vGEQ_DEF)
  and vDEGEQ_RULE = vCONV_RULE(vREWR_CONV vGEQ_DEF) in
  let vGABS_RULE =
    let pth = prove
     ((parse_term "(?) P ==> P (GABS P)"),
      vSIMP_TAC[vGABS_DEF; vSELECT_AX; vETA_AX]) in
    vMATCH_MP pth in
  let rec create_iterated_projections tm =
    if frees tm = [] then []
    else if is_var tm then [vREFL tm] else
    let con,_args = strip_comb tm in
    let prjths = create_projections (fst(dest_const con)) in
    let atm = rand(rand(concl(hd prjths))) in
    let instn = term_match [] atm tm in
    let arths = map (vINSTANTIATE instn) prjths in
    let ths = map (fun arth ->
      let sths = create_iterated_projections (lhand(concl arth)) in
      map (vCONV_RULE(vRAND_CONV(vSUBS_CONV[arth]))) sths) arths in
    unions' equals_thm ths in
  let vGEN_BETA_CONV tm =
    try vBETA_CONV tm with Failure _ ->
    let l,r = dest_comb tm in
    let vstr,bod = dest_gabs l in
    let instn = term_match [] vstr r in
    let prjs = create_iterated_projections vstr in
    let th1 = vSUBS_CONV prjs bod in
    let bod' = rand(concl th1) in
    let gv = genvar(type_of vstr) in
    let pat = mk_abs(gv,subst[gv,vstr] bod') in
    let th2 = vTRANS (vBETA_CONV (mk_comb(pat,vstr))) (vSYM th1) in
    let avs = fst(strip_forall(body(rand l))) in
    let th3 = vGENL (fst(strip_forall(body(rand l)))) th2 in
    let efn = genvar(type_of pat) in
    let th4 = vEXISTS(mk_exists(efn,subst[efn,pat] (concl th3)),pat) th3 in
    let th5 = vCONV_RULE(funpow (length avs + 1) vBINDER_CONV vGEQ_CONV) th4 in
    let th6 = vCONV_RULE vBETA_CONV (vGABS_RULE th5) in
    vINSTANTIATE instn (vDEGEQ_RULE (vSPEC_ALL th6)) in
  vGEN_BETA_CONV;;

(* ------------------------------------------------------------------------- *)
(* Add this to the basic "rewrites" and pairs to the inductive type store.   *)
(* ------------------------------------------------------------------------- *)

extend_basic_convs("GEN_BETA_CONV",((parse_term "GABS (\\a. b) c"),vGEN_BETA_CONV));;

inductive_type_store :=
 ("prod",(1,pair_INDUCT,pair_RECURSION))::(!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* Convenient rules to eliminate binders over pairs.                         *)
(* ------------------------------------------------------------------------- *)

let vFORALL_PAIR_THM = try Cache.lookup_thm "FORALL_PAIR_THM" with _ ->  prove
 ((parse_term "!P. (!p. P p) <=> (!p1 p2. P(p1,p2))"),
  vMESON_TAC[vPAIR]);;

let vEXISTS_PAIR_THM = try Cache.lookup_thm "EXISTS_PAIR_THM" with _ ->  prove
 ((parse_term "!P. (?p. P p) <=> ?p1 p2. P(p1,p2)"),
  vMESON_TAC[vPAIR]);;

let vLAMBDA_PAIR_THM = try Cache.lookup_thm "LAMBDA_PAIR_THM" with _ ->  prove
 ((parse_term "!t. (\\p. t p) = (\\(x,y). t(x,y))"),
  vREWRITE_TAC[vFORALL_PAIR_THM; vFUN_EQ_THM]);;

let vLAMBDA_PAIR = try Cache.lookup_thm "LAMBDA_PAIR" with _ ->  prove
 ((parse_term "!f:A->B->C. (\\(x,y). f x y) = (\\p. f (FST p) (SND p))"),
  vREWRITE_TAC[vLAMBDA_PAIR_THM]);;

let vLAMBDA_TRIPLE_THM = try Cache.lookup_thm "LAMBDA_TRIPLE_THM" with _ ->  prove
 ((parse_term "!f:A#B#C->D. (\\t. f t) = (\\(x,y,z). f(x,y,z))"),
  vREWRITE_TAC[vFORALL_PAIR_THM; vFUN_EQ_THM]);;

let vLAMBDA_TRIPLE = try Cache.lookup_thm "LAMBDA_TRIPLE" with _ ->  prove
 ((parse_term "!f:A->B->C->D.\n   (\\(x,y,z). f x y z) = (\\t. f (FST t) (FST(SND t)) (SND(SND t)))"),
  vREWRITE_TAC[vLAMBDA_TRIPLE_THM]);;

let vPAIRED_ETA_THM = try Cache.lookup_thm "PAIRED_ETA_THM" with _ ->  prove
 ((parse_term "(!f. (\\(x,y). f (x,y)) = f) /\\\n   (!f. (\\(x,y,z). f (x,y,z)) = f) /\\\n   (!f. (\\(w,x,y,z). f (w,x,y,z)) = f)"),
  vREPEAT vSTRIP_TAC ----> vREWRITE_TAC[vFUN_EQ_THM; vFORALL_PAIR_THM]);;

let vFORALL_UNCURRY = try Cache.lookup_thm "FORALL_UNCURRY" with _ ->  prove
 ((parse_term "!P. (!f:A->B->C. P f) <=> (!f. P (\\a b. f(a,b)))"),
  vGEN_TAC ----> vEQ_TAC ----> vSIMP_TAC[] ----> vDISCH_TAC ---->
  vX_GEN_TAC (parse_term "f:A->B->C") ---->
  vFIRST_ASSUM(vMP_TAC -| vSPEC (parse_term "\\(a,b). (f:A->B->C) a b")) ----> vSIMP_TAC[vETA_AX]);;

let vEXISTS_UNCURRY = try Cache.lookup_thm "EXISTS_UNCURRY" with _ ->  prove
 ((parse_term "!P. (?f:A->B->C. P f) <=> (?f. P (\\a b. f(a,b)))"),
  vONCE_REWRITE_TAC[vMESON[] (parse_term "(?x. P x) <=> ~(!x. ~P x)")] ---->
  vREWRITE_TAC[vFORALL_UNCURRY]);;

let vEXISTS_CURRY = try Cache.lookup_thm "EXISTS_CURRY" with _ ->  prove
 ((parse_term "!P. (?f. P f) <=> (?f. P (\\(a,b). f a b))"),
  vREWRITE_TAC[vEXISTS_UNCURRY; vPAIRED_ETA_THM]);;

let vFORALL_CURRY = try Cache.lookup_thm "FORALL_CURRY" with _ ->  prove
 ((parse_term "!P. (!f. P f) <=> (!f. P (\\(a,b). f a b))"),
  vREWRITE_TAC[vFORALL_UNCURRY; vPAIRED_ETA_THM]);;

let vFORALL_UNPAIR_THM = try Cache.lookup_thm "FORALL_UNPAIR_THM" with _ ->  prove
 ((parse_term "!P. (!x y. P x y) <=> !z. P (FST z) (SND z)"),
  vREWRITE_TAC[vFORALL_PAIR_THM; vFST; vSND] ----> vMESON_TAC[]);;

let vEXISTS_UNPAIR_THM = try Cache.lookup_thm "EXISTS_UNPAIR_THM" with _ ->  prove
 ((parse_term "!P. (?x y. P x y) <=> ?z. P (FST z) (SND z)"),
  vREWRITE_TAC[vEXISTS_PAIR_THM; vFST; vSND] ----> vMESON_TAC[]);;

let vFORALL_PAIR_FUN_THM = try Cache.lookup_thm "FORALL_PAIR_FUN_THM" with _ ->  prove
 ((parse_term "!P. (!f:A->B#C. P f) <=> (!g h. P(\\a. g a,h a))"),
  vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vGEN_TAC ----> vGEN_REWRITE_TAC vRAND_CONV [vGSYM vETA_AX] ---->
  vGEN_REWRITE_TAC vBINDER_CONV [vGSYM vPAIR] ----> vPURE_ASM_REWRITE_TAC[]);;

let vEXISTS_PAIR_FUN_THM = try Cache.lookup_thm "EXISTS_PAIR_FUN_THM" with _ ->  prove
 ((parse_term "!P. (?f:A->B#C. P f) <=> (?g h. P(\\a. g a,h a))"),
  vREWRITE_TAC[vMESON[] (parse_term "(?x. P x) <=> ~(!x. ~P x)")] ---->
  vREWRITE_TAC[vFORALL_PAIR_FUN_THM]);;

let vFORALL_UNPAIR_FUN_THM = try Cache.lookup_thm "FORALL_UNPAIR_FUN_THM" with _ ->  prove
 ((parse_term "!P. (!f g. P f g) <=> (!h. P (FST o h) (SND o h))"),
  vREWRITE_TAC[vFORALL_PAIR_FUN_THM; o_DEF; vETA_AX]);;

let vEXISTS_UNPAIR_FUN_THM = try Cache.lookup_thm "EXISTS_UNPAIR_FUN_THM" with _ ->  prove
 ((parse_term "!P. (?f g. P f g) <=> (?h. P (FST o h) (SND o h))"),
  vREWRITE_TAC[vEXISTS_PAIR_FUN_THM; o_DEF; vETA_AX]);;

let vEXISTS_SWAP_FUN_THM = try Cache.lookup_thm "EXISTS_SWAP_FUN_THM" with _ ->  prove
 ((parse_term "!P:(A->B->C)->bool. (?f. P f) <=> (?f. P (\\a b. f b a))"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ++-->
   [vDISCH_THEN(vX_CHOOSE_TAC (parse_term "f:A->B->C")) ---->
    vEXISTS_TAC (parse_term "\\b a. (f:A->B->C) a b");
    vDISCH_THEN(vX_CHOOSE_TAC (parse_term "f:B->A->C")) ---->
    vEXISTS_TAC (parse_term "\\b a. (f:B->A->C) a b")] ---->
  vASM_REWRITE_TAC[vETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Related theorems for explicitly paired quantifiers.                       *)
(* ------------------------------------------------------------------------- *)

let vFORALL_PAIRED_THM = try Cache.lookup_thm "FORALL_PAIRED_THM" with _ ->  prove
 ((parse_term "!P. (!(x,y). P x y) <=> (!x y. P x y)"),
  vGEN_TAC ----> vGEN_REWRITE_TAC (vLAND_CONV -| vRATOR_CONV) [vFORALL_DEF] ---->
  vREWRITE_TAC[vFUN_EQ_THM; vFORALL_PAIR_THM]);;

let vEXISTS_PAIRED_THM = try Cache.lookup_thm "EXISTS_PAIRED_THM" with _ ->  prove
 ((parse_term "!P. (?(x,y). P x y) <=> (?x y. P x y)"),
  vGEN_TAC ----> vMATCH_MP_TAC(vTAUT (parse_term "(~p <=> ~q) ==> (p <=> q)")) ---->
  vREWRITE_TAC[vREWRITE_RULE[vETA_AX] vNOT_EXISTS_THM; vFORALL_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Likewise for tripled quantifiers (could continue with the same proof).    *)
(* ------------------------------------------------------------------------- *)

let vFORALL_TRIPLED_THM = try Cache.lookup_thm "FORALL_TRIPLED_THM" with _ ->  prove
 ((parse_term "!P. (!(x,y,z). P x y z) <=> (!x y z. P x y z)"),
  vGEN_TAC ----> vGEN_REWRITE_TAC (vLAND_CONV -| vRATOR_CONV) [vFORALL_DEF] ---->
  vREWRITE_TAC[vFUN_EQ_THM; vFORALL_PAIR_THM]);;

let vEXISTS_TRIPLED_THM = try Cache.lookup_thm "EXISTS_TRIPLED_THM" with _ ->  prove
 ((parse_term "!P. (?(x,y,z). P x y z) <=> (?x y z. P x y z)"),
  vGEN_TAC ----> vMATCH_MP_TAC(vTAUT (parse_term "(~p <=> ~q) ==> (p <=> q)")) ---->
  vREWRITE_TAC[vREWRITE_RULE[vETA_AX] vNOT_EXISTS_THM; vFORALL_PAIR_THM]);;

(* ------------------------------------------------------------------------- *)
(* Similar theorems for the choice operator.                                 *)
(* ------------------------------------------------------------------------- *)

let vCHOICE_UNPAIR_THM = try Cache.lookup_thm "CHOICE_UNPAIR_THM" with _ ->  prove
 ((parse_term "!P. (@(x:A,y:B). P x y) = (@p. P (FST p) (SND p))"),
  vREWRITE_TAC[vLAMBDA_PAIR]);;

let vCHOICE_PAIRED_THM = try Cache.lookup_thm "CHOICE_PAIRED_THM" with _ ->  prove
 ((parse_term "!P Q. (?x:A y:B. P x y) /\\ (!x y. P x y ==> Q(x,y)) ==> Q (@(x,y). P x y)"),
  vINTRO_TAC "!P Q; (@x0 y0. P0) PQ" ---->
  vSUBGOAL_THEN (parse_term "(\\ (x:A,y:B). P x y:bool) = (\\p. P (FST p) (SND p))")
    vSUBST1_TAC ++-->
  [vREWRITE_TAC[vLAMBDA_PAIR_THM]; vSELECT_ELIM_TAC] ---->
  vINTRO_TAC "![c]; c" ----> vONCE_REWRITE_TAC[vGSYM vPAIR] ---->
  vREMOVE_THEN "PQ" vMATCH_MP_TAC ----> vREMOVE_THEN "c" vMATCH_MP_TAC ---->
  vREWRITE_TAC[vEXISTS_PAIR_THM] ----> vASM_MESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Expansion of a let-term.                                                  *)
(* ------------------------------------------------------------------------- *)

let let_CONV =
  let let1_CONV = vREWR_CONV vLET_DEF +---> vGEN_BETA_CONV
  and lete_CONV = vREWR_CONV vLET_END_DEF in
  let rec vEXPAND_BETAS_CONV tm =
    let tm' = rator tm in
    try let1_CONV tm with Failure _ ->
    let th1 = vAP_THM (vEXPAND_BETAS_CONV tm') (rand tm) in
    let th2 = vGEN_BETA_CONV (rand(concl th1)) in
    vTRANS th1 th2 in
  fun tm ->
    let ltm,pargs = strip_comb tm in
    if fst(dest_const ltm) <> "LET" || pargs = [] then failwith "let_CONV" else
    let abstm = hd pargs in
    let vs,_bod = strip_gabs abstm in
    let es = tl pargs in
    let n = length es in
    if length vs <> n then failwith "let_CONV" else
    (vEXPAND_BETAS_CONV +---> lete_CONV) tm;;

let (vLET_TAC:tactic) =
  let is_trivlet tm =
    try let assigs,_bod = dest_let tm in
        forall (uncurry (=)) assigs
    with Failure _ -> false
  and vPROVE_DEPAIRING_EXISTS =
    let pth = prove
     ((parse_term "((x,y) = a) <=> (x = FST a) /\\ (y = SND a)"),
      vMESON_TAC[vPAIR; vPAIR_EQ]) in
    let rewr1_CONV = vGEN_REWRITE_CONV vTOP_DEPTH_CONV [pth]
    and rewr2_RULE = vGEN_REWRITE_RULE (vLAND_CONV -| vDEPTH_CONV)
                      [vTAUT (parse_term "(x = x) <=> T"); vTAUT (parse_term "a /\\ T <=> a")] in
    fun tm ->
      let th1 = rewr1_CONV tm in
      let tm1 = rand(concl th1) in
      let cjs = conjuncts tm1 in
      let vars = map lhand cjs in
      let th2 = vEQ_MP (vSYM th1) (vASSUME tm1) in
      let th3 = vDISCH_ALL (itlist vSIMPLE_EXISTS vars th2) in
      let th4 = vINST (map (fun t -> rand t,lhand t) cjs) th3 in
      vMP (rewr2_RULE th4) vTRUTH in
  fun (asl,w as gl) ->
    let path = try find_path is_trivlet w
               with Failure _ -> find_path is_let w in
    let tm = follow_path path w in
    let assigs,_bod = dest_let tm in
    let abbrevs =
      mapfilter (fun (x,y) -> if x = y then fail() else mk_eq(x,y)) assigs in
    let lvars = itlist (union -| frees -| lhs) abbrevs []
    and avoids = itlist (union -| thm_frees -| snd) asl (frees w) in
    let rename = vsubst (zip (variants avoids lvars) lvars) in
    let abbrevs' = map (fun eq -> let l,r = dest_eq eq in mk_eq(rename l,r))
                       abbrevs in
    let deprths = map vPROVE_DEPAIRING_EXISTS abbrevs' in
    (vMAP_EVERY (vREPEAT_TCL vCHOOSE_THEN
       (fun th -> let th' = vSYM th in
                  vSUBST_ALL_TAC th' ----> vASSUME_TAC th')) deprths ---->
     vW(fun (_asl',w') ->
        let tm' = follow_path path w' in
        vCONV_TAC(vPATH_CONV path (vK(let_CONV tm'))))) gl;;
