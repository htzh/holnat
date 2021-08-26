(* ========================================================================= *)
(* Inductive (or free recursive) types.                                      *)
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
open Preterm
open Parser
open Equal
open Boolean
open Drule
open Tactics
open Itab
open Simp
open Theorems
open Ind_defs
open Class
open Trivia
open Canon
open Meson
open Pair
open Nums
open Recursion
open Arith
open Calc_num

(* ------------------------------------------------------------------------- *)
(* Abstract left inverses for binary injections (we could construct them...) *)
(* ------------------------------------------------------------------------- *)

let vINJ_INVERSE2 = try Cache.lookup_thm "INJ_INVERSE2" with _ ->  prove
 ((parse_term "!P:A->B->C.\n    (!x1 y1 x2 y2. (P x1 y1 = P x2 y2) <=> (x1 = x2) /\\ (y1 = y2))\n    ==> ?X Y. !x y. (X(P x y) = x) /\\ (Y(P x y) = y)"),
  vGEN_TAC ----> vDISCH_TAC ---->
  vEXISTS_TAC (parse_term "\\z:C. @x:A. ?y:B. P x y = z") ---->
  vEXISTS_TAC (parse_term "\\z:C. @y:B. ?x:A. P x y = z") ---->
  vREPEAT vGEN_TAC ----> vASM_REWRITE_TAC[vBETA_THM] ---->
  vCONJ_TAC ----> vMATCH_MP_TAC vSELECT_UNIQUE ----> vGEN_TAC ----> vBETA_TAC ---->
  vEQ_TAC ----> vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
  vW(vEXISTS_TAC -| rand -| snd -| dest_exists -| snd) ----> vREFL_TAC);;

(* ------------------------------------------------------------------------- *)
(* Define an injective pairing function on ":num".                           *)
(* ------------------------------------------------------------------------- *)

let vNUMPAIR = new_definition
  (parse_term "NUMPAIR x y = (2 EXP x) * (2 * y + 1)");;

let vNUMPAIR_INJ_LEMMA = try Cache.lookup_thm "NUMPAIR_INJ_LEMMA" with _ ->  prove
 ((parse_term "!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) ==> (x1 = x2)"),
  vREWRITE_TAC[vNUMPAIR] ----> vREPEAT(vINDUCT_TAC ----> vGEN_TAC) ---->
  vASM_REWRITE_TAC[vEXP; vGSYM vMULT_ASSOC; vARITH; vEQ_MULT_LCANCEL;
    vNOT_SUC; vGSYM vNOT_SUC; vSUC_INJ] ---->
  vDISCH_THEN(vMP_TAC -| vAP_TERM (parse_term "EVEN")) ---->
  vREWRITE_TAC[vEVEN_MULT; vEVEN_ADD; vARITH]);;

let vNUMPAIR_INJ = try Cache.lookup_thm "NUMPAIR_INJ" with _ ->  prove
 ((parse_term "!x1 y1 x2 y2. (NUMPAIR x1 y1 = NUMPAIR x2 y2) <=> (x1 = x2) /\\ (y1 = y2)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vFIRST_ASSUM(vSUBST_ALL_TAC -| vMATCH_MP vNUMPAIR_INJ_LEMMA) ---->
  vPOP_ASSUM vMP_TAC ----> vREWRITE_TAC[vNUMPAIR] ---->
  vREWRITE_TAC[vEQ_MULT_LCANCEL; vEQ_ADD_RCANCEL; vEXP_EQ_0; vARITH]);;

let vNUMPAIR_DEST = new_specification
  ["NUMFST"; "NUMSND"]
  (vMATCH_MP vINJ_INVERSE2 vNUMPAIR_INJ);;

(* ------------------------------------------------------------------------- *)
(* Also, an injective map bool->num->num (even easier!)                      *)
(* ------------------------------------------------------------------------- *)

let vNUMSUM = new_definition
  (parse_term "NUMSUM b x = if b then SUC(2 * x) else 2 * x");;

let vNUMSUM_INJ = try Cache.lookup_thm "NUMSUM_INJ" with _ ->  prove
 ((parse_term "!b1 x1 b2 x2. (NUMSUM b1 x1 = NUMSUM b2 x2) <=> (b1 = b2) /\\ (x1 = x2)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM(vMP_TAC -| vREWRITE_RULE[vNUMSUM]) ---->
  vDISCH_THEN(fun th -> vMP_TAC th ----> vMP_TAC(vAP_TERM (parse_term "EVEN") th)) ---->
  vREPEAT vCOND_CASES_TAC ----> vREWRITE_TAC[vEVEN; vEVEN_DOUBLE] ---->
  vREWRITE_TAC[vSUC_INJ; vEQ_MULT_LCANCEL; vARITH]);;

let vNUMSUM_DEST = new_specification
  ["NUMLEFT"; "NUMRIGHT"]
  (vMATCH_MP vINJ_INVERSE2 vNUMSUM_INJ);;

(* ------------------------------------------------------------------------- *)
(* Injection num->Z, where Z == num->A->bool.                                *)
(* ------------------------------------------------------------------------- *)

let vINJN = new_definition
 (parse_term "INJN (m:num) = \\(n:num) (a:A). n = m");;

let vINJN_INJ = try Cache.lookup_thm "INJN_INJ" with _ ->  prove
 ((parse_term "!n1 n2. (INJN n1 :num->A->bool = INJN n2) <=> (n1 = n2)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM(vMP_TAC -| vC vAP_THM (parse_term "n1:num") -| vREWRITE_RULE[vINJN]) ---->
  vDISCH_THEN(vMP_TAC -| vC vAP_THM (parse_term "a:A")) ----> vREWRITE_TAC[vBETA_THM]);;

(* ------------------------------------------------------------------------- *)
(* Injection A->Z, where Z == num->A->bool.                                  *)
(* ------------------------------------------------------------------------- *)

let vINJA = new_definition
 (parse_term "INJA (a:A) = \\(n:num) b. b = a");;

let vINJA_INJ = try Cache.lookup_thm "INJA_INJ" with _ ->  prove
 ((parse_term "!a1 a2. (INJA a1 = INJA a2) <=> (a1:A = a2)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vINJA; vFUN_EQ_THM] ----> vEQ_TAC ++-->
   [vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "a1:A")) ----> vREWRITE_TAC[];
    vDISCH_THEN vSUBST1_TAC ----> vREWRITE_TAC[]]);;

(* ------------------------------------------------------------------------- *)
(* Injection (num->Z)->Z, where Z == num->A->bool.                           *)
(* ------------------------------------------------------------------------- *)

let vINJF = new_definition
  (parse_term "INJF (f:num->(num->A->bool)) = \\n. f (NUMFST n) (NUMSND n)");;

let vINJF_INJ = try Cache.lookup_thm "INJF_INJ" with _ ->  prove
 ((parse_term "!f1 f2. (INJF f1 :num->A->bool = INJF f2) <=> (f1 = f2)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vREWRITE_TAC[vFUN_EQ_THM] ---->
  vMAP_EVERY vX_GEN_TAC [(parse_term "n:num"); (parse_term "m:num"); (parse_term "a:A")] ---->
  vPOP_ASSUM(vMP_TAC -| vREWRITE_RULE[vINJF]) ---->
  vDISCH_THEN(vMP_TAC -| vC vAP_THM (parse_term "a:A") -| vC vAP_THM (parse_term "NUMPAIR n m")) ---->
  vREWRITE_TAC[vNUMPAIR_DEST]);;

(* ------------------------------------------------------------------------- *)
(* Injection Z->Z->Z, where Z == num->A->bool.                               *)
(* ------------------------------------------------------------------------- *)

let vINJP = new_definition
  (parse_term "INJP f1 f2:num->A->bool =\n        \\n a. if NUMLEFT n then f1 (NUMRIGHT n) a else f2 (NUMRIGHT n) a");;

let vINJP_INJ = try Cache.lookup_thm "INJP_INJ" with _ ->  prove
 ((parse_term "!(f1:num->A->bool) f1' f2 f2'.\n        (INJP f1 f2 = INJP f1' f2') <=> (f1 = f1') /\\ (f2 = f2')"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vONCE_REWRITE_TAC[vFUN_EQ_THM] ----> vREWRITE_TAC[vAND_FORALL_THM] ---->
  vX_GEN_TAC (parse_term "n:num") ----> vPOP_ASSUM(vMP_TAC -| vREWRITE_RULE[vINJP]) ---->
  vDISCH_THEN(vMP_TAC -| vGEN (parse_term "b:bool") -| vC vAP_THM (parse_term "NUMSUM b n")) ---->
  vDISCH_THEN(fun th -> vMP_TAC(vSPEC (parse_term "T") th) ----> vMP_TAC(vSPEC (parse_term "F") th)) ---->
  vASM_SIMP_TAC[vNUMSUM_DEST; vETA_AX]);;

(* ------------------------------------------------------------------------- *)
(* Now, set up "constructor" and "bottom" element.                           *)
(* ------------------------------------------------------------------------- *)

let vZCONSTR = new_definition
  (parse_term "ZCONSTR c i r :num->A->bool\n     = INJP (INJN (SUC c)) (INJP (INJA i) (INJF r))");;

let vZBOT = new_definition
  (parse_term "ZBOT = INJP (INJN 0) (@z:num->A->bool. T)");;

let vZCONSTR_ZBOT = try Cache.lookup_thm "ZCONSTR_ZBOT" with _ ->  prove
 ((parse_term "!c i r. ~(ZCONSTR c i r :num->A->bool = ZBOT)"),
  vREWRITE_TAC[vZCONSTR; vZBOT; vINJP_INJ; vINJN_INJ; vNOT_SUC]);;

(* ------------------------------------------------------------------------- *)
(* Carve out an inductively defined set.                                     *)
(* ------------------------------------------------------------------------- *)

let vZRECSPACE_RULES,vZRECSPACE_INDUCT,vZRECSPACE_CASES =
  new_inductive_definition
   (parse_term "ZRECSPACE (ZBOT:num->A->bool) /\\\n    (!c i r. (!n. ZRECSPACE (r n)) ==> ZRECSPACE (ZCONSTR c i r))");;

let recspace_tydef =
  new_basic_type_definition "recspace" ("_mk_rec","_dest_rec")
  (vCONJUNCT1 vZRECSPACE_RULES);;

(* ------------------------------------------------------------------------- *)
(* Define lifted constructors.                                               *)
(* ------------------------------------------------------------------------- *)

let vBOTTOM = new_definition
  (parse_term "BOTTOM = _mk_rec (ZBOT:num->A->bool)");;

let vCONSTR = new_definition
  (parse_term "CONSTR c i r :(A)recspace\n     = _mk_rec (ZCONSTR c i (\\n. _dest_rec(r n)))");;

(* ------------------------------------------------------------------------- *)
(* Some lemmas.                                                              *)
(* ------------------------------------------------------------------------- *)

let vMK_REC_INJ = try Cache.lookup_thm "MK_REC_INJ" with _ ->  prove
 ((parse_term "!x y. (_mk_rec x :(A)recspace = _mk_rec y)\n         ==> (ZRECSPACE x /\\ ZRECSPACE y ==> (x = y))"),
  vREPEAT vGEN_TAC ----> vDISCH_TAC ---->
  vREWRITE_TAC[snd recspace_tydef] ---->
  vDISCH_THEN(fun th -> vONCE_REWRITE_TAC[vGSYM th]) ---->
  vASM_REWRITE_TAC[]);;

let vDEST_REC_INJ = try Cache.lookup_thm "DEST_REC_INJ" with _ ->  prove
 ((parse_term "!x y. (_dest_rec x = _dest_rec y) <=> (x:(A)recspace = y)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM(vMP_TAC -| vAP_TERM
    (parse_term "_mk_rec:(num->A->bool)->(A)recspace")) ---->
  vREWRITE_TAC[fst recspace_tydef]);;

(* ------------------------------------------------------------------------- *)
(* Show that the set is freely inductively generated.                        *)
(* ------------------------------------------------------------------------- *)

let vCONSTR_BOT = try Cache.lookup_thm "CONSTR_BOT" with _ ->  prove
 ((parse_term "!c i r. ~(CONSTR c i r :(A)recspace = BOTTOM)"),
  vREPEAT vGEN_TAC ----> vREWRITE_TAC[vCONSTR; vBOTTOM] ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vMK_REC_INJ) ---->
  vREWRITE_TAC[vZCONSTR_ZBOT; vZRECSPACE_RULES] ---->
  vMATCH_MP_TAC(vCONJUNCT2 vZRECSPACE_RULES) ---->
  vREWRITE_TAC[fst recspace_tydef; snd recspace_tydef]);;

let vCONSTR_INJ = try Cache.lookup_thm "CONSTR_INJ" with _ ->  prove
 ((parse_term "!c1 i1 r1 c2 i2 r2. (CONSTR c1 i1 r1 :(A)recspace = CONSTR c2 i2 r2) <=>\n                       (c1 = c2) /\\ (i1 = i2) /\\ (r1 = r2)"),
  vREPEAT vGEN_TAC ----> vEQ_TAC ----> vDISCH_TAC ----> vASM_REWRITE_TAC[] ---->
  vPOP_ASSUM(vMP_TAC -| vREWRITE_RULE[vCONSTR]) ---->
  vDISCH_THEN(vMP_TAC -| vMATCH_MP vMK_REC_INJ) ---->
  vW(vC vSUBGOAL_THEN vASSUME_TAC -| funpow 2 lhand -| snd) ++-->
   [vCONJ_TAC ----> vMATCH_MP_TAC(vCONJUNCT2 vZRECSPACE_RULES) ---->
    vREWRITE_TAC[fst recspace_tydef; snd recspace_tydef];
    vASM_REWRITE_TAC[] ----> vREWRITE_TAC[vZCONSTR] ---->
    vREWRITE_TAC[vINJP_INJ; vINJN_INJ; vINJF_INJ; vINJA_INJ] ---->
    vONCE_REWRITE_TAC[vFUN_EQ_THM] ----> vBETA_TAC ---->
    vREWRITE_TAC[vSUC_INJ; vDEST_REC_INJ]]);;

let vCONSTR_IND = try Cache.lookup_thm "CONSTR_IND" with _ ->  prove
 ((parse_term "!P. P(BOTTOM) /\\\n       (!c i r. (!n. P(r n)) ==> P(CONSTR c i r))\n       ==> !x:(A)recspace. P(x)"),
  vREPEAT vSTRIP_TAC ---->
  vMP_TAC(vSPEC (parse_term "\\z:num->A->bool. ZRECSPACE(z) /\\ P(_mk_rec z)")
         vZRECSPACE_INDUCT) ---->
  vBETA_TAC ----> vASM_REWRITE_TAC[vZRECSPACE_RULES; vGSYM vBOTTOM] ---->
  vW(vC vSUBGOAL_THEN vASSUME_TAC -| funpow 2 lhand -| snd) ++-->
   [vREPEAT vGEN_TAC ----> vREWRITE_TAC[vFORALL_AND_THM] ---->
    vREPEAT vSTRIP_TAC ++-->
     [vMATCH_MP_TAC(vCONJUNCT2 vZRECSPACE_RULES) ----> vASM_REWRITE_TAC[];
      vFIRST_ASSUM(vANTE_RES_THEN vMP_TAC) ---->
      vREWRITE_TAC[vCONSTR] ---->
      vRULE_ASSUM_TAC(vREWRITE_RULE[snd recspace_tydef]) ---->
      vASM_SIMP_TAC[vETA_AX]];
    vASM_REWRITE_TAC[] ---->
    vDISCH_THEN(vMP_TAC -| vSPEC (parse_term "_dest_rec (x:(A)recspace)")) ---->
    vREWRITE_TAC[fst recspace_tydef] ---->
    vREWRITE_TAC[vITAUT (parse_term "(a ==> a /\\ b) <=> (a ==> b)")] ---->
    vDISCH_THEN vMATCH_MP_TAC ---->
    vREWRITE_TAC[fst recspace_tydef; snd recspace_tydef]]);;

(* ------------------------------------------------------------------------- *)
(* Now prove the recursion theorem (this subcase is all we need).            *)
(* ------------------------------------------------------------------------- *)

let vCONSTR_REC = try Cache.lookup_thm "CONSTR_REC" with _ ->  prove
 ((parse_term "!Fn:num->A->(num->(A)recspace)->(num->B)->B.\n     ?f. (!c i r. f (CONSTR c i r) = Fn c i r (\\n. f (r n)))"),
  vREPEAT vSTRIP_TAC ----> (vMP_TAC -| prove_inductive_relations_exist)
    (parse_term "(Z:(A)recspace->B->bool) BOTTOM b /\\\n     (!c i r y. (!n. Z (r n) (y n)) ==> Z (CONSTR c i r) (Fn c i r y))") ---->
  vDISCH_THEN(vCHOOSE_THEN(vCONJUNCTS_THEN2 vSTRIP_ASSUME_TAC vMP_TAC)) ---->
  vDISCH_THEN(vCONJUNCTS_THEN2 vASSUME_TAC (vASSUME_TAC -| vGSYM)) ---->
  vSUBGOAL_THEN (parse_term "!x. ?!y. (Z:(A)recspace->B->bool) x y") vMP_TAC ++-->
   [vW(vMP_TAC -| vPART_MATCH rand vCONSTR_IND -| snd) ---->
    vDISCH_THEN vMATCH_MP_TAC ----> vCONJ_TAC ----> vREPEAT vGEN_TAC ++-->
     [vFIRST_ASSUM(fun t -> vGEN_REWRITE_TAC vBINDER_CONV [vGSYM t]) ---->
      vREWRITE_TAC[vGSYM vCONSTR_BOT; vEXISTS_UNIQUE_REFL];
      vDISCH_THEN(vMP_TAC -| vREWRITE_RULE[vEXISTS_UNIQUE_THM; vFORALL_AND_THM]) ---->
      vDISCH_THEN(vCONJUNCTS_THEN2 vMP_TAC vASSUME_TAC) ---->
      vDISCH_THEN(vMP_TAC -| vREWRITE_RULE[vSKOLEM_THM]) ---->
      vDISCH_THEN(vX_CHOOSE_THEN (parse_term "y:num->B") vASSUME_TAC) ---->
      vREWRITE_TAC[vEXISTS_UNIQUE_THM] ---->
      vFIRST_ASSUM(fun th -> vCHANGED_TAC(vONCE_REWRITE_TAC[vGSYM th])) ---->
      vCONJ_TAC ++-->
       [vEXISTS_TAC (parse_term "(Fn:num->A->(num->(A)recspace)->(num->B)->B) c i r y") ---->
        vREWRITE_TAC[vCONSTR_BOT; vCONSTR_INJ; vGSYM vCONJ_ASSOC] ---->
        vREWRITE_TAC[vUNWIND_THM1; vRIGHT_EXISTS_AND_THM] ---->
        vEXISTS_TAC (parse_term "y:num->B") ----> vASM_REWRITE_TAC[];
        vREWRITE_TAC[vCONSTR_BOT; vCONSTR_INJ; vGSYM vCONJ_ASSOC] ---->
        vREWRITE_TAC[vUNWIND_THM1; vRIGHT_EXISTS_AND_THM] ---->
        vREPEAT vSTRIP_TAC ----> vASM_REWRITE_TAC[] ---->
        vREPEAT vAP_TERM_TAC ----> vONCE_REWRITE_TAC[vFUN_EQ_THM] ---->
        vX_GEN_TAC (parse_term "w:num") ----> vFIRST_ASSUM vMATCH_MP_TAC ---->
        vEXISTS_TAC (parse_term "w:num") ----> vASM_REWRITE_TAC[]]];
    vREWRITE_TAC[vUNIQUE_SKOLEM_ALT] ---->
    vDISCH_THEN(vX_CHOOSE_THEN (parse_term "fn:(A)recspace->B") (vASSUME_TAC -| vGSYM)) ---->
    vEXISTS_TAC (parse_term "fn:(A)recspace->B") ----> vASM_REWRITE_TAC[] ---->
    vREPEAT vGEN_TAC ----> vFIRST_ASSUM vMATCH_MP_TAC ----> vGEN_TAC ---->
    vFIRST_ASSUM(fun th -> vGEN_REWRITE_TAC vI [vGSYM th]) ---->
    vREWRITE_TAC[vBETA_THM]]);;

(* ------------------------------------------------------------------------- *)
(* The following is useful for coding up functions casewise.                 *)
(* ------------------------------------------------------------------------- *)

let vFCONS = new_recursive_definition num_RECURSION
 (parse_term "(!a f. FCONS (a:A) f 0 = a) /\\\n  (!a f n. FCONS (a:A) f (SUC n) = f n)");;

let vFCONS_UNDO = try Cache.lookup_thm "FCONS_UNDO" with _ ->  prove
 ((parse_term "!f:num->A. f = FCONS (f 0) (f o SUC)"),
  vGEN_TAC ----> vREWRITE_TAC[vFUN_EQ_THM] ---->
  vINDUCT_TAC ----> vREWRITE_TAC[vFCONS; o_THM]);;

let vFNIL = new_definition
  (parse_term "FNIL (n:num) = @x:A. T");;

(* ------------------------------------------------------------------------- *)
(* The initial mutual type definition function, with a type-restricted       *)
(* recursion theorem.                                                        *)
(* ------------------------------------------------------------------------- *)

let define_type_raw =

  (* ----------------------------------------------------------------------- *)
  (* Handy utility to produce "SUC o SUC o SUC ..." form of numeral.         *)
  (* ----------------------------------------------------------------------- *)

  let sucivate =
    let zero = (parse_term "0") and suc = (parse_term "SUC") in
    fun n -> funpow n (curry mk_comb suc) zero in

  (* ----------------------------------------------------------------------- *)
  (* Eliminate local "definitions" in hyps.                                  *)
  (* ----------------------------------------------------------------------- *)


  let vSCRUB_EQUATION eq (th,insts) = (*HA*)
    let eq' = itlist subst (map (fun t -> [t]) insts) eq in
    let l,r = dest_eq eq' in
    (vMP (vINST [r,l] (vDISCH eq' th)) (vREFL r),(r,l)::insts) in

  (* ----------------------------------------------------------------------- *)
  (* Proves existence of model (inductively); use pseudo-constructors.       *)
  (*                                                                         *)
  (* Returns suitable definitions of constructors in terms of CONSTR, and    *)
  (* the rule and induction theorems from the inductive relation package.    *)
  (* ----------------------------------------------------------------------- *)

  let justify_inductive_type_model =
    let t_tm = (parse_term "T") and n_tm = (parse_term "n:num") and beps_tm = (parse_term "@x:bool. T") in
    let rec munion s1 s2 =
      if s1 = [] then s2 else
      let h1 = hd s1
      and s1' = tl s1 in
      try let _,s2' = remove (fun h2 -> h2 = h1) s2 in h1::(munion s1' s2')
      with Failure _ -> h1::(munion s1' s2) in
    fun def ->
      let newtys,rights = unzip def in
      let tyargls = itlist ((@) -| map snd) rights [] in
      let alltys = itlist (munion -| vC subtract newtys) tyargls [] in
      let epstms = map (fun ty -> mk_select(mk_var("v",ty),t_tm)) alltys in
      let pty =
        try end_itlist (fun ty1 ty2 -> mk_type("prod",[ty1;ty2])) alltys
        with Failure _ -> bool_ty in
      let recty = mk_type("recspace",[pty]) in
      let constr = mk_const("CONSTR",[pty,aty]) in
      let fcons = mk_const("FCONS",[recty,aty]) in
      let bot = mk_const("BOTTOM",[pty,aty]) in
      let bottail = mk_abs(n_tm,bot) in
      let mk_constructor n (cname,cargs) =
        let ttys = map (fun ty -> if mem ty newtys then recty else ty) cargs in
        let args = make_args "a" [] ttys in
        let rargs,iargs = partition (fun t -> type_of t = recty) args in
        let rec mk_injector epstms alltys iargs =
          if alltys = [] then [] else
          let ty = hd alltys in
          try let a,iargs' = remove (fun t -> type_of t = ty) iargs in
              a::(mk_injector (tl epstms) (tl alltys) iargs')
          with Failure _ ->
              (hd epstms)::(mk_injector (tl epstms) (tl alltys) iargs) in
        let iarg =
          try end_itlist (curry mk_pair) (mk_injector epstms alltys iargs)
          with Failure _ -> beps_tm in
        let rarg = itlist (mk_binop fcons) rargs bottail in
      let conty = itlist mk_fun_ty (map type_of args) recty in
      let condef = list_mk_comb(constr,[sucivate n; iarg; rarg]) in
      mk_eq(mk_var(cname,conty),list_mk_abs(args,condef)) in
    let rec mk_constructors n rights =
      if rights = [] then [] else
      (mk_constructor n (hd rights))::(mk_constructors (n + 1) (tl rights)) in
    let condefs = mk_constructors 0 (itlist (@) rights []) in
    let conths = map vASSUME condefs in
    let predty = mk_fun_ty recty bool_ty in
    let edefs = itlist (fun (x,l) acc -> map (fun t -> x,t) l @ acc) def [] in
    let idefs = map2 (fun (r,(_,atys)) def -> (r,atys),def) edefs condefs in
    let mk_rule ((r,a),condef) =
      let left,right = dest_eq condef in
      let args,_bod = strip_abs right in
      let lapp = list_mk_comb(left,args) in
      let conds = itlist2
        (fun arg argty sofar ->
          if mem argty newtys then
            mk_comb(mk_var(dest_vartype argty,predty),arg)::sofar
          else sofar) args a [] in
      let conc = mk_comb(mk_var(dest_vartype r,predty),lapp) in
      let rule = if conds = [] then conc
                 else mk_imp(list_mk_conj conds,conc) in
      list_mk_forall(args,rule) in
    let rules = list_mk_conj (map mk_rule idefs) in
    let th0 = derive_nonschematic_inductive_relations rules in
    let th1 = prove_monotonicity_hyps th0 in
    let th2a,th2bc = vCONJ_PAIR th1 in
    let th2b = vCONJUNCT1 th2bc in
    conths,th2a,th2b in

  (* ----------------------------------------------------------------------- *)
  (* Shows that the predicates defined by the rules are all nonempty.        *)
  (* (This could be done much more efficiently/cleverly, but it's OK.)       *)
  (* ----------------------------------------------------------------------- *)

  let prove_model_inhabitation rth =
    let srules = map vSPEC_ALL (vCONJUNCTS rth) in
    let imps,bases = partition (is_imp -| concl) srules in
    let concs = map concl bases @ map (rand -| concl) imps in
    let preds = setify (map (repeat rator) concs) in
    let rec exhaust_inhabitations ths sofar =
      let dunnit = setify(map (fst -| strip_comb -| concl) sofar) in
      let useful = filter
        (fun th -> not (mem (fst(strip_comb(rand(concl th)))) dunnit)) ths in
      if useful = [] then sofar else
      let follow_horn thm =
        let preds = map (fst -| strip_comb) (conjuncts(lhand(concl thm))) in
        let asms = map
          (fun p -> find (fun th -> fst(strip_comb(concl th)) = p) sofar)
          preds in
        vMATCH_MP thm (end_itlist vCONJ asms) in
      let newth = tryfind follow_horn useful in
      exhaust_inhabitations ths (newth::sofar) in
    let ithms = exhaust_inhabitations imps bases in
    let exths = map
      (fun p -> find (fun th -> fst(strip_comb(concl th)) = p) ithms) preds in
    exths in

  (* ----------------------------------------------------------------------- *)
  (* Makes a type definition for one of the defined subsets.                 *)
  (* ----------------------------------------------------------------------- *)

  let define_inductive_type cdefs exth =
    let extm = concl exth in
    let epred = fst(strip_comb extm) in
    let ename = fst(dest_var epred) in
    let th1 = vASSUME (find (fun eq -> lhand eq = epred) (hyp exth)) in
    let th2 = vTRANS th1 (vSUBS_CONV cdefs (rand(concl th1))) in
    let th3 = vEQ_MP (vAP_THM th2 (rand extm)) exth in
    let th4,_ = itlist vSCRUB_EQUATION (hyp th3) (th3,[]) in
    let mkname = "_mk_"^ename and destname = "_dest_"^ename in
    let bij1,bij2 = new_basic_type_definition ename (mkname,destname) th4 in
    let bij2a = vAP_THM th2 (rand(rand(concl bij2))) in
    let bij2b = vTRANS bij2a bij2 in
    bij1,bij2b in

  (* ----------------------------------------------------------------------- *)
  (* Defines a type constructor corresponding to current pseudo-constructor. *)
  (* ----------------------------------------------------------------------- *)

  let define_inductive_type_constructor defs consindex th =
    let _avs,bod = strip_forall(concl th) in
    let asms,conc =
      if is_imp bod then conjuncts(lhand bod),rand bod else [],bod in
    let asmlist = map dest_comb asms in
    let cpred,cterm = dest_comb conc in
    let oldcon,oldargs = strip_comb cterm in
    let modify_arg v =
      try let dest = snd(assoc (rev_assoc v asmlist) consindex) in
          let ty' = hd(snd(dest_type(type_of dest))) in
          let v' = mk_var(fst(dest_var v),ty') in
          mk_comb(dest,v'),v'
      with Failure _ -> v,v in
    let newrights,newargs = unzip(map modify_arg oldargs) in
    let retmk = fst(assoc cpred consindex) in
    let defbod = mk_comb(retmk,list_mk_comb(oldcon,newrights)) in
    let defrt = list_mk_abs(newargs,defbod) in
    let expth = find (fun th -> lhand(concl th) = oldcon) defs in
    let rexpth = vSUBS_CONV [expth] defrt in
    let deflf = mk_var(fst(dest_var oldcon),type_of defrt) in
    let defth = new_definition(mk_eq(deflf,rand(concl rexpth))) in
    vTRANS defth (vSYM rexpth) in

  (* ----------------------------------------------------------------------- *)
  (* Instantiate the induction theorem on the representatives to transfer    *)
  (* it to the new type(s). Uses "\x. rep-pred(x) /\ P(mk x)" for "P".       *)
  (* ----------------------------------------------------------------------- *)

  let instantiate_induction_theorem consindex ith =
    let avs,bod = strip_forall(concl ith) in
    let corlist = map((repeat rator $-$ repeat rator) -| dest_imp -| body -| rand)
      (conjuncts(rand bod)) in
    let consindex' = map (fun v -> let w = rev_assoc v corlist in
                                   w,assoc w consindex) avs in
    let recty = (hd -| snd -| dest_type -| type_of -| fst -| snd -| hd) consindex in
    let newtys = map (hd -| snd -| dest_type -| type_of -| snd -| snd) consindex' in
    let ptypes = map (vC mk_fun_ty bool_ty) newtys in
    let preds = make_args "P" [] ptypes in
    let args = make_args "x" [] (map (vK recty) preds) in
    let lambs = map2 (fun (r,(m,_d)) (p,a) ->
                       mk_abs(a,mk_conj(mk_comb(r,a),mk_comb(p,mk_comb(m,a)))))
                     consindex' (zip preds args) in
    vSPECL lambs ith in

  (* ----------------------------------------------------------------------- *)
  (* Reduce a single clause of the postulated induction theorem (old_ver) ba *)
  (* to the kind wanted for the new type (new_ver); |- new_ver ==> old_ver   *)
  (* ----------------------------------------------------------------------- *)

  let pullback_induction_clause tybijpairs conthms =
    let vPRERULE = vGEN_REWRITE_RULE (funpow 3 vRAND_CONV) (map vSYM conthms) in
    let vIPRULE = vSYM -| vGEN_REWRITE_RULE vI (map snd tybijpairs) in
    fun rthm tm ->
      let avs,bimp = strip_forall tm in
      if is_imp bimp then
        let ant,con = dest_imp bimp in
        let ths = map (vCONV_RULE vBETA_CONV) (vCONJUNCTS (vASSUME ant)) in
        let tths,pths = unzip (map vCONJ_PAIR ths) in
        let tth = vMATCH_MP (vSPEC_ALL rthm) (end_itlist vCONJ tths) in
        let mths = map vIPRULE (tth::tths) in
        let conth1 = vBETA_CONV con in
        let contm1 = rand(concl conth1) in
        let conth2 = vTRANS conth1
          (vAP_TERM (rator contm1) (vSUBS_CONV (tl mths) (rand contm1))) in
        let conth3 = vPRERULE conth2 in
        let lctms = map concl pths in
        let asmin = mk_imp(list_mk_conj lctms,rand(rand(concl conth3))) in
        let argsin = map rand (conjuncts(lhand asmin)) in
        let argsgen =
          map (fun tm -> mk_var(fst(dest_var(rand tm)),type_of tm)) argsin in
        let asmgen = subst (zip argsgen argsin) asmin in
        let asmquant =
          list_mk_forall(snd(strip_comb(rand(rand asmgen))),asmgen) in
        let th1 = vINST (zip argsin argsgen) (vSPEC_ALL (vASSUME asmquant)) in
        let th2 = vMP th1 (end_itlist vCONJ pths) in
        let th3 = vEQ_MP (vSYM conth3) (vCONJ tth th2) in
        vDISCH asmquant (vGENL avs (vDISCH ant th3))
      else
        let con = bimp in
        let conth2 = vBETA_CONV con in
        let tth = vPART_MATCH vI rthm (lhand(rand(concl conth2))) in
        let conth3 = vPRERULE conth2 in
        let asmgen = rand(rand(concl conth3)) in
        let asmquant = list_mk_forall(snd(strip_comb(rand asmgen)),asmgen) in
        let th2 = vSPEC_ALL (vASSUME asmquant) in
        let th3 = vEQ_MP (vSYM conth3) (vCONJ tth th2) in
        vDISCH asmquant (vGENL avs th3) in

  (* ----------------------------------------------------------------------- *)
  (* Finish off a consequence of the induction theorem.                      *)
  (* ----------------------------------------------------------------------- *)

  let finish_induction_conclusion consindex tybijpairs =
    let tybij1,tybij2 = unzip tybijpairs in
    let vPRERULE =
      vGEN_REWRITE_RULE (vLAND_CONV -| vLAND_CONV -| vRAND_CONV) tybij1 -|
      vGEN_REWRITE_RULE vLAND_CONV tybij2
    and vFINRULE = vGEN_REWRITE_RULE vRAND_CONV tybij1 in
    fun th ->
      let _av,bimp = dest_forall(concl th) in
      let pv = lhand(body(rator(rand bimp))) in
      let p,v = dest_comb pv in
      let _mk,dest = assoc p consindex in
      let ty = hd(snd(dest_type(type_of dest))) in
      let v' = mk_var(fst(dest_var v),ty) in
      let dv = mk_comb(dest,v') in
      let th1 = vPRERULE (vSPEC dv th) in
      let th2 = vMP th1 (vREFL (rand(lhand(concl th1)))) in
      let th3 = vCONV_RULE vBETA_CONV th2 in
      vGEN v' (vFINRULE (vCONJUNCT2 th3)) in

  (* ----------------------------------------------------------------------- *)
  (* Derive the induction theorem.                                           *)
  (* ----------------------------------------------------------------------- *)

  let derive_induction_theorem consindex tybijpairs conthms iith rth =
    let bths = map2
      (pullback_induction_clause tybijpairs conthms)
      (vCONJUNCTS rth) (conjuncts(lhand(concl iith))) in
    let asm = list_mk_conj(map (lhand -| concl) bths) in
    let ths = map2 vMP bths (vCONJUNCTS (vASSUME asm)) in
    let th1 = vMP iith (end_itlist vCONJ ths) in
    let th2 = end_itlist vCONJ (map
      (finish_induction_conclusion consindex tybijpairs) (vCONJUNCTS th1)) in
    let th3 = vDISCH asm th2 in
    let preds = map (rator -| body -| rand) (conjuncts(rand(concl th3))) in
    let th4 = vGENL preds th3 in
    let pasms = filter (vC mem (map fst consindex) -| lhand) (hyp th4) in
    let th5 = itlist vDISCH pasms th4 in
    let th6,_ = itlist vSCRUB_EQUATION (hyp th5) (th5,[]) in
    let th7 = vUNDISCH_ALL th6 in
    fst (itlist vSCRUB_EQUATION (hyp th7) (th7,[])) in

  (* ----------------------------------------------------------------------- *)
  (* Create the recursive functions and eliminate pseudo-constructors.       *)
  (* (These are kept just long enough to derive the key property.)           *)
  (* ----------------------------------------------------------------------- *)

  let create_recursive_functions tybijpairs consindex conthms rth =
    let domtys = map (hd -| snd -| dest_type -| type_of -| snd -| snd) consindex in
    let recty = (hd -| snd -| dest_type -| type_of -| fst -| snd -| hd) consindex in
    let ranty = mk_vartype "Z" in
    let fn = mk_var("fn",mk_fun_ty recty ranty)
    and fns = make_args "fn" [] (map (vC mk_fun_ty ranty) domtys) in
    let args = make_args "a" [] domtys in
    let rights = map2 (fun (_,(_,d)) a -> mk_abs(a,mk_comb(fn,mk_comb(d,a))))
      consindex args in
    let eqs = map2 (curry mk_eq) fns rights in
    let fdefs = map vASSUME eqs in
    let fxths1 = map (fun th1 -> tryfind (fun th2 -> vMK_COMB(th2,th1)) fdefs)
      conthms in
    let fxths2 = map (fun th -> vTRANS th (vBETA_CONV (rand(concl th)))) fxths1 in
    let mk_tybijcons (th1,th2) =
      let th3 = vINST [rand(lhand(concl th1)),rand(lhand(concl th2))] th2 in
      let th4 = vAP_TERM (rator(lhand(rand(concl th2)))) th1 in
      vEQ_MP (vSYM th3) th4 in
    let vSCONV = vGEN_REWRITE_CONV vI (map mk_tybijcons tybijpairs)
    and vERULE = vGEN_REWRITE_RULE vI (map snd tybijpairs) in
    let simplify_fxthm rthm fxth =
      let pat = funpow 4 rand (concl fxth) in
      if is_imp(repeat (snd -| dest_forall) (concl rthm)) then
        let th1 = vPART_MATCH (rand -| rand) rthm pat in
        let tms1 = conjuncts(lhand(concl th1)) in
        let ths2 = map (fun t -> vEQ_MP (vSYM(vSCONV t)) vTRUTH) tms1 in
        vERULE (vMP th1 (end_itlist vCONJ ths2))
      else
        vERULE (vPART_MATCH rand rthm pat) in
    let fxths3 = map2 simplify_fxthm (vCONJUNCTS rth) fxths2 in
    let fxths4 = map2 (fun th1 -> vTRANS th1 -| vAP_TERM fn) fxths2 fxths3 in
    let cleanup_fxthm cth fxth =
      let tms = snd(strip_comb(rand(rand(concl fxth)))) in
      let kth = vRIGHT_BETAS tms (vASSUME (hd(hyp cth))) in
      vTRANS fxth (vAP_TERM fn kth) in
    let fxth5 = end_itlist vCONJ (map2 cleanup_fxthm conthms fxths4) in
    let pasms = filter (vC mem (map fst consindex) -| lhand) (hyp fxth5) in
    let fxth6 = itlist vDISCH pasms fxth5 in
    let fxth7,_ =
      itlist vSCRUB_EQUATION (itlist (union -| hyp) conthms []) (fxth6,[]) in
    let fxth8 = vUNDISCH_ALL fxth7 in
    fst (itlist vSCRUB_EQUATION (subtract (hyp fxth8) eqs) (fxth8,[])) in

  (* ----------------------------------------------------------------------- *)
  (* Create a function for recursion clause.                                 *)
  (* ----------------------------------------------------------------------- *)

  let create_recursion_iso_constructor =
    let s = (parse_term "s:num->Z") in
    let zty = (parse_type "Z") in
    let numty = (parse_type "num") in
    let rec extract_arg tup v =
      if v = tup then vREFL tup else
      let t1,t2 = dest_pair tup in
      let vPAIR_th = vISPECL [t1;t2] (if free_in v t1 then vFST else vSND) in
      let tup' = rand(concl vPAIR_th) in
      if tup' = v then vPAIR_th else
      let th = extract_arg (rand(concl vPAIR_th)) v in
      vSUBS[vSYM vPAIR_th] th in
    fun consindex ->
      let recty = hd(snd(dest_type(type_of(fst(hd consindex))))) in
      let domty = hd(snd(dest_type recty)) in
      let i = mk_var("i",domty)
      and r = mk_var("r",mk_fun_ty numty recty) in
      let mks = map (fst -| snd) consindex in
      let mkindex = map (fun t -> hd(tl(snd(dest_type(type_of t)))),t) mks in
      fun cth ->
        let artms = snd(strip_comb(rand(rand(concl cth)))) in
        let artys = mapfilter (type_of -| rand) artms in
        let args,bod = strip_abs(rand(hd(hyp cth))) in
        let ccitm,rtm = dest_comb bod in
        let _cctm,itm = dest_comb ccitm in
        let rargs,iargs = partition (vC free_in rtm) args in
        let xths = map (extract_arg itm) iargs in
        let cargs' = map (subst [i,itm] -| lhand -| concl) xths in
        let indices = map sucivate (0--(length rargs - 1)) in
        let rindexed = map (curry mk_comb r) indices in
        let rargs' = map2 (fun a rx -> mk_comb(assoc a mkindex,rx))
            artys rindexed in
        let sargs' = map (curry mk_comb s) indices in
        let allargs = cargs'@ rargs' @ sargs' in
        let funty = itlist (mk_fun_ty -| type_of) allargs zty in
        let funname = fst(dest_const(repeat rator (lhand(concl cth))))^"'" in
        let funarg = mk_var(funname,funty) in
        list_mk_abs([i;r;s],list_mk_comb(funarg,allargs)) in

  (* ----------------------------------------------------------------------- *)
  (* Derive the recursion theorem.                                           *)
  (* ----------------------------------------------------------------------- *)

  let derive_recursion_theorem =
    let vCCONV = funpow 3 vRATOR_CONV (vREPEATC (vGEN_REWRITE_CONV vI [vFCONS])) in
    fun tybijpairs consindex conthms rath ->
      let isocons = map (create_recursion_iso_constructor consindex) conthms in
      let ty = type_of(hd isocons) in
      let fcons = mk_const("FCONS",[ty,aty])
      and fnil = mk_const("FNIL",[ty,aty]) in
      let bigfun = itlist (mk_binop fcons) isocons fnil in
      let eth = vISPEC bigfun vCONSTR_REC in
      let fn = rator(rand(hd(conjuncts(concl rath)))) in
      let betm = let v,bod = dest_abs(rand(concl eth)) in vsubst[fn,v] bod in
      let vLCONV = vREWR_CONV (vASSUME betm) in
      let fnths =
        map (fun t -> vRIGHT_BETAS [bndvar(rand t)] (vASSUME t)) (hyp rath) in
      let vSIMPER = vPURE_REWRITE_RULE
        (map vSYM fnths @ map fst tybijpairs @ [vFST; vSND; vFCONS; vBETA_THM]) in
      let hackdown_rath th =
        let ltm,rtm = dest_eq(concl th) in
        let wargs = snd(strip_comb(rand ltm)) in
        let th1 = vTRANS th (vLCONV rtm) in
        let th2 = vTRANS th1 (vCCONV (rand(concl th1))) in
        let th3 = vTRANS th2 (funpow 2 vRATOR_CONV vBETA_CONV (rand(concl th2))) in
        let th4 = vTRANS th3 (vRATOR_CONV vBETA_CONV (rand(concl th3))) in
        let th5 = vTRANS th4 (vBETA_CONV (rand(concl th4))) in
        vGENL wargs (vSIMPER th5) in
      let rthm = end_itlist vCONJ (map hackdown_rath (vCONJUNCTS rath)) in
      let seqs =
        let unseqs = filter is_eq (hyp rthm) in
        let tys = map (hd -| snd -| dest_type -| type_of -| snd -| snd) consindex in
        map (fun ty -> find
          (fun t -> hd(snd(dest_type(type_of(lhand t)))) = ty) unseqs) tys in
      let rethm = itlist vEXISTS_EQUATION seqs rthm in
      let fethm = vCHOOSE(fn,eth) rethm in
      let pcons = map (repeat rator -| rand -| repeat (snd -| dest_forall))
        (conjuncts(concl rthm)) in
      vGENL pcons fethm in

  (* ----------------------------------------------------------------------- *)
  (* Basic function: returns induction and recursion separately. No parser.  *)
  (* ----------------------------------------------------------------------- *)

  fun def ->
    let defs,rth,ith = justify_inductive_type_model def in
    let neths = prove_model_inhabitation rth in
    let tybijpairs = map (define_inductive_type defs) neths in
    let preds = map (repeat rator -| concl) neths in
    let mkdests = map
      (fun (th,_) -> let tm = lhand(concl th) in rator tm,rator(rand tm))
      tybijpairs in
    let consindex = zip preds mkdests in
    let condefs = map (define_inductive_type_constructor defs consindex)
                      (vCONJUNCTS rth) in
    let conthms = map
      (fun th -> let args = fst(strip_abs(rand(concl th))) in
                 vRIGHT_BETAS args th) condefs in
    let iith = instantiate_induction_theorem consindex ith in
    let fth = derive_induction_theorem consindex tybijpairs conthms iith rth in
    let rath = create_recursive_functions tybijpairs consindex conthms rth in
    let kth = derive_recursion_theorem tybijpairs consindex conthms rath in
    fth,kth;;

(* ------------------------------------------------------------------------- *)
(* Parser to present a nice interface a la Melham.                           *)
(* ------------------------------------------------------------------------- *)

let parse_inductive_type_specification =
  let parse_type_loc src =
    let pty,rst = parse_pretype src in
    type_of_pretype pty,rst in
  let parse_type_conapp src =
    let cn,sps =
     match src with (Ident cn)::sps -> cn,sps
                  | _ -> fail() in
    let tys,rst = many parse_type_loc sps in
    (cn,tys),rst in
  let parse_type_clause src =
    let tn,sps =
      match src with (Ident tn)::sps -> tn,sps
                   | _ -> fail() in
    let tys,rst = (a (Ident "=") ++ listof parse_type_conapp (a (Resword "|"))
                                   "type definition clauses"
                   >> snd) sps in
    (mk_vartype tn,tys),rst in
  let parse_type_definition =
    listof parse_type_clause (a (Resword ";")) "type definition" in
  fun s ->
    let spec,rst = (parse_type_definition -| lex -| explode) s in
    if rst = [] then spec
    else failwith "parse_inductive_type_specification: junk after def";;

(* ------------------------------------------------------------------------- *)
(* Use this temporary version to define the sum type.                        *)
(* ------------------------------------------------------------------------- *)

let sum_INDUCT,sum_RECURSION =
  define_type_raw (parse_inductive_type_specification "sum = INL A | INR B");;

let vOUTL = new_recursive_definition sum_RECURSION
  (parse_term "OUTL (INL x :A+B) = x");;

let vOUTR = new_recursive_definition sum_RECURSION
  (parse_term "OUTR (INR y :A+B) = y");;

(* ------------------------------------------------------------------------- *)
(* Generalize the recursion theorem to multiple domain types.                *)
(* (We needed to use a single type to justify it via a proforma theorem.)    *)
(*                                                                           *)
(* NB! Before this is called nontrivially (i.e. more than one new type)      *)
(*     the type constructor ":sum", used internally, must have been defined. *)
(* ------------------------------------------------------------------------- *)

let define_type_raw =
  let generalize_recursion_theorem =
    let vELIM_OUTCOMBS = vGEN_REWRITE_RULE vTOP_DEPTH_CONV [vOUTL; vOUTR] in
    let rec mk_sum tys =
      let k = length tys in
      if k = 1 then hd tys else
      let tys1,tys2 = chop_list (k / 2) tys in
      mk_type("sum",[mk_sum tys1; mk_sum tys2]) in
    let mk_inls =
      let rec mk_inls ty =
        if is_vartype ty then [mk_var("x",ty)] else
        let [@warning "-8"] _,[ty1;ty2] = dest_type ty [@warning "+8"] in
        let inls1 = mk_inls ty1
        and inls2 = mk_inls ty2 in
        let inl = mk_const("INL",[ty1,aty; ty2,bty])
        and inr = mk_const("INR",[ty1,aty; ty2,bty]) in
        map (curry mk_comb inl) inls1 @ map (curry mk_comb inr) inls2 in
      fun ty -> let bods = mk_inls ty in
                map (fun t -> mk_abs(find_term is_var t,t)) bods in
    let mk_outls =
      let rec mk_inls sof ty =
        if is_vartype ty then [sof] else
        let [@warning "-8"] _,[ty1;ty2] = dest_type ty [@warning "+8"] in
        let outl = mk_const("OUTL",[ty1,aty; ty2,bty])
        and outr = mk_const("OUTR",[ty1,aty; ty2,bty]) in
        mk_inls (mk_comb(outl,sof)) ty1 @ mk_inls (mk_comb(outr,sof)) ty2 in
      fun ty -> let x = mk_var("x",ty) in
                map (curry mk_abs x) (mk_inls x ty) in
    let mk_newfun fn outl =
      let s,ty = dest_var fn in
      let dty = hd(snd(dest_type ty)) in
      let x = mk_var("x",dty) in
      let y,bod = dest_abs outl in
      let r = mk_abs(x,vsubst[mk_comb(fn,x),y] bod) in
      let l = mk_var(s,type_of r) in
      let th1 = vASSUME (mk_eq(l,r)) in
      vRIGHT_BETAS [x] th1 in
    fun th ->
      let _avs,ebod = strip_forall(concl th) in
      let evs,bod = strip_exists ebod in
      let n = length evs in
      if n = 1 then th else
      let tys = map (fun i -> mk_vartype ("Z"^(string_of_int i)))
                    (0--(n - 1)) in
      let sty = mk_sum tys in
      let inls = mk_inls sty
      and outls = mk_outls sty in
      let zty = type_of(rand(snd(strip_forall(hd(conjuncts bod))))) in
      let ith = vINST_TYPE [sty,zty] th in
      let _avs,ebod = strip_forall(concl ith) in
      let evs,bod = strip_exists ebod in
      let fns' = map2 mk_newfun evs outls in
      let fnalist = zip evs (map (rator -| lhs -| concl) fns')
      and inlalist = zip evs inls
      and outlalist = zip evs outls in
      let hack_clause tm =
        let _avs,bod = strip_forall tm in
        let l,r = dest_eq bod in
        let fn,args = strip_comb r in
        let pargs = map
          (fun a -> let g = genvar(type_of a) in
                    if is_var a then g,g else
                    let outl = assoc (rator a) outlalist in
                    mk_comb(outl,g),g) args in
        let args',args'' = unzip pargs in
        let inl = assoc (rator l) inlalist in
        let rty = hd(snd(dest_type(type_of inl))) in
        let nty = itlist (mk_fun_ty -| type_of) args' rty in
        let fn' = mk_var(fst(dest_var fn),nty) in
        let r' = list_mk_abs(args'',mk_comb(inl,list_mk_comb(fn',args'))) in
        r',fn in
      let defs = map hack_clause (conjuncts bod) in
      let jth = vBETA_RULE (vSPECL (map fst defs) ith) in
      let bth = vASSUME (snd(strip_exists(concl jth))) in
      let finish_clause th =
        let avs,bod = strip_forall (concl th) in
        let outl = assoc (rator (lhand bod)) outlalist in
        vGENL avs (vBETA_RULE (vAP_TERM outl (vSPECL avs th))) in
      let cth = end_itlist vCONJ (map finish_clause (vCONJUNCTS bth)) in
      let dth = vELIM_OUTCOMBS cth in
      let eth = vGEN_REWRITE_RULE vONCE_DEPTH_CONV (map vSYM fns') dth in
      let fth = itlist vSIMPLE_EXISTS (map snd fnalist) eth in
      let dtms = map (hd -| hyp) fns' in
      let gth = itlist (fun e th -> let l,r = dest_eq e in
                        vMP (vINST [r,l] (vDISCH e th)) (vREFL r)) dtms fth in
      let hth = vPROVE_HYP jth (itlist vSIMPLE_CHOOSE evs gth) in
      let xvs = map (fst -| strip_comb -| rand -| snd -| strip_forall)
                    (conjuncts(concl eth)) in
      vGENL xvs hth in
  fun def -> let ith,rth = define_type_raw def in
             ith,generalize_recursion_theorem rth;;

(* ------------------------------------------------------------------------- *)
(* Set up options and lists.                                                 *)
(* ------------------------------------------------------------------------- *)

let option_INDUCT,option_RECURSION =
  define_type_raw
   (parse_inductive_type_specification "option = NONE | SOME A");;

let list_INDUCT,list_RECURSION =
  define_type_raw
   (parse_inductive_type_specification "list = NIL | CONS A list");;

let vFORALL_OPTION_THM = try Cache.lookup_thm "FORALL_OPTION_THM" with _ ->  prove
 ((parse_term "!P. (!x. P x) <=> P NONE /\\ !a. P(SOME a)"),
  vGEN_TAC ----> vEQ_TAC ----> vREWRITE_TAC[option_INDUCT] ----> vSIMP_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Tools for proving injectivity and distinctness of constructors.           *)
(* ------------------------------------------------------------------------- *)

let prove_constructors_injective =
  let vDEPAIR = vGEN_REWRITE_RULE vTOP_SWEEP_CONV [vPAIR_EQ] in
  let prove_distinctness ax pat =
    let f,args = strip_comb pat in
    let rt = end_itlist (curry mk_pair) args in
    let ty = mk_fun_ty (type_of pat) (type_of rt) in
    let fn = genvar ty in
    let dtm = mk_eq(mk_comb(fn,pat),rt) in
    let eth = prove_recursive_functions_exist ax (list_mk_forall(args,dtm)) in
    let args' = variants args args in
    let atm = mk_eq(pat,list_mk_comb(f,args')) in
    let ath = vASSUME atm in
    let bth = vAP_TERM fn ath in
    let cth1 = vSPECL args (vASSUME(snd(dest_exists(concl eth)))) in
    let cth2 = vINST (zip args' args) cth1 in
    let pth = vTRANS (vTRANS (vSYM cth1) bth) cth2 in
    let qth = vDEPAIR pth in
    let qtm = concl qth in
    let rth = rev_itlist (vC(curry vMK_COMB)) (vCONJUNCTS(vASSUME qtm)) (vREFL f) in
    let tth = vIMP_ANTISYM_RULE (vDISCH atm qth) (vDISCH qtm rth) in
    let uth = vGENL args (vGENL args' tth) in
    vPROVE_HYP eth (vSIMPLE_CHOOSE fn uth) in
  fun ax ->
    let cls = conjuncts(snd(strip_exists(snd(strip_forall(concl ax))))) in
    let pats = map (rand -| lhand -| snd -| strip_forall) cls in
    end_itlist vCONJ (mapfilter (prove_distinctness ax) pats);;

let prove_constructors_distinct =
  let num_ty = (parse_type "num") in
  let rec allopairs f l m =
    if l = [] then [] else
    map (f (hd l)) (tl m) @ allopairs f (tl l) (tl m) in
  let vNEGATE = vGEN_ALL -| vCONV_RULE (vREWR_CONV (vTAUT (parse_term "a ==> F <=> ~a"))) in
  let prove_distinct ax pat =
    let nums = map mk_small_numeral (0--(length pat - 1)) in
    let fn = genvar (mk_type("fun",[type_of(hd pat); num_ty])) in
    let ls = map (curry mk_comb fn) pat in
    let defs = map2 (fun l r -> list_mk_forall(frees (rand l),mk_eq(l,r)))
      ls nums in
    let eth = prove_recursive_functions_exist ax (list_mk_conj defs) in
    let ev,bod = dest_exists(concl eth) in
    let vREWRITE = vGEN_REWRITE_RULE vONCE_DEPTH_CONV (vCONJUNCTS (vASSUME bod)) in
    let pat' = map
     (fun t -> let f,args = if is_numeral t then t,[] else strip_comb t in
               list_mk_comb(f,variants args args)) pat in
    let pairs = allopairs (curry mk_eq) pat pat' in
    let nths = map (vREWRITE -| vAP_TERM fn -| vASSUME) pairs in
    let fths = map2 (fun t th -> vNEGATE (vDISCH t (vCONV_RULE vNUM_EQ_CONV th)))
      pairs nths in
    vCONJUNCTS(vPROVE_HYP eth (vSIMPLE_CHOOSE ev (end_itlist vCONJ fths))) in
  fun ax ->
    let cls = conjuncts(snd(strip_exists(snd(strip_forall(concl ax))))) in
    let lefts = map (dest_comb -| lhand -| snd -| strip_forall) cls in
    let fns = itlist (insert -| fst) lefts [] in
    let pats = map (fun f -> map snd (filter ((=)f -| fst) lefts)) fns in
    end_itlist vCONJ
     (end_itlist (@) (mapfilter (prove_distinct ax) pats));;

(* ------------------------------------------------------------------------- *)
(* Automatically prove the case analysis theorems.                           *)
(* ------------------------------------------------------------------------- *)

let prove_cases_thm =
  let mk_exclauses x rpats =
    let xts = map (fun t -> list_mk_exists(frees t,mk_eq(x,t))) rpats in
    mk_abs(x,list_mk_disj xts) in
  let prove_triv tm =
    let _evs,bod = strip_exists tm in
    let l,r = dest_eq bod in
    if l = r then vREFL l else
    let lf,largs = strip_comb l
    and rf,rargs = strip_comb r in
    if lf = rf then
      let ths = map (vASSUME -| mk_eq) (zip rargs largs) in
      let th1 = rev_itlist (vC (curry vMK_COMB)) ths (vREFL lf) in
      itlist vEXISTS_EQUATION (map concl ths) (vSYM th1)
    else failwith "prove_triv" in
  let rec prove_disj tm =
    if is_disj tm then
      let l,r = dest_disj tm in
      try vDISJ1 (prove_triv l) r
      with Failure _ -> vDISJ2 l (prove_disj r)
    else
      prove_triv tm in
  let prove_eclause tm =
    let avs,bod = strip_forall tm in
    let ctm = if is_imp bod then rand bod else bod in
    let cth = prove_disj ctm in
    let dth = if is_imp bod then vDISCH (lhand bod) cth else cth in
    vGENL avs dth in
  fun th ->
    let _avs,bod = strip_forall(concl th) in
    let cls = map (snd -| strip_forall) (conjuncts(lhand bod)) in
    let pats = map (fun t -> if is_imp t then rand t else t) cls in
    let spats = map dest_comb pats in
    let preds = itlist (insert -| fst) spats [] in
    let rpatlist = map
      (fun pr -> map snd (filter (fun (p,_x) -> p = pr) spats)) preds in
    let xs = make_args "x" (freesl pats) (map (type_of -| hd) rpatlist) in
    let xpreds = map2 mk_exclauses xs rpatlist in
    let ith = vBETA_RULE (vINST (zip xpreds preds) (vSPEC_ALL th)) in
    let eclauses = conjuncts(fst(dest_imp(concl ith))) in
    vMP ith (end_itlist vCONJ (map prove_eclause eclauses));;

(* ------------------------------------------------------------------------- *)
(* Now deal with nested recursion. Need a store of previous theorems.        *)
(* ------------------------------------------------------------------------- *)

inductive_type_store :=
 ["list",(2,list_INDUCT,list_RECURSION);
  "option",(2,option_INDUCT,option_RECURSION);
  "sum",(2,sum_INDUCT,sum_RECURSION)] @
 (!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* Also add a cached rewrite of distinctness and injectivity theorems. Since *)
(* there can be quadratically many distinctness clauses, it would really be  *)
(* preferable to have a conversion, but this seems OK up 100 constructors.   *)
(* ------------------------------------------------------------------------- *)

let basic_rectype_net = ref empty_net;;
let distinctness_store = ref ["bool",vTAUT (parse_term "(T <=> F) <=> F")];;
let injectivity_store = ref [];;

let extend_rectype_net (tyname,(_,_,rth)) =
  let ths1 = try [prove_constructors_distinct rth] with Failure _ -> []
  and ths2 = try [prove_constructors_injective rth] with Failure _ -> [] in
  let canon_thl = itlist (mk_rewrites false) (ths1 @ ths2) [] in
  distinctness_store := map (fun th -> tyname,th) ths1 @ (!distinctness_store);
  injectivity_store := map (fun th -> tyname,th) ths2 @ (!injectivity_store);
  basic_rectype_net :=
    itlist (net_of_thm true) canon_thl (!basic_rectype_net);;

do_list extend_rectype_net (!inductive_type_store);;

(* ------------------------------------------------------------------------- *)
(* Return distinctness and injectivity for a type by simple lookup.          *)
(* ------------------------------------------------------------------------- *)

let distinctness ty = assoc ty (!distinctness_store);;

let injectivity ty = assoc ty (!injectivity_store);;

let cases ty =
  if ty = "num" then num_CASES else
  let _,ith,_ = assoc ty (!inductive_type_store) in prove_cases_thm ith;;

let option_DISTINCT = try Cache.lookup_thm "option_DISTINCT" with _ ->  prove
 ((parse_term "!a:A. ~(SOME a = NONE)"),
  vREWRITE_TAC[distinctness "option"]);;

let option_INJ = try Cache.lookup_thm "option_INJ" with _ ->  prove
 ((parse_term "!a b:A. SOME a = SOME b <=> a = b"),
  vREWRITE_TAC[injectivity "option"]);;

(* ------------------------------------------------------------------------- *)
(* Convenient definitions for type isomorphism.                              *)
(* ------------------------------------------------------------------------- *)

let vISO = new_definition
  (parse_term "ISO (f:A->B) (g:B->A) <=> (!x. f(g x) = x) /\\ (!y. g(f y) = y)");;

let vISO_REFL = try Cache.lookup_thm "ISO_REFL" with _ ->  prove
 ((parse_term "ISO (\\x:A. x) (\\x. x)"),
  vREWRITE_TAC[vISO]);;

let vISO_FUN = try Cache.lookup_thm "ISO_FUN" with _ ->  prove
 ((parse_term "ISO (f:A->A') f' /\\ ISO (g:B->B') g'\n   ==> ISO (\\h a'. g(h(f' a'))) (\\h a. g'(h(f a)))"),
  vREWRITE_TAC[vISO; vFUN_EQ_THM] ----> vMESON_TAC[]);;

let vISO_USAGE = try Cache.lookup_thm "ISO_USAGE" with _ ->  prove
 ((parse_term "ISO f g\n   ==> (!P. (!x. P x) <=> (!x. P(g x))) /\\\n       (!P. (?x. P x) <=> (?x. P(g x))) /\\\n       (!a b. (a = g b) <=> (f a = b))"),
  vREWRITE_TAC[vISO; vFUN_EQ_THM] ----> vMESON_TAC[]);;

(* ------------------------------------------------------------------------- *)
(* Hence extend type definition to nested types.                             *)
(* ------------------------------------------------------------------------- *)

let define_type_raw =

  (* ----------------------------------------------------------------------- *)
  (* Dispose of trivial antecedent.                                          *)
  (* ----------------------------------------------------------------------- *)

  let vTRIV_ANTE_RULE =
    let vTRIV_IMP_CONV tm =
      let avs,bod = strip_forall tm in
      let bth =
        if is_eq bod then vREFL (rand bod) else
        let ant,con = dest_imp bod in
        let ith = vSUBS_CONV (vCONJUNCTS(vASSUME ant)) (lhs con) in
        vDISCH ant ith in
      vGENL avs bth in
    fun th ->
      let tm = concl th in
      if is_imp tm then
        let ant,_con = dest_imp(concl th) in
        let cjs = conjuncts ant in
        let cths = map vTRIV_IMP_CONV cjs in
        vMP th (end_itlist vCONJ cths)
      else th in

  (* ----------------------------------------------------------------------- *)
  (* Lift type bijections to "arbitrary" (well, free rec or function) type.  *)
  (* ----------------------------------------------------------------------- *)

  let vISO_EXPAND_CONV = vPURE_ONCE_REWRITE_CONV[vISO] in

  let rec lift_type_bijections iths cty =
    let itys = map (hd -| snd -| dest_type -| type_of -| lhand -| concl) iths in
    try assoc cty (zip itys iths) with Failure _ ->
    if not (exists (vC occurs_in cty) itys)
    then vINST_TYPE [cty,aty] vISO_REFL else
    let tycon,isotys = dest_type cty in
    if tycon = "fun"
    then vMATCH_MP vISO_FUN
           (end_itlist vCONJ (map (lift_type_bijections iths) isotys))
    else failwith
            ("lift_type_bijections: Unexpected type operator \""^tycon^"\"") in

  (* ----------------------------------------------------------------------- *)
  (* Prove isomorphism of nested types where former is the smaller.          *)
  (* ----------------------------------------------------------------------- *)

  let vDE_EXISTENTIALIZE_RULE =
    let pth = prove
     ((parse_term "(?) P ==> (c = (@)P) ==> P c"),
      vGEN_REWRITE_TAC (vLAND_CONV -| vRAND_CONV) [vGSYM vETA_AX] ---->
      vDISCH_TAC ----> vDISCH_THEN vSUBST1_TAC ---->
      vMATCH_MP_TAC vSELECT_AX ----> vPOP_ASSUM vACCEPT_TAC) in
    let vUSE_PTH = vMATCH_MP pth in
    let rec vDE_EXISTENTIALIZE_RULE th =
      if not (is_exists(concl th)) then [],th else
      let th1 = vUSE_PTH th in
      let v1 = rand(rand(concl th1)) in
      let gv = genvar(type_of v1) in
      let th2 = vCONV_RULE vBETA_CONV (vUNDISCH (vINST [gv,v1] th1)) in
      let vs,th3 = vDE_EXISTENTIALIZE_RULE th2 in
      gv::vs,th3 in
    vDE_EXISTENTIALIZE_RULE in

  let grab_type = type_of -| rand -| lhand -| snd -| strip_forall in

  let clause_corresponds cl0  =
    let f0,ctm0 = dest_comb (lhs cl0) in
    let c0 = fst(dest_const(fst(strip_comb ctm0))) in
    let dty0,rty0 = dest_fun_ty (type_of f0) in
    fun cl1 ->
      let f1,ctm1 = dest_comb (lhs cl1) in
      let c1 = fst(dest_const(fst(strip_comb ctm1))) in
      let dty1,rty1 = dest_fun_ty (type_of f1) in
      c0 = c1 && dty0 = rty1 && rty0 = dty1 in

  let prove_inductive_types_isomorphic n k (ith0,rth0) (ith1,rth1) =
    let sth0 = vSPEC_ALL rth0
    and sth1 = vSPEC_ALL rth1
    and t_tm = concl vTRUTH in
    let pevs0,pbod0 = strip_exists (concl sth0)
    and pevs1,pbod1 = strip_exists (concl sth1) in
    let pcjs0,_qcjs0 = chop_list k (conjuncts pbod0)
    and pcjs1,_qcjs1 = chop_list k (snd(chop_list n (conjuncts pbod1))) in
    let tyal0 = setify (zip (map grab_type pcjs1) (map grab_type pcjs0)) in
    let tyal1 = map (fun (a,b) -> (b,a)) tyal0 in
    let tyins0 = map
     (fun f -> let domty,ranty = dest_fun_ty (type_of f) in
               tysubst tyal0 domty,ranty) pevs0
    and tyins1 = map
     (fun f -> let domty,ranty = dest_fun_ty (type_of f) in
               tysubst tyal1 domty,ranty) pevs1 in
    let tth0 = vINST_TYPE tyins0 sth0
    and tth1 = vINST_TYPE tyins1 sth1 in
    let _evs0,bod0 = strip_exists(concl tth0)
    and _evs1,bod1 = strip_exists(concl tth1) in
    let lcjs0,rcjs0 = chop_list k (map (snd -| strip_forall) (conjuncts bod0))
    and lcjs1,rcjsx = chop_list k (map (snd -| strip_forall)
      (snd(chop_list n (conjuncts bod1)))) in
    let rcjs1 =  map (fun t -> find (clause_corresponds t) rcjsx) rcjs0 in
    let proc_clause tm0 tm1 =
      let l0,r0 = dest_eq tm0
      and l1,r1 = dest_eq tm1 in
      let vc0,wargs0 = strip_comb r0 in
      let _con0,vargs0 = strip_comb(rand l0) in
      let gargs0 = map (genvar -| type_of) wargs0 in
      let nestf0 = map (fun a -> can (find (fun t -> is_comb t && rand t = a))
        wargs0) vargs0 in
      let targs0 = map2 (fun a f ->
        if f then find (fun t -> is_comb t && rand t = a) wargs0 else a)
         vargs0 nestf0 in
      let gvlist0 = zip wargs0 gargs0 in
      let xargs = map (fun v -> assoc v gvlist0) targs0 in
      let inst0 =
        list_mk_abs(gargs0,list_mk_comb(fst(strip_comb(rand l1)),xargs)),vc0 in
      let vc1,wargs1 = strip_comb r1 in
      let _con1,vargs1 = strip_comb(rand l1) in
      let gargs1 = map (genvar -| type_of) wargs1 in
      let targs1 = map2
        (fun a f -> if f then
                    find (fun t -> is_comb t && rand t = a) wargs1
                    else a) vargs1 nestf0 in
      let gvlist1 = zip wargs1 gargs1 in
      let xargs = map (fun v -> assoc v gvlist1) targs1 in
      let inst1 =
        list_mk_abs(gargs1,list_mk_comb(fst(strip_comb(rand l0)),xargs)),vc1 in
      inst0,inst1 in
    let insts0,insts1 = unzip (map2 proc_clause (lcjs0@rcjs0) (lcjs1@rcjs1)) in
    let uth0 = vBETA_RULE(vINST insts0 tth0)
    and uth1 = vBETA_RULE(vINST insts1 tth1) in
    let efvs0,sth0 = vDE_EXISTENTIALIZE_RULE uth0
    and efvs1,sth1 = vDE_EXISTENTIALIZE_RULE uth1 in
    let efvs2 = map
     (fun t1 -> find (fun t2 -> hd(tl(snd(dest_type(type_of t1)))) =
                                hd(snd(dest_type(type_of t2)))) efvs1) efvs0 in
    let isotms = map2 (fun ff gg -> list_mk_icomb "ISO" [ff;gg]) efvs0 efvs2 in
    let ctm = list_mk_conj isotms in
    let cth1 = vISO_EXPAND_CONV ctm in
    let ctm1 = rand(concl cth1) in
    let cjs = conjuncts ctm1 in
    let eee = map (fun n -> n mod 2 = 0) (0--(length cjs - 1)) in
    let cjs1,cjs2 = partition fst (zip eee cjs) in
    let ctm2 = mk_conj(list_mk_conj (map snd cjs1),
                       list_mk_conj (map snd cjs2)) in
    let vDETRIV_RULE = vTRIV_ANTE_RULE -| vREWRITE_RULE[sth0;sth1] in
    let jth0 =
      let itha = vSPEC_ALL ith0 in
      let icjs = conjuncts(rand(concl itha)) in
      let cinsts = map
        (fun tm -> tryfind (fun vtm -> term_match [] vtm tm) icjs)
        (conjuncts (rand ctm2)) in
      let tvs = subtract (fst(strip_forall(concl ith0)))
                  (itlist (fun (_,x,_) -> union (map snd x)) cinsts []) in
      let ctvs =
        map (fun p -> let x = mk_var("x",hd(snd(dest_type(type_of p)))) in
                             mk_abs(x,t_tm),p) tvs in
      vDETRIV_RULE (vINST ctvs (itlist vINSTANTIATE cinsts itha))
    and jth1 =
      let itha = vSPEC_ALL ith1 in
      let icjs = conjuncts(rand(concl itha)) in
      let cinsts = map
        (fun tm -> tryfind (fun vtm -> term_match [] vtm tm) icjs)
        (conjuncts (lhand ctm2)) in
      let tvs = subtract (fst(strip_forall(concl ith1)))
                    (itlist (fun (_,x,_) -> union (map snd x)) cinsts []) in
      let ctvs =
        map (fun p -> let x = mk_var("x",hd(snd(dest_type(type_of p)))) in
                               mk_abs(x,t_tm),p) tvs in
      vDETRIV_RULE (vINST ctvs (itlist vINSTANTIATE cinsts itha)) in
    let cths4 = map2 vCONJ (vCONJUNCTS jth0) (vCONJUNCTS jth1) in
    let cths5 = map (vPURE_ONCE_REWRITE_RULE[vGSYM vISO]) cths4 in
    let cth6 = end_itlist vCONJ cths5 in
    cth6,vCONJ sth0 sth1 in

  (* ----------------------------------------------------------------------- *)
  (* Define nested type by doing a 1-level unwinding.                        *)
  (* ----------------------------------------------------------------------- *)

  let vSCRUB_ASSUMPTION th =
    let hyps = hyp th in
    let eqn = find (fun t -> let x = lhs t in
                             forall (fun u -> not (free_in x (rand u))) hyps)
                   hyps in
    let l,r = dest_eq eqn in
    vMP (vINST [r,l] (vDISCH eqn th)) (vREFL r) in

  let define_type_basecase def =
    let add_id _s = fst(dest_var(genvar bool_ty)) in
    let def' = map (vI $-$ (map (add_id $-$ vI))) def in
    define_type_raw def' in

  let vSIMPLE_BETA_RULE = vGSYM -| vPURE_REWRITE_RULE[vBETA_THM; vFUN_EQ_THM] in
  let vISO_USAGE_RULE = vMATCH_MP vISO_USAGE in
  let vSIMPLE_ISO_EXPAND_RULE = vCONV_RULE(vREWR_CONV vISO) in

  let vREWRITE_FUN_EQ_RULE =
    let ths = itlist (mk_rewrites false) [vFUN_EQ_THM] [] in
    let net = itlist (net_of_thm false) ths (basic_net()) in
    vCONV_RULE -| vGENERAL_REWRITE_CONV true vTOP_DEPTH_CONV net in

  let is_nested vs ty =
    not (is_vartype ty) && not (intersect (tyvars ty) vs = []) in
  let rec modify_type alist ty =
    try rev_assoc ty alist
    with Failure _ -> try
        let tycon,tyargs = dest_type ty in
        mk_type(tycon,map (modify_type alist) tyargs)
    with Failure _ -> ty in
  let modify_item alist (s,l) =
    s,map (modify_type alist) l in
  let modify_clause alist (l,lis) =
     l,map (modify_item alist) lis in
  let recover_clause id tm =
    let con,args = strip_comb tm in
    fst(dest_const con)^id,map type_of args in
  let create_auxiliary_clauses nty =
    let id = fst(dest_var(genvar bool_ty)) in
    let tycon,_tyargs = dest_type nty in
    let k,ith,rth = try assoc tycon (!inductive_type_store) with Failure _ ->
      failwith ("Can't find definition for nested type: "^tycon) in
    let evs,bod = strip_exists(snd(strip_forall(concl rth))) in
    let cjs = map (lhand -| snd -| strip_forall) (conjuncts bod) in
    let rtys = map (hd -| snd -| dest_type -| type_of) evs in
    let tyins = tryfind (fun vty -> type_match vty nty []) rtys in
    let cjs' = map (inst tyins -| rand) (fst(chop_list k cjs)) in
    let mtys = itlist (insert -| type_of) cjs' [] in
    let pcons = map (fun ty -> filter (fun t -> type_of t = ty) cjs') mtys in
    let cls' = zip mtys (map (map (recover_clause id)) pcons) in
    let tyal = map (fun ty -> mk_vartype(fst(dest_type ty)^id),ty) mtys in
    let cls'' = map (modify_type tyal $-$ map (modify_item tyal)) cls' in
    k,tyal,cls'',vINST_TYPE tyins ith,vINST_TYPE tyins rth in
  let rec define_type_nested def =
    let n = length(itlist (@) (map (map fst -| snd) def) []) in
    let newtys = map fst def in
    let utys = unions (itlist (union -| map snd -| snd) def []) in
    let rectys = filter (is_nested newtys) utys in
    if rectys = [] then
      let th1,th2 = define_type_basecase def in n,th1,th2 else
    let nty = hd (sort (fun t1 t2 -> occurs_in t2 t1) rectys) in
    let k,tyal,ncls,ith,rth = create_auxiliary_clauses nty in
    let cls = map (modify_clause tyal) def @ ncls in
    let _,ith1,rth1 = define_type_nested cls in
    let xnewtys = map (hd -| snd -| dest_type -| type_of)
                      (fst(strip_exists(snd(strip_forall(concl rth1))))) in
    let xtyal = map (fun ty -> let s = dest_vartype ty in
                               find (fun t -> fst(dest_type t) = s) xnewtys,ty)
                    (map fst cls) in
    let ith0 = vINST_TYPE xtyal ith
    and rth0 = vINST_TYPE xtyal rth in
    let isoth,rclauses =
      prove_inductive_types_isomorphic n k (ith0,rth0) (ith1,rth1) in
    let irth3 = vCONJ ith1 rth1 in
    let vtylist = itlist (insert -| type_of) (variables(concl irth3)) [] in
    let isoths = vCONJUNCTS isoth in
    let isotys = map (hd -| snd -| dest_type -| type_of -| lhand -| concl) isoths in
    let ctylist = filter
      (fun ty -> exists (fun t -> occurs_in t ty) isotys) vtylist in
    let atylist = itlist
      (union -| striplist dest_fun_ty) ctylist [] in
    let isoths' = map (lift_type_bijections isoths)
      (filter (fun ty -> exists (fun t -> occurs_in t ty) isotys) atylist) in
    let cisoths = map (vBETA_RULE -| lift_type_bijections isoths')
      ctylist in
    let uisoths = map vISO_USAGE_RULE cisoths in
    let visoths = map (vASSUME -| concl) uisoths in
    let irth4 = itlist vPROVE_HYP uisoths (vREWRITE_FUN_EQ_RULE visoths irth3) in
    let irth5 = vREWRITE_RULE
      (rclauses :: map vSIMPLE_ISO_EXPAND_RULE isoths') irth4 in
    let irth6 = repeat vSCRUB_ASSUMPTION irth5 in
    let ncjs = filter (fun t -> exists (fun v -> not(is_var v))
                             (snd(strip_comb(rand(lhs(snd(strip_forall t)))))))
                      (conjuncts(snd(strip_exists
                         (snd(strip_forall(rand(concl irth6))))))) in
    let mk_newcon tm =
      let vs,bod = strip_forall tm in
      let rdeb = rand(lhs bod) in
      let rdef = list_mk_abs(vs,rdeb) in
      let newname = fst(dest_var(genvar bool_ty)) in
      let def = mk_eq(mk_var(newname,type_of rdef),rdef) in
      let dth = new_definition def in
      vSIMPLE_BETA_RULE dth in
    let dths = map mk_newcon ncjs in
    let ith6,rth6 = vCONJ_PAIR(vPURE_REWRITE_RULE dths irth6) in
    n,ith6,rth6 in
  fun def ->
    let newtys = map fst def in
    let truecons = itlist (@) (map (map fst -| snd) def) [] in
    let (p,ith0,rth0) = define_type_nested def in
    let avs,etm = strip_forall(concl rth0) in
    let allcls = conjuncts(snd(strip_exists etm)) in
    let relcls = fst(chop_list (length truecons) allcls) in
    let gencons =
      map (repeat rator -| rand -| lhand -| snd -| strip_forall) relcls in
    let cdefs =
      map2 (fun s r -> vSYM(new_definition (mk_eq(mk_var(s,type_of r),r))))
           truecons gencons in
    let tavs = make_args "f" [] (map type_of avs) in
    let ith1 = vSUBS cdefs ith0
    and rth1 = vGENL tavs (vSUBS cdefs (vSPECL tavs rth0)) in
    let retval = p,ith1,rth1 in
    let newentries = map (fun s -> dest_vartype s,retval) newtys in
    (inductive_type_store := newentries @ (!inductive_type_store);
     do_list extend_rectype_net newentries; ith1,rth1);;

(* ----------------------------------------------------------------------- *)
(* The overall function, with rather crude string-based benignity.         *)
(* ----------------------------------------------------------------------- *)

let the_inductive_types = ref
 ["list = NIL | CONS A list",(list_INDUCT,list_RECURSION);
  "option = NONE | SOME A",(option_INDUCT,option_RECURSION);
  "sum = INL A | INR B",(sum_INDUCT,sum_RECURSION)];;

let define_type s =
  try let retval = assoc s (!the_inductive_types) in
      (warn true "Benign redefinition of inductive type"; retval)
  with Failure _ ->
      let defspec = parse_inductive_type_specification s in
      let newtypes = map fst defspec
      and constructors = itlist ((@) -| map fst) (map snd defspec) [] in
      if not(length(setify newtypes) = length newtypes)
      then failwith "define_type: multiple definitions of a type"
      else if not(length(setify constructors) = length constructors)
      then failwith "define_type: multiple instances of a constructor"
      else if exists (can get_type_arity -| dest_vartype) newtypes
      then let t = find (can get_type_arity) (map dest_vartype newtypes) in
           failwith("define_type: type :"^t^" already defined")
      else if exists (can get_const_type) constructors
      then let t = find (can get_const_type) constructors in
           failwith("define_type: constant "^t^" already defined")
      else
        let retval = define_type_raw defspec in
        the_inductive_types := (s,retval)::(!the_inductive_types); retval;;

(* ------------------------------------------------------------------------- *)
(* Unwinding, and application of patterns. Add easy cases to default net.    *)
(* ------------------------------------------------------------------------- *)

let vUNWIND_CONV,vMATCH_CONV =
  let pth_0 = prove
   ((parse_term "(if ?!x. x = a /\\ p then @x. x = a /\\ p else @x. F) =\n     (if p then a else @x. F)"),
    vBOOL_CASES_TAC (parse_term "p:bool") ----> vASM_REWRITE_TAC[vCOND_ID] ---->
    vMESON_TAC[])
  and pth_1 = prove
   ((parse_term "_MATCH x (_SEQPATTERN r s) =\n     (if ?y. r x y then _MATCH x r else _MATCH x s) /\\\n    _FUNCTION (_SEQPATTERN r s) x =\n     (if ?y. r x y then _FUNCTION r x else _FUNCTION s x)"),
    vREWRITE_TAC[_MATCH; _SEQPATTERN; _FUNCTION] ---->
    vMESON_TAC[])
  and pth_2 = prove
   ((parse_term "((?y. _UNGUARDED_PATTERN (GEQ s t) (GEQ u y)) <=> s = t) /\\\n     ((?y. _GUARDED_PATTERN (GEQ s t) p (GEQ u y)) <=> s = t /\\ p)"),
    vREWRITE_TAC[_UNGUARDED_PATTERN; _GUARDED_PATTERN; vGEQ_DEF] ---->
    vMESON_TAC[])
  and pth_3 = prove
   ((parse_term "(_MATCH x (\\y z. P y z) = if ?!z. P x z then @z. P x z else @x. F) /\\\n     (_FUNCTION (\\y z. P y z) x = if ?!z. P x z then @z. P x z else @x. F)"),
    vREWRITE_TAC[_MATCH; _FUNCTION])
  and pth_4 = prove
   ((parse_term "(_UNGUARDED_PATTERN (GEQ s t) (GEQ u y) <=> y = u /\\ s = t) /\\\n     (_GUARDED_PATTERN (GEQ s t) p (GEQ u y) <=> y = u /\\ s = t /\\ p)"),
    vREWRITE_TAC[_UNGUARDED_PATTERN; _GUARDED_PATTERN; vGEQ_DEF] ---->
    vMESON_TAC[])
  and pth_5 = prove
   ((parse_term "(if ?!z. z = k then @z. z = k else @x. F) = k"),
    vMESON_TAC[]) in
  let rec vINSIDE_EXISTS_CONV conv tm =
    if is_exists tm then vBINDER_CONV (vINSIDE_EXISTS_CONV conv) tm
    else conv tm in
  let vPUSH_EXISTS_CONV =
    let econv = vREWR_CONV vSWAP_EXISTS_THM in
    let rec conv bc tm =
      try (econv +---> vBINDER_CONV(conv bc)) tm
      with Failure _ -> bc tm in
    conv in
  let vBREAK_CONS_CONV =
    let conv2 = vGEN_REWRITE_CONV vDEPTH_CONV [vAND_CLAUSES; vOR_CLAUSES] +--->
                vASSOC_CONV vCONJ_ASSOC in
    fun tm ->
      let conv0 = vTOP_SWEEP_CONV(vREWRITES_CONV(!basic_rectype_net)) in
      let conv1 = if is_conj tm then vLAND_CONV conv0 else conv0 in
      (conv1 +---> conv2) tm in
  let vUNWIND_CONV =
    let baseconv = vGEN_REWRITE_CONV vI
      [vUNWIND_THM1; vUNWIND_THM2;
       vEQT_INTRO(vSPEC_ALL vEXISTS_REFL);
       vEQT_INTRO(vGSYM(vSPEC_ALL vEXISTS_REFL))] in
    let rec vUNWIND_CONV tm =
      let evs,bod = strip_exists tm in
      let eqs = conjuncts bod in
      try let eq = find
           (fun tm -> is_eq tm &&
                      let l,r = dest_eq tm in
                      (mem l evs && not (free_in l r)) ||
                      (mem r evs && not (free_in r l))) eqs in
          let l,r = dest_eq eq in
          let v = if mem l evs && not (free_in l r) then l else r in
          let cjs' = eq::(subtract eqs [eq]) in
          let n = length evs - (1 + index v (rev evs)) in
          let th1 = vCONJ_ACI_RULE(mk_eq(bod,list_mk_conj cjs')) in
          let th2 = itlist vMK_EXISTS evs th1 in
          let th3 = funpow n vBINDER_CONV (vPUSH_EXISTS_CONV baseconv)
                      (rand(concl th2)) in
          vCONV_RULE (vRAND_CONV vUNWIND_CONV) (vTRANS th2 th3)
       with Failure _ -> vREFL tm in
     vUNWIND_CONV in
  let vMATCH_SEQPATTERN_CONV =
    vGEN_REWRITE_CONV vI [pth_1] +--->
    vRATOR_CONV(vLAND_CONV
     (vBINDER_CONV(vRATOR_CONV vBETA_CONV +---> vBETA_CONV) +--->
      vPUSH_EXISTS_CONV(vGEN_REWRITE_CONV vI [pth_2] +---> vBREAK_CONS_CONV) +--->
      vUNWIND_CONV +--->
      vGEN_REWRITE_CONV vDEPTH_CONV
       [vEQT_INTRO(vSPEC_ALL vEQ_REFL); vAND_CLAUSES] +--->
      vGEN_REWRITE_CONV vDEPTH_CONV [vEXISTS_SIMP]))
  and vMATCH_ONEPATTERN_CONV tm =
    let th1 = vGEN_REWRITE_CONV vI [pth_3] tm in
    let tm' = body(rand(lhand(rand(concl th1)))) in
    let th2 = (vINSIDE_EXISTS_CONV
                (vGEN_REWRITE_CONV vI [pth_4] +--->
                 vRAND_CONV vBREAK_CONS_CONV) +--->
               vUNWIND_CONV +--->
               vGEN_REWRITE_CONV vDEPTH_CONV
                [vEQT_INTRO(vSPEC_ALL vEQ_REFL); vAND_CLAUSES] +--->
               vGEN_REWRITE_CONV vDEPTH_CONV [vEXISTS_SIMP])
              tm' in
    let conv tm = if tm = lhand(concl th2) then th2 else fail() in
    vCONV_RULE
        (vRAND_CONV (vRATOR_CONV
          (vCOMB2_CONV (vRAND_CONV (vBINDER_CONV conv)) (vBINDER_CONV conv))))
        th1 in
  let vMATCH_SEQPATTERN_CONV_TRIV =
    vMATCH_SEQPATTERN_CONV +--->
    vGEN_REWRITE_CONV vI [vCOND_CLAUSES]
  and vMATCH_SEQPATTERN_CONV_GEN =
    vMATCH_SEQPATTERN_CONV +--->
    vGEN_REWRITE_CONV vTRY_CONV [vCOND_CLAUSES]
  and vMATCH_ONEPATTERN_CONV_TRIV =
    vMATCH_ONEPATTERN_CONV +--->
    vGEN_REWRITE_CONV vI [pth_5]
  and vMATCH_ONEPATTERN_CONV_GEN =
    vMATCH_ONEPATTERN_CONV +--->
    vGEN_REWRITE_CONV vTRY_CONV [pth_0; pth_5] in
  do_list extend_basic_convs
   ["MATCH_SEQPATTERN_CONV",
    ((parse_term "_MATCH x (_SEQPATTERN r s)"),vMATCH_SEQPATTERN_CONV_TRIV);
    "FUN_SEQPATTERN_CONV",
    ((parse_term "_FUNCTION (_SEQPATTERN r s) x"),vMATCH_SEQPATTERN_CONV_TRIV);
    "MATCH_ONEPATTERN_CONV",
    ((parse_term "_MATCH x (\\y z. P y z)"),vMATCH_ONEPATTERN_CONV_TRIV);
    "FUN_ONEPATTERN_CONV",
    ((parse_term "_FUNCTION (\\y z. P y z) x"),vMATCH_ONEPATTERN_CONV_TRIV)];
  (vCHANGED_CONV vUNWIND_CONV,
   (vMATCH_SEQPATTERN_CONV_GEN ||--> vMATCH_ONEPATTERN_CONV_GEN));;

let vFORALL_UNWIND_CONV =
  let vPUSH_FORALL_CONV =
     let econv = vREWR_CONV vSWAP_FORALL_THM in
     let rec conv bc tm =
       try (econv +---> vBINDER_CONV(conv bc)) tm
       with Failure _ -> bc tm in
     conv in
  let baseconv = vGEN_REWRITE_CONV vI
   [vMESON[] (parse_term "(!x. x = a /\\ p x ==> q x) <=> (p a ==> q a)");
    vMESON[] (parse_term "(!x. a = x /\\ p x ==> q x) <=> (p a ==> q a)");
    vMESON[] (parse_term "(!x. x = a ==> q x) <=> q a");
    vMESON[] (parse_term "(!x. a = x ==> q x) <=> q a")] in
  let rec vFORALL_UNWIND_CONV tm =
    try let avs,bod = strip_forall tm in
        let ant,con = dest_imp bod in
        let eqs = conjuncts ant in
        let eq = find (fun tm ->
          is_eq tm &&
          let l,r = dest_eq tm in
          (mem l avs && not (free_in l r)) ||
          (mem r avs && not (free_in r l))) eqs in
        let l,r = dest_eq eq in
        let v = if mem l avs && not (free_in l r) then l else r in
        let cjs' = eq::(subtract eqs [eq]) in
        let n = length avs - (1 + index v (rev avs)) in
        let th1 = vCONJ_ACI_RULE(mk_eq(ant,list_mk_conj cjs')) in
        let th2 = vAP_THM (vAP_TERM (rator(rator bod)) th1) con in
        let th3 = itlist vMK_FORALL avs th2 in
        let th4 = funpow n vBINDER_CONV (vPUSH_FORALL_CONV baseconv)
                    (rand(concl th3)) in
        vCONV_RULE (vRAND_CONV vFORALL_UNWIND_CONV) (vTRANS th3 th4)
    with Failure _ -> vREFL tm in
  vFORALL_UNWIND_CONV;;
