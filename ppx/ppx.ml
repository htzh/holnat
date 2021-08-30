open Ppxlib

let q_expand ~ctxt s =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let c = String.sub s 0 1 in
  let n = String.length s - 1 in
  if c = ":" then
    let ps = String.sub s 1 n |> Ast_builder.Default.estring ~loc in
    [%expr parse_type [%e ps]]
  else if c = ";" then
    let ps = Ast_builder.Default.estring ~loc s in
    [%expr parse_qproof [%e ps]]
  else if String.sub s n 1 = ":" then
    let ps = String.sub s 0 n |> Ast_builder.Default.estring ~loc in
    [%expr [%e ps]]
  else
    let ps = Ast_builder.Default.estring ~loc s in
    [%expr parse_term [%e ps]]

let q_ext =
  Extension.V3.declare "q" Extension.Context.expression Ast_pattern.(single_expr_payload (estring __)) q_expand

let q_rule = Context_free.Rule.extension q_ext

let a_expand ~ctxt name expr =
  let loc = Expansion_context.Extension.extension_point_loc ctxt in
  let pv = Ast_builder.Default.pvar ~loc name in
  match expr.pexp_desc with
  | Pexp_apply ({pexp_desc= Pexp_ident {txt= Lident id; _}; _}, (_, arg) :: _) ->
      if List.mem id ["prove"; "vARITH_RULE"] then
        let tm =
          if id = "prove" then match arg with {pexp_desc= Pexp_tuple [tm; _]; _} -> tm | _ -> arg else arg
        in
        let pn = Ast_builder.Default.estring ~loc name in
        let start = loc.loc_start in
        let desc = Format.sprintf "%s#%i" start.pos_fname start.pos_lnum in
        let pd = Ast_builder.Default.estring ~loc desc in
        [%stri let [%p pv] = accept [%e pn] [%e pd] [%e tm]]
      else [%stri let [%p pv] = [%e expr]]
  | _ -> [%stri let [%p pv] = [%e expr]]

let a_ext =
  Extension.V3.declare "a" Extension.Context.structure_item
    Ast_pattern.(pstr (pstr_value nonrecursive (value_binding ~pat:(ppat_var __) ~expr:__ ^:: nil) ^:: nil))
    a_expand

let a_rule = Context_free.Rule.extension a_ext

let () = Driver.register_transformation ~rules:[a_rule; q_rule] "hol"
