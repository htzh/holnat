open Ppxlib

let expand ~ctxt s =
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
  Extension.V3.declare "q" Extension.Context.expression Ast_pattern.(single_expr_payload (estring __)) expand

let rule = Context_free.Rule.extension q_ext

let () = Driver.register_transformation ~rules:[rule] "q"
