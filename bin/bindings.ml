open Typedtree

let print_tree_flag = ref false

let gen_sed_flag = ref false

let arg_list =
  Arg.align [("-pt", Arg.Set print_tree_flag, " Printtyp"); ("-s", Arg.Set gen_sed_flag, " Generate sed script")]

let arg_usage = "bindings FILE.cmt : list top level bindings of interest"

let format_type t = String.concat "" (String.split_on_char '\n' (Format.asprintf "%a" Printtyp.type_scheme t))

let format_position pos =
  string_of_int pos.Lexing.pos_lnum ^ "." ^ string_of_int (pos.pos_cnum - pos.pos_bol (*begining of line*))

let format_location ?(fname = false) Location.{loc_start; loc_end; _ (*loc_ghost*)} =
  Format.sprintf "%s%s,%s"
    (if fname then loc_start.pos_fname ^ ":" else "")
    (format_position loc_start) (format_position loc_end)

let env_of_only_summary env =
  try Env.env_of_only_summary Envaux.env_from_summary env
  with Envaux.Error err ->
    Format.eprintf "%a@." Envaux.report_error err ;
    exit 2

let uppercase_id = Str.regexp "v[A-Z][A-Z0-9']*\\($\\|_[a-zA-Z0-9'_]*$\\)"

(* Theorem names excluded from the transform because they were rebound. *)
let excluded_thms = ["NOT_SUC"; "num_INDUCTION"; "num_Axiom"]

(* We can only try cache lookup for functions that do not have side effects -- note argument
 * binding expressions could produce side effects beyond our ability to check *)
let possible_candidates =
  [ "Hol.Tactics.prove"
  ; "vINT_OF_REAL_THM"
  ; "Hol.Simp.vREWRITE_RULE"
  ; "Hol.Drule.vMATCH_MP"
  ; "Hol.Lib.end_itlist"
  ; "vINT_ARITH"
  ; "vHAS_SIZE_DIMINDEX_RULE" ]

let gen_sed loc typ f =
  if typ = "Hol.Fusion.thm" then
    let open Location in
    let name =
      if Str.string_match uppercase_id loc.txt 0 then String.sub loc.txt 1 (String.length loc.txt - 1) else loc.txt
    in
    if List.mem f possible_candidates && not (List.mem name excluded_thms) then
      Format.printf "%is/=/= try Cache.lookup_thm \"%s\" with _ -> /\n" loc.loc.loc_end.Lexing.pos_lnum name

let exp_ident exp = match exp.exp_desc with Texp_ident (path, _, _) -> Path.name path | _ -> ""

let value_binding {vb_pat; vb_expr; _} =
  match (vb_pat.pat_desc, vb_expr.exp_desc) with
  | Tpat_var (ident, loc), Texp_apply (fexpr, _arg_bindings) ->
      let name = Ident.name ident in
      let typ = format_type vb_pat.pat_type in
      let fun_name = exp_ident fexpr in
      if !gen_sed_flag then gen_sed loc typ fun_name
      else Format.printf "%s (%s), type: %s, fun: %s\n" name (format_location loc.loc) typ fun_name
  | _ -> ()

let structure_item {str_desc; _} =
  match str_desc with Tstr_value (_rec_flag, bindings) -> List.iter value_binding bindings | _ -> ()

let structure {str_items; _} = List.iter structure_item str_items

let cmt_name fn =
  if Filename.check_suffix fn ".ml" then
    let dir = Filename.dirname fn in
    let base = Filename.basename fn |> Filename.remove_extension in
    Format.sprintf "_build/default/%s/.%s.objs/byte/%s__%s.cmt" dir dir dir (String.capitalize_ascii base)
  else fn

let main () =
  Arg.parse_expand arg_list
    (fun fname ->
      let fn = cmt_name fname in
      if Filename.check_suffix fn ".cmt" then (
        Compmisc.init_path () ;
        let cmt = Cmt_format.read_cmt fn in
        match cmt.cmt_annots with
        | Cmt_format.Implementation typed ->
            if !print_tree_flag then Printtyped.implementation Format.std_formatter typed else structure typed
        | _ -> () )
      else (
        Printf.fprintf stderr "Error: %s does not end in .ml or .cmt!\n" fn ;
        Arg.usage arg_list arg_usage ) )
    arg_usage

let () = main ()
