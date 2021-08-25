open Typedtree

let print_tree_flag = ref false

let arg_list = Arg.align [("-pt", Arg.Set print_tree_flag, " Printtyp")]

let arg_usage = "bindings FILE.cmt : list top level bindings of interest"

let format_type t = String.concat "" (String.split_on_char '\n' (Format.asprintf "%a" Printtyp.type_scheme t))

let format_position pos =
  string_of_int pos.Lexing.pos_lnum ^ "." ^ string_of_int (pos.pos_cnum - pos.pos_bol (*begining of line*))

let format_location ?(fname = false) Location.{loc_start; loc_end; _ (*loc_ghost*)} =
  Format.sprintf "%s%s,%s"
    (if fname then loc_start.pos_fname ^ ":" else "")
    (format_position loc_start) (format_position loc_end)

let value_binding {vb_pat; _} =
  match vb_pat.pat_desc with
  | Tpat_var (ident, loc) ->
      let name = Ident.name ident in
      Format.printf "%s (%s), type: %s\n" name (format_location loc.loc) (format_type vb_pat.pat_type)
  | _ -> ()

let structure_item {str_desc; _} =
  match str_desc with Tstr_value (_rec_flag, bindings) -> List.iter value_binding bindings | _ -> ()

let structure {str_items; _} = List.iter structure_item str_items

let main () =
  Arg.parse_expand arg_list
    (fun fn ->
      if Filename.check_suffix fn ".cmt" then (
        Compmisc.init_path () ;
        let cmt = Cmt_format.read_cmt fn in
        match cmt.cmt_annots with
        | Cmt_format.Implementation typed ->
            if !print_tree_flag then Printtyped.implementation Format.std_formatter typed else structure typed
        | _ -> () )
      else (
        Printf.fprintf stderr "Error: %s does not end in .cmt!\n" fn ;
        Arg.usage arg_list arg_usage ) )
    arg_usage

let () = main ()
