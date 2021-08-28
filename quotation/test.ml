open Hol.Printer
open Hol.Parser

let _ = Hol.Boolean.vEXISTS_DEF (* make sure boolean module is loaded *)

let () = string_of_term [%q {|
        a ==> b /\
        b ==> a
|}] |> print_endline

let () = string_of_type [%q ":A"] |> print_endline
