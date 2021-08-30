open Hol.Printer
open Hol.Parser
open Hol.Accept

let _ = Hol.Boolean.vEXISTS_DEF (* make sure boolean module is loaded *)

let () = string_of_term [%q {|
        a ==> b /\
        b ==> a
|}] |> print_endline

let () = string_of_type [%q ":A"] |> print_endline

let%a th = prove [%q "A <=> A"] Hol.Tactics.vALL_TAC

let () =
  pp_print_thm Format.std_formatter th ;
  print_newline () ;
  let a, b, _ = List.hd !accepted in
  Format.printf "%s %s\n" a b
