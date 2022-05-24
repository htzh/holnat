open Hol.All

let tyops = types()

let () = Format.printf "let hol_tyops = %a\n" [%show: (string * int) list] tyops

