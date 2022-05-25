module H = Hol.All

let _ = H.all_loaded

let tyops = H.types ()

let () = Format.printf "let hol_tyops = %a\n" [%show: (string * int) list] tyops

type hol_type = Tyvar of string | Tyapp of string * hol_type list [@@deriving show]

let rec copy_hol_type = function H.Tyvar s -> Tyvar s | H.Tyapp (s, hts) -> Tyapp (s, List.map copy_hol_type hts)

let type_constants = List.map (fun (a, b) -> (a, copy_hol_type b)) (H.constants ())

let () = Format.printf "let hol_constants = %a\n" [%show: (string * hol_type) list] type_constants
