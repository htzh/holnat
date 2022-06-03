module H = Hol.All

let _ = H.all_loaded

let tyops = H.types ()

let () = Format.printf "let hol_tyops = %a\n" [%show: (string * int) list] tyops

open Types

let rec copy_hol_type = function H.Tyvar s -> Tyvar s | H.Tyapp (s, hts) -> Tyapp (s, List.map copy_hol_type hts)

let copy_pair_hol_type (a, b) = (a, copy_hol_type b)

let type_constants = List.map copy_pair_hol_type (H.constants ())

let () = Format.printf "let hol_constants = %a\n" [%show: (string * hol_type) list] type_constants

let () = Format.printf "let hol_infixes = %a\n" [%show: (string * (int * string)) list] (H.infixes ())

let () =
  Format.printf "let hol_overload_skeletons = %a\n" [%show: (string * hol_type) list]
    (List.map copy_pair_hol_type !H.the_overload_skeletons)

let () =
  Format.printf "let hol_interface = %a\n" [%show: (string * (string * hol_type)) list]
    (List.map (fun (s, p) -> (s, copy_pair_hol_type p)) !H.the_interface)
