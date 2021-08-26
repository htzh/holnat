(* Test loading all core modules. *)

let compare_lengths () =
  Format.printf "Number of theorems in database: %i\n" (List.length !Hol.Database.theorems) ;
  Format.printf "Number of theorems in cache: %i\n" (Hashtbl.length !Hol.Cache.thm_db)

let () = compare_lengths ()
