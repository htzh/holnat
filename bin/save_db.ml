(* save thm database *)

(* make sure database is actually loaded *)
let () =
  Format.printf "Number of theorems in database: %i\n" (List.length !Hol.Database.theorems) ;
  Hol.Cache.save_thm_db ()
