open Fusion
open Help

let thm_db_name = "db"

let thm_db = ref (Hashtbl.create 3000)

let read_thms fn =
        let ic = open_in_bin fn in
        let thms = (input_value ic : (string*thm) list) in
        close_in ic;
        thms

let () = try
        let db_list = read_thms thm_db_name in
        List.iter (fun (k, v) -> Hashtbl.add !thm_db k v) db_list
with _ -> ()

let lookup_thm k = Hashtbl.find !thm_db k

let save_thm_db () =
        let oc = open_out thm_db_name in
        output_value oc !theorems;
        close_out oc
