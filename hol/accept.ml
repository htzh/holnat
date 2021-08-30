open Fusion

let accepted = ref ([] : (string * string * thm) list)

let accept name desc tm =
        let th = new_axiom tm in
        accepted := (name, desc, th) :: !accepted;
        th

