(* There are things that can't be done at syntax level, like distinguishing 
 * module and constructor names. Also "(* *)" embedded in comments won't be
 * process correctly. *)
let start_comment = [%sedlex.regexp? "(*"]
let end_comment = [%sedlex.regexp? "*)"]
let dquote = [%sedlex.regexp? '"']
let squote = [%sedlex.regexp? '\'']
let backtick = [%sedlex.regexp? '`']
let till_backtick = [%sedlex.regexp? Star (Compl backtick), backtick] 
let letter = [%sedlex.regexp? 'A'..'Z' | 'a'..'z']
let digit = [%sedlex.regexp? '0'..'9']
let hex = [%sedlex.regexp? digit | 'A'..'F' | 'a'..'f']
let ident = [%sedlex.regexp? (letter | '_'), Star (letter | digit | '_' | '\'')]
let num = [%sedlex.regexp? digit, Star (letter | digit | '_' | '.')]
let escape = [%sedlex.regexp? '\\', ((Chars "\\\"'ntbr") | "space" | (digit,digit,digit) | ('x', hex, hex) | ('o', '0'..'3', '0'..'7', '0'..'7'))]

module Coding = Sedlexing.Latin1
let lexeme = Coding.lexeme

let copy oc buf = output_string oc (lexeme buf)

let hol_uppercase_id = Str.regexp "[A-Z][A-Z0-9_']*$"

let convert_ident s = 
        match s with 
        | "Pervasives" -> "Stdlib"
        | "THEN" -> "---->"
        | "THENC" -> "+--->"
        | "THENL" -> "++-->"
        | "THEN_TCL" -> "+++->"
        | "ORELSE" -> "|--->"
        | "ORELSEC" -> "||-->"
        | "ORELSE_TCL" -> "|||->"
        | "F_F" -> "$-$"
        | _ -> if Str.string_match hol_uppercase_id s 0 then "v" ^ s else s 

let rec regular oc buf =
        match%sedlex buf with
        | start_comment -> copy oc buf; comment oc buf
        | dquote -> copy oc buf; sliteral oc buf
        | squote -> copy oc buf; cliteral oc buf
        | backtick -> output_string oc "("; quotation oc buf
        | num -> copy oc buf; regular oc buf
        | " o " -> output_string oc " -| "; regular oc buf
        | ident -> lexeme buf |> convert_ident |> output_string oc; regular oc buf
        | any -> copy oc buf; regular oc buf
        | eof -> ()
        | _ -> assert false
and quotation oc buf =
        match%sedlex buf with
        | till_backtick -> let s = lexeme buf in let n = String.length s in 
        String.sub s 0 (n-1) |> Quote.quotexpander |> output_string oc; output_string oc ")"; regular oc buf
        | _ -> assert false
and sliteral oc buf =
        match%sedlex buf with
        | escape -> copy oc buf; sliteral oc buf
        | '\n' -> assert false
        | Compl '"' -> copy oc buf; sliteral oc buf
        | dquote -> copy oc buf; regular oc buf
        | _ -> assert false
and cliteral oc buf =
        match%sedlex buf with
        | escape -> copy oc buf; closing_squote oc buf
        | Compl '\'' -> copy oc buf; closing_squote oc buf
        | _ -> assert false
and closing_squote oc buf =
        match%sedlex buf with
        | squote -> copy oc buf; regular oc buf
        | _ -> assert false
and comment oc buf =
        match%sedlex buf with
        | end_comment -> output_string oc (lexeme buf); regular oc buf
        | any -> output_string oc (lexeme buf); comment oc buf
        | _ -> assert false

let () = 
        (*let lexbuf = Coding.from_string "foo`bar\\p` I F 0E2 \"AWS\\t\" '\\n' A2W_E Comb(Comb(Comb Aabv(* some comments *)" in*)
        let lexbuf = Coding.from_channel stdin in
        regular stdout lexbuf; flush_all ()
