{
  open Lexing
  open Parser
  open Format

  let keywords = Hashtbl.create 97
  let () =
    List.iter
      (fun (x,y) -> Hashtbl.add keywords x y)
      [ "ac", AC;
	"and", AND;
	"axiom", AXIOM;
	"bitv", BITV;
        "bool", BOOL;
        "case_split", CASESPLIT;
	"check", CHECK;
	"cut", CUT;
        "distinct", DISTINCT;
        "else", ELSE;
        "end", END;
	"exists", EXISTS;
	"extends", EXTENDS;
        "false", FALSE;
	"forall", FORALL;
	"function", FUNCTION;
	"goal", GOAL;
	"if", IF;
	"in", IN;
	"int", INT;
	"let", LET;
	"logic", LOGIC;
	"not", NOT;
	"or", OR;
	"predicate", PREDICATE;
	"prop", PROP;
	"real", REAL;
	"rewriting", REWRITING;
	"then", THEN;
	"theory", THEORY;
	"true", TRUE;
	"type", TYPE;
	"unit", UNIT;
	"void", VOID;
	"with", WITH;
      ]

  let newline lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_lnum = pos.pos_lnum + 1; pos_bol = pos.pos_cnum }

  let string_buf = Buffer.create 1024

  let char_for_backslash = function
    | 'n' -> '\n'
    | 't' -> '\t'
    | c -> c

  let num0 = Num.Int 0
  let num10 = Num.Int 10
  let num16 = Num.Int 16

  let decnumber s =
    let r = ref num0 in
    for i=0 to String.length s - 1 do
      r := Num.add_num (Num.mult_num num10 !r)
	(Num.num_of_int (Char.code s.[i] - Char.code '0'))
    done;
    !r

  let hexnumber s =
    let r = ref num0 in
    for i=0 to String.length s - 1 do
      let c = s.[i] in
      let v =
	match c with
	  | '0'..'9' -> Char.code c - Char.code '0'
	  | 'a'..'f' -> Char.code c - Char.code 'a' + 10
	  | 'A'..'F' -> Char.code c - Char.code 'A' + 10
	  | _ -> assert false
      in
      r := Num.add_num (Num.mult_num num16 !r) (Num.num_of_int v)
    done;
    !r

  exception Lexcal_Error

}

let newline = '\n'
let space = [' ' '\t' '\r']
let alpha = ['a'-'z' 'A'-'Z']
let letter = alpha | '_'
let digit = ['0'-'9']
let hexdigit = ['0'-'9''a'-'f''A'-'F']
let ident = (letter | '?')(letter | digit | '?' | '\'')*

rule token = parse
  | newline
      { newline lexbuf; token lexbuf }
  | space+
      { token lexbuf }
  (*| '?' (ident ?) as id
    { QM_IDENT id }*)
  | '#' '|' (([^ '|'])+ as id) '|' '#'
      {IDENT id}
  | ident as id (* identifiers *)
      { try
	  let k = Hashtbl.find keywords id in
	  k
	with Not_found ->
	  IDENT id }
  | digit+ as s (* integers *)
      {	INTEGER s }
  | (digit+ as i) ("" as f) ['e' 'E'] (['-' '+']? as sign (digit+ as exp))
  | (digit+ as i) '.' (digit* as f)
      (['e' 'E'] (['-' '+']? as sign (digit+ as exp)))?
  | (digit* as i) '.' (digit+ as f)
      (['e' 'E'] (['-' '+']? as sign (digit+ as exp)))?
      (* decimal real literals *)
      { (*
          Format.eprintf "decimal real literal found: i=%s f=%s sign=%a exp=%a"
          i f so sign so exp;
	*)
        let v =
	  match exp,sign with
	    | Some exp,Some "-" ->
		Num.div_num (decnumber (i^f))
		  (Num.power_num (Num.Int 10) (decnumber exp))
	    | Some exp,_ ->
		Num.mult_num (decnumber (i^f))
		  (Num.power_num (Num.Int 10) (decnumber exp))
	    | None,_ -> decnumber (i^f)
	in
	let v =
	  Num.div_num v
	    (Num.power_num (Num.Int 10) (Num.num_of_int (String.length f)))
	in
	(* Format.eprintf " -> value = %s@." (Num.string_of_num v); *)
	NUM v
      }

      (* hexadecimal real literals a la C99 (0x..p..) *)
  | "0x" (hexdigit+ as e) ('.' (hexdigit* as f))?
      ['p''P'] (['+''-']? as sign) (digit+ as exp)
      { (* Format.eprintf "hex num found: %s" (lexeme lexbuf); *)
	let f = match f with None -> "" | Some f -> f in
	let v =
	  match sign with
	    | "-" ->
		Num.div_num (hexnumber (e^f))
		  (Num.power_num (Num.Int 2) (decnumber exp))
	    | _ ->
		Num.mult_num (hexnumber (e^f))
		  (Num.power_num (Num.Int 2) (decnumber exp))
	in
	let v =
	  Num.div_num v
	    (Num.power_num (Num.Int 16) (Num.num_of_int (String.length f)))
	in
	(* Format.eprintf " -> value = %s@." (Num.string_of_num v); *)
	NUM v
      }
  | "(*"
      { comment lexbuf; token lexbuf }
  | "'"
      { QUOTE }
  | ","
      { COMMA }
  | ";"
      { PV }
  | "("
      { LEFTPAR }
  | ")"
      { RIGHTPAR }
  | ":"
      { COLON }
  | "->"
      { ARROW }
  | "<-"
      { LEFTARROW }
  | "<->"
      { LRARROW }
  | "="
      { EQUAL }
  | "<"
      { LT }
  | "<="
      { LE }
  | ">"
      { GT }
  | ">="
      { GE }
  | "<>"
      { NOTEQ }
  | "+"
      { PLUS }
  | "-"
      { MINUS }
  | "*"
      { TIMES }
  | "/"
      { SLASH }
  | "%"
      { PERCENT }
  | "@"
      { AT }
  | "."
      { DOT }
  | "["
      { LEFTSQ }
  | "]"
      { RIGHTSQ }
  | "{"
      { LEFTBR }
  | "}"
      { RIGHTBR }
  | "|"
      { BAR }
  | "^"
      { HAT }
  | "\""
      { Buffer.clear string_buf; string lexbuf }
  | eof
      { EOF }
  | _ { raise Lexcal_Error }

and comment = parse
  | "*)"
      { () }
  | "(*"
      { comment lexbuf; comment lexbuf }
  | newline
      { newline lexbuf; comment lexbuf }
  | eof
      { raise Lexcal_Error }
  | _
      { comment lexbuf }

and string = parse
  | "\""
      { STRING (Buffer.contents string_buf) }
  | "\\" (_ as c)
      { Buffer.add_char string_buf (char_for_backslash c); string lexbuf }
  | newline
      { newline lexbuf; Buffer.add_char string_buf '\n'; string lexbuf }
  | eof
      {raise Lexcal_Error }
  | _ as c
      { Buffer.add_char string_buf c; string lexbuf }
