%{

  open Parsed
  open Parsing

  let loc () = (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = (rhs_start_pos i, rhs_end_pos i)
  let loc_ij i j = (rhs_start_pos i, rhs_end_pos j)
    
  let mk_ppl loc d = { pp_loc = loc; pp_desc = d }
  let mk_pp d = mk_ppl (loc ()) d
  let mk_pp_i i d = mk_ppl (loc_i i) d
    
  let infix_ppl loc a i b = mk_ppl loc (PPinfix (a, i, b))
  let infix_pp a i b = infix_ppl (loc ()) a i b
    
  let prefix_ppl loc p a = mk_ppl loc (PPprefix (p, a))
  let prefix_pp p a = prefix_ppl (loc ()) p a
    
  let check_binary_mode s =
    begin
      String.iter (fun x ->
	match x with
	| '0' | '1' -> ()
	| _ -> raise Parsing.Parse_error) s;
      s
    end

  let replace_qmark id =
    if String.get id 0 = '?' then
      "qmark_" ^ (String.sub id 1 ((String.length id) - 1))
    else id
%}

%token <string> IDENT
%token <string> INTEGER
%token <string> FLOAT
%token <Num.num> NUM
%token <string> STRING
%token WITH THEORY EXTENDS END
%token AND LEFTARROW ARROW AC AT AXIOM CASESPLIT REWRITING
%token BAR HAT
%token BOOL COLON COMMA PV DISTINCT DOT ELSE EOF EQUAL
%token EXISTS FALSE VOID FORALL FUNCTION GE GOAL GT CHECK CUT ADDTERM
%token IF IN INT BITV
%token LE LET LEFTPAR LEFTSQ LEFTBR LOGIC LRARROW LT MINUS
%token NOT NOTEQ OR PERCENT PLUS PREDICATE PROP
%token QUOTE REAL UNIT
%token RIGHTPAR RIGHTSQ RIGHTBR
%token SLASH
%token THEN TIMES TRUE TYPE

/* Precedences */

%nonassoc WITH
%nonassoc IN
%nonassoc prec_forall prec_exists
%right ARROW LRARROW
%right OR
%right AND
%nonassoc prec_ite
%left prec_relation EQUAL NOTEQ LT LE GT GE
%left PLUS MINUS
%left TIMES SLASH PERCENT AT
%nonassoc HAT
%nonassoc uminus
%nonassoc NOT DOT
%right prec_named
%nonassoc CHECK CUT ADDTERM
%left LEFTSQ
%nonassoc LIDENT

%type <Parsed.lexpr list> trigger
%start trigger
%type <Parsed.lexpr> lexpr
%start lexpr
%type <Parsed.file> file
%start file
%%

file:
| list1_decl EOF {$1}
| EOF {[]}
  ;

list1_decl:
| decl {[$1]}
| decl list1_decl
    {$1 :: $2}
;

decl:
| TYPE type_vars ident
    { TypeDecl (loc_ij 1 2, $2, $3, Abstract) }
| TYPE type_vars ident EQUAL list1_constructors_sep_bar
   { TypeDecl (loc_i 2, $2, $3, Enum $5 ) }
| TYPE type_vars ident EQUAL record_type
   { TypeDecl (loc_i 2, $2, $3, Record $5 ) }
| LOGIC ac_modifier list1_named_ident_sep_comma COLON logic_type
   { Logic (loc (), $2, $3, $5) }
| FUNCTION named_ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR COLON
  primitive_type EQUAL lexpr
   { Function_def (loc (), $2, $4, $7, $9) }
| PREDICATE named_ident EQUAL lexpr
   { Predicate_def (loc (), $2, [], $4) }
| PREDICATE named_ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR EQUAL lexpr
   { Predicate_def (loc (), $2, $4, $7) }
| AXIOM ident COLON lexpr
   { Axiom (loc (), $2, $4) }
| REWRITING ident COLON list1_lexpr_sep_pv
   { Rewriting(loc (), $2, $4) }
| GOAL ident COLON lexpr
   { Goal (loc (), $2, $4) }
;

ac_modifier:
  /* */ { Other }
| AC    { Ac }

primitive_type:
| INT
   { PPTint }
| BOOL
   { PPTbool }
| REAL
   { PPTreal }
| UNIT
   { PPTunit }
| BITV LEFTSQ INTEGER RIGHTSQ
   { PPTbitv(int_of_string $3) }
| ident
   { PPTexternal ([], $1, loc()) }
| type_var
   { PPTvarid ($1, loc()) }
| primitive_type ident
   { PPTexternal ([$1], $2, loc_i 2) }
| LEFTPAR list1_primitive_type_sep_comma RIGHTPAR ident
   { PPTexternal ($2, $4, loc_i 4) }
;

logic_type:
| list0_primitive_type_sep_comma ARROW PROP
   { PPredicate $1 }
| PROP
   { PPredicate [] }
| list0_primitive_type_sep_comma ARROW primitive_type
   { PFunction ($1, $3) }
| primitive_type
   { PFunction ([], $1) }
;

list1_primitive_type_sep_comma:
| primitive_type                                      { [$1] }
| primitive_type COMMA list1_primitive_type_sep_comma { $1 :: $3 }
;

list0_primitive_type_sep_comma:
| /* epsilon */                  { [] }
| list1_primitive_type_sep_comma { $1 }
;

list0_logic_binder_sep_comma:
| /* epsilon */                { [] }
| list1_logic_binder_sep_comma { $1 }
;

list1_logic_binder_sep_comma:
| logic_binder                                    { [$1] }
| logic_binder COMMA list1_logic_binder_sep_comma { $1 :: $3 }
;

logic_binder:
| ident COLON primitive_type
    { (loc_i 1, $1, $3) }
;

list1_constructors_sep_bar:
| ident { [$1] }
| ident BAR list1_constructors_sep_bar { $1 :: $3}
;

ac_modifier:
  /* */ { Other }
| AC    { Ac }

primitive_type:
| INT
   { PPTint }
| BOOL
   { PPTbool }
| REAL
   { PPTreal }
| UNIT
   { PPTunit }
| BITV LEFTSQ INTEGER RIGHTSQ
   { PPTbitv(int_of_string $3) }
| ident
   { PPTexternal ([], $1, loc ()) }
| type_var
   { PPTvarid ($1, loc ()) }
| primitive_type ident
   { PPTexternal ([$1], $2, loc_i 2) }
| LEFTPAR list1_primitive_type_sep_comma RIGHTPAR ident
   { PPTexternal ($2, $4, loc_i 4) }
;

logic_type:
| list0_primitive_type_sep_comma ARROW PROP
    { PPredicate $1 }
| PROP
   { PPredicate [] }
| list0_primitive_type_sep_comma ARROW primitive_type
   { PFunction ($1, $3) }
| primitive_type
   { PFunction ([], $1) }
;

list1_primitive_type_sep_comma:
| primitive_type                                      { [$1] }
| primitive_type COMMA list1_primitive_type_sep_comma { $1 :: $3 }
;

list0_primitive_type_sep_comma:
| /* epsilon */                  { [] }
| list1_primitive_type_sep_comma { $1 }
;

list0_logic_binder_sep_comma:
| /* epsilon */                { [] }
| list1_logic_binder_sep_comma { $1 }
;

list1_logic_binder_sep_comma:
| logic_binder                                    { [$1] }
| logic_binder COMMA list1_logic_binder_sep_comma { $1 :: $3 }
;

logic_binder:
| ident COLON primitive_type
    { (loc_i 1, $1, $3) }
;

list1_constructors_sep_bar:
| ident { [$1] }
| ident BAR list1_constructors_sep_bar { $1 :: $3}
;


lexpr:

| simple_expr { $1 }

/* binary operators */

| lexpr PLUS lexpr
   {infix_pp $1 PPadd $3 }
| lexpr MINUS lexpr
   {infix_pp $1 PPsub $3 }
| lexpr TIMES lexpr
   {infix_pp $1 PPmul $3 }
| lexpr SLASH lexpr
   {infix_pp $1 PPdiv $3 }
| lexpr PERCENT lexpr
   {infix_pp $1 PPmod $3 }
| lexpr AND lexpr
   {infix_pp $1 PPand $3 }
| lexpr OR lexpr
   {infix_pp $1 PPor $3 }
| lexpr LRARROW lexpr
   {infix_pp $1 PPiff $3 }
| lexpr ARROW lexpr
   {infix_pp $1 PPimplies $3 }
| lexpr relation lexpr %prec prec_relation
   {infix_pp $1 $2 $3 }

/* unary operators */

| NOT lexpr
   {prefix_pp PPnot $2 }
| MINUS lexpr %prec uminus
   {prefix_pp PPneg $2 }

/* bit vectors */

| LEFTSQ BAR INTEGER BAR RIGHTSQ
    { mk_pp (PPconst (ConstBitv (check_binary_mode $3))) }
| lexpr HAT LEFTBR INTEGER COMMA INTEGER RIGHTBR
	{let i =  mk_pp (PPconst (ConstInt $4)) in
	 let j =  mk_pp (PPconst (ConstInt $6)) in
	 mk_pp (PPextract ($1, i, j)) }
| lexpr AT lexpr
   { mk_pp (PPconcat($1, $3))}

/* predicate or function calls */

| DISTINCT LEFTPAR list2_lexpr_sep_comma RIGHTPAR
   { mk_pp (PPdistinct $3) }


| IF lexpr THEN lexpr ELSE lexpr %prec prec_ite
   { mk_pp (PPif ($2, $4, $6)) }

| FORALL list1_named_ident_sep_comma COLON primitive_type triggers
  DOT lexpr %prec prec_forall
   {mk_pp (PPforall_named ($2, $4, $5, $7)) }

| EXISTS list1_named_ident_sep_comma COLON primitive_type triggers
  DOT lexpr %prec prec_exists
   {mk_pp (PPexists_named ($2, $4, $5, $7)) }

| STRING COLON lexpr %prec prec_named
   {mk_pp (PPnamed ($1, $3))}

| LET ident EQUAL lexpr IN lexpr
   {mk_pp (PPlet ($2, $4, $6))}

| CHECK lexpr
    {mk_pp (PPcheck $2)}

| CUT lexpr
    {mk_pp (PPcut $2)}
;

simple_expr :

/* constants */
| INTEGER
   {mk_pp (PPconst (ConstInt $1))}
| NUM
   {mk_pp (PPconst (ConstReal $1))}
| TRUE
   {mk_pp (PPconst ConstTrue)}
| FALSE
   {mk_pp (PPconst ConstFalse)}
| VOID
   {mk_pp (PPconst ConstVoid)}
| ident
   {mk_pp (PPvar $1)}

/* records */

| LEFTBR list1_label_expr_sep_PV RIGHTBR
   {mk_pp (PPrecord $2)}

| LEFTBR simple_expr WITH list1_label_expr_sep_PV RIGHTBR
    {mk_pp (PPwith($2, $4))}

| simple_expr DOT ident
   {mk_pp (PPdot($1, $3))}

/* function or predicat calls */

| ident LEFTPAR list0_lexpr_sep_comma RIGHTPAR
   {mk_pp (PPapp ($1, $3))}


/* arrays */

| simple_expr LEFTSQ lexpr RIGHTSQ
    {mk_pp(PPget($1, $3))}
| simple_expr LEFTSQ array_assignements RIGHTSQ
    { let acc, l = match $3 with
	| [] -> assert false
	| (i, v)::l -> mk_pp (PPset($1, i, v)), l
      in
      List.fold_left 
	(fun acc (i,v) -> mk_pp (PPset(acc, i, v))) acc l
    }

| LEFTPAR lexpr RIGHTPAR
   { $2 }

| simple_expr COLON primitive_type
    {mk_pp (PPcast($1,$3))
    }
;

array_assignements:
| array_assignement { [$1] }
| array_assignement COMMA array_assignements { $1 :: $3 }
;

array_assignement:
|  lexpr LEFTARROW lexpr { $1, $3 }
;

triggers:
| /* epsilon */
    { [] }
| LEFTSQ list1_trigger_sep_bar RIGHTSQ
    { $2 }
;

list1_trigger_sep_bar:
| trigger { [$1] }
| trigger BAR list1_trigger_sep_bar { $1 :: $3 }
;

trigger:
  list1_lexpr_sep_comma
     { $1 }
;


list1_lexpr_sep_pv:
| lexpr                       { [$1] }
| lexpr PV                    { [$1] }
| lexpr PV list1_lexpr_sep_pv { $1 :: $3 }
;

list0_lexpr_sep_comma:
| /*empty */                        { [] }
| lexpr { [$1] }
| lexpr COMMA list0_lexpr_sep_comma { $1 :: $3 }
;

list1_lexpr_sep_comma:
| lexpr                             { [$1] }
| lexpr COMMA list1_lexpr_sep_comma { $1 :: $3 }
;

list2_lexpr_sep_comma:
| lexpr COMMA lexpr                 { [$1; $3] }
| lexpr COMMA list2_lexpr_sep_comma { $1 :: $3 }
;

relation:
| LT { PPlt }
| LE { PPle }
| GT { PPgt }
| GE { PPge }
| EQUAL { PPeq }
| NOTEQ { PPneq }
;

record_type:
| LEFTBR list1_label_sep_PV RIGHTBR
   { $2 }
;

list1_label_sep_PV:
| label_with_type                         { [$1] }
| label_with_type PV list1_label_sep_PV   { $1::$3 }
;

label_with_type:
| ident COLON primitive_type
   { $1,$3 }
;


list1_label_expr_sep_PV:
| ident EQUAL lexpr
   { [$1, $3] }
| ident EQUAL lexpr PV list1_label_expr_sep_PV
   { ($1, $3) :: $5 }
;

type_var:
| QUOTE ident
    { $2 }
;

type_vars:
| /* empty */
  { [] }
| type_var
   { [$1] }
| LEFTPAR list1_type_var_sep_comma RIGHTPAR
   { $2 }

list1_type_var_sep_comma:
| type_var                                { [$1] }
| type_var COMMA list1_type_var_sep_comma { $1 :: $3 }
;

ident:
| IDENT { replace_qmark $1 }
;

list1_named_ident_sep_comma:
| named_ident                                   { [$1] }
| named_ident COMMA list1_named_ident_sep_comma { $1 :: $3 }
;

named_ident:
| IDENT { $1, "" }
| IDENT STRING { $1, $2 }
;


