%{

  open Parsed
  open Parsing

  let check_binary_mode s =
    String.iter (fun x ->
                 match x with
                 | '0' | '1' -> ()
                 | _ -> raise Parsing.Parse_error) s;
    s

%}

%token <string> IDENT
%token <string> QM_IDENT
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
   { TypeDecl ($2, $3, Abstract) }
| TYPE type_vars ident EQUAL list1_constructors_sep_bar
   { TypeDecl ($2, $3, Enum $5 ) }
| TYPE type_vars ident EQUAL record_type
   { TypeDecl ($2, $3, Record $5 ) }
| LOGIC ac_modifier list1_named_ident_sep_comma COLON logic_type
   { Logic ( $2, $3, $5) }
| FUNCTION named_ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR COLON
  primitive_type EQUAL lexpr
   { Function_def ($2, $4, $7, $9) }
| PREDICATE named_ident EQUAL lexpr
   { Predicate_def ( $2, [], $4) }
| PREDICATE named_ident LEFTPAR list0_logic_binder_sep_comma RIGHTPAR EQUAL lexpr
   { Predicate_def ( $2, $4, $7) }
| AXIOM ident COLON lexpr
   { Axiom ( $2, $4) }
| REWRITING ident COLON list1_lexpr_sep_pv
   { Rewriting( $2, $4) }
| GOAL ident COLON lexpr
   { Goal ( $2, $4) }
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
   { PPTexternal ([], $1) }
| type_var
   { PPTvarid ($1) }
| primitive_type ident
   { PPTexternal ([$1], $2) }
| LEFTPAR list1_primitive_type_sep_comma RIGHTPAR ident
   { PPTexternal ($2, $4) }
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
    { ($1, $3) }
;

list1_constructors_sep_bar:
| ident { [$1] }
| ident BAR list1_constructors_sep_bar { $1 :: $3}
;


lexpr:

| simple_expr { $1 }

/* binary operators */

| lexpr PLUS lexpr
   {{pp_desc = PPinfix ($1, PPadd, $3)} }
| lexpr MINUS lexpr
   {{pp_desc = PPinfix ($1, PPsub, $3)} }
| lexpr TIMES lexpr
   {{pp_desc = PPinfix ($1, PPmul, $3)} }
| lexpr SLASH lexpr
   {{pp_desc = PPinfix ($1, PPdiv, $3) }}
| lexpr PERCENT lexpr
   {{pp_desc = PPinfix ($1, PPmod, $3)} }
| lexpr AND lexpr
   {{pp_desc = PPinfix ($1, PPand, $3)} }
| lexpr OR lexpr
   {{pp_desc = PPinfix ($1, PPor, $3)} }
| lexpr LRARROW lexpr
   {{pp_desc = PPinfix ($1, PPiff, $3)} }
| lexpr ARROW lexpr
   {{pp_desc = PPinfix ($1, PPimplies, $3)} }
| lexpr relation lexpr %prec prec_relation
   {{pp_desc = PPinfix ($1, $2, $3)} }

/* unary operators */

| NOT lexpr
   {{pp_desc = PPprefix (PPnot, $2)} }
| MINUS lexpr %prec uminus
   {{pp_desc = PPprefix (PPneg, $2)} }

/* bit vectors */

| LEFTSQ BAR INTEGER BAR RIGHTSQ
    {{pp_desc = PPconst (ConstBitv (check_binary_mode $3))} }
| lexpr HAT LEFTBR INTEGER COMMA INTEGER RIGHTBR
   { let i =  {pp_desc = PPconst (ConstInt $4)} in
     let j =  {pp_desc = PPconst (ConstInt $6)} in
    {pp_desc = PPextract ($1, i, j)} }
| lexpr AT lexpr
   { {pp_desc = PPconcat($1, $3)} }

/* predicate or function calls */

| DISTINCT LEFTPAR list2_lexpr_sep_comma RIGHTPAR
   { {pp_desc = PPdistinct $3} }


| IF lexpr THEN lexpr ELSE lexpr %prec prec_ite
   { {pp_desc = PPif ($2, $4, $6)} }

| FORALL list1_named_ident_sep_comma COLON primitive_type triggers filters
  DOT lexpr %prec prec_forall
   {{pp_desc = PPforall_named ($2, $4, $5, $6, $8)} }

| EXISTS list1_named_ident_sep_comma COLON primitive_type triggers filters
  DOT lexpr %prec prec_exists
   {{pp_desc = PPexists_named ($2, $4, $5, $6, $8)} }

| STRING COLON lexpr %prec prec_named
   {{pp_desc = PPnamed ($1, $3) }}

| LET ident EQUAL lexpr IN lexpr
   {{pp_desc = PPlet ($2, $4, $6) }}

| CHECK lexpr
    {{pp_desc = PPcheck $2 }}

| CUT lexpr
    {{pp_desc = PPcut $2 }}
;

simple_expr :

/* constants */
| INTEGER
   {{pp_desc = PPconst (ConstInt $1) }}
| NUM
   {{pp_desc = PPconst (ConstReal $1) }}
| TRUE
   {{pp_desc = PPconst ConstTrue }}
| FALSE
   {{pp_desc = PPconst ConstFalse }}
| VOID
   {{pp_desc = PPconst ConstVoid }}
| ident
   {{pp_desc = PPvar $1 }}

/* records */

| LEFTBR list1_label_expr_sep_PV RIGHTBR
   {{pp_desc = PPrecord $2 }}

| LEFTBR simple_expr WITH list1_label_expr_sep_PV RIGHTBR
    {{pp_desc = PPwith($2, $4) }}

| simple_expr DOT ident
   {{pp_desc = PPdot($1, $3) }}

/* function or predicat calls */

| ident LEFTPAR list0_lexpr_sep_comma RIGHTPAR
   {{pp_desc = PPapp ($1, $3) }}


/* arrays */

| simple_expr LEFTSQ lexpr RIGHTSQ
    {{pp_desc = PPget($1, $3) }}
| simple_expr LEFTSQ array_assignements RIGHTSQ
    { let acc, l = match $3 with
	| [] -> assert false
	| (i, v)::l -> {pp_desc = PPset($1, i, v)}, l
      in
      List.fold_left 
	(fun acc (i,v) -> {pp_desc = PPset(acc, i, v)}) acc l
    }

| LEFTPAR lexpr RIGHTPAR
   { $2 }

| simple_expr COLON primitive_type
    {{pp_desc = PPcast($1,$3)}
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

filters:
| /* epsilon */
    { [] }
| LEFTBR lexpr RIGHTBR
    { [$2] }

| LEFTBR lexpr COMMA list0_lexpr_sep_comma RIGHTBR
    { $2 :: $4 }
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
| lexpr_or_dom                             { [$1] }
| lexpr_or_dom COMMA list1_lexpr_sep_comma { $1 :: $3 }
;

lexpr_or_dom:
| lexpr {$1}
| lexpr IN sq bound COMMA bound sq
    {{pp_desc = PPinInterval ($1, $3, $4, $6, $7)}}

sq:
| LEFTSQ {true}
| RIGHTSQ {false}

bound:
| QM_IDENT {{pp_desc = PPvar $1}}
| IDENT {{pp_desc = PPvar $1}}
| INTEGER {{pp_desc = PPconst (ConstInt $1)}}
| NUM {{pp_desc = PPconst (ConstReal $1)}}


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
| IDENT { $1 }
;

list1_named_ident_sep_comma:
| named_ident                                   { [$1] }
| named_ident COMMA list1_named_ident_sep_comma { $1 :: $3 }
;

named_ident:
| IDENT { $1, "" }
| IDENT STRING { $1, $2 }
;

