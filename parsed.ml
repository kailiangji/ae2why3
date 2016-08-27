
type constant =
  | ConstBitv of string
  | ConstInt of string
  | ConstReal of Num.num
  | ConstTrue
  | ConstFalse
  | ConstVoid

type pp_infix =
  | PPand | PPor | PPimplies | PPiff
  | PPlt | PPle | PPgt | PPge | PPeq | PPneq
  | PPadd | PPsub | PPmul | PPdiv | PPmod

type pp_prefix =
  | PPneg | PPnot

type ppure_type =
  | PPTint
  | PPTbool
  | PPTreal
  | PPTunit
  | PPTbitv of int
  | PPTvarid of string * Loc.t
  | PPTexternal of ppure_type list * string * Loc.t

type lexpr =
    {pp_loc : Loc.t; pp_desc : pp_desc }

(*
type lexpr = {pp_desc : pp_desc }
*)
and pp_desc =
  | PPvar of string
  | PPapp of string * lexpr list
  | PPinInterval of lexpr * bool * lexpr * lexpr * bool
  (* bool = true <-> interval is_open *)

  | PPdistinct of lexpr list
  | PPconst of constant
  | PPinfix of lexpr * pp_infix * lexpr
  | PPprefix of pp_prefix * lexpr
  | PPget of lexpr * lexpr
  | PPset of lexpr * lexpr * lexpr
  | PPdot of lexpr * string
  | PPrecord of (string * lexpr) list
  | PPwith of lexpr * (string * lexpr) list
  | PPextract of lexpr * lexpr * lexpr
  | PPconcat of lexpr * lexpr
  | PPif of lexpr * lexpr * lexpr
  | PPforall of string list * ppure_type * lexpr list list  * lexpr
  | PPexists of string list * ppure_type * lexpr list list  * lexpr
  | PPforall_named of
      (string * string) list * ppure_type * lexpr list list * lexpr
  | PPexists_named of
      (string * string) list * ppure_type * lexpr list list * lexpr
  | PPnamed of string * lexpr
  | PPlet of string * lexpr * lexpr
  | PPcheck of lexpr
  | PPcut of lexpr
  | PPcast of lexpr * ppure_type

(* Declarations. *)

type plogic_type =
  | PPredicate of ppure_type list
  | PFunction of ppure_type list * ppure_type

type name_kind = Ac | Constructor | Other

type body_type_decl =
  | Record of (string * ppure_type) list  (* lbl : t *)
  | Enum of string list
  | Abstract

      (*
type theory_decl =
| ThAxiom of Loc.t * string * lexpr
| ThCs of Loc.t * string * lexpr
      *)
type decl =
  | Axiom of Loc.t * string * lexpr
  | Rewriting of Loc.t * string * lexpr list
  | Goal of Loc.t * string * lexpr
  | Logic of Loc.t * name_kind * (string * string) list * plogic_type
  | Predicate_def of
      Loc.t * (string * string) *
	(Loc.t * string * ppure_type) list * lexpr
  | Function_def of
      Loc.t * (string * string) *
	(Loc.t * string * ppure_type) list * ppure_type * lexpr
  | TypeDecl of Loc.t * string list * string * body_type_decl

type file = decl list

type g_decs =
  {mutable i_vars : string list; mutable r_vars : string list;
   mutable i_funs : string list; mutable r_funs : string list;
   mutable b_vars : string list; mutable b_funs : string list}

type loc_decs=
  {mutable int_vars : string list; mutable real_vars : string list;
   mutable bool_vars: string list}

type lib_include =
  {mutable int_lib   : bool; mutable real_lib    : bool;
   mutable bool_lib  : bool; mutable float_rnd   : bool;
   mutable float_sgl : bool; mutable float_dbl   : bool;
   mutable map_lib   : bool; mutable abs_int     : bool;
   mutable abs_real  : bool; mutable real_of_int : bool;
   mutable sqrt_real : bool; mutable mode        : bool;
   mutable unit      : bool}

type filters =
  {mutable axioms : string list; mutable funs  : string list;
   mutable preds  : string list; mutable types : string list}
