open Format
open Parsed

exception Not_found
exception Not_Math_Expr
exception Not_Math_Expr1
exception Not_Int_Real_Bool

type int_or_real_or_bool = Is_Int | Is_Real | Is_Bool

let rec find_in_local_vars id l =
  if List.mem id l.int_vars then Is_Int
  else if List.mem id l.real_vars then Is_Real
  else if List.mem id l.bool_vars then Is_Bool
  else raise Not_found

let rec find_in_global_vars id g =
  if List.mem id g.i_vars then Is_Int
  else if List.mem id g.r_vars then Is_Real
  else if List.mem id g.b_vars then Is_Bool
  else raise Not_found

let rec find_in_global_funs id g =
  if List.mem id g.i_funs then Is_Int
  else if List.mem id g.r_funs then Is_Real
  else if List.mem id g.b_funs then Is_Bool
  else raise Not_found
    
let rec type_lexpr exp g l=
  let {pp_desc} = exp in
  match pp_desc with
  | PPvar id ->
     begin
       try find_in_local_vars id l
       with Not_found ->
	 begin
	   try find_in_global_vars id g
	   with Not_found ->
	     begin
	       print_string id;
	       raise Not_Int_Real_Bool
	     end
	 end
     end
  | PPapp (id, exp_lst) ->
     begin
       try find_in_global_funs id g
       with Not_found -> raise Not_Int_Real_Bool
     end
  | PPconst const ->
     begin
       match const with
       | ConstInt _ -> Is_Int
       | ConstReal _ -> Is_Real
       | ConstTrue | ConstFalse -> Is_Bool
       | _ -> raise Not_Int_Real_Bool
     end
  | PPinfix (lexp, op, rexp) ->
     begin
       match op with
       | PPand | PPor | PPimplies | PPiff
       | PPlt | PPle | PPgt | PPge | PPeq
       | PPneq -> Is_Bool 
       | PPadd | PPsub
       | PPmul | PPdiv -> type_lexpr lexp g l
       | PPmod -> Is_Int
     end
  | PPprefix (op, exp) ->
     begin
       match op with
       | PPneg -> type_lexpr exp g l
       | PPnot -> Is_Bool
     end
  | PPget (lexp, rexp) ->
     begin
       match lexp.pp_desc with
       | PPvar id ->
	  begin
	    try find_in_local_vars id l
	    with Not_found ->
	      begin
		try find_in_global_vars id g
		with Not_found -> raise Not_Int_Real_Bool
	      end
	  end
       | PPset (exp1, exp2, exp3) ->
	  begin
	    match exp1.pp_desc with
	    | PPvar id1 ->
	       begin
		 try find_in_local_vars id1 l
	    with Not_found ->
	      begin
		try find_in_global_vars id1 g
		with Not_found -> raise Not_Int_Real_Bool
	      end
	       end
	    | _ -> assert false
	  end
       | _ -> assert false
     end
  | PPset (lexp,mexp,rexp) -> assert false
  | PPdot (exp, id) -> assert false
    (* begin
       try find_in_local_vars id l
       with Not_found ->
	 begin
	   try find_in_global_vars id g
	   with Not_found -> raise Not_Int_Real_Bool
	 end
       end*)
  | PPrecord lbl_lst -> assert false
  | PPwith (exp, lbl_lst) -> assert false
  | PPextract (lexp, mexp, rexp) -> assert false
  | PPconcat (lexp, rexp) -> assert false
  | PPif (lexp, mexp, rexp) -> assert false
  | PPforall (vars, pp_ty, exp_lst_lst, exp_lst, exp) -> 
     assert false
  | PPexists (vars, pp_ty, exp_lst_lst, exp_lst, exp) -> 
     assert false
  | PPforall_named (id_lst, pp_ty, exp_lst_lst, exp_lst, exp) -> 
    assert false
  | PPexists_named (id_lst, pp_ty, exp_lst_lst, exp_lst, exp) -> 
     assert false
  | PPnamed (id, exp) -> assert false
  | PPlet (id, lexp, rexp) -> assert false
  | PPcheck exp -> assert false
  | PPcut exp -> assert false
  | PPcast (exp, pp_ty) ->
     begin
       match pp_ty with
       | PPTint -> Is_Int
       | PPTreal -> Is_Real
       | PPTbool -> Is_Bool
       | _ -> raise Not_Math_Expr
     end
  | PPinInterval _ -> assert false
  | PPdistinct exp_lst -> assert false

