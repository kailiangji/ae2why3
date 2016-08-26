open Parsed
open Format
open Type_check

let rec print_ppure_type fmt ty =
  match ty with
  | PPTint -> fprintf fmt "int"
  | PPTbool -> fprintf fmt "bool"
  | PPTreal -> fprintf fmt "real"
  | PPTunit -> fprintf fmt "tuple0"
  | PPTbitv _ -> assert false
  | PPTvarid id -> fprintf fmt "'%s" (String.uncapitalize id)
  | PPTexternal (pt_lst, id) ->
     if List.length pt_lst = 0 then
       fprintf fmt "%s"
	 (if id = "fpa_rounding_mode" then "mode"
	  else (String.uncapitalize id))
     else
       begin
	 fprintf fmt "(%s" 
	   ( if id ="farray" then "map"
	     else (String.uncapitalize id));
	 List.iter (fun pt ->
	   fprintf fmt " %a" print_ppure_type pt) pt_lst;
	 fprintf fmt ")"
       end
	 
let rec print_ppure_type1 fmt ty =
  match ty with
  | PPTint -> fprintf fmt "int"
  | PPTbool -> fprintf fmt "bool"
  | PPTreal -> fprintf fmt "real"
  | PPTunit -> fprintf fmt "tuple0"
  | PPTbitv _ -> assert false
  | PPTvarid id -> fprintf fmt "'%s" (String.uncapitalize id)
  | PPTexternal (pt_lst, id) ->
     if List.length pt_lst = 0 then
       fprintf fmt "%s"
	 (if id = "fpa_rounding_mode" then
	     "mode"
	  else (String.uncapitalize id))
     else
       begin
	 fprintf fmt "%s" 
	   ( if id = "farray" then "map"
	     else (String.uncapitalize id));
	 List.iter (fun pt ->
	   fprintf fmt " %a" print_ppure_type pt) pt_lst;
       end

let is_single exprs =
  match exprs with
  | [m;e;mode;exp] ->
     begin
       match m.pp_desc,e.pp_desc with
       | PPconst (ConstInt "24"),PPconst(ConstInt "149") ->
	  true
       | PPconst(ConstInt "53"), PPconst(ConstInt "1074") ->
	  false
       | PPconst(ConstInt m1), PPconst(ConstInt e1) ->
	  if int_of_string m1 <= 24 && int_of_string e1 <= 149 then
	    true
	  else
	    false
       | _,_ -> assert false
     end
  | _ -> assert false 
  
       
let rec test_fun_names g lib expr fun_lst =
  let {pp_desc} = expr in
  match pp_desc with
  | PPvar id -> ()
  | PPapp (id, exprs) ->
     begin
       match id with
       | "abs_int" ->
	  begin
	    if lib.abs_int = false then
	      begin
		lib.abs_int <- true;
		fun_lst := "abs_int"::!fun_lst;
	      end;
	    List.iter
	      (fun e1 -> test_fun_names g lib e1 fun_lst)
	      exprs
	  end
       | "abs_real" ->
	  begin
	    if lib.abs_real = false then
	      begin
		lib.abs_real <- true;
		fun_lst := "abs_real"::!fun_lst;
	      end;
	    List.iter
	      (fun e1 -> test_fun_names g lib e1 fun_lst)
	      exprs
	  end
       | "real_of_int" ->
	  begin
	    if lib.real_of_int = false then
	      begin
		lib.real_of_int <- true;
		fun_lst := "real_of_int"::!fun_lst;
	      end;
	    List.iter
	      (fun e1 -> test_fun_names g lib e1 fun_lst)
	      exprs
	  end
       | "sqrt_real" -> assert false
       | "float" ->
	  begin
	    if is_single exprs && lib.float_sgl = false then
	      begin
		if lib.mode = false then
		  begin
		    lib.mode <- true;
		    fun_lst := "mode" :: !fun_lst
		  end;
		lib.float_sgl <- true;
		fun_lst := "single" :: !fun_lst;
	      end
	    else if lib.float_dbl = false then
	      begin
		if lib.mode = false then
		  begin
		    lib.mode <- true;
		    fun_lst := "mode" :: !fun_lst
		  end;
		lib.float_dbl <- true;
		fun_lst := "double" :: !fun_lst
	      end;
	    List.iter
	      (fun e1 -> test_fun_names g lib e1 fun_lst)
	      exprs
	  end
	   
       | _ ->
	  List.iter (fun e1 -> test_fun_names g lib e1 fun_lst)
	    exprs
     end
  | PPconst const -> ()
  | PPinfix (e1, op, e2)->
     begin
       test_fun_names g lib e1 fun_lst;
       test_fun_names g lib e2 fun_lst
     end
  | PPprefix (op, e1) ->
     test_fun_names g lib e1 fun_lst
  | PPget (e1, e2) ->
     begin
       test_fun_names g lib e1 fun_lst;
       test_fun_names g lib e2 fun_lst
     end
  | PPset (e1, e2, e3) ->
     begin
       test_fun_names g lib e1 fun_lst;
       test_fun_names g lib e2 fun_lst;
       test_fun_names g lib e3 fun_lst
     end
  | PPdot (e1, id) ->
     test_fun_names g lib e1 fun_lst
  | PPrecord lbls -> ()
  | PPwith (e1, lbls) ->
     test_fun_names g lib e1 fun_lst
  | PPextract (e1,e2,e3) ->
     begin
       test_fun_names g lib e1 fun_lst;
       test_fun_names g lib e2 fun_lst;
       test_fun_names g lib e3 fun_lst
     end
  | PPconcat (e1,e2) ->
     begin
       test_fun_names g lib e1 fun_lst;
       test_fun_names g lib e2 fun_lst
     end
  | PPif (e1,e2,e3) ->
     begin
       test_fun_names g lib e1 fun_lst;
       test_fun_names g lib e2 fun_lst;
       test_fun_names g lib e3 fun_lst
     end
  | PPforall (vars, pp_ty, exp_lst_lst, exp_lst, e1) ->
     test_fun_names g lib e1 fun_lst
  | PPexists (vars, pp_ty, exp_lst_lst, exp_lst, e1) ->
     test_fun_names g lib e1 fun_lst
  | PPforall_named (id_lst, pp_ty, exp_lst_lst, exp_lst, e1) -> 
     test_fun_names g lib e1 fun_lst
  | PPexists_named (id_lst, pp_ty, exp_lst_lst, exp_lst, e1) -> 
     test_fun_names g lib e1 fun_lst
  | PPnamed (id, e1) -> test_fun_names g lib e1 fun_lst
  | PPlet (id, e1, e2) ->
     begin
       test_fun_names g lib e1 fun_lst;
       test_fun_names g lib e2 fun_lst
     end
  | PPcheck e1 -> test_fun_names g lib e1 fun_lst
  | PPcut e1 -> test_fun_names g lib e1 fun_lst
  | PPcast (e1, pp_ty) ->
     test_fun_names g lib e1 fun_lst 
  | PPinInterval _ -> ()
  | PPdistinct exp_lst ->
     List.iter (fun e1 -> test_fun_names g lib e1 fun_lst) exp_lst

let print_modules fmt fname =
  match fname with
  | "int_lib" -> fprintf fmt "\n\nuse import int.Int"
  | "real_lib" -> fprintf fmt "\n\nuse import real.RealInfix"
  | "bool_lib" -> fprintf fmt "\n\nuse import bool.Bool"
  | "map_lib" -> fprintf fmt "\n\nuse import map.Map"
  | "abs_int" -> fprintf fmt "\n\nuse import int.Abs as IA"
  | "abs_real" -> fprintf fmt "\n\nuse import real.Abs as RA"
  | "real_of_int" -> fprintf fmt "\n\nuse import real.FromInt"
  | "sqrt_real" -> assert false
  | "single" -> fprintf fmt "\n\nuse import floating_point.Single as S"
  | "double" -> fprintf fmt "\n\nuse import floating_point.Double as D"
  | "mode" -> fprintf fmt "\n\nuse import floating_point.Rounding"
  | "unit" -> fprintf fmt "\n\nuse import Tuple0"
  | _ -> assert false
       
let rec test_types1 lib pt_lst lib_lst =
  List.iter
    (
      fun pt ->
      begin
	match pt with
	| PPTint ->
	   if lib.int_lib = false then
	     begin
	       lib.int_lib <- true;
	       lib_lst := "int_lib" :: !lib_lst;
	     end
	| PPTbool ->
	   if lib.bool_lib = false then
	     begin
	       lib.bool_lib <- true;
	       lib_lst := "bool_lib" :: !lib_lst;
	     end
	| PPTreal ->
	   if lib.real_lib = false then
	     begin
	       lib.real_lib <- true;
	       lib_lst := "real_lib" :: !lib_lst;
	     end
	| PPTunit ->
	   if lib.unit = false then
	     begin
	       lib.unit <- true;
	       lib_lst := "unit" :: !lib_lst
	     end
	| PPTexternal (pt_lst, id) ->
	   begin
	     if lib.map_lib = false && id = "farray" then
	       begin
		 lib.map_lib <- true;
		 lib_lst := "map_lib" :: !lib_lst;
	       end
	     else
	       if lib.mode = false &&
		 id = "fpa_rounding_mode" then
		 begin
		   lib.mode <- true;
		   lib_lst := "mode" :: !lib_lst;
		   assert (pt_lst = [])
		 end;
	     test_types1 lib pt_lst lib_lst
	   end
	| _ -> ()
      end
    ) pt_lst
       
let rec test_types lib lb_tys lib_lst =
  List.iter
    (fun lb_ty ->
      let (var, ty) = lb_ty in
      begin
	match ty with
	| PPTint ->
	   if lib.int_lib = false then
	     begin
	       lib.int_lib <- true;
	       lib_lst := "int_lib" :: !lib_lst
	     end
	| PPTbool ->
	   if lib.bool_lib = false then
	     begin
	       lib.bool_lib <- true;
	       lib_lst := "bool_lib" :: !lib_lst
	     end
	| PPTreal ->
	   if lib.real_lib = false then
	     begin
	       lib.real_lib <- true;
	       lib_lst := "real_lib" :: !lib_lst
	     end
	| PPTunit ->
	   if lib.unit = false then
	     begin
	       lib.unit <- true;
	       lib_lst := "unit" :: !lib_lst
	     end
	| PPTexternal (pt_lst, id) ->
	   begin
	     if lib.map_lib = false && id = "farray" then
	       begin
		 lib.map_lib <- true;
		 lib_lst := "map_lib" :: !lib_lst;
	       end
	     else
	       if lib.mode = false &&
		 id = "fpa_rounding_mode" then
		 begin
		   lib.mode <- true;
		   lib_lst := "mode" :: !lib_lst;
		   assert (pt_lst = [])
		 end;
	     test_types1 lib pt_lst lib_lst
	   end
	| _ -> ()
      end
    )lb_tys
       
let rec print_record fmt lb_types =
  match lb_types with
  | [] -> ()
  | [lb] ->
     let (var,ty) = lb in
     fprintf fmt "%s : %a" var print_ppure_type ty
  | h :: tl ->
     let (var,ty) = h in
     fprintf fmt "%s : %a; %a" var print_ppure_type ty print_record tl
       
let print_type fmt (g, lib, ty) =
  match ty with
  | TypeDecl (vars, id, Abstract) ->
     begin
       match id with
       | "single" ->
	  if lib.float_sgl = false then
	    begin
	      lib.float_sgl <- true;
	      fprintf fmt "\n\nuse import floating_point.Single as S";
		assert (vars = [])
	    end
       | "double" ->
	  if lib.float_dbl = false then
	    begin
	      lib.float_dbl <- true;
	      fprintf fmt "\n\nuse import floating_point.Double as D";
		assert (vars = [])
	    end
       | _ ->
	  begin
	    fprintf fmt "\n\ntype %s " (String.uncapitalize id);
	    List.iter (fun var -> fprintf fmt "'%s " var) vars
	  end
     end
  | TypeDecl (vars, id, Enum id_lst) ->
     begin
       fprintf fmt "\n\ntype %s " id;
       List.iter (fun var -> fprintf fmt "'%s " var) vars;
       fprintf fmt "= %s" (List.hd id_lst);
       List.iter (fun id -> fprintf fmt " | %s" id) (List.tl id_lst);
     end
  | TypeDecl (vars, id, Record lbl_lst) ->
     begin
       let lib_lst = ref [] in
       test_types lib lbl_lst lib_lst;
       List.iter (fun lib -> print_modules fmt lib) (List.rev !lib_lst);
       fprintf fmt "\n\ntype %s " id;
       List.iter (fun var -> fprintf fmt "'%s " var) vars;
       fprintf fmt "= {%a}" print_record lbl_lst;
     end
  | _ -> assert false


let rec print_named_ids fmt id_lst =
  match id_lst with
  | [] -> fprintf fmt " : "
  | h :: tl ->
    let (n1, n2) = h in
    if String.length n2 = 0 then
      fprintf fmt " %s%a" n1 print_named_ids tl
    else
      fprintf fmt " (%s %s)%a" n1 n2 print_named_ids tl

let rec print_ppred fmt pp_tys =
  match pp_tys with
  | [] -> ()
  | [h] -> fprintf fmt "%a " print_ppure_type h
  | h :: tl ->
     fprintf fmt "%a %a" print_ppure_type h print_ppred tl

let print_pfun fmt pp_tys pp_ty =
  List.iter (fun t -> fprintf fmt "%a " print_ppure_type t)
    pp_tys;
  fprintf fmt ": %a" print_ppure_type1 pp_ty

    
let print_fun_type fmt ty =
  match ty with
  | PPredicate pp_tys -> print_ppred fmt pp_tys
  | PFunction (pp_tys, pp_ty) -> print_pfun fmt pp_tys pp_ty

let print_fun_name fmt id =
  let (h,t)= id in
  if String.length t = 0 then fprintf fmt "%s " (String.uncapitalize h)
  else fprintf fmt "%s %s " (String.uncapitalize h) t

let print_fun_args fmt args =
  List.iter (fun arg ->
    let (var, ty) = arg in
    fprintf fmt "(%s : %a) " var print_ppure_type1 ty
  ) args

    
let print_logic fmt (g, lib, lg, f_rm) =
  match lg with
  | Logic (nam_kd,id_lst, ty) ->
     begin       
       match nam_kd with
       | Other ->
	  begin
	    match ty with
	    |PPredicate pp_tys ->
	       begin
		 if List.length pp_tys = 0 then
		   List.iter (fun id ->
		     if lib.bool_lib = false then
		       begin
			 lib.bool_lib <- true;
			 fprintf fmt "\n\nuse import bool.Bool"
		       end;
		     g.b_vars <- (fst id) :: g.b_vars;
		     if List.mem (fst id) f_rm then ()
		     else
		       fprintf fmt "\n\nconstant %a%a: bool"
			 print_fun_name id  print_fun_type ty
		   )id_lst
		 else
		   begin
		     let lib_lst = ref [] in
		     test_types1 lib pp_tys lib_lst;
		     List.iter (fun lib -> print_modules fmt lib)
		       (List.rev !lib_lst);
		     List.iter (fun id ->
		       if lib.bool_lib = false then
			 begin
			   lib.bool_lib <- true;
			   fprintf fmt "\n\nuse import bool.Bool"
			 end;
		       g.b_funs <- (fst id) :: g.b_funs;
		       if List.mem (fst id) f_rm then ()
		       else
			 fprintf fmt "\n\nfunction %a%a: bool"
			   print_fun_name id  print_fun_type ty
		     )id_lst
		   end
	       end
	    | PFunction (pp_tys, pp_ty) ->
	       begin
		 if List.length pp_tys = 0 then
		   begin
		     let lib_lst = ref [] in
		     test_types1 lib [pp_ty] lib_lst;
		     List.iter
		       (fun lib -> print_modules fmt lib)
		       (List.rev !lib_lst);
		     List.iter (fun id ->
		       begin
			 match pp_ty with
			 | PPTint -> g.i_vars <- (fst id) :: g.i_vars
			 | PPTreal -> g.r_vars <- (fst id) :: g.r_vars
			 | PPTbool -> g.b_vars <- (fst id) :: g.b_vars
			 | _ -> ()
		       end;
		       if List.mem (fst id) f_rm then ()
		       else
			 fprintf fmt "\n\nconstant %a%a"
			   print_fun_name id print_fun_type ty
		     )id_lst
		   end
		 else
		     begin
		       let lib_lst = ref [] in
		       test_types1 lib pp_tys lib_lst;
		       test_types1 lib [pp_ty] lib_lst;
		       List.iter
			 (fun lib -> print_modules fmt lib)
			 (List.rev !lib_lst);
		       List.iter (fun id ->
			 begin
			   match pp_ty with
			   | PPTint -> g.i_funs <- (fst id) :: g.i_funs
			   | PPTreal -> g.r_funs <- (fst id) :: g.r_funs
			   | PPTbool -> g.b_funs <- (fst id) :: g.b_funs
			   | _ -> ()
			 end;
			 if List.mem (fst id) f_rm then ()
			 else
			   fprintf fmt "\n\nfunction %a%a"
			     print_fun_name id print_fun_type ty
		       )id_lst
		     end
	       end
	  end
       | Ac -> assert false
       | _ -> assert false
     end
  | _ -> assert false
     
let print_pp_infix fmt (g, l, rexp, op) =
  match op with
  | PPand -> fprintf fmt "/\\"
  | PPor -> fprintf fmt "\\/"
  | PPimplies -> fprintf fmt "->\n   "
  | PPiff -> fprintf fmt "<->"
  | PPlt ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf fmt "<"
       | Is_Real -> fprintf fmt "<."
       | _ -> assert false
     end
  | PPle ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf fmt "<="
       | Is_Real -> fprintf fmt "<=."
       | _ -> assert false
     end
  | PPgt ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf fmt ">"
       | Is_Real -> fprintf fmt ">."
       | _ -> assert false
     end
  | PPge ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf fmt ">="
       | Is_Real -> fprintf fmt ">=."
       | _ -> assert false
     end
  | PPeq -> fprintf fmt "="
  | PPneq -> fprintf fmt "<>"
  | PPadd ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf fmt "+"
       | Is_Real -> fprintf fmt "+."
       | _ -> assert false
     end
  | PPsub ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf fmt "-"
       | Is_Real -> fprintf fmt "-."
       | _ -> assert false
     end
  | PPmul ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf fmt "*"
       | Is_Real -> fprintf fmt "*."
       | _ -> assert false
     end
  | PPdiv ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf fmt "/"
       | Is_Real -> fprintf fmt "/."
       | _ -> assert false
     end
  | PPmod -> assert false

let rec print_lexpr fmt (g, l, expr) =
  let {pp_desc} = expr in
  match pp_desc with
  | PPvar id -> fprintf fmt "%s" id
  | PPapp (id, exprs) ->
     begin
       match id with
       | "float" ->
	  begin
	    match exprs with
	    | [m;e;mode;exp] ->
	       begin
		 match m.pp_desc,e.pp_desc with
		 | PPconst (ConstInt "24"),PPconst(ConstInt "149") ->
		    fprintf fmt "(S.round %a %a)"
		      print_lexpr (g, l, mode) print_lexpr (g, l, exp)
		 | PPconst(ConstInt "53"), PPconst(ConstInt "1074") ->
		    fprintf fmt "(D.round %a %a)"
		      print_lexpr (g, l, mode) print_lexpr (g, l, exp)
		 | PPconst(ConstInt m1), PPconst(ConstInt e1) ->
		    if int_of_string m1 <= 24 && int_of_string e1 <= 149 then
		      fprintf fmt "(S.round %a %a)"
			print_lexpr (g, l, mode) print_lexpr (g, l, exp)
		    else
		      fprintf fmt "(D.round %a %a)"
			print_lexpr (g, l, mode) print_lexpr (g, l, exp)
		 | _,_ -> assert false
	       end
	    | _ -> assert false
	  end
       | "abs_int" -> fprintf fmt "(IA.abs%a)" print_lexprs (g, l, exprs)
       | "abs_real" -> fprintf fmt "(RA.abs%a)" print_lexprs (g, l, exprs)
       | "real_of_int" -> fprintf fmt "(from_int%a)" print_lexprs (g, l, exprs)
       | "round" -> fprintf fmt "(S.round%a)" print_lexprs (g, l, exprs)
       | "value" -> fprintf fmt "(S.value%a)" print_lexprs (g, l, exprs)
       | "exact" -> fprintf fmt "(S.exact%a)" print_lexprs (g, l, exprs)
       | "fpa_rounding_model" -> fprintf fmt "(S.model%a)"
	  print_lexprs (g, l, exprs)
       | "round_error" -> fprintf fmt "(S.round_error%a)"
	  print_lexprs (g, l, exprs)
       | "total_error" -> fprintf fmt "(S.total_error%a)"
	  print_lexprs (g, l, exprs)
       | "round_logic" -> fprintf fmt "(S.round_logic%a)"
	  print_lexprs (g, l, exprs)
       | "round1" -> fprintf fmt "(D.round%a)" print_lexprs (g, l, exprs)
       | "value1" -> fprintf fmt "(D.value%a)" print_lexprs (g, l, exprs)
       | "exact1" -> fprintf fmt "(D.exact%a)" print_lexprs (g, l, exprs)
       | "fpa_rounding_model1" -> fprintf fmt "(D.model%a)"
	  print_lexprs (g, l, exprs)
       | "round_error1" -> fprintf fmt "(D.round_error%a)"
	  print_lexprs (g, l, exprs)
       | "total_error1" -> fprintf fmt "(D.total_error%a)"
	  print_lexprs (g, l, exprs)
       | "round_logic1" -> fprintf fmt "(D.round_logic%a)"
	  print_lexprs (g, l, exprs)
       |_ -> fprintf fmt "(%s%a)"
	  (String.uncapitalize id) print_lexprs (g, l, exprs)
     end
  | PPinInterval _ -> assert false
  | PPdistinct exprs ->
     fprintf fmt "(%a)" pairwise_distinct (g, l, exprs)
  | PPconst const -> 
    begin
      match const with
      | ConstBitv b -> fprintf fmt "%s" b
      | ConstInt i -> fprintf fmt "%s" i
      | ConstReal n -> fprintf fmt "%s" (string_of_float (Num.float_of_num n)) 
      | ConstTrue -> fprintf fmt "true"
      | ConstFalse -> fprintf fmt "false"
      | ConstVoid -> fprintf fmt "Tuple0"
    end
  | PPinfix (lexp, op, rexp) -> 
    begin
      match op with
      | PPmod -> fprintf fmt "(%a %a %a)"
	 print_pp_infix (g, l, lexp, op)
	 print_lexpr (g, l, lexp)
	 print_lexpr (g, l, rexp)
      | PPand | PPor | PPimplies | PPiff | PPneq ->
	 fprintf fmt "(%a %a %a)" 
	   print_lexpr (g, l, lexp)
	   print_pp_infix (g, l, rexp, op)
	   print_lexpr (g, l, rexp)
      | PPlt | PPle | PPgt | PPge | PPeq ->
	 fprintf fmt "%a %a %a" 
	   print_lexpr (g, l, lexp)
	   print_pp_infix (g, l, rexp, op)
	   print_lexpr (g, l, rexp)	  
      | _ ->
	 fprintf fmt "(%a %a %a)" 
	 print_lexpr (g, l, lexp)
	 print_pp_infix (g, l, lexp, op)
	 print_lexpr (g, l, rexp)
    end 
  | PPprefix (op, exp) ->
    begin
      match op with
      | PPneg ->
	 if type_lexpr exp g l = Is_Int then 
	   fprintf fmt "(-%a)" print_lexpr (g, l, exp)
	 else
	   fprintf fmt "(-.%a)" print_lexpr (g, l, exp)
      | PPnot -> fprintf fmt "(not %a)" print_lexpr (g, l, exp)
    end
  | PPget (lexp, rexp) ->
     fprintf fmt "%a[%a]"
       print_lexpr (g, l, lexp) print_lexpr (g, l, rexp)
  | PPset (lexp, mexp, rexp) ->
     fprintf fmt "%a%a"
       print_arr_set (g, l, expr) print_arr_assig (g, l, expr)
  | PPdot (exp, id) -> assert false
  | PPrecord lbl_lst -> assert false
  | PPwith (exp, lbl_lst) -> assert false
  | PPextract (lexp, mexp, rexp) -> assert false
  | PPconcat (lexp, rexp) -> assert false
  | PPif (e1, e2, e3) ->
     fprintf fmt "(if %a then %a else %a)"
       print_lexpr (g, l, e1) print_lexpr (g, l, e2) print_lexpr (g, l, e3)
  | PPforall (t_lst, pp_ty, exp_lst_lst, exp_lst, exp) -> 
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter (fun var -> l.int_vars <- var :: l.int_vars) t_lst
	 | PPTreal ->
	    List.iter (fun var -> l.real_vars <- var::l.real_vars) t_lst
	 | _ -> ()
       end;
       fprintf fmt "(forall";
       List.iter (fun var -> fprintf fmt " %s" var) t_lst;
       fprintf fmt "%a" print_ppure_type1 pp_ty;
       print_triggers fmt (g, l, exp_lst_lst);
       (*print_filters fmt exp_lst;*)
       fprintf fmt ".\n   %a)" print_lexpr (g, l, exp)      
    end
  | PPexists (t_lst, pp_ty, exp_lst_lst, exp_lst, exp) -> 
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter (fun var -> l.int_vars <- var::l.int_vars) t_lst
	 | PPTreal ->
	    List.iter (fun var -> l.real_vars <- var::l.real_vars) t_lst
	 | _ -> ()
       end;
       fprintf fmt "(exists";
       List.iter (fun var -> fprintf fmt " %s" var) t_lst;
       fprintf fmt "%a" print_ppure_type1 pp_ty;
       print_triggers fmt  (g, l, exp_lst_lst);
       (*print_filters fmt exp_lst;*)
       fprintf fmt ".\n   %a)" print_lexpr (g, l, exp)      
     end
  | PPforall_named (id_lst, pp_ty, exp_lst_lst, exp_lst, exp) -> 
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter (fun var -> l.int_vars <- (fst var)::l.int_vars) id_lst
	 | PPTreal ->
	    List.iter (fun var -> l.real_vars <- (fst var)::l.real_vars) id_lst
	 | _ -> ()
       end;
      fprintf fmt "(forall";
      print_named_ids fmt id_lst;
      fprintf fmt "%a" print_ppure_type1 pp_ty;
      print_triggers fmt  (g, l, exp_lst_lst);
      (*print_filters fmt exp_lst;*)
      fprintf fmt ".\n   %a)" print_lexpr (g, l, exp)      
    end
  | PPexists_named (id_lst, pp_ty, exp_lst_lst, exp_lst, exp) -> 
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter (fun var -> l.int_vars <- (fst var)::l.int_vars) id_lst
	 | PPTreal ->
	    List.iter (fun var -> l.real_vars <- (fst var)::l.real_vars) id_lst
	 | _ -> ()
       end;
       fprintf fmt "(exists";
       print_named_ids fmt id_lst;
       fprintf fmt "%a" print_ppure_type1 pp_ty;
       print_triggers fmt  (g, l, exp_lst_lst);
       (*print_filters fmt exp_lst;*)
       fprintf fmt ".\n   %a)" print_lexpr (g, l, exp)      
     end
  | PPnamed (id, exp) -> assert false
  | PPlet (id, lexp, rexp) ->
     begin
       begin
	 try
	   if type_lexpr lexp g l = Is_Int then
	     l.int_vars <- id :: l.int_vars
	   else l.real_vars <- id :: l.real_vars
	 with Not_Math_Expr -> ()
       end;
       fprintf fmt "let %s = %a in\n   %a" id
	 print_lexpr (g, l, lexp) print_lexpr (g, l, rexp)
     end
  | PPcheck exp -> assert false
  | PPcut exp -> assert false
  | PPcast (exp, pp_ty) ->
     fprintf fmt "%a" print_lexpr (g, l, exp)
       
and print_lexprs fmt (g, l, exprs) =
  List.iter (fun expr ->
    fprintf fmt " %a" print_lexpr (g, l, expr)
  ) exprs
    
and print_arr_set fmt
    (g, l, expr) =
  match expr.pp_desc with
  | PPset (arr_name, index, value) ->
     fprintf fmt "%a" print_arr_set (g, l, arr_name) 
  | _ -> fprintf fmt "%a" print_lexpr (g, l, expr)
     
and print_arr_assig fmt (g, l, expr) =
  match expr.pp_desc with
  | PPset (acc, index, value) ->
    begin
      match acc.pp_desc with
      | PPset _ -> 
	 fprintf fmt "%a[%a<-%a]"
	   print_arr_assig (g, l, acc)
	   print_lexpr (g, l, index)
	   print_lexpr (g, l, value)
      | _ ->
	 fprintf fmt "[%a<-%a]"
	   print_lexpr (g, l, index)
	   print_lexpr (g, l, value)
    end
  | _ -> assert false

and print_triggers fmt (g, l, exp_lst_lst) =
  match exp_lst_lst with
  | [] -> ()
  | [h] -> fprintf fmt "[%a]" print_trigger (g, l, h)
  | h :: tl ->
     begin
       fprintf fmt "[%a" print_trigger (g, l, h);
       let rec print_trigs fmt trs =
	 match trs with
	 | [] -> fprintf fmt "]"
	 | h1::tl1 ->
	    fprintf fmt " | %a%a" print_trigger (g, l, h1) print_trigs tl1
       in print_trigs fmt tl
     end
       
and print_trigger fmt (g, l, tr) =
  match tr with
  | [] -> ()
  | [h] -> fprintf fmt "%a" print_lexpr (g, l, h)
  | h :: tl ->
     begin
       fprintf fmt "%a" print_lexpr (g, l, h);
       List.iter (fun exp ->
	 fprintf fmt ", %a" print_lexpr (g, l,	exp)
       ) tl
     end

and pairwise_distinct fmt (g, l, exprs) =
  match exprs with
  | [] -> ()
  | [h] -> ()
  | h1 :: h2 :: tl ->
     begin
       fprintf fmt "%a <> %a"
	 print_lexpr (g, l, h1) print_lexpr (g, l, h2);
       List.iter (fun v ->
	 fprintf fmt " /\\ %a <> %a"
	   print_lexpr (g, l, h1) print_lexpr (g, l, v))
	 tl;
       pairwise_distinct1 fmt (g, l, (h2::tl))
     end
and pairwise_distinct1 fmt (g, l, exps) =
  match exps with
  | [] -> ()
  | [h] -> ()
  | h :: tl ->
     begin
       List.iter (fun v ->
	 fprintf fmt " /\\ %a <> %a"
	   print_lexpr (g, l, h) print_lexpr (g, l, v))
	 tl;
       pairwise_distinct1 fmt (g, l, tl)
     end
       
let print_func fmt (g,lib,f, f_rm) =
  match f with
  | Function_def (name_id, args, prim_ty, exp )->
     if List.mem (fst name_id) f_rm then ()
     else
       begin
	 let l = {int_vars = []; real_vars = []; bool_vars = []} in
	 let fun_lst = ref [] in
	 test_fun_names g lib exp fun_lst;
	 List.iter (fun fname -> fprintf fmt "%a" print_modules fname)
	   (List.rev !fun_lst);
	 List.iter (fun arg ->
	   let (id,ty) = arg in
	   match ty with
	   | PPTint -> l.int_vars <- id :: l.int_vars
	   | PPTreal -> l.real_vars <- id :: l.real_vars
	   | PPTbool -> l.bool_vars <- id :: l.bool_vars
	   | _ -> ()
	 )args;
	 begin
	   match prim_ty with
	   | PPTint -> g.i_funs <- (fst name_id) :: g.i_funs
	   | PPTreal -> g.r_funs <- (fst name_id) :: g.r_funs
	   | PPTbool -> g.b_funs <- (fst name_id) :: g.b_funs
	   | _ -> ()
	 end;
	 fprintf fmt "\n\nfunction %a%a: %a = %a"
	   print_fun_name name_id print_fun_args args
	   print_ppure_type prim_ty  print_lexpr (g, l, exp)
       end
  | _ -> assert false


let print_pred_name fmt id =
  let (n1, n2) = id in
  if String.length n2 = 0 then fprintf fmt "%s " (String.uncapitalize n1)
  else fprintf fmt "%s %s " (String.uncapitalize n1) n2
  
let print_pred fmt (g, lib, p, preds_rm) = 
  match p with
  | Predicate_def (id, lbls, exp) ->
     begin
       g.b_funs <- (fst id) :: g.b_funs;
       if List.mem (fst id) preds_rm then ()
       else
	 begin
	   let l = {int_vars = []; real_vars = []; bool_vars = []} in
	   let ty_lst = ref [] in
	   test_types lib lbls ty_lst;
           List.iter
	     (fun ty_lib ->
	       fprintf fmt "%a" print_modules ty_lib
	     ) (List.rev !ty_lst);
	   let fun_lst = ref [] in
	   test_fun_names g lib exp fun_lst;
	   List.iter
	     (fun fname ->
	       fprintf fmt "%a" print_modules fname
	     ) (List.rev !fun_lst);
	   begin
	     match lbls with
	     | [] -> fprintf fmt "\n\npredicate %a= %a"
		print_pred_name id print_lexpr (g, l, exp)
	     | _ ->
		begin
		  List.iter (fun lbl ->
		    let (id,ty) = lbl in
		    match ty with
		    | PPTint -> l.int_vars <- id :: l.int_vars
		    | PPTreal -> l.real_vars <- id :: l.real_vars
		    | PPTbool -> l.bool_vars <- id :: l.bool_vars
		    | _ -> ()
		  )lbls;
		  fprintf fmt "\n\npredicate %a%a=\n   %a"	  
		    print_pred_name id print_fun_args lbls
		    print_lexpr (g, l, exp)
		end
	   end
	 end
     end
  | _ -> assert false

let rec test_local_types g l lib expr ty_lst =
  let {pp_desc} = expr in
  match pp_desc with
  | PPvar id -> ()
  | PPapp (id, exprs) ->
     List.iter (fun e -> test_local_types g l lib e ty_lst)
       exprs
  | PPconst const ->
     begin
       match const with
       | ConstInt _ ->
	  if lib.int_lib = false then
	    begin
	      lib.int_lib <- true;
	      ty_lst := "int_lib" :: !ty_lst;
	     end
       | ConstReal _ ->
	  if lib.real_lib = false then
	    begin
	      lib.real_lib <- true;
	      ty_lst := "real_lib" :: !ty_lst;
	     end
       | ConstTrue | ConstFalse ->
	  if lib.bool_lib = false then
	    begin
	      lib.bool_lib <- true;
	      ty_lst := "bool_lib" :: !ty_lst
	    end
       | ConstVoid ->
	  if lib.unit = false then
	    begin
	      lib.unit <- true;
	      ty_lst := "unit" :: !ty_lst
	    end
       | ConstBitv _ -> assert false
     end
  | PPinfix (e1, op, e2)->
     begin
       test_local_types g l lib e1 ty_lst;
       test_local_types g l lib e2 ty_lst
     end
  | PPprefix (op, e1) ->
     test_local_types g l lib e1 ty_lst
  | PPget (e1, e2) ->
     begin
       test_local_types g l lib e1 ty_lst;
       test_local_types g l lib e2 ty_lst
     end
  | PPset (e1, e2, e3) ->
     begin
       test_local_types g l lib e1 ty_lst;
       test_local_types g l lib e2 ty_lst;
       test_local_types g l lib e3 ty_lst
     end
  | PPdot (e1, id) ->
     test_local_types g l lib e1 ty_lst
  | PPrecord lbls -> ()
  | PPwith (e1, lbls) ->
     test_local_types g l lib e1 ty_lst
  | PPextract (e1,e2,e3) ->
     begin
       test_local_types g l lib e1 ty_lst;
       test_local_types g l lib e2 ty_lst;
       test_local_types g l lib e3 ty_lst
     end
  | PPconcat (e1,e2) ->
     begin
       test_local_types g l lib e1 ty_lst;
       test_local_types g l lib e2 ty_lst
     end
  | PPif (e1,e2,e3) ->
     begin
       test_local_types g l lib e1 ty_lst;
       test_local_types g l lib e2 ty_lst;
       test_local_types g l lib e3 ty_lst
     end
  | PPforall (vars, pp_ty, exp_lst_lst, exp_lst, e1) ->
     begin
       test_types1 lib [pp_ty] ty_lst;
       test_local_types g l lib e1 ty_lst
     end
  | PPexists (vars, pp_ty, exp_lst_lst, exp_lst, e1) ->
     begin
       test_types1 lib [pp_ty] ty_lst;
       test_local_types g l lib e1 ty_lst
     end
  | PPforall_named (id_lst, pp_ty, exp_lst_lst, exp_lst, e1) ->
     begin
       test_types1 lib [pp_ty] ty_lst;
       test_local_types g l lib e1 ty_lst
     end
  | PPexists_named (id_lst, pp_ty, exp_lst_lst, exp_lst, e1) ->
     begin
       test_types1 lib [pp_ty] ty_lst;
       test_local_types g l lib e1 ty_lst
     end
  | PPnamed (id, e1) -> test_local_types g l lib e1 ty_lst
  | PPlet (id, e1, e2) ->
     begin
       begin
	 match type_lexpr e1 g l with
	 | Is_Int ->
	    if lib.int_lib = false then
	      begin
		lib.int_lib <- true;
		ty_lst := "int_lib" :: !ty_lst
	      end
	 | Is_Real ->
	    if lib.real_lib = false then
	      begin
		lib.real_lib <- true;
		ty_lst := "real_lib" :: !ty_lst
	      end
	 | Is_Bool ->
	    if lib.bool_lib = false then
	      begin
		lib.bool_lib <- true;
		ty_lst := "bool_lib" :: !ty_lst
	      end
	 | _ -> assert false
       end;
       test_local_types g l lib e1 ty_lst;
       test_local_types g l lib e2 ty_lst
     end
  | PPcheck e1 -> test_local_types g l lib e1 ty_lst
  | PPcut e1 -> test_local_types g l lib e1 ty_lst
  | PPcast (e1, pp_ty) ->
     begin
       test_types1 lib [pp_ty] ty_lst;
       test_local_types g l lib e1 ty_lst
     end
  | PPinInterval _ -> ()
  | PPdistinct exp_lst ->
     List.iter (fun e1 -> test_local_types g l lib e1 ty_lst) exp_lst
     
let print_axiom fmt (g, lib, ax, ax_rm) =
  match ax with
  | Axiom (id, exp) ->
     if List.mem id ax_rm then ()
     else
       begin
	 let l = {int_vars = []; real_vars = []; bool_vars = []} in
	 let fun_lst = ref [] in
	 let ty_lst = ref [] in
	 test_local_types g l lib exp ty_lst;
	 test_fun_names g lib exp fun_lst;
	 List.iter (fun ty ->
	   fprintf fmt "%a" print_modules ty
	 ) (List.rev !ty_lst);
	 List.iter
	   (fun fname ->
	     fprintf fmt "%a" print_modules fname
	   ) (List.rev !fun_lst);
	 fprintf fmt "\n\naxiom %s:\n   %a" id print_lexpr (g, l, exp)
       end
  | _ -> assert false

let print_goal fmt (g, lib, goal) =
  match goal with
  | Goal (id, exp) ->
     begin
       let l = {int_vars = []; real_vars = []; bool_vars = []} in
       let fun_lst = ref [] in
       let ty_lst = ref [] in
       test_local_types g l lib exp ty_lst;
       test_fun_names g lib exp fun_lst;
       List.iter (fun ty ->
	 fprintf fmt "%a" print_modules ty
       ) (List.rev !ty_lst);
       List.iter (fun fname ->
	 fprintf fmt "%a" print_modules fname
       ) (List.rev !fun_lst);
       fprintf fmt "\n\ngoal %s:\n   %a" id print_lexpr (g, l, exp)
     end
  | _ -> assert false
