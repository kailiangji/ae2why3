open Parsed
open Printf
open Type_check

let rec print_ppure_type chan_out ty =
  match ty with
  | PPTint -> fprintf chan_out "int"
  | PPTbool -> fprintf chan_out "bool"
  | PPTreal -> fprintf chan_out "real"
  | PPTunit -> fprintf chan_out "tuple0"
  | PPTbitv _ -> assert false
  | PPTvarid (id,_) ->
     fprintf chan_out "'%s" (String.uncapitalize id)
  | PPTexternal (pt_lst, id,_) ->
     if List.length pt_lst = 0 then
       fprintf chan_out "%s"
	 (if id = "fpa_rounding_mode" then "mode"
	  else (String.uncapitalize id))
     else
       begin
	 fprintf chan_out "(%s" 
	   ( if id ="farray" then "map"
	     else (String.uncapitalize id));
	 List.iter (fun pt ->
	   fprintf chan_out " %a" print_ppure_type pt) pt_lst;
	 fprintf chan_out ")"
       end
	 
let rec print_ppure_type1 chan_out ty =
  match ty with
  | PPTint -> fprintf chan_out "int"
  | PPTbool -> fprintf chan_out "bool"
  | PPTreal -> fprintf chan_out "real"
  | PPTunit -> fprintf chan_out "tuple0"
  | PPTbitv _ -> assert false
  | PPTvarid (id,_) ->
     fprintf chan_out "'%s" (String.uncapitalize id)
  | PPTexternal (pt_lst, id,_) ->
     if List.length pt_lst = 0 then
       fprintf chan_out "%s"
	 (if id = "fpa_rounding_mode" then
	     "mode"
	  else (String.uncapitalize id))
     else
       begin
	 fprintf chan_out "%s" 
	   ( if id = "farray" then "map"
	     else (String.uncapitalize id));
	 List.iter (fun pt ->
	   fprintf chan_out " %a" print_ppure_type pt) pt_lst;
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
	  int_of_string m1 <= 24 && int_of_string e1 <= 149
       | _,_ -> assert false
     end
  | _ -> assert false 
  
       
let rec test_fun_names g l  lib expr fun_lst =
  let {pp_loc;pp_desc} = expr in
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
	      (fun e1 -> test_fun_names g l lib e1 fun_lst)
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
	      (fun e1 -> test_fun_names g l lib e1 fun_lst)
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
	      (fun e1 -> test_fun_names g l lib e1 fun_lst)
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
	      (fun e1 -> test_fun_names g l lib e1 fun_lst)
	      exprs
	  end
	   
       | _ ->
	  List.iter (fun e1 -> test_fun_names g l lib e1 fun_lst)
	    exprs
     end
  | PPconst const -> ()
  | PPinfix (e1, op, e2)->
     begin
       begin
	 match op with
	 | PPmod ->
	    if lib.int_div = false then
	      begin
		lib.int_div <- true;
		fun_lst := "int_div"::!fun_lst;
	      end;
	 | PPdiv ->
	    if lib.int_div = false && type_lexpr e1 g l = Is_Int then
	      begin
		lib.int_div <- true;
		fun_lst := "int_div"::!fun_lst;
	      end
	 |_ -> ()
       end;
       test_fun_names g l lib e1 fun_lst;
       test_fun_names g l lib e2 fun_lst
     end
  | PPprefix (op, e1) ->
     test_fun_names g l lib e1 fun_lst
  | PPget (e1, e2) ->
     begin
       test_fun_names g l lib e1 fun_lst;
       test_fun_names g l lib e2 fun_lst
     end
  | PPset (e1, e2, e3) ->
     begin
       test_fun_names g l lib e1 fun_lst;
       test_fun_names g l lib e2 fun_lst;
       test_fun_names g l lib e3 fun_lst
     end
  | PPdot (e1, id) ->
     test_fun_names g l lib e1 fun_lst
  | PPrecord lbls -> ()
  | PPwith (e1, lbls) ->
     test_fun_names g l lib e1 fun_lst
  | PPextract (e1,e2,e3) ->
     begin
       test_fun_names g l lib e1 fun_lst;
       test_fun_names g l lib e2 fun_lst;
       test_fun_names g l lib e3 fun_lst
     end
  | PPconcat (e1,e2) ->
     begin
       test_fun_names g l lib e1 fun_lst;
       test_fun_names g l lib e2 fun_lst
     end
  | PPif (e1,e2,e3) ->
     begin
       test_fun_names g l lib e1 fun_lst;
       test_fun_names g l lib e2 fun_lst;
       test_fun_names g l lib e3 fun_lst
     end
  | PPforall (vars, pp_ty, exp_lst_lst, e1) ->
     test_fun_names g l lib e1 fun_lst
  | PPexists (vars, pp_ty, exp_lst_lst, e1) ->
     test_fun_names g l lib e1 fun_lst
  | PPforall_named (id_lst, pp_ty, exp_lst_lst, e1) -> 
     test_fun_names g l lib e1 fun_lst
  | PPexists_named (id_lst, pp_ty, exp_lst_lst, e1) -> 
     test_fun_names g l lib e1 fun_lst
  | PPnamed (id, e1) -> test_fun_names g l lib e1 fun_lst
  | PPlet (id, e1, e2) ->
     begin
       test_fun_names g l lib e1 fun_lst;
       test_fun_names g l lib e2 fun_lst
     end
  | PPcheck e1 -> test_fun_names g l lib e1 fun_lst
  | PPcut e1 -> test_fun_names g l lib e1 fun_lst
  | PPcast (e1, pp_ty) ->
     test_fun_names g l lib e1 fun_lst 
  | PPinInterval _ -> ()
  | PPdistinct exp_lst ->
     List.iter (fun e1 -> test_fun_names g l lib e1 fun_lst) exp_lst

let print_modules chan_out fname =
  match fname with
  | "int_lib" -> fprintf chan_out "\n\nuse import int.Int"
  | "real_lib" -> fprintf chan_out "\n\nuse import real.RealInfix"
  | "bool_lib" -> fprintf chan_out "\n\nuse import bool.Bool"
  | "map_lib" -> fprintf chan_out "\n\nuse import map.Map"
  | "abs_int" -> fprintf chan_out "\n\nuse import int.Abs as IA"
  | "abs_real" -> fprintf chan_out "\n\nuse import real.Abs as RA"
  | "real_of_int" -> fprintf chan_out "\n\nuse import real.FromInt"
  | "sqrt_real" -> assert false
  | "single" -> fprintf chan_out "\n\nuse import floating_point.Single as S"
  | "double" -> fprintf chan_out "\n\nuse import floating_point.Double as D"
  | "mode" -> fprintf chan_out "\n\nuse import floating_point.Rounding"
  | "unit" -> fprintf chan_out "\n\nuse import Tuple0"
  | "int_div" -> fprintf chan_out "\n\nuse import int.ComputerDivision"
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
	       lib.int_lib <- true; lib_lst := "int_lib" :: !lib_lst
	     end
	| PPTbool ->
	   if lib.bool_lib = false then
	     begin
	       lib.bool_lib <- true; lib_lst := "bool_lib" :: !lib_lst
	     end
	| PPTreal ->
	   if lib.real_lib = false then
	     begin
	       lib.real_lib <- true; lib_lst := "real_lib" :: !lib_lst
	     end
	| PPTunit ->
	   if lib.unit = false then
	     begin
	       lib.unit <- true; lib_lst := "unit" :: !lib_lst
	     end
	| PPTexternal (pt_lst, id,_) ->
	   begin
	     if lib.map_lib = false && id = "farray" then
	       begin
		 lib.map_lib <- true; lib_lst := "map_lib" :: !lib_lst
	       end
	     else
	       if lib.mode = false && id = "fpa_rounding_mode" then
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




let test_types2 lib lb_tys lib_lst =
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
	| PPTexternal (pt_lst, id,_) ->
	   begin
	     if lib.map_lib = false && id = "farray" then
	       begin
		 lib.map_lib <- true;
		 lib_lst := "map_lib" :: !lib_lst;
	       end
	     else
	       if lib.mode = false && id = "fpa_rounding_mode" then
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


let test_types lib lb_tys lib_lst =
  List.iter
    (fun lb_ty ->
      let (_,var, ty) = lb_ty in
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
	| PPTexternal (pt_lst, id,_) ->
	   begin
	     if lib.map_lib = false && id = "farray" then
	       begin
		 lib.map_lib <- true;
		 lib_lst := "map_lib" :: !lib_lst;
	       end
	     else
	       if lib.mode = false && id = "fpa_rounding_mode" then
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


let rec test_local_types g l lib expr ty_lst =
  let {pp_loc;pp_desc} = expr in
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
  | PPforall (vars, pp_ty, exp_lst_lst, e1) ->
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter (fun var -> l.int_vars <- var :: l.int_vars) vars
	 | PPTreal ->
	    List.iter (fun var -> l.real_vars <- var::l.real_vars) vars
	 | _ -> ()
       end;
       test_types1 lib [pp_ty] ty_lst;
       test_local_types g l lib e1 ty_lst
     end
  | PPexists (vars, pp_ty, exp_lst_lst, e1) ->
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter (fun var -> l.int_vars <- var :: l.int_vars) vars
	 | PPTreal ->
	    List.iter (fun var -> l.real_vars <- var::l.real_vars) vars
	 | _ -> ()
       end;
       test_types1 lib [pp_ty] ty_lst;
       test_local_types g l lib e1 ty_lst
     end
  | PPforall_named (id_lst, pp_ty, exp_lst_lst, e1) ->
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter
	      (fun var -> l.int_vars <- (fst var)::l.int_vars) id_lst
	 | PPTreal ->
	    List.iter
	      (fun var -> l.real_vars <- (fst var)::l.real_vars) id_lst
	 | _ -> ()
       end;
       test_types1 lib [pp_ty] ty_lst;
       test_local_types g l lib e1 ty_lst
     end
  | PPexists_named (id_lst, pp_ty, exp_lst_lst, e1) ->
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter
	      (fun var -> l.int_vars <- (fst var)::l.int_vars) id_lst
	 | PPTreal ->
	    List.iter
	      (fun var -> l.real_vars <- (fst var)::l.real_vars) id_lst
	 | _ -> ()
       end;
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

    
let rec print_record chan_out lb_types =
  match lb_types with
  | [] -> ()
  | [lb] ->
     let (var,ty) = lb in
     fprintf chan_out "%s : %a" var print_ppure_type ty
  | h :: tl ->
     let (var,ty) = h in
     fprintf chan_out "%s : %a; %a" var print_ppure_type ty print_record tl
       
let print_type chan_out (g, lib, ty) =
  match ty with
  | TypeDecl (_,vars, id, Abstract) ->
     begin
       match id with
       | "single" ->
	  if lib.float_sgl = false then
	    begin
	      lib.float_sgl <- true;
	      fprintf chan_out "\n\nuse import floating_point.Single as S";
		assert (vars = [])
	    end
       | "double" ->
	  if lib.float_dbl = false then
	    begin
	      lib.float_dbl <- true;
	      fprintf chan_out "\n\nuse import floating_point.Double as D";
		assert (vars = [])
	    end
       | _ ->
	  begin
	    fprintf chan_out "\n\ntype %s " (String.uncapitalize id);
	    List.iter (fun var -> fprintf chan_out "'%s " var) vars
	  end
     end
  | TypeDecl (_,vars, id, Enum id_lst) ->
     begin
       fprintf chan_out "\n\ntype %s " id;
       List.iter (fun var -> fprintf chan_out "'%s " var) vars;
       fprintf chan_out "= %s" (List.hd id_lst);
       List.iter (fun id -> fprintf chan_out " | %s" id)
	 (List.tl id_lst);
     end
  | TypeDecl (_,vars, id, Record lbl_lst) ->
     begin
       let lib_lst = ref [] in
       test_types2 lib lbl_lst lib_lst;
       List.iter (fun lib -> print_modules chan_out lib)
	 (List.rev !lib_lst);
       fprintf chan_out "\n\ntype %s " id;
       List.iter (fun var -> fprintf chan_out "'%s " var) vars;
       fprintf chan_out "= {%a}" print_record lbl_lst;
     end
  | _ -> assert false


let rec print_named_ids chan_out id_lst =
  match id_lst with
  | [] -> fprintf chan_out " : "
  | h :: tl ->
    let (n1, n2) = h in
    if String.length n2 = 0 then
      fprintf chan_out " %s%a" n1 print_named_ids tl
    else
      fprintf chan_out " (%s %s)%a" n1 n2 print_named_ids tl

let rec print_ppred chan_out pp_tys =
  match pp_tys with
  | [] -> ()
  | [h] -> fprintf chan_out "%a " print_ppure_type h
  | h :: tl ->
     fprintf chan_out "%a %a" print_ppure_type h print_ppred tl

let print_pfun chan_out pp_tys pp_ty =
  List.iter (fun t -> fprintf chan_out "%a " print_ppure_type t)
    pp_tys;
  fprintf chan_out ": %a" print_ppure_type1 pp_ty

    
let print_fun_type chan_out ty =
  match ty with
  | PPredicate pp_tys -> print_ppred chan_out pp_tys
  | PFunction (pp_tys, pp_ty) -> print_pfun chan_out pp_tys pp_ty

let print_fun_name chan_out id =
  let (h,t)= id in
  if String.length t = 0 then
    fprintf chan_out "%s " (String.uncapitalize h)
  else fprintf chan_out "%s %s " (String.uncapitalize h) t

let print_fun_args chan_out args =
  List.iter (fun arg ->
    let (_, var, ty) = arg in
    fprintf chan_out "(%s : %a) " var print_ppure_type1 ty
  ) args

    
let print_logic chan_out (g, lib, lg, f_rm) =
  match lg with
  | Logic (_,nam_kd,id_lst, ty) ->
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
			 fprintf chan_out "\n\nuse import bool.Bool"
		       end;
		     g.b_vars <- (fst id) :: g.b_vars;
		     if List.mem (fst id) f_rm then ()
		     else
		       fprintf chan_out "\n\nconstant %a%a: bool"
			 print_fun_name id  print_fun_type ty
		   )id_lst
		 else
		   begin
		     let lib_lst = ref [] in
		     test_types1 lib pp_tys lib_lst;
		     List.iter (fun lib -> print_modules chan_out lib)
		       (List.rev !lib_lst);
		     List.iter (fun id ->
		       if lib.bool_lib = false then
			 begin
			   lib.bool_lib <- true;
			   fprintf chan_out "\n\nuse import bool.Bool"
			 end;
		       g.b_funs <- (fst id) :: g.b_funs;
		       if List.mem (fst id) f_rm then ()
		       else
			 fprintf chan_out "\n\nfunction %a%a: bool"
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
		       (fun lib -> print_modules chan_out lib)
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
			 fprintf chan_out "\n\nconstant %a%a"
			   print_fun_name id print_fun_type ty
		     )id_lst
		   end
		 else
		   begin
		     let lib_lst = ref [] in
		     test_types1 lib pp_tys lib_lst;
		     test_types1 lib [pp_ty] lib_lst;
		     List.iter
		       (fun lib -> print_modules chan_out lib)
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
			 fprintf chan_out "\n\nfunction %a%a"
			   print_fun_name id print_fun_type ty
		     )id_lst
		   end
	       end
	  end
       | Ac -> assert false
       | _ -> assert false
     end
  | _ -> assert false
     
let print_pp_infix chan_out (g, l, rexp, op) =
  match op with
  | PPand -> fprintf chan_out "/\\"
  | PPor -> fprintf chan_out "\\/"
  | PPimplies -> fprintf chan_out "->\n   "
  | PPiff -> fprintf chan_out "<->"
  | PPlt ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf chan_out "<"
       | Is_Real -> fprintf chan_out "<."
       | _ -> begin Loc.report rexp.pp_loc; raise Not_Int_Real end
     end
  | PPle ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf chan_out "<="
       | Is_Real -> fprintf chan_out "<=."
       | _ -> begin Loc.report rexp.pp_loc; raise Not_Int_Real end
     end
  | PPgt ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf chan_out ">"
       | Is_Real -> fprintf chan_out ">."
       | _ -> begin Loc.report rexp.pp_loc; raise Not_Int_Real end
     end
  | PPge ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf chan_out ">="
       | Is_Real -> fprintf chan_out ">=."
       | _ -> begin Loc.report rexp.pp_loc; raise Not_Int_Real end
     end
  | PPeq -> fprintf chan_out "="
  | PPneq -> fprintf chan_out "<>"
  | PPadd ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf chan_out "+"
       | Is_Real -> fprintf chan_out "+."
       | _ -> begin Loc.report rexp.pp_loc; raise Not_Int_Real end
     end
  | PPsub ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf chan_out "-"
       | Is_Real -> fprintf chan_out "-."
       | _ -> begin Loc.report rexp.pp_loc; raise Not_Int_Real end
     end
  | PPmul ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf chan_out "*"
       | Is_Real -> fprintf chan_out "*."
       | _ -> begin Loc.report rexp.pp_loc; raise Not_Int_Real end
     end
  | PPdiv ->
     begin
       match type_lexpr rexp g l with
       | Is_Int -> fprintf chan_out "div"
       | Is_Real -> fprintf chan_out "/."
       | _ -> begin Loc.report rexp.pp_loc; raise Not_Int_Real end
     end
  | PPmod -> fprintf chan_out "mod"

let rec print_lexpr chan_out (g, l, expr) =
  let {pp_loc;pp_desc} = expr in
  match pp_desc with
  | PPvar id -> fprintf chan_out "%s" id
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
		    fprintf chan_out "(S.round %a %a)"
		      print_lexpr (g, l, mode) print_lexpr (g, l, exp)
		 | PPconst(ConstInt "53"), PPconst(ConstInt "1074") ->
		    fprintf chan_out "(D.round %a %a)"
		      print_lexpr (g, l, mode) print_lexpr (g, l, exp)
		 | PPconst(ConstInt m1), PPconst(ConstInt e1) ->
		    if int_of_string m1 <= 24 && int_of_string e1 <= 149 then
		      fprintf chan_out "(S.round %a %a)"
			print_lexpr (g, l, mode) print_lexpr (g, l, exp)
		    else
		      fprintf chan_out "(D.round %a %a)"
			print_lexpr (g, l, mode) print_lexpr (g, l, exp)
		 | _,_ -> assert false
	       end
	    | _ -> assert false
       end
       | "abs_int" -> fprintf chan_out "(IA.abs%a)" print_lexprs (g, l, exprs)
       | "abs_real" -> fprintf chan_out "(RA.abs%a)" print_lexprs (g, l, exprs)
       | "real_of_int" ->
	  fprintf chan_out "(from_int%a)" print_lexprs (g, l, exprs)
       | "round" -> fprintf chan_out "(S.round%a)" print_lexprs (g, l, exprs)
       | "value" -> fprintf chan_out "(S.value%a)" print_lexprs (g, l, exprs)
       | "exact" -> fprintf chan_out "(S.exact%a)" print_lexprs (g, l, exprs)
       | "fpa_rounding_model" -> fprintf chan_out "(S.model%a)"
	  print_lexprs (g, l, exprs)
       | "round_error" -> fprintf chan_out "(S.round_error%a)"
	  print_lexprs (g, l, exprs)
       | "total_error" -> fprintf chan_out "(S.total_error%a)"
	  print_lexprs (g, l, exprs)
       | "round_logic" -> fprintf chan_out "(S.round_logic%a)"
	  print_lexprs (g, l, exprs)
       | "round1" -> fprintf chan_out "(D.round%a)" print_lexprs (g, l, exprs)
       | "value1" -> fprintf chan_out "(D.value%a)" print_lexprs (g, l, exprs)
       | "exact1" -> fprintf chan_out "(D.exact%a)" print_lexprs (g, l, exprs)
       | "fpa_rounding_model1" -> fprintf chan_out "(D.model%a)"
	  print_lexprs (g, l, exprs)
       | "round_error1" -> fprintf chan_out "(D.round_error%a)"
	  print_lexprs (g, l, exprs)
       | "total_error1" -> fprintf chan_out "(D.total_error%a)"
	  print_lexprs (g, l, exprs)
       | "round_logic1" -> fprintf chan_out "(D.round_logic%a)"
	  print_lexprs (g, l, exprs)
       |_ -> fprintf chan_out "(%s%a)"
	  (String.uncapitalize id) print_lexprs (g, l, exprs)
     end
  | PPinInterval _ -> assert false
  | PPdistinct exprs ->
     fprintf chan_out "(%a)" pairwise_distinct (g, l, exprs)
  | PPconst const -> 
    begin
      match const with
      | ConstBitv b -> fprintf chan_out "%s" b
      | ConstInt i -> fprintf chan_out "%s" i
      | ConstReal n -> fprintf chan_out "%s"
	 (string_of_float (Num.float_of_num n)) (*?*)
      | ConstTrue -> fprintf chan_out "true"
      | ConstFalse -> fprintf chan_out "false"
      | ConstVoid -> fprintf chan_out "Tuple0"
    end
  | PPinfix (e1, op, e2) -> 
    begin
      match op with
      | PPmod ->
	 fprintf chan_out "(%a %a %a)"
	   print_pp_infix (g, l, e1, op)
	   print_lexpr (g, l, e1)
	   print_lexpr (g, l, e2)
      | PPand | PPor | PPimplies | PPiff | PPneq ->
	 fprintf chan_out "(%a %a %a)" 
	   print_lexpr (g, l, e1)
	   print_pp_infix (g, l, e2, op)
	   print_lexpr (g, l, e2)
      | PPlt | PPle | PPgt | PPge | PPeq ->
	 fprintf chan_out "%a %a %a" 
	   print_lexpr (g, l, e1)
	   print_pp_infix (g, l, e2, op)
	   print_lexpr (g, l, e2)
      | PPdiv ->
	 if type_lexpr e1 g l = Is_Int then
	 begin
	   fprintf chan_out "(%a %a %a)"
	     print_pp_infix (g, l, e1, op)
	     print_lexpr (g, l, e1)
	     print_lexpr (g, l, e2)
	 end
	 else
	   begin
	     assert (type_lexpr e1 g l = Is_Real);
	     fprintf chan_out "(%a %a %a)" 
	       print_lexpr (g, l, e1)
	       print_pp_infix (g, l, e2, op)
	       print_lexpr (g, l, e2)
	   end
      | _ ->
	 fprintf chan_out "(%a %a %a)" 
	 print_lexpr (g, l, e1)
	 print_pp_infix (g, l, e1, op)
	 print_lexpr (g, l, e2)
    end 
  | PPprefix (op, exp) ->
    begin
      match op with
      | PPneg ->
	 if type_lexpr exp g l = Is_Int then 
	   fprintf chan_out "(-%a)" print_lexpr (g, l, exp)
	 else
	   fprintf chan_out "(-.%a)" print_lexpr (g, l, exp)
      | PPnot -> fprintf chan_out "(not %a)" print_lexpr (g, l, exp)
    end
  | PPget (e1, e2) ->
     fprintf chan_out "%a[%a]"
       print_lexpr (g, l, e1) print_lexpr (g, l, e2)
  | PPset (e1, mexp, e2) ->
     fprintf chan_out "%a%a"
       print_arr_set (g, l, expr) print_arr_assig (g, l, expr)
  | PPdot (exp, id) -> assert false
  | PPrecord lbl_lst -> assert false
  | PPwith (exp, lbl_lst) -> assert false
  | PPextract (e1, mexp, e2) -> assert false
  | PPconcat (e1, e2) -> assert false
  | PPif (e1, e2, e3) ->
     fprintf chan_out "(if %a then %a else %a)"
       print_lexpr (g, l, e1)
       print_lexpr (g, l, e2)
       print_lexpr (g, l, e3)
  | PPforall (t_lst, pp_ty, exp_lst_lst, exp) -> 
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter (fun var -> l.int_vars <- var :: l.int_vars) t_lst
	 | PPTreal ->
	    List.iter (fun var -> l.real_vars <- var::l.real_vars) t_lst
	 | _ -> ()
       end;
       fprintf chan_out "(forall";
       List.iter (fun var -> fprintf chan_out " %s" var) t_lst;
       fprintf chan_out "%a" print_ppure_type1 pp_ty;
       print_triggers chan_out (g, l, exp_lst_lst);
       (*print_filters chan_out exp_lst;*)
       fprintf chan_out ".\n   %a)" print_lexpr (g, l, exp)      
    end
  | PPexists (t_lst, pp_ty, exp_lst_lst, exp) -> 
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter (fun var -> l.int_vars <- var::l.int_vars) t_lst
	 | PPTreal ->
	    List.iter (fun var -> l.real_vars <- var::l.real_vars) t_lst
	 | _ -> ()
       end;
       fprintf chan_out "(exists";
       List.iter (fun var -> fprintf chan_out " %s" var) t_lst;
       fprintf chan_out "%a" print_ppure_type1 pp_ty;
       print_triggers chan_out  (g, l, exp_lst_lst);
       (*print_filters chan_out exp_lst;*)
       fprintf chan_out ".\n   %a)" print_lexpr (g, l, exp)      
     end
  | PPforall_named (id_lst, pp_ty, exp_lst_lst, exp) -> 
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter (fun var -> l.int_vars <- (fst var)::l.int_vars) id_lst
	 | PPTreal ->
	    List.iter (fun var -> l.real_vars <- (fst var)::l.real_vars) id_lst
	 | _ -> ()
       end;
      fprintf chan_out "(forall";
      print_named_ids chan_out id_lst;
      fprintf chan_out "%a" print_ppure_type1 pp_ty;
      print_triggers chan_out  (g, l, exp_lst_lst);
      (*print_filters chan_out exp_lst;*)
      fprintf chan_out ".\n   %a)" print_lexpr (g, l, exp)      
    end
  | PPexists_named (id_lst, pp_ty, exp_lst_lst, exp) -> 
     begin
       begin
	 match pp_ty with
	 | PPTint ->
	    List.iter
	      (fun var -> l.int_vars <- (fst var)::l.int_vars) id_lst
	 | PPTreal ->
	    List.iter
	      (fun var -> l.real_vars <- (fst var)::l.real_vars) id_lst
	 | _ -> ()
       end;
       fprintf chan_out "(exists";
       print_named_ids chan_out id_lst;
       fprintf chan_out "%a" print_ppure_type1 pp_ty;
       print_triggers chan_out  (g, l, exp_lst_lst);
       (*print_filters chan_out exp_lst;*)
       fprintf chan_out ".\n   %a)" print_lexpr (g, l, exp)      
     end
  | PPnamed (id, exp) -> assert false
  | PPlet (id, e1, e2) ->
     begin
       begin
	 match type_lexpr e1 g l with
	 | Is_Int  -> l.int_vars <- id :: l.int_vars
	 | Is_Real -> l.real_vars <- id :: l.real_vars
	 | Is_Bool -> l.bool_vars <- id :: l.bool_vars
       end;
       fprintf chan_out "let %s = %a in\n   %a" id
	 print_lexpr (g, l, e1) print_lexpr (g, l, e2)
     end
  | PPcheck exp -> assert false
  | PPcut exp -> assert false
  | PPcast (exp, pp_ty) ->
     fprintf chan_out "%a" print_lexpr (g, l, exp)
       
and print_lexprs chan_out (g, l, exprs) =
  List.iter (fun expr ->
    fprintf chan_out " %a" print_lexpr (g, l, expr)
  ) exprs
    
and print_arr_set chan_out
    (g, l, expr) =
  match expr.pp_desc with
  | PPset (arr_name, index, value) ->
     fprintf chan_out "%a" print_arr_set (g, l, arr_name) 
  | _ -> fprintf chan_out "%a" print_lexpr (g, l, expr)
     
and print_arr_assig chan_out (g, l, expr) =
  match expr.pp_desc with
  | PPset (acc, index, value) ->
    begin
      match acc.pp_desc with
      | PPset _ -> 
	 fprintf chan_out "%a[%a<-%a]"
	   print_arr_assig (g, l, acc)
	   print_lexpr (g, l, index) print_lexpr (g, l, value)
      | _ ->
	 fprintf chan_out "[%a<-%a]"
	   print_lexpr (g, l, index) print_lexpr (g, l, value)
    end
  | _ -> assert false

and print_triggers chan_out (g, l, exp_lst_lst) =
  match exp_lst_lst with
  | [] -> ()
  | [h] -> fprintf chan_out "[%a]" print_trigger (g, l, h)
  | h :: tl ->
     begin
       fprintf chan_out "[%a" print_trigger (g, l, h);
       List.iter
	 (fun tr ->
	   fprintf chan_out " | %a" print_trigger (g, l, tr)
	 )tl;
       fprintf chan_out "]"
     end
       
and print_trigger chan_out (g, l, tr) =
  match tr with
  | [] -> ()
  | [h] -> fprintf chan_out "%a" print_lexpr (g, l, h)
  | h :: tl ->
     begin
       fprintf chan_out "%a" print_lexpr (g, l, h);
       List.iter (fun exp ->
	 fprintf chan_out ", %a" print_lexpr (g, l,	exp)
       ) tl
     end

and pairwise_distinct chan_out (g, l, exprs) =
  match exprs with
  | [] -> ()
  | [h] -> ()
  | h1 :: h2 :: tl ->
     begin
       fprintf chan_out "%a <> %a"
	 print_lexpr (g, l, h1) print_lexpr (g, l, h2);
       List.iter (fun v ->
	 fprintf chan_out " /\\ %a <> %a"
	   print_lexpr (g, l, h1) print_lexpr (g, l, v))
	 tl;
       pairwise_distinct1 chan_out (g, l, (h2::tl))
     end
and pairwise_distinct1 chan_out (g, l, exps) =
  match exps with
  | [] -> ()
  | [h] -> ()
  | h :: tl ->
     begin
       List.iter (fun v ->
	 fprintf chan_out " /\\ %a <> %a"
	   print_lexpr (g, l, h) print_lexpr (g, l, v))
	 tl;
       pairwise_distinct1 chan_out (g, l, tl)
     end
       
let print_func chan_out (g,lib,f, f_rm) =
  match f with
  | Function_def (_,name_id, args, prim_ty, exp )->
     if List.mem (fst name_id) f_rm then ()
     else
       begin
	 let l = {int_vars = []; real_vars = []; bool_vars = []} in
	 let lib_lst = ref [] in
	 List.iter
	   (fun arg ->
	     let (_,id,ty) = arg in
	     begin
	       test_types1 lib [ty] lib_lst;
	       match ty with
	       | PPTint  -> l.int_vars  <- id :: l.int_vars
	       | PPTreal -> l.real_vars <- id :: l.real_vars
	       | PPTbool -> l.bool_vars <- id :: l.bool_vars
	       | _ -> ()
	     end
	   )args;
	 begin
	   test_types1 lib [prim_ty] lib_lst;
	   match prim_ty with
	   | PPTint -> g.i_funs <- (fst name_id) :: g.i_funs
	   | PPTreal -> g.r_funs <- (fst name_id) :: g.r_funs
	   | PPTbool -> g.b_funs <- (fst name_id) :: g.b_funs
	   | _ -> ()
	 end;
	 test_local_types g l lib exp lib_lst;
	 List.iter
	   (fun lib -> print_modules chan_out lib)
	   (List.rev !lib_lst);
	 let fun_lst = ref [] in
	 test_fun_names g l lib exp fun_lst;
	 List.iter (fun fname ->
	   fprintf chan_out "%a" print_modules fname)
	   (List.rev !fun_lst);
	 fprintf chan_out "\n\nfunction %a%a: %a = %a"
	   print_fun_name name_id print_fun_args args
	   print_ppure_type prim_ty  print_lexpr (g, l, exp)
       end
  | _ -> assert false


let print_pred_name chan_out id =
  let (n1, n2) = id in
  if String.length n2 = 0 then
    fprintf chan_out "%s " (String.uncapitalize n1)
  else
    fprintf chan_out "%s %s " (String.uncapitalize n1) n2
  
let print_pred chan_out (g, lib, p, preds_rm) = 
  match p with
  | Predicate_def (_,id, lbls, exp) ->
     begin
       g.b_funs <- (fst id) :: g.b_funs;
       if List.mem (fst id) preds_rm then ()
       else
	 begin
	   let l = {int_vars = []; real_vars = []; bool_vars = []} in
	   List.iter (fun lbl ->
	     let (_,id,ty) = lbl in
	     match ty with
	     | PPTint -> l.int_vars <- id :: l.int_vars
	     | PPTreal -> l.real_vars <- id :: l.real_vars
	     | PPTbool -> l.bool_vars <- id :: l.bool_vars
	     | _ -> ()
	   )lbls;
	   let ty_lst = ref [] in
	   test_types lib lbls ty_lst;
	   test_local_types g l lib exp ty_lst;
           List.iter
	     (fun ty_lib ->
	       fprintf chan_out "%a" print_modules ty_lib
	     ) (List.rev !ty_lst);
	   let fun_lst = ref [] in
	   test_fun_names g l lib exp fun_lst;
	   List.iter
	     (fun fname ->
	       fprintf chan_out "%a" print_modules fname
	     ) (List.rev !fun_lst);
	   fprintf chan_out "\n\npredicate %a%a=\n   %a"	  
	     print_pred_name id print_fun_args lbls
	     print_lexpr (g, l, exp)
	 end
     end
  | _ -> assert false


     
let print_axiom chan_out (g, lib, ax, ax_rm) =
  match ax with
  | Axiom (_,id, exp) ->
     if List.mem id ax_rm then ()
     else
       begin
	 let l = {int_vars = []; real_vars = []; bool_vars = []} in
	 let fun_lst = ref [] in
	 let ty_lst = ref [] in
	 test_local_types g l lib exp ty_lst;
	 test_fun_names g l lib exp fun_lst;
	 List.iter (fun ty ->
	   fprintf chan_out "%a" print_modules ty
	 ) (List.rev !ty_lst);
	 List.iter
	   (fun fname ->
	     fprintf chan_out "%a" print_modules fname
	   ) (List.rev !fun_lst);
	 fprintf chan_out "\n\naxiom %s:\n   %a" id print_lexpr (g, l, exp)
       end
  | _ -> assert false

let print_goal chan_out (g, lib, goal) =
  match goal with
  | Goal (_,id, exp) ->
     begin
       let l = {int_vars = []; real_vars = []; bool_vars = []} in
       let ty_lst = ref [] in
       test_local_types g l lib exp ty_lst;
       let fun_lst = ref [] in
       test_fun_names g l lib exp fun_lst;
       List.iter (fun ty ->
	 fprintf chan_out "%a" print_modules ty
       ) (List.rev !ty_lst);
       List.iter (fun fname ->
	 fprintf chan_out "%a" print_modules fname
       ) (List.rev !fun_lst);
       fprintf chan_out "\n\ngoal %s:\n   %a" id print_lexpr (g, l, exp)
     end
  | _ -> assert false
