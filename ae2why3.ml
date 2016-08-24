open Parsing
open Printf
(*open Format*)
open Parsed
open Type_check
open Print_exp

exception Input_Error

let name_file hd ori_file =
  let n = String.length ori_file in
  let j = ref (n-1) in
  while !j <> 0 && String.get ori_file !j <> '/' do
    j := !j - 1
  done;
  if !j = 0 then
    hd ^ ori_file
  else
  (String.sub ori_file 0 (!j + 1))
  ^ hd ^ (String.sub ori_file (!j+1) (n-1-(!j)))
    
let name_theory ori_file =
  let n = String.length ori_file in
  let j = ref (n-1) in
  while !j <> 0 && String.get ori_file !j <> '/' do
    j := !j - 1
  done;
  if !j = 0 then
    let name1 = String.sub ori_file 0 (n-4) in
    let name2 = String.uppercase name1 in
    name2
  else
    let name1 = String.sub ori_file (!j+1) (n-1-(!j)-4) in
    let name2 = String.uppercase name1 in
    name2

let () =
  let ori_file = Sys.argv.(1) in
  let chan_in = open_in ori_file in
  let goal_file =
    if Array.length Sys.argv = 2 then
      name_file "why3_" ori_file
    else Sys.argv.(2)
  in
  let chan_out = open_out goal_file in
  let lexbuf = Lexing.from_channel chan_in in
  let result = Parser.file Lexer.token lexbuf in
  let name = name_theory ori_file in
  let g = {i_vars = []; r_vars = []; i_funs = ["abs_int"]; r_funs = ["abs_real";"real_of_int"; "float";"sqrt_real"]} in
  let lib =
    {int_lib   = false; real_lib  = false; bool_lib  = false;
     float_rnd = false; float_sgl = false; float_dbl = false;
     map_lib   = false; abs_int   = false; abs_real  = false;
     real_of_int = false; sqrt_real = false; mode = false;
     unit = false} in
  fprintf chan_out "theory %s\n" name;
  List.iter (fun st ->
    match st with
    | TypeDecl _ ->
       fprintf chan_out "%a" print_type (g, lib, st)
    | Logic _ ->
       fprintf chan_out "%a" print_logic (g, lib, st)
    | Function_def _ ->
       fprintf chan_out "%a" print_func (g, lib, st)
    | Predicate_def _ ->
       fprintf chan_out "%a" print_pred (g, lib, st)
    | Axiom _ -> 
       fprintf chan_out "%a" print_axiom (g, lib, st)
    | Goal _ -> 
       fprintf chan_out "%a" print_goal (g, lib, st)
    | _ -> assert false
    (*| Rewriting _ -> assert false*)
  )result;
  fprintf chan_out "\n\nend";
  close_in chan_in;
  close_out chan_out
