open Typedtree

(* Structure that deals with args that we want to check *)
module ArgMap = Map.Make( 
  struct
    let compare = Pervasives.compare
    type t = Path.t
  end )

(* Function that adds a function to the check list *)
let add_fun k m =
  if ArgMap.mem k m
  then m
  else ArgMap.add k Utils.PathSet.empty m

(* Function that adds an used arg to the check list *)
let add_arg fun_p arg_p m =
  if ArgMap.mem fun_p m
  then 
    let arg_set = ArgMap.find fun_p m in
    let new_arg_set = Utils.PathSet.add arg_p arg_set in
    ArgMap.add fun_p new_arg_set m
  else
    begin
      Utils.debug "can't happend @.";
      m
    end

(* Function that add an arg to the checklist of its function *)
let rec add_pattern fun_p m p = match p.pat_desc with
  | Tpat_var (id,_) -> add_arg fun_p (Path.Pident id) m
  | Tpat_alias (pat,id,_) ->
      let new_m = add_arg fun_p (Path.Pident id) m in
      add_pattern fun_p new_m pat
  | Tpat_tuple l -> 
      List.fold_left (fun acc x -> add_pattern fun_p acc x) m l 
  | _ -> m
  
(* Function that adds an arg list to the checklist of its function *)
let add_arg_list fun_p l m =
  List.fold_left (fun acc (p,_) -> add_pattern fun_p acc p) m l

(* Function that checks the argmap with the dependences *)
let check_argmap m d =
  ArgMap.fold (fun fun_p arg_list acc ->
    if Utils.DepMap.mem fun_p d
    then
      (* We need to know if fun_p uses the args in arg_list *)
      let list_alive = Utils.get_alive fun_p Utils.PathSet.empty d in
      (* Utils.debug "%a@." Utils.print_set_path list_alive; *)
      let dead_arg = 
        Utils.PathSet.filter (fun x -> 
          not (Utils.PathSet.mem x list_alive)) arg_list in
      if Utils.PathSet.cardinal dead_arg > 1 
      then ArgMap.add fun_p dead_arg acc
      else acc
    else
      ArgMap.add fun_p arg_list acc
  ) m ArgMap.empty 

(* let print_warn m l =  *)
(* match l with *)
(*   | *)

(* Function that prints an ArgMap *)
let print_argmap m =
  ArgMap.iter (fun k v ->
    Utils.debug "%a :? %a @." Printer.print_path k Utils.print_set_path v
  ) m
