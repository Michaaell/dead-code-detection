open Typedtree

(* Structure that deals with opened module that we want to check *)
module OpenMap = Map.Make( 
  struct
    let compare = Pervasives.compare
    type t = Path.t
  end )


(* Fonction that extracts the name of a module given its path *)
let print_open_modname = function
  | Path.Pident id -> id.Ident.name
  | _ -> ""
  
(* Fonction that prints a warning regarding an unseless open *)
let print_warning_open p loc =
  let op_name = print_open_modname p in
  Utils.debug "@[%a@] unused open %s @." 
    Location.print loc.Asttypes.loc
    op_name

(* Fonction that prints the long ident (Debug) *)
let print_lg_id lid = 
  List.iter print_endline (Longident.flatten lid)

(* Fonction that checks the long ident *)
let is_long_ident_prefixed k lid =
  (* print_lg_id lid; *)
  let list = Longident.flatten lid in
  if List.length list < 2 then false
  else
    let l = List.rev (List.tl (List.rev list)) in
    let rec aux k l = match k with
      | Path.Pident id ->
          id.Ident.name = (List.hd l)
      | Path.Pdot (p,str,i) ->
         
          if List.length l < 2 then false
          else aux p (List.tl l)
      | Path.Papply (p1,p2) ->  false
    in aux k l

(* Fonction that checks the structure and prints a warning if needed *)
let print_warn_mod_ext s =
  OpenMap.iter (fun k (v,loc) -> 
    if not v then print_warning_open k loc) s

(* Fonction that adds a module to the check list *)
let add_mod_ext k loc m =
  if OpenMap.mem k m
  then m
  else OpenMap.add k (false,loc) m

(* Fonction that updates the structure regarging a module *)
(* We need to check if the value is prefixed by its module name *)
let rec set_mod_ext_used (k,lg_id) m =
  if OpenMap.mem k m
  then 
    let (flag,loc) = OpenMap.find k m in
    if flag
    then m
    else 
      if not (is_long_ident_prefixed k lg_id.Location.txt)
      then OpenMap.add k (true,loc) m
      else m
  else 
    begin
      match k with
        | Path.Pdot (p,_,_) -> set_mod_ext_used (p,lg_id) m
        | _ -> m
    end

(* Fonction that checks core type desc *)
let check_core_type_desc m ct = match ct.ctyp_desc with
  | Ttyp_constr (path,lg_ident,_) | Ttyp_class (path,lg_ident,_,_) ->
      set_mod_ext_used (path,lg_ident) m
  | _ -> m

(* Fonction that check  the core type desc list of a type *)
let check_core_type_desc_list m l =
  List.fold_left (fun acc x -> check_core_type_desc acc x) m l
