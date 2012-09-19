module OpenMap = Map.Make( 
  struct
    let compare = Pervasives.compare
    type t = Path.t
  end )

(** Fonctions pour chercher les open inutiles *)

let print_open_modname = function
  | Path.Pident id -> id.Ident.name
  | _ -> ""
  

let print_warning_open p loc =
  let op_name = print_open_modname p in
  Utils.debug "@[%a@] unused open %s @." 
    Location.print loc.Asttypes.loc
    op_name

let print_lg_id lid = 
  List.iter print_endline (Longident.flatten lid)

let is_long_ident_prefixed k lid =
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


let print_warn_mod_ext s =
  OpenMap.iter (fun k (v,loc) -> 
    if not v then print_warning_open k loc) s
    (* if not v then Utils.debug "Unused open %a @." Printer.print_path k *)

let print_mod_ext s =
  OpenMap.iter (fun k (v,loc) -> 
    if not v then Utils.debug "Unused open %a @." Printer.print_path k) s

let add_mod_ext k loc m =
  if OpenMap.mem k m
  then m
  else OpenMap.add k (false,loc) m

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

      
