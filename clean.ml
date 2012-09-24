open Typedtree
open Ident
open Cmt_format

let print_warning_id id loc =
  Utils.debug "@[%a@] %s is unused@." 
    Location.print loc.Asttypes.loc
    id.name
    (* Printer.print_warning_path (Warnings.Unused_var id.Ident.name) *)

let print_warning_type id loc =
  Utils.debug "@[%a@] type %s is never used.@." 
    Location.print loc.Asttypes.loc
    id.name

let print_warning_cnstr id loc =
  Utils.debug "@[%a@] constructor %s is never used.@." 
    Location.print loc.Asttypes.loc
    id.name

let print_warning_rec id loc =
  Utils.debug "@[%a@] field %s is never used.@." 
    Location.print loc.Asttypes.loc
    id.name

(* let print_warning_path path loc = *)
(*   Utils.debug "@[%a@] %s is unused@." *)
(*     Location.print loc.Asttypes.loc *)
(*     (Path.head path).name *)
(*     (\* Printer.print_warning_path (Warnings.Unused_var (Path.head path).name) *\) *)

(* let is_in e s =  *)
(*   Utils.IdentSet.mem e s *)

let is_in_id id s = 
  Utils.PathSet.mem (Path.Pident id) s

let rec clean_exp idlist = function
  | Texp_ident (path,loc,val_desc) as x -> x
  | Texp_constant c as x -> x
  | Texp_let (rec_flag,list,e) as x ->
      ignore (clean_let_list idlist list);
      ignore (clean_exp idlist e.exp_desc);
      x
  | Texp_function (lbl,l,part) as x ->
      let rec aux = function
        | [] -> []
        | (p,e1)::ys -> ignore(clean_exp idlist e1.exp_desc);aux ys in ignore(aux l);x
  | Texp_apply (e,list) as x -> x
  | Texp_construct (path,loc,constr_des,list,_) as x -> x
  | Texp_sequence (e1,e2) ->
      let new_e1 = { e1 with exp_desc = clean_exp idlist e1.exp_desc } and
          new_e2 = { e1 with exp_desc = clean_exp idlist e2.exp_desc } in
      Texp_sequence (new_e1,new_e2)
  | Texp_record (l,e_opt) as x -> x
  | _ as x -> x

and clean_let_list id_list =
  let clean_patexp (p,e1) = match p.pat_desc with
    | Tpat_var (id,loc) ->
        if not (is_in_id id id_list)
        then 
          begin 
            print_warning_id id loc;
            (p,e1) 
          end
        else (p,{ e1 with exp_desc = clean_exp id_list e1.exp_desc})
    | _ -> (p,{ e1 with exp_desc = clean_exp id_list e1.exp_desc}) in
  let rec clean_let_aux = function
    | [] -> []
    | x::xs -> clean_patexp x::(clean_let_aux xs)
  in clean_let_aux

let clean_record l idl =
  let l1,l2 = List.partition (fun (id,loc,_,_,_) -> (is_in_id id idl)) l in
  List.iter (fun (id,loc,_,_,_) -> print_warning_rec id loc) l2;
  l1
    
let clean_variant l idl =
  let l1,l2 = List.partition (fun (id,loc,_,_) -> (is_in_id id idl)) l in
  List.iter (fun (id,loc,_,_) -> print_warning_cnstr id loc) l2;
  l1

let clean_type id loc td idl = match td.typ_kind with
    | Ttype_variant list -> 
        let l = clean_variant list idl in
        if List.length l = 0 
        then 
          begin 
            print_warning_type id loc;
            None
          end
        else Some (Ttype_variant l)
    | Ttype_record list -> 
        let l = clean_record list idl in
        if List.length l = 0 
        then 
          begin 
            print_warning_type id loc;
            None
          end
        else Some (Ttype_record l)
    | _ as x -> Some x   

let clean_type_decl ltd idl =
  let _ = List.map (fun (id,loc,tdl) -> 
    (id,loc,clean_type id loc tdl idl)) ltd in 
  ()
  
let soft_clean_struct_item_descr src idl = function
  | Tstr_eval e -> Some ( Tstr_eval { e with exp_desc = clean_exp idl e.exp_desc})
  | Tstr_value (recflag,list) ->
      let new_list = clean_let_list idl list in
      if (new_list = []) 
      then None
      else Some (Tstr_value (recflag,new_list))
  | Tstr_type l -> clean_type_decl l idl;Some (Tstr_type l)
  | _ as x -> Some x


let soft_clean_structure_items src l idl = 
  let rec aux = function
    | [] -> []
    | x::xs ->
        let new_desc = soft_clean_struct_item_descr src idl x.str_desc in
        begin
          match new_desc with
            | Some d -> {x with str_desc = d}::(aux xs)
            | None -> aux xs
        end
  in aux l

let soft_clean_annot src idl = function
  | Implementation strct -> 
      {strct with str_items = (soft_clean_structure_items src strct.str_items idl)}
  | _ -> failwith "Can't clean that" 


let soft_clean filename idl =
  let cmt_inf = Cmt_format.read_cmt filename in
  soft_clean_annot cmt_inf.cmt_modname idl cmt_inf.cmt_annots
