open Cmt_format
open Types
open Typedtree
open Ident

let mod_list = ref []

let rec is_id_in_mod_list id = function
  | [] -> false
  | x::_ when x = id.name -> true
  | _::xs -> is_id_in_mod_list id xs

let is_in_mod_list = function
  | Path.Pident id -> is_id_in_mod_list id !mod_list
  | _ -> false


(** Lors de l'appel d'une fonction, si elle vient d'un module qu'on 
    n'analyse pas alors on dit qu'elle fait des effets de bords ! 
*)

let side_effect_fun = ref Utils.PathSet.empty


let path_make_side_effect' = function
  | Path.Pdot(_,_,26) -> true (* IF PERVASIVE *)
  | Path.Pdot(_,_,29) -> true (* IF PERVASIVE *)
  | _ -> false

let path_make_side_effect = function
  | Path.Pdot(_,_,26) -> true (* IF PERVASIVE *)
  | Path.Pdot(_,_,29) -> true (* IF PERVASIVE *)
  | Path.Pdot(modname,var,st) ->
      if (is_in_mod_list modname) then false
      else true
  | _ as p -> Utils.PathSet.mem p !side_effect_fun 

(* let rec side_effect_in_list = function *)
(*   | [] -> false *)
(*   | true::xs -> true *)
(*   | _::xs -> side_effect_in_list xs *)

(* let rec match_fun_apply p dep_list e = match e.exp_desc with *)
(*   | Texp_ident (path,_,_) ->  *)
(*       begin  *)
(*         match path with *)
(*           | Path.Pdot (p,s,26) -> true *)
(*           | _ -> false *)
(*       end *)
(*   | Texp_let (_,list,_) -> add_side_effect p dep_list list *)
(*   | Texp_function _ -> false *)
(*   | Texp_apply (e,list) ->  *)
(*       let f = match_fun_apply p dep_list e in *)
(*       if f  *)
(*       then true *)
(*       else (\* add_side_effect dep_list list *\)false *)
(*   | Texp_sequence (e1,e2) -> *)
(*       (exp_side_effect p dep_list e1) || (exp_side_effect p dep_list e2) *)
(*   | Texp_tuple list -> *)
(*       let l = List.map (fun e ->  *)
(*         exp_side_effect p dep_list e) list in *)
(*       side_effect_in_list l *)
(*   | _ -> true *)
      

let rec exp_side_fun_body list =
  let aux = function
    | Texp_ident _ | Texp_constant _ -> false
    | Texp_apply (e,list) ->
        begin
          match e.exp_desc with
            | Texp_ident (p,loc,_) ->
                if path_make_side_effect p then true
                else false
            | _ -> false
        end  
    | _ -> false
  in  
  List.fold_left (fun b (p,e) -> b || aux e.exp_desc) false list

let rec exp_side_let_body = function
  | Texp_ident _ | Texp_constant _ -> false
  | Texp_let (_,list,e) ->
      List.fold_left (fun b (p,e) ->
        b || exp_side_let_body e.exp_desc) false list
  | Texp_function (lbl,list,part) ->
      exp_side_fun_body list
  | _ -> false

          

and get_path_from_pat p = match p.pat_desc with 
    | Tpat_any -> Path.Pident (Ident.create "any")
    | Tpat_var (id,loc) -> Path.Pident id
    | Tpat_alias (p,kind,_) -> failwith "as TODO"
    | Tpat_constant cnst -> failwith "cst TODO"
    | Tpat_tuple pat_list -> get_path_from_pat (List.hd pat_list)
    | Tpat_construct (path,loc,cnstor_desc,exp_list,_) -> path
    | Tpat_variant (lbl,pat_option,row_desc) -> failwith "var TODO"
    | Tpat_record (list,flag) -> failwith "rec TODO"
    | Tpat_array pat_list -> failwith "array TODO"
    | Tpat_or (pat1,pat2,row_desc_opt) -> failwith "or TODO"
    | Tpat_lazy pat -> failwith "lazy TODO"

(* Si on def une fonction on veut savoir si celle ci 
   fait des effets de bords.Si oui on ajoute dans la table, 
   attention au let f = print_truc;fun x -> x + 1 *)

and exp_side = function
  | Texp_ident _ -> ()
  | Texp_constant _ -> ()
  | Texp_let (rec_flag,list,e) -> 
      List.iter (fun (p,e) ->
        let path = get_path_from_pat p in
        let flag = exp_side_let_body e.exp_desc in
        if (flag)
        then side_effect_fun := Utils.PathSet.add path !side_effect_fun) list;
      exp_side e.exp_desc
  (* | Texp_function (lbl,l,part) -> *)
  (*     List.iter (fun (p,e) -> exp_side e.exp_desc) l *)
  (* | Texp_apply (e,l) -> () *)
  (* | Texp_match (e,l,part) -> () *)
  (* | Texp_try (e,l) -> () *)
  (* | Texp_tuple l -> *)
  (*     List.iter (fun e -> exp_side e.exp_desc) l *)
  (* | Texp_construct (_,_,_,el) -> *)
  (*     List.iter (fun e -> exp_side e.exp_desc) el *)
  | _ -> () 

let side_struct_item_descr s = match s.str_desc with 
  | Tstr_eval e -> exp_side e.exp_desc
  | Tstr_value (recflag,list) -> 
      List.iter (fun (p,e) ->
        let path = get_path_from_pat p in
        let flag = exp_side_let_body e.exp_desc in
        if (flag)
        then side_effect_fun := Utils.PathSet.add path !side_effect_fun) list;
  | Tstr_type l -> failwith "type"
  | Tstr_include (_, _) -> failwith "inc todo"
  | Tstr_class_type _ -> failwith "ct todo"
  | Tstr_class _ -> failwith "cl todo"
  | Tstr_open (_, _) -> failwith "open todo"
  | Tstr_modtype (_, _, _) -> failwith "modtype todo"
  | Tstr_recmodule _ -> failwith "recmodule todo"
  | Tstr_module (id, _, _) ->  failwith "module todo"
  | Tstr_exn_rebind (_, _, _, _) -> failwith "exnreb todo"
  | Tstr_exception (_, _, _) -> failwith "exc todo"
  | Tstr_primitive (_, _, _)   -> failwith "prim todo"


let side_structure_items list =
  List.iter side_struct_item_descr list

let side_annot = function
  | Implementation strct -> side_structure_items strct.str_items
  | _ -> failwith "Can't print that" 

let main_side modlist filename =
  mod_list := modlist;
  let cmt_inf = Cmt_format.read_cmt filename in
  side_annot cmt_inf.cmt_annots;
  !side_effect_fun



(** Sur LES DEPS *)

let reverse_dep local_dep = 
  Utils.DepMap.fold (fun k v acc -> 
    Utils.PathSet.fold (fun x acc -> Deps.add_entry x k acc) v acc
  ) local_dep Utils.DepMap.empty

let rec aux rdeps id acc =
  if Utils.DepMap.mem id rdeps
  then 
    let new_acc = Utils.PathSet.add id acc in
    let path_list = Utils.DepMap.find id rdeps in
    Utils.PathSet.fold (fun x acc -> aux rdeps x acc) path_list new_acc
  else Utils.PathSet.add id acc

let id_affect_by_side_effect rdeps =
  Utils.DepMap.fold (fun k v acc ->
    if path_make_side_effect' k then
      Utils.PathSet.fold (fun x acc -> aux rdeps x acc) v acc
    else
      acc
  ) rdeps Utils.PathSet.empty
  

