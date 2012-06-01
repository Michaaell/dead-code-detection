open Cmt_format
open Types
open Typedtree
open Ident

(* Ident for the program *)
let ident_prog = ref (Path.Pident (Ident.create ""))

let ident_prog_list = ref []

let cmt_modname = ref []

let ind = ref 0


(******************************************************************************)
(**   Test pour les calculs de graph de dependences sur des petits exemples  **)

type graph = (Ident.t * Ident.t) list

let rec get_id_from_path = function 
  | Path.Pident id -> id
  | Path.Pdot (p,s,i) ->  
      Ident.create (
        (Ident.unique_name (get_id_from_path p))^"."^s^(string_of_int i))
  | Path.Papply (p1,p2) ->
       Ident.create (
         (Ident.unique_name 
            (get_id_from_path p1))^(Ident.unique_name (get_id_from_path p2)))


(* Calcul de dep *)          
          
let rec calc_dep deps_list id = function
  | Texp_ident (path,loc,val_desc) ->
      let dep_id = path in
      if dep_id = id 
      then deps_list
      else (id,dep_id)::deps_list
  | Texp_constant c -> deps_list
  | Texp_let (rec_flag,list,e) ->
      let new_dep_list = calc_dep_let deps_list list in
      calc_dep new_dep_list id e.exp_desc
  | Texp_function (lbl,l,part) ->
       let rec aux xs = function
        | [] -> xs
        | (p,e1)::ys ->
            let new_dep = calc_dep xs id e1.exp_desc in
            aux new_dep ys
       in (aux deps_list l)(* deps_list *)
  | Texp_apply (e,list) ->
      let calc_params deps_list = function
        | (_,Some e1,_) ->
            calc_dep deps_list id e1.exp_desc
        | (_,None,_) ->
            deps_list 
      in 
      let new_dep = List.fold_left calc_params deps_list list in
      calc_dep new_dep id e.exp_desc
  | Texp_construct (path,loc,constr_des,list) ->
      let dep_id = path in
      let new_dep_list = (id,dep_id)::deps_list in
      List.fold_left (fun dep_list x -> 
        calc_dep dep_list id x.exp_desc) new_dep_list list
  | Texp_sequence (e1,e2) -> 
      let new_dep = calc_dep deps_list id e1.exp_desc in
      calc_dep new_dep id e2.exp_desc
  | Texp_tuple list ->
      List.fold_left (fun dep_list e -> 
        calc_dep dep_list id e.exp_desc) deps_list list
  | Texp_match (e,l,part) ->
      let new_dep = calc_dep deps_list id e.exp_desc in
      let rec aux dep_list = function
        | [] -> dep_list
        | (p,e1)::xs -> 
            let new_dep = dep_in_patexp_case p e1 id dep_list in
            aux new_dep xs
      in aux new_dep l
  | Texp_field (e,path,_,_) ->
      let new_dep_list = calc_dep deps_list id e.exp_desc in
      let dep_id = path in
      (id,dep_id)::new_dep_list
  | Texp_record (l,e) -> 
      begin
        match e with
          | None -> 
              List.fold_left (fun dep_list (path,_,_,e) -> 
                calc_dep dep_list id e.exp_desc) deps_list l
          | Some e1 ->
              let new_deps =  
                List.fold_left (fun dep_list (path,_,_,e) -> 
                  calc_dep dep_list id e.exp_desc) deps_list l in
              calc_dep new_deps id e1.exp_desc
      end
  | Texp_when (e1,e2) ->
      let new_dep_list = calc_dep deps_list id e1.exp_desc in
      calc_dep new_dep_list id e2.exp_desc
  | Texp_open (_, _, e) -> calc_dep deps_list id e.exp_desc
  | Texp_pack _ -> deps_list
  | Texp_newtype (_, e) -> calc_dep deps_list id e.exp_desc
  | Texp_object (_, _) -> deps_list
  | Texp_poly (e, _) -> calc_dep deps_list id e.exp_desc
  | Texp_lazy e -> calc_dep deps_list id e.exp_desc
  | Texp_assert e -> calc_dep deps_list id e.exp_desc
  | Texp_letmodule (_, _, _, e) -> calc_dep deps_list id e.exp_desc
  | Texp_override (_, l) ->  
      List.fold_left (fun dep_list (_,_,e) -> calc_dep dep_list id e.exp_desc) deps_list l
  | Texp_setinstvar (_, _, _, e) -> calc_dep deps_list id e.exp_desc
  | Texp_instvar (_, _, _) -> deps_list 
  | Texp_new (_, _, _) -> deps_list
  | Texp_send (e0, _, e1_opt) -> calc_dep deps_list id e0.exp_desc
  | Texp_constraint (e, _, _) -> calc_dep deps_list id e.exp_desc
  | Texp_for (_, _, e0, e1, _, e2) -> 
      let deps1 = calc_dep deps_list id e0.exp_desc in
      let deps2 = calc_dep deps1 id e1.exp_desc in
      calc_dep deps2 id e2.exp_desc
  | Texp_while (e1, e2) -> 
      let deps1 = calc_dep deps_list id e1.exp_desc in
      calc_dep deps1 id e2.exp_desc
  | Texp_ifthenelse (e0, e1, e2_opt) ->
      begin
        match e2_opt with
          | None -> 
              let deps1 = calc_dep deps_list id e0.exp_desc in
              calc_dep deps1 id e1.exp_desc
          | Some e2 ->
              let deps1 = calc_dep deps_list id e0.exp_desc in
              let deps2 = calc_dep deps1 id e1.exp_desc in
              calc_dep deps2 id e2.exp_desc
      end 
  | Texp_array l ->  
      List.fold_left (fun dep_list e -> calc_dep dep_list id e.exp_desc) deps_list l
  | Texp_setfield (e0, _, _, _, e1) ->
      let deps1 = calc_dep deps_list id e1.exp_desc in
      calc_dep deps1 id e1.exp_desc
  | Texp_variant (_, _) -> deps_list      
  | Texp_try (e, l) -> calc_dep deps_list id e.exp_desc
  | Texp_assertfalse -> deps_list
  (*| _ as x ->
      Utils.debug "Can't calc dep on @[%a@]@." Printer.print_tt_expr_desc x;
      deps_list*)

and calc_index_let index l =
  let rec get_path_from_patexp = function
    | Tpat_any -> Path.Pident (Ident.create "any")
    | Tpat_var (id,loc) -> Path.Pident id
    | Tpat_alias (p,kind) -> failwith "as TODO"
    | Tpat_constant cnst -> failwith "cst TODO"
    | Tpat_tuple pat_list -> failwith "tuple TODO"
    (* List.fold_left (fun l i ->  *)
    (*   List.append l (aux i.pat_desc)) [] pat_list *)
    | Tpat_construct (path,loc,cnstor_desc,exp_list) -> Path.Pident (Ident.create "any")
    | Tpat_variant (lbl,pat_option,row_desc) -> failwith "var TODO"
    | Tpat_record (list,flag) -> failwith "rec TODO"
    | Tpat_array pat_list -> failwith "array TODO"
    | Tpat_or (pat1,pat2,row_desc_opt) -> failwith "or TODO"
    | Tpat_lazy pat -> failwith "lazy TODO"
  in  
  List.fold_left 
    (fun index (x,e) -> 
      incr ind;
      (!ind-1,get_path_from_patexp x.pat_desc)::index)
    index l
  

and calc_dep_let dep_list =
  let rec aux dep_list = function
    | [] -> dep_list
    | (p,e1)::deps_list -> 
        let new_dep = dep_in_patexp_def p e1 dep_list in
        aux new_dep deps_list
  in aux dep_list

  
and dep_in_patexp_def p e1 dep_list =
  let rec pat_aux = function
    | Tpat_any ->
        let id = Path.Pident (Ident.create "any") in
        calc_dep dep_list id e1.exp_desc
    | Tpat_var (id,loc) -> calc_dep dep_list (Path.Pident id) e1.exp_desc
    | Tpat_alias (p,kind) -> failwith "as TODO"
    | Tpat_constant cnst -> failwith "cst TODO"
    | Tpat_tuple pat_list ->
        List.fold_left (fun l i -> 
          List.append l (pat_aux i.pat_desc)) [] pat_list
    | Tpat_construct (path,loc,cnstor_desc,exp_list) -> dep_list
    | Tpat_variant (lbl,pat_option,row_desc) -> failwith "var TODO"
    | Tpat_record (list,flag) -> failwith "rec TODO"
    | Tpat_array pat_list -> failwith "array TODO"
    | Tpat_or (pat1,pat2,row_desc_opt) -> failwith "or TODO"
    | Tpat_lazy pat -> failwith "lazy TODO"
  in pat_aux p.pat_desc

and dep_in_patexp_case p e1 id dep_list =
  let rec pat_aux id dep_list = function
    | Tpat_any -> dep_list
    | Tpat_var (id_var,_) -> (Path.Pident id_var,id)::dep_list
    | Tpat_alias (p,kind) -> failwith "as TODO"
    | Tpat_constant cnst -> failwith "cst TODO"
    | Tpat_tuple pat_list ->
        List.fold_left (fun l i -> 
          List.append l (pat_aux id dep_list i.pat_desc)) [] pat_list
    | Tpat_construct (path,loc,cnstor_desc,pat_list) -> 
        List.fold_left (fun l i -> 
          (pat_aux id dep_list i.pat_desc)) dep_list pat_list
    | Tpat_variant (lbl,pat_option,row_desc) -> failwith "var TODO"
    | Tpat_record (list,flag) -> 
        let new_dep_list = 
          List.fold_left (fun dep_list (path,_,_,pat) -> 
            pat_aux path dep_list pat.pat_desc) 
            dep_list list in
        calc_dep new_dep_list id e1.exp_desc
    | Tpat_array pat_list -> failwith "array TODO"
    | Tpat_or (pat1,pat2,row_desc_opt) -> failwith "or TODO"
    | Tpat_lazy pat -> failwith "lazy TODO"
  in calc_dep (pat_aux id dep_list p.pat_desc) id e1.exp_desc

let rec calc_core_type id dps = function
  | Ttyp_any -> dps
  | Ttyp_var s -> dps
  | Ttyp_arrow (lbl,_,_) -> dps
  | Ttyp_tuple _ -> dps
  | Ttyp_constr (path,_,ctl) -> 
      let new_id = path in
      let new_deps =  
        List.fold_left (fun deps ct ->
          calc_core_type new_id deps ct.ctyp_desc) dps ctl in 
      (id,new_id)::new_deps
  | Ttyp_object _ -> dps
  | Ttyp_class (path,_,_,_) -> (id,path)::dps
  | Ttyp_alias (_,s) -> dps
  | Ttyp_package _ -> dps
  | Ttyp_variant (_,_,_) -> dps
  | Ttyp_poly (l,ct) -> calc_core_type id dps ct.ctyp_desc

let calc_type (id0,_,td) dps =
  let calc_type_var l = 
    List.fold_left (fun deps_list (id,_,ctl,_) -> 
      List.fold_left (fun deps_list ct -> 
        calc_core_type (Path.Pident id) deps_list ct.ctyp_desc) deps_list ctl) dps l in
  let calc_type_rec l = 
    List.fold_left (fun deps_list (id,_,_,ct,_) -> 
      calc_core_type (Path.Pident id) ((Path.Pident id0,Path.Pident id)::deps_list) ct.ctyp_desc) dps l in
  let calc_type_desc td = match td.typ_kind with  
    | Ttype_variant l -> calc_type_var l
    | Ttype_record l -> calc_type_rec l
    | Ttype_abstract -> dps
  in calc_type_desc td

let calc_struct_item_descr src index ident_prog deps = function
  | Tstr_eval e -> 
        (* Utils.debug "indexing %a" Printer.print_tt_expr_desc e.exp_desc; *)
      (index,calc_dep deps ident_prog e.exp_desc)
    (* incr ind; *)
    (* ((!ind,itm_desc)::index,calc_dep deps ident_prog e.exp_desc) *)
  | Tstr_value (recflag,list) -> 
        (* (index,calc_dep_let deps list)  *)
      (calc_index_let index list,calc_dep_let deps list)
  | Tstr_type l -> 
      (index,
       List.fold_left (fun new_deps t -> (calc_type t new_deps)) deps l)
  | Tstr_include (_, _) -> failwith "inc todo"
  | Tstr_class_type _ -> failwith "ct todo"
  | Tstr_class _ -> failwith "cl todo"
  | Tstr_open (_, _) -> (index,deps)
  | Tstr_modtype (_, _, _) -> failwith "modtype todo"
  | Tstr_recmodule _ -> failwith "recmodule todo"
  | Tstr_module (id, _, _) ->  incr ind;((!ind-1,Path.Pident id)::index,deps)
  | Tstr_exn_rebind (_, _, _, _) -> failwith "exnreb todo"
  | Tstr_exception (_, _, _) -> failwith "exc todo"
  | Tstr_primitive (_, _, _)   -> failwith "prim todo"
        
let calc_structure_items src list =
  ident_prog := Path.Pident (Ident.create src);
  ident_prog_list := (src,(!ident_prog))::(!ident_prog_list);
  List.fold_left (fun (index,dep) x -> 
    calc_struct_item_descr src index !ident_prog dep x.str_desc) ([],[]) list

let calc_annot src = function
  | Implementation strct -> calc_structure_items src strct.str_items
  | _ -> failwith "Can't print that" 
 
let calc filename  =
  let cmt_inf = Cmt_format.read_cmt filename in
  ind := 0;
  cmt_modname := (filename,cmt_inf.cmt_modname)::!cmt_modname;
  calc_annot cmt_inf.cmt_modname cmt_inf.cmt_annots

let is_in e s = 
  Utils.IdentSet.mem e s

let is_in_path e s = 
  Utils.PathSet.mem e s

let rec live id acc l = function
  | [] -> acc
  | (x,y)::xs when (x = id && not (is_in_path y acc))->
      (* Utils.debug "%i " (List.length xs); *)
      begin
        match y with 
          | Path.Pdot _ -> live id acc l xs
          | _ -> 
              let new_acc = 
                (Utils.PathSet.add y acc) in
              let new_acc1 = (live y new_acc l l)  and
                  new_acc2 = (live id new_acc l xs) in
              Utils.PathSet.union new_acc1 new_acc2
      end
  | x::xs -> live id acc l xs
  

(* Arbre sans id inutile *)

let rec clean_exp idlist = function
  | Texp_ident (path,loc,val_desc) as x -> x
  | Texp_constant c as x -> x
  | Texp_let (rec_flag,list,e) ->
      let new_defs = clean_let_list idlist list in
      if (List.length new_defs) = 0
      then clean_exp idlist e.exp_desc
      else 
        let new_exp = clean_exp idlist e.exp_desc in
        let res = Texp_let (rec_flag,new_defs,{e with exp_desc = new_exp}) in
        res
  | Texp_function (lbl,l,part) ->
      let rec aux = function
        | [] -> []
        | (p,e1)::ys ->
            begin 
              match p.pat_desc with
                | Tpat_var (id,loc) ->
                    (* Utils.debug "delete %a ?" Ident.print id; *)
                    (*debug "delete %s ? " (Ident.name id);*)
                    if not (is_in id idlist)
                    then aux ys
                    else 
                      begin
                        let new_e1 = 
                          {e1 with exp_desc = clean_exp idlist e1.exp_desc} in
                        (p,new_e1)::aux ys
                      end
                | _ -> 
                    begin
                      let new_e1 = 
                        {e1 with exp_desc = clean_exp idlist e1.exp_desc} in
                      (p,new_e1)::aux ys
                    end
            end in 
      let new_defs = aux l in
      Texp_function (lbl,new_defs,part)
  | Texp_apply (e,list) as x -> x
  | Texp_construct (path,loc,constr_des,list) as x -> x
  | Texp_sequence (e1,e2) ->
      let new_e1 = { e1 with exp_desc = clean_exp idlist e1.exp_desc } and
          new_e2 = { e1 with exp_desc = clean_exp idlist e2.exp_desc } in
      Texp_sequence (new_e1,new_e2)
  | Texp_record (l,e_opt) ->
      begin
        let rec clean_rec_list = function
          | [] -> []
          | ((path,_,_,_) as x)::xs ->
              if is_in (get_id_from_path path) idlist 
              then x::(clean_rec_list xs)
              else (clean_rec_list xs)
        in match e_opt,clean_rec_list l with
          (* | None,[] ->  *)
          | None,(_ as l) -> Texp_record (l,None)
          | Some e,[] -> clean_exp idlist e.exp_desc
          | Some e,l -> 
              Texp_record(l,
                           Some {e with exp_desc = clean_exp idlist e.exp_desc})
      end
  | _ as x -> x

and clean_let_list id_list =
  let rec is_pat_alive p = match p.pat_desc with
      | Tpat_var (id,loc) -> is_in id id_list
      | Tpat_tuple l ->
          let new_tuple = List.filter (fun x -> not (is_pat_alive x)) l in
          new_tuple = []
      | _ -> true in
  let rec clean_patexp (p,e1) = match p.pat_desc with
    | Tpat_tuple l ->
        let new_tuple = List.filter (fun x -> is_pat_alive x) l in
        if new_tuple = []
        then None
        else 
          let new_e1 = {e1 with exp_desc = clean_exp id_list e1.exp_desc} in
          Some (p,new_e1)
    | _ ->
        if is_pat_alive p
        then 
          let new_e1 = {e1 with exp_desc = clean_exp id_list e1.exp_desc} in
          Some (p,new_e1)
        else None in
  let rec clean_let_aux = function
    | [] -> []
    | x::xs ->
        begin
          let new_patexp = clean_patexp x in
          match new_patexp with
            | None -> clean_let_aux xs
            | Some pe -> pe::(clean_let_aux xs)
        end
  in clean_let_aux


let clean_type idl (id,loc,typ_desc) = 
  let rec clean_type_var dep = 
    List.filter (fun (id,_,_,_) -> is_in id idl) in
  let rec clean_type_rec idl = 
    List.filter (fun (id,_,_,_,_) -> is_in id idl) in
  let clean_type_desc dep td = match td.typ_kind with  
    | Ttype_variant l -> 
        let new_list = clean_type_var idl l in
        if (new_list = [])
        then None
        else 
          Some {td with 
            typ_kind = Ttype_variant (clean_type_var idl l)}
    | Ttype_record l -> 
        let new_list = clean_type_rec idl l in
        if (new_list = [])
        then None
        else 
          Some {td with 
            typ_kind = Ttype_record (clean_type_rec idl l)}
    | Ttype_abstract -> Some td
  in
  if is_in id idl 
  then (id,loc,Some typ_desc)
  else (id,loc,clean_type_desc idl typ_desc)
  
let clean_struct_item_descr src idl = function
  | Tstr_eval e -> 
      Some (Tstr_eval {e with exp_desc = (clean_exp idl e.exp_desc)})
  | Tstr_value (recflag,list) ->
      let new_list = clean_let_list idl list in
      if (new_list = []) 
      then None
      else Some (Tstr_value (recflag,new_list))
  | Tstr_type l -> 
      let new_list = (List.map (clean_type idl) l) in
      let new_list2 = List.concat (List.map (fun (id,loc,x) -> 
          match x with
            | None -> []
            | Some x -> [(id,loc,x)]) new_list) in
      if (new_list2 = [])
      then None
      else Some (Tstr_type new_list2)
  | _ -> failwith "todo"


let clean_structure_items src l idl = 
  let rec aux = function
    | [] -> []
    | x::xs ->
        let new_desc = clean_struct_item_descr src idl x.str_desc in
        begin
          match new_desc with
            | Some d -> {x with str_desc = d}::(aux xs)
            | None -> aux xs
        end
  in aux l

let clean_annot src idl = function
  | Implementation strct -> 
      {strct with str_items = (clean_structure_items src strct.str_items idl)}
  | _ -> failwith "Can't clean that" 


let clean_ttree filename idl =
  let cmt_inf = Cmt_format.read_cmt filename in
  clean_annot cmt_inf.cmt_modname idl cmt_inf.cmt_annots

let mod_equality p m = match p with
  | Path.Pident id -> id.name = m
  | _ -> false


(** !!!!!!! + NAME EQ pour etre sur ?! *)
let rec id_from_cnstr i = function
  | [] -> failwith ("can't find construction "^string_of_int i)
  | (x,y)::xs when x = i -> 
      (* Utils.debug "@[ +%a(%i)+@]@." Printer.print_path y i; *)
      y
  | _::xs -> id_from_cnstr i xs

let rec get_from_ident_prog_list id = function
  | [] -> failwith "no id"
  | (x,y)::xs when x = id -> y
  | _::xs -> get_from_ident_prog_list id xs

let rec live_dep id id2 ((mod2,cnst2,l2) as c) l = function
  | [] -> c
  | (x,y)::xs when x = id ->
      begin
        Utils.debug "[%a]@," Printer.print_path y;
        match y with
          | Path.Pdot (p,s,i) -> 
              if mod_equality p mod2
              then 
                let new_l2 = (id2,id_from_cnstr i cnst2)::l2 in
                let c = (live_dep y id2 (mod2,cnst2,new_l2) l l) in
                (live_dep id id2 c l xs)
              else
                let c = (live_dep y id2 (mod2,cnst2,l2) l l) in
                (live_dep id id2 c l xs)   
          | _ -> let c = (live_dep y id2 (mod2,cnst2,l2) l l) in
                 (live_dep id id2 c l xs)      
      end
      (* Si y est dans mod2 alors on ajoute une dep a l2 et on continue*)
  | x::xs -> live_dep id id2 c l xs
      
let rec test_id (mod1,cnst1,l1) (mod2,cnst2,l2) = ()

let rec is_mod p = function
  | [] -> false
  | (x1,_)::_ when mod_equality p x1 -> true
  | _::xs -> is_mod p xs
      
let get_modname = function
  | Path.Pident id -> id.name
  | _ -> failwith "no module name here"
      
let rec get_deps_cnst modname = function
  | [] -> failwith "can't find this mod"
  | (x,y)::_ when x = modname -> y
  | _::xs -> get_deps_cnst modname xs

let rec get_mod_id p = function
  | [] -> failwith "no modname with this id"
  | (x1,x2)::_ when mod_equality p x1 -> x2
  | _::xs -> get_mod_id p xs

let rec get_cmt_from_modname mn = function
  | [] -> failwith "no modname with this id"
  | (x1,x2)::_ when x2 = mn -> x1
  | _::xs -> get_cmt_from_modname mn xs


let rec update_deps p dep = function
  | [] -> failwith "no modname with this id"
  | (x1,(c,d))::xs when mod_equality p x1 -> (x1,(c,dep::d))::xs
  | x::xs -> x::(update_deps p dep xs)

let rec calc_inter_dep_mod syst = function
  | [] -> syst
  | (x1,x2)::xs ->
      begin
        match x2 with
          | Path.Pdot (p,s,i) -> 
              (* Utils.debug "@[?%s(%i)@]@." s i; *)
              (* Type constru -> -1 *)
              if (is_mod p !ident_prog_list && i <> -1)
              then 
                begin
                  let p_cnstr,p_deps = (get_deps_cnst (get_modname p) syst) in
                  let inter_dep = 
                    (get_mod_id p !ident_prog_list,id_from_cnstr i p_cnstr) in
                  let new_syst = update_deps p inter_dep syst in
                  calc_inter_dep_mod new_syst xs
                end
              else 
                calc_inter_dep_mod syst xs
          | _ -> calc_inter_dep_mod syst xs
      end
        
let calc_inter_dep syst li = 
  List.fold_left (calc_inter_dep_mod) syst li


let calc_live (fn,(c,d)) = 
  let id = get_from_ident_prog_list fn !ident_prog_list in
  let used = live id (Utils.PathSet.empty) d d in
  (* Utils.debug "@[%a : [%a]@]" Printer.print_path id Utils.print_set_path used; *)
  let cmt = get_cmt_from_modname fn !cmt_modname in
  (cmt,used)

let deps_to_live_id l =
  List.map calc_live l







