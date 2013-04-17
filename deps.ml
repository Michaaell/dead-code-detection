open Cmt_format
open Typedtree
open Ident

(* Ident for the program *)
let ident_prog = ref (Path.Pident (Ident.create ""))

let ident_prog_list = ref []

let cmt_modname = ref []

let path_any = Path.Pident (Ident.create "any")

let ind = ref 0

let mod_ext = ref (Opcheck.OpenMap.empty)

let fun_arg = ref (Argcheck.ArgMap.empty)

let add_entry k e m =
  if Utils.DepMap.mem k m
  then
    let old_entry = Utils.DepMap.find k m in
    Utils.DepMap.add k (Utils.PathSet.add e old_entry) m
  else
    Utils.DepMap.add k (Utils.PathSet.singleton e) m

(******************************************************************************)

(** Fonctions pour chercher les rec inutiles *)

(* Calcul de dep *)          
          
let rec calc_dep deps_list id = function
  | Texp_ident (path,loc,val_desc) ->
      (* Utils.debug "%a ?" Printer.print_path path; *)
      mod_ext := Opcheck.set_mod_ext_used (path,loc) !mod_ext;
      let dep_id = path in
      if dep_id = id 
      then deps_list
      else add_entry id dep_id deps_list
  | Texp_constant c -> deps_list
  | Texp_let (rec_flag,list,e) ->
      let new_dep_list = calc_dep_let deps_list list in
      calc_dep new_dep_list id e.exp_desc
  | Texp_function (lbl,l,part) ->
      fun_arg := Argcheck.add_fun id !fun_arg;
      fun_arg := Argcheck.add_arg_list id l !fun_arg;
      let rec aux xs = function
        | [] -> xs
        | (p,e1)::ys ->
            let new_dep = calc_dep xs id e1.exp_desc in
            aux new_dep ys
      in (aux deps_list l)
  | Texp_apply (e,list) ->
      let calc_params deps_list = function
        | (_,Some e1,_) ->
            calc_dep deps_list id e1.exp_desc
        | (_,None,_) ->
            deps_list 
      in 
      let new_dep = List.fold_left calc_params deps_list list in
      calc_dep new_dep id e.exp_desc
  | Texp_construct (path,loc,constr_des,list,_) ->
      mod_ext := Opcheck.set_mod_ext_used (path,loc) !mod_ext;
      let dep_id = path in
      let new_dep_list = add_entry id dep_id deps_list in
      List.fold_left (fun dep_list x -> 
        calc_dep dep_list id x.exp_desc) new_dep_list list
  | Texp_sequence (e1,e2) -> 
      let new_dep = calc_dep deps_list id e1.exp_desc in
      calc_dep new_dep id e2.exp_desc
  | Texp_tuple list ->
      List.fold_left (fun dep_list e -> 
        calc_dep dep_list id e.exp_desc) deps_list list
  | Texp_match (e,l,_) | Texp_try (e, l) -> 
      let new_dep = calc_dep deps_list id e.exp_desc in
      let rec aux dep_list = function
        | [] -> dep_list
        | (p,e1)::xs -> 
            let new_dep = dep_in_patexp_case p e1 id dep_list in
            aux new_dep xs
      in aux new_dep l
  | Texp_field (e,path,loc,_) ->
      mod_ext := Opcheck.set_mod_ext_used (path,loc) !mod_ext;
      let new_dep_list = calc_dep deps_list id e.exp_desc in
      let dep_id = path in
      add_entry id dep_id new_dep_list
  | Texp_record (l,e) -> 
      begin
        match e with
          | None -> 
              List.fold_left (fun dep_list (path,loc,_,e) -> 
                mod_ext := Opcheck.set_mod_ext_used (path,loc) !mod_ext;
                calc_dep dep_list id e.exp_desc) deps_list l
          | Some e1 ->
              let new_deps =  
                List.fold_left (fun dep_list (path,loc,_,e) ->
                  mod_ext := Opcheck.set_mod_ext_used (path,loc) !mod_ext;
                  calc_dep dep_list id e.exp_desc) deps_list l in
              calc_dep new_deps id e1.exp_desc
      end
  | Texp_when (e1,e2) ->
      let new_dep_list = calc_dep deps_list id e1.exp_desc in
      calc_dep new_dep_list id e2.exp_desc
  | Texp_pack _ -> deps_list
  | Texp_object (_, _) -> deps_list
  | Texp_lazy e -> calc_dep deps_list id e.exp_desc
  | Texp_assert e -> calc_dep deps_list id e.exp_desc
  | Texp_letmodule (_, _, _, e) -> calc_dep deps_list id e.exp_desc
  | Texp_override (_, l) ->  
      List.fold_left (fun dep_list (_,_,e) -> calc_dep dep_list id e.exp_desc) deps_list l
  | Texp_setinstvar (_, _, _, e) -> calc_dep deps_list id e.exp_desc
  | Texp_instvar (_, _, _) -> deps_list 
  | Texp_new (_, _, _) -> deps_list
  | Texp_send (e0, _, e1_opt) -> calc_dep deps_list id e0.exp_desc
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
  | Texp_assertfalse -> deps_list

and calc_t_var type_env l =
  List.fold_left (fun te (id,_,ctl,_) -> 
    mod_ext := Opcheck.check_core_type_desc_list !mod_ext ctl;
    (id.Ident.name,id)::te) type_env l

and calc_t_rec type_env l =
  List.fold_left (fun te (id,_,_,ct,_) -> 
    mod_ext := Opcheck.check_core_type_desc !mod_ext ct;
    (id.Ident.name,id)::te) type_env l
    
and calc_t_env type_env l =
  List.fold_left (fun te (_,_,td) -> 
    match td.typ_kind with  
      | Ttype_variant l -> calc_t_var te l
      | Ttype_record l -> calc_t_rec te l
      | Ttype_abstract -> te
  ) type_env l

and calc_index_let index l =
  let rec get_path_from_patexp = function
    | Tpat_any -> [Path.Pident (Ident.create "any")]
    | Tpat_var (id,loc) -> [Path.Pident id]
    | Tpat_alias (p,kind,_) -> get_path_from_patexp p.pat_desc
    | Tpat_constant cnst -> failwith "cst TODO"
    | Tpat_tuple pat_list ->
        List.flatten (List.map (fun i -> get_path_from_patexp i.pat_desc) pat_list)
    | Tpat_construct (path,loc,cnstor_desc,exp_list,_) -> 
        [Path.Pident (Ident.create "any")]
    | Tpat_variant (lbl,pat_option,row_desc) -> failwith "var TODO"
    | Tpat_record (list,flag) -> [Path.Pident (Ident.create "any")]
    | Tpat_array pat_list -> [Path.Pident (Ident.create "any")]
    | Tpat_or (pat1,pat2,row_desc_opt) -> failwith "or TODO"
    | Tpat_lazy pat -> failwith "lazy TODO"
  in  
  List.fold_left 
    (fun index (x,e) ->
      let paths = get_path_from_patexp x.pat_desc in
      List.fold_left (fun acc p ->
        incr ind;(!ind-1,p)::acc) index paths) index l
    
and calc_dep_let_mod dep_list id =
  let rec aux dep_list = function
    | [] -> dep_list
    | (p,e1)::deps_list -> 
        let new_dep = dep_in_patexp_def_mod id p e1 dep_list in
        aux new_dep deps_list
  in aux dep_list

and calc_dep_let dep_list =
  let rec aux dep_list = function
    | [] -> dep_list
    | (p,e1)::deps_list -> 
        let new_dep = dep_in_patexp_def p e1 dep_list in
        aux new_dep deps_list
  in aux dep_list

and dep_in_patexp_def p e1 dep_list =
  let rec pat_aux dep_list = function
    | Tpat_any -> calc_dep dep_list path_any e1.exp_desc
    | Tpat_var (id,loc) -> calc_dep dep_list (Path.Pident id) e1.exp_desc
    | Tpat_alias (p,kind,_) -> pat_aux dep_list p.pat_desc
    | Tpat_constant cnst -> dep_list
    | Tpat_tuple pat_list -> 
        List.fold_left (fun a p ->
          pat_aux a p.pat_desc) dep_list pat_list
    | Tpat_construct (path,loc,cnstor_desc,pat_list,_) -> 
        List.fold_left (fun l i -> 
          (pat_aux l i.pat_desc)) dep_list pat_list
    | Tpat_variant (lbl,pat_option,row_desc) -> failwith "var TODO"
    | Tpat_record (list,flag) -> dep_list
    | Tpat_array pat_list -> dep_list
    | Tpat_or (pat1,pat2,row_desc_opt) -> failwith "or TODO"
    | Tpat_lazy pat -> failwith "lazy TODO"
  in pat_aux dep_list p.pat_desc

and dep_in_patexp_def_mod mod_id p e1 dep_list =
  let rec pat_aux dep_list = function
    | Tpat_any -> calc_dep dep_list path_any e1.exp_desc
    | Tpat_var (id,loc) -> 
        calc_dep 
          (add_entry mod_id (Path.Pident id) dep_list) 
          (Path.Pident id) 
          e1.exp_desc
    | Tpat_alias (p,kind,_) -> pat_aux dep_list p.pat_desc
    | Tpat_constant cnst -> dep_list
    | Tpat_tuple pat_list -> 
        List.fold_left (fun a p ->
          pat_aux a p.pat_desc) dep_list pat_list
    | Tpat_construct (path,loc,cnstor_desc,exp_list,_) -> dep_list
    | Tpat_variant (lbl,pat_option,row_desc) -> failwith "var TODO"
    | Tpat_record (list,flag) -> dep_list
    | Tpat_array pat_list -> dep_list
    | Tpat_or (pat1,pat2,row_desc_opt) -> failwith "or TODO"
    | Tpat_lazy pat -> failwith "lazy TODO"
  in pat_aux dep_list p.pat_desc

and dep_in_patexp_case p e1 id dep_list =
  let rec pat_aux id dep_list = function
    | Tpat_any -> dep_list
    | Tpat_var (id_var,_) -> add_entry (Path.Pident id_var) id dep_list
    | Tpat_alias (p,kind,_) -> pat_aux id dep_list p.pat_desc
    | Tpat_constant cnst -> dep_list
    | Tpat_tuple pat_list -> 
        List.fold_left (fun a p ->
          pat_aux id a p.pat_desc) dep_list pat_list
    | Tpat_construct (path,loc,cnstor_desc,pat_list,_) -> 
        mod_ext := Opcheck.set_mod_ext_used (path,loc) !mod_ext;
        List.fold_left (fun l i -> 
          (pat_aux id dep_list i.pat_desc)) dep_list pat_list
    | Tpat_variant (lbl,pat_option,row_desc) -> failwith "var TODO"
    | Tpat_record (list,flag) -> 
        let new_dep_list = 
          List.fold_left (fun dep_list (path,loc,_,pat) -> 
            mod_ext := Opcheck.set_mod_ext_used (path,loc) !mod_ext;
            pat_aux path dep_list pat.pat_desc) 
            dep_list list in
        calc_dep new_dep_list id e1.exp_desc
    | Tpat_array pat_list -> dep_list
    | Tpat_or (pat1,pat2,row_desc_opt) -> pat_aux id dep_list pat1.pat_desc (** TODO *)
    | Tpat_lazy pat -> failwith "lazy TODO"
  in calc_dep (pat_aux id dep_list p.pat_desc) id e1.exp_desc

let rec calc_dep_module deps_list id_mod mod_desc = match mod_desc.mod_desc with
  | Tmod_ident (p, _) -> add_entry id_mod p deps_list
  | Tmod_structure str ->
      List.fold_left (fun d tstr -> match tstr.str_desc with
        | Tstr_value (recflag,list) -> calc_dep_let_mod d id_mod list
        | _ -> d) deps_list str.str_items
  | Tmod_functor (id, _, _, me) -> 
      calc_dep_module deps_list id_mod me
  | Tmod_apply (me1, me2, _) -> 
      let new_dep = calc_dep_module deps_list id_mod me1 in
      calc_dep_module new_dep id_mod me2
  | Tmod_constraint (_, _, _, _) -> deps_list
  | Tmod_unpack (_, _) -> deps_list

let calc_struct_item_descr index type_env primi_env ident_prog deps = function
  | Tstr_eval e -> (index,type_env,primi_env,calc_dep deps ident_prog e.exp_desc)
  | Tstr_value (recflag,list) -> 
      (calc_index_let index list,type_env,primi_env,calc_dep_let deps list)
  | Tstr_type l -> (index,calc_t_env type_env l,primi_env,deps)
  | Tstr_include (_, _) -> failwith "inc todo"
  | Tstr_class_type _ -> failwith "ct todo"
  | Tstr_class _ ->  (index,type_env,primi_env,deps)
  | Tstr_open (p,lid) -> 
      mod_ext := Opcheck.add_mod_ext p lid !mod_ext;
      (index,type_env,primi_env,deps)
  | Tstr_modtype (_, _, _) -> (index,type_env,primi_env,deps)
  | Tstr_recmodule _ -> (index,type_env,primi_env,deps)
  | Tstr_module (id, _, mod_desc) ->  
      incr ind;
      ((!ind-1,Path.Pident id)::index,
       type_env,
       primi_env,
       calc_dep_module deps (Path.Pident id) mod_desc)
  | Tstr_exn_rebind (_, _, _, _) -> failwith "exnreb todo"
  | Tstr_exception (id, _, _) -> 
      incr ind;
      ((!ind-1,Path.Pident id)::index,type_env,primi_env,deps)
  | Tstr_primitive (id, _, _)   -> (index,type_env,(!ind,Path.Pident id)::primi_env,deps)
        
let calc_structure_items src list =
  ident_prog := Path.Pident (Ident.create src);
  ident_prog_list := (src,(!ident_prog))::(!ident_prog_list);
  mod_ext := Opcheck.OpenMap.empty;
  List.fold_left (fun (index,type_env,primi_env,dep) x -> 
    calc_struct_item_descr index type_env primi_env !ident_prog dep x.str_desc) 
    ([],[],[],add_entry !ident_prog path_any Utils.DepMap.empty) list

let calc_annot src = function
  | Implementation strct -> 
      let cnst,t_env,primi_env,deps = calc_structure_items src strct.str_items in
      mod_ext := Opcheck.clean_mod_ext !mod_ext;
      fun_arg := Argcheck.check_argmap !fun_arg deps;
      (cnst,t_env,primi_env,!mod_ext,!fun_arg,deps)
  | _ -> failwith "Can't print that" 
 
let merge_cnst_mli fn cnst primi =
  let ind = ref 0 in
  let cmi_inf = Cmt_format.read_cmi (fn^"i") in
  let is_in_cnst_list n =
    List.exists (fun (_,p) -> 
      match p with 
        | Path.Pident var_name -> var_name.Ident.name = n
        | _ -> false) cnst in
   let get_in_cnst_list n =
    List.find (fun (_,p) ->
      match p with 
        | Path.Pident var_name -> var_name.Ident.name = n
        | _ -> false) cnst in
   let is_in_primi_list n =
    List.exists (fun (_,p) ->
      match p with
        | Path.Pident var_name -> var_name.Ident.name = n
        | _ -> false) primi in
   let is_primi = function
     | Types.Sig_value (_,vd) -> 
         begin 
           match vd.Types.val_kind with
             | Types.Val_prim _ -> true
             | _ -> false
         end
     | _ -> false in
   let get_in_primi_list n = 
    List.find (fun (_,p) ->
      match p with
        | Path.Pident var_name -> var_name.Ident.name = n
        | _ -> false) primi in
   let get_item_name = function
    | Types.Sig_value (id,_) | Types.Sig_type (id,_,_) 
    | Types.Sig_exception  (id,_) | Types.Sig_module (id,_,_) 
    | Types.Sig_modtype  (id,_) | Types.Sig_class  (id,_,_)
    | Types.Sig_class_type  (id,_,_) -> id.Ident.name in
   (* let list_sign = List.map get_item_name cmi_inf.Cmi_format.cmi_sign in *)
   let list_val = List.filter (fun x -> 
     let n = get_item_name x in
     is_in_cnst_list n || is_in_primi_list n) cmi_inf.Cmi_format.cmi_sign in
   let list_total =
     (* List.map (fun x -> *)
     (*   let (_,p) = get_in_cnst_list x in *)
     (*   incr ind; *)
     (*   (!ind-1,p)) list_val *)      
     List.map (fun x ->
       if is_primi x
       then
         let (_,p) = get_in_primi_list (get_item_name x) in
         (0,!ind,p)
       else
         begin
           let (_,p) = get_in_cnst_list (get_item_name x) in
           incr ind;
           (1,!ind-1,p)
         end
     ) list_val in
   let primitives = List.filter (fun (i,_,_) -> i = 0) list_total and
       values     = List.filter (fun (i,_,_) -> i = 1) list_total in
   List.map (fun (_,i,p) -> (i,p)) values,
   List.map (fun (_,i,p) -> (i,p)) primitives



let calc filename  =
  (* try *)
  (* Utils.debug "calc %s @." filename; *)
    let infos = Cmt_format.read filename in
    match infos with
      | None, Some cmt_inf ->
          (** Presence d'un mli, il faut calculer les index a l'aide du .cmti*)
          ind := 0;
          cmt_modname := (filename,cmt_inf.cmt_modname)::!cmt_modname;
          let (cnst,t_env,p_env,opn,args,deps) = 
            calc_annot cmt_inf.cmt_modname cmt_inf.cmt_annots in
          let (mli_cnst,mli_primi) = merge_cnst_mli filename cnst p_env in
          (mli_cnst,t_env,mli_primi,opn,args,deps)
      | Some cmi_inf, Some cmt_inf ->
          ind := 0;
          cmt_modname := (filename,cmt_inf.cmt_modname)::!cmt_modname;
          calc_annot cmt_inf.cmt_modname cmt_inf.cmt_annots
      | _ ->  failwith ("can't calc "^filename)
  (* with Not_found -> failwith ("can't read "^filename) *)
    
let mod_equality p m = match p with
  | Path.Pident id -> id.name = m
  | _ -> false


let rec get_local_id_from_cnst i = function
  | [] -> failwith ("can't find construction "^string_of_int i)
  | (x,y)::xs when x = i -> y
  | _::xs -> get_local_id_from_cnst i xs

let rec get_local_id_from_n i n cnstr primi =
  if Utils.is_in_primi i n primi
  then Utils.get_in_primi i n primi
  else get_local_id_from_cnst i cnstr

let rec get_local_id i n cnstr primi = 
  if List.mem_assoc i primi
  then get_local_id_from_n i n cnstr primi
  else get_local_id_from_cnst i cnstr

let id_from_t_env n te = 
  List.assoc n te 
      
let rec get_from_ident_prog_list id = function
  | [] -> failwith "no id"
  | (x,y)::xs when x = id -> y
  | _::xs -> get_from_ident_prog_list id xs

let rec is_mod p = function
  | [] -> false
  | (x1,_)::_ when mod_equality p x1 -> true
  | _::xs -> is_mod p xs
      
let get_name = function
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


let rec calc_inter_dep_mod_aux syst mn mn_deps used = function
  | Path.Pdot (p,n,i) as x -> 
      begin
        (* Utils.debug "@.-> %a <-@." Printer.print_path x; *)
        if (is_mod p !ident_prog_list && i <> -1)
        then
          begin
            let p_cnstr,_,primi_env,_,_,p_deps = (get_deps_cnst (get_name p) syst) in
            let p_mn = get_mod_id p !ident_prog_list in
            (* Utils.debug "%a ?: %a @." Printer.print_path mn Printer.print_path x; *)
            let id1 = get_local_id i n p_cnstr primi_env in
            let new_used = add_entry p_mn id1 used in
            calc_inter_dep_mod syst p_mn id1 p_deps new_used
                        (* Utils.debug "%a %i" Printer.print_path p i; *)
                        (* calc_inter_dep_mod syst x m *)
          end
        else
          if (is_mod p !ident_prog_list && i = -1)
          then
            begin
              let _,t_env,_,_,_,p_deps = (get_deps_cnst (get_name p) syst) in
              let p_mn = get_mod_id p !ident_prog_list in
              (* Utils.debug "=> %a " Printer.print_path x; *)
              (* Utils.debug "in %a @." Printer.print_path p_mn; *)
              let id1 = id_from_t_env n t_env in
              let new_used = add_entry p_mn (Path.Pident id1) used in
              (* let new_used = add_entry mn x used in *)
              calc_inter_dep_mod syst mn x mn_deps new_used
            end
          else
            if Utils.DepMap.mem p mn_deps
            then calc_inter_dep_mod syst mn p mn_deps used
            else
              let new_used = add_entry mn x used in
              calc_inter_dep_mod syst mn x mn_deps new_used
      end
  | _ as x ->
      let new_used = add_entry mn x used in
      calc_inter_dep_mod syst mn x mn_deps new_used
        
and calc_inter_dep_mod syst mn id_cur mn_deps used =
  if (Utils.DepMap.mem id_cur mn_deps)
  then
    begin
      let dep_id = Utils.DepMap.find id_cur mn_deps in
      Utils.PathSet.fold (fun x acc ->
        if Utils.DepMap.mem mn used 
        then
          let mn_used = Utils.DepMap.find mn used in
          if Utils.PathSet.mem x mn_used then acc
          else calc_inter_dep_mod_aux syst mn mn_deps acc x
        else calc_inter_dep_mod_aux syst  mn mn_deps acc x
      ) dep_id used
    end
  else used
        
let calc_inter_live syst = 
  let used = 
    List.fold_left (fun used (fn,(cnst,_,_,_,_,d)) ->
      (* Utils.debug "calc inter %s @." fn; *)
      (* Utils.debug "==\n %a ==\n@." Utils.print_graph_map d; *)
      (* List.iter (fun (i,x) -> Utils.debug "%i : %a @." i Printer.print_path x) cnst; *)
      let id = get_from_ident_prog_list fn !ident_prog_list in
      calc_inter_dep_mod syst id id d used) Utils.DepMap.empty syst in
  List.map (fun (fn,(_,_,_,opn,args,_)) ->
    let id = get_from_ident_prog_list fn !ident_prog_list in
    let cmt = get_cmt_from_modname fn !cmt_modname in
    if Utils.DepMap.mem id used
    then (cmt,(Utils.DepMap.find id used,opn,args))
    else (cmt,(Utils.PathSet.empty,opn,args))
  ) syst



    
