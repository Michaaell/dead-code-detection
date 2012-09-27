open Cmt_format
open Typedtree
open Format

(* Fonction qui print un Path *)
let rec print_path ppf = function 
  | Path.Pident id -> (Ident.print ppf id)
  | Path.Pdot (p,s,i) -> fprintf ppf "%a.%s(%i)" print_path p s i
  | Path.Papply (p1,p2) -> fprintf ppf "%a %a" print_path p1 print_path p2 
  
let rec print_tt_expr_desc ppf = function
  | Texp_ident (path,loc,val_desc) ->
      fprintf ppf "%a" print_path path
  | Texp_constant c ->
      fprintf ppf "%a" print_constant c
  | Texp_let (rec_flag,list,e) ->
      let rec letbody = function
        |  Texp_let (rec_flag,list,e) ->
            fprintf ppf "@ @[<2>%a@]" print_patexp list;
            letbody e.exp_desc
        | expr -> expr in
      fprintf ppf "@[<2>(let@ %a]" print_patexp list;
      let expr = letbody e.exp_desc in
      fprintf ppf ")@]@ %a@]" print_tt_expr_desc expr
      (* fprintf ppf "let ([%a],%a)" print_patexp list print_tt_expr_desc e.exp_desc *)
  | Texp_function (lbl,l,part) -> print_function ppf (lbl,l,part)
  | Texp_apply (e,list) -> print_apply ppf (e,list)
  | Texp_match (e,list,part) -> 
      fprintf ppf "match@ %a with " print_tt_expr_desc e.exp_desc;
      fprintf ppf "%a" print_patexp list
  | Texp_try (e,list) -> fprintf ppf "try"
  | Texp_tuple exp_list -> 
      let aux ppf l = List.iter (fun x -> 
        fprintf ppf "@ %a" print_tt_expr_desc x.exp_desc) l in
      fprintf ppf "[%a]" aux exp_list
  | Texp_construct (path,loc,cnstr_desc,exp_list,_) -> 
      fprintf ppf "Texp_construct(%a :" print_path path;
      List.iter (fun x -> fprintf ppf "@.%a" print_tt_expr_desc x.exp_desc) exp_list;
      fprintf ppf ")"
  | Texp_variant (lbl,e_opt) -> fprintf ppf "variant"
  | Texp_record (list,e_opt) -> 
      begin 
        match e_opt with 
          | None -> fprintf ppf "{}"
          | Some e -> fprintf ppf "{S}"
      end
  | Texp_sequence (e1,e2) -> 
      fprintf ppf "%a ; %a" print_tt_expr_desc e1.exp_desc print_tt_expr_desc e2.exp_desc
  | Texp_field (e,path,loc,lbl_desc) ->
      fprintf ppf "%a.%a" print_tt_expr_desc e.exp_desc print_path path
  | Texp_when (e1,e2) ->
      fprintf 
        ppf 
        "when %a -> %a" 
        print_tt_expr_desc e1.exp_desc
        print_tt_expr_desc e2.exp_desc
  | _ -> fprintf ppf "smthg else"

and print_function ppf (lbl,arg_list,part) =
  fprintf ppf "fun %s %a" lbl print_patexp arg_list

and print_apply ppf (e,list) =
  let aux ppf = function
    | (lbl,Some e1,_) ->
        (* fprintf ppf "%s ," lbl *)
        fprintf ppf "%s %a," lbl print_tt_expr_desc e1.exp_desc
    | (lbl,None,_) ->
        fprintf ppf "%s," lbl
  in
  let pr_param ppf ll = 
    List.iter (fun l -> fprintf ppf "@ %a" aux l) ll in
  (* fprintf ppf "%a (%a)" print_tt_expr_desc e.exp_desc aux list *)
  fprintf ppf "@[<2>(apply@ %a%a)@]" print_tt_expr_desc e.exp_desc pr_param list

and print_constant ppf = function
  | Asttypes.Const_int i -> fprintf ppf "%i" i
  | Asttypes.Const_char c -> fprintf ppf "%c" c
  | Asttypes.Const_string s -> fprintf ppf "%s" s
  | Asttypes.Const_float s -> fprintf ppf "%s" s
  | Asttypes.Const_int32 i32 -> fprintf ppf"i32"
  | Asttypes.Const_int64 i64 -> fprintf ppf "i64"
  | Asttypes.Const_nativeint nativei -> fprintf ppf "nativei"

and print_pattern ppf = function
  | Tpat_any -> fprintf ppf "any"
  | Tpat_var (id,loc) -> fprintf ppf "%a" Ident.print id
  | Tpat_alias (p,kind,_) -> fprintf ppf "alias"
  | Tpat_constant cnst -> fprintf ppf "cnst"
  | Tpat_tuple pat_list -> fprintf ppf "tuple"
  | Tpat_construct (path,loc,cnstor_desc,pat_list,_) -> fprintf ppf "cnstr"
  | Tpat_variant (lbl,pat_option,row_desc) -> fprintf ppf "variant"
  | Tpat_record (list,flag) -> 
      List.iter (fun (path,_,_,pat) -> 
      fprintf ppf "%a = %a," print_path path print_pattern pat.pat_desc) list
  | Tpat_array pat_list -> fprintf ppf "array"
  | Tpat_or (pat1,pat2,row_desc_opt) -> fprintf ppf "or"
  | Tpat_lazy pat -> fprintf ppf "lazy"

and print_patexp ppf l =
  let rec aux = function
    | [] -> ()
    | [(p,e)] -> 
        fprintf 
          ppf 
          "@[<hv 1>(@[<2>%a@ %a@]" 
          print_pattern p.pat_desc 
          print_tt_expr_desc e.exp_desc;
    | (p,e)::xs ->
        fprintf 
          ppf 
          "@[<hv 1>(@[<2>%a@ %a@] and " 
          print_pattern p.pat_desc 
          print_tt_expr_desc e.exp_desc;
        aux xs
  in aux l

let rec print_core_type_desc ppf = function
  | Ttyp_any -> fprintf ppf "Ttyp_any"
  | Ttyp_var s -> fprintf ppf "Ttyp_var %s" s
  | Ttyp_arrow (lbl,_,_) -> fprintf ppf "Ttyp_var %s" lbl
  | Ttyp_tuple _ -> fprintf ppf "Ttyp_tuple"
  | Ttyp_constr (path,_,_) -> fprintf ppf "constr[%a]" print_path path
  | Ttyp_object _ -> fprintf ppf "Ttyp_object"
  | Ttyp_class (path,_,_,_) -> fprintf ppf "cl%a" print_path path
  | Ttyp_alias (_,s) -> fprintf ppf "Ttyp_alias %s" s
  | Ttyp_package _ -> fprintf ppf "Ttyp_package"
  | Ttyp_variant (_,_,_) -> fprintf ppf "Ttyp_variant"
  | Ttyp_poly (l,ct) -> fprintf ppf "%a" print_core_type ct
  

and print_core_type ppf ct =
  fprintf ppf "%a" print_core_type_desc ct.ctyp_desc

let print_type ppf (id,loc,typ_desc) = 
  let print_type_var ppf = 
    List.iter (fun (id,_,ctl,_) ->
      fprintf ppf "@ %a " Ident.print id;
      List.iter (print_core_type ppf) ctl) in
  let print_type_rec ppf = 
    List.iter (fun (id,_,_,ct,_) -> 
      fprintf ppf "@ %a:%a " Ident.print id print_core_type ct) in
  let print_type_desc ppf td = match td.typ_kind with  
    | Ttype_variant l -> fprintf ppf "%a" print_type_var l
    | Ttype_record l -> fprintf ppf "%a" print_type_rec l
    | Ttype_abstract -> fprintf ppf "abst"
  in
  fprintf ppf "type %a = %a@." Ident.print id print_type_desc typ_desc
  
let rec print_mod_expr ppf me = match me.mod_desc with
  | Tmod_ident (p, _) -> fprintf ppf "Tmod_ident (%a,_)" print_path p
  | Tmod_structure str -> fprintf ppf "Tmod_struct(%a)" print_structure_items str.str_items
  | Tmod_functor (id, _, _, me) -> 
      fprintf ppf "Tmod_fun(%a,_,%a)" Ident.print id print_mod_expr me
  | Tmod_apply (me1, me2, _) -> 
      fprintf ppf "Tmod_appl((%a,%a,_)" print_mod_expr me1  print_mod_expr me2 
  | Tmod_constraint (me, _, _, _) -> fprintf ppf "Tmod_constraint"
  | Tmod_unpack (_,_)  -> fprintf ppf "Tmod_unpack"
  
  
and print_struct_item_descr ppf = function
  | Tstr_eval e -> 
      fprintf ppf "%a@." print_tt_expr_desc e.exp_desc
  | Tstr_value (recflag, list) -> 
      fprintf ppf "@[<2>(let@ %a@]@ )@])@]@]@." print_patexp list;
  | Tstr_primitive (_, _, _) -> fprintf ppf "Tprimitive@."
  | Tstr_type l ->  List.iter (fprintf ppf "%a@." print_type) l
  | Tstr_exception (_, _, _) -> fprintf ppf "Texception@."
  | Tstr_exn_rebind (_, _, _, _) -> fprintf ppf "Texn_rebind@."
  | Tstr_module (id, _, mod_expr) -> 
      fprintf ppf "Tstr_module (%a,_,%a)@." Ident.print id print_mod_expr mod_expr
  | Tstr_recmodule _ -> fprintf ppf "Trecmodule@."
  | Tstr_modtype (_, _, _) -> fprintf ppf "Tmodtype@."
  | Tstr_open (_, _) -> fprintf ppf "Topen@."
  | Tstr_class _ -> fprintf ppf "Tclass@."
  | Tstr_class_type _ -> fprintf ppf "Tclass_type@."
  | Tstr_include (_, _) -> fprintf ppf "Tinclude@."

and print_structure_items ppf = function
  | [] -> ()
  | x::xs -> 
      print_struct_item_descr ppf x.str_desc;
      print_structure_items ppf xs
  

let print_annot ppf = function
  | Implementation strct -> 
      fprintf ppf "%a@." print_structure_items strct.str_items
  | _ -> fprintf ppf "Can't print that" 
 
let dttree ppf filename =
  let cmt_inf = Cmt_format.read_cmt filename in
  print_annot ppf cmt_inf.cmt_annots
