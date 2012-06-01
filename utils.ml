open Cmt_format
open Typedtree
(* Debug *)

module PathSet = Set.Make( 
  struct
    type t = Path.t
    let compare = Pervasives.compare
  end )

module IdentSet = Set.Make( 
  struct
    type t = Ident.t
    let compare = Pervasives.compare
  end )

module DepMap = Map.Make( 
  struct
    let compare = Pervasives.compare
    type t = Path.t
  end )

let debug_flag = ref true

let debug fmt = 
  if !debug_flag then Format.printf fmt 
  else Format.ifprintf Format.err_formatter fmt


let rec print_variant = function
  | [] -> ()
  | (id,_,_,_)::xs ->
      debug "%a" Ident.print id;
      print_variant xs

let rec print_rec = function
  | [] -> ()
  | (id,_,_,_,_)::xs ->
      debug "%a" Ident.print id;
      print_rec xs  

let rec print_type_desc ppf tv = match tv.typ_kind with
  | Ttype_abstract -> debug "abstract"
  | Ttype_variant l -> print_variant l
  | Ttype_record l -> print_rec l
    
  
let rec print_set_path ppf = 
  PathSet.iter (debug "%a " Printer.print_path)

let rec print_ids ppf = 
  IdentSet.iter (debug "%a " Ident.print)


let rec print_full_graph ppf = function
  | [],[] -> ()
  | [],[(x1,x2)] -> 
      debug "%a -> %a \n" Printer.print_path x1 Printer.print_path x2
  | [],(x1,x2)::xs ->
      debug "%a -> %a," Printer.print_path x1 Printer.print_path x2;
      print_full_graph ppf ([],xs)
  | (i,id)::inds,xs -> 
      debug "@[<0>%i:%a]" i Printer.print_path id;
      print_full_graph ppf (inds,xs)

let rec print_graph ppf = function
  | [] -> ()
  | [(x1,x2)] -> debug "%a -> %a \n" Printer.print_path x1  Printer.print_path x2
  | (x1,x2)::xs -> 
      debug "%a -> %a,"  Printer.print_path x1  Printer.print_path x2;
      print_graph ppf xs

let rec print_graph_map ppf =
  DepMap.iter (fun k e ->
    debug "@[ %a : " Printer.print_path k;
    PathSet.iter (fun x -> debug "%a " Printer.print_path x) e;
    debug "@]"
  )
  

let rec print_cnst ppf = function
  | [] -> ()
  | [(x1,x2)] -> debug "%i : %a \n" x1  Printer.print_path x2
  | (x1,x2)::xs -> 
      debug "%i : %a,"  x1  Printer.print_path x2;
      print_cnst ppf xs


let print_untype ppf fn = 
  let aux = function
    | Implementation strct -> 
        Pprintast.print_structure ppf (Untypeast.untype_structure strct);
    | _ -> failwith "Can't print that" in
  let cmt_inf = Cmt_format.read_cmt fn in
  aux cmt_inf.cmt_annots


let get_modname filename =
  let cmt_inf = Cmt_format.read_cmt filename in
  cmt_inf.cmt_modname


let get_id_from_patexp_list l =
  let rec aux = function
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
  in (fun (p,_) -> aux p.pat_desc) (List.hd l)


let rec print_list l = 
  List.iter (fun (n,(_,d)) -> 
    debug "%s : %a\n" n print_graph d) l

let rec print_list2 l = 
  List.iter (fun (n,(c,_)) -> 
    debug "%s : %a\n" n print_cnst c) l


let rec print_deps_map l = 
  List.iter (fun (n,(_,d)) -> 
    debug "%s : %a\n" n print_graph_map d) l
