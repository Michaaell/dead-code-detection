open Cmt_format
open Typedtree

(* Set of Path *)
module PathSet = Set.Make( 
  struct
    type t = Path.t
    let compare = Pervasives.compare
  end )

(* Set of Ident *)
module IdentSet = Set.Make( 
  struct
    type t = Ident.t
    let compare = Pervasives.compare
  end )

(* Structure that representents dependence : Path * PathSet *)
module DepMap = Map.Make( 
  struct
    let compare = Pervasives.compare
    type t = Path.t
  end )

(* Tools for debugging *)
let debug_flag = ref true

let debug fmt = 
  if !debug_flag then Format.printf fmt 
  else Format.ifprintf Format.err_formatter fmt

(* Function that prints a type variant *)
let rec print_variant = function
  | [] -> ()
  | (id,_,_,_)::xs ->
      debug "%a" Ident.print id;
      print_variant xs

(* Function that prints a type record *)
let rec print_rec = function
  | [] -> ()
  | (id,_,_,_,_)::xs ->
      debug "%a" Ident.print id;
      print_rec xs  

(* Function that prints a type_desc *)
let rec print_type_desc ppf tv = match tv.typ_kind with
  | Ttype_abstract -> debug "abstract"
  | Ttype_variant l -> print_variant l
  | Ttype_record l -> print_rec l
    
(* Function that prints a PathSet *)  
let rec print_set_path ppf = 
  PathSet.iter (debug "%a " Printer.print_path)

(* Function that prints a IdentSet *)
let rec print_ids ppf = 
  IdentSet.iter (debug "%a " Ident.print)

(* Function that prints a list of dependences with the index *)
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

(* Function that prints a list of dependences *)
let rec print_graph ppf = function
  | [] -> ()
  | [(x1,x2)] -> debug "%a -> %a \n" Printer.print_path x1  Printer.print_path x2
  | (x1,x2)::xs -> 
      debug "%a -> %a,"  Printer.print_path x1  Printer.print_path x2;
      print_graph ppf xs

(* Function that prints a DepMap *)
let rec print_graph_map ppf =
  DepMap.iter (fun k e ->
    debug "@[ %a : " Printer.print_path k;
    PathSet.iter (fun x -> debug "%a " Printer.print_path x) e;
    debug "@]"
  )

(* Function that prints the index *)  
let rec print_cnst ppf = function
  | [] -> ()
  | [(x1,x2)] -> debug "%i : %a \n" x1  Printer.print_path x2
  | (x1,x2)::xs -> 
      debug "%i : %a,"  x1  Printer.print_path x2;
      print_cnst ppf xs

(* Function that prints the ast given a .cmt *)
let print_untype ppf fn = 
  let aux = function
    | Implementation strct -> 
        Pprintast.print_structure ppf (Untypeast.untype_structure strct);
    | _ -> failwith "Can't print that" in
  let cmt_inf = Cmt_format.read_cmt fn in
  aux cmt_inf.cmt_annots

(* Function that extracts the module name given a .cmt *)
let get_modname filename =
  let cmt_inf = Cmt_format.read_cmt filename in
  cmt_inf.cmt_modname

(* Function that prints the dependences of the whole project *)
let rec print_list l = 
  List.iter (fun (n,(_,d)) -> 
    debug "%s : %a\n" n print_graph d) l

(* Function that prints the index of the whole project *)
let rec print_list2 l = 
  List.iter (fun (n,(c,_)) -> 
    debug "%s : %a\n" n print_cnst c) l

(* Function that prints the DepMap of the whole project *)
let rec print_deps_map l = 
  List.iter (fun (n,(_,d)) -> 
    debug "%s : %a\n" n print_graph_map d) l
