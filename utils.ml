open Cmt_format
open Typedtree

(* Ensemble de Path *)
module PathSet = Set.Make( 
  struct
    type t = Path.t
    let compare = Pervasives.compare
  end )

(* Ensemble d'Ident *)
module IdentSet = Set.Make( 
  struct
    type t = Ident.t
    let compare = Pervasives.compare
  end )

(* Structure utilisée pour les dépendances : Path * PathSet *)
module DepMap = Map.Make( 
  struct
    let compare = Pervasives.compare
    type t = Path.t
  end )

(* Outils de debug *)
let debug_flag = ref true

let debug fmt = 
  if !debug_flag then Format.printf fmt 
  else Format.ifprintf Format.err_formatter fmt

(* Fonction pour printer un constructeur *)
let rec print_variant = function
  | [] -> ()
  | (id,_,_,_)::xs ->
      debug "%a" Ident.print id;
      print_variant xs

(* Fonction pour printer un record *)
let rec print_rec = function
  | [] -> ()
  | (id,_,_,_,_)::xs ->
      debug "%a" Ident.print id;
      print_rec xs  

(* Fonction pour printer un type_desc *)
let rec print_type_desc ppf tv = match tv.typ_kind with
  | Ttype_abstract -> debug "abstract"
  | Ttype_variant l -> print_variant l
  | Ttype_record l -> print_rec l
    
(* Fonction pour printer un PathSet *)  
let rec print_set_path ppf = 
  PathSet.iter (debug "%a " Printer.print_path)

(* Fonction pour printer une IdentSet *)
let rec print_ids ppf = 
  IdentSet.iter (debug "%a " Ident.print)

(* Fonction pour printer une liste de dependances avec les index *)
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

(* Fonction pour printer une liste de dependances *)
let rec print_graph ppf = function
  | [] -> ()
  | [(x1,x2)] -> debug "%a -> %a \n" Printer.print_path x1  Printer.print_path x2
  | (x1,x2)::xs -> 
      debug "%a -> %a,"  Printer.print_path x1  Printer.print_path x2;
      print_graph ppf xs

(* Fonction pour printer un DepMap *)
let rec print_graph_map ppf =
  DepMap.iter (fun k e ->
    debug "@[ %a : " Printer.print_path k;
    PathSet.iter (fun x -> debug "%a " Printer.print_path x) e;
    debug "@]"
  )

(* Fonction pour printer les index *)  
let rec print_cnst ppf = function
  | [] -> ()
  | [(x1,x2)] -> debug "%i : %a \n" x1  Printer.print_path x2
  | (x1,x2)::xs -> 
      debug "%i : %a,"  x1  Printer.print_path x2;
      print_cnst ppf xs

(* Fonction pour printer l'ast en prenant un .cmt *)
let print_untype ppf fn = 
  let aux = function
    | Implementation strct -> 
        Pprintast.print_structure ppf (Untypeast.untype_structure strct);
    | _ -> failwith "Can't print that" in
  let cmt_inf = Cmt_format.read_cmt fn in
  aux cmt_inf.cmt_annots

(* Fonction pour extraire le nom du module du nom du fichier .cmt *)
let get_modname filename =
  let cmt_inf = Cmt_format.read_cmt filename in
  cmt_inf.cmt_modname

(* Fonction pour printer les graph de dependance de l'ensemble du projet *)
let rec print_list l = 
  List.iter (fun (n,(_,d)) -> 
    debug "%s : %a\n" n print_graph d) l

(* Fonction pour printer les index de l'ensemble du projet *)
let rec print_list2 l = 
  List.iter (fun (n,(c,_)) -> 
    debug "%s : %a\n" n print_cnst c) l

(* Fonction pour printer les DepMap de l'ensemble du projet *)
let rec print_deps_map l = 
  List.iter (fun (n,(_,d)) -> 
    debug "%s : %a\n" n print_graph_map d) l
