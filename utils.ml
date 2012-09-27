open Cmt_format
open Typedtree
open Lexing
open Location

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

(* Flag for short rapport *)
let short_flag = ref false

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
let print_type_desc ppf tv = match tv.typ_kind with
  | Ttype_abstract -> debug "abstract"
  | Ttype_variant l -> print_variant l
  | Ttype_record l -> print_rec l
    
(* Function that prints a PathSet *)  
let print_set_path ppf = 
  PathSet.iter (debug "%a " Printer.print_path)

(* Function that prints a IdentSet *)
let print_ids ppf = 
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
let print_graph_map ppf =
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
let print_list l = 
  List.iter (fun (n,(_,d)) -> 
    debug "%s : %a\n" n print_graph d) l

(* Function that prints the index of the whole project *)
let print_list2 l = 
  List.iter (fun (n,(c,_)) -> 
    debug "%s : %a\n" n print_cnst c) l

(* Function that prints the DepMap of the whole project *)
let print_deps_map l = 
  List.iter (fun (n,(_,d)) -> 
    debug "%s : %a\n" n print_graph_map d) l

(* Function that print loc accordingly to the option *)
let print_loc ppf loc =
  if !short_flag 
  then
    begin
      let (msg_file, msg_line, msg_chars, msg_to, msg_colon) =
        ("File \"", "line ", ", characters ", "-", ":") in
      let (file, line, startchar) = get_pos_info loc.loc_start in
      let endchar = 
        loc.loc_end.Lexing.pos_cnum - loc.loc_start.Lexing.pos_cnum + startchar in
      debug"%s%i" msg_line line;
      if startchar >= 0 then
        debug "%s%i%s%i :" msg_chars startchar msg_to endchar
    end
  else
    print ppf loc 

(* Function that looks for the live idents from pstart in a DepMap *)
let rec get_alive pstart acc deps =
  if PathSet.mem pstart acc 
  then acc
  else
    if DepMap.mem pstart deps
    then
      let deps_start = DepMap.find pstart deps in
      PathSet.fold (fun x acc -> 
        let new_acc = PathSet.add x acc in get_alive x new_acc deps) deps_start acc
    else
      acc
      
let rec is_in_primi i n = function
  | [] -> false
  | (i,p)::xs -> 
      begin 
        match p with
          | Path.Pident id -> 
              if id.Ident.name = n
              then true
              else is_in_primi i n xs
          | _ -> is_in_primi i n xs
      end

let rec get_in_primi i n = function
  | [] -> failwith ("can't find primi "^string_of_int i)
  | (i,p)::xs -> 
      begin 
        match p with
          | Path.Pident id -> 
              if id.Ident.name = n
              then p
              else get_in_primi i n xs
          | _ -> get_in_primi i n xs
      end
