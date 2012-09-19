open Typedtree

(* Fonction pour printer le warning concernant un letrec inutile *)
let print_warning_letrec loc =
  Utils.debug "@[%a@] unused rec flag @." 
    Location.print loc.Asttypes.loc

(* Flag pour garder la 1ere loc d'une liste de letrec *)
let fst_letrec = ref true

(* L'ident du 1er identificateur d'une liste de letrec *)
let let_rec = ref (Utils.IdentSet.empty)

(* Loc de l'identificateur visé *)
let fst_letrec_loc = ref (Location.mknoloc "")

(* Flag pour verifier si un letrec est utilisé ou non *)
let rec_used = ref false

(* Fonction qui verifie si un path est présent dans un ensemble d'ident *)
let rec is_in_set p s = match p with
  | Path.Pident id -> Utils.IdentSet.mem id s
  | Path.Pdot (p,_,_) -> is_in_set p s
  | _ -> false

(* Fonction qui parcourt le corps de la fonction déclaré récurcive
   et cherche un appel à cette fonction *)
let rec check_rec_exp e = match e.exp_desc with
  | Texp_ident (path, _, _) ->
      if is_in_set path !let_rec
      then rec_used := true
  | Texp_constant _ -> ()
  | Texp_let (_, l, e) -> 
      List.iter (fun (_,e) -> check_rec_exp e) l;
      check_rec_exp e
  | Texp_function (_, l, _) -> List.iter (fun (_,e) -> check_rec_exp e) l
  | Texp_apply (e, list) ->
      begin 
        check_rec_exp e;
        List.iter (fun (_, e_opt, _) -> 
          match e_opt with Some e -> check_rec_exp e | None -> ()) list
      end
  | Texp_construct (_, _, _, list, _) -> List.iter check_rec_exp list
  | Texp_sequence (e1, e2) -> check_rec_exp e1;check_rec_exp e2
  | Texp_tuple list ->  List.iter check_rec_exp list
  | Texp_match (e, l, _) -> 
      begin 
        check_rec_exp e;List.iter (fun (_,e) -> check_rec_exp e) l 
      end
  | Texp_field (e, _, _, _) -> check_rec_exp e
  | Texp_record (l, e_opt) -> 
      begin
         List.iter (fun (_, _, _, e) -> check_rec_exp e) l;
        match e_opt with
          | Some e -> check_rec_exp e
          | None -> ()
      end
  | Texp_when (e1, e2) -> check_rec_exp e1;check_rec_exp e2
  | Texp_pack _ -> ()
  | Texp_object (_, _) -> () 
  | Texp_lazy e -> check_rec_exp e
  | Texp_assert e -> check_rec_exp e
  | Texp_letmodule (_, _, _, e) -> check_rec_exp e
  | Texp_override (_, l) -> List.iter (fun (_, _, e) -> check_rec_exp e) l 
  | Texp_setinstvar (_, _, _, e) -> check_rec_exp e
  | Texp_instvar (_, _, _) -> ()
  | Texp_new (_, _, _) -> ()
  | Texp_send (e0, _, e1_opt) ->  
      begin
        check_rec_exp e0;
        match e1_opt with
          | Some e -> check_rec_exp e
          | None -> ()
      end
  | Texp_for (_, _, e0, e1, _, e2) -> 
      check_rec_exp e0;check_rec_exp e1;check_rec_exp e2
  | Texp_while (e1, e2) -> check_rec_exp e1;check_rec_exp e2
  | Texp_ifthenelse (e0, e1, e2_opt) ->
      begin
        check_rec_exp e0;
        check_rec_exp e1;
        match e2_opt with
          | Some e -> check_rec_exp e
          | None -> ()
      end
  | Texp_array l -> List.iter check_rec_exp l
  | Texp_setfield (e0, _, _, _, e1) -> check_rec_exp e0;check_rec_exp e1
  | Texp_variant (_, _) -> ()
  | Texp_try (e, l) -> 
      begin
        check_rec_exp e;
        List.iter (fun (_,e) -> check_rec_exp e) l
      end
  | Texp_assertfalse -> ()

(* Fonction qui créée l'ensemble des ident qui va
   etre analysé et l'information de location pour 
   l'eventuel warning *)
let rec check_rec_pat pat = match pat.pat_desc with
  | Tpat_var (id,loc) -> 
      if !fst_letrec 
      then
        begin
          let_rec := Utils.IdentSet.add id !let_rec;
          fst_letrec_loc := loc;
          fst_letrec := false
        end
      else let_rec := Utils.IdentSet.add id !let_rec;
  | Tpat_tuple l -> List.iter check_rec_pat l
  | _ -> ()

(* Fonction pour analyser l'ensemble des ident déclaré letrec *)
let check_rec_list l =
  fst_letrec := true;
  let_rec := Utils.IdentSet.empty;
  fst_letrec_loc := Location.mknoloc "";
  rec_used := false;
  let pat_list,exp_list = List.split l in
  List.iter check_rec_pat pat_list;
  List.iter check_rec_exp exp_list;
  if not !rec_used then
    print_warning_letrec !fst_letrec_loc
