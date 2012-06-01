open Read

let cmt_list = ref []

let filename = ref ""

let print_flag = ref false

let test_flag = ref false

let elim_flag = ref false

let side_flag = ref false

let parse_arg_list = Str.split (Str.regexp "[ \t]+")

let usage = "usage: " ^ Sys.argv.(0) ^ " [-elim cmt_file] [-comment cmt_file] [-test cmt1 cmt2]"
 
let speclist = [
  ("-elim", Arg.String (fun s -> cmt_list := parse_arg_list s;elim_flag := true),
   ": delete dead code in source file giving the cmt file");
  ("-print", Arg.String (fun s -> filename := s;print_flag := true),
   ": print the typedtree giving the cmt file");
  ("-test", Arg.String (fun s -> cmt_list := parse_arg_list s; test_flag := true),
   ": test");
  ("-side", Arg.String (fun s -> cmt_list := parse_arg_list s; side_flag := true),
   ": detects side effect")]

let _ =
  Arg.parse
    speclist
    (fun x -> raise (Arg.Bad ("Bad argument : " ^ x)))
    usage;
  let fn = !filename in
  let ppf = Format.std_formatter in
  if (!elim_flag)
  then
    begin
      let syst = 
        List.map (fun x -> (Utils.get_modname x,calc x)) !cmt_list in
      (* Utils.print_list2 syst; *)
      (* Utils.print_list syst; *)
      let local_deps = snd (List.split (snd (List.split syst))) in
      (* Utils.print_list syst; *)
      let new_syst = calc_inter_dep syst local_deps in
      Utils.print_list2 new_syst;
      Utils.print_list new_syst;
      (* Utils.debug "OKKKK"; *)
      let used = deps_to_live_id new_syst in
      List.iter (fun (fn,s) -> ignore (Clean.soft_clean fn s)) used
    end
  else
    if (!test_flag)
    then
      begin
        let syst = 
          List.map (fun x -> (Utils.get_modname x,Deps.calc x)) !cmt_list in
        (* Utils.print_deps_map syst; *)
        (* Utils.print_list2 syst; *)
        let local_deps = snd (List.split (snd (List.split syst))) in
        let new_syst = Deps.calc_inter_dep syst local_deps in
        let used = Deps.deps_to_live_id new_syst in
        List.iter (fun (fn,s) -> ignore (Clean.soft_clean fn s)) used
      end
    else
      if !side_flag
      then
        begin 
          List.iter (Side_effect.main_side) !cmt_list
        end
      else
      Printer.dttree ppf fn
