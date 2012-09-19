let cmt_list = ref []

let filename = ref ""

let dirname = ref ""

let print_flag = ref false

let test_flag = ref false

let elim_flag = ref false

let side_flag = ref false

let parse_arg_list = Str.split (Str.regexp "[ \t]+")

let rec iter_dir dirname =
  let files = Sys.readdir dirname in
  Array.iter (fun file ->
    let file = Filename.concat dirname file in
    if Sys.is_directory file then iter_dir file;
    if Filename.check_suffix file ".cmt" then cmt_list := file::!cmt_list;
  ) files

let usage = "usage: " ^ Sys.argv.(0) ^ " [-elim cmt_file] [-print cmt_file] [-elim-project rep]"
 
let speclist = [
  ("-elim", Arg.String (fun s -> cmt_list := parse_arg_list s;elim_flag := true),
   ": detect dead code in source file giving the cmt files");
  ("-print", Arg.String (fun s -> filename := s;print_flag := true),
   ": print the typedtree giving the cmt file");
  ("-elim-project", Arg.String (fun s -> dirname := s; test_flag := true),
   ": detect dead code in source files giving a repositery containing cmt files");
  ]

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
        List.map (fun x -> (Utils.get_modname x,Deps.calc x)) !cmt_list in
      let used = Deps.calc_inter_live syst in
      List.iter (fun (fn,s) -> ignore (Clean.soft_clean fn s)) used
    end
  else
    if (!test_flag)
    then
      begin
        iter_dir !dirname;
        let syst =
          List.map (fun x -> (Utils.get_modname x,Deps.calc x)) !cmt_list in
        let used = Deps.calc_inter_live syst in
        List.iter (fun (fn,s) -> ignore (Clean.soft_clean fn s)) used
      end
    else
      Printer.dttree ppf fn















        
