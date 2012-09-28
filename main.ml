let cmt_list = ref []

let filename = ref ""

let dirname = ref ""

let print_flag = ref false

let test_flag = ref false

let elim_flag = ref false

let parse_arg_list = Str.split (Str.regexp "[ \t]+")

(* Function that recurcivly list all the .cmt in dirname *)
let rec iter_dir dirname =
  if dirname = ""
  then ()
  else
    let files = Sys.readdir dirname in
    Array.iter (fun file ->
      let file = Filename.concat dirname file in
      if (Sys.file_exists file) 
      then
        begin
          if Sys.is_directory file then iter_dir file;
          if Filename.check_suffix file ".cmt" 
          then cmt_list := file::!cmt_list
        end
    ) files
      
let usage = "usage: " ^ Sys.argv.(0) ^ " [cmt1 cmt2 cmt3 ...] [-elim cmt_file] [-print cmt_file] [-elim-project rep]"
 
let speclist = [
  (* ("-elim", Arg.String (fun s -> cmt_list := parse_arg_list s;elim_flag := true), *)
  (*  ": detect dead code in source file giving the cmt files"); *)
  ("-short", Arg.Unit (fun () -> Utils.short_flag := true),
   ": print rapport in short version");
  ("-print", Arg.String (fun s -> filename := s;print_flag := true),
   ": print the typedtree giving the cmt file");
  ("-d", Arg.String (fun s -> dirname := s; test_flag := true),
   ": detect dead code in source files giving a repositery containing cmt files");
  ]

let _ =
  Arg.parse
    speclist
    (fun x ->
      if Filename.check_suffix x ".cmt"
      then
        begin
          cmt_list := x::(!cmt_list);
          test_flag := true
        end
      else
        raise (Arg.Bad ("Bad argument : " ^ x)))
    usage;
  let fn = !filename in
  let ppf = Format.std_formatter in
  if (!elim_flag)
  then
    begin
      let syst =
        List.map (fun x -> (Utils.get_modname x,Deps.calc x)) !cmt_list in
      let used = Deps.calc_inter_live syst in
      List.iter (fun (fn,(idl,opn,args)) -> 
        ignore (Clean.soft_clean fn idl opn args)) used
    end
  else
    if (!test_flag)
    then
      begin
        iter_dir !dirname;
        let syst =
          List.map (fun x -> (Utils.get_modname x,Deps.calc x)) !cmt_list in
        Utils.debug "@.inter@.";
        let used = Deps.calc_inter_live syst in
        List.iter (fun (fn,(idl,opn,args)) -> 
          ignore (Clean.soft_clean fn idl opn args)) used
      end
    else
      Printer.dttree ppf fn















        
