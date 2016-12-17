open Core.Std
open Cil
open Log
open Prover
open Visitors
open Why3
(*let string_of_doc = Pretty.sprint ~width:Int.max_value*)
 

let onlyFunctions (fn : fundec -> location -> Call_provers.prover_result option) (g : global) : unit = 
  match g with
  | GFun(f, loc) -> Log.info "%s" f.svar.vname ; ignore (fn f loc) (* this fun maps over functions*)
  | _ -> ()

let dump (f : Cil.file) : unit =
  List.iter ~f:(fun g -> match g with
      | Cil.GFun(fd,loc) -> Cil.dumpGlobal Cil.defaultCilPrinter stdout (Cil.GFun(fd,loc));
      | _ -> ()) f.globals



let eraseAttrs (f : file) : unit =
  let vis = new attrEraserVisitor ["pre";"post";"invar"] in
  ignore (visitCilFile vis  f)

let visitRets (f:file) : unit =
  let vis = new returnVisitor in 
  ignore (visitCilFile vis f)

let visit_calls (f : Cil.file) : unit =
  let vis = new attr_visitor [] in
  ignore (visitCilFile vis f)

let visit_call_site (f : Cil.file) : unit =
  let vis = new call_visitor in
  ignore (visitCilFile vis f)


let prove (f:Cil.file) (fname:string)  =
  let wc = init_why_context "Alt-Ergo" "1.01" in 
  let ls = [] in
  Cil.iterGlobals f (onlyFunctions (checkFunction wc fname))  
  
let do_preprocess infile_path =
  Log.debug "entering do_compile";
  let c_raw = (In_channel.read_all "src/cil_compat.h") ^ match infile_path with
    | None -> In_channel.input_all In_channel.stdin
    | Some(path) -> In_channel.read_all path
  in
  (* Preprocess the file with clang *)
  let (from_clang, to_clang) = Unix.open_process "clang - -std=c11 -E -P" in
  Out_channel.output_string to_clang c_raw;
  Out_channel.close to_clang; (* clang waits for end of file *)
  let c_preprocessed = In_channel.input_all from_clang in
  if Unix.close_process (from_clang, to_clang) <> Result.Ok( () ) then
    failwith "Preprocessing failed"
  else ();
  let preprocessed_path = match infile_path with
    | None -> "a.out.i"
    | Some(path) -> path ^ ".i"
  in
  Out_channel.write_all preprocessed_path ~data:c_preprocessed;
  preprocessed_path

let do_parse (fname : string) : Cil.file =
  let cil = Frontc.parse fname () in
  cil

let do_cil (fname : string) (file : Cil.file) =
  let oc = open_out (fname^".cil") in
  Cil.dumpFile Cil.defaultCilPrinter oc (fname^".cil") file

let command =
  Command.basic
    ~summary:"C prover"
    ~readme:(fun () -> "https://github.com/jeb2239/VerifiedFormally")
    Command.Spec.(
      empty
      +> flag "-c" (optional string) ~doc:"file.c compile the specified file"
      +> flag "-o" (optional_with_default "a.out" string) ~doc:"file write output to the specified file"
      +> flag "-v" no_arg ~doc:" print verbose debugging information"
      +> flag "-vv" no_arg ~doc:" print extra verbose debugging information"
    )
    ( (* Handler *)
      fun infile_path outfile_path verbose1 verbose2 () ->
        let log_level = if verbose2 then Debug else if verbose1 then Info else Warn in
        Log.set_min_level log_level;
        Log.debug "Parsed command line options:";
        Log.debug "  minimum log_level: %s" (string_of_level log_level);
        Log.debug "  compiling file (empty for stdin): %s" (match infile_path with None -> "" | Some(s) -> s);
        Log.debug "  writing executable to: %s" outfile_path;
        try
          Cil.print_CIL_Input := true;
          Cil.insertImplicitCasts := false;
          Cil.lineLength := 100000;
          Cil.warnTruncate := false;
          Errormsg.colorFlag := true;
          Cabs2cil.doCollapseCallCast := true;
          Cilutil.printStats :=true;
          Cilutil.printStages :=true;
          Cilutil.makeCFG:=true;
          let preprocessed_path = do_preprocess infile_path in
          let cil = do_parse preprocessed_path in
          (*remove unused bs*)
          Rmtmps.removeUnusedTemps cil;

          (*This will fill in the preds and succs fields of Cil.stmt*)
          Cfg.computeFileCFG cil;
          (*Partial.do_feature_partial cil;*)
          (*Deadcodeelim.dce cil;*)
          (*visit_calls cil;*)
          visit_call_site cil;
          do_cil (preprocessed_path^".notproved") cil;

          visitRets cil;
          prove cil ((Option.value_exn infile_path)^".vc");
          eraseAttrs cil;
          do_cil preprocessed_path cil;
          (* Catch any unhandled exceptions to suppress the nasty-looking message *)
        with
        | Failure(msg) | Sys_error(msg) ->
          Log.error "%s" msg; Log.debug "call stack:\n%s" (Printexc.get_backtrace ()); exit 3
    )

let _ =
  try Command.run ~version:("1.0") ~build_info:("1") command;
  with Sys_error(msg) -> Log.error "Argument error: %s" msg; exit 4
