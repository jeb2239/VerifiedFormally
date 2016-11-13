open Core.Std
open Cil
open Log

let test1 (f:Cil.file) : unit =
  List.iter ~f:(fun g -> match g with
      | Cil.GFun(fd,loc) -> Cil.dumpGlobal Cil.defaultCilPrinter stdout (Cil.GFun(fd,loc));
      | _ -> ()) f.globals

let do_preprocess infile_path outfile_path =
  ignore outfile_path;
  Log.debug "entering do_compile";
  let c_raw = match infile_path with
    | None -> In_channel.input_all In_channel.stdin
    | Some(path) -> In_channel.read_all path
  in
  (* Preprocess the file with clang *)
  let (from_clang, to_clang) = Unix.open_process "clang - -std=c11 -E" in
  Out_channel.output_string to_clang c_raw;
  Out_channel.close to_clang; (* clang waits for end of file *)
  let c_preprocessed = In_channel.input_all from_clang in
  if Unix.close_process (from_clang, to_clang) <> Result.Ok( () ) then
    failwith "Preprocessing failed"
  else ();
  (*generate preprocessed file*)
  let outc=Out_channel.create outfile_path in
  fprintf outc "%s\n" c_preprocessed;
  ()

let do_parse (fname: string) : Cil.file =
  let cabs, cil = Frontc.parse_with_cabs fname () in
  cil


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
          Ciloptions.fileNames :=[outfile_path];
          let files = List.map ~f:do_parse !Ciloptions.fileNames in
          let one =
          match files with
          | [] -> Errormsg.s (Errormsg.error "No file names provided")
          | [o] -> o
          | _ -> Mergecil.merge files "stdout"
          in
          test1 one;
          do_preprocess infile_path outfile_path;
          ignore (do_parse outfile_path)

        (* Catch any unhandled exceptions to suppress the nasty-looking message *)
        with
        | Failure(msg) | Sys_error(msg) ->
            Log.error "%s" msg; Log.debug "call stack:\n%s" (Printexc.get_backtrace ()); exit 3
    )

let _ =
  try Command.run ~version:("1.0") ~build_info:("1") command;
  with Sys_error(msg) -> Log.error "Argument error: %s" msg; exit 4
