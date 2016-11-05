open Core.Std
open Cil

open Log

let do_compile infile_path outfile_path =
  ignore infile_path;
  ignore outfile_path;
  Log.debug "entering do_compile"

let command =
  Command.basic
    ~summary:"Verified C compiler"
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
          do_compile infile_path outfile_path;
        (* Catch any unhandled exceptions to suppress the nasty-looking message *)
        with
        | Failure(msg) | Sys_error(msg) ->
            Log.error "%s" msg; Log.debug "call stack:\n%s" (Printexc.get_backtrace ()); exit 3
    )

let _ =
  try Command.run ~version:("1.0") ~build_info:("1") command;
  with Sys_error(msg) -> Log.error "Argument error: %s" msg; exit 4
