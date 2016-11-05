module C = Cil

open Core.Std
open Vccutil


let size_t: string ref = ref ""
let outFile : string ref = ref ""
let debug : bool ref = ref false
let verbose : bool ref = ref false
let stats: bool ref = ref false
let parseFile : string ref = ref ""
let warnAsm: bool ref = ref false
let warnVararg: bool ref = ref false
let home : string ref = ref ""
let merge : bool ref = ref false

let num_tuts = 16
let enable_tut : bool ref array = Array.init num_tuts (fun i -> ref false)

let prover : string ref = ref "Alt-Ergo"
let prover_version : string ref = ref "0.94"
let tut13out : string ref = ref "callgraph.dot"
let sargs (f : 'b -> 'a -> 'c) (x : 'a) (y : 'b) : 'c = f y x
(*let options_ref = ref []*)

let options = [
  ("--prover",
   Arg.Set_string prover,
   "The prover that Why3 should use in Tut11 [default: Alt-Ergo]");
  ("--prover-version",
   Arg.Set_string prover_version,
   "The version for the prover that Why3 should use in Tut11 [default: 0.94]");
  ("--tut13-out",
   Arg.Set_string tut13out,
   "The output dot file for tut13");
  "", Arg.Unit (fun () -> ()), "General:";
  "--out", Arg.Set_string outFile, "Set the name of the output file";
  "--home", Arg.Set_string home, "Set the name of ciltut's home directory";
  "--verbose", Arg.Set verbose,
    "Enable verbose output";
  "--stats", Arg.Set stats,
    "Output optimizer execution time stats";
  "--merge", Arg.Set merge,
    "Operate in CIL merger mode";
   "--envmachine",
   Arg.Unit (fun _ ->
     try
       let machineModel = Sys.getenv_exn "CIL_MACHINE" in
       Cil.envMachine := Some (Machdepenv.modelParse machineModel);
     with
       Not_found ->
	 ignore (Errormsg.error "CIL_MACHINE environment variable is not set")
     | Failure msg ->
	 ignore (Errormsg.error "CIL_MACHINE machine model is invalid: %s" msg)),
   "Use machine model specified in CIL_MACHINE environment variable";
]

let align options =
  let options = options in

  let left = try
      options
      |> List.map ~f:fst3
      |> List.map ~f:String.length
      |> List.sort ~cmp:compare_int
      |> List.hd_exn
    with Not_found -> 0
  in

  let left = left + 4 in

  let width = 78 - left in

  let rec wrap str =
    if String.length str <= width then str else

    let break, skip =
      try let break = String.rindex_from_exn str width ' ' in
        try String.index (String.sub str 0 break) '\n', 1
        with Not_found -> Some(break), 1
      with Not_found -> Some(width), 0
    in
    let break  = match break with Some(a) -> a | _ -> raise E.Error() in
    (*let skip =match skip with Some(b) -> b | _ raise E.error() in*)

    let lstr, rstr =
      String.sub str 0 break,
      String.sub str (break + skip) (String.length str - break - skip)
    in
    lstr ^ "\n" ^ String.make left ' ' ^ wrap rstr
  in

  List.map ~f:(fun (arg, action, str) ->
    if arg = "" then arg, action, "\n" ^ str ^ "\n"
    else let pre = String.make (abs (left - String.length arg - 3)) ' ' in (*this may bite me in the butt later but it works*)
    arg, action, pre ^ wrap str)
  options





(*let _ = options_ref := options;;*)
