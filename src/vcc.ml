module F = Frontc
module C = Cil
module O = Vccoptions
module E = Errormsg
open Core.Std

let test1 (f:C.file) : unit =
  print_string "hello";
  List.iter ~f:(fun g -> match g with
  | C.GFun(fd,loc) -> C.dumpGlobal C.defaultCilPrinter stdout (C.GFun(fd,loc));
  | _ -> ()) f.globals


let parseOneFile (fname: string) : C.file =
  let cabs, cil = F.parse_with_cabs fname () in
  Rmtmps.removeUnusedTemps cil;
  cil

let outputFile (f : C.file) : unit =
  if !O.outFile <> "" then
    try
      let c = open_out !O.outFile in

      C.print_CIL_Input := false;
      Stats.time "printCIL"
        (C.dumpFile (!C.printerForMaincil) c !O.outFile) f;
      close_out c
    with _ ->
      E.s (E.error "Couldn't open file %s" !O.outFile)

let processOneFile (cil: C.file) : unit =
  outputFile cil

let () =

  C.print_CIL_Input := true;


  C.insertImplicitCasts := false;


  C.lineLength := 100000;


  C.warnTruncate := false;


  E.colorFlag := true;


  Cabs2cil.doCollapseCallCast := true;

  let usageMsg = "Usage: vcc [options] source-files" in
  Core.Caml.Arg.parse (O.align ()) Ciloptions.recordFile usageMsg;
  Ciloptions.fileNames := Core.Caml.List.rev !Ciloptions.fileNames;
  let files = List.map !Ciloptions.fileNames parseOneFile  in
  let one =
    match files with
    | [] -> E.s (E.error "No file names provided")
    | [o] -> o
    | _ -> Mergecil.merge files "stdout"
  in
   test1 one 
   
  (*tut1 one*)

;;



