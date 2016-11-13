open Core.Std

let test1 (f:Cil.file) : unit =
  print_string "hello";
  List.iter ~f:(fun g -> match g with
      | Cil.GFun(fd,loc) -> Cil.dumpGlobal Cil.defaultCilPrinter stdout (Cil.GFun(fd,loc));
      | _ -> ()) f.globals

let rec findFunction (gl : Cil.global list) (fname : string) : Cil.fundec =
  match gl with
  | [] -> raise(Failure "Function not found")
  | Cil.GFun(fd,_) :: _ when fd.svar.vname = fname -> fd
  | _ :: rst -> findFunction rst fname

class assignRmVisitor(vname:string)=object(self)
  inherit Cil.nopCilVisitor
  method vinst(i:Cil.instr)=
    match i with 
    |Cil.Set((Cil.Var vi,Cil.NoOffset),_,loc) when vi.vname = vname && vi.vglob -> 
      Errormsg.log "%a : Assignment Deleted %a\n" Cil.d_loc loc Cil.d_instr i;
      Cil.ChangeTo []
    |_ -> Cil.SkipChildren
end

let parseOneFile (fname: string) : Cil.file =
  let cabs, cil = Frontc.parse_with_cabs fname () in
  cil

let outputFile (f : Cil.file) : unit =
  if !Vccoptions.outFile <> "" then
    try
      let c = open_out !Vccoptions.outFile in

      Cil.print_CIL_Input := false;
      Stats.time "printCIL"
        (Cil.dumpFile (!Cil.printerForMaincil) c !Vccoptions.outFile) f;
      close_out c
    with _ ->
      Errormsg.s (Errormsg.error "Couldn't open file %s" !Vccoptions.outFile)

let processOneFile (cil: Cil.file) : unit =
  outputFile cil

let () =
  
  (*Unix.open_process "clang";*)  
  Cil.print_CIL_Input := true;
  Cil.insertImplicitCasts := false;
  Cil.lineLength := 100000;
  Cil.warnTruncate := false;
  Errormsg.colorFlag := true;
  Cabs2cil.doCollapseCallCast := true;
  Ciloptions.fileNames :=["example.c.p"];
  let files = List.map !Ciloptions.fileNames parseOneFile  in
  let one =
    match files with
    | [] -> Errormsg.s (Errormsg.error "No file names provided")
    | [o] -> o
    | _ -> Mergecil.merge files "stdout"
  in
  test1 one

;;



