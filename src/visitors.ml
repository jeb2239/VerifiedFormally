open Core.Std
open Cil
open Log
open Prover







class call_visitor  = object(self)
  inherit nopCilVisitor
  method vinst (i : instr) =
    let _ = match i with
      | Call(_, Lval(Var(var), _), operand, loc)  -> let operand=List.hd_exn operand  in
      Log.info "%s: Asserting precondition %s(%s)" (Log.string_of_doc (Cil.d_loc () loc)) var.vname (Log.string_of_doc (Cil.d_exp () operand))
      | _ -> ()
        
    in
    DoChildren
end

class attr_visitor(vname :string list)  = object(self)
  inherit nopCilVisitor
  method vattr (a : attribute) =
    let _ =match a with
      | Attr(_,_) ->  Log.info "Found an attribute %s" (string_of_doc (Cil.d_attr () a)) 
    in
    DoChildren
end

class attrEraserVisitor(aname:string list) = object(self)
  inherit nopCilVisitor

  method vattr (a : attribute) =
    match a with
    | Attr(s,_) when List.mem aname s -> ChangeTo []
    | _ -> DoChildren

end

let get_return_type t = match t with
TFun(t , _,_,_) -> Log.info "%s" (string_of_doc (d_type () t)); t
| _ -> failwith "fail"

class returnVisitor = object(self)
  inherit nopCilVisitor
  
  (*method vfunc (a:fundec) =
    let vi = makeLocalVar a "ret" (get_return_type a.svar.vtype)
    in
    let k a=match List.hd_exn (List.rev a.sbody.bstmts) with
    Return(_,loc) -> loc 
    | _ -> failwith "fail"
    in 
    let stm = mkStmt Return(Var(vi), k)
    in
    DoChildren*)

  method vstmt (a: stmt) = 
    let _ = match a.skind with
      | Return(Some(e),loc) -> Log.debug "%s" (string_of_doc (d_exp () e));
      | _ -> ()
      in 
      DoChildren

end

