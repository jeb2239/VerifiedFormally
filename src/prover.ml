

open Cil
open Core.Std
open Why3
open Log
open Format
open Availexpslv
open Visitors

(*let string_of_doc = Vcc.string_of_doc*)



let string_of_task t = Format.asprintf "%a" Pretty.print_task t
let string_of_term p = Format.asprintf "%a" Pretty.print_term p

let sm_find_all (sm : 'a String.Map.t) (sl : string list) : 'a list =
  List.map sl ~f:(fun s -> String.Map.find_exn sm s)

let force_block (s : stmt) : block =
  match s.skind with
  | Block b -> b
  | _ -> Errormsg.s(Errormsg.bug "Expected block")

(* from cctut *)
type why_ops = {

  iplus_op : Term.lsymbol;
  iminus_op : Term.lsymbol;
  neg_op : Term.lsymbol;
  itimes_op : Term.lsymbol;
  idiv_op : Term.lsymbol;
  imod_op : Term.lsymbol;
  lt_op : Term.lsymbol;
  gt_op : Term.lsymbol;
  lte_op : Term.lsymbol;
  gte_op : Term.lsymbol;
  eq_op : Term.lsymbol;
  set_op : Term.lsymbol;
  get_op : Term.lsymbol;

}



(* this is the universe of our proof*)
type why_context = {
  mutable env : Env.env;
  mutable task : Task.task;
  mutable driver : Driver.driver;
  mutable ops : why_ops;
  mutable memory: Term.vsymbol;
  mutable vars :  Term.vsymbol String.Map.t;
  mutable prover : Whyconf.config_prover;
  mutable function_data : Visitors.function_metadata list;
  mutable current_fd : Cil.fundec option;
  mutable current_assumption : Term.term option; (*we update this as we run into internal function calls*)
  available_vals : Cil.exp String.Map.t;
}




let init_ops (it : Theory.theory) (dt : Theory.theory) (mt: Theory.theory) : why_ops =
  {
    iplus_op = Theory.ns_find_ls it.Theory.th_export ["infix +"];
    iminus_op = Theory.ns_find_ls it.Theory.th_export ["infix -"];
    neg_op = Theory.ns_find_ls it.Theory.th_export ["prefix -"];
    itimes_op = Theory.ns_find_ls it.Theory.th_export ["infix *"];
    idiv_op     = Theory.ns_find_ls dt.Theory.th_export ["div"];
    imod_op     = Theory.ns_find_ls dt.Theory.th_export ["mod"];
    lt_op       = Theory.ns_find_ls it.Theory.th_export ["infix <"];
    gt_op       = Theory.ns_find_ls it.Theory.th_export ["infix >"];
    lte_op      = Theory.ns_find_ls it.Theory.th_export ["infix <="];
    gte_op      = Theory.ns_find_ls it.Theory.th_export ["infix >="];
    eq_op       = Theory.ns_find_ls it.Theory.th_export ["infix ="];
    get_op      = Theory.ns_find_ls mt.Theory.th_export ["get"];
    set_op      = Theory.ns_find_ls mt.Theory.th_export ["set"];
  }

let init_why_context (p:string) (pv:string) (fdata : Visitors.function_metadata list) =
  Log.debug "just entered why_context";
  let config = Whyconf.read_config None in
  let main = Whyconf.get_main config in
  Whyconf.load_plugins main;
  let provers = Whyconf.get_provers config in
  Whyconf.Mprover.iter
    (fun k a -> Errormsg.warn "%s %s (%s)" k.Whyconf.prover_name k.Whyconf.prover_version k.Whyconf.prover_altern)
    provers;
  let prover_spec = {Whyconf.prover_name = p; Whyconf.prover_version = pv; Whyconf.prover_altern=""} in
  let prover =
    try Whyconf.Mprover.find prover_spec provers
    with Not_found -> Errormsg.s (Errormsg.error "Prover %s not found." p)
  in
  let env = Why3.Env.create_env (Why3.Whyconf.loadpath main) in
  let driver : Why3.Driver.driver =
    try Why3.Driver.load_driver env prover.Whyconf.driver []
    with e -> Errormsg.s (Errormsg.error "Failed to load driver for %s." p)
  in
  let int_theory = Why3.Env.read_theory env ["int"] "Int" in
  let div_theory = Why3.Env.read_theory env ["int"] "ComputerDivision" in
  let arr_theory = Why3.Env.read_theory env ["map"] "Map" in
  let task = List.fold_left [int_theory; div_theory; arr_theory] ~init:None ~f:Why3.Task.use_export
  in
  let arr_ts = Theory.ns_find_ts arr_theory.Theory.th_export ["map"] in
  let int_arr_t = Why3.Ty.ty_app arr_ts [Why3.Ty.ty_int; Why3.Ty.ty_int] in
  Log.debug "In why init";
  {
    env = env; task=task; prover = prover; driver=driver;
    ops = init_ops int_theory div_theory arr_theory;
    memory = Term.create_vsymbol (Why3.Ident.id_fresh "M") int_arr_t;
    vars=String.Map.empty; available_vals = String.Map.empty;
    function_data = fdata;
    current_fd = None;
    current_assumption = None;
  }


let term_of_int (i:int) : Term.term =  Term.t_nat_const i

let make_symbol (s :string ) : Term.vsymbol = Term.create_vsymbol (Why3.Ident.id_fresh s) Why3.Ty.ty_int

let freshvar_of_ap (ap : attrparam) : string * Term.vsymbol =
  match ap with
    ACons(n,[]) -> n , make_symbol n
  | _ -> Errormsg.s (Errormsg.error "Names only")



(** this is our mutually recursive function which will decode the attibutes ast*)
let rec term_of_atterparam (wc:why_context) (ap: Cil.attrparam) =
  match ap with
    AInt(i) -> term_of_int i
  | ACons(n,[]) -> Log.warn "This may raise"; Term.t_var (String.Map.find_exn wc.vars n)
  | ACons("forall", apl) -> term_of_forall wc apl
  | ACons("implies", [a ; b]) -> term_of_implies wc a b
  | AUnOp(uo,ap) -> term_of_apuop wc uo ap
  | ABinOp(bo,a1,a2) -> term_of_apbop wc bo a1 a2
  | AStar(ap) -> term_of_star wc ap
  | AIndex(base,index) -> term_of_index wc base index
  | _ -> Errormsg.s (Errormsg.error "Attrparam Is not a term %a" d_attrparam ap)

and term_of_forall wc apl =
  (*first atter*)
  let fat = apl |> List.rev |> List.hd_exn in
  let vl = apl |> List.rev |> List.tl_exn |> List.map ~f:freshvar_of_ap in
  let oldm = wc.vars in (*before mutating the current why context we snapshot the prev context map*)
  wc.vars <- List.fold_left vl ~init:oldm ~f:(fun m (n,v) -> String.Map.add  m ~key:n ~data:v) ;
  let t = term_of_atterparam wc fat in
  wc.vars <- oldm;
  Term.t_forall_close (List.map vl ~f:snd) [] t

and term_of_implies (wc: why_context) (a: attrparam) (c: attrparam) =
  let at = term_of_atterparam wc a in
  let ct = term_of_atterparam wc c in
  Term.t_implies at ct

and term_of_apuop (wc : why_context) (u: unop) (ap: attrparam) =
  let te = term_of_atterparam wc ap in
  match u with
    Cil.Neg -> Term.t_app_infer wc.ops.neg_op [te]
  | Cil.LNot -> Term.t_equ te (term_of_int 0)
  | _ -> Errormsg.s (Errormsg.error "unop : %a\n" d_attrparam ap)

and term_of_apbop (wc : why_context) (b: binop) (ap1: attrparam) (ap2: attrparam) =
  let te1 = term_of_atterparam wc ap1 in
  let te2 = term_of_atterparam wc ap2 in
  match b with
  | PlusA | PlusPI | IndexPI -> Term.t_app_infer wc.ops.iplus_op [te1; te2]
  | Mult -> Term.t_app_infer wc.ops.itimes_op [te1; te2]
  | Div  -> Term.t_app_infer wc.ops.idiv_op   [te1; te2]
  | Mod  -> Term.t_app_infer wc.ops.imod_op   [te1; te2]
  | Lt   -> Term.t_app_infer wc.ops.lt_op  [te1; te2]
  | Gt   -> Term.t_app_infer wc.ops.gt_op  [te1; te2]
  | Le   -> Term.t_app_infer wc.ops.lte_op [te1; te2]
  | Ge   -> Term.t_app_infer wc.ops.gte_op [te1; te2]
  | Eq   -> Term.t_equ te1 te2
  | Ne   -> Term.t_neq te1 te2
  | LAnd -> Term.t_and te1 te2
  | LOr  -> Term.t_or  te1 te2
  | _ -> Errormsg.s (Errormsg.error "term_of_apbop fails")
(* we are using a basic mapping to handle pointers this is unsound - we will comeback *)
(* this will not address pointer arithmatic *)
and term_of_star (wc: why_context) (a: attrparam) =
  let at = term_of_atterparam wc a in
  let mt = Term.t_var wc.memory in
  Term.t_app_infer wc.ops.get_op [mt;at]
(*pointer arith but we also need to check this*)
and term_of_index (wc:why_context) (b: attrparam) (i:attrparam) =
  let base = term_of_atterparam wc b in
  let index = term_of_atterparam wc i in
  (* we are leaving our address as an unevaluated why expression
     and add + dereff
  *)
  let address = Term.t_app_infer wc.ops.iplus_op[base;index] in
  let mt =Term.t_var wc.memory in
  Term.t_app_infer wc.ops.get_op [mt;address]


let oldvar_of_ap (wc:why_context) (ap:attrparam) =
  match ap with
  | ACons(n,[]) -> String.Map.find_exn wc.vars n
  | _ -> Errormsg.s (Errormsg.error "Names only")


let inv_of_attrs (wc : why_context) (a : attributes)
  : Term.term * Term.term * Term.vsymbol list
  =
  match filterAttributes "invar" a with
  | [Attr(_,lc :: li :: rst)] ->
    term_of_atterparam wc lc,
    term_of_atterparam wc li,
    List.map rst ~f:(oldvar_of_ap wc)
  | _ -> Errormsg.s(Errormsg.error "Malformed invariant attribute: %a" d_attrlist a)



let cond_of_function (k : string) (wc : why_context) (fd : fundec) : Term.term option =
  match filterAttributes k (typeAttrs fd.svar.vtype) with
  | [Attr(_,[ap])] -> Some(term_of_atterparam wc ap)
  | _ -> None

let post_of_function = cond_of_function "post"
let pre_of_function  = cond_of_function "pre"

let cond_of_function_meta (k:string) (wc:why_context) (fmd:function_metadata) : Term.term option =
  Log.warn "in cond_of_function_meta";
  wc.vars <-
    List.fold_left ~f:(fun m vi -> String.Map.add m ~key:vi.vname ~data:(make_symbol vi.vname))
      ~init:wc.vars (fmd.fn_sformals); (* bring inner pre condition in scope *)
  (*fmd.fn_sformals *)
  match filterAttributes k (typeAttrs fmd.fn_svar.vtype) with 
  |  [Attr(_,[ap])] -> Log.warn "Some Attr"; Some(term_of_atterparam wc ap)
  | _ -> None


let iterm_of_bterm (t : Term.term) : Term.term = Term.t_if t (term_of_int 1) (term_of_int 0)
let bterm_of_iterm (t : Term.term) : Term.term = Term.t_neq t (term_of_int 0)


let rec term_of_exp (wc : why_context) (e : exp) : Term.term =

  match e with
  | Const(CInt64(i,_,_))   -> term_of_int (Int64.to_int_exn i)
  | Lval(Var vi, NoOffset) -> (Log.debug "Lval found: %s" (Log.string_of_doc (d_exp () e))); Term.t_var (String.Map.find_exn wc.vars vi.vname)
  | Lval(Mem e, NoOffset)  ->
    let et = term_of_exp wc e in
    let mt = Term.t_var wc.memory in
    Term.t_app_infer wc.ops.get_op [mt;et]
  | SizeOf _ | SizeOfE _ | SizeOfStr _ | AlignOf _ | AlignOfE _ ->
    e |> constFold true |> term_of_exp wc
  | UnOp(uo, e, typ) -> term_of_uop wc uo e
  | BinOp(bo, e1, e2, typ) -> term_of_bop wc bo e1 e2
  | CastE(t, e) -> term_of_exp wc e
  | AddrOf _
  | StartOf _
  | _ -> Errormsg.s(Errormsg.error "term_of_exp failed: %a" d_exp e)


and iterm_of_bterm (t : Term.term) : Term.term =(printf "%a" Pretty.print_term t); Term.t_if  t (term_of_int 1) (term_of_int 0)


and bterm_of_iterm (t : Term.term) : Term.term = (printf "%a" Pretty.print_term t); Term.t_neq t (term_of_int 0)

and term_of_uop (wc : why_context) (u : unop) (e : exp) : Term.term =

  let te = term_of_exp wc e in
  match u with
  | Neg  -> Term.t_app_infer wc.ops.iminus_op [(term_of_int 0);te]
  | LNot -> iterm_of_bterm (Term.t_equ te (term_of_int 0))
  | BNot -> Errormsg.s (Errormsg.error "term_of_uop failed: ~%a\n" d_exp e)


and term_of_bop (wc : why_context) (b : binop) (e1 : exp) (e2 : exp) : Term.term =

  let te1 = term_of_exp wc e1 in
  let te2 = term_of_exp wc e2 in
  match b with
  | PlusA  | PlusPI  | IndexPI -> Term.t_app_infer wc.ops.iplus_op  [te1; te2]
  | MinusA | MinusPI | MinusPP -> Term.t_app_infer wc.ops.iminus_op [te1; te2]
  | Mult -> Term.t_app_infer wc.ops.itimes_op [te1; te2]
  | Div  -> Term.t_app_infer wc.ops.idiv_op   [te1; te2]
  | Mod  -> Term.t_app_infer wc.ops.imod_op   [te1; te2]
  | Lt   -> Term.t_app_infer wc.ops.lt_op  [te1; te2]
  | Gt   -> Term.t_app_infer wc.ops.gt_op  [te1; te2]
  | Le   -> Term.t_app_infer wc.ops.lte_op [te1; te2]
  | Ge   -> Term.t_app_infer wc.ops.gte_op [te1; te2]
  | Eq   -> Term.t_equ te1 te2
  | Ne   -> Term.t_neq te1 te2
  | LAnd -> Term.t_and te1 te2
  | LOr  -> Term.t_or  te1 te2
  | Eq -> (Log.debug "%s" (Log.string_of_doc (d_binop () b))); Term.t_equ te1 te2
  | _ -> Errormsg.s (Errormsg.error "term_of_bop failed: %a %a %a\n"
                       d_exp e1 d_binop b d_exp e2)


let vsymbols_of_function (wc : why_context) (fd : fundec) : Term.vsymbol list =
  fd.sformals
  |> List.map ~f:(fun vi -> vi.vname)
  |> sm_find_all wc.vars
  |> List.append [wc.memory]



let rec term_of_stmt (wc : why_context) (s : stmt) : Term.term -> Term.term =
  match s.skind with
  | Instr il          -> Core.Caml.List.fold_right (fun i t -> (term_of_inst wc i) t) il
  | If(e,tb,fb,loc)   -> term_of_if wc e tb fb
  | Loop(b,loc,bo,co) -> term_of_loop wc b
  | Block b           -> term_of_block wc b
  | Return(eo, loc)   -> (fun t -> t)
  | _ -> Errormsg.s(Errormsg.error "Term_of_stmt failed")

and term_of_if (wc : why_context) (e : exp) (tb : block) (fb : block) : Term.term -> Term.term =
  Log.debug "%s" (Log.string_of_doc (d_exp () e));
  let te  =  (term_of_exp wc e)   in
  let tbf = term_of_block wc tb in
  let fbf = term_of_block wc fb in
  (fun t -> Term.t_if te (tbf t) (fbf t))


and term_of_loop (wc : why_context) (b : block) : Term.term -> Term.term =
  let test, body = List.hd_exn b.bstmts, List.tl_exn b.bstmts in
  let body_block = body |> List.hd_exn |> force_block in
  let bf = term_of_block wc (mkBlock (body_block.bstmts @ (List.tl_exn body))) in
  (*if we have battrs*)
  let ct, li, lvl = inv_of_attrs wc body_block.battrs in
  let lvl' = wc.memory :: lvl in
  (fun t -> t
            |> Term.t_if ct (bf li)
            |> Term.t_implies li
            |> Term.t_forall_close lvl' []
            |> Term.t_and li)

and set_formals (wc:why_context) (sformals:Cil.varinfo list) (exp:Cil.exp list): Term.term -> Term.term = 
  Log.debug "in set_formals";
  assert ((List.length sformals) = (List.length exp));
  let assignment_pairs = List.zip_exn sformals exp in
  let let_bindings : (Term.term-> Term.term ) list =
    List.map assignment_pairs ~f:(fun (formal,e) -> set_variables wc formal e) in
  (*why does core fold right not work*)
  Core.Caml.List.fold_right (fun x y-> (x y)) let_bindings


(*List.fold let_bindings ~f:(fun a b -> (a b)) ~init:*)
(*let hd = List.hd_exn let_bindings in
  List.fold (List.tl_exn let_bindings) ~init:hd ~f:(fun x y -> (x y))*)

and set_variables (wc:why_context) (vi:Cil.varinfo) (exp:exp) :Term.term -> Term.term =
  let te = term_of_exp wc exp in 
  Log.info "This is the exp in set_variable %s" (string_of_doc (d_exp () exp));
  let vs = String.Map.find_exn wc.vars vi.vname in
  String.Map.iter_keys wc.vars ~f:(Log.warn "%s");
  Term.t_let_close vs te

and add_goal (wc:why_context) (pre:Term.term) (vi:Cil.varinfo) (term:Term.term->Term.term) = 
  String.Map.iter_keys wc.vars ~f:(Log.term "%s");
  (*|> List.map ~f:(fun vi -> vi.vname)
    |> sm_find_all wc.vars
    |> List.append [wc.memory]*)
  let vc = inline_vcgen wc (Option.value_exn ~message:"no fundec" wc.current_fd) wc.current_assumption pre in
  Log.term "%s" (string_of_term vc);
  
  let g = Decl.create_prsymbol (Ident.id_fresh "goal") in
  Log.info "Made it this far";
  let t = Task.add_prop_decl wc.task Decl.Pgoal g pre in
  Log.info "---made it this far-----";
  Log.info "%s" (string_of_task t);

  failwith "done"


(*and assign_abstract_return (wc:why_context) ()*)

and term_of_inst (wc : why_context) (i : instr) : Term.term -> Term.term =
  Log.info "in term_of_inst";
  match i with
  | Set((Var vi, NoOffset), e, loc) ->
    (*Log.debug "%s" (string_of_task wc.task);*)
    (*Log.term "%s" (string_of_task wc.task);*)
    let te = term_of_exp wc e in
    Log.info "%s" (string_of_doc  (d_exp () e));
    let vs = String.Map.find_exn wc.vars vi.vname in
    String.Map.iter_keys wc.vars ~f:(Log.debug "%s");
    Term.t_let_close vs te

  | Set((Mem me, NoOffset), e, loc) ->
    let te = term_of_exp wc e in
    let tme = term_of_exp wc me in
    let ms = wc.memory in
    let ume = Term.t_app_infer wc.ops.set_op [Term.t_var ms; tme; te] in
    String.Map.iter_keys wc.vars ~f:(Log.debug "%s");
    Term.t_let_close ms ume

  | Call(Some(Var vi, NoOffset),expr,exprs,loc) ->
    Log.term "%s" vi.vname;
    (*Log.debug "%s" (string_of_task wc.task);*)
    Log.debug "%s" (string_of_doc (d_exp () expr));
    Log.debug "%d" (List.length wc.function_data);
    Log.warn "right before calldata";
    let calldata=List.find_exn wc.function_data
        ~f:(fun x -> 
            Log.debug "%s" x.fn_svar.vname;
            x.fn_svar.vname = string_of_doc (d_exp () expr)) in
    Log.warn "after calldata";
    List.iter calldata.fn_sformals ~f:(fun x -> Log.debug "%s" x.vname);
    Log.warn "before inner pre";
    let inner_pre=cond_of_function_meta "pre" wc calldata in
    let inner_post=cond_of_function_meta "post" wc calldata in
    Log.debug "post t_cond";
    Log.debug "we make it this far-----------";
    Log.debug "%s" (string_of_term (Option.value_exn ~message:"no inner_pre" inner_pre));
    let term =set_formals wc calldata.fn_sformals exprs in
    add_goal wc (Option.value_exn ~message:"no inner_pre" inner_pre) vi term



  (*failwith "Over";*)
  (*what term to generate*)
  (*split functions into multiple goals*)
  (*when we hit a function call, we quit and call it a goal*)



  (*let cur_term_of_exp = term_of_exp wc in
    let te = term_of_exp wc expr in
    let tme = List.map exprs ~f:cur_term_of_exp in*)

  | _ -> Errormsg.s (Errormsg.error "term_of_inst: We can only handle assignment")

and term_of_block (wc : why_context) (b : block) : Term.term -> Term.term =
  Core.Caml.List.fold_right (term_of_stmt wc) b.bstmts

and inline_vcgen (wc : why_context) (fd : fundec) (pre : Term.term option) : Term.term -> Term.term =
  (fun t -> Term.t_forall_close (vsymbols_of_function wc fd) [] (inline_pre_impl_t wc fd pre t))

and inline_pre_impl_t (wc : why_context) (fd : fundec) (pre : Term.term option) : Term.term -> Term.term =
  match pre with
  | None -> term_of_block wc fd.sbody
  | Some pre -> (fun t -> Term.t_implies pre (term_of_block wc fd.sbody t))

let pre_impl_t (wc : why_context) (fd : fundec) (pre : Term.term option) : Term.term -> Term.term =
  match pre with
  | None -> term_of_block wc fd.sbody
  | Some pre -> (fun t -> Term.t_implies pre (term_of_block wc fd.sbody t))


let vcgen (wc : why_context) (fd : fundec) (pre : Term.term option) : Term.term -> Term.term =
  (fun t -> Term.t_forall_close (vsymbols_of_function wc fd) [] (pre_impl_t wc fd pre t))


let name_of_fundec (fd : fundec) = fd.svar.vname



let validateWhyCtxt (w : why_context) (p : Term.term) (fname :string) =

  Format.printf "@[validate:@ %a@]@." Pretty.print_term p;
  let g = Decl.create_prsymbol (Ident.id_fresh "goal") in
  let t = Task.add_prop_decl w.task Decl.Pgoal g p in
  Log.info "%s "(string_of_task t);
  Out_channel.write_all (fname^".why") ~data:(string_of_task t);

  Why3.Call_provers.wait_on_call
    (Why3.Driver.prove_task ~command:w.prover.command
       ~limit:{limit_time=Some(120); limit_mem=None ; limit_steps=None} w.driver t ())
    ()


(*Log.info (Format.asprintf stdout Pretty.print_task w.task);*)



let checkFunction (wc : why_context) (fname) (fd: fundec) (loc :location) :  Call_provers.prover_result option =
  wc.vars <-
    List.fold_left ~f:(fun m vi -> String.Map.add m ~key:vi.vname ~data:(make_symbol vi.vname))
      ~init:String.Map.empty (fd.slocals @ fd.sformals);
  wc.current_fd <- Some(fd);
  match post_of_function wc fd with
  | None -> None
  | Some g ->
    let pre = pre_of_function wc fd in
    let vc = vcgen wc fd pre g in
    Some(validateWhyCtxt wc vc (fname^"."^(Log.name_of_fundec fd)))

(*
Note that at the callsite for a function, we
I assert the pre-condition
I assume the post-condition
while when checking the callee we
I assume the pre-condition
I assert the post-condition
This is key for modular verification
I Breaks verification up into pieces matching function
abstraction
*)

(*let processFunction (wc : why_context) (fname) (fd : fundec) (loc : location) : unit =
  (*Availexpslv.computeAEs fd;*)
  (*Oneret.oneret fd;*)
  (** return the why_context so we can reuse it *)
  wc.vars <-
    List.fold_left ~f:(fun m vi -> String.Map.add m ~key:vi.vname ~data:(make_symbol vi.vname))
      ~init:String.Map.empty (fd.slocals @ fd.sformals);
  match post_of_function wc fd with
  | None   -> ()
  | Some g ->
    let pre = pre_of_function wc fd in
    let vc = vcgen wc fd pre g in
    validateWhyCtxt wc vc (Log.name_of_fundec fd)*)
