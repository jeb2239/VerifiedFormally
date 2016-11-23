(*
Currently most of this file is from https://www.cs.virginia.edu/~weimer/615/reading/ciltut.pdf
chapter 11, it will act as a template from which we explore more of what the why3 prover has to offer
implement some of the exercises at the end of the chapter.
*)


open Core.Std
open Why3
open Cil

(* from cctut *)
type why_ops = {
    
    iplus_op : Term.lsymbol;
    iminus_op : Term.lsymbol;
    itimes_op : Term.lsymbol;
    idiv_op : Term.lsymbol;
    imod_op : Term.lsymbol;
    lt_op : Term.lsymbol;
    gt_op : Term.lsymbol;
    lte_op : Term.lsymbol;
    gte_op : Term.lsymbol;
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
}

let init_ops (it : Theory.theory) (dt : Theory.theory) (mt: Theory.theory) : why_ops =
    {
        iplus_op = Theory.ns_find_ls it.Theory.th_export ["infix +"];
        iminus_op = Theory.ns_find_ls it.Theory.th_export ["infix -"];
        itimes_op = Theory.ns_find_ls it.Theory.th_export ["infix *"];
        idiv_op     = Theory.ns_find_ls dt.Theory.th_export ["div"];
        imod_op     = Theory.ns_find_ls dt.Theory.th_export ["mod"];
        lt_op       = Theory.ns_find_ls it.Theory.th_export ["infix <"];
        gt_op       = Theory.ns_find_ls it.Theory.th_export ["infix >"];
        lte_op      = Theory.ns_find_ls it.Theory.th_export ["infix <="];
        gte_op      = Theory.ns_find_ls it.Theory.th_export ["infix >="];
        get_op      = Theory.ns_find_ls mt.Theory.th_export ["get"];
        set_op      = Theory.ns_find_ls mt.Theory.th_export ["set"];
    }

let init_why_context (p:string) (pv:string) = 

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
    {
        env = env; task=task; prover = prover; driver=driver;
        ops = init_ops int_theory div_theory arr_theory;
        memory = Term.create_vsymbol (Why3.Ident.id_fresh "M") int_arr_t;
        vars=String.Map.empty;
    }
    

let term_of_int (i:int) : Term.term =  Term.t_nat_const i

let make_symbol (s :string ) : Term.vsymbol = Term.create_vsymbol (Why3.Ident.id_fresh s) Why3.Ty.ty_int

let freshvar_of_ap (ap : attrparam) : string * Term.vsymbol = 
    match ap with
    ACons(n,[]) -> n , make_symbol n
    | _ -> Errormsg.s (Errormsg.error "Names only")




    


