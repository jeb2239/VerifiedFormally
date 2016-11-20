open Core.Std
open Why3


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
    provers
    let prover_spec = {Whyconf.prover_name = p; Whyconf.prover_version = pv; Whyconf.prover_altern=""} in
    let prover = 
        try Whyconf.Mprover.find prover_spec provers
        with Not_found -> Errormsg.s (Errormsg.error "Prover %s not found." p)
    in
    let env = Why3.Env.create_env (Why3.Whyconf.loadpath main) in
    
    


