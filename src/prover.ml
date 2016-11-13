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

let initOps (it : Theory.theory) (dt : Theory.theory) (mt: Theory.theory) : why_ops =
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

