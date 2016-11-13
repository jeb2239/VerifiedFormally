
open Cil
open Pretty
open Core.Std
module E = Errormsg
module S = Str




let i2s (i : instr) : stmt = mkStmt(Instr [i])

let v2e (v : varinfo) : exp = Lval(var v)

let (|>) (a : 'a) (f : 'a -> 'b) : 'b = f a

let fst3 (a,_,_) = a
let snd3 (_,b,_) = b
let thd3 (_,_,c) = c

let fst23 (f,s,_) = (f,s)
let snd23 (_,s,t) = (s,t)

let fst24 (f,s,_,_) = (f,s)

let tuplemap (f : 'a -> 'b) ((a,b) : ('a * 'a)) : ('b * 'b) = (f a, f b)

let triplemap (f : 'a -> 'b) ((a,b,c) : ('a * 'a * 'a)) : ('b * 'b * 'b) =
  (f a, f b, f c)

let forceOption (ao : 'a option) : 'a =
  match ao with
  | Some a -> a
  | None -> raise(Failure "forceOption")



let list_init (len : int) (f : int -> 'a) : 'a list =
	let rec helper l f r =
		if l < 0 then r
		else helper (l - 1) f ((f l) :: r)
	in
	helper (len - 1) f []

let split ?(re : string = "[ \t]+") (line : string) : string list =
  S.split (S.regexp re) line


let onlyFunctions (fn : fundec -> location -> unit) (g : global) : unit =
  match g with
  | GFun(f, loc) -> fn f loc
  | _ -> ()

let function_elements (fe : exp) : typ * (string * typ * attributes) list =
  match typeOf fe with
  | TFun(rt, Some stal, _, _) -> rt, stal
  | TFun(rt, None,      _, _) -> rt, []
  | _ -> E.s(E.bug "Expected function expression")

let fieldinfo_of_name (t: typ) (fn: string) : fieldinfo =
	match unrollType t with
	| TComp(ci, _) -> begin
		try List.find_exn ~f:(fun fi -> fi.fname = fn) ci.cfields
		with Not_found ->
			E.s (E.error "%a: Field %s not in comp %s"
				d_loc (!currentLoc) fn ci.cname)
	end
	| _ ->
		E.s (E.error "%a: Base type not a comp: %a"
			d_loc (!currentLoc) d_type t)

let force_block (s : stmt) : block =
  match s.skind with
  | Block b -> b
  | _ -> E.s(E.bug "Expected block")

let list_equal (eq : 'a -> 'a -> bool) (l1 : 'a list) (l2 : 'a list) : bool =
  let rec helper b l1 l2 =
    if not b then false else
    match l1, l2 with
    | e1 :: rst1, e2 :: rst2 ->
      helper (eq e1 e2) rst1 rst2
    | [], [] -> true
    | _, _ -> false
  in
  helper true l1 l2

let list_take (len : int) (l : 'a list) : 'a list =
  let rec helper n l res =
    match l with
    | [] -> List.rev res
    | _ :: _ when n = 0 -> List.rev res
    | x :: rst -> helper (n - 1) rst (x :: res)
  in
  helper len l []





