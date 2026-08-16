(* lib/optimize.ml *)
(*
 * 编译器优化通道，作用于 lib/ir.ml 的 TAC 中间表示：
 *
 *   1. 常量折叠（constant folding）
 *   2. 尾递归优化（tail recursion optimization）
 *   3. 死代码消除（dead code elimination）
 *   4. 循环不变式外提（loop invariant code motion）
 *)

 open Ir

 module S = Set.Make(String)
 module M = Map.Make(String)
 module IntSet = Set.Make(struct type t = int let compare = compare end)
 
 (* ---------- 通用工具 ---------- *)
 
 (* 操作数键：Temp -> "T<n>"，Var -> "V<name>"；Const 无键 *)
 let op_key = function
   | Const _ -> None
   | Temp t -> Some ("T" ^ string_of_int t)
   | Var v -> Some ("V" ^ v)
 
 (* 遍历一条 TAC 指令中的所有操作数 *)
 let iter_operands f = function
   | Assign (x, y) -> f x; f y
   | AssignBinOp (x, _, a, b) -> f x; f a; f b
   | AssignUnOp (x, _, a) -> f x; f a
   | IfGoto (a, _) | IfNotGoto (a, _) -> f a
   | Param a -> f a
   | Call (x, _, _) -> f x
   | Return (Some a) -> f a
   | Goto _ | Label _ | Return None -> ()
 
 (* 统计扁平指令序列中出现的最大 Temp 编号 + 1 *)
 let count_temps instrs =
   let m = ref (-1) in
   List.iter (iter_operands (function
     | Temp t -> if t > !m then m := t
     | _ -> ())) instrs;
   !m + 1
 
 (* 把函数展开为带 Label 的扁平指令序列 *)
 let flatten_func (f: ir_func) : tac list =
   List.concat_map (fun b -> Label b.label :: b.instrs) (f.entry :: f.blocks)
 
 (* 重新切分基本块；收缩临时变量编号；剔除不再被引用的局部变量 *)
 let rebuild_func (f: ir_func) (instrs: tac list) : ir_func =
   let blocks = match instrs with [] -> [] | _ -> split_blocks instrs in
   let entry, rest =
     match blocks with
     | e :: r -> e, r
     | [] -> { label = f.entry.label; instrs = [] }, []
   in
   let used = ref S.empty in
   List.iter (iter_operands (function
     | Var v -> used := S.add v !used
     | _ -> ())) instrs;
   let locals =
     List.filter (fun l -> List.mem l f.params || S.mem l !used) f.locals
   in
   { f with entry; blocks = rest; temps = count_temps instrs; locals }
 
 


 
 (* ---------- 常量折叠 ---------- *)
 
 (* 将结果折叠到 32 位有符号整数 *)
 let wrap32 n =
   let m = n land 0xFFFFFFFF in
   if m >= 0x80000000 then m - 0x100000000 else m
 
 let fold_binop op a b =
   match op with
   | Ast.Div | Ast.Mod when b = 0 -> None
   | _ -> Some (wrap32 (eval_binop op a b))
 
 let fold_unop op a =
   match op with
   | Ast.Pos -> Some (wrap32 a)
   | Ast.Neg -> Some (wrap32 (-a))
   | Ast.Not -> Some (if a = 0 then 1 else 0)
 
 let is_commutative = Ast.(function
   | Add | Mul | Eq | Ne | And | Or -> true
   | Sub | Div | Mod | Lt | Gt | Le | Ge -> false)
 
 let operand_repr = function
   | Const n -> "C" ^ string_of_int n
   | Temp t -> "T" ^ string_of_int t
   | Var v -> "V" ^ v
 
 let binop_repr = Ast.(function
   | Add -> "+" | Sub -> "-" | Mul -> "*" | Div -> "/" | Mod -> "%"
   | Eq -> "==" | Ne -> "!=" | Lt -> "<" | Gt -> ">" | Le -> "<=" | Ge -> ">="
   | And -> "&&" | Or -> "||")
 
 let unop_repr = Ast.(function
   | Pos -> "+" | Neg -> "-" | Not -> "!")
 
 let expr_key op a b =
   let ra = operand_repr a and rb = operand_repr b in
   let x, y =
     if is_commutative op && String.compare rb ra < 0 then rb, ra else ra, rb
   in
   "B" ^ binop_repr op ^ "(" ^ x ^ "," ^ y ^ ")"
 
 let unexpr_key op a =
   "U" ^ unop_repr op ^ "(" ^ operand_repr a ^ ")"
 
 let depends_on_key k = function
   | Const _ -> false
   | (Temp _ | Var _) as o -> op_key o = Some k
 
 let operand_is_local = function
   | Temp _ -> true
   | Var v -> String.contains v '$'
   | Const _ -> false
 
 let subst_copy env o =
   let rec go seen o =
     match op_key o with
     | None -> o
     | Some k when List.mem k seen -> o
     | Some k ->
         (match List.assoc_opt k env with
          | Some o' -> go (k :: seen) o'
          | None -> o)
   in
   go [] o
 
 let invalidate_copy d env =
   match op_key d with
   | None -> env
   | Some k ->
       List.filter
         (fun (dst, src) -> dst <> k && not (depends_on_key k src))
         env
 
 let copy_prop (instrs: tac list) : tac list =
   let env = ref [] in
   let set d s =
     match op_key d with
     | Some k when d <> s -> env := (k, s) :: List.remove_assoc k !env
     | _ -> ()
   in
   let kill d = env := invalidate_copy d !env in
   let clear () = env := [] in
   let out = ref [] in
   let emit i = out := i :: !out in
   List.iter (fun i ->
     match i with
     | Assign (d, s) ->
         let s' = subst_copy !env s in
         kill d;
         if d <> s' then (
           emit (Assign (d, s'));
           set d s')
     | AssignBinOp (d, op, a, b) ->
         let a' = subst_copy !env a and b' = subst_copy !env b in
         kill d;
         emit (AssignBinOp (d, op, a', b'))
     | AssignUnOp (d, op, a) ->
         let a' = subst_copy !env a in
         kill d;
         emit (AssignUnOp (d, op, a'))
     | IfGoto (a, l) -> emit (IfGoto (subst_copy !env a, l))
     | IfNotGoto (a, l) -> emit (IfNotGoto (subst_copy !env a, l))
     | Param a -> emit (Param (subst_copy !env a))
     | Call (d, fname, n) ->
         emit (Call (d, fname, n));
         env :=
           List.filter
             (fun (k, src) ->
               (String.length k = 0 || k.[0] <> 'V')
               && match src with
                  | Var v -> String.contains v '$'
                  | Const _ | Temp _ -> true)
             !env;
         kill d
     | Return (Some a) -> emit (Return (Some (subst_copy !env a)))
     | Label l -> emit (Label l); clear ()
     | Goto l -> emit (Goto l)
     | Return None -> emit (Return None)
   ) instrs;
   List.rev !out
 
 type available_expr = {
   ekey: string;
   result: operand;
   deps: operand list;
 }
 
 let invalidate_exprs d env =
   match op_key d with
   | None -> env
   | Some k ->
       List.filter
         (fun e ->
           op_key e.result <> Some k
           && not (List.exists (depends_on_key k) e.deps))
         env
 
 let find_expr k env =
   match List.find_opt (fun e -> e.ekey = k) env with
   | Some e -> Some e.result
   | None -> None
 
 let record_expr k d deps env =
   if operand_is_local d then { ekey = k; result = d; deps } :: List.filter (fun e -> e.ekey <> k) env
   else env
 
 let common_subexpr (instrs: tac list) : tac list =
   let env = ref [] in
   let out = ref [] in
   let emit i = out := i :: !out in
   let clear () = env := [] in
   List.iter (fun i ->
     match i with
     | Assign (d, s) ->
         env := invalidate_exprs d !env;
         if d <> s then emit i
     | AssignBinOp (d, op, a, b) ->
         env := invalidate_exprs d !env;
         let k = expr_key op a b in
         (match find_expr k !env with
          | Some prev -> emit (Assign (d, prev))
          | None ->
              emit i;
              env := record_expr k d [a; b] !env)
     | AssignUnOp (d, op, a) ->
         env := invalidate_exprs d !env;
         let k = unexpr_key op a in
         (match find_expr k !env with
          | Some prev -> emit (Assign (d, prev))
          | None ->
              emit i;
              env := record_expr k d [a] !env)
     | Call (d, fname, n) ->
         emit (Call (d, fname, n));
         clear ();
         env := invalidate_exprs d !env
     | Label l -> emit (Label l); clear ()
     | _ -> emit i
   ) instrs;
   List.rev !out
 
 let def_operand = function
   | Assign (d, _) | AssignBinOp (d, _, _, _) | AssignUnOp (d, _, _)
   | Call (d, _, _) -> Some d
   | _ -> None
 
 let substitute_operands subst = function
   | Assign (d, s) -> Assign (d, subst s)
   | AssignBinOp (d, op, a, b) -> AssignBinOp (d, op, subst a, subst b)
   | AssignUnOp (d, op, a) -> AssignUnOp (d, op, subst a)
   | IfGoto (a, l) -> IfGoto (subst a, l)
   | IfNotGoto (a, l) -> IfNotGoto (subst a, l)
   | Param a -> Param (subst a)
   | Return (Some a) -> Return (Some (subst a))
   | i -> i
 
 let single_assign_const_prop (params: string list) (instrs: tac list) : tac list =
   let defs = Hashtbl.create 32 in
   let const_defs = Hashtbl.create 32 in
   let bump k =
     let old = match Hashtbl.find_opt defs k with Some n -> n | None -> 0 in
     Hashtbl.replace defs k (old + 1)
   in
   List.iter (fun i ->
     match def_operand i with
     | Some d ->
         (match op_key d with
          | Some k ->
              bump k;
              (match i with
               | Assign (_, Const n) -> Hashtbl.replace const_defs k n
               | _ -> Hashtbl.remove const_defs k)
          | None -> ())
     | None -> ())
     instrs;
   let is_param = function Var v -> List.mem v params | _ -> false in
   let subst = function
     | (Temp _ | Var _) as o when operand_is_local o && not (is_param o) ->
         (match op_key o with
          | Some k when Hashtbl.find_opt defs k = Some 1 ->
              (match Hashtbl.find_opt const_defs k with
               | Some n -> Const n
               | None -> o)
          | _ -> o)
     | o -> o
   in
   List.map (substitute_operands subst) instrs
 
 let const_fold (instrs: tac list) : tac list =
   let env = ref [] in
   let find k = List.assoc_opt k !env in
   let set k v = env := (k, v) :: List.remove_assoc k !env in
   let drop k = env := List.remove_assoc k !env in
   let clear () = env := [] in
   let subst o =
     match op_key o with
     | Some k -> (match find k with Some n -> Const n | None -> o)
     | None -> o
   in
   let record_def d v =
     match op_key d with Some k -> set k v | None -> ()
   in
   let invalidate d =
     match op_key d with Some k -> drop k | None -> ()
   in
   let out = ref [] in
   let emit i = out := i :: !out in
   List.iter (fun i ->
     match i with
     | Assign (d, s) when d = s -> ()
     | Assign (d, s) ->
         let s' = subst s in
         (match s' with
          | Const n -> emit (Assign (d, Const n)); record_def d n
          | _ -> emit (Assign (d, s')); invalidate d)
     | AssignBinOp (d, op, a, b) ->
         let a' = subst a and b' = subst b in
         (match a', b' with
          | Const x, Const y ->
              (match fold_binop op x y with
               | Some v -> emit (Assign (d, Const v)); record_def d v
               | None -> emit (AssignBinOp (d, op, a', b')); invalidate d)
          | _ ->
              let simplified =
                match op, a', b' with
                | Ast.Add, x, Const 0 | Ast.Add, Const 0, x -> Some x
                | Ast.Sub, x, Const 0 -> Some x
                | Ast.Sub, x, y when x = y -> Some (Const 0)
                | Ast.Mul, Const 0, _ | Ast.Mul, _, Const 0 -> Some (Const 0)
                | Ast.Mul, Const 1, x | Ast.Mul, x, Const 1 -> Some x
                | Ast.Div, x, Const 1 -> Some x
                | Ast.Mod, _, Const 1 -> Some (Const 0)
                | Ast.Eq, x, y when x = y -> Some (Const 1)
                | Ast.Ne, x, y when x = y -> Some (Const 0)
                | Ast.Lt, x, y when x = y -> Some (Const 0)
                | Ast.Gt, x, y when x = y -> Some (Const 0)
                | Ast.Le, x, y when x = y -> Some (Const 1)
                | Ast.Ge, x, y when x = y -> Some (Const 1)
                | _ -> None
              in
              (match simplified with
               | Some s -> emit (Assign (d, s)); invalidate d
               | None -> emit (AssignBinOp (d, op, a', b')); invalidate d))
     | AssignUnOp (d, op, a) ->
         let a' = subst a in
         (match a' with
          | Const n ->
              (match fold_unop op n with
               | Some v -> emit (Assign (d, Const v)); record_def d v
               | None -> emit (AssignUnOp (d, op, a')); invalidate d)
          | _ -> emit (AssignUnOp (d, op, a')); invalidate d)
     | IfGoto (a, l) ->
         let a' = subst a in
         (match a' with
          | Const n -> if n <> 0 then emit (Goto l)
          | _ -> emit (IfGoto (a', l)))
     | IfNotGoto (a, l) ->
         let a' = subst a in
         (match a' with
          | Const n -> if n = 0 then emit (Goto l)
          | _ -> emit (IfNotGoto (a', l)))
     | Param a -> emit (Param (subst a))
     | Call (d, fname, n) ->
         emit (Call (d, fname, n));
         env := List.filter (fun (k, _) -> String.length k = 0 || k.[0] <> 'V') !env;
         invalidate d
     | Return (Some a) -> emit (Return (Some (subst a)))
     | Goto l -> emit (Goto l)
     | Label l -> emit (Label l); clear ()
     | Return None -> emit (Return None)
   ) instrs;
   List.rev !out
 
 let algebra_simplify (instrs: tac list) : tac list =
   List.map (function
     | AssignBinOp (d, Ast.Mul, x, Const 2)
     | AssignBinOp (d, Ast.Mul, Const 2, x) ->
         AssignBinOp (d, Ast.Add, x, x)
     | AssignBinOp (d, Ast.Mul, x, Const (-1))
     | AssignBinOp (d, Ast.Mul, Const (-1), x) ->
         AssignUnOp (d, Ast.Neg, x)
     | AssignBinOp (d, Ast.Div, Const 0, _) ->
         Assign (d, Const 0)
     | AssignBinOp (d, Ast.Mod, Const 0, _) ->
         Assign (d, Const 0)
     | AssignBinOp (d, Ast.And, Const 0, _)
     | AssignBinOp (d, Ast.And, _, Const 0) ->
         Assign (d, Const 0)
     | AssignBinOp (d, Ast.And, Const n, x) when n <> 0 ->
         Assign (d, x)
     | AssignBinOp (d, Ast.And, x, Const n) when n <> 0 ->
         Assign (d, x)
     | AssignBinOp (d, Ast.Or, Const n, _) when n <> 0 ->
         Assign (d, Const 1)
     | AssignBinOp (d, Ast.Or, _, Const n) when n <> 0 ->
         Assign (d, Const 1)
     | AssignBinOp (d, Ast.Or, Const 0, x)
     | AssignBinOp (d, Ast.Or, x, Const 0) ->
         Assign (d, x)
     | i -> i
   ) instrs

(* constant reassociation: (x + c1) + c2 -> x + (c1 + c2) (wrap32-safe) *)
let reassoc_consts (instrs: tac list) : tac list =
  let out = ref [] in
  let emit i = out := i :: !out in
  let combine pop pc op c =
    if op = pop then
      match op with
      | Ast.Add -> Some (Ast.Add, wrap32 (pc + c))
      | Ast.Sub -> Some (Ast.Sub, wrap32 (pc + c))
      | Ast.Mul -> Some (Ast.Mul, wrap32 (pc * c))
      | _ -> None
    else if op = Ast.Add && pop = Ast.Sub then Some (Ast.Add, wrap32 (c - pc))
    else if op = Ast.Sub && pop = Ast.Add then Some (Ast.Add, wrap32 (pc - c))
    else None
  in
  let prev : (string * Ast.binop * operand * int) option ref = ref None in
  List.iter (fun i ->
    match i with
    | AssignBinOp (d, op, a, Const c) ->
        let matched = ref false in
        (match !prev with
         | Some (pk, pop, px, pc) ->
             (match op_key a with
              | Some ak when ak = pk ->
                  (match combine pop pc op c with
                   | Some (nop, nc) ->
                       emit (AssignBinOp (d, nop, px, Const nc));
                       prev :=
                         (match op_key d with
                          | Some dk -> Some (dk, nop, px, nc)
                          | None -> None);
                       matched := true
                   | None -> ())
              | _ -> ())
         | None -> ());
        if not !matched then (
          emit i;
          prev :=
            match op with
            | Ast.Add | Ast.Sub | Ast.Mul ->
                (match op_key d with
                 | Some dk -> Some (dk, op, a, c)
                 | None -> None)
            | _ -> None)
    | i ->
        emit i;
        prev := None)
    instrs;
  List.rev !out
 
 (* ---------- 尾递归优化 ---------- *)
 
 let tail_recursion (f: ir_func) (instrs: tac list) : tac list =
   let fname = f.fname in
   let params = f.params in
   let nparams = List.length params in
   let entry_label = f.entry.label in
   let is_param o = match o with Var v -> List.mem v params | _ -> false in
   let tmp = ref (count_temps instrs) in
   let fresh () = let t = !tmp in incr tmp; Temp t in
   let rec loop acc = function
     | [] -> List.rev acc
     | (Param o :: rest) as instrs when nparams > 0 ->
         let rec collect k acc_ps = function
           | (Param p) :: r when k > 0 -> collect (k - 1) (p :: acc_ps) r
           | r -> List.rev acc_ps, r
         in
         let ps, after = collect nparams [] instrs in
         (match after with
          | Call (d, callee, n) :: Return (Some d') :: rest'
            when callee = fname && n = nparams
              && List.length ps = nparams && d = d' ->
              let args = List.rev ps in
              let copies =
                List.map (fun a -> if is_param a then Some (fresh ()) else None) args
              in
              let pre =
                List.concat
                  (List.map2 (fun a c ->
                     match c with Some t -> [Assign (t, a)] | None -> [])
                     args copies)
              in
              let assigns =
                List.map2 (fun p (c, a) ->
                  Assign (Var p, match c with Some t -> t | None -> a))
                  params (List.combine copies args)
              in
              loop (List.rev_append (pre @ assigns @ [Goto entry_label]) acc) rest'
          | _ -> loop (Param o :: acc) rest)
     | Call (d, callee, 0) :: Return (Some d') :: rest
       when callee = fname && nparams = 0 && d = d' ->
         loop (Goto entry_label :: acc) rest
     | i :: rest -> loop (i :: acc) rest
   in
   loop [] instrs
 
 (* ---------- 死代码消除 ---------- *)
 
 let normalize_entry (f: ir_func) (instrs: tac list) : ir_func * tac list =
   if f.entry.label <> "entry" then f, instrs
   else
     let l = fresh_label () in
     let instrs =
       match instrs with
       | Label _ :: rest -> Label l :: rest
       | _ -> Label l :: instrs
     in
     { f with entry = { f.entry with label = l } }, instrs
 
 let truncate_block (b: basic_block) : basic_block =
   let rec go acc = function
     | [] -> List.rev acc
     | ((Goto _ | Return _) as i) :: _ -> List.rev (i :: acc)
     | i :: rest -> go (i :: acc) rest
   in
   { b with instrs = go [] b.instrs }
 
 let truncate_func (f: ir_func) : ir_func =
   { f with
     entry = truncate_block f.entry;
     blocks = List.map truncate_block f.blocks }
 
 let block_succs (all: basic_block list) : int list list =
   let n = List.length all in
   let idx = Hashtbl.create 16 in
   List.iteri (fun i b -> Hashtbl.replace idx b.label i) all;
   let target l =
     match Hashtbl.find_opt idx l with Some j -> [j] | None -> []
   in
   List.mapi (fun i (b: basic_block) ->
     let next = if i + 1 < n then [i + 1] else [] in
     let targets = ref [] in
     List.iter (function
       | Goto l | IfGoto (_, l) | IfNotGoto (_, l) -> targets := l :: !targets
       | _ -> ()) b.instrs;
     let ts = List.concat_map target (List.rev !targets) in
     let terminated =
       match List.rev b.instrs with
       | (Goto _ | Return _) :: _ -> true
       | _ -> false
     in
     if terminated then ts else ts @ next) all
 
 let const_prop_cfg (f: ir_func) : ir_func =
   let all = f.entry :: f.blocks in
   let n = List.length all in
   if n = 0 then f
   else
     let succs = Array.of_list (block_succs all) in
     let preds = Array.make n [] in
     Array.iteri
       (fun i js ->
         List.iter
           (fun j ->
             if j >= 0 && j < n then preds.(j) <- i :: preds.(j))
           js)
       succs;
     let tracked = function
       | Temp _ -> true
       | Var v -> List.mem v f.params || List.mem v f.locals
       | Const _ -> false
     in
     let env_find o env =
       match op_key o with
       | Some k -> M.find_opt k env
       | None -> None
     in
     let subst env = function
       | Const _ as c -> c
       | (Temp _ | Var _) as o ->
           (match env_find o env with Some n -> Const n | None -> o)
     in
     let env_set d v env =
       match op_key d with
       | Some k when tracked d -> M.add k v env
       | _ -> env
     in
     let env_drop d env =
       match op_key d with
       | Some k when tracked d -> M.remove k env
       | _ -> env
     in
     let meet envs =
       match envs with
       | [] -> M.empty
       | first :: rest ->
           M.filter
             (fun k v -> List.for_all (fun e -> M.find_opt k e = Some v) rest)
             first
     in
     let transfer env instrs =
       let env = ref env in
       let out = ref [] in
       let emit i = out := i :: !out in
       let def_const d v =
         env := env_set d v !env;
         emit (Assign (d, Const v))
       in
       List.iter
         (fun inst ->
           match inst with
           | Assign (d, s) ->
               let s' = subst !env s in
               (match s' with
                | Const n -> def_const d n
                | _ ->
                    env := env_drop d !env;
                    if d <> s' then emit (Assign (d, s')))
           | AssignBinOp (d, op, a, b) ->
               let a' = subst !env a and b' = subst !env b in
               (match a', b' with
                | Const x, Const y ->
                    (match fold_binop op x y with
                     | Some v -> def_const d v
                     | None ->
                         env := env_drop d !env;
                         emit (AssignBinOp (d, op, a', b')))
                | _ ->
                    env := env_drop d !env;
                    emit (AssignBinOp (d, op, a', b')))
           | AssignUnOp (d, op, a) ->
               let a' = subst !env a in
               (match a' with
                | Const x ->
                    (match fold_unop op x with
                     | Some v -> def_const d v
                     | None ->
                         env := env_drop d !env;
                         emit (AssignUnOp (d, op, a')))
                | _ ->
                    env := env_drop d !env;
                    emit (AssignUnOp (d, op, a')))
           | IfGoto (a, l) ->
               (match subst !env a with
                | Const n -> if n <> 0 then emit (Goto l)
                | a' -> emit (IfGoto (a', l)))
           | IfNotGoto (a, l) ->
               (match subst !env a with
                | Const n -> if n = 0 then emit (Goto l)
                | a' -> emit (IfNotGoto (a', l)))
           | Param a ->
               emit (Param (subst !env a))
           | Call (d, callee, nargs) ->
               env := env_drop d !env;
               emit (Call (d, callee, nargs))
           | Return (Some a) ->
               emit (Return (Some (subst !env a)))
           | Goto _  | Label _ | Return None ->
               emit inst)
         instrs;
       !env, List.rev !out
     in
     let in_env = Array.make n M.empty in
     let out_env = Array.make n M.empty in
     let changed = ref true in
     while !changed do
       changed := false;
       for i = 0 to n - 1 do
         let input =
           if i = 0 then M.empty
           else meet (List.map (fun p -> out_env.(p)) preds.(i))
         in
         if not (M.equal (=) input in_env.(i)) then (
           in_env.(i) <- input;
           changed := true);
         let output, _ = transfer input (List.nth all i).instrs in
         if not (M.equal (=) output out_env.(i)) then (
           out_env.(i) <- output;
           changed := true)
       done
     done;
     let rewritten =
       List.mapi
         (fun i (b: basic_block) ->
           let _, instrs = transfer in_env.(i) b.instrs in
           { b with instrs })
         all
     in
     match rewritten with
     | entry :: blocks -> { f with entry; blocks }
     | [] -> f
 
 let remove_unreachable_blocks (f: ir_func) : ir_func =
   let all = f.entry :: f.blocks in
   let succs = Array.of_list (block_succs all) in
   let n = List.length all in
   let reachable = Array.make n false in
   let queue = Queue.create () in
   reachable.(0) <- true;
   Queue.push 0 queue;
   while not (Queue.is_empty queue) do
     let i = Queue.pop queue in
     List.iter (fun j ->
       if j >= 0 && j < n && not reachable.(j) then (
         reachable.(j) <- true;
         Queue.push j queue))
       succs.(i)
   done;
   let kept =
     List.filteri (fun i _ -> reachable.(i)) all
   in
   match kept with
   | e :: r -> { f with entry = e; blocks = r }
   | [] -> { f with entry = { label = f.entry.label; instrs = [] }; blocks = [] }
 
 let dce (f: ir_func) : ir_func =
   let all = f.entry :: f.blocks in
   let succs = Array.of_list (block_succs all) in
   let n = List.length all in
   let killable_names =
     List.fold_left (fun s v -> S.add v s) S.empty (f.params @ f.locals)
   in
   let killable = function
     | Temp _ -> true
     | Var v -> S.mem v killable_names
     | Const _ -> false
   in
   let add_use o s = match op_key o with Some k -> S.add k s | None -> s in
   let kill_def o s =
     match op_key o with
     | Some k when killable o -> S.remove k s
     | _ -> s
   in
   let uses_of = function
     | Assign (_, y) -> [y]
     | AssignBinOp (_, _, a, b) -> [a; b]
     | AssignUnOp (_, _, a) -> [a]
     | IfGoto (a, _) | IfNotGoto (a, _) -> [a]
     | Param a -> [a]
     | Return (Some a) -> [a]
     | _ -> []
   in
   let def_of = function
     | Assign (x, _) | AssignBinOp (x, _, _, _) | AssignUnOp (x, _, _)
     | Call (x, _, _) -> Some x
     | _ -> None
   in
   let use_arr =
     Array.of_list
       (List.map (fun (b: basic_block) ->
          List.fold_left (fun s i ->
            List.fold_left (fun s o -> add_use o s) s (uses_of i))
            S.empty b.instrs) all)
   in
   let kill_arr =
     Array.of_list
       (List.map (fun (b: basic_block) ->
          List.fold_left (fun s i ->
            match def_of i with
            | Some d -> kill_def d s
            | None -> s) S.empty b.instrs) all)
   in
   let live_in = Array.make n S.empty in
   let live_out = Array.make n S.empty in
   let changed = ref true in
   while !changed do
     changed := false;
     for i = n - 1 downto 0 do
       let li = S.union use_arr.(i) (S.diff live_out.(i) kill_arr.(i)) in
       if not (S.equal li live_in.(i)) then (live_in.(i) <- li; changed := true);
       let lo =
         List.fold_left (fun s j -> S.union s live_in.(j)) S.empty succs.(i)
       in
       if not (S.equal lo live_out.(i)) then (live_out.(i) <- lo; changed := true)
     done
   done;
   let rewrite (b: basic_block) i =
     let live = ref live_out.(i) in
     let instrs =
       List.fold_right (fun inst acc ->
         let keep, live' =
           match inst with
           | Assign (d, s) when d = s -> false, !live
           | Assign (d, s) ->
               let dead =
                 match op_key d with
                 | Some k when killable d -> not (S.mem k !live)
                 | _ -> false
               in
               if dead then false, !live
               else true, kill_def d (add_use s !live)
           | AssignBinOp (d, _, a, b) ->
               let dead =
                 match op_key d with
                 | Some k when killable d -> not (S.mem k !live)
                 | _ -> false
               in
               if dead then false, !live
               else true, kill_def d (add_use b (add_use a !live))
           | AssignUnOp (d, _, a) ->
               let dead =
                 match op_key d with
                 | Some k when killable d -> not (S.mem k !live)
                 | _ -> false
               in
               if dead then false, !live
               else true, kill_def d (add_use a !live)
           | IfGoto (a, _) | IfNotGoto (a, _) -> true, add_use a !live
           | Param a -> true, add_use a !live
           | Return (Some a) -> true, add_use a !live
           | Call (d, _, _) -> true, kill_def d !live
           | Goto _ | Label _ | Return None -> true, !live
         in
         live := live';
         if keep then inst :: acc else acc)
         b.instrs []
     in
     { b with instrs }
   in
   { f with
     entry = rewrite f.entry 0;
     blocks = List.mapi (fun i b -> rewrite b (i + 1)) f.blocks }
 
 let cleanup (f: ir_func) : ir_func =
   let all = f.entry :: f.blocks in
   let aliases = Hashtbl.create 16 in
   List.iter
     (fun (b: basic_block) ->
       match b.instrs with
       | [Goto l] -> Hashtbl.replace aliases b.label l
       | _ -> ())
     all;
   let rec resolve seen l =
     if List.mem l seen then l
     else
       match Hashtbl.find_opt aliases l with
       | Some l' -> resolve (l :: seen) l'
       | None -> l
   in
   let rewrite_label l = resolve [] l in
   let rewrite_jumps (b: basic_block) =
     let instrs =
       List.map
         (function
           | Goto l -> Goto (rewrite_label l)
           | IfGoto (o, l) -> IfGoto (o, rewrite_label l)
           | IfNotGoto (o, l) -> IfNotGoto (o, rewrite_label l)
           | i -> i)
         b.instrs
     in
     { b with instrs }
   in
   let all = List.map rewrite_jumps all in
   let simplify_fallthrough next_label (b: basic_block) =
     let instrs =
       match List.rev b.instrs with
       | Goto l :: rest when l = next_label ->
           List.rev rest
       | IfGoto (_, l) :: rest when l = next_label ->
           List.rev rest
       | IfNotGoto (_, l) :: rest when l = next_label ->
           List.rev rest
       | Goto g :: IfGoto (cond, l) :: rest when l = next_label ->
           List.rev (IfNotGoto (cond, g) :: rest)
       | Goto g :: IfNotGoto (cond, l) :: rest when l = next_label ->
           List.rev (IfGoto (cond, g) :: rest)
       | _ -> b.instrs
     in
     { b with instrs }
   in
   let rec go acc = function
     | [] -> List.rev acc
     | [b] -> List.rev (b :: acc)
     | (b1: basic_block) :: (((b2: basic_block) :: _) as rest) ->
         let b1' = simplify_fallthrough b2.label b1 in
         go (b1' :: acc) rest
   in
   match go [] all with
   | e :: r -> { f with entry = e; blocks = r }
   | [] -> f
 
 let merge_empty_blocks (f: ir_func) : ir_func =
   let all = f.entry :: f.blocks in
   let n = List.length all in
   let effective = Array.make n "" in
   for i = n - 1 downto 0 do
     let b = List.nth all i in
     if b.instrs = [] && i + 1 < n then effective.(i) <- effective.(i + 1)
     else effective.(i) <- b.label
   done;
   let rename = Hashtbl.create 16 in
   List.iteri (fun i (b: basic_block) ->
     if b.instrs = [] && effective.(i) <> b.label then
       Hashtbl.replace rename b.label effective.(i)) all;
   let rename_l l =
     match Hashtbl.find_opt rename l with Some l' -> l' | None -> l
   in
   let rewrite_block (b: basic_block) : basic_block =
     let instrs =
       List.map (function
         | Goto l -> Goto (rename_l l)
         | IfGoto (o, l) -> IfGoto (o, rename_l l)
         | IfNotGoto (o, l) -> IfNotGoto (o, rename_l l)
         | i -> i) b.instrs
     in
     { b with instrs }
   in
   let kept =
     List.filteri (fun i (b: basic_block) -> i = 0 || b.instrs <> []) all
     |> List.map rewrite_block
   in
   match kept with
   | e :: r -> { f with entry = e; blocks = r }
   | [] -> f
 
 let shrink_func (f: ir_func) : ir_func =
   let instrs = flatten_func f in
   let used = ref S.empty in
   List.iter (iter_operands (function
     | Var v -> used := S.add v !used
     | _ -> ())) instrs;
   let locals =
     List.filter (fun l -> List.mem l f.params || S.mem l !used) f.locals
   in
   { f with temps = count_temps instrs; locals }
 
 (* ---------- 全局常量传播 ---------- *)
 
 let global_const_prop (prog: ir_program) : ir_program =
   let globals =
     List.fold_left (fun s -> function
       | GlobalVar (name, _) -> S.add name s
       | Function _ -> s)
       S.empty prog
   in
   let candidates =
     List.fold_left (fun env -> function
       | GlobalVar (name, Some v) -> (name, v) :: env
       | GlobalVar (_, None) | Function _ -> env)
       [] prog
   in
   let assigned = ref S.empty in
   let note_def = function
     | Var v when S.mem v globals -> assigned := S.add v !assigned
     | _ -> ()
   in
   List.iter (function
     | Function f ->
         List.iter
           (fun i -> match def_operand i with Some d -> note_def d | None -> ())
           (flatten_func f)
     | GlobalVar _ -> ())
     prog;
   let env =
     List.filter (fun (name, _) -> not (S.mem name !assigned)) candidates
   in
   let subst = function
     | Var v ->
         (match List.assoc_opt v env with
          | Some n -> Const n
          | None -> Var v)
     | o -> o
   in
   let rewrite_func f =
     rebuild_func f (List.map (substitute_operands subst) (flatten_func f))
   in
   List.map (function
     | Function f -> Function (rewrite_func f)
     | GlobalVar _ as g -> g)
     prog
 
 let split_at n xs =
   let rec go n left rest =
     if n <= 0 then List.rev left, rest
     else
       match rest with
       | [] -> List.rev left, []
       | x :: xs -> go (n - 1) (x :: left) xs
   in
   go n [] xs
 
 let const_eval_program (prog: ir_program) : ir_program =
   let funcs =
     List.filter_map (function Function f -> Some (f.fname, f) | GlobalVar _ -> None) prog
   in
   let globals =
     List.fold_left (fun env -> function
       | GlobalVar (name, Some v) -> ("V" ^ name, v) :: env
       | GlobalVar (_, None) | Function _ -> env)
       [] prog
   in
   let assigned_globals =
     List.fold_left (fun s -> function
       | Function f ->
           List.fold_left (fun s i ->
             match def_operand i with
             | Some (Var v) when not (String.contains v '$') -> S.add v s
             | _ -> s)
             s (flatten_func f)
       | GlobalVar _ -> s)
       S.empty prog
   in
   let reads_globals = Hashtbl.create 16 in
   List.iter (fun (fname, f) ->
     let s = ref S.empty in
     List.iter (iter_operands (function
       | Var v when not (String.contains v '$') -> s := S.add v !s
       | _ -> ())) (flatten_func f);
     Hashtbl.replace reads_globals fname !s)
     funcs;
   let changed = ref true in
   while !changed do
     changed := false;
     List.iter (fun (fname, f) ->
       let cur = Hashtbl.find reads_globals fname in
       let next =
         List.fold_left (fun s i ->
           match i with
           | Call (_, callee, _) ->
               (match Hashtbl.find_opt reads_globals callee with
                | Some r -> S.union s r
                | None -> s)
           | _ -> s)
           cur (flatten_func f)
       in
       if not (S.equal next cur) then (
        Hashtbl.replace reads_globals fname next;
        changed := true))
      funcs
  done;
  let writes_globals = Hashtbl.create 16 in
  List.iter (fun (fname, f) ->
    let s = ref S.empty in
    List.iter (fun i ->
      match def_operand i with
      | Some (Var v) when not (String.contains v '$') -> s := S.add v !s
      | _ -> ())
      (flatten_func f);
    Hashtbl.replace writes_globals fname !s)
    funcs;
  let changed = ref true in
  while !changed do
    changed := false;
    List.iter (fun (fname, f) ->
      let cur = Hashtbl.find writes_globals fname in
      let next =
        List.fold_left (fun s i ->
          match i with
          | Call (_, callee, _) ->
              (match Hashtbl.find_opt writes_globals callee with
               | Some w -> S.union s w
               | None -> s)
          | _ -> s)
          cur (flatten_func f)
      in
      if not (S.equal next cur) then (
        Hashtbl.replace writes_globals fname next;
        changed := true))
      funcs
  done;
  let eval_memo : (string, int option) Hashtbl.t = Hashtbl.create 64 in
  let eval_budget = ref 3000000 in
  let rec eval_body fuel depth fname args =
     if fuel <= 0 || depth > 16 then None
     else
       match List.assoc_opt fname funcs with
       | None -> None
       | Some f ->
           if List.length f.params <> List.length args then None
           else
           let instrs = Array.of_list (flatten_func f) in
           let labels = Hashtbl.create 32 in
           Array.iteri (fun i -> function Label l -> Hashtbl.replace labels l i | _ -> ()) instrs;
           let env = ref globals in
           List.iter2
             (fun p v -> env := ("V" ^ p, v) :: List.remove_assoc ("V" ^ p) !env)
             f.params args;
           let args_stack = ref [] in
           let get = function
             | Const n -> Some n
             | Temp t -> List.assoc_opt ("T" ^ string_of_int t) !env
             | Var v -> List.assoc_opt ("V" ^ v) !env
           in
           let set o v =
             match op_key o with
             | Some k -> env := (k, v) :: List.remove_assoc k !env; true
             | None -> false
           in
           let local_or_temp = function
             | Temp _ -> true
             | Var v -> List.mem v f.params || List.mem v f.locals
             | Const _ -> false
           in
           let step () =
             if !eval_budget <= 0 then false
             else (decr eval_budget; true)
           in
           let rec run fuel pc =
             if fuel <= 0 || pc < 0 || pc >= Array.length instrs || not (step ()) then None
             else
               match instrs.(pc) with
               | Label _ -> run (fuel - 1) (pc + 1)
               | Assign (d, s) ->
                   if not (local_or_temp d) then None
                   else (match get s with Some v when set d v -> run (fuel - 1) (pc + 1) | _ -> None)
               | AssignBinOp (d, op, a, b) ->
                   if not (local_or_temp d) then None
                   else
                     (match get a, get b with
                      | Some x, Some y ->
                          (match fold_binop op x y with
                           | Some v when set d v -> run (fuel - 1) (pc + 1)
                           | _ -> None)
                      | _ -> None)
               | AssignUnOp (d, op, a) ->
                   if not (local_or_temp d) then None
                   else
                     (match get a with
                      | Some x ->
                          (match fold_unop op x with
                           | Some v when set d v -> run (fuel - 1) (pc + 1)
                           | _ -> None)
                      | None -> None)
               | Goto l ->
                   (match Hashtbl.find_opt labels l with
                    | Some target -> run (fuel - 1) target
                    | None -> None)
               | IfGoto (a, l) ->
                   (match get a with
                    | Some v when v <> 0 ->
                        (match Hashtbl.find_opt labels l with
                         | Some target -> run (fuel - 1) target
                         | None -> None)
                    | Some _ -> run (fuel - 1) (pc + 1)
                    | None -> None)
               | IfNotGoto (a, l) ->
                   (match get a with
                    | Some 0 ->
                        (match Hashtbl.find_opt labels l with
                         | Some target -> run (fuel - 1) target
                         | None -> None)
                    | Some _ -> run (fuel - 1) (pc + 1)
                    | None -> None)
               | Param a ->
                   (match get a with
                    | Some v -> args_stack := v :: !args_stack; run (fuel - 1) (pc + 1)
                    | None -> None)
               | Call (d, callee, nargs) ->
                   if not (local_or_temp d) then None
                   else
                     let call_args, rem = split_at nargs !args_stack in
                     args_stack := rem;
                     if List.length call_args <> nargs then None
                     else
                       (match eval_body (fuel - 1) (depth + 1) callee call_args with
                        | Some v when set d v -> run (fuel - 1) (pc + 1)
                        | _ -> None)
               | Return (Some a) -> get a
               | Return None -> Some 0
           in
           (try run fuel 0 with Invalid_argument _ -> None)
   in
   let eval_func fuel depth fname args =
     if fuel <= 0 || depth > 16 then None
     else
       match List.assoc_opt fname funcs with
       | None -> None
       | Some f ->
           if List.length f.params <> List.length args then None
           else
             let key =
               Printf.sprintf "%s|%s" fname
                 (String.concat "," (List.map string_of_int args))
             in
             match Hashtbl.find_opt eval_memo key with
             | Some res -> res
             | None ->
                 let res = eval_body fuel depth fname args in
                 Hashtbl.replace eval_memo key res;
                 res
   in
   let const_arg = function Const n -> Some n | _ -> None in
   let fold_func f =
     let rec go acc arg_stack = function
       | [] ->
           let pending = List.rev (List.map fst arg_stack) in
           rebuild_func f (List.rev (List.fold_left (fun a i -> i :: a) acc pending))
       | Param a :: rest ->
           go acc ((Param a, const_arg a) :: arg_stack) rest
       | Call (d, callee, nargs) :: rest ->
           let call_args, rem = split_at nargs arg_stack in
           let arg_vals = List.map snd call_args in
           let can_fold =
             List.length call_args = nargs
             && List.for_all (function Some _ -> true | None -> false) arg_vals
             && (match Hashtbl.find_opt reads_globals callee with
                 | Some r -> S.is_empty (S.inter r assigned_globals)
                 | None -> false)
             && (match Hashtbl.find_opt writes_globals callee with
                 | Some w -> S.is_empty w
                 | None -> true)
           in
           if can_fold then
             let vals = List.map (function Some v -> v | None -> assert false) arg_vals in
             (match eval_func 5000000 0 callee vals with
              | Some v -> go (Assign (d, Const v) :: acc) rem rest
              | None ->
                  let pending = List.rev (List.map fst call_args) in
                  let acc = List.fold_left (fun a i -> i :: a) acc pending in
                  go (Call (d, callee, nargs) :: acc) rem rest)
           else
             let pending = List.rev (List.map fst call_args) in
             let acc = List.fold_left (fun a i -> i :: a) acc pending in
             go (Call (d, callee, nargs) :: acc) rem rest
       | i :: rest ->
           let pending = List.rev (List.map fst arg_stack) in
           let acc = List.fold_left (fun a p -> p :: a) acc pending in
           go (i :: acc) [] rest
     in
     go [] [] (flatten_func f)
   in
  List.map (function
    | Function f -> Function (fold_func f)
    | GlobalVar _ as g -> g)
    prog

(* ---------- rewrite all operand positions ---------- *)

let map_all_operands map = function
  | Assign (d, s) -> Assign (map d, map s)
  | AssignBinOp (d, op, a, b) -> AssignBinOp (map d, op, map a, map b)
  | AssignUnOp (d, op, a) -> AssignUnOp (map d, op, map a)
  | IfGoto (a, l) -> IfGoto (map a, l)
  | IfNotGoto (a, l) -> IfNotGoto (map a, l)
  | Param a -> Param (map a)
  | Call (d, f, n) -> Call (map d, f, n)
  | Return (Some a) -> Return (Some (map a))
  | i -> i

(* compact temp ids to a contiguous range 0..n-1 *)
let compact_temps (instrs: tac list) : tac list =
  let mapping = Hashtbl.create 64 in
  let next = ref 0 in
  let map = function
    | Temp t ->
        (match Hashtbl.find_opt mapping t with
         | Some t' -> Temp t'
         | None ->
             let t' = !next in
             incr next;
             Hashtbl.add mapping t t';
             Temp t')
    | o -> o
  in
  List.map (map_all_operands map) instrs

(* ---------- global side-effect analysis ---------- *)

type func_analysis = {
  fa_funcs : (string, ir_func) Hashtbl.t;
  fa_assigned : S.t;
  fa_reads : (string, S.t) Hashtbl.t;
  fa_writes : (string, S.t) Hashtbl.t;
}

let is_global_var v = not (String.contains v '$')

let global_analysis (prog: ir_program) : func_analysis =
  let funcs = Hashtbl.create 16 in
  List.iter (function Function f -> Hashtbl.replace funcs f.fname f | _ -> ()) prog;
  let assigned = ref S.empty in
  List.iter (function
    | Function f ->
        List.iter (fun i ->
          match def_operand i with
          | Some (Var v) when is_global_var v -> assigned := S.add v !assigned
          | _ -> ())
          (flatten_func f)
    | GlobalVar _ -> ())
    prog;
  let reads = Hashtbl.create 16 in
  let writes = Hashtbl.create 16 in
  Hashtbl.iter (fun fname f ->
    let rs = ref S.empty in
    let ws = ref S.empty in
    List.iter (fun i ->
      iter_operands (function
        | Var v when is_global_var v -> rs := S.add v !rs
        | _ -> ()) i;
      match def_operand i with
      | Some (Var v) when is_global_var v -> ws := S.add v !ws
      | _ -> ())
      (flatten_func f);
    Hashtbl.replace reads fname !rs;
    Hashtbl.replace writes fname !ws)
    funcs;
  let changed = ref true in
  while !changed do
    changed := false;
    Hashtbl.iter (fun fname f ->
      let rs = Hashtbl.find reads fname in
      let ws = Hashtbl.find writes fname in
      let rs' = ref rs in
      let ws' = ref ws in
      List.iter (function
        | Call (_, callee, _) when Hashtbl.mem funcs callee ->
            rs' := S.union !rs' (Hashtbl.find reads callee);
            ws' := S.union !ws' (Hashtbl.find writes callee)
        | _ -> ())
        (flatten_func f);
      if not (S.equal !rs' rs) then (
        Hashtbl.replace reads fname !rs';
        changed := true);
      if not (S.equal !ws' ws) then (
        Hashtbl.replace writes fname !ws';
        changed := true))
      funcs
  done;
  { fa_funcs = funcs; fa_assigned = !assigned; fa_reads = reads; fa_writes = writes }

let split_take n xs =
  let rec go n acc rest =
    if n <= 0 then List.rev acc, rest
    else
      match rest with
      | [] -> List.rev acc, []
      | x :: xs -> go (n - 1) (x :: acc) xs
  in
  go n [] xs

(* ---------- function inlining ---------- *)

let inline_uniq = ref 1000000
let inline_temp_uniq = ref 10000000

let has_loop_blocks (all: basic_block list) : bool =
  let succs = block_succs all in
  let rec check i = function
    | [] -> false
    | j :: js -> j <= i || check i js
  in
  let rec go i = function
    | [] -> false
    | s :: ss -> check i s || go (i + 1) ss
  in
  go 0 succs

let callees_of (funcs: (string, ir_func) Hashtbl.t) (f: ir_func) : S.t =
  List.fold_left (fun s -> function
    | Call (_, callee, _) when Hashtbl.mem funcs callee -> S.add callee s
    | _ -> s)
    S.empty (flatten_func f)

let is_recursive_func (funcs: (string, ir_func) Hashtbl.t) (name: string) : bool =
  let seen = ref S.empty in
  let stack = ref (S.elements (callees_of funcs (Hashtbl.find funcs name))) in
  let rec go () =
    match !stack with
    | [] -> false
    | x :: rest ->
        stack := rest;
        if x = name then true
        else if S.mem x !seen then go ()
        else (
          seen := S.add x !seen;
          stack := S.elements (callees_of funcs (Hashtbl.find funcs x)) @ !stack;
          go ())
  in
  go ()

let inline_func (f: ir_func) (funcs: (string, ir_func) Hashtbl.t) (inlineable: (string, bool) Hashtbl.t) : ir_func * string list =
  let out = ref [] in
  let pending = ref [] in
  let added = ref [] in
  let emit i = out := i :: !out in
  let clone callee dest args =
    let body = ref [] in
    let tmap = Hashtbl.create 16 in
    let vmap = Hashtbl.create 16 in
    let lmap = Hashtbl.create 16 in
    let end_lbl = fresh_label () in
    let emitb i = body := i :: !body in
    let fresh_t t =
      match Hashtbl.find_opt tmap t with
      | Some t' -> t'
      | None ->
          let t' = !inline_temp_uniq in
          incr inline_temp_uniq;
          Hashtbl.add tmap t t';
          t'
    in
    let fresh_v v =
      match Hashtbl.find_opt vmap v with
      | Some v' -> v'
      | None ->
          let v' = Printf.sprintf "inl$%d" !inline_uniq in
          incr inline_uniq;
          Hashtbl.add vmap v v';
          added := v' :: !added;
          v'
    in
    let lbl l =
      match Hashtbl.find_opt lmap l with
      | Some l' -> l'
      | None ->
          let l' = fresh_label () in
          Hashtbl.add lmap l l';
          l'
    in
    let map_op = function
      | Temp t -> Temp (fresh_t t)
      | Var v when String.contains v '$' -> Var (fresh_v v)
      | o -> o
    in
    List.iter2
      (fun p a -> emitb (Assign (Var (fresh_v p), a)))
      callee.params args;
    List.iter (fun i ->
      match i with
      | Label l -> emitb (Label (lbl l))
      | Assign (d, s) -> emitb (Assign (map_op d, map_op s))
      | AssignBinOp (d, op, a, b) -> emitb (AssignBinOp (map_op d, op, map_op a, map_op b))
      | AssignUnOp (d, op, a) -> emitb (AssignUnOp (map_op d, op, map_op a))
      | Goto l -> emitb (Goto (lbl l))
      | IfGoto (a, l) -> emitb (IfGoto (map_op a, lbl l))
      | IfNotGoto (a, l) -> emitb (IfNotGoto (map_op a, lbl l))
      | Param a -> emitb (Param (map_op a))
      | Call (d, fname, n) -> emitb (Call (map_op d, fname, n))
      | Return None -> emitb (Assign (dest, Const 0)); emitb (Goto end_lbl)
      | Return (Some a) -> emitb (Assign (dest, map_op a)); emitb (Goto end_lbl))
      (flatten_func callee);
    emitb (Label end_lbl);
    List.rev !body
  in
  let rec go = function
    | [] ->
        List.iter (fun p -> emit (Param p)) !pending;
        (rebuild_func f (compact_temps (List.rev !out)), List.rev !added)
    | Param a :: rest ->
        pending := !pending @ [a];
        go rest
    | Call (d, callee, nargs) :: rest ->
        let can_inline =
          Hashtbl.mem funcs callee
          && (match Hashtbl.find_opt inlineable callee with Some true -> true | _ -> false)
          && List.length !pending >= nargs
          && List.length !out < 2000
        in
        if can_inline then (
          let m = List.length !pending in
          let front, lastn = split_take (m - nargs) !pending in
          pending := front;
          let args = List.rev lastn in
          let callee_f = Hashtbl.find funcs callee in
          if List.length callee_f.params = List.length args then
            List.iter emit (clone callee_f d args)
          else (
            List.iter (fun p -> emit (Param p)) lastn;
            emit (Call (d, callee, nargs)));
          go rest)
        else (
          List.iter (fun p -> emit (Param p)) !pending;
          pending := [];
          emit (Call (d, callee, nargs));
          go rest)
    | i :: rest ->
        List.iter (fun p -> emit (Param p)) !pending;
        pending := [];
        emit i;
        go rest
  in
  go (flatten_func f)

let inline_calls (prog: ir_program) : ir_program =
  let prog = ref prog in
  for _ = 1 to 2 do
    let analysis = global_analysis !prog in
    if Hashtbl.length analysis.fa_funcs >= 2 then (
      let inlineable = Hashtbl.create 16 in
      Hashtbl.iter (fun name f ->
        let ok =
          name <> "main"
          && List.length (flatten_func f) <= 30
          && not (is_recursive_func analysis.fa_funcs name)
          && not (has_loop_blocks (f.entry :: f.blocks))
          && S.is_empty (Hashtbl.find analysis.fa_writes name)
        in
        Hashtbl.replace inlineable name ok)
        analysis.fa_funcs;
      let any = ref false in
      Hashtbl.iter (fun _ ok -> if ok then any := true) inlineable;
      if !any then
        prog :=
          List.map (function
            | GlobalVar _ as g -> g
            | Function f ->
                let nf, added = inline_func f analysis.fa_funcs inlineable in
                Function
                  { nf with
                    locals =
                      List.filter (fun l -> not (List.mem l added)) nf.locals @ added })
            !prog)
  done;
  !prog

(* ---------- loop invariant code motion ---------- *)

let licm_func (f: ir_func) (writes: (string, S.t) Hashtbl.t) : ir_func =
  let all = f.entry :: f.blocks in
  let idx = Hashtbl.create 16 in
  List.iteri (fun i (b: basic_block) -> Hashtbl.replace idx b.label i) all;
  let cands = ref [] in
  List.iteri (fun i (b: basic_block) ->
    match List.rev b.instrs with
    | Goto h_lbl :: _ ->
        (match Hashtbl.find_opt idx h_lbl with
         | Some h when h < i -> cands := (h, i) :: !cands
         | _ -> ())
    | _ -> ())
    all;
  let cands = List.rev !cands in
  if cands = [] then f
  else
    let body_size (h, i) =
      let rec go k acc =
        if k > i then acc
        else go (k + 1) (acc + List.length (List.nth all k).instrs)
      in
      go h 0
    in
    let h, i =
      List.fold_left
        (fun best c -> if body_size c < body_size best then c else best)
        (List.hd cands) (List.tl cands)
    in
    if h = 0 then f
    else
      let loop_blocks =
        let rec go k acc =
          if k > i then List.rev acc
          else go (k + 1) ((List.nth all k) :: acc)
        in
        go h []
      in
      let loop_callees = ref S.empty in
      List.iter (fun (b: basic_block) ->
        List.iter (function
          | Call (_, callee, _) -> loop_callees := S.add callee !loop_callees
          | _ -> ())
          b.instrs)
        loop_blocks;
      let unsafe_globals = ref S.empty in
      S.iter (fun c ->
        match Hashtbl.find_opt writes c with
        | Some w -> unsafe_globals := S.union !unsafe_globals w
        | None -> ())
        !loop_callees;
      let defined = ref S.empty in
      let def_counts = Hashtbl.create 16 in
      List.iter (fun (b: basic_block) ->
        List.iter (fun inst ->
          match def_operand inst with
          | Some d ->
              (match op_key d with
               | Some k ->
                   defined := S.add k !defined;
                   let c = match Hashtbl.find_opt def_counts k with Some c -> c | None -> 0 in
                   Hashtbl.replace def_counts k (c + 1)
               | None -> ())
          | None -> ())
          b.instrs)
        loop_blocks;
      let uses_of = function
        | Assign (_, y) -> [y]
        | AssignBinOp (_, _, a, b) -> [a; b]
        | AssignUnOp (_, _, a) -> [a]
        | _ -> []
      in
      let invariant inst =
        match inst with
        | Goto _ | IfGoto _ | IfNotGoto _ | Label _ | Return _ | Param _ | Call _ -> false
        | Assign _ | AssignBinOp _ | AssignUnOp _ ->
            let ok = ref true in
            List.iter (fun o ->
              match op_key o with
              | Some k when S.mem k !defined -> ok := false
              | _ ->
                  (match o with
                   | Var v when is_global_var v && S.mem v !unsafe_globals -> ok := false
                   | _ -> ()))
              (uses_of inst);
            if not !ok then false
            else
              match def_operand inst with
              | None -> false
              | Some d ->
                  (match d with
                   | Temp _ ->
                       (match op_key d with
                        | None -> false
                        | Some k ->
                            if Hashtbl.find_opt def_counts k <> Some 1 then false
                            else
                              match inst with
                              | AssignBinOp (_, (Ast.Div | Ast.Mod), _, b) ->
                                  (match b with Const c when c <> 0 -> true | _ -> false)
                              | _ -> true)
                   | _ -> false)
      in
      let hoist = ref [] in
      List.iter (fun (b: basic_block) ->
        List.iter (fun inst -> if invariant inst then hoist := (b, inst) :: !hoist) b.instrs)
        loop_blocks;
      let hoist = List.rev !hoist in
      if hoist = [] then f
      else
        let is_hoisted inst = List.exists (fun (_, i') -> inst == i') hoist in
        let new_loop =
          List.map (fun (b: basic_block) ->
            { b with instrs = List.filter (fun inst -> not (is_hoisted inst)) b.instrs })
            loop_blocks
        in
        let header_label = (List.nth all h).label in
        let pre_label = fresh_label () in
        let pre_instrs = List.map snd hoist in
        let retarget instrs =
          List.map (function
            | Goto l when l = header_label -> Goto pre_label
            | IfGoto (a, l) when l = header_label -> IfGoto (a, pre_label)
            | IfNotGoto (a, l) when l = header_label -> IfNotGoto (a, pre_label)
            | i -> i)
            instrs
        in
        let blocks = ref [] in
        List.iteri (fun k (b: basic_block) ->
          if k < h then blocks := { b with instrs = retarget b.instrs } :: !blocks)
          all;
        blocks := { label = pre_label; instrs = pre_instrs } :: !blocks;
        List.iteri (fun k _ ->
          if k >= h && k <= i then
            blocks := List.nth new_loop (k - h) :: !blocks)
          all;
        List.iteri (fun k (b: basic_block) ->
          if k > i then blocks := { b with instrs = retarget b.instrs } :: !blocks)
          all;
        match List.rev !blocks with
        | entry :: rest -> { f with entry; blocks = rest }
        | [] -> f

let licm_loops (prog: ir_program) : ir_program =
  let analysis = global_analysis prog in
  List.map (function
    | Function f -> Function (licm_func f analysis.fa_writes)
    | GlobalVar _ as g -> g)
    prog

(* ---------- loop unrolling ---------- *)

let unroll_func (f: ir_func) : ir_func =
  let factor = 4 in
  let size_cap = 4000 in
  let all = f.entry :: f.blocks in
  let idx = Hashtbl.create 16 in
  List.iteri (fun i (b: basic_block) -> Hashtbl.replace idx b.label i) all;
  let cands = ref [] in
  List.iteri (fun i (b: basic_block) ->
    match List.rev b.instrs with
    | Goto h_lbl :: _ ->
        (match Hashtbl.find_opt idx h_lbl with
         | Some h when h < i -> cands := (h, i) :: !cands
         | _ -> ())
    | _ -> ())
    all;
  let cands = List.rev !cands in
  if cands = [] then f
  else
    let body_size (h, i) =
      let rec go k acc =
        if k > i then acc
        else go (k + 1) (acc + List.length (List.nth all k).instrs)
      in
      go h 0
    in
    let h, i =
      List.fold_left
        (fun best c -> if body_size c < body_size best then c else best)
        (List.hd cands) (List.tl cands)
    in
    if body_size (h, i) > 60 then f
    else
      let hins = (List.nth all h).instrs in
      match List.rev hins with
      | IfNotGoto (cond, exit_l) :: _ ->
          let loop_labels =
            let rec go k acc =
              if k > i then acc
              else go (k + 1) (S.add (List.nth all k).label acc)
            in
            go h S.empty
          in
          if S.mem exit_l loop_labels then f
          else if
            List.length (flatten_func f) + (factor - 1) * (body_size (h, i) + 1)
            > size_cap
          then f
          else
            let header_label = (List.nth all h).label in
            let hpart =
              match List.rev hins with
              | _ :: rest -> List.rev rest
              | [] -> []
            in
            let body =
              let rec go k acc =
                if k > i then List.rev acc
                else go (k + 1) ((List.nth all k) :: acc)
              in
              go (h + 1) []
            in
            let loop_temp_defs = ref IntSet.empty in
            for k = h to i do
              List.iter (fun inst ->
                match def_operand inst with
                | Some (Temp t) -> loop_temp_defs := IntSet.add t !loop_temp_defs
                | _ -> ())
                (List.nth all k).instrs
            done;
            let remap_op tmap o =
              match o with
              | Temp t when IntSet.mem t !loop_temp_defs ->
                  (match Hashtbl.find_opt tmap t with
                   | Some t' -> Temp t'
                   | None ->
                       let t' = !inline_temp_uniq in
                       incr inline_temp_uniq;
                       Hashtbl.add tmap t t';
                       Temp t')
              | o -> o
            in
            let map_inst tmap lmap inst =
              match inst with
              | Assign (d, s) -> Assign (remap_op tmap d, remap_op tmap s)
              | AssignBinOp (d, op, a, b) ->
                  AssignBinOp (remap_op tmap d, op, remap_op tmap a, remap_op tmap b)
              | AssignUnOp (d, op, a) -> AssignUnOp (remap_op tmap d, op, remap_op tmap a)
              | Goto target ->
                  if target = header_label then Goto target
                  else if S.mem target loop_labels then (
                    if not (Hashtbl.mem lmap target) then Hashtbl.add lmap target (fresh_label ());
                    Goto (Hashtbl.find lmap target))
                  else Goto target
              | IfGoto (a, target) ->
                  if target = header_label then IfGoto (remap_op tmap a, target)
                  else if S.mem target loop_labels then (
                    if not (Hashtbl.mem lmap target) then Hashtbl.add lmap target (fresh_label ());
                    IfGoto (remap_op tmap a, Hashtbl.find lmap target))
                  else IfGoto (remap_op tmap a, target)
              | IfNotGoto (a, target) ->
                  if target = header_label then IfNotGoto (remap_op tmap a, target)
                  else if S.mem target loop_labels then (
                    if not (Hashtbl.mem lmap target) then Hashtbl.add lmap target (fresh_label ());
                    IfNotGoto (remap_op tmap a, Hashtbl.find lmap target))
                  else IfNotGoto (remap_op tmap a, target)
              | Label l -> Label l
              | Param a -> Param (remap_op tmap a)
              | Call (d, fname, n) -> Call (remap_op tmap d, fname, n)
              | Return (Some a) -> Return (Some (remap_op tmap a))
              | Return None -> Return None
            in
            let clone_instrs drop_last tmap lmap instrs =
              let len = List.length instrs in
              let out = ref [] in
              List.iteri (fun k inst ->
                let is_last = k = len - 1 in
                match inst with
                | Goto _ when drop_last && is_last -> ()
                | _ -> out := map_inst tmap lmap inst :: !out)
                instrs;
              List.rev !out
            in
            let new_blocks_rev = ref [] in
            let push b = new_blocks_rev := b :: !new_blocks_rev in
            for _ = 1 to factor - 1 do
              let tmap = Hashtbl.create 16 in
              let lmap = Hashtbl.create 16 in
              List.iter (fun (bb: basic_block) ->
                if not (Hashtbl.mem lmap bb.label) then
                  Hashtbl.add lmap bb.label (fresh_label ()))
                body;
              let hp =
                clone_instrs false tmap lmap hpart
                @ [IfNotGoto (remap_op tmap cond, exit_l)]
              in
              push { label = fresh_label (); instrs = hp };
              List.iteri (fun k (bb: basic_block) ->
                let drop = k = List.length body - 1 in
                let instrs = clone_instrs drop tmap lmap bb.instrs in
                push { label = Hashtbl.find lmap bb.label; instrs })
                body
            done;
            let tmap = Hashtbl.create 16 in
            let lmap = Hashtbl.create 16 in
            List.iter (fun (bb: basic_block) ->
              if not (Hashtbl.mem lmap bb.label) then
                Hashtbl.add lmap bb.label (fresh_label ()))
              body;
            List.iter (fun (bb: basic_block) ->
              let instrs = clone_instrs false tmap lmap bb.instrs in
              push { label = Hashtbl.find lmap bb.label; instrs })
              body;
            let prefix =
              List.mapi (fun k (b: basic_block) ->
                if k = i then
                  { b with
                    instrs =
                      (match List.rev b.instrs with
                       | _ :: rest -> List.rev rest
                       | [] -> []) }
                else b)
                (List.filteri (fun k _ -> k <= i) all)
            in
            let suffix =
              List.filteri (fun k _ -> k > i) all
            in
            let all_new = prefix @ List.rev !new_blocks_rev @ suffix in
            (match all_new with
             | entry :: blocks ->
                 rebuild_func f
                   (compact_temps (flatten_func { f with entry; blocks }))
             | [] -> f)
      | _ -> f

let unroll_loops (prog: ir_program) : ir_program =
  List.map (function
    | Function f -> Function (unroll_func f)
    | GlobalVar _ as g -> g)
    prog

let repeat_pass n pass prog =
  let rec go k p =
    if k <= 0 then p
    else
      let p' = pass p in
      if p' = p then p else go (k - 1) p'
  in
  go n prog
 
 (* ---------- 优化管道 ---------- *)
 
let optimize_linear (params: string list) (instrs: tac list) : tac list =
  instrs
  |> single_assign_const_prop params
  |> const_fold
  |> algebra_simplify
  |> reassoc_consts
  |> copy_prop
  |> common_subexpr
  |> copy_prop
  |> single_assign_const_prop params
  |> const_fold
  |> algebra_simplify
  |> reassoc_consts
 
 let rec repeat_linear (params: string list) n instrs =
   if n <= 0 then instrs
   else
     let instrs' = optimize_linear params instrs in
     if instrs' = instrs then instrs else repeat_linear params (n - 1) instrs'
 
 let optimize_func (f: ir_func) : ir_func =
   let instrs = flatten_func f in
   let f, instrs = normalize_entry f instrs in
   let instrs = repeat_linear f.params 3 instrs in
   let instrs = tail_recursion f instrs in
   let instrs = repeat_linear f.params 3 instrs in
   let f = rebuild_func f instrs in
   let f = truncate_func f in
   
   let f = remove_unreachable_blocks f in
   
   
   
   let f = const_prop_cfg f in
   let f = rebuild_func f (repeat_linear f.params 2 (flatten_func f)) in
   let f = truncate_func f in
   let f = remove_unreachable_blocks f in
   let f = dce f in
   let f = rebuild_func f (repeat_linear f.params 2 (flatten_func f)) in
   let f = dce f in
   let f = merge_empty_blocks f in
   let f = cleanup f in
   let f = remove_unreachable_blocks f in
   let f = shrink_func f in
   f
 
 (* 对整个 IR 程序做优化：逐个函数处理，全局变量保持不变 *)
let optimize_program (prog: ir_program) : ir_program =
  let optimize_all prog =
    List.map (function
      | GlobalVar _ as g -> g
      | Function f -> Function (optimize_func f))
      prog
  in
  let prog = global_const_prop prog in
  let prog = optimize_all prog in
  let prog = inline_calls prog in
  let prog = optimize_all prog in
  let prog = repeat_pass 6 licm_loops prog in
  let prog = optimize_all prog in
  let prog = repeat_pass 3 unroll_loops prog in
  let prog = optimize_all prog in
  let prog = const_eval_program prog in
  optimize_all prog
