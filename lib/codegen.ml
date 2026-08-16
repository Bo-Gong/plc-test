(* lib/codegen.ml *)
open Ir

(* 唯一标签计数器 *)
let inline_label_counter = ref 0

let gen_inline_label prefix =
  incr inline_label_counter;
  Printf.sprintf "%s_inline_%d" prefix !inline_label_counter

(* 辅助函数：列表切分 *)
let rec split_at n = function
  | xs when n <= 0 -> [], xs
  | [] -> [], []
  | x :: xs ->
      let prefix, suffix = split_at (n - 1) xs in
      x :: prefix, suffix

(* ============================================================ *)
(* 常量判断和数学工具 *)

(* 判断操作数是否为常量 *)
let is_const_op = function Const _ -> true | _ -> false
let get_const_val = function Const n -> n | _ -> 0

(* 判断是否为 2 的幂 *)
let is_power_of_two n =
  n > 0 && (n land (n - 1)) = 0

let log2 n =
  let rec loop x acc =
    if x = 1 then acc
    else loop (x lsr 1) (acc + 1)
  in
  if n <= 0 then 0 else loop n 0

(* 检查立即数是否在 12 位范围内 *)
let is_imm12 n = n >= -2048 && n <= 2047

(* ============================================================ *)
(* 判断函数是否需要栈帧 *)

(* 展开函数为指令列表 *)
let flatten_func (f: ir_func) =
  List.concat_map (fun b -> Label b.label :: b.instrs) (f.entry :: f.blocks)

(* 检查函数是否为叶函数（无函数调用） *)
let is_leaf_function (f: ir_func) =
  let instrs = flatten_func f in
  let has_call = ref false in
  List.iter (function
    | Call _ -> has_call := true
    | _ -> ()
  ) instrs;
  not !has_call

(* 检查函数是否有局部变量需要栈槽 *)
let has_local_storage (f: ir_func) =
  List.length f.locals > 0 || f.temps > 0

(* ============================================================ *)
(* 安全的偏移量查找 *)
let find_offset map op =
  match Hashtbl.find_opt map op with
  | Some off -> off
  | None ->
      match op with
      | Var name ->
          Printf.eprintf "Warning: Variable '%s' not found in offset map, treating as global\n" name;
          -1
      | Temp t ->
          Printf.eprintf "Fatal: Temp %d not found in offset map\n" t;
          exit 1
      | Const _ ->
          Printf.eprintf "Fatal: Const should not be in offset map\n";
          exit 1

(* ============================================================ *)
(* 加载和存储操作数 *)

let load_op reg op map reg_map =
  match op with
  | Const n ->
      Printf.printf "    li %s, %d\n" reg n
  | (Temp _ | Var _) as op ->
      (match Hashtbl.find_opt reg_map op with
       | Some phys ->
           if phys <> reg then
             Printf.printf "    addi %s, %s, 0\n" reg phys
       | None ->
           (match op with
            | Temp t ->
                if Hashtbl.mem map (Temp t) then
                  let off = Hashtbl.find map (Temp t) in
                  Printf.printf "    lw %s, %d(fp)\n" reg off
                else (
                  Printf.eprintf "ERROR: Temp %d not found in offset map\n" t;
                  exit 1
                )
            | Var name ->
                if Hashtbl.mem map (Var name) then
                  let off = Hashtbl.find map (Var name) in
                  Printf.printf "    lw %s, %d(fp)\n" reg off
                else
                  (Printf.printf "    la %s, %s\n" reg name;
                   Printf.printf "    lw %s, 0(%s)\n" reg reg)
            | Const _ -> assert false))

let store_op reg op map reg_map =
  match op with
  | Const _ -> ()
  | (Temp _ | Var _) as op ->
      (match Hashtbl.find_opt reg_map op with
       | Some phys ->
           if phys <> reg then
             Printf.printf "    addi %s, %s, 0\n" phys reg
       | None ->
           (match op with
            | Temp t ->
                if Hashtbl.mem map (Temp t) then
                  let off = Hashtbl.find map (Temp t) in
                  Printf.printf "    sw %s, %d(fp)\n" reg off
                else (
                  Printf.eprintf "ERROR: Temp %d not found in offset map for store\n" t;
                  exit 1
                )
            | Var name ->
                if Hashtbl.mem map (Var name) then
                  let off = Hashtbl.find map (Var name) in
                  Printf.printf "    sw %s, %d(fp)\n" reg off
                else
                  (Printf.printf "    la t3, %s\n" name;
                   Printf.printf "    sw %s, 0(t3)\n" reg)
            | Const _ -> assert false))

(* ============================================================ *)
(* 计算栈帧偏移量映射表 *)
let compute_offsets (f: ir_func) =
  let local_slots = ref 0 in
  let map = Hashtbl.create 32 in

  List.iter (fun name ->
    incr local_slots;
    Hashtbl.add map (Var name) (-8 - 4 * !local_slots)
  ) f.params;

  List.iter (fun name ->
    if not (Hashtbl.mem map (Var name)) then (
      incr local_slots;
      Hashtbl.add map (Var name) (-8 - 4 * !local_slots)
    )
  ) f.locals;

  for t = 0 to f.temps - 1 do
    incr local_slots;
    Hashtbl.add map (Temp t) (-8 - 4 * !local_slots)
  done;

  (!local_slots, map)

(* ============================================================ *)
(* 寄存器分配：基于活跃区间的线性扫描 *)

let callee_saved_regs =
  ["s1"; "s2"; "s3"; "s4"; "s5"; "s6"; "s7"; "s8"; "s9"; "s10"; "s11"]

let leaf_extra_regs =
  ["t4"; "t5"; "t6"; "a0"; "a1"; "a2"; "a3"; "a4"; "a5"; "a6"; "a7"]

let add_unique x xs = if List.mem x xs then xs else x :: xs

let list_union xs ys =
  List.fold_left (fun acc x -> if List.mem x acc then acc else x :: acc) ys xs

let list_diff xs ys =
  List.filter (fun x -> not (List.mem x ys)) xs

let list_equal xs ys =
  List.for_all (fun x -> List.mem x ys) xs
  && List.for_all (fun y -> List.mem y xs) ys

let allocate_registers (f : ir_func) (is_leaf : bool) =
  let blocks = f.entry :: f.blocks in
  let instrs = List.concat_map (fun b -> Label b.label :: b.instrs) blocks in
  let arr = Array.of_list instrs in
  let n = Array.length arr in

  let label_map = Hashtbl.create 32 in
  Array.iteri (fun i -> function
    | Label l -> Hashtbl.replace label_map l i
    | _ -> ()) arr;

  let target l =
    match Hashtbl.find_opt label_map l with Some i -> [i] | None -> []
  in
  let successors i =
    match arr.(i) with
    | Goto l -> target l
    | IfGoto (_, l) | IfNotGoto (_, l) ->
        let fall = if i + 1 < n then [i + 1] else [] in
        target l @ fall
    | Return _ -> []
    | _ -> if i + 1 < n then [i + 1] else []
  in

  let local_names = Hashtbl.create 64 in
  List.iter (fun name -> Hashtbl.replace local_names name ()) f.params;
  List.iter (fun name -> Hashtbl.replace local_names name ()) f.locals;
  let is_allocatable = function
    | Temp _ -> true
    | Var name -> Hashtbl.mem local_names name
    | Const _ -> false
  in

  let uses_arr = Array.make n [] in
  let defs_arr = Array.make n [] in
  let add_use i op = if is_allocatable op then uses_arr.(i) <- add_unique op uses_arr.(i) in
  let add_def i op = if is_allocatable op then defs_arr.(i) <- add_unique op defs_arr.(i) in
  let add_call_arg_uses i nargs =
    let rec collect k j acc =
      if k = 0 then acc
      else if j < 0 then acc
      else
        match arr.(j) with
        | Param op -> collect (k - 1) (j - 1) (op :: acc)
        | _ -> collect k (j - 1) acc
    in
    List.iter (fun op -> add_use i op) (collect nargs (i - 1) [])
  in
  Array.iteri (fun i -> function
    | Assign (x, y) -> add_def i x; add_use i y
    | AssignBinOp (x, _, y, z) -> add_def i x; add_use i y; add_use i z
    | AssignUnOp (x, _, y) -> add_def i x; add_use i y
    | IfGoto (x, _) | IfNotGoto (x, _) -> add_use i x
    | Param _ -> ()
    | Call (x, _, nargs) -> add_def i x; add_call_arg_uses i nargs
    | Return (Some x) -> add_use i x
    | Goto _ | Label _ | Return None -> ()) arr;

  let live_in = Array.make n [] in
  let live_out = Array.make n [] in
  let changed = ref true in
  while !changed do
    changed := false;
    for i = n - 1 downto 0 do
      let out =
        List.fold_left (fun acc j -> list_union acc live_in.(j)) [] (successors i)
      in
      if not (list_equal out live_out.(i)) then begin
        live_out.(i) <- out;
        changed := true
      end;
      let inn = list_union uses_arr.(i) (list_diff live_out.(i) defs_arr.(i)) in
      if not (list_equal inn live_in.(i)) then begin
        live_in.(i) <- inn;
        changed := true
      end
    done
  done;

  let intervals = Hashtbl.create 64 in
  let update op pos =
    let start, stop =
      match Hashtbl.find_opt intervals op with
      | Some (a, b) -> min a pos, max b (pos + 1)
      | None -> pos, pos + 1
    in
    Hashtbl.replace intervals op (start, stop)
  in
  for i = 0 to n - 1 do
    List.iter (fun op -> update op i) live_in.(i);
    List.iter (fun op -> update op i) live_out.(i)
  done;

  let interval_list =
    Hashtbl.fold (fun op (start, stop) acc -> (op, start, stop) :: acc) intervals []
    |> List.sort (fun (_, s1, _) (_, s2, _) -> compare s1 s2)
  in

  let pool = if is_leaf then leaf_extra_regs @ callee_saved_regs else callee_saved_regs in
  let reg_map = Hashtbl.create 64 in
  let free_regs = ref pool in
  let active = ref [] in
  let expire start =
    let done_, alive = List.partition (fun (_, _, stop) -> stop <= start) !active in
    List.iter (fun (_, r, _) -> free_regs := r :: !free_regs) done_;
    active := alive
  in
  List.iter (fun (op, start, stop) ->
    expire start;
    match !free_regs with
    | r :: rest ->
        free_regs := rest;
        Hashtbl.replace reg_map op r;
        active := (op, r, stop) :: !active
    | [] -> ())
    interval_list;

  let used_regs =
    let all =
      Hashtbl.fold (fun _ r acc -> add_unique r acc) reg_map []
    in
    List.filter (fun r -> List.mem r all) pool
  in
  (reg_map, used_regs)

let emit_add x y z map reg_map =
  begin
    match y, z with
    | Const 0, nonconst ->
        load_op "t0" nonconst map reg_map
    | nonconst, Const 0 ->
        load_op "t0" nonconst map reg_map
    | Const c, nonconst when is_imm12 c ->
        load_op "t0" nonconst map reg_map;
        Printf.printf "    addi t0, t0, %d\n" c
    | nonconst, Const c when is_imm12 c ->
        load_op "t0" nonconst map reg_map;
        Printf.printf "    addi t0, t0, %d\n" c
    | Const a, Const b ->
        Printf.printf "    li t0, %d\n" (a + b)
    | _ ->
        load_op "t0" y map reg_map;
        load_op "t1" z map reg_map;
        Printf.printf "    add t0, t0, t1\n"
    end;
  store_op "t0" x map reg_map

(* 生成减法代码（含常量优化） *)
let emit_sub x y z map reg_map =
  begin
    match y, z with
    | nonconst, Const 0 ->
        load_op "t0" nonconst map reg_map
    | Const 0, nonconst ->
        load_op "t0" nonconst map reg_map;
        Printf.printf "    neg t0, t0\n"
    | nonconst, Const c when is_imm12 (-c) ->
        load_op "t0" nonconst map reg_map;
        Printf.printf "    addi t0, t0, %d\n" (-c)
    | Const a, Const b ->
        Printf.printf "    li t0, %d\n" (a - b)
    | _ ->
        load_op "t0" y map reg_map;
        load_op "t1" z map reg_map;
        Printf.printf "    sub t0, t0, t1\n"
    end;
  store_op "t0" x map reg_map

(* 生成乘法代码（使用 M 扩展 + 常量优化） *)
let emit_mul x y z map reg_map =
  let is_y_const = is_const_op y in
  let is_z_const = is_const_op z in
  
  if is_z_const then
    let n = get_const_val z in
    load_op "t0" y map reg_map;
    if n = 0 then
      Printf.printf "    li t0, 0\n"
    else if n = 1 then
      ()
    else if n = -1 then
      Printf.printf "    neg t0, t0\n"
    else if is_power_of_two n then
      let shift = log2 n in
      Printf.printf "    slli t0, t0, %d\n" shift
    else if n = 3 then
      (Printf.printf "    slli t1, t0, 1\n";
       Printf.printf "    add t0, t0, t1\n")
    else if n = 5 then
      (Printf.printf "    slli t1, t0, 2\n";
       Printf.printf "    add t0, t0, t1\n")
    else if n = 7 then
      (Printf.printf "    slli t1, t0, 3\n";
       Printf.printf "    sub t0, t1, t0\n")
    else if n = 9 then
      (Printf.printf "    slli t1, t0, 3\n";
       Printf.printf "    add t0, t0, t1\n")
    else if n = 10 then
      (Printf.printf "    slli t1, t0, 3\n";
       Printf.printf "    slli t2, t0, 1\n";
       Printf.printf "    add t0, t1, t2\n")
    else
      (load_op "t1" z map reg_map;
       Printf.printf "    mul t0, t0, t1\n")
  else if is_y_const then
    let n = get_const_val y in
    load_op "t0" z map reg_map;
    if n = 0 then
      Printf.printf "    li t0, 0\n"
    else if n = 1 then
      ()
    else if n = -1 then
      Printf.printf "    neg t0, t0\n"
    else if is_power_of_two n then
      let shift = log2 n in
      Printf.printf "    slli t0, t0, %d\n" shift
    else
      (load_op "t1" y map reg_map;
       Printf.printf "    mul t0, t0, t1\n")
  else
    (load_op "t0" y map reg_map;
     load_op "t1" z map reg_map;
     Printf.printf "    mul t0, t0, t1\n");
  store_op "t0" x map reg_map

(* 生成除法代码（使用 M 扩展 + 常量优化） *)
let emit_div x y z map reg_map =
  if is_const_op z then
    let n = get_const_val z in
    load_op "t0" y map reg_map;
    if n = 1 then
      ()
    else if n = -1 then
      Printf.printf "    neg t0, t0\n"
    else if is_power_of_two n then
      let shift = log2 n in
      if shift >= 31 then
        (load_op "t1" z map reg_map;
         Printf.printf "    div t0, t0, t1\n")
      else
        (Printf.printf "    srai t1, t0, 31\n";
         Printf.printf "    srli t1, t1, %d\n" (32 - shift);
         Printf.printf "    add t0, t0, t1\n";
         Printf.printf "    srai t0, t0, %d\n" shift)
    else
      (load_op "t1" z map reg_map;
       Printf.printf "    div t0, t0, t1\n")
  else
    (load_op "t0" y map reg_map;
     load_op "t1" z map reg_map;
     Printf.printf "    div t0, t0, t1\n");
  store_op "t0" x map reg_map

(* 生成取模代码（使用 M 扩展 + 常量优化） *)
let emit_mod x y z map reg_map =
  if is_const_op z then
    let n = get_const_val z in
    load_op "t0" y map reg_map;
    if n = 1 then
      Printf.printf "    li t0, 0\n"
    else if is_power_of_two n then
      let shift = log2 n in
      let mask = n - 1 in
      if shift >= 31 then
        (load_op "t1" z map reg_map;
         Printf.printf "    rem t0, t0, t1\n")
      else
        (Printf.printf "    srai t1, t0, 31\n";
         Printf.printf "    srli t1, t1, %d\n" (32 - shift);
         Printf.printf "    add t0, t0, t1\n";
         if is_imm12 mask then
           Printf.printf "    andi t0, t0, %d\n" mask
         else
           (Printf.printf "    li t2, %d\n" mask;
            Printf.printf "    and t0, t0, t2\n");
         Printf.printf "    sub t0, t0, t1\n")
    else
      (load_op "t1" z map reg_map;
       Printf.printf "    rem t0, t0, t1\n")
  else
    (load_op "t0" y map reg_map;
     load_op "t1" z map reg_map;
     Printf.printf "    rem t0, t0, t1\n");
  store_op "t0" x map reg_map

(* 生成比较运算代码（含常量优化） *)
let emit_compare x op y z map reg_map =
  begin
    match op with
    | Ast.Eq ->
        (match y, z with
         | Const 0, nonconst ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    seqz t0, t0\n"
         | nonconst, Const 0 ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    seqz t0, t0\n"
         | Const a, Const b ->
             Printf.printf "    li t0, %d\n" (if a = b then 1 else 0)
         | _ ->
             load_op "t0" y map reg_map;
             load_op "t1" z map reg_map;
             Printf.printf "    xor t0, t0, t1\n";
             Printf.printf "    seqz t0, t0\n")
    | Ast.Ne ->
        (match y, z with
         | Const 0, nonconst ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    snez t0, t0\n"
         | nonconst, Const 0 ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    snez t0, t0\n"
         | Const a, Const b ->
             Printf.printf "    li t0, %d\n" (if a <> b then 1 else 0)
         | _ ->
             load_op "t0" y map reg_map;
             load_op "t1" z map reg_map;
             Printf.printf "    xor t0, t0, t1\n";
             Printf.printf "    snez t0, t0\n")
    | Ast.Lt ->
        (match y, z with
         | Const 0, nonconst ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    slti t0, t0, 1\n";
             Printf.printf "    xori t0, t0, 1\n"
         | nonconst, Const 0 ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    srli t0, t0, 31\n"
         | nonconst, Const c when is_imm12 c ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    slti t0, t0, %d\n" c
         | Const a, Const b ->
             Printf.printf "    li t0, %d\n" (if a < b then 1 else 0)
         | _ ->
             load_op "t0" y map reg_map;
             load_op "t1" z map reg_map;
             Printf.printf "    slt t0, t0, t1\n")
    | Ast.Gt ->
        (match y, z with
         | nonconst, Const 0 ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    slti t0, t0, 1\n";
             Printf.printf "    xori t0, t0, 1\n"
         | Const 0, nonconst ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    srli t0, t0, 31\n"
         | Const a, Const b ->
             Printf.printf "    li t0, %d\n" (if a > b then 1 else 0)
         | _ ->
             load_op "t0" y map reg_map;
             load_op "t1" z map reg_map;
             Printf.printf "    slt t0, t1, t0\n")
    | Ast.Le ->
        (match y, z with
         | nonconst, Const 0 ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    slti t0, t0, 1\n"
         | Const 0, nonconst ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    srli t0, t0, 31\n";
             Printf.printf "    xori t0, t0, 1\n"
         | Const a, Const b ->
             Printf.printf "    li t0, %d\n" (if a <= b then 1 else 0)
         | _ ->
             load_op "t0" y map reg_map;
             load_op "t1" z map reg_map;
             Printf.printf "    slt t0, t1, t0\n";
             Printf.printf "    xori t0, t0, 1\n")
    | Ast.Ge ->
        (match y, z with
         | nonconst, Const 0 ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    srli t0, t0, 31\n";
             Printf.printf "    xori t0, t0, 1\n"
         | Const 0, nonconst ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    slti t0, t0, 1\n"
         | Const a, Const b ->
             Printf.printf "    li t0, %d\n" (if a >= b then 1 else 0)
         | _ ->
             load_op "t0" y map reg_map;
             load_op "t1" z map reg_map;
             Printf.printf "    slt t0, t0, t1\n";
             Printf.printf "    xori t0, t0, 1\n")
    | _ -> ()
  end;
  store_op "t0" x map reg_map

(* 生成逻辑运算代码（含常量优化） *)
let emit_logic x op y z map reg_map =
  begin
    match op with
    | Ast.And ->
        (match y, z with
         | Const 0, _ ->
             Printf.printf "    li t0, 0\n"
         | _, Const 0 ->
             Printf.printf "    li t0, 0\n"
         | Const 1, nonconst ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    snez t0, t0\n"
         | nonconst, Const 1 ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    snez t0, t0\n"
         | Const a, Const b ->
             Printf.printf "    li t0, %d\n" (if a <> 0 && b <> 0 then 1 else 0)
         | _ ->
             load_op "t0" y map reg_map;
             load_op "t1" z map reg_map;
             Printf.printf "    and t0, t0, t1\n";
             Printf.printf "    snez t0, t0\n")
    | Ast.Or ->
        (match y, z with
         | Const 0, nonconst ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    snez t0, t0\n"
         | nonconst, Const 0 ->
             load_op "t0" nonconst map reg_map;
             Printf.printf "    snez t0, t0\n"
         | Const 1, _ ->
             Printf.printf "    li t0, 1\n"
         | _, Const 1 ->
             Printf.printf "    li t0, 1\n"
         | Const a, Const b ->
             Printf.printf "    li t0, %d\n" (if a <> 0 || b <> 0 then 1 else 0)
         | _ ->
             load_op "t0" y map reg_map;
             load_op "t1" z map reg_map;
             Printf.printf "    or t0, t0, t1\n";
             Printf.printf "    snez t0, t0\n")
    | _ -> ()
  end;
  store_op "t0" x map reg_map

(* ============================================================ *)
(* 翻译单条 TAC 指令 *)

let emit_tac fname tac_inst map reg_map current_args needs_frame =
  match tac_inst with
  | Assign (x, y) ->
    if x = y then
      ()
    else
      load_op "t0" y map reg_map;
      store_op "t0" x map reg_map

  | AssignBinOp (x, op, y, z) ->
      (match op with
       | Ast.Add -> emit_add x y z map reg_map
       | Ast.Sub -> emit_sub x y z map reg_map
       | Ast.Mul -> emit_mul x y z map reg_map
       | Ast.Div -> emit_div x y z map reg_map
       | Ast.Mod -> emit_mod x y z map reg_map
       | Ast.Eq | Ast.Ne | Ast.Lt | Ast.Gt | Ast.Le | Ast.Ge ->
           emit_compare x op y z map reg_map
       | Ast.And | Ast.Or ->
           emit_logic x op y z map reg_map)

  | AssignUnOp (x, op, y) ->
      load_op "t0" y map reg_map;
      (match op with
       | Ast.Pos -> ()
       | Ast.Neg -> Printf.printf "    neg t0, t0\n"
       | Ast.Not -> Printf.printf "    seqz t0, t0\n");
      store_op "t0" x map reg_map

  | Goto l ->
      Printf.printf "    j %s\n" l

  | IfGoto (x, l) ->
      load_op "t0" x map reg_map;
      Printf.printf "    bnez t0, %s\n" l

  | IfNotGoto (x, l) ->
      load_op "t0" x map reg_map;
      Printf.printf "    beqz t0, %s\n" l

  | Label l ->
      Printf.printf "%s:\n" l

  | Param x ->
      current_args := x :: !current_args

  | Call (dest, callee, nargs) ->
      let call_args, rem = split_at nargs !current_args in
      current_args := rem;
      let args = call_args in
      
      let extra_space = if nargs > 8 then ((nargs - 8) * 4 + 15) / 16 * 16 else 0 in
      if extra_space > 0 then
        Printf.printf "    addi sp, sp, -%d\n" extra_space;
        
      List.iteri (fun j arg ->
        if j < 8 then
          load_op (Printf.sprintf "a%d" j) arg map reg_map
        else
          (load_op "t0" arg map reg_map;
           Printf.printf "    sw t0, %d(sp)\n" ((j - 8) * 4))
      ) args;
      
      Printf.printf "    call %s\n" callee;
      
      if extra_space > 0 then
        Printf.printf "    addi sp, sp, %d\n" extra_space;
        
      store_op "a0" dest map reg_map

  | Return (Some x) ->
      load_op "a0" x map reg_map;
      if needs_frame then
        Printf.printf "    j .L_epilogue_%s\n" fname
      else
        Printf.printf "    ret\n"

  | Return None ->
      if needs_frame then
        Printf.printf "    j .L_epilogue_%s\n" fname
      else
        Printf.printf "    ret\n"

(* ============================================================ *)
(* 翻译单个基本块 *)

let emit_block fname (b: basic_block) map reg_map current_args print_label needs_frame =
  if print_label && b.label <> "entry" then
    Printf.printf "%s:\n" b.label;
  let rec emit_until_terminator = function
    | [] -> ()
    | inst :: rest ->
        emit_tac fname inst map reg_map current_args needs_frame;
        match inst with
        | Return _ | Goto _ -> ()
        | _ -> emit_until_terminator rest
  in
  emit_until_terminator b.instrs

(* ============================================================ *)
(* 翻译单个函数 *)

let emit_function (f: ir_func) =
  let is_leaf = is_leaf_function f in
  let reg_map, used_regs = allocate_registers f is_leaf in
  let saved_regs =
    List.filter (fun r -> List.mem r callee_saved_regs) used_regs
  in
  let slots, map = compute_offsets f in
  let has_locals = has_local_storage f in
  let has_params = List.length f.params > 0 in
  let needs_frame = (not is_leaf) || has_locals || has_params in
  let saved_count = List.length saved_regs in
  let framesize =
    if needs_frame then ((8 + slots * 4 + saved_count * 4 + 15) / 16) * 16
    else 0
  in

  Printf.printf "    .globl %s\n" f.fname;
  Printf.printf "%s:\n" f.fname;

  if needs_frame then begin
    Printf.printf "    addi sp, sp, -%d\n" framesize;
    if not is_leaf then
      Printf.printf "    sw ra, %d(sp)\n" (framesize - 4);
    Printf.printf "    sw fp, %d(sp)\n" (framesize - 8);
    Printf.printf "    addi fp, sp, %d\n" framesize;

    List.iteri (fun j r ->
      let off = -8 - 4 * (slots + j + 1) in
      Printf.printf "    sw %s, %d(fp)\n" r off) saved_regs;

    List.iteri (fun i name ->
      let off = Hashtbl.find map (Var name) in
      if i < 8 then
        Printf.printf "    sw a%d, %d(fp)\n" i off
      else begin
        Printf.printf "    lw t0, %d(fp)\n" ((i - 8) * 4);
        Printf.printf "    sw t0, %d(fp)\n" off
      end) f.params;

    List.iteri (fun _i name ->
      match Hashtbl.find_opt reg_map (Var name) with
      | Some r ->
          let off = Hashtbl.find map (Var name) in
          Printf.printf "    lw %s, %d(fp)\n" r off
      | None -> ()) f.params
  end;

  if f.entry.label <> "entry" then
    Printf.printf "%s:\n" f.entry.label;

  let current_args = ref [] in
  emit_block f.fname f.entry map reg_map current_args false needs_frame;
  List.iter (fun b -> emit_block f.fname b map reg_map current_args true needs_frame) f.blocks;

  if needs_frame then begin
    Printf.printf ".L_epilogue_%s:\n" f.fname;
    List.iteri (fun j r ->
      let off = -8 - 4 * (slots + j + 1) in
      Printf.printf "    lw %s, %d(fp)\n" r off) saved_regs;
    if not is_leaf then
      Printf.printf "    lw ra, -4(fp)\n";
    Printf.printf "    lw fp, -8(fp)\n";
    Printf.printf "    addi sp, sp, %d\n" framesize;
    Printf.printf "    ret\n"
  end

let generate_riscv (prog: ir_program) =
  Printf.printf "    .text\n";

  List.iter (function
    | GlobalVar (name, Some v) ->
        Printf.printf "    .globl %s\n" name;
        Printf.printf "    .data\n";
        Printf.printf "    .align 2\n";
        Printf.printf "%s:\n" name;
        Printf.printf "    .word %d\n" v
    | GlobalVar (name, None) ->
        Printf.printf "    .globl %s\n" name;
        Printf.printf "    .data\n";
        Printf.printf "    .align 2\n";
        Printf.printf "%s:\n" name;
        Printf.printf "    .space 4\n"
    | Function f ->
        Printf.printf "    .text\n";
        emit_function f
  ) prog
