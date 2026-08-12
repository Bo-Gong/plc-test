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

let load_op reg op map =
  match op with
  | Const n ->
      Printf.printf "    li %s, %d\n" reg n
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

let store_op reg op map =
  match op with
  | Const _ -> ()
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

(* ============================================================ *)
(* 计算栈槽偏移量映射表 *)

let compute_offsets (f: ir_func) =
  let local_slots = ref 0 in
  let map = Hashtbl.create 32 in
  
  List.iteri (fun i name ->
    if i < 8 then (
      incr local_slots;
      Hashtbl.add map (Var name) (-8 - 4 * !local_slots)
    ) else (
      Hashtbl.add map (Var name) ((i - 8) * 4)
    )
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
(* 生成乘除法优化的代码 *)

(* 生成乘法代码（使用 M 扩展 + 常量优化） *)
let emit_mul x y z map =
  let is_y_const = is_const_op y in
  let is_z_const = is_const_op z in
  
  if is_z_const then
    let n = get_const_val z in
    load_op "t0" y map;
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
      (load_op "t1" z map;
       Printf.printf "    mul t0, t0, t1\n")
  else if is_y_const then
    let n = get_const_val y in
    load_op "t0" z map;
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
      (load_op "t1" y map;
       Printf.printf "    mul t0, t0, t1\n")
  else
    (load_op "t0" y map;
     load_op "t1" z map;
     Printf.printf "    mul t0, t0, t1\n");
  store_op "t0" x map

(* 生成除法代码（使用 M 扩展 + 常量优化） *)
let emit_div x y z map =
  if is_const_op z then
    let n = get_const_val z in
    load_op "t0" y map;
    if n = 1 then
      ()
    else if n = -1 then
      Printf.printf "    neg t0, t0\n"
    else if is_power_of_two n then
      let shift = log2 n in
      Printf.printf "    srai t0, t0, %d\n" shift
    else
      (load_op "t1" z map;
       Printf.printf "    div t0, t0, t1\n")
  else
    (load_op "t0" y map;
     load_op "t1" z map;
     Printf.printf "    div t0, t0, t1\n");
  store_op "t0" x map

(* 生成取模代码（使用 M 扩展 + 常量优化） *)
let emit_mod x y z map =
  if is_const_op z then
    let n = get_const_val z in
    load_op "t0" y map;
    if n = 1 then
      Printf.printf "    li t0, 0\n"
    else if is_power_of_two n then
      let mask = n - 1 in
      if is_imm12 mask then
        (* 小掩码：用 andi（一条指令） *)
        Printf.printf "    andi t0, t0, %d\n" mask
      else
        (* 大掩码：用 li + and（两条指令） *)
        (Printf.printf "    li t1, %d\n" mask;
         Printf.printf "    and t0, t0, t1\n")
    else
      (load_op "t1" z map;
       Printf.printf "    rem t0, t0, t1\n")
  else
    (load_op "t0" y map;
     load_op "t1" z map;
     Printf.printf "    rem t0, t0, t1\n");
  store_op "t0" x map

(* ============================================================ *)
(* 翻译单条 TAC 指令 *)

let emit_tac fname tac_inst map current_args =
  match tac_inst with
  | Assign (x, y) ->
      load_op "t0" y map;
      store_op "t0" x map

  | AssignBinOp (x, op, y, z) ->
      (match op with
       | Ast.Mul -> emit_mul x y z map
       | Ast.Div -> emit_div x y z map
       | Ast.Mod -> emit_mod x y z map
       | _ ->
           load_op "t0" y map;
           load_op "t1" z map;
           (match op with
            | Ast.Add -> Printf.printf "    add t0, t0, t1\n"
            | Ast.Sub -> Printf.printf "    sub t0, t0, t1\n"
            | Ast.Eq  -> Printf.printf "    sub t0, t0, t1\n    sltiu t0, t0, 1\n"
            | Ast.Ne  -> Printf.printf "    sub t0, t0, t1\n    sltu t0, zero, t0\n"
            | Ast.Lt  -> Printf.printf "    slt t0, t0, t1\n"
            | Ast.Gt  -> Printf.printf "    slt t0, t1, t0\n"
            | Ast.Le  -> Printf.printf "    slt t0, t1, t0\n    xori t0, t0, 1\n"
            | Ast.Ge  -> Printf.printf "    slt t0, t0, t1\n    xori t0, t0, 1\n"
            | Ast.And -> Printf.printf "    and t0, t0, t1\n"
            | Ast.Or  -> Printf.printf "    or t0, t0, t1\n"
            | Ast.Mul | Ast.Div | Ast.Mod -> assert false
           );
           store_op "t0" x map)

  | AssignUnOp (x, op, y) ->
      load_op "t0" y map;
      (match op with
       | Ast.Pos -> ()
       | Ast.Neg -> Printf.printf "    neg t0, t0\n"
       | Ast.Not -> Printf.printf "    seqz t0, t0\n");
      store_op "t0" x map

  | Goto l ->
      Printf.printf "    j %s\n" l

  | IfGoto (x, l) ->
      load_op "t0" x map;
      Printf.printf "    bnez t0, %s\n" l

  | IfNotGoto (x, l) ->
      load_op "t0" x map;
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
          load_op (Printf.sprintf "a%d" j) arg map
        else
          (load_op "t0" arg map;
           Printf.printf "    sw t0, %d(sp)\n" ((j - 8) * 4))
      ) args;
      
      Printf.printf "    call %s\n" callee;
      
      if extra_space > 0 then
        Printf.printf "    addi sp, sp, %d\n" extra_space;
        
      store_op "a0" dest map

  | Return (Some x) ->
      load_op "a0" x map;
      Printf.printf "    j .L_epilogue_%s\n" fname

  | Return None ->
      Printf.printf "    j .L_epilogue_%s\n" fname

(* ============================================================ *)
(* 翻译单个基本块 *)

(* 翻译单个基本块 - 遇到跳转指令后停止输出后续指令 *)
let emit_block fname (b: basic_block) map current_args =
  if b.label <> "entry" then
   Printf.printf "%s:\n" b.label;
  let rec emit_until_terminator = function
    | [] -> ()
    | inst :: rest ->
        emit_tac fname inst map current_args;
        (* 如果是终止指令，停止输出后续指令 *)
        match inst with
        | Return _ | Goto _ ->
            (* 后续指令是死代码，不输出 *)
            ()
        | _ ->
            emit_until_terminator rest
  in
  emit_until_terminator b.instrs

(* ============================================================ *)
(* 翻译单个函数 *)

let emit_function (f: ir_func) =
  let slots, map = compute_offsets f in
  let framesize = ((8 + slots * 4 + 15) / 16) * 16 in
  
  Printf.printf "    .globl %s\n" f.fname;
  Printf.printf "%s:\n" f.fname;
  
  Printf.printf "    addi sp, sp, -%d\n" framesize;
  Printf.printf "    sw ra, %d(sp)\n" (framesize - 4);
  Printf.printf "    sw fp, %d(sp)\n" (framesize - 8);
  Printf.printf "    addi fp, sp, %d\n" framesize;
  
  List.iteri (fun i name ->
    if i < 8 then
      let off = Hashtbl.find map (Var name) in
      Printf.printf "    sw a%d, %d(fp)\n" i off
  ) f.params;
  
  let current_args = ref [] in
  emit_block f.fname f.entry map current_args;
  List.iter (fun b -> emit_block f.fname b map current_args) f.blocks;
  
  Printf.printf ".L_epilogue_%s:\n" f.fname;
  Printf.printf "    lw ra, -4(fp)\n";
  Printf.printf "    lw fp, -8(fp)\n";
  Printf.printf "    addi sp, sp, %d\n" framesize;
  Printf.printf "    ret\n\n"

(* ============================================================ *)
(* 整个程序的代码生成主入口点 *)

let generate_riscv (prog: ir_program) =
  Printf.printf "    .text\n\n";

  List.iter (function
    | GlobalVar (name, Some v) ->
        Printf.printf "    .globl %s\n" name;
        Printf.printf "    .data\n";
        Printf.printf "    .align 2\n";
        Printf.printf "%s:\n" name;
        Printf.printf "    .word %d\n\n" v
    | GlobalVar (name, None) ->
        Printf.printf "    .globl %s\n" name;
        Printf.printf "    .data\n";
        Printf.printf "    .align 2\n";
        Printf.printf "%s:\n" name;
        Printf.printf "    .space 4\n\n"
    | Function f ->
        Printf.printf "    .text\n";
        emit_function f
  ) prog