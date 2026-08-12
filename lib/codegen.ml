(* lib/codegen.ml *)
open Ir

(* 唯一标签计数器，防止内联展开时的汇编标签冲突 *)
let inline_label_counter = ref 0

let gen_inline_label prefix =
  incr inline_label_counter;
  Printf.sprintf "%s_inline_%d" prefix !inline_label_counter

let power_of_two_shift n =
  if n <= 0 then None
  else
    let rec loop shift v =
      if v = 1 then Some shift
      else if v mod 2 <> 0 then None
      else loop (shift + 1) (v / 2)
    in
    loop 0 n

(* 辅助函数：列表切分 *)
let rec split_at n = function
  | xs when n <= 0 -> [], xs
  | [] -> [], []
  | x :: xs ->
      let prefix, suffix = split_at (n - 1) xs in
      x :: prefix, suffix

(* 计算栈槽偏移量映射表 *)
let compute_offsets (f: ir_func) =
  let local_slots = ref 0 in
  let map = Hashtbl.create 32 in
  
  (* 处理函数参数 *)
  List.iteri (fun i name ->
    if i < 8 then (
      incr local_slots;
      Hashtbl.add map (Var name) (-8 - 4 * !local_slots)
    ) else (
      (* 大于 8 个的参数由 Caller 压栈，在旧 SP（即当前 FP）的正偏移处 *)
      Hashtbl.add map (Var name) ((i - 8) * 4)
    )
  ) f.params;
  
  (* 处理其它未映射的局部变量 *)
  List.iter (fun name ->
    if not (Hashtbl.mem map (Var name)) then (
      incr local_slots;
      Hashtbl.add map (Var name) (-8 - 4 * !local_slots)
    )
  ) f.locals;
  
  (* 处理所有临时变量 *)
  for t = 0 to f.temps - 1 do
    incr local_slots;
    Hashtbl.add map (Temp t) (-8 - 4 * !local_slots)
  done;
  
  (!local_slots, map)

(* 将操作数的值加载到目标寄存器 *)
let load_op reg op map =
  match op with
  | Const n ->
      Printf.printf "    li %s, %d\n" reg n
  | Temp t ->
      let off = Hashtbl.find map (Temp t) in
      Printf.printf "    lw %s, %d(fp)\n" reg off
  | Var name ->
      if Hashtbl.mem map (Var name) then
        let off = Hashtbl.find map (Var name) in
        Printf.printf "    lw %s, %d(fp)\n" reg off
      else
        (* 找不到说明是全局变量 *)
        (Printf.printf "    la %s, %s\n" reg name;
         Printf.printf "    lw %s, 0(%s)\n" reg reg)

(* 将寄存器中的值写回到操作数对应的栈槽中 *)
let store_op reg op map =
  match op with
  | Const _ -> () (* 常量不可作为左值 *)
  | Temp t ->
      let off = Hashtbl.find map (Temp t) in
      Printf.printf "    sw %s, %d(fp)\n" reg off
  | Var name ->
      if Hashtbl.mem map (Var name) then
        let off = Hashtbl.find map (Var name) in
        Printf.printf "    sw %s, %d(fp)\n" reg off
      else
        (* 全局变量写回 *)
        (Printf.printf "    la t3, %s\n" name;
         Printf.printf "    sw %s, 0(t3)\n" reg)

(* ============================================================ *)
(* 辅助函数 *)
(* ============================================================ *)

(* 检查是否为 2 的幂 *)
let is_power_of_two n = n > 0 && (n land (n - 1)) = 0

(* 计算 2 的幂的指数 *)
let log2 n =
  let rec loop acc x =
    if x = 1 then acc
    else loop (acc + 1) (x / 2)
  in
  loop 0 n

(* ============================================================ *)
(* 优化的二元运算代码生成 *)
(* ============================================================ *)

(* 1. 加法优化 *)
let emit_add dest src1 src2 map =
  match src1, src2 with
  | Const 0, nonconst ->  (* x + 0 = x *)
      load_op "t0" nonconst map;
      store_op "t0" dest map
  | nonconst, Const 0 ->  (* 0 + x = x *)
      load_op "t0" nonconst map;
      store_op "t0" dest map
  
  | Const c, nonconst when c >= -2048 && c <= 2047 ->
      (* 立即数在 12 位范围内，使用 addi *)
      load_op "t0" nonconst map;
      Printf.printf "    addi t0, t0, %d\n" c;
      store_op "t0" dest map
  | nonconst, Const c when c >= -2048 && c <= 2047 ->
      load_op "t0" nonconst map;
      Printf.printf "    addi t0, t0, %d\n" c;
      store_op "t0" dest map
  
  | Const a, Const b ->
      (* 常量折叠 *)
      let result = a + b in
      Printf.printf "    li t0, %d\n" result;
      store_op "t0" dest map
  
  | _ ->
      (* 通用加法 *)
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    add t0, t0, t1\n";
      store_op "t0" dest map

(* 2. 减法优化 *)
let emit_sub dest src1 src2 map =
  match src1, src2 with
  | nonconst, Const 0 ->
      (* x - 0 = x *)
      load_op "t0" nonconst map;
      store_op "t0" dest map
  
  | Const 0, nonconst ->
      (* 0 - x = -x *)
      load_op "t0" nonconst map;
      Printf.printf "    neg t0, t0\n";
      store_op "t0" dest map
  
  | nonconst, Const c when c >= -2048 && c <= 2047 ->
      (* x - c = x + (-c)，使用 addi *)
      load_op "t0" nonconst map;
      Printf.printf "    addi t0, t0, %d\n" (-c);
      store_op "t0" dest map
  
  | Const a, Const b ->
      let result = a - b in
      Printf.printf "    li t0, %d\n" result;
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    sub t0, t0, t1\n";
      store_op "t0" dest map

(* 3. 乘法优化：2 的幂用移位 *)
let emit_mul dest src1 src2 map =
  match src1, src2 with
  | Const 0, _ ->
      (* 乘以 0 = 0 *)
      Printf.printf "    li t0, 0\n";
      store_op "t0" dest map
  | _, Const 0 ->
      Printf.printf "    li t0, 0\n";
      store_op "t0" dest map
  
  | Const 1, nonconst ->
      (* 乘以 1 = 自身 *)
      load_op "t0" nonconst map;
      store_op "t0" dest map
  | nonconst, Const 1 ->
      load_op "t0" nonconst map;
      store_op "t0" dest map
  
  | Const (-1), nonconst ->
      (* 乘以 -1 = 取负 *)
      load_op "t0" nonconst map;
      Printf.printf "    neg t0, t0\n";
      store_op "t0" dest map
  | nonconst, Const (-1) ->
      load_op "t0" nonconst map;
      Printf.printf "    neg t0, t0\n";
      store_op "t0" dest map
  
  | Const c, nonconst ->
      let abs_c = abs c in
      if is_power_of_two abs_c then
        (let shift = log2 abs_c in
        load_op "t0" nonconst map;
        if shift = 0 then
          Printf.printf "    mv t0, t0\n"
        else
          Printf.printf "    slli t0, t0, %d\n" shift;
        if c < 0 then
          Printf.printf "    neg t0, t0\n";
        store_op "t0" dest map)
      else if abs_c < 16 then
        (* 小常量用加法展开 *)
        (load_op "t0" nonconst map;
        Printf.printf "    mv t1, t0\n";
        for _ = 1 to abs_c - 1 do
          Printf.printf "    add t1, t1, t0\n"
        done;
        Printf.printf "    mv t0, t1\n";
        if c < 0 then
          Printf.printf "    neg t0, t0\n";
        store_op "t0" dest map)
      else
        (* 其他常量使用 MUL 指令 *)
        (load_op "t0" src1 map;
        load_op "t1" src2 map;
        Printf.printf "    mul t0, t0, t1\n";
        store_op "t0" dest map)
  | nonconst, Const c ->
      let abs_c = abs c in
      if is_power_of_two abs_c then
        (let shift = log2 abs_c in
        load_op "t0" nonconst map;
        if shift = 0 then
          Printf.printf "    mv t0, t0\n"
        else
          Printf.printf "    slli t0, t0, %d\n" shift;
        if c < 0 then
          Printf.printf "    neg t0, t0\n";
        store_op "t0" dest map)
      else if abs_c < 16 then
        (* 小常量用加法展开 *)
        (load_op "t0" nonconst map;
        Printf.printf "    mv t1, t0\n";
        for _ = 1 to abs_c - 1 do
          Printf.printf "    add t1, t1, t0\n"
        done;
        Printf.printf "    mv t0, t1\n";
        if c < 0 then
          Printf.printf "    neg t0, t0\n";
        store_op "t0" dest map)
      else
        (* 其他常量使用 MUL 指令 *)
        (load_op "t0" src1 map;
        load_op "t1" src2 map;
        Printf.printf "    mul t0, t0, t1\n";
        store_op "t0" dest map)
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    mul t0, t0, t1\n";
      store_op "t0" dest map

(* 4. 除法优化：除以 2 的幂用移位 *)
let emit_div dest src1 src2 map =
  match src1, src2 with
  | _, Const 0 ->
      Printf.printf "    li t0, 0\n";
      store_op "t0" dest map
  
  | nonconst, Const 1 ->
      load_op "t0" nonconst map;
      store_op "t0" dest map
  
  | nonconst, Const (-1) ->
      load_op "t0" nonconst map;
      Printf.printf "    neg t0, t0\n";
      store_op "t0" dest map
  
  | nonconst, Const c when c > 1 && is_power_of_two c ->
      let shift = log2 c in
      load_op "t0" nonconst map;
      Printf.printf "    srai t0, t0, %d\n" shift;
      store_op "t0" dest map
  
  | Const a, Const b when b <> 0 ->
      let result = a / b in
      Printf.printf "    li t0, %d\n" result;
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    div t0, t0, t1\n";
      store_op "t0" dest map

(* 5. 取模优化：模 2 的幂用掩码 *)
let emit_mod dest src1 src2 map =
  match src1, src2 with
  | _, Const 0 ->
      Printf.printf "    li t0, 0\n";
      store_op "t0" dest map
  
  | _, Const 1 ->
      Printf.printf "    li t0, 0\n";
      store_op "t0" dest map
  | _, Const (-1) ->
      Printf.printf "    li t0, 0\n";
      store_op "t0" dest map
  
  | nonconst, Const c when c > 1 && is_power_of_two c ->
      load_op "t0" nonconst map;
      Printf.printf "    andi t0, t0, %d\n" (c - 1);
      store_op "t0" dest map
  
  | Const a, Const b when b <> 0 ->
      let result = a mod b in
      Printf.printf "    li t0, %d\n" result;
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    rem t0, t0, t1\n";
      store_op "t0" dest map

(* 6. 相等比较优化 *)
let emit_eq dest src1 src2 map =
  match src1, src2 with
  | Const 0, nonconst ->
      load_op "t0" nonconst map;
      Printf.printf "    seqz t0, t0\n";
      store_op "t0" dest map
  | nonconst, Const 0 ->
      load_op "t0" nonconst map;
      Printf.printf "    seqz t0, t0\n";
      store_op "t0" dest map
  
  | Const a, Const b ->
      Printf.printf "    li t0, %d\n" (if a = b then 1 else 0);
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    xor t0, t0, t1\n";
      Printf.printf "    seqz t0, t0\n";
      store_op "t0" dest map

(* 7. 不等比较优化 *)
let emit_ne dest src1 src2 map =
  match src1, src2 with
  | Const 0, nonconst ->
      load_op "t0" nonconst map;
      Printf.printf "    snez t0, t0\n";
      store_op "t0" dest map
  | nonconst, Const 0 ->
      load_op "t0" nonconst map;
      Printf.printf "    snez t0, t0\n";
      store_op "t0" dest map
  
  | Const a, Const b ->
      Printf.printf "    li t0, %d\n" (if a <> b then 1 else 0);
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    xor t0, t0, t1\n";
      Printf.printf "    snez t0, t0\n";
      store_op "t0" dest map

(* 8. 小于比较优化 *)
let emit_lt dest src1 src2 map =
  match src1, src2 with
  | Const 0, nonconst ->
      load_op "t0" nonconst map;
      Printf.printf "    slti t0, t0, 1\n";
      Printf.printf "    xori t0, t0, 1\n";
      store_op "t0" dest map
  
  | nonconst, Const 0 ->
      load_op "t0" nonconst map;
      Printf.printf "    srli t0, t0, 31\n";
      store_op "t0" dest map
  
  | nonconst, Const c when c >= -2048 && c <= 2047 ->
      load_op "t0" nonconst map;
      Printf.printf "    slti t0, t0, %d\n" c;
      store_op "t0" dest map
  
  | Const a, Const b ->
      Printf.printf "    li t0, %d\n" (if a < b then 1 else 0);
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    slt t0, t0, t1\n";
      store_op "t0" dest map

(* 9. 大于比较优化 *)
let emit_gt dest src1 src2 map =
  match src1, src2 with
  | nonconst, Const 0 ->
      load_op "t0" nonconst map;
      Printf.printf "    slti t0, t0, 1\n";
      Printf.printf "    xori t0, t0, 1\n";
      store_op "t0" dest map
  
  | Const 0, nonconst ->
      load_op "t0" nonconst map;
      Printf.printf "    srli t0, t0, 31\n";
      store_op "t0" dest map
  
  | nonconst, Const c when c >= -2048 && c <= 2047 ->
      load_op "t0" nonconst map;
      Printf.printf "    addi t0, t0, %d\n" (-(c + 1));
      Printf.printf "    slti t0, t0, 1\n";
      Printf.printf "    xori t0, t0, 1\n";
      store_op "t0" dest map
  
  | Const a, Const b ->
      Printf.printf "    li t0, %d\n" (if a > b then 1 else 0);
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    slt t0, t1, t0\n";
      store_op "t0" dest map

(* 10. 小于等于优化 *)
let emit_le dest src1 src2 map =
  match src1, src2 with
  | nonconst, Const 0 ->
      load_op "t0" nonconst map;
      Printf.printf "    slti t0, t0, 1\n";
      store_op "t0" dest map
  
  | Const 0, nonconst ->
      load_op "t0" nonconst map;
      Printf.printf "    srli t0, t0, 31\n";
      Printf.printf "    xori t0, t0, 1\n";
      store_op "t0" dest map
  
  | nonconst, Const c when c >= -2048 && c <= 2047 ->
      load_op "t0" nonconst map;
      Printf.printf "    slti t0, t0, %d\n" (c + 1);
      store_op "t0" dest map
  
  | Const a, Const b ->
      Printf.printf "    li t0, %d\n" (if a <= b then 1 else 0);
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    slt t0, t1, t0\n";
      Printf.printf "    xori t0, t0, 1\n";
      store_op "t0" dest map

(* 11. 大于等于优化 *)
let emit_ge dest src1 src2 map =
  match src1, src2 with
  | nonconst, Const 0 ->
      load_op "t0" nonconst map;
      Printf.printf "    srli t0, t0, 31\n";
      Printf.printf "    xori t0, t0, 1\n";
      store_op "t0" dest map
  
  | Const 0, nonconst ->
      load_op "t0" nonconst map;
      Printf.printf "    slti t0, t0, 1\n";
      store_op "t0" dest map
  
  | nonconst, Const c when c >= -2048 && c <= 2047 ->
      load_op "t0" nonconst map;
      Printf.printf "    addi t0, t0, %d\n" (-(c - 1));
      Printf.printf "    slti t0, t0, 1\n";
      Printf.printf "    xori t0, t0, 1\n";
      store_op "t0" dest map
  
  | Const a, Const b ->
      Printf.printf "    li t0, %d\n" (if a >= b then 1 else 0);
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    slt t0, t0, t1\n";
      Printf.printf "    xori t0, t0, 1\n";
      store_op "t0" dest map

(* 12. 逻辑与优化 *)
let emit_and dest src1 src2 map =
  match src1, src2 with
  | Const 0, _ ->
      Printf.printf "    li t0, 0\n";
      store_op "t0" dest map
  | _, Const 0 ->
      Printf.printf "    li t0, 0\n";
      store_op "t0" dest map
  
  | Const 1, nonconst ->
      load_op "t0" nonconst map;
      Printf.printf "    snez t0, t0\n";
      store_op "t0" dest map
  | nonconst, Const 1 ->
      load_op "t0" nonconst map;
      Printf.printf "    snez t0, t0\n";
      store_op "t0" dest map
  
  | Const a, Const b ->
      Printf.printf "    li t0, %d\n" (if a <> 0 && b <> 0 then 1 else 0);
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    and t0, t0, t1\n";
      Printf.printf "    snez t0, t0\n";
      store_op "t0" dest map

(* 13. 逻辑或优化 *)
let emit_or dest src1 src2 map =
  match src1, src2 with
  | Const 0, nonconst ->
      load_op "t0" nonconst map;
      Printf.printf "    snez t0, t0\n";
      store_op "t0" dest map
  | nonconst, Const 0 ->
      load_op "t0" nonconst map;
      Printf.printf "    snez t0, t0\n";
      store_op "t0" dest map
  
  | Const 1, _ ->
      Printf.printf "    li t0, 1\n";
      store_op "t0" dest map
  | _, Const 1 ->
      Printf.printf "    li t0, 1\n";
      store_op "t0" dest map
  
  | Const a, Const b ->
      Printf.printf "    li t0, %d\n" (if a <> 0 || b <> 0 then 1 else 0);
      store_op "t0" dest map
  
  | _ ->
      load_op "t0" src1 map;
      load_op "t1" src2 map;
      Printf.printf "    or t0, t0, t1\n";
      Printf.printf "    snez t0, t0\n";
      store_op "t0" dest map

(* 14. 二元运算分发 *)
let emit_binop dest op src1 src2 map =
  match op with
  | Ast.Add -> emit_add dest src1 src2 map
  | Ast.Sub -> emit_sub dest src1 src2 map
  | Ast.Mul -> emit_mul dest src1 src2 map
  | Ast.Div -> emit_div dest src1 src2 map
  | Ast.Mod -> emit_mod dest src1 src2 map
  | Ast.Eq -> emit_eq dest src1 src2 map
  | Ast.Ne -> emit_ne dest src1 src2 map
  | Ast.Lt -> emit_lt dest src1 src2 map
  | Ast.Gt -> emit_gt dest src1 src2 map
  | Ast.Le -> emit_le dest src1 src2 map
  | Ast.Ge -> emit_ge dest src1 src2 map
  | Ast.And -> emit_and dest src1 src2 map
  | Ast.Or -> emit_or dest src1 src2 map

(* ============================================================ *)
(* 翻译单条 TAC 指令 *)
(* ============================================================ *)

let emit_tac fname tac_inst map current_args =
  match tac_inst with
  | Assign (x, y) ->
      load_op "t0" y map;
      store_op "t0" x map

  | AssignBinOp (x, op, y, z) ->
      emit_binop x op y z map

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

(* 翻译单个基本块 *)
let emit_block fname (b: basic_block) map current_args =
  if b.label <> "entry" then
   Printf.printf "%s:\n" b.label;
  let rec emit_until_terminator = function
    | [] -> ()
    | inst :: rest ->
        emit_tac fname inst map current_args;
        match inst with
        | Return _ | Goto _ -> ()
        | _ -> emit_until_terminator rest
  in
  emit_until_terminator b.instrs

(* 翻译单个函数 *)
let emit_function (f: ir_func) =
  let slots, map = compute_offsets f in
  let framesize = ((8 + slots * 4 + 15) / 16) * 16 in
  
  Printf.printf "    .globl %s\n" f.fname;
  Printf.printf "%s:\n" f.fname;
  
  (* 函数序言 *)
  Printf.printf "    addi sp, sp, -%d\n" framesize;
  Printf.printf "    sw ra, %d(sp)\n" (framesize - 4);
  Printf.printf "    sw fp, %d(sp)\n" (framesize - 8);
  Printf.printf "    addi fp, sp, %d\n" framesize;
  
  (* 保存参数 *)
  List.iteri (fun i name ->
    if i < 8 then
      let off = Hashtbl.find map (Var name) in
      Printf.printf "    sw a%d, %d(fp)\n" i off
  ) f.params;

  if f.entry.label <> "entry" then
    Printf.printf "%s:\n" f.entry.label;
  
  let current_args = ref [] in
  emit_block f.fname f.entry map current_args;
  List.iter (fun b -> emit_block f.fname b map current_args) f.blocks;
  
  (* 函数结语 *)
  Printf.printf ".L_epilogue_%s:\n" f.fname;
  Printf.printf "    lw ra, -4(fp)\n";
  Printf.printf "    lw fp, -8(fp)\n";
  Printf.printf "    addi sp, sp, %d\n" framesize;
  Printf.printf "    ret\n\n"

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