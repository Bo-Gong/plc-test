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

(* 翻译单条 TAC 指令 *)
let emit_tac fname tac_inst map current_args =
  match tac_inst with
  | Assign (x, y) ->
      load_op "t0" y map;
      store_op "t0" x map
  | AssignBinOp (x, op, y, z) ->
      load_op "t0" y map;
      load_op "t1" z map;
      (match op with
       | Ast.Add -> Printf.printf "    add t0, t0, t1\n"
       | Ast.Sub -> Printf.printf "    sub t0, t0, t1\n"
       | Ast.Mul -> Printf.printf "    mul t0, t0, t1\n"
       | Ast.Div -> Printf.printf "    div t0, t0, t1\n"
       | Ast.Mod -> Printf.printf "    rem t0, t0, t1\n"
       | Ast.Eq  -> Printf.printf "    sub t0, t0, t1\n    seqz t0, t0\n"
       | Ast.Ne  -> Printf.printf "    sub t0, t0, t1\n    snez t0, t0\n"
       | Ast.Lt  -> Printf.printf "    slt t0, t0, t1\n"
       | Ast.Gt  -> Printf.printf "    slt t0, t1, t0\n"
       | Ast.Le  -> Printf.printf "    slt t0, t1, t0\n    xori t0, t0, 1\n"
       | Ast.Ge  -> Printf.printf "    slt t0, t0, t1\n    xori t0, t0, 1\n"
       | Ast.And -> Printf.printf "    and t0, t0, t1\n"
       | Ast.Or  -> Printf.printf "    or t0, t0, t1\n");
      store_op "t0" x map

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
      (* 基本块外部有单独标签逻辑，通常 TAC 中的 Label 可在此打印或被块接管 *)
      Printf.printf "%s:\n" l

  | Param x ->
      current_args := x :: !current_args

  | Call (dest, callee, nargs) ->
      let call_args, rem = split_at nargs !current_args in
      current_args := rem;
      (* FIX: IR 中 Params 以"最后一个实参在前"的流序出现，这里用 prepend
         累积后恰好还原成源码顺序（首个参数在头），再按 a0..a7 顺序消费，
         不要再反转。optimize.ml 的尾递归改写同样依赖这一约定。 *)
      let args = call_args in
      
      (* 如果调用的函数参数超过 8 个，需要为其在 sp 低位开辟动态传参空间 *)
      let extra_space = if nargs > 8 then ((nargs - 8) * 4 + 15) / 16 * 16 else 0 in
      if extra_space > 0 then
        Printf.printf "    addi sp, sp, -%d\n" extra_space;
        
      (* 传递参数 *)
      List.iteri (fun j arg ->
        if j < 8 then
          load_op (Printf.sprintf "a%d" j) arg map
        else
          (load_op "t0" arg map;
           Printf.printf "    sw t0, %d(sp)\n" ((j - 8) * 4))
      ) args;
      
      (* 执行调用 *)
      Printf.printf "    call %s\n" callee;
      
      (* 恢复动态开辟的传参栈空间 *)
      if extra_space > 0 then
        Printf.printf "    addi sp, sp, %d\n" extra_space;
        
      (* 保存返回值 *)
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
        (* 如果是终止指令，停止输出后续指令 *)
        match inst with
        | Return _ | Goto _ ->
            (* 后续指令是死代码，不输出 *)
            ()
        | _ ->
            emit_until_terminator rest
  in
  emit_until_terminator b.instrs
(* 翻译单个函数 *)
let emit_function (f: ir_func) =
  let slots, map = compute_offsets f in
  (* 计算对齐 16 字节后的帧大小（8 字节用于保存 ra 和 fp） *)
  let framesize = ((8 + slots * 4 + 15) / 16) * 16 in
  
  Printf.printf "    .globl %s\n" f.fname;
  Printf.printf "%s:\n" f.fname;
  
  (* 函数序言 (Prologue) *)
  Printf.printf "    addi sp, sp, -%d\n" framesize;
  Printf.printf "    sw ra, %d(sp)\n" (framesize - 4);
  Printf.printf "    sw fp, %d(sp)\n" (framesize - 8);
  Printf.printf "    addi fp, sp, %d\n" framesize;
  
  (* 将传进来的前 8 个参数从寄存器转存到本地分配的栈槽 *)
  List.iteri (fun i name ->
    if i < 8 then
      let off = Hashtbl.find map (Var name) in
      Printf.printf "    sw a%d, %d(fp)\n" i off
  ) f.params;

  (* 打印函数入口标签：尾递归优化会跳回该标签。
     未优化时入口标签统一为 "entry"，无需打印，保持原输出。 *)
  if f.entry.label <> "entry" then
    Printf.printf "%s:\n" f.entry.label;
  
  (* 函数体翻译 (Body) *)
  let current_args = ref [] in
  emit_block f.fname f.entry map current_args;
  List.iter (fun b -> emit_block f.fname b map current_args) f.blocks;
  
  (* 函数结语 (Epilogue) *)
  Printf.printf ".L_epilogue_%s:\n" f.fname;
  Printf.printf "    lw ra, -4(fp)\n";
  Printf.printf "    lw fp, -8(fp)\n";
  Printf.printf "    addi sp, sp, %d\n" framesize;
  Printf.printf "    ret\n\n"

(* 整个程序的代码生成主入口点 *)
let generate_riscv (prog: ir_program) =
  (* 打印全局段声明 *)
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
