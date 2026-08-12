Semantic check success!
global A = 10
global B = 20

func test1(x$0):
  locals: [x$0]
  temps: 2

L5:
  t0 = x$0 + x$0
  t1 = t0 + 5
  return t1

func test2(x$0):
  locals: [x$0]
  temps: 3

L6:
  t0 = x$0 + 10
  t1 = t0 + t0
  t2 = t1 - 5
  return t2

func test3(x$0):
  locals: [result$2, a$1, x$0]
  temps: 4

L7:
  t0 = x$0 + x$0
  a$1 = t0
  t1 = t0 > 10
  ifFalse t1 goto L0
  t2 = t0 + 5
  result$2 = t2
  goto L1
L0:
  t3 = a$1 - 5
  result$2 = t3
L1:
  return result$2

func test4(n$0):
  locals: [i$2, sum$1, n$0]
  temps: 4

L8:
  sum$1 = 0
  i$2 = 0
L2:
  t0 = i$2 < n$0
  ifFalse t0 goto L4
L3:
  t1 = i$2 + i$2
  t2 = sum$1 + t1
  sum$1 = t2
  t3 = i$2 + 1
  i$2 = t3
  goto L2
L4:
  return sum$1

func test5():
  locals: []
  temps: 0

L9:
  return 30

func helper(x$0):
  locals: [x$0]
  temps: 1

L10:
  t0 = x$0 + 5
  return t0

func test6(x$0):
  locals: [x$0]
  temps: 2

L11:
  param x$0
  t0 = call helper, 1
  t1 = t0 + t0
  return t1

func main():
  locals: []
  temps: 0

L12:
  return 141
    .text

    .globl A
    .data
    .align 2
A:
    .word 10

    .globl B
    .data
    .align 2
B:
    .word 20

    .text
    .globl test1
test1:
    addi sp, sp, -32
    sw ra, 28(sp)
    sw fp, 24(sp)
    addi fp, sp, 32
    sw a0, -12(fp)
L5:
L5:
    lw t0, -12(fp)
    lw t1, -12(fp)
    add t0, t0, t1
    sw t0, -16(fp)
    lw t0, -16(fp)
    li t1, 5
    add t0, t0, t1
    sw t0, -20(fp)
    lw a0, -20(fp)
    j .L_epilogue_test1
.L_epilogue_test1:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 32
    ret

    .text
    .globl test2
test2:
    addi sp, sp, -32
    sw ra, 28(sp)
    sw fp, 24(sp)
    addi fp, sp, 32
    sw a0, -12(fp)
L6:
L6:
    lw t0, -12(fp)
    li t1, 10
    add t0, t0, t1
    sw t0, -16(fp)
    lw t0, -16(fp)
    lw t1, -16(fp)
    add t0, t0, t1
    sw t0, -20(fp)
    lw t0, -20(fp)
    li t1, 5
    sub t0, t0, t1
    sw t0, -24(fp)
    lw a0, -24(fp)
    j .L_epilogue_test2
.L_epilogue_test2:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 32
    ret

    .text
    .globl test3
test3:
    addi sp, sp, -48
    sw ra, 44(sp)
    sw fp, 40(sp)
    addi fp, sp, 48
    sw a0, -12(fp)
L7:
L7:
    lw t0, -12(fp)
    lw t1, -12(fp)
    add t0, t0, t1
    sw t0, -24(fp)
    lw t0, -24(fp)
    sw t0, -20(fp)
    lw t0, -24(fp)
    li t1, 10
    slt t0, t1, t0
    sw t0, -28(fp)
    lw t0, -28(fp)
    beqz t0, L0
    lw t0, -24(fp)
    li t1, 5
    add t0, t0, t1
    sw t0, -32(fp)
    lw t0, -32(fp)
    sw t0, -16(fp)
    j L1
L0:
    lw t0, -20(fp)
    li t1, 5
    sub t0, t0, t1
    sw t0, -36(fp)
    lw t0, -36(fp)
    sw t0, -16(fp)
L1:
    lw a0, -16(fp)
    j .L_epilogue_test3
.L_epilogue_test3:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 48
    ret

    .text
    .globl test4
test4:
    addi sp, sp, -48
    sw ra, 44(sp)
    sw fp, 40(sp)
    addi fp, sp, 48
    sw a0, -12(fp)
L8:
L8:
    li t0, 0
    sw t0, -20(fp)
    li t0, 0
    sw t0, -16(fp)
L2:
    lw t0, -16(fp)
    lw t1, -12(fp)
    slt t0, t0, t1
    sw t0, -24(fp)
    lw t0, -24(fp)
    beqz t0, L4
L3:
    lw t0, -16(fp)
    lw t1, -16(fp)
    add t0, t0, t1
    sw t0, -28(fp)
    lw t0, -20(fp)
    lw t1, -28(fp)
    add t0, t0, t1
    sw t0, -32(fp)
    lw t0, -32(fp)
    sw t0, -20(fp)
    lw t0, -16(fp)
    li t1, 1
    add t0, t0, t1
    sw t0, -36(fp)
    lw t0, -36(fp)
    sw t0, -16(fp)
    j L2
L4:
    lw a0, -20(fp)
    j .L_epilogue_test4
.L_epilogue_test4:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 48
    ret

    .text
    .globl test5
test5:
    addi sp, sp, -16
    sw ra, 12(sp)
    sw fp, 8(sp)
    addi fp, sp, 16
L9:
L9:
    li a0, 30
    j .L_epilogue_test5
.L_epilogue_test5:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 16
    ret

    .text
    .globl helper
helper:
    addi sp, sp, -16
    sw ra, 12(sp)
    sw fp, 8(sp)
    addi fp, sp, 16
    sw a0, -12(fp)
L10:
L10:
    lw t0, -12(fp)
    li t1, 5
    add t0, t0, t1
    sw t0, -16(fp)
    lw a0, -16(fp)
    j .L_epilogue_helper
.L_epilogue_helper:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 16
    ret

    .text
    .globl test6
test6:
    addi sp, sp, -32
    sw ra, 28(sp)
    sw fp, 24(sp)
    addi fp, sp, 32
    sw a0, -12(fp)
L11:
L11:
    lw a0, -12(fp)
    call helper
    sw a0, -16(fp)
    lw t0, -16(fp)
    lw t1, -16(fp)
    add t0, t0, t1
    sw t0, -20(fp)
    lw a0, -20(fp)
    j .L_epilogue_test6
.L_epilogue_test6:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 32
    ret

    .text
    .globl main
main:
    addi sp, sp, -16
    sw ra, 12(sp)
    sw fp, 8(sp)
    addi fp, sp, 16
L12:
L12:
    li a0, 141
    j .L_epilogue_main
.L_epilogue_main:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 16
    ret

