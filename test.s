Semantic check success!

func add(a$0, b$1):
  locals: []
  temps: 1

L0:
  t0 = a$0 + b$1
  return t0

func main():
  locals: []
  temps: 0

L1:
  return 18
    .text
    .text
    .globl add
add:
    addi sp, sp, -32
    sw ra, 28(sp)
    sw fp, 24(sp)
    addi fp, sp, 32
    sw a0, -12(fp)
    sw a1, -16(fp)
L0:
    lw t0, -12(fp)
    lw t1, -16(fp)
    add t0, t0, t1
    sw t0, -20(fp)
    lw a0, -20(fp)
    j .L_epilogue_add
.L_epilogue_add:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 32
    ret
    .text
    .globl main
main:
L1:
    li a0, 18
    ret
