Semantic check success!

func add(a$0, b$1):
  locals: []
  temps: 1

L0:
  t0 = a$0 * 4
  return t0

func main():
  locals: [d$3, c$2, b$1, a$0, inl$1000000, inl$1000001]
  temps: 4

L1:
  a$0 = 10
  t0 = 20
  b$1 = 20
  t1 = 30
  c$2 = 30
  inl$1000000 = 10
  inl$1000001 = 30
L3:
  t2 = 40
  t3 = 40
L2:
  d$3 = 40
  return 40
    .text
    .text
    .globl add
add:
    addi sp, sp, -32
    sw fp, 24(sp)
    addi fp, sp, 32
    sw a0, -12(fp)
    sw a1, -16(fp)
    lw t4, -12(fp)
L0:
    addi t0, t4, 0
    slli t0, t0, 2
    addi t5, t0, 0
    addi a0, t5, 0
    j .L_epilogue_add
.L_epilogue_add:
    lw fp, -8(fp)
    addi sp, sp, 32
    ret
    .text
    .globl main
main:
    addi sp, sp, -48
    sw fp, 40(sp)
    addi fp, sp, 48
L1:
    li t0, 10
    sw t0, -24(fp)
    li t0, 20
    sw t0, -36(fp)
    li t0, 20
    sw t0, -20(fp)
    li t0, 30
    sw t0, -40(fp)
    li t0, 30
    sw t0, -16(fp)
    li t0, 10
    sw t0, -28(fp)
    li t0, 30
    sw t0, -32(fp)
L3:
    li t0, 40
    sw t0, -44(fp)
    li t0, 40
    sw t0, -48(fp)
L2:
    li t0, 40
    sw t0, -12(fp)
    li a0, 40
    j .L_epilogue_main
.L_epilogue_main:
    lw fp, -8(fp)
    addi sp, sp, 48
    ret
