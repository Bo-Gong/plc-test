Semantic check success!

func main():
  locals: [sum$5, i$0]
  temps: 5

L3:
  i$0 = 0
  sum$5 = 0
L0:
  t0 = i$0 < 100
  ifFalse t0 goto L2
L1:
  t2 = sum$5 + 15
  t3 = t2 + 2
  sum$5 = t3
  t4 = i$0 + 1
  i$0 = t4
  goto L0
L2:
  return sum$5
    .text
    .text
    .globl main
main:
    addi sp, sp, -48
    sw ra, 44(sp)
    sw fp, 40(sp)
    addi fp, sp, 48
L3:
    li t0, 0
    sw t0, -16(fp)
    li t0, 0
    sw t0, -12(fp)
L0:
    lw t0, -16(fp)
    slti t0, t0, 100
    sw t0, -20(fp)
    lw t0, -20(fp)
    beqz t0, L2
L1:
    lw t0, -12(fp)
    addi t0, t0, 15
    sw t0, -28(fp)
    lw t0, -28(fp)
    addi t0, t0, 2
    sw t0, -32(fp)
    lw t0, -32(fp)
    sw t0, -12(fp)
    lw t0, -16(fp)
    addi t0, t0, 1
    sw t0, -36(fp)
    lw t0, -36(fp)
    sw t0, -16(fp)
    j L0
L2:
    lw a0, -12(fp)
    j .L_epilogue_main
.L_epilogue_main:
    lw ra, -4(fp)
    lw fp, -8(fp)
    addi sp, sp, 48
    ret
