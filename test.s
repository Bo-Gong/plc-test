    .text
    .text
    .globl add
add:
    addi sp, sp, -16
    sw fp, 8(sp)
    addi fp, sp, 16
    sw a0, -12(fp)
    lw t4, -12(fp)
L0:
    addi t0, t4, 0
    addi t0, t0, 10
    addi t5, t0, 0
    addi a0, t5, 0
    j .L_epilogue_add
.L_epilogue_add:
    lw fp, -8(fp)
    addi sp, sp, 16
    ret
    .text
    .globl main
main:
L1:
L2:
    li a0, 20
    ret
