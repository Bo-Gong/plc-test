    .text
    .text
    .globl add
add:
    addi sp, sp, -16
    sw fp, 8(sp)
    addi fp, sp, 16
    sw a0, -12(fp)
L0:
    lw t0, -12(fp)
    addi t0, t0, 10
    sw t0, -16(fp)
    lw a0, -16(fp)
    j .L_epilogue_add
.L_epilogue_add:
    lw fp, -8(fp)
    addi sp, sp, 16
    ret
    .text
    .globl main
main:
L1:
    li a0, 20
    ret
