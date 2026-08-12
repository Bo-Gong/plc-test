	.file	"test.c"
	.text
	.section	.text.startup,"ax",@progbits
	.p2align 4
	.globl	main
	.type	main, @function
main:
.LFB0:
	.cfi_startproc
	endbr64
	movl	$40, %eax
	ret
	.cfi_endproc
.LFE0:
	.size	main, .-main
	.globl	C
	.section	.rodata
	.align 4
	.type	C, @object
	.size	C, 4
C:
	.long	30
	.globl	B
	.align 4
	.type	B, @object
	.size	B, 4
B:
	.long	20
	.globl	A
	.align 4
	.type	A, @object
	.size	A, 4
A:
	.long	10
	.ident	"GCC: (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0"
	.section	.note.GNU-stack,"",@progbits
	.section	.note.gnu.property,"a"
	.align 8
	.long	1f - 0f
	.long	4f - 1f
	.long	5
0:
	.string	"GNU"
1:
	.align 8
	.long	0xc0000002
	.long	3f - 2f
2:
	.long	0x3
3:
	.align 8
4:
