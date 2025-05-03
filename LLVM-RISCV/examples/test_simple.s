	.text
	.attribute	4, 16
	.attribute	5, "rv64i2p1_m2p0_zmmul1p0"
	.file	"test_basics.ll"
	.globl	gin                             # -- Begin function gin
	.p2align	2
	.type	gin,@function
gin:                                    # @gin
	.cfi_startproc
# %bb.0:                                # %entry
	add	a1, a0, a0
	xor	a2, a1, a0
	mul	a3, a2, a2
	or	a3, a3, a1
	sub	a3, a3, a2
	xor	a0, a3, a0
	add	a1, a0, a1
	slli	a3, a1, 5
	sub	a3, a3, a1
	or	a2, a3, a2
	sub	a0, a2, a0
	ret
.Lfunc_end0:
	.size	gin, .Lfunc_end0-gin
	.cfi_endproc
                                        # -- End function
	.globl	main                            # -- Begin function main
	.p2align	2
	.type	main,@function
main:                                   # @main
	.cfi_startproc
# %bb.0:
	addi	sp, sp, -16
	.cfi_def_cfa_offset 16
	sd	ra, 8(sp)                       # 8-byte Folded Spill
	sd	s0, 0(sp)                       # 8-byte Folded Spill
	.cfi_offset ra, -8
	.cfi_offset s0, -16
	mv	s0, a0
	call	gin
	add	a0, a0, s0
	ld	ra, 8(sp)                       # 8-byte Folded Reload
	ld	s0, 0(sp)                       # 8-byte Folded Reload
	addi	sp, sp, 16
	ret
.Lfunc_end1:
	.size	main, .Lfunc_end1-main
	.cfi_endproc
                                        # -- End function
	.section	".note.GNU-stack","",@progbits
