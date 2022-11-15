.text
	beqz $a0, init_end
	lw $a0, 0($a1)
	jal atoi
init_end:
	sw $v0, 0($sp)
	subi $sp, $sp, 4
	jal main
	li $v0, 10
	syscall
main:
	li $t3, 2
	li $t2, 3
	addi $t3, $t3, 1
	add $t2, $t3, $t2
	li $t2, 1
	slt $t3, $t3, $t2
#built-in atoi
atoi:
	li $v0, 0
atoi_loop:
	lbu $t0, 0($a0)
	beqz $t0, atoi_end
	addi $t0, $t0, -48
	bltz $t0, atoi_error
	bge $t0, 10, atoi_error
	mul $v0, $v0, 10
	add $v0, $v0, $t0
	addi $a0, $a0, 1
	b atoi_loop
atoi_error:
	li $v0, 10
	syscall
atoi_end:
	jr $ra
.data
