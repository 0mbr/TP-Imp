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
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	subi $sp, $sp, 4
	addi $fp, $sp, 8
	addi $sp, $sp, 0
	li $t2, 5
	li $t3, 8
	slt $t3, $t2, $t3
	bne $t3, 0, __lab_2
	li $t2, 1
	b __lab_3
__lab_2:
	move $t2, $t2
__lab_3:
	li $t2, 3
	li $t0, 0
	move $sp, $fp
	lw $ra, -4($fp)
	lw $fp, 0($fp)
	jr $ra
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
