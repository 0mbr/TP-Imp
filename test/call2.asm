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
	sw $t2, 0($sp)
	sw $t3, -4($sp)
	sw $t4, -8($sp)
	sw $t5, -12($sp)
	sw $t6, -16($sp)
	sw $t7, -20($sp)
	sw $t8, -24($sp)
	sw $t9, -28($sp)
	addi $sp, $sp, -32
	addi $sp, $sp, 0
	li $t3, 10
	li $t4, 5
__lab_3:
	slt $t2, $t4, $t3
	beqz $t2, __lab_4
	sw $t4, 0($sp)
	subi $sp, $sp, 4
	jal incr
	addi $sp, $sp, 4
	move $t4, $v0
	addi $t2, $t4, 48
	move $a0, $t2
	li $v0, 11
	syscall
	b __lab_3
__lab_4:
__lab_2:
	move $sp, $fp
	lw $t2, -8($sp)
	lw $t3, -12($sp)
	lw $t4, -16($sp)
	lw $t5, -20($sp)
	lw $t6, -24($sp)
	lw $t7, -28($sp)
	lw $t8, -32($sp)
	lw $t9, -36($sp)
	lw $ra, -4($fp)
	lw $fp, 0($fp)
	jr $ra
incr:
	sw $fp, 0($sp)
	subi $sp, $sp, 4
	sw $ra, 0($sp)
	subi $sp, $sp, 4
	addi $fp, $sp, 8
	sw $t2, 0($sp)
	sw $t3, -4($sp)
	sw $t4, -8($sp)
	sw $t5, -12($sp)
	sw $t6, -16($sp)
	sw $t7, -20($sp)
	sw $t8, -24($sp)
	sw $t9, -28($sp)
	addi $sp, $sp, -32
	addi $sp, $sp, 0
	lw $t0, 4($fp)
	addi $t2, $t0, 1
	move $v0, $t2
	b __lab_1
__lab_1:
	move $sp, $fp
	lw $t2, -8($sp)
	lw $t3, -12($sp)
	lw $t4, -16($sp)
	lw $t5, -20($sp)
	lw $t6, -24($sp)
	lw $t7, -28($sp)
	lw $t8, -32($sp)
	lw $t9, -36($sp)
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
