# RV32I logical operations sample
# Exercises bitwise AND/OR/XOR and reports results under the shared completion convention.

.equ COMPLETION_BASE, 0x00001000
.equ AND_OFFSET, 8
.equ OR_OFFSET, 12
.equ XOR_OFFSET, 16
.equ FLAG_OFFSET, 0

.section .text
.globl _start

_start:
    addi x5, x0, 0x0f0     # operand A
    addi x6, x0, 0x0a5     # operand B
    and  x7, x5, x6
    or   x8, x5, x6
    xor  x9, x5, x6

    lui  x10, (COMPLETION_BASE >> 12)
    sw   x7, AND_OFFSET(x10)
    sw   x8, OR_OFFSET(x10)
    sw   x9, XOR_OFFSET(x10)

    addi x11, x0, 1
    sw   x11, FLAG_OFFSET(x10)

done:
    beq  x0, x0, done
