# RV32I arithmetic sample program
# Demonstrates add/subtract datapath behavior and writes a completion flag to 0x00001000.

.equ COMPLETION_BASE, 0x00001000
.equ RESULT_OFFSET, 4
.equ FLAG_OFFSET, 0

.section .text
.globl _start

_start:
    addi x5, x0, 10        # x5 = 10
    addi x6, x0, 7         # x6 = 7
    add  x7, x5, x6        # x7 = 17
    sub  x8, x7, x6        # x8 = 10
    add  x9, x8, x8        # x9 = 20

    lui  x10, (COMPLETION_BASE >> 12)
    sw   x9, RESULT_OFFSET(x10)

    addi x11, x0, 1        # flag = 1 signals completion
    sw   x11, FLAG_OFFSET(x10)

done:
    beq  x0, x0, done      # park forever
