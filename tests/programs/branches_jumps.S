# RV32I branch and jump sample
# Counts to three using branches, demonstrates jal/jalr, then signals completion.

.equ COMPLETION_BASE, 0x00001000
.equ COUNT_OFFSET, 4
.equ FLAG_OFFSET, 0

.section .text
.globl _start

_start:
    addi x5, x0, 0         # counter = 0
    addi x6, x0, 3         # limit   = 3

loop:
    beq  x5, x6, exit      # exit when counter == limit
    addi x5, x5, 1
    jal  x0, loop          # jump back unconditionally

exit:
    jal  x1, after_call    # capture return address in x1
    addi x0, x0, 0         # explicit NOP for spacing

after_call:
    addi x7, x1, 0         # observe the link register
    addi x8, x0, done      # prepare indirect jump target
    jalr x0, 0(x8)         # jump to done via register

done:
    lui  x9, (COMPLETION_BASE >> 12)
    sw   x5, COUNT_OFFSET(x9)
    addi x10, x0, 1
    sw   x10, FLAG_OFFSET(x9)

halt:
    beq  x0, x0, halt
