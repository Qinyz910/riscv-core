# RV32I immediate instruction sample
# Covers addi/slti/xori/ori/andi and shift immediates, emitting intermediate values to memory.

.equ COMPLETION_BASE, 0x00001000
.equ SLTI_OFFSET, 20
.equ SLLI_OFFSET, 24
.equ SRLI_OFFSET, 28
.equ XORI_OFFSET, 32
.equ ORI_OFFSET, 36
.equ ANDI_OFFSET, 40
.equ FLAG_OFFSET, 0

.section .text
.globl _start

_start:
    addi x5, x0, 5         # x5 = 5
    addi x6, x0, -3        # x6 = -3
    slti x7, x6, 0         # 1 when x6 < 0
    slli x8, x5, 2         # x8 = 20
    srli x9, x8, 1         # x9 = 10
    xori x10, x5, 3
    ori  x11, x5, 8
    andi x12, x5, 1

    lui  x13, (COMPLETION_BASE >> 12)
    sw   x7, SLTI_OFFSET(x13)
    sw   x8, SLLI_OFFSET(x13)
    sw   x9, SRLI_OFFSET(x13)
    sw   x10, XORI_OFFSET(x13)
    sw   x11, ORI_OFFSET(x13)
    sw   x12, ANDI_OFFSET(x13)

    addi x14, x0, 1
    sw   x14, FLAG_OFFSET(x13)

done:
    beq  x0, x0, done
