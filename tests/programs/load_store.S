# RV32I load/store sample
# Moves data through byte/halfword/word accesses and terminates via the shared memory flag.

.equ COMPLETION_BASE, 0x00001000
.equ WORD_SRC_OFFSET, 8
.equ BYTE_OFFSET, 12
.equ HALFWORD_OFFSET, 16
.equ WORD_DST_OFFSET, 20
.equ FLAG_OFFSET, 0

.section .text
.globl _start

_start:
    lui  x5, (COMPLETION_BASE >> 12)  # base pointer @ 0x1000
    addi x6, x0, 42                   # example payload
    sw   x6, WORD_SRC_OFFSET(x5)      # store word 42
    lw   x7, WORD_SRC_OFFSET(x5)      # load it back

    addi x8, x0, -1                   # 0xff = -1 as a byte
    sb   x8, BYTE_OFFSET(x5)
    lb   x9, BYTE_OFFSET(x5)          # sign-extended load

    addi x10, x0, 0x123               # 0x0123 sample halfword
    sh   x10, HALFWORD_OFFSET(x5)
    lh   x11, HALFWORD_OFFSET(x5)

    sw   x7, WORD_DST_OFFSET(x5)
    addi x12, x0, 1
    sw   x12, FLAG_OFFSET(x5)

halt:
    beq  x0, x0, halt
