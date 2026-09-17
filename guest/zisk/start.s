.option norvc
.option norelax
.section .text.start,"ax",@progbits
.balign 4
.globl _start
.type _start, @function
_start:
    la sp, _stack_top
    call guest_main
    li a7, 93
    ecall
1:
    j 1b
.size _start, . - _start
.section .note.GNU-stack,"",@progbits
