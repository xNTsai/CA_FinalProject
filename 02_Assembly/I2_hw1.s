.data
    n: .word 10
.text
.globl __start


__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1, Function
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall
Function:
  addi sp, sp, -8
  sw x1, 0(sp)
  jal x1, Recursive
  add x10, x0, x11
  lw x1, 0(sp)
  addi sp, sp, 8
  jalr x0, 0(x1)

Recursive:
  addi sp, sp, -16  # Save return address and n on stack
  sw x1, 8(sp)
  sw a0, 0(sp)
  addi x28, a0, -1  # x28 = n-1
  bne x28, x0, L1  # if n==1, go to L1
  addi x11, x0, 2  # else, set return value 2
  addi sp, sp, 16  # pop stack
  jalr x0, 0(x1)  #return
L1:
  srli a0, a0, 1  # a0 = n/2
  jal x1, Recursive  # call Recursive(n/2)
  addi x6, x11, 0  # move result of Recursive(n/2) to x6
  addi x11, x0, 0  # initialize x11 to 0
  lw a0, 0(sp)  # restore caller's n
  lw x1, 8(sp)  # restore caller's return address
  addi sp, sp, 16  # pop stack
  li x12, 5  # set constans 5, 6
  li x13, 6
  mul x7, x12, x6  # multiply 5, T(n/2)
  add x11, x11, x7  # add to to
  mul x7, x13, a0  # multiply 6, n
  add x11, x11, x7  # add to x11
  addi x11, x11, 4  # add 4 to x11
  jalr x0, 0(x1)
    
