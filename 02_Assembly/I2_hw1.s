.data
    n: .word 10
    
.text
.globl __start

FUNCTION:
    # Todo: Define your own function in HW1
    # You should store the output into x10
  jal x1, Recursive
  jal x1, result  

Recursive:
  addi sp, sp, -16  # Save return address and n on stack
  sw x1, 8(sp)
  sw t0, 0(sp)
  addi x28, t0, -1  # x28 = n-1
  bne x28, x0, L1  # if n==1, go to L1
  addi a0, x0, 2  # else, set return value 2
  addi sp, sp, 16  # pop stack
  jalr x0, 0(x1)  #return
L1:
  srli t0, t0, 1  # t0 = n/2
  jal x1, Recursive  # call Recursive(n/2)
  addi x6, a0, 0  # move result of Recursive(n/2) to x6
  addi a0, x0, 0  # initialize a0 to 0
  lw t0, 0(sp)  # restore caller's n
  lw x1, 8(sp)  # restore caller's return address
  addi sp, sp, 16  # pop stack
  li x12, 5  # set constans 5, 6
  li x13, 6
  mul x7, x12, x6  # multiply 5, T(n/2)
  add a0, a0, x7  # add to to
  mul x7, x13, t0  # multiply 6, n
  add a0, a0, x7  # add to a0
  addi a0, a0, 4  # add 4 to a0
  jalr x0, 0(x1)
    

# Do NOT modify this part!!!
__start:
    la   t0, n
    lw   x10, 0(t0)
    jal  x1,FUNCTION
    la   t0, n
    sw   x10, 4(t0)
    addi a0,x0,10
    ecall