global points

section .text

; <--- unsigned points(const char *games[]) --->
points:
    
    ; clear the register because the function will be
    ; called multiple times
    xor r15, r15 
    
    mov rcx, 10; number of strings in array
    
    ; the result will be stored to r15 and then
    ; loaded to rax
.loop:
    ; move the address of string in rsi
    mov rsi, rdi
    mov rsi, [rsi]
    
    ; move first byte of string in rax
    xor rax, rax
    lodsb
    
    ; move that byte into rbx for later
    mov rbx, rax
    
    ; ignore the ':' character
    lodsb
    
    ; move the third byte to rax
    xor rax, rax
    lodsb
    
    ; if the string is '1:2' for ex
    ; we will compare '1'(rax) with '2'(rbx)
    cmp rbx, rax
    jl .loop.back; if rbx < rax do nothing
    je .loop.equal; if rbx = rax add 1 to r15
    
    ; if rbx > rax add 3 to r15
    add r15, 3
    jmp .loop.back
    
.loop.equal:
    inc r15
    
.loop.back:
    ; go to next string
    add rdi, 8
    loop .loop
    
    mov rax, r15
    
    ret
; ---------> endof pts <---------