section .text
    cons:
        push rbp
        mov rbp,rsp
        mov rsi,PVAR(0)
        mov rdi,PVAR(1)
        MAKE_PAIR(rax,rsi,rdi)
        pop rbp
        ret
    car:
        push rbp
        mov rbp,rsp
        mov rsi,PVAR(0)
        CAR rax,rsi
        leave
        ret

    cdr:
        push rbp
        mov rbp,rsp
        mov rsi,PVAR(0)
        CDR rax,rsi
        leave
        ret

    set_car:
            push rbp
            mov rbp,rsp
            mov rsi,PVAR(0)
            mov rdi,PVAR(1)
            mov qword [rsi+TYPE_SIZE],rdi
            mov rax,const_tbl
            pop rbp
            ret
   set_cdr:
        push rbp
        mov rbp,rsp
        mov rsi,PVAR(0)
        mov rdi,PVAR(1)
        mov qword [rsi+TYPE_SIZE+WORD_SIZE], rdi
        mov rax,const_tbl
        pop rbp
        ret

   apply:
      mov r14,rbp
      push rbp
      mov rbp,rsp
      mov rdi,qword[rbp + 8]          ;rdi = ret address
      mov rbx,qword[rbp + 8*3]        ;;rbx = number of params
      mov rdx,qword[rbp + 8*4]        ;;rdx = proc to apply
      add rsp,40
      mov r11,0                       ;;list length counter
      mov rcx,0                       ;;counter
      mov r12,5                       ;;counter
      mov r10,rbx                     ;;stopping point
      lea r9,[(rbx-2)*8]              ;;creating list
      MALLOC r8,r9                    ;;r8 = list with args from stack
      cmp r10,2                       ;;there are no args except the list
      je end_pop_args
      add r10,3
      pop_args:                       ;;poping the args before the list and saving them on a new list
          cmp r12,r10
          je end_pop_args
          mov r9,qword[rbp + 8*r12]
          add rsp,8
          mov qword[r8+8*rcx],r9
          inc rcx
          inc r12
          jmp pop_args
      end_pop_args:
          mov rcx,qword[rbp + 8*r12]                         ;;rcx = list at the end of the apply
          add rsp,8
          mov r12,rcx
      push_the_list:
          CAR r15,r12                 ;;r15 = (car list)
          cmp r12,const_tbl+1         ;;end of the list
          je end_push_the_list
          inc r11
          push r15
          CDR r12,r12
          jmp push_the_list
      end_push_the_list:
          lea r9,[8*r11]
          MALLOC r9,r9
           mov rcx,r11
           enter_to_array:
            cmp rcx,0
            je end_enter_to_array
            pop rsi
            mov r10,r11
            sub r10,rcx
            mov qword [ r9+8*r10],rsi
            dec rcx
            jmp enter_to_array
           end_enter_to_array:
           mov rcx,0
          push_again:
          cmp rcx,r11
          je end_push_again
          push qword [r9+8*rcx]
          inc rcx
          jmp push_again
          end_push_again:
          lea r9,[(rbx-3)]
          cmp rbx,2
          je end_push_back_args
      push_back_args:                 ;;pushing back the args before the list
          cmp r9,0
          jl end_push_back_args
          push qword[r8 + 8*r9]
          dec r9
          jmp push_back_args
      end_push_back_args:
          mov rcx,rbx                     ;;rcx = old param number
          add rbx,r11
          sub rbx,2                       ;;set the param number to the proc
          push rbx                        ;;push param num to proc
          push qword [rdx+1]              ;;push the env to proc
          push rdi                        ;;push ret address to proc
          mov rbp,r14
          jmp [rdx+9]