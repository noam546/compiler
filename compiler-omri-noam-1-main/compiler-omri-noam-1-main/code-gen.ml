#use "semantic-analyser.ml";;

(* This module is here for you convenience only!
   You are not required to use it.
   you are allowed to change it. *)
module type CODE_GEN = sig
  (* This signature assumes the structure of the constants table is
     a list of key-value pairs:
     - The keys are constant values (Sexpr(x) or Void)
     - The values are pairs of:
       * the offset from the base const_table address in bytes; and
       * a string containing the byte representation (or a sequence of nasm macros)
         of the constant value
     For example: [(Sexpr(Nil), (1, "T_NIL"))]
   *)
  val make_consts_tbl : expr' list -> (sexpr * (int * string)) list

  (* This signature assumes the structure of the fvars table is
     a list of key-value pairs:
     - The keys are the fvar names as strings
     - The values are the offsets from the base fvars_table address in bytes
     For example: [("boolean?", 0)]
   *)
  val make_fvars_tbl : expr' list -> (string * int) list
  (* If you change the types of the constants and fvars tables, you will have to update
     this signature to match: The first argument is the constants table type, the second
     argument is the fvars table type, and the third is an expr' that has been annotated
     by the semantic analyser.
   *)
  val generate : (sexpr * (int * string)) list -> (string * int) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

 let index = ref 0 ;;
 let generate_new_index x =
     index:= (!index + 1)

 let rec extend_const ast =
       match ast with
           |ScmSymbol(symbol) -> [ScmString(symbol)]@[ast]
           |ScmPair(car,cdr) ->
                         let ex_car = extend_const car in
                         let ex_cdr = extend_const cdr in
                         ex_car@ex_cdr@[ast]
           |ScmVector(vec) ->
                            let body= List.flatten (List.map extend_const vec) in
                            body@[ast]
           |_ -> [ast]
 let remove_duplicate const_lst =
     let rec remove lst out  =
     match lst with
     | [] -> out
     |hd :: tl -> (match (List.mem hd out )with
                   |true -> remove tl out
                   |false -> remove tl (out@[hd])) in
     remove  const_lst []
 let get_size sexp  =
     match sexp with
     |ScmVoid -> 1
     |ScmNil -> 1
     |ScmBoolean(bool) -> 2
     |ScmChar(ch) -> 2
     |ScmNumber(ScmReal(num)) -> 9
     |ScmNumber(ScmRational(x,y)) -> 17
     |ScmString(str)-> (9 + (String.length str))
     |ScmSymbol(symbol)-> 9
     |ScmPair(car,cdr) -> 17
     |ScmVector(vec) -> 9+ (List.length vec)

 let rec find_off sexp consts_tbl =
     match consts_tbl with
     | [] -> 0
     |hd::tl ->
             let sexpr' = (fun (se,(off,str)) -> se)  hd in
             (match (sexpr_eq sexpr' sexp) with
                 |true -> (fun (se,(off,str)) -> off)  hd
                 |false -> find_off sexp tl)

 let rec create_str_vec vec out consts_tbl=
  match vec with
  |[] -> out
  |hd::[] ->
             let hd_ptr = find_off hd consts_tbl in
             let hd_to_add = Printf.sprintf "const_tbl+%d" hd_ptr in
             out^hd_to_add
  |hd::tl ->
             let hd_ptr = find_off hd consts_tbl in
             let hd_to_add =Printf.sprintf "const_tbl+%d," hd_ptr in
             create_str_vec tl (out^hd_to_add) consts_tbl

 let create_asm sexp tb =
     match sexp with
     |ScmVoid -> "db T_VOID"
     |ScmNil -> "db T_NIL"
     |ScmBoolean(false) -> "db T_BOOL ,0"
     |ScmBoolean(true) ->  "db T_BOOL ,1"
     |ScmChar(ch) ->  Printf.sprintf "MAKE_LITERAL_CHAR("^ (string_of_int(int_of_char ch))^")"
     |ScmNumber(ScmRational(x,y)) -> Printf.sprintf "MAKE_LITERAL_RATIONAL(%d,%d)" x y
     |ScmNumber(ScmReal(num)) -> "MAKE_LITERAL_REAL("^(string_of_sexpr sexp)^")"
     |ScmString(str)-> Printf.sprintf "MAKE_LITERAL_STRING \"%s\"" str
     |ScmSymbol(symbol)->
                         let off = find_off (ScmString(symbol)) tb in
                         Printf.sprintf "MAKE_LITERAL_SYMBOL (const_tbl+%d)" off
     |ScmPair(car,cdr) ->
                  let off_car = find_off car tb in
                  let off_cdr = find_off cdr tb in
                  Printf.sprintf "MAKE_LITERAL_PAIR(const_tbl+%d, const_tbl+%d)" off_car off_cdr
     |ScmVector(vec) ->      let out = "MAKE_LITERAL_VECTOR " in
                             create_str_vec vec out tb

 let rec expand_const lst out curr_offset=
     match lst with
          |[] -> out
          |hd::tl ->
                 let asm= create_asm hd out in
                 let new_head = [(hd,(curr_offset,asm^(Printf.sprintf ";;offset is %d" curr_offset)))] in
                 let new_offset = curr_offset + (get_size hd) in
                 let out = out@new_head in
                 expand_const tl out new_offset


  let make_consts_tbl asts =
     let rec find_consts ast =
         match ast with
             |ScmConst'(const) -> extend_const const
             |ScmVar'(var) -> []
             |ScmBoxGet'(var) -> []
             |ScmBoxSet'(var,value) -> (find_consts value)
             |ScmBox'(var) -> []
             |ScmApplic'(expr,expr_list)->
                 let parset_expr_list = List.flatten (List.map (fun exp -> find_consts exp) expr_list) in
                 let parsed_expr = find_consts expr in
                 parsed_expr@parset_expr_list
             |ScmApplicTP'(expr,expr_list)->
                  let parset_expr_list = List.flatten (List.map (fun exp -> find_consts exp) expr_list) in
                  let parsed_expr = find_consts expr in
                  parsed_expr@parset_expr_list
             |ScmSet'(var,value)-> (find_consts value)
             |ScmDef'(var,value)-> (find_consts value)
             |ScmIf'(test,dit,dif)->
                                 let parsed_test=(find_consts test) in
                                 let parsed_dit=(find_consts dit) in
                                 let parsed_dif=(find_consts dif) in
                                 parsed_test@parsed_dit@parsed_dif
             |ScmOr'(expr_list)-> List.flatten (List.map (fun exp -> find_consts exp) expr_list)
             |ScmSeq'(expr_list)-> List.flatten (List.map (fun exp -> find_consts exp) expr_list)
             |ScmLambdaSimple'(params,body)-> (find_consts body)
             |ScmLambdaOpt'(params,var,body)-> (find_consts body) in
     let const_tb = List.flatten (List.map find_consts asts) in
     let default_lst = [ScmVoid;ScmNil;ScmBoolean(false);ScmBoolean(true)] in
     let const_tb = remove_duplicate (default_lst@const_tb) in
     expand_const const_tb [] 0

 let rec add_offset_to_list offset = function
         |[] -> []
         |hd::[] -> [(hd,offset)]
         |hd::tl -> [(hd,offset)]@(add_offset_to_list (offset+1) tl)

   let make_fvars_tbl asts =
       let rec make_fvars_list expr =
                    match expr with
                        |ScmConst'(const) -> []
                        |ScmVar'(var) -> (match var with
                                             |VarFree(name) -> [name]
                                             |_-> [])
                        |ScmApplic'(rator,rands) -> List.append (make_fvars_list rator) (List.flatten (List.map (fun rand -> make_fvars_list rand) rands))
                        |ScmApplicTP'(rator,rands) -> List.append (make_fvars_list rator) (List.flatten (List.map (fun rand -> make_fvars_list rand) rands))
                        |ScmBoxGet'(var) -> []
                        |ScmBoxSet'(var,value) -> []
                        |ScmSet'(_,value)-> make_fvars_list value
                        |ScmDef'(_,value)-> make_fvars_list value
                        |ScmIf'(test,dit,dif) ->
                            let parsed_test=(make_fvars_list test) in
                            let parsed_dit=(make_fvars_list dit) in
                            let parsed_dif=(make_fvars_list dif) in
                            (parsed_test@parsed_dit)@parsed_dif
                        |ScmOr'(expr_list)->List.flatten (List.map (fun exp -> make_fvars_list exp) expr_list)
                        |ScmSeq'(expr_list)->List.flatten (List.map (fun exp -> make_fvars_list exp) expr_list)
                        |ScmLambdaOpt'(params,var,body)-> make_fvars_list body
                        |ScmLambdaSimple'(params,body)-> make_fvars_list body
                        |_ -> [] in
       let lib_func = ["map";"fold-left";"fold-right";"cons*";"append";"list";"list?";"make-string";"not";
                       "-";">";"apply";"cons";"gcd";"zero?";"integer?";"number?";"length";"string->list";"equal?";"car";"cdr";"set-car!";"set-cdr!"] @
       [
           (* Type queries  *)
           "boolean?";"flonum?"; "rational?";
           "pair?";"null?";"char?";"string?";
           "procedure?";"symbol?";
           (* String procedures *)
           "string-length"; "string-ref";"string-set!";
           "make-string";"symbol->string";
           (* Type conversions *)
           "char->integer";"integer->char";"exact->inexact";
           (* Identity test *)
           "eq?";
           (* Arithmetic ops *)
           "+"; "*"; "/"; "="; "<";
           (* Additional rational numebr ops *)
           "numerator"; "denominator";"gcd";
           (* you can add yours here *)
         ] in
       let fvars_names_list = List.flatten (List.map (fun expr' -> make_fvars_list expr') asts) in
       let fvars_names_list = lib_func@fvars_names_list in
       let fvars_names_list = remove_duplicate fvars_names_list in
       add_offset_to_list 0 fvars_names_list

   let rec find_free_var name free_tbl =
     match free_tbl with
      |[] -> 0
      |hd::tl ->
                 let hd_name = (fun (n,i)-> n) hd in
                 match (String.equal hd_name name) with
                 | true -> (fun (n,i)-> i) hd
                 | false -> find_free_var name tl

   and handle_deeper_lambda params body depth =
        generate_new_index 0;
        (*define new arr with new params in rax, rbx number of params*)
        let new_arr = Printf.sprintf "mov rax,   [rbp+8*3]
        inc rax
        lea rax,[rax*8]
        MALLOC rdx,rax
        mov rcx,[rbp+8*3]
        mov rbx,0
        param_arr_loop%d:
            cmp rbx,rcx
            je end_param_loop%d
            mov r9, [rbp+8*(rbx+4)]
            mov  [rdx+8*rbx],r9
            inc rbx
            jmp param_arr_loop%d
        end_param_loop%d:
            mov qword [rdx + 8*rbx],SOB_NIL_ADDRESS
            mov rcx,0
            mov rbx,0
            mov r9,0" !index !index !index !index  in
        (*define env  with the size of depth+1 in rbx
          And put the new arr of params in the extenv[0]
          [rbx]=rax*)
        let ext_env= Printf.sprintf  "
          MALLOC rbx,%d
          mov  [rbx],rdx\n" (8*(depth+1))  in
        (*put the old env in the new env*)
        let extended_env_code = Printf.sprintf
        "mov rsi ,  [rbp+8*2]
        mov rcx,%d
        mov r9,0
        mov r8,0
        copy_env_loop%d:
            cmp r9,rcx
            je end_copy_env_loop%d
            mov r8, [rsi+8*r9]
            mov [rbx+8*(r9+1)],r8
            inc r9
            jmp copy_env_loop%d
        end_copy_env_loop%d:" depth !index !index !index !index in
        let l_code = Printf.sprintf "Lcode%d:
                                           push rbp
                                           mov rbp,rsp
                                           %s
                                           leave
                                           ret
                                           Lcont%d:" !index body !index in
        let ext_env =  new_arr^ext_env^extended_env_code in
        let closure =Printf.sprintf "MAKE_CLOSURE(rax,rbx,Lcode%d)
        jmp Lcont%d\n" !index !index in
        ext_env^"\n"^closure^"\n"^l_code
   let handle_lambda_depth_0 params body depth =
      generate_new_index 0;
      let l_code = Printf.sprintf "Lcode%d:
                                   push rbp
                                   mov rbp,rsp
                                   %s
                                   leave
                                   ret
                                   Lcont%d:" !index body !index in
      let out =(Printf.sprintf "MAKE_CLOSURE(rax,SOB_NIL_ADDRESS,Lcode%d)\njmp Lcont%d\n" !index !index)^l_code  in
      out
  let handle_lambdaOPT_depth_0 params body depth =
        generate_new_index 0;
        let l_code = Printf.sprintf "Lcode%d:
                                    CHANGE_STACK_TO_LAMBDA_OPT %d
                                    mov rbp, r14
                                    push rbp
                                    mov rbp,rsp
                                    %s
                                    leave
                                    ret
                                    Lcont%d:" !index (List.length params) body !index in
        let out =(Printf.sprintf "MAKE_CLOSURE(rax,SOB_NIL_ADDRESS,Lcode%d)\njmp Lcont%d\n" !index !index)^l_code  in
        out


   let handle_deeper_lambdaOPT params body depth =
        generate_new_index 0;
        let next_index = !index in
        (*define new arr with new params in rax, rbx number of params*)
        let new_arr = Printf.sprintf "mov rax,   [rbp+8*3]
        inc rax
        lea rax,[rax*8]
        MALLOC rdx,rax
        mov rcx,[rbp+8*3]
        mov rbx,0
        param_arr_loop%d:
            cmp rbx,rcx
            je end_param_loop%d
            mov r9, [rbp+8*(rbx+4)]
            mov  [rdx+8*rbx],r9
            inc rbx
            jmp param_arr_loop%d
        end_param_loop%d:
            mov qword [rdx + 8*rbx],SOB_NIL_ADDRESS
            mov rcx,0
            mov rbx,0
            mov r9,0" next_index next_index next_index next_index  in
        (*define env  with the size of depth+1 in rbx
          And put the new arr of params in the extenv[0]
          [rbx]=rax*)
        let ext_env= Printf.sprintf  "
          MALLOC rbx,%d
          mov  [rbx],rdx\n" (8*(depth+1))  in
        (*put the old env in the new env*)
        let extended_env_code = Printf.sprintf
        "mov rsi ,  [rbp+8*2]
        mov rcx,%d
        mov r9,0
        mov r8,0
        copy_env_loop%d:
            cmp r9,rcx
            je end_copy_env_loop%d
            mov r8, [rsi+8*r9]
            mov [rbx+8*(r9+1)],r8
            inc r9
            jmp copy_env_loop%d
        end_copy_env_loop%d:" depth next_index next_index next_index next_index in
        let l_code = Printf.sprintf "Lcode%d:
                                           CHANGE_STACK_TO_LAMBDA_OPT %d
                                           mov rbp, r14
                                           push rbp
                                           mov rbp,rsp
                                           %s
                                           leave
                                           ret
                                           Lcont%d:" next_index (List.length params) body next_index in
        let ext_env =  new_arr^ext_env^extended_env_code in
        let closure =Printf.sprintf "MAKE_CLOSURE(rax,rbx,Lcode%d)
        jmp Lcont%d\n" next_index next_index in
        ext_env^closure^l_code
   let generate consts fvars e =
    let rec gen exp depth =
     (match exp with
         |ScmConst'(const) ->   let offset = find_off const consts in
                                Printf.sprintf "mov rax,const_tbl+%d\n" offset
         |ScmVar'(var) -> (match var with
                            |VarFree(name) ->
                                          let offset = find_free_var name fvars in
                                          Printf.sprintf "mov rax,[fvar_tbl+%d*WORD_SIZE]" offset

                            |VarParam(_,minor) ->  Printf.sprintf "mov rax,qword [rbp+8*(4+%d)]" minor
                            |VarBound(_,mj,mi) ->  Printf.sprintf "mov rax,qword [rbp+8*2]
                                                                   mov rax,qword [rax+8*%d]
                                                                   mov rax,qword [rax+8*%d]" mj mi)
         |ScmBoxGet'(var) -> let parsed_var = gen (ScmVar'(var)) depth in
                             Printf.sprintf "%s\nmov rax, qword[rax]" parsed_var
         |ScmBoxSet'(var,value) -> let parsed_val = gen value depth in
                                   let parsed_var = gen (ScmVar'(var)) depth in
                                   Printf.sprintf "%s
                                                   push rax
                                                   %s
                                                   pop qword [rax]
                                                   mov rax,const_tbl+0" parsed_val parsed_var

         |ScmBox'(var) -> let parsed_var = gen (ScmVar'(var)) depth in
         Printf.sprintf"%s
         MALLOC r11, 8
         mov qword [r11], rax
         mov rax, r11" parsed_var
         |ScmApplic'(rator,rands)->
                                    let parsed_rands = (match (List.length rands) with
                                    |0 -> ""
                                    |_ ->   let parsed_rands = List.rev(List.map (fun expr-> gen expr depth) rands) in
                                            let parsed_rands = List.fold_left (fun a b -> "\n"^a^"\npush rax\n;;---param---\n"^b) (List.hd parsed_rands) (List.tl parsed_rands) in
                                            parsed_rands^"\npush rax") in
                                    let parsed_rands  = parsed_rands^(Printf.sprintf "\npush %d\n" (List.length rands)) in
                                    let parsed_rator = gen rator depth in
                                    generate_new_index 0;
                                    let next_index = !index in
                                    let str = Printf.sprintf
                                    "\n cmp byte[rax] , T_CLOSURE
                                    je skip_applic%d
                                    mov rax, 1
                                    mov rdx, 0
                                    div rdx
                                    skip_applic%d:
                                    push qword[rax+1]
                                    call [rax+9]
                                    add rsp,8
                                    pop rbx
                                    lea rsp, [rsp + 8*rbx]\n" next_index next_index  in
                                   parsed_rands^parsed_rator^str
         |ScmApplicTP'(rator,rands)->  let parsed_rands = (match (List.length rands) with
                                                                           |0 -> ""
                                                                           |_ -> let parsed_rands = List.rev(List.map (fun expr-> gen expr depth) rands) in
                                                                                 let parsed_rands = List.fold_left (fun a b -> "\n"^a^"\npush rax\n"^b) (List.hd parsed_rands) (List.tl parsed_rands) in
                                                                                 parsed_rands^"\npush rax") in
                                                                           let parsed_rands  = parsed_rands^(Printf.sprintf "\npush %d\n" (List.length rands)) in
                                                                           let parsed_rator = gen rator depth in
                                                                           generate_new_index 0;
                                                                           let next_index = !index in
                                                                           let str = Printf.sprintf
                                                                           "\n cmp byte[rax] , T_CLOSURE
                                                                             je skip_applic%d
                                                                             mov rax, 1
                                                                             mov rdx, 0
                                                                             div rdx
                                                                           skip_applic%d:
                                                                            push qword[rax+1]
                                                                            push qword[rbp + 8 * 1]
                                                                           SHIFT_FRAME %d
                                                                           jmp [rax+9]" next_index next_index  ((List.length rands)+4)  in
                                                                          parsed_rands^parsed_rator^str
         |ScmSet'(var,value)-> let parsed_val = gen value depth in
                               (match var with
                                 |VarParam(_,minor) ->   Printf.sprintf "%s
                                                                        mov qword [rbp+8*(4+%d)],rax
                                                                        mov rax,const_tbl+0" parsed_val minor
                                 |VarBound(_,mj,mi) -> Printf.sprintf "%s
                                                                       mov rbx,qword [rbp+8*2]
                                                                       mov rbx,qword [rbx+8*%d]
                                                                       mov qword [rbx+8*%d],rax
                                                                       mov rax,const_tbl+0" parsed_val mj mi
                                 |VarFree(name) -> let offset = find_free_var name fvars in

                                                Printf.sprintf "%s
                                                               mov qword [fvar_tbl+%d*WORD_SIZE],rax
                                                               mov rax,const_tbl+0" parsed_val offset )
         |ScmDef'(var,value)->   let parsed_value = gen value depth in
                                 generate_new_index 0;
                                 (match var with
                                 |VarFree(name) ->   let offset = find_free_var name fvars in
                                                     Printf.sprintf "
                                                     %s
                                                                     mov [fvar_tbl+%d*WORD_SIZE],rax\n
                                                                     mov rax,const_tbl+0"  parsed_value offset

                                 |VarParam(_,minor) ->   Printf.sprintf "%s
                                                                         mov qword [rbp+8*(4+%d)],rax
                                                                         mov rax,const_tbl+0" parsed_value minor
                                 |VarBound(_,mj,mi) ->   Printf.sprintf "%s
                                                                         mov rbx,qword [rbp+8*2]
                                                                         mov rbx,qword [rbx+8*%d]
                                                                         mov qword [rax+8*%d],rax
                                                                         mov rax,const_tbl+0" parsed_value mj mi)
         |ScmIf'(test,dit,dif)-> let parsed_test = gen test depth in
                                 let parsed_dit = gen dit depth in
                                 let parsed_dif = gen dif depth in
                                 generate_new_index 0;
                                 Printf.sprintf "%s
                                                 cmp rax, const_tbl+2
                                                 je Lelse%d
                                                 %s
                                                 jmp Lexit%d
                                                 Lelse%d:
                                                 %s
                                                 Lexit%d:"  parsed_test !index parsed_dit !index !index parsed_dif !index
         |ScmOr'(expr_list)->   let parsed_lst = List.map (fun expr-> gen expr depth) expr_list in
                                generate_new_index 0;
                                let str = Printf.sprintf "
                                                           cmp rax, const_tbl+2
                                                           jne Lexit%d\n" !index in
                                let str = (List.fold_left (fun a b -> a^str^b) (List.hd parsed_lst) (List.tl parsed_lst)) in
                                Printf.sprintf "%s\nLexit%d:" str !index
         |ScmSeq'(expr_list)->  let parsed_lst = List.map (fun expr-> gen expr depth) expr_list in
                                List.fold_left (fun a b -> a^"\n;;;NextSeq\n"^b) (List.hd parsed_lst) (List.tl parsed_lst)
         |ScmLambdaSimple'(params,body)-> (match depth with
                                                |0 -> handle_lambda_depth_0 params (gen body (depth+1)) depth
                                                |_ -> handle_deeper_lambda params (gen body (depth+1)) depth)
         |ScmLambdaOpt'(params,var,body)-> (match depth with
                                            |0 -> handle_lambdaOPT_depth_0 params (gen body (depth+1)) depth
                                            |_ -> handle_deeper_lambdaOPT params (gen body (depth+1)) depth)
         ) in
      gen e 0
end;;

