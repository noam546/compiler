(* semantic-analyser.ml
 * The semantic analysis phase of the compiler
 *
 * Programmer: Mayer Goldberg, 2021
 *)

#use "tag-parser.ml";;

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;

type var' =
  | VarFree of string
  | VarParam of string * int
  | VarBound of string * int * int;;

type expr' =
  | ScmConst' of sexpr
  | ScmVar' of var'
  | ScmBox' of var'
  | ScmBoxGet' of var'
  | ScmBoxSet' of var' * expr'
  | ScmIf' of expr' * expr' * expr'
  | ScmSeq' of expr' list
  | ScmSet' of var' * expr'
  | ScmDef' of var' * expr'
  | ScmOr' of expr' list
  | ScmLambdaSimple' of string list * expr'
  | ScmLambdaOpt' of string list * string * expr'
  | ScmApplic' of expr' * (expr' list)
  | ScmApplicTP' of expr' * (expr' list);;
let join_scmseq expr' expr's  =
match expr' with
| ScmSeq' seq_expr's -> seq_expr's@expr's
| _ -> expr'::expr's;;

let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false
let rec flatten_scmseq expr' =
match expr' with
| (ScmConst' _ | ScmVar' _ | ScmBox' _ | ScmBoxGet' _) -> expr'
| ScmBoxSet' (var, expr') -> ScmBoxSet' (var, flatten_scmseq expr')
| ScmIf' (test, dit, dif) -> ScmIf' (flatten_scmseq test, flatten_scmseq dit, flatten_scmseq dif)
| ScmSet' (var, expr') -> ScmSet' (var, flatten_scmseq expr')
| ScmDef' (var, expr') -> ScmDef' (var, flatten_scmseq expr')
| ScmOr' expr's -> ScmOr' (List.map flatten_scmseq expr's)
| ScmLambdaSimple'(params, expr') -> ScmLambdaSimple' (params, flatten_scmseq expr')
| ScmLambdaOpt'(params, param, expr') -> ScmLambdaOpt' (params, param, flatten_scmseq expr')
| ScmApplic' (expr', expr's) -> ScmApplic' (flatten_scmseq expr', List.map flatten_scmseq expr's)
| ScmApplicTP' (expr', expr's) -> ScmApplicTP' (flatten_scmseq expr', List.map flatten_scmseq expr's)
| ScmSeq' expr's ->
    let expr's = List.map flatten_scmseq expr's in
    let spliced_expr's = List.fold_right join_scmseq expr's [] in
    ScmSeq' spliced_expr's;;

let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2

let rec expr'_eq e1 e2 =
  let e1, e2 = (flatten_scmseq e1, flatten_scmseq e2) in
  match e1, e2 with
  | ScmConst' (sexpr1), ScmConst' (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar' (var1), ScmVar' (var2) -> var_eq var1 var2
  | ScmIf' (test1, dit1, dif1), ScmIf' (test2, dit2, dif2) -> (expr'_eq test1 test2) &&
                                            (expr'_eq dit1 dit2) &&
                                              (expr'_eq dif1 dif2)
  | (ScmSeq' (exprs1), ScmSeq' (exprs2) | ScmOr' (exprs1), ScmOr' (exprs2)) ->
        list_eq expr'_eq exprs1 exprs2
  | (ScmSet' (var1, val1), ScmSet' (var2, val2) | ScmDef' (var1, val1), ScmDef' (var2, val2)) ->
        (var_eq var1 var2) && (expr'_eq val1 val2)
  | ScmLambdaSimple' (vars1, body1), ScmLambdaSimple' (vars2, body2) ->
     (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmLambdaOpt' (vars1, var1, body1), ScmLambdaOpt' (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (list_eq String.equal vars1 vars2) && (expr'_eq body1 body2)
  | ScmApplic' (e1, args1), ScmApplic' (e2, args2) ->
     (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmApplicTP' (e1, args1), ScmApplicTP' (e2, args2) ->
      (expr'_eq e1 e2) && (list_eq expr'_eq args1 args2)
  | ScmBox' (v1), ScmBox' (v2) -> var_eq v1 v2
  | ScmBoxGet' (v1), ScmBoxGet' (v2) -> var_eq v1 v2
  | ScmBoxSet' (v1, e1), ScmBoxSet' (v2, e2) -> (var_eq v1 v2) && (expr'_eq e1 e2)
  | _ -> false


module type SEMANTIC_ANALYSIS = sig
  val annotate_lexical_addresses : expr -> expr'
  val annotate_tail_calls : expr' -> expr'
  val box_set : expr' -> expr'
  val run_semantics : expr -> expr'
end;; (* end of module type SEMANTIC_ANALYSIS *)

module Semantic_Analysis : SEMANTIC_ANALYSIS = struct

  let rec lookup_in_rib name = function
    | [] -> None
    | name' :: rib ->
       if name = name'
       then Some(0)
       else (match (lookup_in_rib name rib) with
             | None -> None
             | Some minor -> Some (minor + 1));;

  let rec lookup_in_env name = function
    | [] -> None
    | rib :: env ->
       (match (lookup_in_rib name rib) with
        | None ->
           (match (lookup_in_env name env) with
            | None -> None
            | Some(major, minor) -> Some(major + 1, minor))
        | Some minor -> Some(0, minor));;

  let tag_lexical_address_for_var name params env =
    match (lookup_in_rib name params) with
    | None ->
       (match (lookup_in_env name env) with
        | None -> VarFree name
        | Some(major, minor) -> VarBound(name, major, minor))
    | Some minor -> VarParam(name, minor);;

  (* run this first! *)
  let annotate_lexical_addresses pe =
   let rec run pe params env =
      match pe with
      |ScmConst(const)->ScmConst'(const)
      |ScmVar(var)-> ScmVar'(tag_lexical_address_for_var var params env )
      |ScmApplic(expr,expr_list)-> ScmApplic'(run expr params env,List.map (fun exp -> run exp params env) expr_list)
      |ScmSet(ScmVar(var),value)->
        ScmSet'((tag_lexical_address_for_var var params env),(run value params env))
      |ScmDef(ScmVar(var),value)->
            ScmDef'((tag_lexical_address_for_var var params env),run value params env)
      |ScmIf(test,dit,dif)->
            let parsed_test=(run test params env) in
            let parsed_dit=(run dit params env) in
            let parsed_dif=(run dif params env) in
            ScmIf'(parsed_test,parsed_dit,parsed_dif)
      |ScmOr(expr_list)->ScmOr'(List.map (fun exp -> run exp params env) expr_list)
      |ScmSeq(expr_list)->ScmSeq'(List.map (fun exp -> run exp params env) expr_list)
      |ScmLambdaOpt(vars,var,body)->
           let env=[params]@env in
           let params=vars@[var] in
           let body = (run body params env) in
           ScmLambdaOpt'(vars,var,body)
      |ScmLambdaSimple(vars,body)->
            let env=[params]@env in
            let body = (run body vars env) in
            ScmLambdaSimple'(vars,body)
       | x ->  raise X_this_should_not_happen
   in
   run pe [] [];;

  let rec rdc_rac s =
    match s with
    | [e] -> ([], e)
    | e :: s ->
       let (rdc, rac) = rdc_rac s
       in (e :: rdc, rac)
    | _ -> raise X_this_should_not_happen;;

  (* run this second! *)
  let annotate_tail_calls pe =
   let rec run pe in_tail = match pe with
     |ScmApplic'(expr,list_expr)->
                        (match in_tail with
                                      |true-> ScmApplicTP'(run expr false,List.map (fun exp->run exp false) list_expr)
                                      |false -> ScmApplic'(run expr false,List.map (fun exp->run exp false) list_expr))
     |ScmDef'(var,value)->ScmDef'(var,run value false)
     |ScmLambdaSimple'(vars,body)->
                        ScmLambdaSimple'(vars,(run body true))
     |ScmLambdaOpt'(vars,var,body)->  ScmLambdaOpt'(vars,var,(run body true))
     |ScmOr'(list_expr)->
            let rec change_last list newList= match list with
                 |hd::[] -> newList@[(run hd in_tail)]
                 |hd::tl -> (change_last tl (newList@[(run hd false)]))
                  |x -> x in
                 ScmOr'(change_last list_expr [])
     |ScmSeq'(list_expr)->
            let rec change_last list newList= (match list with
                    |hd::[] -> newList@[(run hd true)]
                    |hd::tl -> (change_last tl (newList@[(run hd false)]))
                    |x -> x) in
            ScmSeq'(change_last list_expr [])
     |ScmSet'(var,value)-> ScmSet'(var,run value false)
     |ScmIf'(test,dit,dif) -> ScmIf'(test,(run dit in_tail) ,(run dif in_tail))
     |exp -> exp
   in
   run pe false;;

  (* boxing *)
  let flatten lst =
    List.flatten lst
  let rec find_reads name enclosing_lambda expr bounded=
             match expr with
                 |ScmConst'(const) -> []
                 |ScmVar'(var) -> (match var with
                                      |VarBound(var1,major,minor) when var1 = name -> [enclosing_lambda]
                                      |VarParam(var1,minor) when var1 = name -> [enclosing_lambda]
                                      | _ -> [])
                 |ScmApplic'(rator,rands) -> List.append (find_reads name enclosing_lambda rator bounded) (flatten (List.map (fun rand -> find_reads name enclosing_lambda rand bounded) rands))
                 |ScmApplicTP'(rator,rands) -> List.append (find_reads name enclosing_lambda rator bounded) (flatten (List.map (fun rand -> find_reads name enclosing_lambda rand bounded) rands))
                 |ScmSet'(_,value)-> find_reads name enclosing_lambda value bounded
                 |ScmDef'(_,value)-> find_reads name enclosing_lambda value bounded
                 |ScmIf'(test,dit,dif) ->
                     let parsed_test=(find_reads name enclosing_lambda test bounded) in
                     let parsed_dit=(find_reads name enclosing_lambda dit bounded) in
                     let parsed_dif=(find_reads name enclosing_lambda dif bounded) in
                     (parsed_test@parsed_dit)@parsed_dif
                 |ScmOr'(expr_list)->flatten (List.map (fun exp -> find_reads name enclosing_lambda exp bounded) expr_list)
                 |ScmSeq'(expr_list)->flatten (List.map (fun exp -> find_reads name enclosing_lambda exp bounded) expr_list)
                 |ScmLambdaOpt'(params,var,body)-> (match (List.mem name (params@[var])) with
                                                       |true -> []
                                                       |false -> (match bounded with
                                                                |true -> find_reads name enclosing_lambda body true
                                                                |false -> find_reads name expr body true))
                 |ScmLambdaSimple'(params,body)-> (match (List.mem name params) with
                                                       |true -> []
                                                       |false -> (match bounded with
                                                                |true -> find_reads name enclosing_lambda body true
                                                                |false -> find_reads name expr body true))
                 |_ -> []
  let rec find_writes name enclosing_lambda expr bounded =
            match expr with
                    |ScmConst'(const)->[]
                    |ScmVar'(var)-> []
                    |ScmApplic'(expr,expr_list)->List.append (find_writes name enclosing_lambda expr bounded) (flatten (List.map (fun exp -> find_writes name enclosing_lambda exp bounded) expr_list))
                    |ScmApplicTP'(expr,expr_list)->List.append (find_writes name enclosing_lambda expr bounded) (flatten (List.map (fun exp -> find_writes name enclosing_lambda exp bounded) expr_list))
                    |ScmSet'(var,_) -> (match var with
                                      |VarBound(var1,major,minor) when var1 = name -> [enclosing_lambda]
                                      |VarParam(var1,minor) when var1 = name -> [enclosing_lambda]
                                       | _ -> [])
                    |ScmDef'(var,_)  -> (match var with
                                       |VarBound(var1,major,minor) when var1 = name -> [enclosing_lambda]
                                       |VarParam(var1,minor) when var1 = name -> [enclosing_lambda]
                                       | _ -> [])
                    |ScmIf'(test,dit,dif)->
                          let parsed_test=(find_writes name enclosing_lambda test bounded) in
                          let parsed_dit=(find_writes name enclosing_lambda dit bounded) in
                          let parsed_dif=(find_writes name enclosing_lambda dif bounded) in
                          (parsed_test@parsed_dit)@parsed_dif
                    |ScmOr'(expr_list)->flatten (List.map (fun exp -> find_writes name enclosing_lambda exp bounded) expr_list)
                    |ScmSeq'(expr_list)->flatten (List.map (fun exp -> find_writes name enclosing_lambda exp bounded) expr_list)
                    |ScmLambdaOpt'(params,var,body)-> (match (List.mem name (params@[var])) with
                                                          |true -> []
                                                          |false -> (match bounded with
                                                                        |true -> find_writes name enclosing_lambda body true
                                                                        |false -> find_writes name expr body true))
                    |ScmLambdaSimple'(params,body)-> (match (List.mem name params) with
                                                          |true -> []
                                                          |false -> (match bounded with
                                                                        |true -> find_writes name enclosing_lambda body true
                                                                        |false -> find_writes name expr body true))
                    | _ -> []
  let get_second lst = List.hd (List.tl lst)
  let check_bound v1 v2 =
    match v1,v2 with
    |ScmVar'(VarBound(x,mj1,mn1)),ScmVar'(VarBound(y,mj2,mn2)) -> ((mj1=mj2)&&(mj1=0))||(mj1!=mj2)
    |_,_ -> true

  let rec nested_loop re wr =
                      (match re ,wr with
                          |hd ,hd2::[] -> not (expr'_eq hd hd2)
                          |hd ,hd2::tl2 -> (match (expr'_eq hd hd2) with
                                                  |true -> nested_loop hd tl2
                                                  |false -> true)
                          |x , [] -> false)
  let rec main_loop name re wr =
                     match re , wr with
                         |[],x -> []
                         |hd::x,y ->(match (nested_loop hd y) with
                                         |true -> [name]
                                         |false -> main_loop name x y)
  let need_to_box vars body enclosing_lambda =
        let before= List.map (fun name ->
                            let reads = find_reads name enclosing_lambda body false in
                            let writes = find_writes name enclosing_lambda body false in
                            main_loop name reads writes) vars in
        flatten before
  let rec find_in_array name bool_lst var_lst =
        match var_lst with
        | [] ->  raise X_this_should_not_happen
        |hd::tl -> match (hd=name)  with
                 |true ->  (List.hd bool_lst)
                 |false -> find_in_array name (List.tl bool_lst) tl

    let delete_dup old_lst new_lst =
        List.filter (fun var -> not( List.mem var new_lst)) old_lst
  let rec box_lambda args_to_box lambda_body =
          match lambda_body with
                    |ScmConst'(const)->ScmConst'(const)
                    |ScmVar'(var) -> (match var with
                                          |VarParam(name,_) when (List.mem name args_to_box) -> ScmBoxGet'(var)
                                          |VarBound(name,_,_) when (List.mem name args_to_box) -> ScmBoxGet'(var)
                                          |_ -> ScmVar'(var))
                    |ScmApplic'(expr,expr_list)-> ScmApplic'(box_lambda args_to_box expr, List.map (fun exp -> box_lambda args_to_box exp) expr_list)
                    |ScmApplicTP'(expr,expr_list)-> ScmApplicTP'(box_lambda args_to_box expr, List.map (fun exp -> box_lambda args_to_box exp) expr_list)
                    |ScmSet'(var,value)-> (match var with
                                              |VarParam(name,_) when (List.mem name args_to_box) -> ScmBoxSet'(var,box_lambda args_to_box value)
                                              |VarBound(name,_,_) when (List.mem name args_to_box) -> ScmBoxSet'(var,box_lambda args_to_box value)
                                              |_ -> ScmSet'(var,box_lambda args_to_box value))
                    |ScmDef'(var,value)-> ScmDef'(var,value)
                    |ScmIf'(test,dit,dif)->
                          let parsed_test = (box_lambda args_to_box test) in
                          let parsed_dit = (box_lambda args_to_box dit) in
                          let parsed_dif = (box_lambda args_to_box dif) in
                          ScmIf'(parsed_test,parsed_dit,parsed_dif)
                    |ScmOr'(expr_list)-> ScmOr'(List.map (fun exp -> box_lambda args_to_box exp) expr_list)
                    |ScmSeq'(expr_list)-> ScmSeq'(List.map (fun exp -> box_lambda args_to_box exp) expr_list)
                    |ScmLambdaOpt'(params,var,body)->
                          let updated_args = delete_dup args_to_box (params@[var] )in
                          ScmLambdaOpt'(params,var,box_lambda updated_args body)

                    |ScmLambdaSimple'(params,body)->
                          let updated_args = delete_dup args_to_box params in
                          ScmLambdaSimple'(params, box_lambda updated_args body)
                    | x -> x
  let get_name var =
  (match var with
      |VarBound(var1,major,minor)-> var1
      |VarParam(var1,minor)  -> var1
      | VarFree(var1)-> var1)

let rec find_index name lst =
    match lst with
    |hd::[] -> (match (hd=name) with
                           |true -> 0
                           |false -> raise X_this_should_not_happen)
    |hd::tl -> (match (hd=name) with
            |true -> 0
            |false -> (1+ find_index name tl))
    |x ->  raise X_this_should_not_happen



  let rec box_set expr =
    match expr with
          |ScmConst'(const)->ScmConst'(const)
          |ScmVar'(var)-> ScmVar'(var)
          |ScmApplic'(expr,expr_list)-> ScmApplic'(box_set expr,List.map box_set expr_list)
          |ScmApplicTP'(expr,expr_list)-> ScmApplicTP'(box_set expr,List.map box_set expr_list)
          |ScmSet'(var,value)-> ScmSet'(var,(box_set value))
          |ScmDef'(var,value)-> ScmDef'(var,(box_set value))
          |ScmIf'(test,dit,dif)->
                let parsed_test=(box_set test) in
                let parsed_dit=(box_set dit) in
                let parsed_dif=(box_set dif) in
                ScmIf'(parsed_test,parsed_dit,parsed_dif)
          |ScmOr'(expr_list)->ScmOr'(List.map box_set expr_list)
          |ScmSeq'(expr_list)->ScmSeq'(List.map box_set expr_list)
          |ScmLambdaOpt'(vars,var,body)->
                let body = box_set body in
               let vars_to_box = need_to_box (vars@[var]) body (ScmLambdaOpt'(vars,var,body)) in
               let new_body =( match (List.length vars_to_box) with
                                               | 0 -> body
                                               | _ ->
                                                (match body with
                                                | ScmSeq' (expr_list) ->
                                                    ScmSeq'((List.map (fun var ->
                                                     let wrapped_var = VarParam(var, (find_index var (vars@[var]))) in
                                                     ScmSet'(wrapped_var,ScmBox'(wrapped_var))) vars_to_box)@(List.map (fun exp -> box_lambda vars_to_box exp) expr_list))

                                                |_ ->
                                                    ScmSeq'((List.map (fun var ->
                                                   let wrapped_var = VarParam(var, (find_index var (vars@[var]))) in
                                                   ScmSet'(wrapped_var,ScmBox'(wrapped_var))) vars_to_box)@[(box_lambda vars_to_box body)]))) in
               ScmLambdaOpt'(vars,var,new_body)
          |ScmLambdaSimple'(vars,body)->
                let body = box_set body in
                let vars_to_box = need_to_box vars body (ScmLambdaSimple'(vars,body)) in
                let new_body = ( match (List.length vars_to_box) with
                  | 0 -> body
                  | _ ->
                    (match body with
                    | ScmSeq'(expr_list) ->
                            ScmSeq'((List.map (fun var ->
                                              let wrapped_var = VarParam(var,(find_index var vars)) in
                                              ScmSet'(wrapped_var,ScmBox'(wrapped_var))) vars_to_box)
                                              @(List.map (fun exp -> box_lambda vars_to_box exp) expr_list))
                    |_ ->
                     ScmSeq'((List.map (fun var ->
                            let wrapped_var = VarParam(var,(find_index var vars)) in
                            ScmSet'(wrapped_var,ScmBox'(wrapped_var))) vars_to_box)@[(box_lambda vars_to_box body)]))
                     ) in
                ScmLambdaSimple'(vars,new_body)
           |exp -> exp



  let run_semantics expr =
    box_set
        (annotate_tail_calls
         (annotate_lexical_addresses expr))

end;; (* end of module Semantic_Analysis *)
