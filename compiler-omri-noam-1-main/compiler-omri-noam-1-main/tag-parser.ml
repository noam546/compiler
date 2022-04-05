#use "reader.ml";;

type expr =
  | ScmConst of sexpr
  | ScmVar of string
  | ScmIf of expr * expr * expr
  | ScmSeq of expr list
  | ScmSet of expr * expr
  | ScmDef of expr * expr
  | ScmOr of expr list
  | ScmLambdaSimple of string list * expr
  | ScmLambdaOpt of string list * string * expr
  | ScmApplic of expr * (expr list);;

exception X_syntax_error of sexpr * string;;
exception X_reserved_word of string;;
exception X_proper_list_error;;
exception X_not_implemented;;

let rec list_to_proper_list = function
| [] -> ScmNil
| hd::[] -> ScmPair (hd, ScmNil)
| hd::tl -> ScmPair (hd, list_to_proper_list tl);;

let rec list_to_improper_list = function
| [] -> raise X_proper_list_error
| hd::[] -> hd
| hd::tl -> ScmPair (hd, list_to_improper_list tl);;

let rec scm_append scm_list sexpr =
match scm_list with
| ScmNil -> sexpr
| ScmPair (car, cdr) -> ScmPair (car, scm_append cdr sexpr)
| _ -> raise (X_syntax_error (scm_list, "Append expects a proper list"))

let rec scm_map f sexpr =
match sexpr with
| ScmNil -> ScmNil
| ScmPair (car, cdr) -> ScmPair (f car, scm_map f cdr)
| _ -> raise (X_syntax_error (sexpr, "Map expects a list"));;

let rec scm_zip f sexpr1 sexpr2 =
match sexpr1, sexpr2 with
| ScmNil, ScmNil -> ScmNil
| ScmPair (car1, cdr1), ScmPair (car2, cdr2) -> ScmPair (f car1 car2, scm_zip f cdr1 cdr2)
| _, _ ->
    let sepxrs = list_to_proper_list [ScmSymbol "sexpr1:"; sexpr1; ScmSymbol "sexpr2:"; sexpr2] in
    raise (X_syntax_error (sepxrs, "Zip expects 2 lists of equal length"));;

let rec scm_list_to_list = function
| ScmPair (hd, tl) -> hd::(scm_list_to_list tl)
| ScmNil -> []
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;
let rec is_valid_list origin_list new_list= match origin_list with
        |[] -> true
        |hd::[] -> let out =match (List.mem hd new_list) with
                    |true -> false
                    |false -> true in
                   out
        |hd::tl ->
                  match  (List.mem hd new_list) with
                  |false -> is_valid_list tl (new_list@[hd])
                  |true -> false

let rec scm_is_list = function
    | ScmPair (hd, tl) -> scm_is_list tl
    | ScmNil -> true
    | _ -> false

let rec scm_list_length = function
| ScmPair (hd, tl) -> 1 + (scm_list_length tl)
| ScmNil -> 0
| sexpr -> raise (X_syntax_error (sexpr, "Expected proper list"));;
let rec scm_improper_list_to_proper_list = function
|ScmPair(a,ScmPair(b,c)) -> ScmPair(a,scm_improper_list_to_proper_list (ScmPair(b,c)))
|ScmPair(a, b) -> ScmPair(a,ScmPair(b,ScmNil))
| sexpr -> raise (X_syntax_error (sexpr, "Expected improper list"));;

let rec last_element= function
    | hd::[] -> hd
    | hd::tl -> last_element tl
    | [] -> raise (X_syntax_error (ScmNil, "Expected non empty list"));;
let rec remove_last_element = function
    | [] -> []
    | hd::[] -> []
    | hd::tl -> hd:: remove_last_element tl;;

let rec untag expr =
let untag_vars vars = List.map (fun s -> ScmSymbol s) vars in
let untag_tagged_list tag exprs = list_to_proper_list (ScmSymbol tag::(List.map untag exprs)) in

let untag_lambda_opt vars var body =
let vars = match vars with
| [] -> ScmSymbol var
| _ -> list_to_improper_list (untag_vars (vars@[var])) in
list_to_proper_list ([ScmSymbol "lambda"; vars]@body) in

match expr with
| (ScmConst (ScmSymbol(_) as sexpr)
    | ScmConst (ScmNil as sexpr)
    | ScmConst (ScmPair (_, _) as sexpr)) -> list_to_proper_list [ScmSymbol "quote"; sexpr]
| ScmConst s -> s
| ScmVar (name) -> ScmSymbol(name)
| ScmIf (test, dit, ScmConst (ScmVoid)) -> untag_tagged_list "if" [test; dit]
| ScmIf (test, dit, dif) -> untag_tagged_list "if" [test; dit; dif]
| ScmSeq(exprs) -> untag_tagged_list "begin" exprs
| ScmSet (var, value) -> untag_tagged_list "set!" [var; value]
| ScmDef (var, value) -> untag_tagged_list "define" [var; value]
| ScmOr (exprs) -> untag_tagged_list "or" exprs
| ScmLambdaSimple (vars, ScmSeq(body)) ->
    let vars = list_to_proper_list (untag_vars vars) in
    let body = List.map untag body in
    list_to_proper_list ([ScmSymbol "lambda"; vars]@body)
| ScmLambdaSimple (vars, body) ->
    let vars = list_to_proper_list (untag_vars vars) in
    list_to_proper_list ([ScmSymbol "lambda"; vars; untag body])
| ScmLambdaOpt (vars, var, ScmSeq(body)) ->
    let body = List.map untag body in
    untag_lambda_opt vars var body
| ScmLambdaOpt (vars, var, body) ->
    let body = [untag body] in
    untag_lambda_opt vars var body
| ScmApplic(procedure, args) -> list_to_proper_list (List.map untag (procedure::args));;


let rec string_of_expr expr =
string_of_sexpr (untag expr)

let scm_number_eq n1 n2 =
match n1, n2 with
| ScmRational(numerator1, denominator1), ScmRational(numerator2, denominator2) ->
        numerator1 = numerator2 && denominator1 = denominator2
| ScmReal(real1), ScmReal(real2) -> abs_float(real1 -. real2) < 0.001
| _, _ -> false

let rec sexpr_eq s1 s2 =
match s1, s2 with
| (ScmVoid, ScmVoid) | (ScmNil, ScmNil)  -> true
| ScmBoolean(bool1), ScmBoolean(bool2) -> bool1 = bool2
| ScmChar(char1), ScmChar(char2) -> char1 = char2
| ScmString(string1), ScmString(string2) -> String.equal string1 string2
| ScmSymbol(symbol1), ScmSymbol(symbol2) -> String.equal symbol1 symbol2
| ScmNumber(number1), ScmNumber(number2) -> scm_number_eq number1 number2
| ScmVector(sexprs1), ScmVector(sexprs2) -> List.for_all2 sexpr_eq sexprs1 sexprs2
| ScmPair(car1, cdr1), ScmPair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
| _, _ -> false

let rec expr_eq e1 e2 =
  match e1, e2 with
  | ScmConst (sexpr1), ScmConst (sexpr2) -> sexpr_eq sexpr1 sexpr2
  | ScmVar (var1), ScmVar (var2) -> String.equal var1 var2
  | ScmIf (test1, dit1, dif1), ScmIf (test2, dit2, dif2) -> (expr_eq test1 test2) &&
                                            (expr_eq dit1 dit2) &&
                                              (expr_eq dif1 dif2)
  | (ScmSeq(exprs1), ScmSeq(exprs2) | ScmOr (exprs1), ScmOr (exprs2)) ->
        List.for_all2 expr_eq exprs1 exprs2
  | (ScmSet (var1, val1), ScmSet (var2, val2) | ScmDef (var1, val1), ScmDef (var2, val2)) ->
        (expr_eq var1 var2) && (expr_eq val1 val2)
  | ScmLambdaSimple (vars1, body1), ScmLambdaSimple (vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmLambdaOpt (vars1, var1, body1), ScmLambdaOpt (vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) && (expr_eq body1 body2)
  | ScmApplic (e1, args1), ScmApplic (e2, args2) ->
     (expr_eq e1 e2) && (List.for_all2 expr_eq args1 args2)
  | _ -> false;;


module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
end;;

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;

let rec scm_improper_list_to_proper_list = function
  |ScmPair(a,ScmPair(b,c)) -> ScmPair(a,scm_improper_list_to_proper_list (ScmPair(b,c)))
  |ScmPair(a, b) -> ScmPair(a,ScmPair(b,ScmNil))
  | sexpr -> raise (X_syntax_error (sexpr, "Expected improper list"));;
let rec last_element= function
  | hd::[] -> hd
  | hd::tl -> last_element tl
  | x-> raise (X_syntax_error(ScmNil,"This should not happen"));;

let rec remove_last_element = function
  | hd::[] -> []
  | hd::tl -> hd:: remove_last_element tl
  | x-> raise (X_syntax_error(ScmNil,"This should not happen"));;


let rec tag_parse_expression sexpr =
let sexpr = macro_expand sexpr in
match sexpr with 
(* Implement tag parsing here *)
|ScmNil -> ScmConst(ScmNil)
|ScmVector(vec)->ScmConst(ScmVector(vec))
|ScmPair(hd,rest) when (not(scm_is_list rest)) -> ScmConst(sexpr)
|ScmBoolean(value)-> ScmConst(ScmBoolean(value))
|ScmChar(char)-> ScmConst(ScmChar(char))
|ScmString(string) -> ScmConst(ScmString(string))
|ScmPair(ScmSymbol("quote"), ScmPair(x, ScmNil)) -> ScmConst(x)
|ScmNumber(x) -> ScmConst(ScmNumber(x))

|ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmNil))) ->
            ScmIf(tag_parse_expression test,tag_parse_expression dit,ScmConst(ScmVoid))
|ScmPair (ScmSymbol "if", ScmPair (test, ScmPair (dit, ScmPair (dif, ScmNil)))) ->
            ScmIf(tag_parse_expression (test),tag_parse_expression (dit),tag_parse_expression (dif))
|ScmPair (ScmSymbol "or", ScmNil) -> ScmConst (ScmBoolean false)
|ScmPair (ScmSymbol "or", ScmPair (a, ScmNil)) -> tag_parse_expression a
|ScmPair(ScmSymbol "or", ScmPair (first, rest)) ->
    ScmOr(List.map tag_parse_expression (scm_list_to_list (ScmPair (first, rest))))
(*TODO handle the exception when var is not correct*)
|ScmPair (ScmSymbol "define", ScmPair(ScmPair (var, args),lambdaExp)) ->
    ScmDef (tag_parse_expression var, tag_parse_expression (ScmPair (ScmSymbol "lambda",ScmPair (args,lambdaExp))))
(*TODO handle the exception when var is not correct*)
|ScmPair (ScmSymbol "define" , ScmPair ((ScmSymbol var),ScmPair (value ,ScmNil))) ->
    ScmDef (tag_parse_expression ((ScmSymbol var)), tag_parse_expression value)
(*TODO handle the exception when var is not correct*)
|ScmPair(ScmSymbol "set!",ScmPair(ScmSymbol var,ScmPair(value,ScmNil))) ->
    ScmSet(tag_parse_expression (ScmSymbol var),tag_parse_expression value)
(* simple lambda*)
|ScmPair(ScmSymbol "lambda", ScmPair(vars,exprs))  when (scm_is_list vars)->
            let lengthExprs = scm_list_length exprs in
            let vars=List.map string_of_expr ( List.map tag_parse_expression (scm_list_to_list vars)) in
            let exprs= List.map tag_parse_expression (scm_list_to_list exprs) in
             let vals=  match lengthExprs with
                | 1 -> ScmLambdaSimple(vars,List.hd exprs)
                | _ -> ScmLambdaSimple(vars,ScmSeq(exprs)) in
            vals

 (* vardic lambda*)
|ScmPair(ScmSymbol "lambda", ScmPair(ScmSymbol var,exprs))->
            let lengthExprs = scm_list_length exprs in
            let exprs= List.map tag_parse_expression (scm_list_to_list exprs) in
             let vals=  match lengthExprs with
                | 1 -> ScmLambdaOpt( [],var,List.hd exprs)
                | _ -> ScmLambdaOpt([],var,ScmSeq(exprs)) in
            vals
(* opt lambda*)
|ScmPair(ScmSymbol "lambda", ScmPair(vars,exprs))->
            let lengthExprs = scm_list_length exprs in
            let vars=List.map string_of_expr ( List.map tag_parse_expression (scm_list_to_list (scm_improper_list_to_proper_list vars))) in
            let exprs= List.map tag_parse_expression (scm_list_to_list exprs) in
             let vals=  match lengthExprs with
                | 1 -> ScmLambdaOpt(remove_last_element vars,last_element vars,List.hd exprs)
                | _ -> ScmLambdaOpt(remove_last_element vars,last_element vars,ScmSeq(exprs)) in
            vals
|ScmPair (ScmSymbol "begin",exps) ->
         let length = scm_list_length exps in
         let exps= List.map tag_parse_expression (scm_list_to_list exps) in
         let out = match length with
         | 1-> List.hd exps
         | _ ->  ScmSeq(exps) in
         out

(*Application*)
|ScmPair(app,rest) when (scm_is_list rest)-> ScmApplic(tag_parse_expression app,List.map tag_parse_expression (scm_list_to_list rest))
|ScmSymbol(symbol) ->
                    let vals= match List.mem symbol reserved_word_list with
                        | true -> raise (X_reserved_word(symbol))
                        | _ -> ScmVar(symbol) in
                    vals
| _ -> raise (X_syntax_error (sexpr, "Sexpr structure not recognized"))


and macro_expand sexpr =
match sexpr with
(* Handle macro expansion patterns here *)
|ScmPair(ScmSymbol "cond", conds) ->
      let args= scm_list_to_list conds in
      let rec parse_conds = function
      | [] -> raise (X_syntax_error((sexpr, "the cond  structure not valid")))
      | hd::[] ->
                    let out= match hd with
                        |ScmPair(ScmSymbol "else",cons) -> ScmPair(ScmSymbol "begin",cons)
                        | _ -> ScmPair(ScmSymbol "if",hd) in
                    out
      | hd::tl ->
                match hd with
                |ScmPair(ScmSymbol "else",cons) ->ScmPair(ScmSymbol "begin",cons)
                |ScmPair(ScmSymbol symbol,ScmPair(ScmSymbol "=>", dit)) ->
                                                    let nt_arrow_test= ScmSymbol "value" in
                                                    let nt_arrow_dit = ScmPair(ScmPair(ScmSymbol "f",ScmNil),
                                                                               ScmPair(ScmSymbol "value",ScmNil)) in
                                                    let nt_arrow_dif =  ScmPair(ScmSymbol "rest",ScmNil) in
                                                    let nt_if=ScmPair(ScmPair (ScmSymbol "if", ScmPair(nt_arrow_test,
                                                                                               ScmPair(nt_arrow_dit,
                                                                                               ScmPair(nt_arrow_dif,ScmNil))))
                                                                     ,ScmNil)  in
                                                   let nt_vals=ScmPair(ScmSymbol "value",ScmPair(ScmSymbol "f",ScmPair(ScmSymbol "rest",ScmNil))) in
                                                   let nt_lambda=ScmPair(ScmSymbol "lambda",ScmPair(nt_vals,nt_if)) in
                                                   let nt_dit= ScmPair(ScmSymbol "lambda",ScmPair(ScmNil,dit))      in
                                                   let nt_dif= ScmPair(ScmSymbol "lambda",ScmPair(ScmNil,ScmPair((parse_conds tl),ScmNil)))     in
                                                   let nt_list=ScmPair(ScmSymbol symbol,ScmPair(nt_dit,ScmPair(nt_dif,ScmNil))) in
                                                    ScmPair(nt_lambda,nt_list)
                |_ ->
                    ScmPair(ScmSymbol "if",
                       ScmPair(List.hd (scm_list_to_list hd),
                       ScmPair (ScmPair(ScmSymbol "begin",list_to_proper_list (List.tl (scm_list_to_list hd))),
                      ScmPair((parse_conds tl),ScmNil))))in
      parse_conds args
|ScmPair(ScmSymbol "and",exprs) ->
            let rec and_to_if_expr = function
            |ScmPair(exp1,ScmNil) -> exp1
            |ScmPair(exp1,rest) -> ScmPair(ScmSymbol "if",ScmPair(exp1,ScmPair(and_to_if_expr rest,ScmPair(ScmBoolean (false),ScmNil))))
            |_ -> ScmBoolean (true) in
            and_to_if_expr exprs
|ScmPair(ScmSymbol "let",ScmPair(args,bodies)) ->
            let argsVars = scm_map (fun (x)-> List.hd (scm_list_to_list x)) args in
            let argsVals = scm_map (fun (x)-> match x with
                                                |ScmPair(_,ScmPair(tl,ScmNil)) -> tl
                                                |ScmPair(_,tl) -> tl
                                                |_ -> raise (X_syntax_error (x, "let args is not in the correct syntax3"))) args in
            let out = match (is_valid_list (scm_list_to_list argsVars) []) with
                |true -> ScmPair(ScmPair(ScmSymbol "lambda",ScmPair(argsVars, bodies)),argsVals)
                |false -> raise (X_syntax_error(argsVars,"same var twice")) in
            out

(*            args*)
|ScmPair(ScmSymbol "let*",ScmPair(args,bodies)) ->
            let argsVars = scm_map (fun (x)-> List.hd (scm_list_to_list x)) args in
            let argsVals = scm_map (fun (x)-> match x with
                                               |ScmPair(_,ScmPair(tl,ScmNil)) -> tl
                                               |ScmPair(_,tl) -> tl
                                               |_ -> raise (X_syntax_error (x, "let args is not in the correct syntax2"))) args in
            let rec make_lists_to_lambdas lst1 lst2 =
                match lst1,lst2 with
                |hd1::[],hd2::[] -> ScmPair(ScmPair(ScmSymbol "lambda",ScmPair(ScmPair(hd1,ScmNil),bodies)),ScmPair(hd2,ScmNil))
                |hd1::tl1,hd2::tl2 -> ScmPair(ScmPair(ScmSymbol "lambda",ScmPair(ScmPair(hd1,ScmNil),ScmPair(make_lists_to_lambdas tl1 tl2,ScmNil))),ScmPair(hd2,ScmNil))
                | x,y -> raise( X_syntax_error(ScmNil,"This should not happen")) in
            let out = match List.length (scm_list_to_list argsVars) with
                        |0 -> ScmPair(ScmPair(ScmSymbol "lambda",ScmPair(argsVars,scm_map (fun a -> macro_expand a) bodies)),argsVals)
                        |_ -> make_lists_to_lambdas (scm_list_to_list argsVars) (scm_list_to_list argsVals) in
            out
|ScmPair(ScmSymbol "letrec",ScmPair(args,bodies)) ->
            let argsVars = scm_map (fun (x)-> List.hd (scm_list_to_list x)) args in
            let argsVals = scm_map (fun (x)-> match x with
                                                |ScmPair(_,ScmPair(tl,ScmNil)) -> tl
                                                |ScmPair(_,tl) -> tl
                                                |_ -> raise (X_syntax_error (x, "let args is not in the correct syntax1"))) args in
            let argsWhateverList = scm_map (fun x -> ScmPair(x,ScmPair(ScmSymbol "quote",ScmPair(ScmSymbol "whatever",ScmNil)))) argsVars in
            let argsRealValueList = scm_zip (fun var value -> ScmPair(ScmSymbol "set!",ScmPair(var,ScmPair(value,ScmNil)))) argsVars argsVals in
            let newBodies = scm_append argsRealValueList bodies in
            let out = match (is_valid_list (scm_list_to_list argsVars) []) with
                        |true -> macro_expand(ScmPair(ScmSymbol "let", ScmPair(argsWhateverList,scm_map (fun a -> macro_expand a) newBodies)))
                        |false -> raise (X_syntax_error (argsVars, "same var twice")) in
            out
|ScmPair(ScmSymbol "quasiquote",ScmPair(qq_args,ScmNil))->
        let rec parse_body= function
            | ScmNil -> ScmPair (ScmSymbol ("quote"),
                                 ScmPair (ScmNil, ScmNil))
            | ScmSymbol (symbol) -> ScmPair (ScmSymbol ("quote"),
                                              ScmPair (ScmSymbol symbol, ScmNil))
            | ScmPair (ScmSymbol ("unquote"), ScmPair (uq_body, ScmNil)) -> uq_body
            | ScmPair (ScmSymbol ("unquote-splicing"), ScmPair (body, ScmNil)) ->  ScmPair (ScmSymbol ("quote"),
                                                                                    ScmPair (ScmPair (ScmSymbol ("unquote-splicing"),
                                                                                                         ScmPair (body, ScmNil)),
                                                                                    ScmNil))
            | ScmVector (vector_body) ->
                                        let vector_body_list= list_to_proper_list vector_body in
                                        scm_append (ScmPair(ScmSymbol "list->vector", ScmNil))
                                                   (ScmPair((parse_body vector_body_list), ScmNil))
             | ScmPair (first, rest) -> (match first with
                                                | ScmPair (ScmSymbol ("unquote-splicing"), ScmPair (a,ScmNil)) ->
                                                        scm_append (scm_append (ScmPair(ScmSymbol ("append"), ScmNil)) (ScmPair (a, ScmNil)))
                                                                   (ScmPair ((parse_body rest), ScmNil))
                                                | _ ->
                                                        scm_append (scm_append (ScmPair(ScmSymbol ("cons"), ScmNil))
                                                                               (ScmPair ((parse_body first), ScmNil)))
                                                                   (ScmPair ((parse_body rest),ScmNil)))
            | sexpr -> sexpr in
       parse_body qq_args
| _ -> sexpr
end;;


