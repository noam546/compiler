(* reader.ml
 * A skeleton for the reader for the 2021-2022 course on compiler-construction
 *)

#use "pc.ml";;

let rec gcd a b =
  match (a, b) with
  | (0, b) -> b
  | (a, 0) -> a
  | (a, b) -> gcd b (a mod b);;

type scm_number =
  | ScmRational of (int * int)
  | ScmReal of float;;

type sexpr =
  | ScmVoid
  | ScmNil
  | ScmBoolean of bool
  | ScmChar of char
  | ScmString of string
  | ScmSymbol of string
  | ScmNumber of scm_number
  | ScmVector of (sexpr list)
  | ScmPair of (sexpr * sexpr);;

module type READER = sig
    val nt_sexpr : sexpr PC.parser
end;; (* end of READER signature *)

module Reader : READER = struct
open PC;;

let unitify nt = pack nt (fun _ -> ());;

let rec nt_whitespace str =
  const (fun ch -> ch <= ' ') str
and nt_end_of_line_or_file str =
  let nt1 = unitify (char '\n') in
  let nt2 = unitify nt_end_of_input in
  let nt1 = disj nt1 nt2 in
  nt1 str
and nt_line_comment str =
    let nt_end=
        disj (unitify (char '\n') )(unitify nt_end_of_input) in
    let nt1 = char ';' in
    let nt2 = diff nt_any nt_end in
    let nt2 = star nt2 in
    let nt1 = caten nt1 (caten nt2 nt_end) in
    let nt1= unitify nt1 in
    nt1 str
and nt_paired_comment str =
  let nt1 = word "{" in
  let nt2 = caten nt_skip_star (char '}') in
  let nt2 = pack nt2 (fun _ -> ()) in
  let nt3 = plus nt_sexpr in
  let nt4 = char '}' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ()) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = unitify nt1 in
  nt1 str
and nt_sexpr_comment str =
    let pref = word "#;" in
    let unite = caten pref nt_sexpr in
    let nt1=  unitify unite in
    nt1 str
and nt_comment str =
  let nt1 =disj_list [nt_line_comment;nt_sexpr_comment;nt_paired_comment] in
     nt1 str
and nt_skip_star str =
  let nt1 = disj (unitify nt_whitespace) nt_comment in
  let nt1 = unitify (star nt1) in
  nt1 str
and make_skipped_star (nt : 'a parser) =
  let nt1 = caten nt_skip_star (caten nt nt_skip_star) in
  let nt1 = pack nt1 (fun (_, (e, _)) -> e) in
  nt1
and nt_natural str =
    let nt2 = range '0' '9' in
    let nt2 = pack nt2
                (let delta = int_of_char '0' in
                fun ch -> (int_of_char ch) - delta) in
    let nt2 = plus nt2 in
    let nt2 = pack nt2
                (fun digits -> List.fold_left
                (fun a b -> 10 * a + b)
                0
                digits) in
    let nt2 = pack nt2 (fun n -> n) in
    nt2 str
and nt_is_positive =
    let nt1 = pack (char '+') (fun _ -> true) in
    let nt2 = pack (char '-') (fun _ -> false) in
    let nt1 = disj nt1 nt2 in
    let nt1 = maybe nt1 in
    let nt1 = pack nt1 (function
                | None -> true
                | Some b -> b) in
    nt1
and nt_int str =
    let nt1 = caten nt_is_positive nt_natural in
    let nt1 = pack nt1 (fun (x,n) ->
                if x then n
                else -1 * n) in
    nt1 str
and nt_frac str =
    let nt1 = caten (caten nt_int (char '/')) nt_natural in
    let nt1 = pack nt1 (fun ((l,d),r) ->
            let nt_gcd = (gcd l r) in
            let l_gcd = l / nt_gcd in
            let r_gcd = r / nt_gcd in
            if r = 0 then raise X_no_match
            else ScmRational (l_gcd,r_gcd)) in
    nt1 str
and nt_integer_part str =
    nt_natural str
and nt_mantissa str =
    let nt2 = range '0' '9' in
    let nt2 = plus nt2 in
    let nt2 = pack nt2 (fun n -> list_to_string n) in
    nt2 str
and nt_exponent str =
    let ten = word "*10**" in
    let ten2 = word "*10^" in
    let e = word_ci "e" in
    let token = disj ten (disj ten2 e) in
    let nt1 = caten token nt_int in
    let nt1 = pack nt1 (fun (_,n) -> n) in
    nt1 str
and nt_floatA str =
    let nt1 = maybe nt_mantissa in
    let nt1 = pack nt1 (fun n -> match n with
                                            | None -> "0"
                                            | Some man -> man) in
    let nt2 = maybe nt_exponent in
    let nt2 = pack nt2 (fun n -> match n with
                                            | None -> 0
                                            | Some exp -> exp) in
    let dot = word "." in
    let nt1 = caten (caten nt_natural dot) (caten nt1 nt2) in
    let nt1 = pack nt1 (fun ((num,d),(man,exp)) -> float_of_string ((string_of_int num)^"."^man^"e"^(string_of_int exp))) in
    nt1 str
and nt_floatB str =
    let dot = pack (char '.') (fun b -> b) in
    let nt1 = maybe nt_exponent in
    let nt1 = pack nt1 (fun n -> match n with
                                        | None -> 0
                                        | Some exp -> exp) in
    let nt1 = caten (caten dot nt_mantissa) nt1 in
    let nt1 = pack nt1 (fun ((d,m),e) -> float_of_string ("."^m^"e"^(string_of_int e))) in
    nt1 str
and nt_floatC str =
    let nt1 = caten nt_natural nt_exponent in
    let nt1 = pack nt1 (fun (a,b) -> float_of_string ((string_of_int a)^".e"^(string_of_int b))) in
    nt1 str
and nt_float str =
    let nt2 = disj nt_floatA (disj nt_floatB nt_floatC) in
    let nt1 = caten nt_is_positive nt2 in
    let nt1 = pack nt1 (fun (sign,fl) -> match sign with
                                            | true -> ScmReal fl
                                            | false -> ScmReal (-1.0 *. fl)) in
    nt1 str
and nt_number str =
  let nt1 = nt_float in
  let nt2 = nt_frac in
  let nt3 = pack nt_int (fun n -> ScmRational(n, 1)) in
  let nt1 = disj nt1 (disj nt2 nt3) in
  let nt1 = pack nt1 (fun r -> ScmNumber r) in
  let nt1 = not_followed_by nt1 nt_symbol_char in
  nt1 str
and nt_boolean str =
    let nt1 = word_ci "#f" in
    let nt1 = pack nt1 (fun _ -> false) in
    let nt2 = word_ci "#t" in
    let nt2 = pack nt2 (fun _ -> true) in
    let nt1 = disj nt1 nt2 in
    let nt1 = pack nt1 (fun b -> ScmBoolean b) in
    nt1 str
and nt_char_simple str =
     let nt_f = const( fun c -> 32 < int_of_char c )in
     nt_f str
and make_named_char char_name ch =
    let nt_name = pack (word_ci char_name) (fun char_name -> ch) in
    nt_name
and nt_char_named str =
  let nt1 =
    disj_list [(make_named_char "newline" '\n');
               (make_named_char "page" '\012');
               (make_named_char "nul" '\000');
               (make_named_char "return" '\r');
               (make_named_char "space" ' ');
               (make_named_char "tab" '\t')] in
  nt1 str
and nt_char_hex str =
    let nt1 = char_ci 'x' in
    let nt2 = range '0' '9' in
    let nt2 = pack nt2
                (let delta = int_of_char '0' in
                fun ch -> (int_of_char ch) - delta) in
    let nt3 = range_ci 'a' 'f' in
    let nt3 = pack nt3
                (let delta = int_of_char 'a' - 10 in
                fun ch -> (int_of_char (lowercase_ascii ch)) - delta) in
    let nt2 = disj nt2 nt3 in
    let nt2 = plus nt2 in
    let nt2 = pack nt2
                (fun digits -> List.fold_left
                (fun a b -> 16 * a + b)
                0
                digits ) in
    let nt1 = caten nt1 nt2 in
    let nt1 = pack nt1 (fun (_,n) -> (char_of_int n)) in
    nt1 str
and nt_char str =
    let nt_prefix = word "#\\" in
    let nt_char_lst= disj_list [nt_char_hex;nt_char_named;nt_char_simple] in
    let nt1 = caten nt_prefix nt_char_lst in
    let nt1 = pack nt1 (fun (pre,ch) -> ScmChar ch) in
    let nt1 = not_followed_by nt1 nt_symbol_char in
    nt1 str
and nt_symbol_char str =
        let nt1 = range '0' '9' in
        let nt2 = range 'a' 'z' in
        let nt3 = range 'A' 'Z' in
        let nt4 = disj_list[(char '!');(char '$');(char '^');(char '*');(char '-');(char '_');
        (char '=');(char '<');(char '>');(char '?');(char '/');(char ':');(char '+');] in
        let nt1 = disj_list [nt1;nt2;nt3;nt4] in
        nt1 str
and nt_symbol str =
  let nt1 = plus nt_symbol_char in
  let nt1 = pack nt1 list_to_string in
  let nt1 = pack nt1 (fun name -> ScmSymbol name) in
  let nt1 = diff nt1 nt_number in
  nt1 str
and nt_meta str =
    let word1 = pack (word_ci "\\n") (fun _ ->  '\n' ) in
    let  word2 = pack (word_ci "\\t") (fun _ ->  '\t') in
    let  word3 = pack (word_ci "\\r") (fun _ ->  '\r') in
    let  word5 = pack (word_ci "\\f") (fun _ ->  '\012') in
    let  word6 = pack (word_ci "~~") (fun _ ->  '~') in
   let  word4 = pack (word_ci "\\\\") (fun _ ->  '\\') in
  let  word7= pack (word_ci "\\\"") (fun _ ->  '\"') in
    let nt1 = disj_list [word1;word2;word3;word5;word6;word7;word4] in
    let nt1 = pack nt1 (fun a ->  a ) in
    nt1 str
and nt_string_hex str =
            let pref = word "\\" in
            let fin = word ";" in
            let nt1= caten (caten pref nt_char_hex) fin in
            let nt1 = pack nt1 (fun ((_,a),_)-> a) in
            nt1 str
 and nt_interpolated str =
        let inter = caten (caten (word "~{")  nt_sexpr) (char '}') in
        let nt1 = pack inter (fun ((a,b),c)-> b) in
        nt1 str
and nt_literal str =
        let nt1 = const (fun ch -> (ch != '\\') && (ch != '"')&& (ch != '~'))  in
        nt1 str
and nt_string_static str =
        let nt_all =  disj_list [nt_meta;nt_string_hex;nt_literal] in
        let nt_all = plus nt_all in
        let nt1 = pack nt_all list_to_string in
        nt1 str
and nt_string str =
        let rec list_to_proper_list = function
                            | [] -> ScmNil
                            | hd::tl -> ScmPair (hd, list_to_proper_list tl) in
       let nt_QM =word "\"" in
       let nt_stat = pack nt_string_static (fun name -> ScmString name) in
       let nt_inter =pack nt_interpolated (fun b-> ScmPair (ScmSymbol "format",ScmPair (ScmString "~a" ,ScmPair(b,ScmNil)))) in
         let nt3 = star (disj nt_inter nt_stat) in
        let nt3 = caten (caten nt_QM nt3 ) nt_QM in
        let nt3 =pack nt3 (fun ((a,str_elements),b) ->
                                   match str_elements with
                                   | [] -> ScmString ""
                                   | hd::[] -> hd
                                   | hd::tl -> list_to_proper_list ([ScmSymbol "string-append"]@str_elements)) in
      nt3 str
and nt_vector str =
  let nt1 = word "#(" in
  let nt2 = caten nt_skip_star (char ')') in
  let nt2 = pack nt2 (fun _ -> ScmVector []) in
  let nt3 = plus nt_sexpr in
  let nt4 = char ')' in
  let nt3 = caten nt3 nt4 in
  let nt3 = pack nt3 (fun (sexprs, _) -> ScmVector sexprs) in
  let nt2 = disj nt2 nt3 in
  let nt1 = caten nt1 nt2 in
  let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
  nt1 str
and nt_list str =
    let nt1 = disj nt_proper_list nt_improper_list in
    nt1 str
and nt_proper_list str =
    let pref= char '(' in
    let nt2 = caten nt_skip_star (char ')') in
    let nt2 = pack nt2 (fun _ -> ScmNil ) in
    let nt1 = star nt_sexpr in
    let nt1 =caten nt1 (char ')') in
    let nt1 = pack nt1 (fun (exp,r)-> list_to_sexprs exp ScmNil) in
    let nt1 = disj nt2 nt1 in
    let nt1 = caten pref nt1 in
     let nt1 = pack nt1 (fun (_, sexpr) -> sexpr) in
    nt1 str
and nt_improper_list str =
    let nt1 = plus nt_sexpr in
    let nt1 = caten (caten (char '(') nt1) (caten (caten (char '.') nt_sexpr) (char ')')) in
    let nt1 = pack nt1 (fun ((left,sexpr1),((dot,sexpr2),right)) ->  list_to_sexprs sexpr1 sexpr2) in
    nt1 str
and list_to_sexprs lst last =
    let rec lst_to_sexprs lst last =
        if (List.length lst) = 0 then last
        else ScmPair (List.hd lst,lst_to_sexprs (List.tl lst) last) in
    lst_to_sexprs lst last
and nt_quoted str =
    let nt1 = caten (word "'") nt_sexpr in
    let nt1 = pack nt1 (fun (a,b) -> ScmPair ((ScmSymbol "quote"),ScmPair (b,ScmNil)) ) in
    nt1 str
and nt_quasiquoted str =
    let nt1 = caten (char '`') nt_sexpr in
    let nt1 = pack nt1 (fun (a,b) -> ScmPair ((ScmSymbol "quasiquote"),ScmPair (b,ScmNil)) ) in
    nt1 str
and nt_unquoted str =
    let nt1 = caten (char ',') nt_sexpr in
    let nt1 = pack nt1 (fun (a,b) -> ScmPair ((ScmSymbol "unquote"),ScmPair (b,ScmNil)) ) in
    nt1 str
and nt_unquoted_and_spliced str =
    let nt1 = caten (word ",@") nt_sexpr in
    let nt1 = pack nt1 (fun (a,b) -> ScmPair ((ScmSymbol "unquote-splicing"),ScmPair (b,ScmNil)) ) in
    nt1 str
and nt_quoted_forms str =
    let nt1 = disj_list [nt_quoted;nt_quasiquoted;nt_unquoted;nt_unquoted_and_spliced] in
    let nt1 = pack nt1 (fun a -> a) in
    nt1 str
and nt_sexpr str =
  let nt1 =
    disj_list [nt_number; nt_boolean; nt_char; nt_symbol;
               nt_string; nt_vector; nt_list; nt_quoted_forms] in
  let nt1 = make_skipped_star nt1 in
  nt1 str;;

end;; (* end of struct Reader *)

let rec string_of_sexpr = function
  | ScmVoid -> "#<void>"
  | ScmNil -> "()"
  | ScmBoolean(false) -> "#f"
  | ScmBoolean(true) -> "#t"
  | ScmChar('\n') -> "#\\newline"
  | ScmChar('\r') -> "#\\return"
  | ScmChar('\012') -> "#\\page"
  | ScmChar('\t') -> "#\\tab"
  | ScmChar(' ') -> "#\\space"
  | ScmChar(ch) ->
     if (ch < ' ')
     then let n = int_of_char ch in
          Printf.sprintf "#\\x%x" n
     else Printf.sprintf "#\\%c" ch
  | ScmString(str) ->
     Printf.sprintf "\"%s\""
       (String.concat ""
          (List.map
             (function
              | '\n' -> "\\n"
              | '\012' -> "\\f"
              | '\r' -> "\\r"
              | '\t' -> "\\t"
              | ch ->
                 if (ch < ' ')
                 then Printf.sprintf "\\x%x;" (int_of_char ch)
                 else Printf.sprintf "%c" ch)
             (string_to_list str)))
  | ScmSymbol(sym) -> sym
  | ScmNumber(ScmRational(0, _)) -> "0"
  | ScmNumber(ScmRational(num, 1)) -> Printf.sprintf "%d" num
  | ScmNumber(ScmRational(num, -1)) -> Printf.sprintf "%d" (- num)
  | ScmNumber(ScmRational(num, den)) -> Printf.sprintf "%d/%d" num den
  | ScmNumber(ScmReal(x)) -> Printf.sprintf "%f" x
  | ScmVector(sexprs) ->
     let strings = List.map string_of_sexpr sexprs in
     let inner_string = String.concat " " strings in
     Printf.sprintf "#(%s)" inner_string
  | ScmPair(ScmSymbol "quote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "'%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "quasiquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf "`%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",%s" (string_of_sexpr sexpr)
  | ScmPair(ScmSymbol "unquote-splicing",
            ScmPair(sexpr, ScmNil)) ->
     Printf.sprintf ",@%s" (string_of_sexpr sexpr)
  | ScmPair(car, cdr) ->
     string_of_sexpr' (string_of_sexpr car) cdr
and string_of_sexpr' car_string = function
  | ScmNil -> Printf.sprintf "(%s)" car_string
  | ScmPair(cadr, cddr) ->
     let new_car_string =
       Printf.sprintf "%s %s" car_string (string_of_sexpr cadr) in
     string_of_sexpr' new_car_string cddr
  | cdr ->
     let cdr_string = (string_of_sexpr cdr) in
     Printf.sprintf "(%s . %s)" car_string cdr_string;;
