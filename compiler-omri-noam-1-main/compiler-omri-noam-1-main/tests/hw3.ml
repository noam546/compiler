
#use "semantic-analyser.ml";;

type 'a test_case = {name: string; test: 'a -> expr' ; input: 'a; expected: expr'}

type case =
| ExprCase of expr test_case
| Expr'Case of expr' test_case

let cases = [ExprCase {name="0-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmDef ((ScmVar ("f")), (ScmLambdaOpt ([], "x", ScmVar ("x")))));
expected=(ScmDef' ((VarFree ("f")), (ScmLambdaOpt' ([], "x", ScmVar' (VarParam ("x", 0))))))};

ExprCase {name="1-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmSet ((ScmVar ("y")), (ScmApplic ((ScmVar ("+")), [ScmIf ((ScmConst (ScmNumber (ScmRational (1, 1)))), (ScmConst (ScmNumber (ScmRational (2, 1)))), (ScmConst (ScmVoid)));ScmSeq [ScmConst (ScmNumber (ScmRational (4, 1)));ScmConst (ScmString ("hello"))]]))));
expected=(ScmSet' ((VarFree ("y")), (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmIf' ((ScmConst' (ScmNumber (ScmRational (1, 1)))), (ScmConst' (ScmNumber (ScmRational (2, 1)))), (ScmConst' (ScmVoid)));ScmSeq' [ScmConst' (ScmNumber (ScmRational (4, 1)));ScmConst' (ScmString ("hello"))]]))))};

ExprCase {name="2-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x";"y";"z"], (ScmIf ((ScmApplic ((ScmVar ("f?")), [ScmVar ("a")])), (ScmApplic ((ScmVar ("g")), [ScmVar ("b")])), (ScmIf ((ScmApplic ((ScmVar ("g?")), [ScmVar ("c")])), (ScmSeq [ScmApplic ((ScmVar ("f")), [ScmVar ("d")]);ScmApplic ((ScmVar ("f")), [ScmVar ("e")])]), (ScmSeq [ScmApplic ((ScmVar ("h")), [ScmVar ("w")]);ScmApplic ((ScmVar ("f")), [ScmVar ("l")]);ScmApplic ((ScmVar ("g")), [ScmApplic ((ScmVar ("f")), [ScmVar ("m")])])])))))));
expected=(ScmLambdaSimple' (["x";"y";"z"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f?"))), [ScmVar' (VarFree ("a"))])), (ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("b"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g?"))), [ScmVar' (VarFree ("c"))])), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("d"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("e"))])]), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("h"))), [ScmVar' (VarFree ("w"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("l"))]);ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("m"))])])])))))))};

ExprCase {name="3-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmIf ((ScmVar ("x")), (ScmApplic ((ScmVar ("x")), [])), (ScmVar ("x"))));
expected=(ScmIf' ((ScmVar' (VarFree ("x"))), (ScmApplic' ((ScmVar' (VarFree ("x"))), [])), (ScmVar' (VarFree ("x")))))};

ExprCase {name="4-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaOpt ([], "x", ScmSeq [ScmLambdaSimple (["x"], (ScmSet ((ScmVar ("x")), (ScmConst (ScmNumber (ScmRational (1, 1)))))));ScmVar ("x")]));
expected=(ScmLambdaOpt' ([], "x", ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))));ScmVar' (VarParam ("x", 0))]))};

ExprCase {name="5-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["a";"b";"c";"d";"e"], (ScmApplic ((ScmVar ("x")), [ScmApplic ((ScmVar ("y")), [ScmVar ("z")]);ScmApplic ((ScmVar ("f")), [ScmVar ("g");ScmVar ("h")]);ScmApplic ((ScmVar ("j")), [ScmApplic ((ScmVar ("k")), [ScmApplic ((ScmVar ("l")), [ScmApplic ((ScmVar ("m")), [ScmVar ("n")])])])])]))));
expected=(ScmLambdaSimple' (["a";"b";"c";"d";"e"], (ScmApplic' ((ScmVar' (VarFree ("x"))), [ScmApplic' ((ScmVar' (VarFree ("y"))), [ScmVar' (VarFree ("z"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("g"));ScmVar' (VarFree ("h"))]);ScmApplic' ((ScmVar' (VarFree ("j"))), [ScmApplic' ((ScmVar' (VarFree ("k"))), [ScmApplic' ((ScmVar' (VarFree ("l"))), [ScmApplic' ((ScmVar' (VarFree ("m"))), [ScmVar' (VarFree ("n"))])])])])]))))};

ExprCase {name="6-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x";"y";"z";"w"], (ScmIf ((ScmApplic ((ScmVar ("even?")), [ScmVar ("a")])), (ScmApplic ((ScmVar ("b")), [ScmVar ("c")])), (ScmApplic ((ScmVar ("d")), [ScmVar ("e")]))))));
expected=(ScmLambdaSimple' (["x";"y";"z";"w"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("even?"))), [ScmVar' (VarFree ("a"))])), (ScmApplic' ((ScmVar' (VarFree ("b"))), [ScmVar' (VarFree ("c"))])), (ScmApplic' ((ScmVar' (VarFree ("d"))), [ScmVar' (VarFree ("e"))]))))))};

ExprCase {name="7-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmIf ((ScmApplic ((ScmLambdaSimple (["y"], (ScmVar ("x")))), [])), (ScmApplic ((ScmLambdaSimple (["x"], (ScmSeq [ScmSet ((ScmVar ("x")), (ScmVar ("y")));ScmLambdaSimple ([], (ScmSet ((ScmVar ("x")), (ScmConst (ScmNumber (ScmRational (1, 1)))))))]))), [ScmConst (ScmSymbol ("a"))])), (ScmLambdaSimple (["x"], (ScmSet ((ScmVar ("x")), (ScmVar ("y"))))))));
expected=(ScmIf' ((ScmApplic' ((ScmLambdaSimple' (["y"], (ScmVar' (VarFree ("x"))))), [])), (ScmApplic' ((ScmLambdaSimple' (["x"], (ScmSeq' [ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y"))));ScmLambdaSimple' ([], (ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))]))), [ScmConst' (ScmSymbol ("a"))])), (ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y")))))))))};

ExprCase {name="8-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmApplic ((ScmLambdaSimple (["x"], (ScmIf ((ScmApplic ((ScmVar ("a")), [ScmConst (ScmNumber (ScmRational (1, 1)))])), (ScmApplic ((ScmVar ("b")), [ScmConst (ScmNumber (ScmRational (2, 1)))])), (ScmApplic ((ScmLambdaSimple (["x"], (ScmSet ((ScmVar ("c")), (ScmConst (ScmNumber (ScmRational (0, 1)))))))), [ScmConst (ScmNumber (ScmRational (3, 1)))])))))), [ScmLambdaSimple (["x"], (ScmVar ("d")))]));
expected=(ScmApplic' ((ScmLambdaSimple' (["x"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("a"))), [ScmConst' (ScmNumber (ScmRational (1, 1)))])), (ScmApplic' ((ScmVar' (VarFree ("b"))), [ScmConst' (ScmNumber (ScmRational (2, 1)))])), (ScmApplic' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarFree ("c")), (ScmConst' (ScmNumber (ScmRational (0, 1)))))))), [ScmConst' (ScmNumber (ScmRational (3, 1)))])))))), [ScmLambdaSimple' (["x"], (ScmVar' (VarFree ("d"))))]))};

ExprCase {name="9-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaOpt (["x";"y"], "z", ScmApplic ((ScmVar ("+")), [ScmVar ("a");ScmVar ("b");ScmLambdaSimple (["z"], (ScmApplic ((ScmVar ("+")), [ScmVar ("c");ScmLambdaSimple ([], (ScmApplic ((ScmVar ("+")), [ScmVar ("d");ScmVar ("e")])))])))])));
expected=(ScmLambdaOpt' (["x";"y"], "z", ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmLambdaSimple' ([], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("d"));ScmVar' (VarFree ("e"))])))])))])))};

ExprCase {name="10-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmSeq [ScmApplic ((ScmVar ("x")), []);ScmSet ((ScmVar ("x")), (ScmApplic ((ScmVar ("x")), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])))};

ExprCase {name="11-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmOr [ScmApplic ((ScmLambdaOpt (["y"], "z", ScmApplic ((ScmLambdaSimple ([], (ScmApplic ((ScmLambdaSimple ([], (ScmApplic ((ScmVar ("+")), [ScmVar ("a");ScmVar ("b")])))), [])))), []))), [ScmVar ("c");ScmConst (ScmNumber (ScmRational (1, 1)))]);ScmLambdaSimple ([], (ScmSet ((ScmVar ("d")), (ScmVar ("w")))));ScmApplic ((ScmVar ("w")), [ScmVar ("w")])])));
expected=(ScmLambdaSimple' (["x"], (ScmOr' [ScmApplic' ((ScmLambdaOpt' (["y"], "z", ScmApplic' ((ScmLambdaSimple' ([], (ScmApplic' ((ScmLambdaSimple' ([], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))), [])))), []))), [ScmVar' (VarFree ("c"));ScmConst' (ScmNumber (ScmRational (1, 1)))]);ScmLambdaSimple' ([], (ScmSet' ((VarFree ("d")), (ScmVar' (VarFree ("w"))))));ScmApplic' ((ScmVar' (VarFree ("w"))), [ScmVar' (VarFree ("w"))])])))};

ExprCase {name="12-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmDef ((ScmVar ("test")), (ScmLambdaSimple (["x";"y"], (ScmSet ((ScmVar ("x")), (ScmApplic ((ScmVar ("*")), [ScmVar ("x");ScmVar ("y")]))))))));
expected=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x";"y"], (ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarFree ("*"))), [ScmVar' (VarParam ("x", 0));ScmVar' (VarParam ("y", 1))]))))))))};

ExprCase {name="13-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmSeq [ScmApplic ((ScmVar ("x")), []);ScmSet ((ScmVar ("x")), (ScmApplic ((ScmVar ("x")), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])))};

ExprCase {name="14-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmApplic ((ScmVar ("f")), [ScmLambdaSimple (["y"], (ScmApplic ((ScmVar ("g")), [ScmVar ("a");ScmVar ("b")])))]))));
expected=(ScmLambdaSimple' (["x"], (ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmLambdaSimple' (["y"], (ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))]))))};

ExprCase {name="15-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x";"y";"z"], (ScmLambdaSimple (["y"], (ScmSeq [ScmSet ((ScmVar ("x")), (ScmConst (ScmNumber (ScmRational (5, 1)))));ScmApplic ((ScmVar ("+")), [ScmVar ("x");ScmVar ("y")]);ScmVar ("x")])))));
expected=(ScmLambdaSimple' (["x";"y";"z"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (5, 1)))));ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarBound ("x", 0, 0));ScmVar' (VarParam ("y", 0))]);ScmVar' (VarBound ("x", 0, 0))])))))};

ExprCase {name="16-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaOpt (["x";"y"], "z", ScmApplic ((ScmVar ("+")), [ScmVar ("a");ScmVar ("b");ScmLambdaSimple (["z"], (ScmApplic ((ScmVar ("+")), [ScmVar ("z");ScmLambdaSimple (["z"], (ScmApplic ((ScmVar ("+")), [ScmVar ("c");ScmVar ("d")])))])))])));
expected=(ScmLambdaOpt' (["x";"y"], "z", ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarParam ("z", 0));ScmLambdaSimple' (["z"], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmVar' (VarFree ("d"))])))])))])))};

ExprCase {name="17-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple ([], (ScmIf ((ScmApplic ((ScmVar ("f")), [ScmVar ("x")])), (ScmIf ((ScmApplic ((ScmVar ("g")), [ScmVar ("y")])), (ScmConst (ScmBoolean (false))), (ScmConst (ScmBoolean (false))))), (ScmConst (ScmBoolean (false)))))));
expected=(ScmLambdaSimple' ([], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("x"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("y"))])), (ScmConst' (ScmBoolean (false))), (ScmConst' (ScmBoolean (false))))), (ScmConst' (ScmBoolean (false)))))))};

ExprCase {name="18-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmDef ((ScmVar ("test")), (ScmLambdaSimple (["x"], (ScmApplic ((ScmVar ("list")), [ScmLambdaSimple ([], (ScmVar ("x")));ScmLambdaSimple (["y"], (ScmSet ((ScmVar ("x")), (ScmVar ("y")))))]))))));
expected=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x"], (ScmApplic' ((ScmVar' (VarFree ("list"))), [ScmLambdaSimple' ([], (ScmVar' (VarBound ("x", 0, 0))));ScmLambdaSimple' (["y"], (ScmSet' ((VarBound ("x", 0, 0)), (ScmVar' (VarParam ("y", 0))))))]))))))};

ExprCase {name="19-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmSeq [ScmApplic ((ScmVar ("a")), []);ScmSet ((ScmVar ("b")), (ScmApplic ((ScmVar ("c")), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("a"))), []);ScmSet' ((VarFree ("b")), (ScmApplic' ((ScmVar' (VarFree ("c"))), [])))])))};

ExprCase {name="20-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmSeq [ScmLambdaSimple (["x"], (ScmSet ((ScmVar ("x")), (ScmVar ("x")))));ScmLambdaSimple (["x"], (ScmSet ((ScmVar ("x")), (ScmVar ("x")))))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))));ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))))])))};

ExprCase {name="21-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmSeq [ScmApplic ((ScmVar ("x")), []);ScmSet ((ScmVar ("x")), (ScmApplic ((ScmVar ("x")), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])))};

ExprCase {name="22-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaOpt ([], "x", ScmIf ((ScmLambdaSimple (["x"], (ScmSet ((ScmVar ("x")), (ScmConst (ScmNumber (ScmRational (1, 1)))))))), (ScmVar ("x")), (ScmVar ("x")))));
expected=(ScmLambdaOpt' ([], "x", ScmIf' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))), (ScmVar' (VarParam ("x", 0))), (ScmVar' (VarParam ("x", 0))))))};

ExprCase {name="23-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmApplic ((ScmVar ("void")), []));
expected=(ScmApplic' ((ScmVar' (VarFree ("void"))), []))};

ExprCase {name="24-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmDef ((ScmVar ("test")), (ScmLambdaOpt (["x"], "y", ScmApplic ((ScmVar ("cons")), [ScmVar ("x");ScmLambdaSimple ([], (ScmSet ((ScmVar ("x")), (ScmVar ("y")))))])))));
expected=(ScmDef' ((VarFree ("test")), (ScmLambdaOpt' (["x"], "y", ScmApplic' ((ScmVar' (VarFree ("cons"))), [ScmVar' (VarParam ("x", 0));ScmLambdaSimple' ([], (ScmSet' ((VarBound ("x", 0, 0)), (ScmVar' (VarBound ("y", 0, 1))))))])))))};

ExprCase {name="25-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple ([], (ScmConst (ScmNumber (ScmRational (1, 1))))));
expected=(ScmLambdaSimple' ([], (ScmConst' (ScmNumber (ScmRational (1, 1))))))};

ExprCase {name="26-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmLambdaOpt (["x"], "y", ScmIf ((ScmApplic ((ScmVar ("x")), [ScmVar (">");ScmConst (ScmNumber (ScmRational (5, 1)))])), (ScmLambdaSimple (["x"], (ScmVar ("x")))), (ScmLambdaSimple (["x"], (ScmVar ("x")))))))));
expected=(ScmLambdaSimple' (["x"], (ScmLambdaOpt' (["x"], "y", ScmIf' ((ScmApplic' ((ScmVar' (VarParam ("x", 0))), [ScmVar' (VarFree (">"));ScmConst' (ScmNumber (ScmRational (5, 1)))])), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))))))))};

ExprCase {name="27-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmApplic ((ScmLambdaSimple (["y"], (ScmSeq [ScmSet ((ScmVar ("z")), (ScmApplic ((ScmVar ("w")), [])));ScmConst (ScmNumber (ScmRational (2, 1)))]))), []))));
expected=(ScmLambdaSimple' (["x"], (ScmApplic' ((ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarFree ("z")), (ScmApplic' ((ScmVar' (VarFree ("w"))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))]))), []))))};

ExprCase {name="29-lexical_addressing";
test=Semantic_Analysis.annotate_lexical_addresses;
input=(ScmLambdaSimple (["x"], (ScmLambdaSimple (["y"], (ScmSeq [ScmSet ((ScmVar ("x")), (ScmApplic ((ScmVar ("y")), [])));ScmConst (ScmNumber (ScmRational (2, 1)))])))));
expected=(ScmLambdaSimple' (["x"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmApplic' ((ScmVar' (VarParam ("y", 0))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))])))))};

Expr'Case {name="0-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmDef' ((VarFree ("f")), (ScmLambdaOpt' ([], "x", ScmVar' (VarParam ("x", 0))))));
expected=(ScmDef' ((VarFree ("f")), (ScmLambdaOpt' ([], "x", ScmVar' (VarParam ("x", 0))))))};

Expr'Case {name="1-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmSet' ((VarFree ("y")), (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmIf' ((ScmConst' (ScmNumber (ScmRational (1, 1)))), (ScmConst' (ScmNumber (ScmRational (2, 1)))), (ScmConst' (ScmVoid)));ScmSeq' [ScmConst' (ScmNumber (ScmRational (4, 1)));ScmConst' (ScmString ("hello"))]]))));
expected=(ScmSet' ((VarFree ("y")), (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmIf' ((ScmConst' (ScmNumber (ScmRational (1, 1)))), (ScmConst' (ScmNumber (ScmRational (2, 1)))), (ScmConst' (ScmVoid)));ScmSeq' [ScmConst' (ScmNumber (ScmRational (4, 1)));ScmConst' (ScmString ("hello"))]]))))};

Expr'Case {name="2-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x";"y";"z"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f?"))), [ScmVar' (VarFree ("a"))])), (ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("b"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g?"))), [ScmVar' (VarFree ("c"))])), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("d"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("e"))])]), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("h"))), [ScmVar' (VarFree ("w"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("l"))]);ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("m"))])])])))))));
expected=(ScmLambdaSimple' (["x";"y";"z"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f?"))), [ScmVar' (VarFree ("a"))])), (ScmApplicTP' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("b"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g?"))), [ScmVar' (VarFree ("c"))])), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("d"))]);ScmApplicTP' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("e"))])]), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("h"))), [ScmVar' (VarFree ("w"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("l"))]);ScmApplicTP' ((ScmVar' (VarFree ("g"))), [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("m"))])])])))))))};

Expr'Case {name="3-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmIf' ((ScmVar' (VarFree ("x"))), (ScmApplic' ((ScmVar' (VarFree ("x"))), [])), (ScmVar' (VarFree ("x")))));
expected=(ScmIf' ((ScmVar' (VarFree ("x"))), (ScmApplic' ((ScmVar' (VarFree ("x"))), [])), (ScmVar' (VarFree ("x")))))};

Expr'Case {name="4-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaOpt' ([], "x", ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))));ScmVar' (VarParam ("x", 0))]));
expected=(ScmLambdaOpt' ([], "x", ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))));ScmVar' (VarParam ("x", 0))]))};

Expr'Case {name="5-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["a";"b";"c";"d";"e"], (ScmApplic' ((ScmVar' (VarFree ("x"))), [ScmApplic' ((ScmVar' (VarFree ("y"))), [ScmVar' (VarFree ("z"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("g"));ScmVar' (VarFree ("h"))]);ScmApplic' ((ScmVar' (VarFree ("j"))), [ScmApplic' ((ScmVar' (VarFree ("k"))), [ScmApplic' ((ScmVar' (VarFree ("l"))), [ScmApplic' ((ScmVar' (VarFree ("m"))), [ScmVar' (VarFree ("n"))])])])])]))));
expected=(ScmLambdaSimple' (["a";"b";"c";"d";"e"], (ScmApplicTP' ((ScmVar' (VarFree ("x"))), [ScmApplic' ((ScmVar' (VarFree ("y"))), [ScmVar' (VarFree ("z"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("g"));ScmVar' (VarFree ("h"))]);ScmApplic' ((ScmVar' (VarFree ("j"))), [ScmApplic' ((ScmVar' (VarFree ("k"))), [ScmApplic' ((ScmVar' (VarFree ("l"))), [ScmApplic' ((ScmVar' (VarFree ("m"))), [ScmVar' (VarFree ("n"))])])])])]))))};

Expr'Case {name="6-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x";"y";"z";"w"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("even?"))), [ScmVar' (VarFree ("a"))])), (ScmApplic' ((ScmVar' (VarFree ("b"))), [ScmVar' (VarFree ("c"))])), (ScmApplic' ((ScmVar' (VarFree ("d"))), [ScmVar' (VarFree ("e"))]))))));
expected=(ScmLambdaSimple' (["x";"y";"z";"w"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("even?"))), [ScmVar' (VarFree ("a"))])), (ScmApplicTP' ((ScmVar' (VarFree ("b"))), [ScmVar' (VarFree ("c"))])), (ScmApplicTP' ((ScmVar' (VarFree ("d"))), [ScmVar' (VarFree ("e"))]))))))};

Expr'Case {name="7-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmIf' ((ScmApplic' ((ScmLambdaSimple' (["y"], (ScmVar' (VarFree ("x"))))), [])), (ScmApplic' ((ScmLambdaSimple' (["x"], (ScmSeq' [ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y"))));ScmLambdaSimple' ([], (ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))]))), [ScmConst' (ScmSymbol ("a"))])), (ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y")))))))));
expected=(ScmIf' ((ScmApplic' ((ScmLambdaSimple' (["y"], (ScmVar' (VarFree ("x"))))), [])), (ScmApplic' ((ScmLambdaSimple' (["x"], (ScmSeq' [ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y"))));ScmLambdaSimple' ([], (ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))]))), [ScmConst' (ScmSymbol ("a"))])), (ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y")))))))))};

Expr'Case {name="8-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmApplic' ((ScmLambdaSimple' (["x"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("a"))), [ScmConst' (ScmNumber (ScmRational (1, 1)))])), (ScmApplic' ((ScmVar' (VarFree ("b"))), [ScmConst' (ScmNumber (ScmRational (2, 1)))])), (ScmApplic' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarFree ("c")), (ScmConst' (ScmNumber (ScmRational (0, 1)))))))), [ScmConst' (ScmNumber (ScmRational (3, 1)))])))))), [ScmLambdaSimple' (["x"], (ScmVar' (VarFree ("d"))))]));
expected=(ScmApplic' ((ScmLambdaSimple' (["x"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("a"))), [ScmConst' (ScmNumber (ScmRational (1, 1)))])), (ScmApplicTP' ((ScmVar' (VarFree ("b"))), [ScmConst' (ScmNumber (ScmRational (2, 1)))])), (ScmApplicTP' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarFree ("c")), (ScmConst' (ScmNumber (ScmRational (0, 1)))))))), [ScmConst' (ScmNumber (ScmRational (3, 1)))])))))), [ScmLambdaSimple' (["x"], (ScmVar' (VarFree ("d"))))]))};

Expr'Case {name="9-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaOpt' (["x";"y"], "z", ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmLambdaSimple' ([], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("d"));ScmVar' (VarFree ("e"))])))])))])));
expected=(ScmLambdaOpt' (["x";"y"], "z", ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmLambdaSimple' ([], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("d"));ScmVar' (VarFree ("e"))])))])))])))};

Expr'Case {name="10-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])))};

Expr'Case {name="11-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmOr' [ScmApplic' ((ScmLambdaOpt' (["y"], "z", ScmApplic' ((ScmLambdaSimple' ([], (ScmApplic' ((ScmLambdaSimple' ([], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))), [])))), []))), [ScmVar' (VarFree ("c"));ScmConst' (ScmNumber (ScmRational (1, 1)))]);ScmLambdaSimple' ([], (ScmSet' ((VarFree ("d")), (ScmVar' (VarFree ("w"))))));ScmApplic' ((ScmVar' (VarFree ("w"))), [ScmVar' (VarFree ("w"))])])));
expected=(ScmLambdaSimple' (["x"], (ScmOr' [ScmApplic' ((ScmLambdaOpt' (["y"], "z", ScmApplicTP' ((ScmLambdaSimple' ([], (ScmApplicTP' ((ScmLambdaSimple' ([], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))), [])))), []))), [ScmVar' (VarFree ("c"));ScmConst' (ScmNumber (ScmRational (1, 1)))]);ScmLambdaSimple' ([], (ScmSet' ((VarFree ("d")), (ScmVar' (VarFree ("w"))))));ScmApplicTP' ((ScmVar' (VarFree ("w"))), [ScmVar' (VarFree ("w"))])])))};

Expr'Case {name="12-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x";"y"], (ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarFree ("*"))), [ScmVar' (VarParam ("x", 0));ScmVar' (VarParam ("y", 1))]))))))));
expected=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x";"y"], (ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarFree ("*"))), [ScmVar' (VarParam ("x", 0));ScmVar' (VarParam ("y", 1))]))))))))};

Expr'Case {name="13-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])))};

Expr'Case {name="14-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmLambdaSimple' (["y"], (ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))]))));
expected=(ScmLambdaSimple' (["x"], (ScmApplicTP' ((ScmVar' (VarFree ("f"))), [ScmLambdaSimple' (["y"], (ScmApplicTP' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))]))))};

Expr'Case {name="15-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x";"y";"z"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (5, 1)))));ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarBound ("x", 0, 0));ScmVar' (VarParam ("y", 0))]);ScmVar' (VarBound ("x", 0, 0))])))));
expected=(ScmLambdaSimple' (["x";"y";"z"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (5, 1)))));ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarBound ("x", 0, 0));ScmVar' (VarParam ("y", 0))]);ScmVar' (VarBound ("x", 0, 0))])))))};

Expr'Case {name="16-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaOpt' (["x";"y"], "z", ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarParam ("z", 0));ScmLambdaSimple' (["z"], (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmVar' (VarFree ("d"))])))])))])));
expected=(ScmLambdaOpt' (["x";"y"], "z", ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarParam ("z", 0));ScmLambdaSimple' (["z"], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmVar' (VarFree ("d"))])))])))])))};

Expr'Case {name="17-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' ([], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("x"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("y"))])), (ScmConst' (ScmBoolean (false))), (ScmConst' (ScmBoolean (false))))), (ScmConst' (ScmBoolean (false)))))));
expected=(ScmLambdaSimple' ([], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("x"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("y"))])), (ScmConst' (ScmBoolean (false))), (ScmConst' (ScmBoolean (false))))), (ScmConst' (ScmBoolean (false)))))))};

Expr'Case {name="18-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x"], (ScmApplic' ((ScmVar' (VarFree ("list"))), [ScmLambdaSimple' ([], (ScmVar' (VarBound ("x", 0, 0))));ScmLambdaSimple' (["y"], (ScmSet' ((VarBound ("x", 0, 0)), (ScmVar' (VarParam ("y", 0))))))]))))));
expected=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x"], (ScmApplicTP' ((ScmVar' (VarFree ("list"))), [ScmLambdaSimple' ([], (ScmVar' (VarBound ("x", 0, 0))));ScmLambdaSimple' (["y"], (ScmSet' ((VarBound ("x", 0, 0)), (ScmVar' (VarParam ("y", 0))))))]))))))};

Expr'Case {name="19-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("a"))), []);ScmSet' ((VarFree ("b")), (ScmApplic' ((ScmVar' (VarFree ("c"))), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("a"))), []);ScmSet' ((VarFree ("b")), (ScmApplic' ((ScmVar' (VarFree ("c"))), [])))])))};

Expr'Case {name="20-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))));ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))));ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))))])))};

Expr'Case {name="21-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])))};

Expr'Case {name="22-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaOpt' ([], "x", ScmIf' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))), (ScmVar' (VarParam ("x", 0))), (ScmVar' (VarParam ("x", 0))))));
expected=(ScmLambdaOpt' ([], "x", ScmIf' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))), (ScmVar' (VarParam ("x", 0))), (ScmVar' (VarParam ("x", 0))))))};

Expr'Case {name="23-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmApplic' ((ScmVar' (VarFree ("void"))), []));
expected=(ScmApplic' ((ScmVar' (VarFree ("void"))), []))};

Expr'Case {name="24-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmDef' ((VarFree ("test")), (ScmLambdaOpt' (["x"], "y", ScmApplic' ((ScmVar' (VarFree ("cons"))), [ScmVar' (VarParam ("x", 0));ScmLambdaSimple' ([], (ScmSet' ((VarBound ("x", 0, 0)), (ScmVar' (VarBound ("y", 0, 1))))))])))));
expected=(ScmDef' ((VarFree ("test")), (ScmLambdaOpt' (["x"], "y", ScmApplicTP' ((ScmVar' (VarFree ("cons"))), [ScmVar' (VarParam ("x", 0));ScmLambdaSimple' ([], (ScmSet' ((VarBound ("x", 0, 0)), (ScmVar' (VarBound ("y", 0, 1))))))])))))};

Expr'Case {name="25-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' ([], (ScmConst' (ScmNumber (ScmRational (1, 1))))));
expected=(ScmLambdaSimple' ([], (ScmConst' (ScmNumber (ScmRational (1, 1))))))};

Expr'Case {name="26-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmLambdaOpt' (["x"], "y", ScmIf' ((ScmApplic' ((ScmVar' (VarParam ("x", 0))), [ScmVar' (VarFree (">"));ScmConst' (ScmNumber (ScmRational (5, 1)))])), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))))))));
expected=(ScmLambdaSimple' (["x"], (ScmLambdaOpt' (["x"], "y", ScmIf' ((ScmApplic' ((ScmVar' (VarParam ("x", 0))), [ScmVar' (VarFree (">"));ScmConst' (ScmNumber (ScmRational (5, 1)))])), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))))))))};

Expr'Case {name="27-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmApplic' ((ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarFree ("z")), (ScmApplic' ((ScmVar' (VarFree ("w"))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))]))), []))));
expected=(ScmLambdaSimple' (["x"], (ScmApplicTP' ((ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarFree ("z")), (ScmApplic' ((ScmVar' (VarFree ("w"))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))]))), []))))};

Expr'Case {name="29-annotate_tail_calls";
test=Semantic_Analysis.annotate_tail_calls;
input=(ScmLambdaSimple' (["x"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmApplic' ((ScmVar' (VarParam ("y", 0))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))])))));
expected=(ScmLambdaSimple' (["x"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmApplic' ((ScmVar' (VarParam ("y", 0))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))])))))};

Expr'Case {name="0-box_set";
test=Semantic_Analysis.box_set;
input=(ScmDef' ((VarFree ("f")), (ScmLambdaOpt' ([], "x", ScmVar' (VarParam ("x", 0))))));
expected=(ScmDef' ((VarFree ("f")), (ScmLambdaOpt' ([], "x", ScmVar' (VarParam ("x", 0))))))};

Expr'Case {name="1-box_set";
test=Semantic_Analysis.box_set;
input=(ScmSet' ((VarFree ("y")), (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmIf' ((ScmConst' (ScmNumber (ScmRational (1, 1)))), (ScmConst' (ScmNumber (ScmRational (2, 1)))), (ScmConst' (ScmVoid)));ScmSeq' [ScmConst' (ScmNumber (ScmRational (4, 1)));ScmConst' (ScmString ("hello"))]]))));
expected=(ScmSet' ((VarFree ("y")), (ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmIf' ((ScmConst' (ScmNumber (ScmRational (1, 1)))), (ScmConst' (ScmNumber (ScmRational (2, 1)))), (ScmConst' (ScmVoid)));ScmSeq' [ScmConst' (ScmNumber (ScmRational (4, 1)));ScmConst' (ScmString ("hello"))]]))))};

Expr'Case {name="2-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x";"y";"z"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f?"))), [ScmVar' (VarFree ("a"))])), (ScmApplicTP' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("b"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g?"))), [ScmVar' (VarFree ("c"))])), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("d"))]);ScmApplicTP' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("e"))])]), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("h"))), [ScmVar' (VarFree ("w"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("l"))]);ScmApplicTP' ((ScmVar' (VarFree ("g"))), [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("m"))])])])))))));
expected=(ScmLambdaSimple' (["x";"y";"z"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f?"))), [ScmVar' (VarFree ("a"))])), (ScmApplicTP' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("b"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g?"))), [ScmVar' (VarFree ("c"))])), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("d"))]);ScmApplicTP' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("e"))])]), (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("h"))), [ScmVar' (VarFree ("w"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("l"))]);ScmApplicTP' ((ScmVar' (VarFree ("g"))), [ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("m"))])])])))))))};

Expr'Case {name="3-box_set";
test=Semantic_Analysis.box_set;
input=(ScmIf' ((ScmVar' (VarFree ("x"))), (ScmApplic' ((ScmVar' (VarFree ("x"))), [])), (ScmVar' (VarFree ("x")))));
expected=(ScmIf' ((ScmVar' (VarFree ("x"))), (ScmApplic' ((ScmVar' (VarFree ("x"))), [])), (ScmVar' (VarFree ("x")))))};

Expr'Case {name="4-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaOpt' ([], "x", ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))));ScmVar' (VarParam ("x", 0))]));
expected=(ScmLambdaOpt' ([], "x", ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))));ScmVar' (VarParam ("x", 0))]))};

Expr'Case {name="5-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["a";"b";"c";"d";"e"], (ScmApplicTP' ((ScmVar' (VarFree ("x"))), [ScmApplic' ((ScmVar' (VarFree ("y"))), [ScmVar' (VarFree ("z"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("g"));ScmVar' (VarFree ("h"))]);ScmApplic' ((ScmVar' (VarFree ("j"))), [ScmApplic' ((ScmVar' (VarFree ("k"))), [ScmApplic' ((ScmVar' (VarFree ("l"))), [ScmApplic' ((ScmVar' (VarFree ("m"))), [ScmVar' (VarFree ("n"))])])])])]))));
expected=(ScmLambdaSimple' (["a";"b";"c";"d";"e"], (ScmApplicTP' ((ScmVar' (VarFree ("x"))), [ScmApplic' ((ScmVar' (VarFree ("y"))), [ScmVar' (VarFree ("z"))]);ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("g"));ScmVar' (VarFree ("h"))]);ScmApplic' ((ScmVar' (VarFree ("j"))), [ScmApplic' ((ScmVar' (VarFree ("k"))), [ScmApplic' ((ScmVar' (VarFree ("l"))), [ScmApplic' ((ScmVar' (VarFree ("m"))), [ScmVar' (VarFree ("n"))])])])])]))))};

Expr'Case {name="6-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x";"y";"z";"w"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("even?"))), [ScmVar' (VarFree ("a"))])), (ScmApplicTP' ((ScmVar' (VarFree ("b"))), [ScmVar' (VarFree ("c"))])), (ScmApplicTP' ((ScmVar' (VarFree ("d"))), [ScmVar' (VarFree ("e"))]))))));
expected=(ScmLambdaSimple' (["x";"y";"z";"w"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("even?"))), [ScmVar' (VarFree ("a"))])), (ScmApplicTP' ((ScmVar' (VarFree ("b"))), [ScmVar' (VarFree ("c"))])), (ScmApplicTP' ((ScmVar' (VarFree ("d"))), [ScmVar' (VarFree ("e"))]))))))};

Expr'Case {name="7-box_set";
test=Semantic_Analysis.box_set;
input=(ScmIf' ((ScmApplic' ((ScmLambdaSimple' (["y"], (ScmVar' (VarFree ("x"))))), [])), (ScmApplic' ((ScmLambdaSimple' (["x"], (ScmSeq' [ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y"))));ScmLambdaSimple' ([], (ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))]))), [ScmConst' (ScmSymbol ("a"))])), (ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y")))))))));
expected=(ScmIf' ((ScmApplic' ((ScmLambdaSimple' (["y"], (ScmVar' (VarFree ("x"))))), [])), (ScmApplic' ((ScmLambdaSimple' (["x"], (ScmSeq' [ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y"))));ScmLambdaSimple' ([], (ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))]))), [ScmConst' (ScmSymbol ("a"))])), (ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarFree ("y")))))))))};

Expr'Case {name="8-box_set";
test=Semantic_Analysis.box_set;
input=(ScmApplic' ((ScmLambdaSimple' (["x"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("a"))), [ScmConst' (ScmNumber (ScmRational (1, 1)))])), (ScmApplicTP' ((ScmVar' (VarFree ("b"))), [ScmConst' (ScmNumber (ScmRational (2, 1)))])), (ScmApplicTP' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarFree ("c")), (ScmConst' (ScmNumber (ScmRational (0, 1)))))))), [ScmConst' (ScmNumber (ScmRational (3, 1)))])))))), [ScmLambdaSimple' (["x"], (ScmVar' (VarFree ("d"))))]));
expected=(ScmApplic' ((ScmLambdaSimple' (["x"], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("a"))), [ScmConst' (ScmNumber (ScmRational (1, 1)))])), (ScmApplicTP' ((ScmVar' (VarFree ("b"))), [ScmConst' (ScmNumber (ScmRational (2, 1)))])), (ScmApplicTP' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarFree ("c")), (ScmConst' (ScmNumber (ScmRational (0, 1)))))))), [ScmConst' (ScmNumber (ScmRational (3, 1)))])))))), [ScmLambdaSimple' (["x"], (ScmVar' (VarFree ("d"))))]))};

Expr'Case {name="9-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaOpt' (["x";"y"], "z", ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmLambdaSimple' ([], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("d"));ScmVar' (VarFree ("e"))])))])))])));
expected=(ScmLambdaOpt' (["x";"y"], "z", ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmLambdaSimple' ([], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("d"));ScmVar' (VarFree ("e"))])))])))])))};

Expr'Case {name="10-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])))};

Expr'Case {name="11-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmOr' [ScmApplic' ((ScmLambdaOpt' (["y"], "z", ScmApplicTP' ((ScmLambdaSimple' ([], (ScmApplicTP' ((ScmLambdaSimple' ([], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))), [])))), []))), [ScmVar' (VarFree ("c"));ScmConst' (ScmNumber (ScmRational (1, 1)))]);ScmLambdaSimple' ([], (ScmSet' ((VarFree ("d")), (ScmVar' (VarFree ("w"))))));ScmApplicTP' ((ScmVar' (VarFree ("w"))), [ScmVar' (VarFree ("w"))])])));
expected=(ScmLambdaSimple' (["x"], (ScmOr' [ScmApplic' ((ScmLambdaOpt' (["y"], "z", ScmApplicTP' ((ScmLambdaSimple' ([], (ScmApplicTP' ((ScmLambdaSimple' ([], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))), [])))), []))), [ScmVar' (VarFree ("c"));ScmConst' (ScmNumber (ScmRational (1, 1)))]);ScmLambdaSimple' ([], (ScmSet' ((VarFree ("d")), (ScmVar' (VarFree ("w"))))));ScmApplicTP' ((ScmVar' (VarFree ("w"))), [ScmVar' (VarFree ("w"))])])))};

Expr'Case {name="12-box_set";
test=Semantic_Analysis.box_set;
input=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x";"y"], (ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarFree ("*"))), [ScmVar' (VarParam ("x", 0));ScmVar' (VarParam ("y", 1))]))))))));
expected=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x";"y"], (ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarFree ("*"))), [ScmVar' (VarParam ("x", 0));ScmVar' (VarParam ("y", 1))]))))))))};

Expr'Case {name="13-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])))};

Expr'Case {name="14-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmApplicTP' ((ScmVar' (VarFree ("f"))), [ScmLambdaSimple' (["y"], (ScmApplicTP' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))]))));
expected=(ScmLambdaSimple' (["x"], (ScmApplicTP' ((ScmVar' (VarFree ("f"))), [ScmLambdaSimple' (["y"], (ScmApplicTP' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"))])))]))))};

Expr'Case {name="15-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x";"y";"z"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (5, 1)))));ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarBound ("x", 0, 0));ScmVar' (VarParam ("y", 0))]);ScmVar' (VarBound ("x", 0, 0))])))));
expected=(ScmLambdaSimple' (["x";"y";"z"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmConst' (ScmNumber (ScmRational (5, 1)))));ScmApplic' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarBound ("x", 0, 0));ScmVar' (VarParam ("y", 0))]);ScmVar' (VarBound ("x", 0, 0))])))))};

Expr'Case {name="16-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaOpt' (["x";"y"], "z", ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarParam ("z", 0));ScmLambdaSimple' (["z"], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmVar' (VarFree ("d"))])))])))])));
expected=(ScmLambdaOpt' (["x";"y"], "z", ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("a"));ScmVar' (VarFree ("b"));ScmLambdaSimple' (["z"], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarParam ("z", 0));ScmLambdaSimple' (["z"], (ScmApplicTP' ((ScmVar' (VarFree ("+"))), [ScmVar' (VarFree ("c"));ScmVar' (VarFree ("d"))])))])))])))};

Expr'Case {name="17-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' ([], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("x"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("y"))])), (ScmConst' (ScmBoolean (false))), (ScmConst' (ScmBoolean (false))))), (ScmConst' (ScmBoolean (false)))))));
expected=(ScmLambdaSimple' ([], (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("f"))), [ScmVar' (VarFree ("x"))])), (ScmIf' ((ScmApplic' ((ScmVar' (VarFree ("g"))), [ScmVar' (VarFree ("y"))])), (ScmConst' (ScmBoolean (false))), (ScmConst' (ScmBoolean (false))))), (ScmConst' (ScmBoolean (false)))))))};

Expr'Case {name="18-box_set";
test=Semantic_Analysis.box_set;
input=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x"], (ScmApplicTP' ((ScmVar' (VarFree ("list"))), [ScmLambdaSimple' ([], (ScmVar' (VarBound ("x", 0, 0))));ScmLambdaSimple' (["y"], (ScmSet' ((VarBound ("x", 0, 0)), (ScmVar' (VarParam ("y", 0))))))]))))));
expected=(ScmDef' ((VarFree ("test")), (ScmLambdaSimple' (["x"], (ScmApplicTP' ((ScmVar' (VarFree ("list"))), [ScmLambdaSimple' ([], (ScmVar' (VarBound ("x", 0, 0))));ScmLambdaSimple' (["y"], (ScmSet' ((VarBound ("x", 0, 0)), (ScmVar' (VarParam ("y", 0))))))]))))))};

Expr'Case {name="19-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("a"))), []);ScmSet' ((VarFree ("b")), (ScmApplic' ((ScmVar' (VarFree ("c"))), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarFree ("a"))), []);ScmSet' ((VarFree ("b")), (ScmApplic' ((ScmVar' (VarFree ("c"))), [])))])))};

Expr'Case {name="20-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))));ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))));ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmVar' (VarParam ("x", 0))))))])))};

Expr'Case {name="21-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])));
expected=(ScmLambdaSimple' (["x"], (ScmSeq' [ScmApplic' ((ScmVar' (VarParam ("x", 0))), []);ScmSet' ((VarParam ("x", 0)), (ScmApplic' ((ScmVar' (VarParam ("x", 0))), [])))])))};

Expr'Case {name="22-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaOpt' ([], "x", ScmIf' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))), (ScmVar' (VarParam ("x", 0))), (ScmVar' (VarParam ("x", 0))))));
expected=(ScmLambdaOpt' ([], "x", ScmIf' ((ScmLambdaSimple' (["x"], (ScmSet' ((VarParam ("x", 0)), (ScmConst' (ScmNumber (ScmRational (1, 1)))))))), (ScmVar' (VarParam ("x", 0))), (ScmVar' (VarParam ("x", 0))))))};

Expr'Case {name="23-box_set";
test=Semantic_Analysis.box_set;
input=(ScmApplic' ((ScmVar' (VarFree ("void"))), []));
expected=(ScmApplic' ((ScmVar' (VarFree ("void"))), []))};

Expr'Case {name="24-box_set";
test=Semantic_Analysis.box_set;
input=(ScmDef' ((VarFree ("test")), (ScmLambdaOpt' (["x"], "y", ScmApplicTP' ((ScmVar' (VarFree ("cons"))), [ScmVar' (VarParam ("x", 0));ScmLambdaSimple' ([], (ScmSet' ((VarBound ("x", 0, 0)), (ScmVar' (VarBound ("y", 0, 1))))))])))));
expected=(ScmDef' ((VarFree ("test")), (ScmLambdaOpt' (["x"], "y", ScmSeq' [ScmSet' ((VarParam ("x", 0)), (ScmBox' (VarParam ("x", 0))));ScmApplicTP' ((ScmVar' (VarFree ("cons"))), [ScmBoxGet' (VarParam ("x", 0));ScmLambdaSimple' ([], (ScmBoxSet' (VarBound ("x", 0, 0), (ScmBoxGet' (VarBound ("y", 0, 1))))))])]))))};

Expr'Case {name="25-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' ([], (ScmConst' (ScmNumber (ScmRational (1, 1))))));
expected=(ScmLambdaSimple' ([], (ScmConst' (ScmNumber (ScmRational (1, 1))))))};

Expr'Case {name="26-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmLambdaOpt' (["x"], "y", ScmIf' ((ScmApplic' ((ScmVar' (VarParam ("x", 0))), [ScmVar' (VarFree (">"));ScmConst' (ScmNumber (ScmRational (5, 1)))])), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))))))));
expected=(ScmLambdaSimple' (["x"], (ScmLambdaOpt' (["x"], "y", ScmIf' ((ScmApplic' ((ScmVar' (VarParam ("x", 0))), [ScmVar' (VarFree (">"));ScmConst' (ScmNumber (ScmRational (5, 1)))])), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))), (ScmLambdaSimple' (["x"], (ScmVar' (VarParam ("x", 0))))))))))};

Expr'Case {name="27-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmApplicTP' ((ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarFree ("z")), (ScmApplic' ((ScmVar' (VarFree ("w"))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))]))), []))));
expected=(ScmLambdaSimple' (["x"], (ScmApplicTP' ((ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarFree ("z")), (ScmApplic' ((ScmVar' (VarFree ("w"))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))]))), []))))};

Expr'Case {name="29-box_set";
test=Semantic_Analysis.box_set;
input=(ScmLambdaSimple' (["x"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmApplic' ((ScmVar' (VarParam ("y", 0))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))])))));
expected=(ScmLambdaSimple' (["x"], (ScmLambdaSimple' (["y"], (ScmSeq' [ScmSet' ((VarBound ("x", 0, 0)), (ScmApplic' ((ScmVar' (VarParam ("y", 0))), [])));ScmConst' (ScmNumber (ScmRational (2, 1)))])))))}];;

let join_scmseq expr' expr's  =
match expr' with
| ScmSeq' seq_expr's -> seq_expr's@expr's
| _ -> expr'::expr's;;

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

let var_eq v1 v2 =
match v1, v2 with
  | VarFree (name1), VarFree (name2) -> String.equal name1 name2
  | VarBound (name1, major1, minor1), VarBound (name2, major2, minor2) ->
    major1 = major2 && minor1 = minor2 && (String.equal name1 name2)
  | VarParam (name1, index1), VarParam (name2, index2) ->
       index1 = index2 && (String.equal name1 name2)
  | _ -> false

let list_eq eq l1 l2 = (List.length l1) = (List.length l2) && List.for_all2 eq l1 l2;;

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
  | _ -> false;;

let unannotate_lexical_address = function
| (VarFree name | VarParam (name, _) | VarBound (name, _, _)) -> ScmVar name

let rec unanalyze expr' =
match expr' with
  | ScmConst' s -> ScmConst(s)
  | ScmVar' var -> unannotate_lexical_address var
  | ScmBox' var -> ScmApplic(ScmVar "box", [unannotate_lexical_address var])
  | ScmBoxGet' var -> unannotate_lexical_address var
  | ScmBoxSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmIf' (test, dit, dif) -> ScmIf (unanalyze test, unanalyze dit, unanalyze dif)
  | ScmSeq' expr's -> ScmSeq (List.map unanalyze expr's)
  | ScmSet' (var, expr') -> ScmSet (unannotate_lexical_address var, unanalyze expr')
  | ScmDef' (var, expr') -> ScmDef (unannotate_lexical_address var, unanalyze expr')
  | ScmOr' expr's -> ScmOr (List.map unanalyze expr's)
  | ScmLambdaSimple' (params, expr') ->
        ScmLambdaSimple (params, unanalyze expr')
  | ScmLambdaOpt'(params, param, expr') ->
        ScmLambdaOpt (params, param, unanalyze expr')
  | (ScmApplic' (expr', expr's) | ScmApplicTP' (expr', expr's)) ->
        ScmApplic (unanalyze expr', List.map unanalyze expr's);;

let string_of_expr' expr' =
    string_of_expr (unanalyze expr');;

let case_name case =
match case with
| ExprCase c -> Printf.sprintf "Expr-%s" c.name
| Expr'Case c -> Printf.sprintf "Expr'-%s" c.name

let test_case case =

try
let actual, expected = match case with
| ExprCase c -> (c.test c.input), c.expected
| Expr'Case c -> (c.test c.input), c.expected in
if (expr'_eq actual expected) then "PASS" else "FAILURE"
with
| X_not_yet_implemented -> Printf.sprintf "Exception: Syntax not yet implemented"
| _ -> "Unknown Failure"

let test_cases cases =
let names, results =  (List.map case_name cases),(List.map test_case cases) in
List.map2 (fun name result -> Printf.sprintf "%s: %s" result name) names results;;

List.map (Printf.printf "%s\n") (test_cases cases);;


let scm_number_to_string = function
| ScmRational (num, denom) -> Printf.sprintf "ScmRational (%d, %d)" num denom
| ScmReal f -> Printf.sprintf "ScmReal %f" f;;

let rec sexpr_to_string = function
| ScmVoid -> "ScmVoid"
| ScmNil -> "ScmNil"
| ScmBoolean b -> Printf.sprintf "ScmBoolean (%b)" b
| ScmChar c -> Printf.sprintf "ScmChar ('%c')" c
| ScmString s -> Printf.sprintf "ScmString (\"%s\")" s
| ScmSymbol s -> Printf.sprintf "ScmSymbol (\"%s\")" s
| ScmNumber n -> Printf.sprintf "ScmNumber (%s)" (scm_number_to_string n)
| ScmVector sexprs -> Printf.sprintf "ScmVector [%s]" (String.concat ";" (List.map sexpr_to_string sexprs))
| ScmPair (car, cdr) -> Printf.sprintf "ScmPair ((%s), (%s)" (sexpr_to_string car) (sexpr_to_string cdr);;

let var_to_string = function
| VarFree name -> Printf.sprintf "VarFree (\"%s\")" name
| VarParam (name, index) -> Printf.sprintf "VarParam (\"%s\", %d)" name index
| VarBound (name, major, minor) -> Printf.sprintf "VarBound (\"%s\", %d, %d)" name major minor

let rec expr'_to_string = function
| ScmConst' s -> Printf.sprintf "ScmConst' (%s)" (sexpr_to_string s)
| ScmVar' var -> Printf.sprintf "ScmVar' (%s)" (var_to_string var)
| ScmBox' var -> Printf.sprintf "ScmBox' (%s)" (var_to_string var)
| ScmBoxGet' var -> Printf.sprintf "ScmBoxGet' (%s)" (var_to_string var)
| ScmBoxSet' (var, expr') -> Printf.sprintf "ScmBoxSet' (%s, (%s))" (var_to_string var) (expr'_to_string expr')
| ScmIf' (test, dit, dif) -> Printf.sprintf "ScmIf' ((%s), (%s), (%s))"
                                            (expr'_to_string test) (expr'_to_string dit)(expr'_to_string dif)
| ScmSeq' expr's -> Printf.sprintf "ScmSeq' [%s]" (String.concat ";" (List.map expr'_to_string expr's))
| ScmSet' (var, expr') -> Printf.sprintf "ScmSet' ((%s), (%s))"  (var_to_string var) (expr'_to_string expr')
| ScmDef' (var, expr') -> Printf.sprintf "ScmDef' ((%s), (%s))"  (var_to_string var) (expr'_to_string expr')
| ScmOr' expr's -> Printf.sprintf "ScmOr' [%s]" (String.concat ";" (List.map expr'_to_string expr's))
| ScmLambdaSimple' (params, expr') ->
    Printf.sprintf "ScmLambdaSimple' ([%s], (%s))" (String.concat ";" (List.map (fun s -> "\""^s^"\"") params))
                                                    (expr'_to_string expr')
| ScmLambdaOpt'(params, param, expr') ->
    Printf.sprintf "ScmLambdaOpt' ([%s], %s, %s)" (String.concat ";" (List.map (fun s -> "\""^s^"\"") params))
                                                    ("\"" ^ param ^ "\"")
                                                    (expr'_to_string expr')
| ScmApplic' (expr', expr's) ->
    Printf.sprintf "ScmApplic' ((%s), [%s])" (expr'_to_string expr')
                                            (String.concat ";" (List.map expr'_to_string expr's))
| ScmApplicTP' (expr', expr's) ->
    Printf.sprintf "ScmApplicTP' ((%s), [%s])" (expr'_to_string expr')
                                              (String.concat ";" (List.map expr'_to_string expr's))


let rec expr_to_string = function
| ScmConst s -> Printf.sprintf "ScmConst (%s)" (sexpr_to_string s)
| ScmVar s -> Printf.sprintf "ScmVar (\"%s\")" s
| ScmIf (test, dit, dif) -> Printf.sprintf "ScmIf ((%s), (%s), (%s))"
                                           (expr_to_string test) (expr_to_string dit) (expr_to_string dif)
| ScmSeq exprs -> Printf.sprintf "ScmSeq [%s]" (String.concat ";" (List.map expr_to_string exprs))
| ScmSet (var, expr) -> Printf.sprintf "ScmSet ((%s), (%s))"  (expr_to_string var) (expr_to_string expr)
| ScmDef (var, expr) -> Printf.sprintf "ScmDef ((%s), (%s))"  (expr_to_string var) (expr_to_string expr)
| ScmOr exprs -> Printf.sprintf "ScmOr [%s]" (String.concat ";" (List.map expr_to_string exprs))
| ScmLambdaSimple (params, expr) ->
    Printf.sprintf "ScmLambdaSimple ([%s], (%s))" (String.concat ";" (List.map (fun s -> "\""^s^"\"") params))
                                                  (expr_to_string expr)
| ScmLambdaOpt(params, param, expr) ->
    Printf.sprintf "ScmLambdaOpt ([%s], %s, %s)" (String.concat ";" (List.map (fun s -> "\""^s^"\"") params))
                                                 ("\"" ^ param ^ "\"")
                                                 (expr_to_string expr)
| ScmApplic (expr, exprs) ->
    Printf.sprintf "ScmApplic ((%s), [%s])" (expr_to_string expr)
                                            (String.concat ";" (List.map expr_to_string exprs))

let case_to_string case test_function_name =
match case with
| Expr'Case ({name; test; input; expected}) ->
    Printf.sprintf "Expr'Case {name=\"%s\";\ntest=%s;\ninput=(%s);\nexpected=(%s)}"
                        name test_function_name (expr'_to_string input) (expr'_to_string expected)
| ExprCase{name; test; input; expected} ->
    Printf.sprintf "ExprCase {name=\"%s\";\ntest=%s;\ninput=(%s);\nexpected=(%s)}"
                        name test_function_name (expr_to_string input) (expr'_to_string expected)


let lexical_addressing_case_str test_index sexpr =
let don'tcare_function = (fun _ -> ScmConst' (ScmString "placeholder")) in
let test_name = Printf.sprintf "%d-lexical_addressing" test_index in
let expr = Tag_Parser.tag_parse_expression sexpr in
let expected_output = Semantic_Analysis.annotate_lexical_addresses expr in
let case = ExprCase {name=test_name; test=don'tcare_function;
                     input=expr; expected=expected_output} in
case_to_string case "Semantic_Analysis.annotate_lexical_addresses"

let annotate_tail_calls_case_str test_index sexpr =
let don'tcare_function = (fun _ -> ScmConst' (ScmString "placeholder")) in
let test_name = Printf.sprintf "%d-annotate_tail_calls" test_index in
let expr = Tag_Parser.tag_parse_expression sexpr in
let expr' = Semantic_Analysis.annotate_lexical_addresses expr in
let expected_output = Semantic_Analysis.annotate_tail_calls expr' in
let case = Expr'Case {name=test_name; test=don'tcare_function;
                     input = expr'; expected = expected_output} in
case_to_string case "Semantic_Analysis.annotate_tail_calls"

let box_set_case_str test_index sexpr =
let don'tcare_function = (fun _ -> ScmConst' (ScmString "placeholder")) in
let test_name = Printf.sprintf "%d-box_set" test_index in
let expr = Tag_Parser.tag_parse_expression sexpr in
let expr' = Semantic_Analysis.annotate_lexical_addresses expr in
let expr' = Semantic_Analysis.annotate_tail_calls expr' in
let expected_output = Semantic_Analysis.box_set expr' in
let case = Expr'Case {name=test_name; test=don'tcare_function;
                     input = expr'; expected = expected_output} in
case_to_string case "Semantic_Analysis.box_set"

let sexpr_list_to_cases_str sexprs =
let lexical_addressing_cases = List.mapi lexical_addressing_case_str sexprs in
let annotate_tail_calls_cases = List.mapi annotate_tail_calls_case_str sexprs in
let box_set_cases = List.mapi box_set_case_str sexprs in
let cases_str = String.concat ";\n\n" (lexical_addressing_cases@annotate_tail_calls_cases@box_set_cases) in
Printf.sprintf "let cases = [%s];;" cases_str

let convert_test_file_to_cases in_path out_path =
let in_channel = open_in in_path in
let input = really_input_string in_channel (in_channel_length in_channel) in
let sexprs = ((PC.star Reader.nt_sexpr) input 0).found in
let cases_str = sexpr_list_to_cases_str sexprs in
let out_channel = open_out out_path in
output_string out_channel cases_str; flush out_channel;;
