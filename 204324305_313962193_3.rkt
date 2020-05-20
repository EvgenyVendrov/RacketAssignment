  #lang pl

  #| BNF for the MUMUWAE  language:
       <MUMUWAE > ::= <num>
               | { + <MUWAE> <MUWAE> }
               | { - <MUWAE> <MUWAE> }
               | { * <MUWAE> <MUWAE> }
               | { / <MUWAE> <MUWAE> }
               | { with { <id> <MUWAE> } <MUWAE> }
               | { sqrt <MUWAE> }
               | <id>
  |#

  ;; MUMUWAE  abstract syntax trees
  (define-type MUWAE 
    [Num  Number]
    [Add  MUWAE MUWAE]
    [Sub  MUWAE MUWAE]
    [Mul  MUWAE MUWAE]
    [Div  MUWAE MUWAE]
    [Sqrt MUWAE]
    [Id   Symbol]
    [With Symbol MUWAE MUWAE])

  (: parse-sexpr : Sexpr -> MUWAE)
  ;; to convert s-expressions into MUMUWAEs
  (define (parse-sexpr sexpr)
    (match sexpr
      [(number: n)    (Num n)]
      [(symbol: name) (Id name)]
      [(cons 'with more)
       (match sexpr
         [(list 'with (list (symbol: name) named) body)
          (With name (parse-sexpr named) (parse-sexpr body))]
         [else (error 'parse-sexpr "bad `with' syntax in ~s" sexpr)])]
      [(list '+ lhs rhs) (Add (parse-sexpr lhs) (parse-sexpr rhs))]
      [(list '- lhs rhs) (Sub (parse-sexpr lhs) (parse-sexpr rhs))]
      [(list '* lhs rhs) (Mul (parse-sexpr lhs) (parse-sexpr rhs))]
      [(list '/ lhs rhs) (Div (parse-sexpr lhs) (parse-sexpr rhs))]
      [(list 'sqrt val) (Sqrt (parse-sexpr val))]
      [else (error 'parse-sexpr "bad syntax in ~s" sexpr)]))

  (: parse : String -> MUWAE)
  ;; parses a string containing a MUWAE expression to a MUWAE AST
  (define (parse str)
    (parse-sexpr (string->sexpr str)))

  #| Formal specs for `subst':
     (`N' is a <num>, `E1', `E2' are <MUWAE>s, `x' is some <id>, `y' is a
     *different* <id>)
        N[v/x]                = N
        {+ E1 E2}[v/x]        = {+ E1[v/x] E2[v/x]}
        {- E1 E2}[v/x]        = {- E1[v/x] E2[v/x]}
        {* E1 E2}[v/x]        = {* E1[v/x] E2[v/x]}
        {/ E1 E2}[v/x]        = {/ E1[v/x] E2[v/x]}
        {sqrt E1}[v/x]        = {sqrt E1[v/x]}
        y[v/x]                = y
        x[v/x]                = v
        {with {y E1} E2}[v/x] = {with {y E1[v/x]} E2[v/x]}
        {with {x E1} E2}[v/x] = {with {x E1[v/x]} E2}
  |#

  (: subst : MUWAE Symbol MUWAE -> MUWAE)
  ;; substitutes the second argument with the third argument in the
  ;; first argument, as per the rules of substitution; the resulting
  ;; expression contains no free instances of the second argument
  (define (subst expr from to)
    (cases expr
      [(Num n) expr]
      [(Add l r) (Add (subst l from to) (subst r from to))]
      [(Sub l r) (Sub (subst l from to) (subst r from to))]
      [(Mul l r) (Mul (subst l from to) (subst r from to))]
      [(Div l r) (Div (subst l from to) (subst r from to))]
      [(Sqrt v)  (Sqrt(subst v from to))]
      [(Id name) (if (eq? name from) to expr)]
      [(With bound-id named-expr bound-body)
       (With bound-id
             (subst named-expr from to)
             (if (eq? bound-id from)
               bound-body
               (subst bound-body from to)))]))

  #| Formal specs for `eval':
       eval(N)         = N
       eval({+ E1 E2}) = eval(E1) + eval(E2)
       eval({- E1 E2}) = eval(E1) - eval(E2)
       eval({* E1 E2}) = eval(E1) * eval(E2)
       eval({/ E1 E2}) = eval(E1) / eval(E2)
       eval({sqrt E1}) = (sqrt eval(E1))
       eval(sqrt 0)    = error!  
       eval(id)        = error!
       eval({with {x E1} E2}) = eval(E2[eval(E1)/x])
  |#

  (: eval : MUWAE -> (Listof Number))
  ;; evaluates MUWAE expressions by reducing them to numbers
  (define (eval expr)
    (cases expr
      [(Num n) (list n)]
      [(Add l r) (list(+ (first(eval l)) (first(eval r))))]
      [(Sub l r) (list(- (first(eval l)) (first(eval r))))]
      [(Mul l r) (list(* (first(eval l)) (first(eval r))))]
      [(Div l r) (list(/ (first(eval l)) (first(eval r))))]
      [(Sqrt e) (sqrt+ (eval e))] 
      [(With bound-id named-expr bound-body)
       (list(first(eval (subst bound-body
                    bound-id
                    (Num (first(eval named-expr)))))))]
      [(Id name) (error 'eval "free identifier: ~s" name)]))

(: sqrt+ : (Listof Number) -> (Listof Number))
;; a version of `sqrt' that takes a list of numbers, and returna list
;; with twice the elements, holding the two roots of each of the inputs; 
;; throws an error if any input is negative. 
(define (sqrt+ ns)
 (cond [(null? ns) ns]
 [(< (first ns) 0) (error 'eval "`sqrt' requires a nonnegative input")]
 [else (cons (sqrt(first ns))(cons (- 0 (sqrt (first ns))) (sqrt+(rest ns))))])) 

(: run : String ->  (Listof Number))
  ;; evaluate a MUWAE program contained in a string
  (define (run str)
    (eval (parse str)))

  ;; tests
  (test (run "5") => '(5))
  (test (run "{+ 5 5}") => '(10))
  (test (run "{with {x {+ 5 5}} {+ x x}}") => '(20))
  (test (run "{with {x 5} {+ x x}}") => '(10))
  (test (run "{with {x {+ 5 5}} {with {y {- x 3}} {+ y y}}}") => '(14))
  (test (run "{with {x 5} {with {y {- x 3}} {+ y y}}}") => '(4))
  (test (run "{with {x 5} {+ x {with {x 3} 10}}}") => '(15))
  (test (run "{with {x 5} {+ x {with {x 3} x}}}") => '(8))
  (test (run "{with {x 5} {+ x {with {y 3} x}}}") => '(10))
  (test (run "{with {x 5} {with {y x} y}}") => '(5))
  (test (run "{with {x 5} {with {x x} x}}") => '(5))
  (test (run "{with {x 1} y}") =error> "free identifier")
(test (run "{sqrt 9}") => '(3 -3))
  (test (run "{sqrt 1}") => '(1 -1))
  (test (run "{sqrt 0}") => '(0 0))  
  (test (run "{sqrt -1}") =error> "`sqrt' requires a nonnegative input")