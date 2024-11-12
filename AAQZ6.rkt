#lang typed/racket
(require typed/rackunit)

;; Project fully implemented. Plus added in a primitive for random for our game

(define-type ExprC (U numC stringC idC appC ifC lamC))
(define-type Value (U numV boolV closV primV stringV nullV))

(struct numV[(n : Real)] #:transparent)
(struct boolV[(bool : Boolean)] #:transparent)
(struct closV [(arg : (Listof Symbol)) (body : ExprC) (env : Environment)])
(struct primV [(arg : Symbol)])
(struct stringV [(str : String)])
(struct arrV [(start : Integer) (size : Integer)])
(struct nullV [])

(struct lamC [(args : (Listof Symbol)) (body : ExprC)] #:transparent)
(struct appC [(func : ExprC) (args : (Listof ExprC))] #:transparent)
(struct idC [(name : Symbol)] #:transparent)
(struct numC[(n : Real)] #:transparent)
(struct stringC[(str : String)] #:transparent)
(struct ifC [(test : ExprC) (then : ExprC) (else : ExprC)] #:transparent)

(define-type Environment (Listof binding))
(struct binding [(bound : Symbol) (index : Integer)] #:transparent)

(struct bindpair [(funName : (Listof Symbol)) (fun : (Listof ExprC))])

;;defining hash table for invalid identifier.
;;These symbols cannot be made into functions because we use these in our language
(define invalid-table
  (hash
   'if 0
   '=> 0
   '= 0
   'bind 0))

;;initial store
(define make-value-vector (inst make-vector Value))
(define store (make-value-vector 100 (nullV)))

(vector-set! store 0 (numV 10))
(vector-set! store 1 (boolV #t))
(vector-set! store 2 (boolV #f))
(vector-set! store 3 (primV '+))
(vector-set! store 4 (primV '-))
(vector-set! store 5 (primV '/))
(vector-set! store 6 (primV '*))
(vector-set! store 7 (primV '<=))
(vector-set! store 8 (primV 'equal?))
(vector-set! store 9 (primV 'seq))
(vector-set! store 10 (primV 'make-array))
(vector-set! store 11 (primV 'array))
(vector-set! store 12 (primV 'aref))
(vector-set! store 13 (primV 'aset!))

;; top level environment 
(define top-level-env : Environment
  (list
   (binding 'true 1)
   (binding 'false 2)
   (binding '+ 3)
   (binding '- 4)
   (binding '/ 5)
   (binding '* 6)
   (binding '<= 7)
   (binding 'equal? 8)
   (binding 'seq 9)
   (binding 'make-array 10)
   (binding 'array 11)
   (binding 'aref 12)
   (binding 'aset! 13)
   ))



;; takes in a symbol to be looked up in an environment and returns its corresponding value
(define (lookup [for : Symbol] [env : Environment] [store : (Vectorof Value)]) : Value
  (match env
    ['() (error 'lookup "user-error AAQZ4 found an unbound variable: ~a ~a" for env)]
    [(cons (binding name (? natural? location)) rest)
     (if (symbol=? for name)
         (vector-ref store location)
         (lookup for rest store))]))

;; takes in two environments and combines them into one environment
(define (extend-env [env : Environment] [news : Environment]) : Environment
  (match news
    ['() env]
    [(cons f r) (cons f (extend-env env r))]))


;; parses, then interprets a given program in the form of an Sexpr, then calls the serialize
;; function to turn it into a string
(define (top-interp [prog : Sexp]) : String
  (serialize (interp (parse prog) top-level-env store)))

;; Takes in an ExprC and an Environment and returns a Value representing the
;; interpreted program.
(define (interp [expr : ExprC] [env : Environment] [store : (Vectorof Value)]) : Value
  (match expr
    [(numC n) (numV n)]
    [(stringC str) (stringV str)]
    [(idC n) (lookup n env store)]
    [(lamC args body) (closV args body env)]
    [(appC f a)
     (define resolved-f (interp f env store))
     (match resolved-f
       [(primV _) (do-math resolved-f a env store)]
       [(closV args body nenv) (app-intrp-helper resolved-f (interp-args a env store) store)]
       [other (error "AAQZ4 needs a function that we can apply got: ~a" other)])]
    [(ifC test then else)
     (define interped-test (interp test env store))
     (if (if (boolV? interped-test) 
             (boolV-bool interped-test)
             (error "AAQZ4 needs a bool to do if ops"))
         (interp then env store)
         (interp else env store))]))


;; takes in a primV operation, arguments in the form of Listof ExprC, and an environment.
;; Matches the operation to its corresponding functionality and returns the evaluated
;; operation.
(define (do-math [op : primV] [arg : (Listof ExprC)] [env : Environment] [store : (Vectorof Value)]) : Value
  (match  (list op arg)
    [(list (primV '+) (list l r)) 
     (define interp-l (interp l env store))
     (define interp-r (interp r env store))
     (if (and (numV? interp-l) (numV? interp-r))
         (numV (+ (numV-n interp-l) (numV-n interp-r)))
         (error  "AAQZ4 need an integer with ~a operator" '+))]
    [(list (primV '-) (list l r))
     (define interp-l (interp l env store))
     (define interp-r (interp r env store))
     (if (and (numV? interp-l) (numV? interp-r))
         (numV (- (numV-n interp-l) (numV-n interp-r)))
         (error  "AAQZ4 need an integer with ~a operator" '-))]
    [(list (primV '*) (list l r))
     (define interp-l (interp l env store))
     (define interp-r (interp r env store))
     (if (and (numV? interp-l) (numV? interp-r))
         (numV (* (numV-n interp-l) (numV-n interp-r)))
         (error  "AAQZ4 need an integer with ~a operator" '*))]
    [(list (primV '/) (list l r))
     (define interp-l (interp l env store))
     (define interp-r (interp r env store))
     (if (and (numV? interp-l) (numV? interp-r))
         (if (not (= (numV-n interp-r) 0))
             (numV (/ (numV-n interp-l) (numV-n interp-r)))
             (error "AAQZ4 cant divide by zero"))
         (error  "AAQZ4 need an integer with ~a operator" '/))]
    [(list (primV '<=) (list l r))
     (define interp-l (interp l env store))
     (define interp-r (interp r env store))
     (if (and (numV? interp-l) (numV? interp-r))
         (boolV (<= (numV-n interp-l) (numV-n interp-r)))
         (error  "AAQZ4 need an integer with ~a operator" '<=))]
    [(list (primV 'equal?) (list l r))
     (define interp-l (interp l env store))
     (define interp-r (interp r env store))
     (cond
       [(and (numV? interp-l) (numV? interp-r)) (boolV (= (numV-n interp-l) (numV-n interp-r)))]
       [(and (stringV? interp-l) (stringV? interp-r))
        (boolV (string=? (stringV-str interp-l) (stringV-str interp-r)))]
       [(and (boolV? interp-l) (boolV? interp-r)) (boolV (eq? (boolV-bool interp-l) (boolV-bool interp-r)))]
       [else (boolV #f)])]
    [(list (primV 'seq) (list args ...))
     (let ([interp-args (map (lambda (expr)
                               (interp (cast expr ExprC) env store))
                             args)])
       (last interp-args))]
    [(list (primV 'make-array) (list size fill))
     (if (< size 1)
         (error "AAQZ can only make array with size bigger than or equal to 1 got: ~a" size)
         ("IGNORE"))]
    
    [other (error "wrong number of variable for primV AAQZ4: ~a" other)]))


 

(define (make-array-helper [size : numV] [start : numV] [fill : Value]) : Integer
  (match
    [(equal? size 0) start]
    [else (make-array-helper (- size 1) (start) (fill))])
  
  )

;; takes in a closure and a list of values and extends the closure's environment
;;by binding closure's syms to the list of values and evaluates the body with the new environment
(define (app-intrp-helper [closer : closV] [args : (Listof Value)] [store : (Vectorof Value)]) : Value
  (match closer
    [(closV syms body env) (interp body (extend-env env (bind syms args store)) store)]))

;; takes in a list of symbols and a list of values and creates a binding for each
;; corresponding symbol value pair. The bindings are then put into an Environment
(define (bind [l1 : (Listof Symbol)] [l2 : (Listof Value)] [store : (Vectorof Value)]) : Environment
  (match (list l1 l2)
    [(list '() '()) '()]
    [(list (cons f1 r1) (cons f2 r2)) (cons (binding f1 (update-store f2 store)) (bind r1 r2 store))]
    [other (error 'bind "Number of variables and arguments do not match AAQZ4: ~a" other)]))

;;takes in a value and a store and return the location that the value has been stored to
(define (update-store [store-val : Value] [store : (Vectorof Value)]) : Integer
  (define available (exact-round (numV-n (cast (vector-ref store 0) numV))))
  (vector-set! store available store-val)
  (vector-set! store 0 (numV (+ available 1)))
  available)

;; takes in a list of ExprC representing args, and an Environment. Interprets everything
;; in the list of ExprC into a list of Values 
(define (interp-args [args : (Listof ExprC)] [env : Environment] [store : (Vectorof Value)]) : (Listof Value)
  (match args
    ['() '()]
    [(cons other r) (cons (interp other env store) (interp-args r env store))]))

;; Takes in a type Value and turns that value into a String
(define (serialize [v : Value]) : String 
  (match v
    [(numV n) (number->string n)] 
    [(stringV str) (~v str)]
    [(boolV bool) (if bool "true" "false")]
    [(closV _ _ _) "#<procedure>"]
    [(primV _) "#<primop>"]
    [(nullV) "null"]
    [(arrV _ _) "#<array>"]))

;;takes in an S-expression and parses it into our AAQZ4 language in the form of an ExprC.
;;Checks for invalid syntaxes and invalid identifiers.
(define (parse [prog : Sexp]) : ExprC 
  (match prog
    [(list 'bind clauses ... expr)
     (define pClause (parse-binds (cast clauses (Listof Sexp))))
     (appC (lamC (check-duplicate-arg (bindpair-funName pClause)) (parse expr)) (bindpair-fun pClause))]
    [(list (list args ...) '=> body)
     (cond
       [(not (andmap symbol? args)) (error 'parse "AAQZ Expected a list of symbols for arguments got ~a" args)]
       [else (lamC (check-duplicate-arg args) (parse body))])]
    [(? real? n) (numC n)]
    [(? string? str) (stringC str)]
    [(list 'if test then else) (ifC (parse test) (parse then) (parse else))]
    [(list s args ...) (appC (parse s) (map parse args))]
    [(? symbol? s)
     (if (hash-has-key? invalid-table s)
         (error 'parse "Invalid identifier: ~a in AAQZ4" prog)
         (idC s))]))

;; takes clauses needed to be bound and creates a bindpair containing the list of symbols
;; and their corresponding parsed expressions
(define (parse-binds [clauses : Sexp]) : bindpair
  (match clauses
    ['() (bindpair '() '())]
    [(cons (list (? symbol? id) '= expr) r)
     (if (hash-has-key? invalid-table id)
         (error 'parse-binds "Invalid identifier: ~a in AAQZ4" id)
         (let* ([parsed-rest (parse-binds r)]
                [ids (cons id (bindpair-funName parsed-rest))]
                [exprs (cons (parse expr) (bindpair-fun parsed-rest))])
           (bindpair ids exprs)))]))

;;takes in a list of symbols representing arguments and checks if there are any duplicate names for
;;arguments in the given list using check-duplicate-arg-helper. Returns the list of arguments.
(define (check-duplicate-arg [args : (Listof Symbol)]) : (Listof Symbol)
  (match args
    ['() '()]
    [(cons first rest) (cons (check-duplicate-arg-helper first rest) (check-duplicate-arg rest))]))

;;Takes in an symbol called 'new' and a list of symbols and checks whether 'new' is in the list of symbols. Throws
;;an error if new is found in the list of symbols.
(define (check-duplicate-arg-helper [new : Symbol] [existing : (Listof Symbol)]) : Symbol
  (match existing
    ['() new]
    [(cons arg rest)
     (if (equal? new arg)
         (error "AAQZ4 found a syntax error repeated argument name\n")
         (check-duplicate-arg-helper new rest))]))
 
;;test
(check-equal? (parse
               '{bind [x = 5]
                      [y = 7]
                      {+ x y}})
              (appC (lamC '(x y)
                          (appC (idC '+)
                                (list (idC 'x)
                                      (idC 'y))))
                    (list (numC 5) (numC 7))))

(check-equal? (parse
               '{bind [x = 5]
                      [y = 7]
                      {+ x y}})
              (appC (lamC '(x y)
                          (appC (idC '+)
                                (list (idC 'x)
                                      (idC 'y))))
                    (list (numC 5) (numC 7))))

(check-equal? (parse
               '{{(add1) => {add1 42}}
                {(x) => {+ x 1}}})
              (appC (lamC '(add1) (appC (idC 'add1)
                                        (list (numC 42))))
                    (list (lamC '(x) (appC (idC '+)
                                           (list (idC 'x)
                                                 (numC 1)))))))
(check-equal? (parse
               '{{(x y) => {+ x y}}
                5 7}) (appC (lamC '(x y)
                                  (appC (idC '+)
                                        (list (idC 'x)
                                              (idC 'y))))
                            (list (numC 5) (numC 7)))) 

(check-equal? (top-interp
               '{if false 3 23}) "23")

(check-equal? (top-interp
               '{{(add1) => {add1 42}}
                {(x) => {+ x 1}}}) "43")

(check-equal? (top-interp
               '{{(min1) => {min1 42}}
                {(x) => {- x 1}}}) "41")

(check-equal? (top-interp
               '{{(mult2) => {mult2 42}}
                {(x) => {* x 2}}}) "84")

(check-equal? (top-interp
               '{{(div3) => {div3 9}}
                {(x) => {/ x 3}}}) "3")

(check-equal? (top-interp
               '{{(bigger-than-2) => {bigger-than-2 4}}
                {(x) => {<= 2 x}}}) "true")

(check-equal? (top-interp
               '{{(bigger-than-2) => {bigger-than-2 4}}
                {(x) => {<= 2 x}}}) "true")

(check-equal? (top-interp
               '{{(same-as-2) => {same-as-2 2}}
                {(x) => {equal? 2 x}}}) "true")

(check-equal? (top-interp
               '{{(same-as-2) => {same-as-2 3}}
                {(x) => {equal? 2 x}}}) "false")

(check-equal? (top-interp
               '{{(same-as-str-2) => {same-as-str-2 "2"}}
                {(x) => {equal? "2" x}}}) "true")

(check-equal? (top-interp
               '{{(same-as-str-2) => {same-as-str-2 "3"}}
                {(x) => {equal? "2" x}}}) "false")

(check-equal? (top-interp
               '{{(same-bool) => {same-bool false}}
                {(x) => {equal? false x}}}) "true")

(check-equal? (top-interp
               '{{(same-bool) => {same-bool false}}
                {(x) => {equal? true x}}}) "false")


(check-equal? (top-interp
               '{{(noArg) => {noArg}}
                {() => 3}}) "3")

(check-equal? (top-interp
               '43) "43")

(check-equal? (top-interp
               '"dogs") "\"dogs\"")

(check-equal? (top-interp
               'true) "true")
(check-equal? (top-interp
               'false) "false")

(check-equal? (top-interp
               '{(x) => {* x 2}}) "#<procedure>")

(check-equal? (top-interp
               '*) "#<primop>")


(check-equal? (top-interp '(+ 2 3)) "5")
(check-equal? (top-interp '{if true 34 39}) "34")
(check-equal? (top-interp '{{(x y) => {+ x y}} 4 3}) "7")

(check-exn #rx"AAQZ4 found a syntax error repeated argument name\n"
           (lambda ()
             (top-interp
               '{{(add1) => {add1 42}}
                {(x x) => {+ x 1}}})))

(check-equal?
 (top-interp
  '{bind [x = 5]
         [y = 7]
         {+ x y}}) "12")
(check-equal?
 (top-interp
  '{bind  12}) "12")

(top-interp '{ bind 
      [one = { (f) => ((v) => (f v)) }]
      [two = { (f) => ((v) => (f (f v))) }]
      [add = { (m) =>
                    ((n) =>
                         ((f) =>
                              ((x) =>
                                   ((m f) ((n f) x))))) }]
      {bind
       [three = {(add one) two}]
       [why = 3]
       {(three ((x) => (* x 2))) why}}})

(check-exn #rx"Number of variables and arguments do not match AAQZ4"
           (lambda ()
             (top-interp
               '{{(div3) => {div3 9 5}}
                {(x) => {/ x 3}}})))
 
(check-exn #rx"AAQZ4 need an integer"
           (lambda ()
             (top-interp
               '{{(prim) => {prim "42"}}
                {(x) => {+ x 1}}})))

(check-exn #rx"AAQZ4 needs a bool to do if ops"
           (lambda ()
             (top-interp
               '{if "true" 42 43})))

(check-exn #rx"AAQZ4 need an integer"
           (lambda ()
             (top-interp
               '{{(prim) => {prim "42"}}
                {(x) => {* x 1}}})))

(check-exn #rx"AAQZ4 need an integer"
           (lambda ()
             (top-interp
               '{{(prim) => {prim "42"}}
                {(x) => {- x 1}}})))

(check-exn #rx"AAQZ4 need an integer"
           (lambda ()
             (top-interp
               '{{(prim) => {prim "42"}}
                {(x) => {/ x 1}}})))

(check-exn #rx"AAQZ4 cant divide by zero"
           (lambda ()
             (top-interp
               '{{(prim) => {prim 42}}
                {(x) => {/ x 0}}}))) 

(check-exn #rx"lookup: user-error AAQZ4 found an unbound variable"
           (lambda ()
             (top-interp
               '{{(prim) => {prim 2}}
                {(x) => {/ x y}}})))

(check-exn #rx"AAQZ4 need an integer"
           (lambda ()
             (top-interp
               '{{(prim) => {prim "2"}}
                {(x) => {<= x 3}}})))

(check-exn #rx"wrong number of variable for primV AAQZ4"
           (lambda ()
             (top-interp
               '{{(prim) => {prim 42}}
                {(x) => {+ x 1 4}}})))

(check-equal?
             (top-interp
               '{{(same-bool) => {same-bool "false"}}
                {(x) => {equal? true x}}}) "false") 

(check-exn #rx"AAQZ Expected a list of symbols for arguments"
           (lambda ()
             (top-interp
               '{{(same-bool) => {same-bool false}}
                {(4) => {equal? true x}}})))


(check-exn #rx"parse: Invalid identifier"
           (lambda ()
             (top-interp
               'if)))

(check-exn #rx"AAQZ4 needs a function that we can apply got"
           (lambda ()
             (top-interp
              '(3 4 5))))

 


(check-exn #rx"Number of variables and arguments do not match AAQZ4"
           (lambda ()
             (top-interp '((() => 9) 17))))






 




