#lang typed/racket
(require typed/rackunit)

;; Project fully implemented. 

(define-type ExprC (U numC stringC idC appC ifC lamC bindC))
(define-type Value (U numV boolV closV primV stringV arrV nullV))

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
(struct bindC [(sym : Symbol) (new : ExprC)])

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
   'bind 0
   ':= 0))

;;initial store

(define make-value-vector (inst make-vector Value))

(define (initial-store [size : Natural]) : (Vectorof Value)
  (define store (make-value-vector (+ 17 size) (nullV)))
  (vector-set! store (ann 0 Natural) (numV 17))
  (vector-set! store (ann 1 Natural) (boolV #t))
  (vector-set! store (ann 2 Natural) (boolV #f))
  (vector-set! store (ann 3 Natural) (primV '+))
  (vector-set! store (ann 4 Natural) (primV '-))
  (vector-set! store (ann 5 Natural) (primV '/))
  (vector-set! store (ann 6 Natural) (primV '*))
  (vector-set! store (ann 7 Natural) (primV '<=))
  (vector-set! store (ann 8 Natural) (primV 'equal?))
  (vector-set! store (ann 9 Natural) (primV 'seq))
  (vector-set! store (ann 10 Natural) (primV 'make-array))
  (vector-set! store (ann 11 Natural) (primV 'array))
  (vector-set! store (ann 12 Natural) (primV 'aref))
  (vector-set! store (ann 13 Natural) (primV 'aset!))
  (vector-set! store (ann 14 Natural) (primV 'substring))
  (vector-set! store (ann 15 Natural) (primV 'error))
  (vector-set! store (ann 16 Natural) (nullV))
  store)

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
   (binding 'substring 14)
   (binding 'error 15)
   (binding 'null 16)
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
(define (top-interp [prog : Sexp] [memsize : Natural]) : String
  (serialize (interp (parse prog) top-level-env (initial-store memsize))))

;; Takes in an ExprC and an Environment and returns a Value representing the
;; interpreted program.
(define (interp [expr : ExprC] [env : Environment] [store : (Vectorof Value)]) : Value
  (match expr
    [(numC n) (numV n)]
    [(stringC str) (stringV str)]
    [(idC n) (lookup n env store)]
    [(lamC args body) (closV args body env)]
    [(bindC sym new) (rebind sym new env store)]
    [(appC f a)
     (define resolved-f (interp f env store))
     (match resolved-f
       [(primV _) (do-math resolved-f a env store)]
       [(closV args body nenv) (app-intrp-helper resolved-f (interp-args a env store) store)]
       [other (error "AAQZ4 needs a function that we can apply got: ~a" other)])]
    [(ifC test then else)
     (define interped-test (interp test env store))
     (printf "Evaluated test result (before bool check): ~a\n" interped-test)
     (if (if (boolV? interped-test) 
             (boolV-bool interped-test)
             (error "AAQZ4 needs a bool to do if ops"))
         (begin
           (printf "Evaluating then branch: ~a\n" then)
           (interp then env store))
         (begin
           (printf "Evaluating else branch: ~a\n" else)
           (interp else env store)))]))

(define (rebind [s : Symbol] [new : ExprC] [env : Environment] [store : (Vectorof Value)]) : nullV
  (match env
    ['() (error "AAQZ trying to rebind an unbound variable ~a" s)]
    [(cons (binding sym location) r)
     (if (equal? sym s)
         (begin
           (vector-set! store location (interp new env store))
           (nullV))
         (rebind s new r store))]))

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
     (printf "Evaluated l result: ~a\n" interp-l)
     (printf "Evaluated r result: ~a\n" interp-r)
     (if (and (numV? interp-l) (numV? interp-r))
         (begin
           (printf "Boolean result of (<= l r): ~a\n" (<= (numV-n interp-l) (numV-n interp-r)))
           (boolV (<= (numV-n interp-l) (numV-n interp-r))))
         (error  "AAQZ4 need an integer with ~a operator" '<=))]
    [(list (primV 'equal?) (list l r))
     (define interp-l (interp l env store))
     (define interp-r (interp r env store))
     (cond
       [(and (numV? interp-l) (numV? interp-r)) (boolV (= (numV-n interp-l) (numV-n interp-r)))]
       [(and (stringV? interp-l) (stringV? interp-r))
        (boolV (string=? (stringV-str interp-l) (stringV-str interp-r)))]
       [(and (boolV? interp-l) (boolV? interp-r)) (boolV (eq? (boolV-bool interp-l) (boolV-bool interp-r)))]
       [(and (arrV? interp-l) (arrV? interp-r))
        (boolV (= (arrV-start interp-l) (arrV-start interp-r)))]
       [else (boolV #f)])]
    [(list (primV 'seq) (list args ...))
     (last (interp-expr-list args env store))
     ]
    [(list (primV 'make-array) (list size fill))
     (define s (interp size env store))
     (define fv (interp fill env store))
     (if (numV? s) 
         (if (natural? (numV-n s))
             (arrV (make-array-helper (numV-n s) fv store) (cast (numV-n s) Integer))
             (error "AAQZ can only make array with size bigger than or equal to 1 got: ~a" size))
         (error "AAQZ needs a number for size to make array but got ~a" size))]
    [(list (primV 'array) (list args ...))
     (if (empty? args)
         (error "AAQZ cant make an empty array :T")
         (arrV (array-helper (interp-expr-list args env store) store) (length args)))]
    [(list (primV 'aref) (list arr index))
     (define got-arr (interp arr env store))
     (define interp-in (interp index env store))
     (if (and (arrV? got-arr) (numV? interp-in))
         (if (and (> (arrV-size got-arr) (numV-n interp-in)) (> (numV-n interp-in) -1))
             (vector-ref store (+ (arrV-start got-arr) (cast (numV-n interp-in) Integer)))
             (error "AAQZ index out of range :P size is ~a index ~a" (arrV-size got-arr) (numV-n interp-in)))
         (error "AAQZ expects an array and integer as input but got ~a and ~a" arr index))]
    [(list (primV 'aset!) (list arr index value))
           (define got-arr (interp arr env store))
           (define interp-in (interp index env store))
           (if (and (arrV? got-arr) (numV? interp-in))
               (if (and (> (arrV-size got-arr) (numV-n interp-in)) (>  (numV-n interp-in) -1))
                   (if (exact-integer? (numV-n interp-in))
                    (begin (vector-set! store (exact-round (+ (arrV-start got-arr) (numV-n interp-in)))
                                       (interp value env store))
                          (nullV))
                    (error "AAQZ needs an integer to set array"))
                   (error "AAQZ index out of range :P"))
               (error "AAQZ expects an array and integer as input but got ~a and ~a" arr index))]
    [(list (primV 'substring) (list str start end))
     (define s (interp str env store))
     (define in-start (interp start env store))
     (define in-end (interp end env store))
     (match* (s in-start in-end)
       [((stringV str) (numV (? exact-integer? start)) (numV (? exact-integer? end)))
        (stringV (substring str start end))]
       [(_ _ _) (error "AAQZ expects input str int int for substring but got ~a  ~a ~a" str start end)])]
    [(list (primV 'error) (list v))
     (error "user error " (serialize (interp v env store)))]
    [other (error "wrong number of variable for primV AAQZ4: ~a" other)]))

(define (make-array-helper [size : Integer] [fill : Value] [store : (Vectorof Value)]) : Integer
  (if (equal? size 0)
      0
      (begin
        (make-array-helper (- size 1) fill store)
        (- (update-store fill store) (- size 1)))))

(define (interp-expr-list [exprs : (Listof ExprC)] [env : Environment] [store : (Vectorof Value)]) : (Listof Value)
  (match exprs
    ['() '()]
    [(cons first rest)
     (cons (interp first env store) (interp-expr-list rest env store))]))

(define (array-helper [content : (Listof Value)] [store : (Vectorof Value)]) : Integer
  (match content
    ['() 0]
    [(cons c r)
     (begin
       (define ret (update-store c store))
       (array-helper r store)
       ret)]))

;; takes in a closure and a list of values and extends the closure's environment
;;by binding closure's syms to the list of values and evaluates the body with the new environment
(define (app-intrp-helper [closer : closV] [args : (Listof Value)] [store : (Vectorof Value)]) : Value
  (match closer
    [(closV syms body env) (interp body (extend-env env (bind syms args store)) store)]))

;; takes in a list of symbols and a list of values and creates a binding for each
;; corresponding symbol value pair. The bindings are then put into an Environment
(define (bind [l1 : (Listof Symbol)] [l2 : (Listof Value)] [store : (Vectorof Value)]) : Environment
  (printf "bind called with l1: ~a, l2: ~a\n" l1 l2)
  (match (list l1 l2)
    [(list '() '()) '()]
    [(list (cons f1 r1) (cons f2 r2)) (cons (binding f1 (update-store f2 store)) (bind r1 r2 store))]
    [other (error 'bind "Number of variables and arguments do not match AAQZ4: ~a" other)]))

;;takes in a value and a store and return the location that the value has been stored to
(define (update-store [store-val : Value] [store : (Vectorof Value)]) : Integer
  (define available (exact-round (numV-n (cast (vector-ref store 0) numV))))
  (if (>= available (vector-length store))
      (error 'update-store "AAQZ memory exceeded :o")
      (begin
        (vector-set! store available store-val)
        (vector-set! store (ann 0 Natural) (numV (+ available 1)))
        available)))

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
    [(list (? symbol? s) ':= new)
     (bindC s (parse new))]
    [(? real? n) (numC n)]
    [(? string? str) (stringC str)]
    [(list 'if test then else) (ifC (parse test) (parse then) (parse else))]
    [(list s args ...) (appC (parse s) (map parse args))]
    [(? symbol? s)
     (if (hash-has-key? invalid-table s)
         (error 'parse "Invalid identifier: ~a in AAQZ4" prog)
         (idC s))]
    ['() (error "AAQZ cant parse nothin >:")]
    ))

;; takes clauses needed to be bound and creates a bindpair containing the list of symbols
;; and their corresponding parsed expressions
(define (parse-binds [clauses : Sexp]) : bindpair
  (match clauses
    ['() (bindpair '() '())]
    [(cons (list (? symbol? id) '= expr) r)
     (if (hash-has-key? invalid-table id)
         (error 'parse-binds "Invalid identifier in AAQZ4 ~a " id)
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


(define while
  '{bind [while = "bogus"]
                   {seq {while := {(cond body) =>
                                                    {if cond
                                                        {seq body {while cond body}}
                                                        nullV}}}
                        while}})

#;(top-interp (while) 100)


(define in-order
  '{bind [inorder ="bogus"]
         [index = 0]
         [increasing = true]
         {seq {inorder := {(array size) =>
                                        {seq
                                         {while
                                          (<= (+ index 2) size)
                                          (if (<= (aref array (+ 1 index)) (aref array index))
                                              (increasing := false)
                                              (seq
                                               {index := {+ 1 index}}
                                               (inorder array size)))
                                          }
                                         increasing}}}
              {inorder {array 10 20 30} 3 }}})
 
#;(if (<= size (+ index 1))
      true
      (if (<= (aref array (+ 1 index)) (aref array index))
          false
          (seq
           {index := {+ 1 index}}
           (inorder array size))))

(top-interp `{bind [while = ,while]
                   {bind  [in-order = ,in-order]
                          {in-order {array 10 20 30} 3}}} 100)

(top-interp '{bind [fact = "bogus"]
      {seq {fact := {(x) => {if {equal? x 0}
                                1
                                {* x {fact {- x 1}}}}}}
           {fact 12}}} 100)

(parse '(bind (x = 3) 3 4))


