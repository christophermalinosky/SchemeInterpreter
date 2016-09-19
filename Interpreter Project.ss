;Christopher Malinosky and Jacob Patterson

;:  Single-file version of the interpreter.
;; Easier to submit to server, probably harder to use in the development process

(load "chez-init.ss") 

;-------------------+
;                   |
;    DATATYPES      |
;                   |
;-------------------+

; parsed expression

(define-datatype expression expression?
  [var-exp
    (id symbol?)]
  
  [lit-exp
    (id literal?)]
  
  [lambda-exp
    (bound pair-or-null?)
    (body list-of-exp-improp?)]
  
  [lambda-improper-exp
    (bound pair-or-null?)
    (body list-of-exp-improp?)]
    
  [lambda-variable-exp
    (bound symbol?)
    (body list-of-exp-improp?)]
  
  [let-exp
    (bound list?)
    (body list-of-expression?)]
  
  [let*-exp
    (bound list?)
    (body list-of-expression?)]
  
  [letrec-exp
    (proc-names (list-of symbol?))
	(idss (list-of letrec-id-exp-check?))
	(bodiess (list-of (list-of expression?)))
	(letrec-body list-of-expression?)]
  
  [named-let-exp
    (proc-name symbol?)
	(ids (list-of symbol?))
	(bodies (list-of expression?))
	(named-let-body list-of-expression?)]
  
  [if-noelse-exp
    (test expression?)
    (body expression?)]
  
  [if-else-exp
    (test expression?)
    (body1 expression?)
    (body2 expression?)]
  
  [set!-exp
    (id symbol?)
    (body expression?)]
  
  [app-exp
    (rator expression?)
    (rand list-of-exp-or-null?)]
  
  [while-exp
    (test-exp expression?)
    (body (list-of expression?))]
  
  [begin-exp
    (body list-of-expression?)]
  
  [cond-exp
    (test-cases (list-of expression?))
    (bodies (list-of (list-of expression?)))]
  
  [and-exp
    (body list-of-exp-or-null?)]
  
  [or-exp
    (body list-of-exp-or-null?)]
  
  [case-exp
    (key expression?)
    (test-cases list-of-list-of-exp-or-exp?)
    (bodies (list-of (list-of expression?)))]
	
  [define-exp
	(id symbol?)
	(body expression?)])

(define list-of-list-of-exp-or-exp?
  (lambda (x)
    (if (null? x)
        #t
        (if (or (expression? (car x)) ((list-of expression?) (car x)))
            (list-of-list-of-exp-or-exp? (cdr x))
            #f))))
			
(define letrec-id-exp-check?
	(lambda (x)
		(or (symbol? x) (improper-symbol? x) (andmap symbol? x))))

(define improper-symbol?
	(lambda (x)
		(if (improper? x)
			(andmap-imp symbol? x)
			#f)))
;Determines if an object is a literal
(define literal?
  (lambda (x)
    (or
      (number? x)
      (boolean? x)
      (string? x)
      (symbol? x)
      (vector? x)
      (quoted? x))))

;Detemines if a list is quoted
(define quoted?
  (lambda (x)
    (eq? (car x) 'quote)))

;Determines if an object is an expression or list of expressions
(define list-of-expression?
  (lambda (x)
    (or
      (expression? x)
      (andmap expression? x))))

;Determines if an object is an expression or list/improper list of expressions
(define list-of-exp-improp?
  (lambda (x)
    (or
      (expression? x)
      (if (improper? x)
          (andmap-imp expression? x)
          (andmap expression? x)))))
          
;Determines if an object is a list of expressions or null
(define list-of-exp-or-null?
  (lambda (x)
    (or (list-of-expression? x)
        (null? x))))

;Determines is a list is a pair or null
(define pair-or-null?
  (lambda (x)
    (or (pair? x) (null? x))))




	
	

;; environment type definitions

(define scheme-value?
  (lambda (x) #t))

(define-datatype environment environment?
  (empty-env-record)
  (extended-env-record
   (syms (list-of symbol?))
   (vals (list-of scheme-value?))
   (env cell-or-env?))
  (recursively-extended-env-record
	(proc-names (list-of symbol?))
	(idss (list-of letrec-id-exp-check?))
	(bodiess (list-of (list-of expression?)))
	(env cell-or-env?))
)

; datatype for procedures.  At first there is only one
; kind of procedure, but more kinds will be added later.

(define-datatype proc-val proc-val?
  [prim-proc
   (name symbol?)]
  [closure
    (vars list?)
    (bodies list-of-expression?)
    (env cell-or-env?)]
  [variable-closure
    (var literal?)
    (bodies list-of-expression?)
    (env cell-or-env?)]
  [improper-closure
    (vars improper-list-of-literal?)
    (bodies list-of-expression?)
    (env cell-or-env?)])

(define cell-or-env?
	(lambda (x)
		(or (environment? x) (cell? x))))
	
(define improper-list-of-literal?
  (lambda (x)
    (if (literal? x)
        #t
        (and (literal? (car x))
             (improper-list-of-literal? (cdr x))))))
	

;-------------------+
;                   |
;    PARSER         |
;                   |
;-------------------+


; This is a parser for simple Scheme expressions, such as those in EOPL, 3.1 thru 3.3.

; You will want to replace this with your parser that includes more expression types, more options for these types, and error-checking.

; Procedures to make the parser a little bit saner.
(define 1st car)
(define 2nd cadr)
(define 3rd caddr)
(define 4th cadddr)

(define parse-exp         
  (lambda (datum)
    (cond
      [(symbol? datum)
       (var-exp datum)]
      
      [(literal? datum)
       (lit-exp datum)]
      
      [(pair? datum)
       (cond
         [(eq? 'lambda (1st datum))
          (cond
            [(not (<= 3 (length datum)))
             (eopl:error 'parse-exp "bad lambda: lambda missing arguments or body")]
            [(not (or (pair-or-null? (2nd datum))
                      (symbol? (2nd datum))))
             (eopl:error 'parse-exp "bad lambda: arguments are not a pair, null, or a symbol")]
            [(if (symbol? (2nd datum))
                 #f
                 (if (improper? (2nd datum))
                     (not (andmap-imp symbol? (2nd datum)))
                     (not (map (lambda (x) (or (and (list? x) (eq? 'ref (car x))) (symbol? x))) (2nd datum))) ))
             (eopl:error 'parse-exp "bad lambda: arguments are not symbols or references")]
            [else  
              (if (symbol? (2nd datum))
                  (lambda-variable-exp
                    (2nd datum)
                    (if (not (null? (cdddr datum)))
                        (map parse-exp (cddr datum))
                        (list (parse-exp (3rd datum)))))
                  (if (improper? (2nd datum))
                      (lambda-improper-exp
                        (2nd datum)
                        (if (not (null? (cdddr datum)))
                            (map parse-exp (cddr datum))
                            (list (parse-exp (3rd datum)))))  
                      (lambda-exp
                        (2nd datum)
                        (if (not (null? (cdddr datum)))
                            (map parse-exp (cddr datum))
                            (list (parse-exp (3rd datum)))))))])]
         
         [(eq? 'let (1st datum))
          (if (symbol? (2nd datum))
              (cond
                [(not (<= 4 (length datum)))
                 (eopl:error 'parse-exp "bad named let: missing name, bound, or body")]
                [(not (list? (3rd datum)))
                 (eopl:error 'parse-exp "bad named let: bound not a list")]
                [(not (andmap list? (3rd datum)))
                 (eopl:error 'parse-exp "bad named let: bound lists are not all proper lists")]
                [(not (andmap length-two? (3rd datum)))
                 (eopl:error 'parse-exp "bad named let: bound lists are not all length 2")]
                [(not (andmap first-symbol? (3rd datum)))
                 (eopl:error 'parse-exp "bad named let: bound variables are not all symbols")]
                [else
                  (named-let-exp
                    (2nd datum)
					(map car (3rd datum))
					(map (lambda (x) (parse-exp (cadr x))) (3rd datum))
					(map parse-exp (cdddr datum)))])
              (cond
                [(not (<= 3 (length datum)))
                 (eopl:error 'parse-exp "bad let: missing bound or body")]
                [(not (list? (2nd datum)))
                 (eopl:error 'parse-exp "bad let: bound not a list")]
                [(not (andmap list? (2nd datum)))
                 (eopl:error 'parse-exp "bad let: bound lists are not all proper lists")]
                [(not (andmap length-two? (2nd datum)))
                 (eopl:error 'parse-exp "bad let: bound lists are not all length 2")]
                [(not (andmap first-symbol? (2nd datum)))
                 (eopl:error 'parse-exp "bad let: bound variables are not all symbols")]
                [else
                  (let-exp
                    (map parse-let-bound (2nd datum))
                    (if (not (null? (cdddr datum)))
                        (map parse-exp (cddr datum))
                        (list (parse-exp (3rd datum)))))]))]
         
         [(eq? 'let* (1st datum))
          (cond
            [(not (<= 3 (length datum)))
             (eopl:error 'parse-exp "bad let*: missing bound or body")]
            [(not (list? (2nd datum)))
             (eopl:error 'parse-exp "bad let*: bound not a list")]
            [(not (andmap list? (2nd datum)))
             (eopl:error 'parse-exp "bad let*: bound lists are not all proper lists")]
            [(not (andmap length-two? (2nd datum)))
             (eopl:error 'parse-exp "bad let*: bound lists are not all length 2")]
            [(not (andmap first-symbol? (2nd datum)))
             (eopl:error 'parse-exp "bad let*: bound variables are not all symbols")]
            [else
              (let*-exp
                (map parse-let-bound (2nd datum))
                (if (not (null? (cdddr datum)))
                    (map parse-exp (cddr datum))
                    (list (parse-exp (3rd datum)))))])]
         
         [(eq? 'letrec (1st datum))
          (cond
            [(not (<= 3 (length datum)))
             (eopl:error 'parse-exp "bad letrec: missing bound or body")]
            [(not (list? (2nd datum)))
             (eopl:error 'parse-exp "bad letrec: bound not a list")]
            [(not (andmap list? (2nd datum)))
             (eopl:error 'parse-exp "bad letrec: bound lists are not all proper lists")]
            [(not (andmap length-two? (2nd datum)))
             (eopl:error 'parse-exp "bad letrec: bound lists are not all length 2")]
            [(not (andmap first-symbol? (2nd datum)))
             (eopl:error 'parse-exp "bad letrec: bound variables are not all symbols")]
            [else
              (letrec-exp
				(map car (2nd datum))
				(map cadadr (2nd datum))
				(map parse-map (map cddadr (2nd datum)))
                (map parse-exp (cddr datum)))])]
         
         [(eq? 'if (1st datum))
          (cond
            [(not (or (= 3 (length datum))
                      (= 4 (length datum))))
             (eopl:error 'parse-exp "bad if: incorrect number of arguments")]
            [else
              (if (= 3 (length datum))
                  (if-noelse-exp
                    (parse-exp (2nd datum))
                    (parse-exp (3rd datum)))
                  (if-else-exp
                    (parse-exp (2nd datum))
                    (parse-exp (3rd datum))
                    (parse-exp (4th datum))))])]
         
         [(eq? 'set! (1st datum))
          (cond
            [(not (= 3 (length datum)))
             (eopl:error 'parse-exp "bad set!: incorrect number of arguments")]
            [(not (symbol? (2nd datum)))
             (eopl:error 'parse-exp "bad set!: id is not a symbol")]
            [else
              (set!-exp
                (2nd datum)
                (parse-exp (3rd datum)))])]
         
         [(eq? 'while (1st datum))
          (while-exp
            (parse-exp (2nd datum))
            (if (not (null? (cdddr datum)))
                (map parse-exp (cddr datum))
                (list (parse-exp (3rd datum)))))]
         
         [(eq? 'begin (1st datum))
          (begin-exp
            (if (not (null? (cddr datum)))
                (map parse-exp (cdr datum))
                (list (parse-exp (2nd datum)))))]
         
         [(eq? 'cond (1st datum))
          (cond-exp (map parse-exp (map car (cdr datum)))
            (map parse-map (map cdr (cdr datum))))]
         
         [(eq? 'and (1st datum))
          (if (null? (cdr datum))
              (and-exp '())
              (and-exp (map parse-exp (cdr datum))))]
         
         [(eq? 'or (1st datum))
          (if (null? (cdr datum))
              (or-exp '())
              (or-exp (map parse-exp (cdr datum))))]
         
          [(eq? 'case (1st datum))
           (case-exp
             (parse-exp (2nd datum))
             (map parse-map-extra (map car (cddr datum)))
             (map parse-map (map cdr (cddr datum))))]
			 
		  [(eq? 'define (1st datum))
		   (define-exp
				(2nd datum)
				(parse-exp (3rd datum)))]
             
                  
         [(improper? datum)
          (eopl:error 'parse-exp "bad application: not a proper list")]
         [else (app-exp (parse-exp (1st datum))
         		      (map parse-exp (cdr datum)))])]
      [else (eopl:error 'parse-exp "bad expression: ~s" datum)])))

(define parse-map
  (lambda (x)
    (map parse-exp x)))

(define parse-map-extra
  (lambda (x)
    (if (list? x)
        (map parse-exp x)
        (list (parse-exp x)))))

;Andmap for an improper list
(define andmap-imp
  (lambda (proc ls)
    (if (not (pair? ls))
        (proc ls)
        (and (proc (car ls))
             (andmap-imp proc (cdr ls))))))

;Determines if a list is an improper list
(define improper?
  (lambda (ls)
    (if (null? ls)
        #f
        (if (not (pair? ls))
            #t
            (improper? (cdr ls))))))

;Determines the the first element of a list is a symbol
(define first-symbol?
  (lambda (x)
    (symbol? (car x))))

;Determines if a list is of length 2
(define length-two?
  (lambda (x)
    (= 2 (length x))))

;Parses the second element in a pair
(define parse-let-bound
  (lambda (x)
    (list (car x) (parse-exp (cadr x)))))


      



	  
(define cell
	(lambda (value)
		(box value)))
		
(define cell?
	(lambda (obj)
		(box? obj)))
		
(define cell-ref
	(lambda (cellE)
		(unbox cellE)))
		
(define cell-set!
	(lambda (cellE value)
		(set-box! cellE value)))
	  
(define deref
	(lambda (ref)
		(cell-ref ref)))
		
(define set-ref!
	(lambda (ref value)
		(cell-set! ref value)))
		
	  

;-------------------+
;                   |
;   ENVIRONMENTS    |
;                   |
;-------------------+





; Environment definitions for CSSE 304 Scheme interpreter.  Based on EoPL section 2.3

(define empty-env
  (lambda ()
    (empty-env-record)))

(define extend-env
  (lambda (syms vals env)
    (extended-env-record syms (map (lambda (x) (if (cell? x) x (cell x))) vals) env)))

(define list-find-position
  (lambda (sym los)
    (list-index (lambda (xsym) (eqv? sym xsym)) los)))

(define list-index
  (lambda (pred ls)
    (cond
     ((null? ls) #f)
     ((pred (car ls)) 0)
     (else (let ((list-index-r (list-index pred (cdr ls))))
	     (if (number? list-index-r)
		 (+ 1 list-index-r)
		 #f))))))

(define apply-env
	(lambda (env var succeed fail)
		(deref (apply-env-ref env var succeed fail))))
		 
(define apply-env-ref
  (lambda (env sym succeed fail) ; succeed and fail are procedures applied if the var is or isn't found, respectively.
    (cases environment (if (cell? env)(cell-ref env) env)
      (empty-env-record ()
        (fail))
      (extended-env-record (syms vals env)
	(let ((pos (list-find-position sym syms)))
      	  (if (number? pos)
	      (succeed (list-ref vals pos))
	      (apply-env-ref env sym succeed fail))))
	(recursively-extended-env-record
		(procnames idss bodiess old-env)
			(let ([pos (list-find-position sym procnames)])
				(if (number? pos)
					(if (symbol? (list-ref idss pos))
						(cell (variable-closure (list-ref idss pos)
							 (list-ref bodiess pos)
							 env))
						(if (improper? (list-ref idss pos))
							(cell (improper-closure (list-ref idss pos)
								(list-ref bodiess pos)
								env))
							(cell (closure (list-ref idss pos)
								(list-ref bodiess pos)
								env))))
					(apply-env-ref old-env sym succeed fail)))))))
					
					
(define extend-env-recursively
	(lambda (proc-names idss bodiess old-env)
		(recursively-extended-env-record
			proc-names idss bodiess old-env)))








;-----------------------+
;                       |
;   SYNTAX EXPANSION    |
;                       |
;-----------------------+



;Syntatically expands parsed statements
(define syntax-expand
  (lambda (ls)
    (cases expression ls
      [var-exp (id)
        (var-exp id)]
      
      [lit-exp (id)
        (lit-exp id)]
      
      [lambda-exp (bound body)
        (lambda-exp bound
          (if (expression? body)
               (list (syntax-expand body))
               (map syntax-expand body)))]
      
      [lambda-improper-exp (bound body)
        (lambda-improper-exp bound
          (if (expression? body)
               (list (syntax-expand body))
               (map syntax-expand body)))]
      
      [lambda-variable-exp (bound body)
        (lambda-variable-exp bound
          (if (expression? body)
               (syntax-expand body)
               (map syntax-expand body)))]
  
      [let-exp (bound body)
        (app-exp (lambda-exp (map 1st bound)
                     (if (expression? body)
                         (list (syntax-expand body))
                         (map syntax-expand body)))
          (map syntax-expand (map 2nd bound)))]
  
      [let*-exp (bound body)
        (if (null? bound)
            (syntax-expand (begin-exp body))
            (if (null? (cdr bound))
                (syntax-expand
                  (let-exp bound body))
                (syntax-expand
                  (let-exp (list (car bound))
                    (let*-exp (cdr bound) body)))))]
  
      [letrec-exp (proc-names idss bodiess letrec-body)
        (letrec-exp proc-names
			idss
            (map syntax-map bodiess)
			(if (expression? letrec-body)
               (list (syntax-expand letrec-body))
               (map syntax-expand letrec-body)))]
  
      [named-let-exp (proc-name ids bodies named-let-body)
        (syntax-expand 
			(letrec-exp (list proc-name) (list ids) (list named-let-body) (app-exp (parse-exp proc-name) bodies)))]
      
      [if-noelse-exp (test body)
        (if-noelse-exp (syntax-expand test) (syntax-expand body))]
      
      [if-else-exp (test body1 body2)
        (if-else-exp (syntax-expand test) (syntax-expand body1) (syntax-expand body2))]
  
      [set!-exp (id body)
        (set!-exp id (syntax-expand body))]
      
      [app-exp (rator rand)
        (app-exp (syntax-expand rator)
          (map syntax-expand rand))]
      
      [while-exp (test-exp body)
        (while-exp (syntax-expand test-exp) (map syntax-expand body))]
      
      [begin-exp (body)
        (syntax-expand
          (let-exp '() body))]
      
      [cond-exp (test-cases bodies)
        (if (equal? '(var-exp else) (car test-cases))
            (syntax-expand (begin-exp (car bodies)))
            (if-else-exp (syntax-expand (car test-cases))
              (syntax-expand (begin-exp (car bodies)))
              (syntax-expand (cond-exp (cdr test-cases)
                               (cdr bodies)))))]
            
      [and-exp (body)
        (if (null? body)
            (lit-exp #t)
            (if (null? (cdr body))
                (syntax-expand (car body))
                (if-else-exp (syntax-expand (car body))
                  (syntax-expand (and-exp (cdr body)))
                  (lit-exp #f))))]
      
      [or-exp (body)
        (if (null? body)
            (lit-exp #f)
            (if (null? (cdr body))
                (syntax-expand (car body))
				(syntax-expand (let-exp (list (list 'a (syntax-expand (car body))))
                (list (if-else-exp (var-exp 'a)
                  (var-exp 'a)
                  (syntax-expand (or-exp (cdr body)))))))))]
      
      [case-exp (key test-cases bodies)
        (if (null? (car test-cases))
            (syntax-expand (case-exp key (cdr test-cases)
                             (cdr bodies)))
            (if (equal? '(var-exp else) (caar test-cases))
                (syntax-expand (begin-exp (car bodies)))
                (if-else-exp (app-exp (var-exp 'equal?) (list (syntax-expand (caar test-cases)) (syntax-expand key)))
                  (syntax-expand (begin-exp (car bodies)))
                  (syntax-expand (case-exp key 
                                   (cons (cdar test-cases)
                                     (cdr test-cases))
                                   bodies)))))]
								   
		[define-exp (id body)
			(define-exp id (syntax-expand body))])))


(define syntax-map
	(lambda (e)
		(map syntax-expand e)))






;-------------------+
;                   |
;    INTERPRETER    |
;                   |
;-------------------+



; top-level-eval evaluates a form in the global environment

(define top-level-eval
  (lambda (form env)
    ; later we may add things that are not expressions.
    
	(eval-exp form env)))
	
(define reset-global-env
	(lambda () (cell-set! global-env (make-init-env))))

; eval-exp is the main component of the interpreter

(define eval-exp
  (lambda (exp env)
    (cases expression exp
      [lit-exp (datum) 
        (if (list? datum)
            (if (quoted? datum)
                (cadr datum)
                datum)
            datum)]
      [var-exp (id)
				(apply-env env id ;look up its value.
      	   (lambda (x) x) ; procedure to call if id is in the environment 
           (lambda () (eopl:error 'apply-env ; procedure to call if id not in env
		          "variable not found in environment: ~s"
			   id)))] 
      [app-exp (rator rands)
        (let ([proc-value (eval-exp rator env)]
              [args (eval-rands rands env)])
          (apply-proc proc-value args))]
	  [letrec-exp (proc-names idss bodiess letrec-body) 
		(eval-bodies letrec-body (extend-env-recursively proc-names idss bodiess env))]

      [let-exp (bound bodies)
        (let ([new-env (extend-env (map 1st bound)
                         (eval-rands (map 2nd bound) env)
                         env)])
          (eval-bodies bodies new-env))]
      [if-noelse-exp (test-exp then-exp)
        (if (eval-exp test-exp env)
            (eval-exp then-exp env))]
      [if-else-exp (test-exp then-exp else-exp)
        (if (eval-exp test-exp env)
            (eval-exp then-exp env)
            (eval-exp else-exp env))]
      [lambda-exp (bound body)
        (closure bound body env)]
      [lambda-improper-exp (bound body)
        (improper-closure bound body env)]
      [lambda-variable-exp (bound body)
        (variable-closure bound body env)]
      [while-exp (test-exp body)
        (while-proc test-exp body env)]
	  [set!-exp (id expr)
		(set-ref! (apply-env-ref env id 
		(lambda (x) x) (lambda () (eopl:error 'set!-exp "Error we don't want: ~a" exp)))
		(eval-exp expr env))]
	  [define-exp (id body)
		(cell-set! global-env (list 'extended-env-record (cons id (2nd (cell-ref global-env))) 
				(cons (cell (eval-exp body env)) (3rd (cell-ref global-env)))
				(empty-env)))]
      [else (eopl:error 'eval-exp "Bad abstract syntax: ~a" exp)])))

(define while-proc
  (lambda (test body env)
    (if (eval-exp test env)
        ((lambda ()
           (eval-bodies body env)
           (while-proc test body env))))))
     
;Evaluates the bodies of an expression
(define eval-bodies
  (lambda (bodies env)
    (let loop ([bodies bodies])
      (if (null? (cdr bodies))
          (eval-exp (car bodies) env)
          (begin
            (eval-exp (car bodies) env)
            (loop (cdr bodies)))))))

; evaluate the list of operands, putting results into a list
(define eval-rands
  (lambda (rands env)
    (map (lambda (expr) (cool-helper-function expr env)) rands)))
	
(define cool-helper-function
	(lambda (expr env)
		(cases expression expr
		[var-exp (id)
			(apply-env-ref env id (lambda (x) x) (lambda (x) x))]
		[else
			(cell (eval-exp expr env))])))

;  Apply a procedure to its arguments.
;  At this point, we only have primitive procedures.  
;  User-defined procedures will be added later.

(define apply-proc
  (lambda (proc-value args)
    (cases proc-val (if (cell? proc-value)(cell-ref proc-value) proc-value)
      [prim-proc (op) (apply-prim-proc op (map deref args))]
      [closure (vars bodies env)
        (let ([new-env (extend-env (create-vars vars) (create-args vars args env) env)])
          (eval-bodies bodies new-env))]
      [variable-closure (var bodies env)
        (let ([new-env (extend-env (list var)
                         (list (map deref args)) env)])
          (eval-bodies bodies new-env))]
      [improper-closure (vars bodies env)
        (let ([new-env (extend-env (make-proper vars)
                         (improper-closure-list vars (map deref args)) env)])
          (eval-bodies bodies new-env))]
			; You will add other cases
      [else (eopl:error 'apply-proc
                   "Attempt to apply bad procedure: ~s" 
                    proc-value)])))
           
(define create-vars
	(lambda (vars)
		(if (null? vars)
			'()
			(if (list? (car vars))
				(cons (cadar vars) (create-vars (cdr vars)))
				(cons (car vars) (create-vars (cdr vars)))))))
		   
(define create-args
	(lambda (vars args env)
		(if (null? vars)
			'()
			(if (list? (car vars))
				(cons (car args) (create-args (cdr vars) (cdr args) env))
				(cons (deref (car args)) (create-args (cdr vars) (cdr args) env))))))
				
(define improper-closure-list
  (lambda (x y)
    (if (literal? x)
        (list y)
        (cons (car y)
          (improper-closure-list (cdr x)
            (cdr y))))))
                  
(define make-proper
  (lambda (x)
    (if (literal? x)
        (cons x '())
        (cons (car x)
          (make-proper (cdr x))))))

(define *prim-proc-names* '(+ - * add1 sub1 cons = / zero? 
                            not < <= > >= car cdr list null? 
                            assq eq? equal? atom? length list->vector
                            list? pair? procedure? vector->list vector
                            make-vector vector-ref vector? number? symbol?
                            set-car! set-cdr! vector-set! display  newline
                            cddr cdddr cdar cadr caar cddar cdadr cdaar caddr
                            cadar caadr caaar map apply quotient append eqv?
							list-tail))

(define init-env         ; for now, our initial global environment only contains 
  (extend-env            ; procedure names.  Recall that an environment associates
     *prim-proc-names*   ;  a value (not an expression) with an identifier.
     (map prim-proc      
          *prim-proc-names*)
     (empty-env)))
	 
(define make-init-env
	(lambda ()
		init-env))
	 
(define global-env (cell init-env))

;Determines if a list contains an element
(define contains?
  (lambda (ls ele)
    (if (null? ls)
        #f
        (if (equal? (car ls) ele)
            #t
            (contains? (cdr ls) ele)))))


; Usually an interpreter must define each 
; built-in procedure individually.  We are "cheating" a little bit.

(define apply-prim-proc
  (lambda (prim-proc args)
    (case prim-proc
      [(+) (apply + args)]
      [(-) (apply - args)]
      [(*) (apply * args)]
      [(add1) (+ (1st args) 1)]
      [(sub1) (- (1st args) 1)]
      [(cons) (cons (1st args) (2nd args))]
      [(=) (= (1st args) (2nd args))]
      [(/) (/ (1st args) (2nd args))]
      [(zero?) (zero? (1st args))]
      [(not) (not (1st args))]
      [(<) (< (1st args) (2nd args))]
      [(<=) (<= (1st args) (2nd args))]
      [(>=) (>= (1st args) (2nd args))]
      [(>) (> (1st args) (2nd args))] 
      [(car) (car (1st args))]
      [(cdr) (cdr (1st args))]
      [(list) args]
      [(null?) (null? (1st args))]
      [(assq) (assq (1st args) (2nd args))]
      [(eq?) (eq? (1st args) (2nd args))]
      [(equal?) (equal? (1st args) (2nd args))]
      [(atom?) (atom? (1st args))]
      [(length) (length (1st args))]
      [(list->vector) (list->vector (1st args))] 
      [(list?) (list? (1st args))]
      [(pair?) (pair? (1st args))]
      [(procedure?) (proc-val? (1st args))] 
      [(vector->list) (vector->list (1st args))]
      [(vector) (apply vector args)]
      [(make-vector) (make-vector (1st args) (2nd args))]
      [(vector-ref) (vector-ref (1st args) (2nd args))] 
      [(number?) (number? (1st args))]
      [(vector?) (vector? (1st args))]
      [(symbol?) (symbol? (1st args))]
      [(set-car!) (set-car! (1st args) (2nd args))]
      [(set-cdr!) (set-cdr! (1st args) (2nd args))]
      [(vector-set!) (vector-set! (1st args) (2nd args) (3rd args))]
      [(display) (apply display args)]
      [(newline) (apply newline args)]
      [(cddr) (cddr (1st args))]
      [(cdddr) (cdddr (1st args))]
      [(cdar) (cdar (1st args))]
      [(cadr) (cadr (1st args))]
      [(caar) (caar (1st args))]
      [(cddar) (cddar (1st args))]
      [(cdadr) (cdadr (1st args))]
      [(cdaar) (cdaar (1st args))]
      [(caddr) (caddr (1st args))]
      [(cadar) (cadar (1st args))]
      [(caadr) (caadr (1st args))]
      [(caaar) (caaar (1st args))]
      [(map) (map (lambda (x) (apply-proc (1st args) (list (cell x)))) (2nd args))]
      [(apply) (apply-proc (1st args) (map cell (2nd args)))]
      [(quotient) (quotient (1st args) (2nd args))]
	  [(append) (apply append args)]
	  [(eqv?) (eqv? (1st args) (2nd args))]
	  [(list-tail) (list-tail (1st args) (2nd args))]
      [else (error 'apply-prim-proc 
            "Bad primitive procedure name: ~s" 
            prim-proc)])))

(define rep      ; "read-eval-print" loop.
  (lambda ()
    (display "--> ")
    ;; notice that we don't save changes to the environment...
    (let ([answer (top-level-eval (parse-exp (read)))])
      ;; TODO: are there answers that should display differently?
      (eopl:pretty-print answer) (newline)
      (rep))))  ; tail-recursive, so stack doesn't grow.

(define eval-one-exp
  (lambda (x) (top-level-eval (syntax-expand (parse-exp x)) global-env)))