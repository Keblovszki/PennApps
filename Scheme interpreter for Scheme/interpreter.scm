;Opgave 1
;Overvejelse af spørgsmålene:
;1) Hvis en af argumenter man tager med at tom, så adder den, den tomme
;liste til den samlede liste, men den kan man ikke se.
;2) Hvis man skriver andet end en liste, så får man en fejlmeddelse
;3) Hvis der ingen parametre er, giver vi den tomme liste.
;4) Hvis der er én parameter, så er det den der bliver returneret.
(define proper-list-append-dyadic
  (lambda (x1 x2)
    (letrec ([visit (lambda (x1)
                      (if (null? x1)
                          x2
                          (cons (car x1) (visit (cdr x1)))))])
      (if (list? x1)
          (visit x1)
          (errorf 'proper-list-append "not a list: ~s" x1)))))

(define proper-list-append
  (lambda xs
    (letrec ([visit (lambda (xs)
                    (if (null? xs)
                        '()
                        (proper-list-append-dyadic (car xs)
                                                   (visit (cdr xs)))))])
      (visit xs))))

;Opgave 2
(define proper-list-of-given-length?
  (lambda (v n)
    (or (and (null? v)
             (= n 0))
        (and (pair? v)
             (> n 0)
             (proper-list-of-given-length? (cdr v)
                                           (- n 1))))))

;Checking the program
(define check-program
  (lambda (v)
    (cond
      [(null? v)
       #t]
      [(pair? v)
       (and (check-toplevel-form (car v))
            (check-program (cdr v)))]
      [else
       #f])))

(define check-toplevel-form
  (lambda (v)
    (cond
      [(is-definition? v)
       (check-definition v)]
      [else
       (check-expression v)])))

;;;;;;;;;;
;;; basic predicates and accessors for definitions:
;;;;;;;;;;

;;; predicate:
(define is-definition?
  (lambda (v)
    (and (proper-list-of-given-length? v 3)
         (equal? (car v) 'define))))

;;; 1st accessor:
(define define-1
  (lambda (v)
    (list-ref v 1)))

;;; 2nd accessor:
(define define-2
  (lambda (v)
    (list-ref v 2)))

;;;;;;;;;;
;;; the syntax checker proper for definitions:
;;;;;;;;;;

(define check-definition
  (lambda (v)
    (and (check-variable (define-1 v))
         (check-expression (define-2 v)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;
;;; basic predicates and accessors for expressions:
;;;;;;;;;;

;;; predicate:
(define is-time?
  (lambda (v)
    (and (proper-list-of-given-length? v 2)
         (equal? (car v) 'time))))

;;; 1st accessor:
(define time-1
  (lambda (v)
    (list-ref v 1)))

;;; predicate:
(define is-if?
  (lambda (v)
    (and (proper-list-of-given-length? v 4)
         (equal? (car v) 'if))))

;;; 1st accessor:
(define if-1
  (lambda (v)
    (list-ref v 1)))

;;; 2nd accessor:
(define if-2
  (lambda (v)
    (list-ref v 2)))

;;; 3rd accessor:
(define if-3
  (lambda (v)
    (list-ref v 3)))

;Vi antager, at en cond, skal have en cond.
;;; predicate:
(define is-cond?
  (lambda (v)
    (and (list-strictly-longer-than? v 1)
         (equal? (car v) 'cond))))

;;; 1st accessor:
(define cond-1
  (lambda (v)
    (list-ref v 1)))

;;; 2nd accessor:
(define cond-rest
  (lambda (v)
    (list-tail v 2)))

;;; predicate:
(define is-and?
  (lambda (v)
    (and (list-strictly-longer-than? v 0)
         (equal? (car v) 'and))))

;;; 1st accessor:
(define and-1
  (lambda (v)
    (list-ref v 1)))

;;; 2nd accessor:
(define and-rest
  (lambda (v)
    (list-tail v 2)))

;;; predicate:
(define is-or?
  (lambda (v)
    (and (list-strictly-longer-than? v 0)
         (equal? (car v) 'or))))

;;; 1st accessor:
(define or-1
  (lambda (v)
    (list-ref v 1)))

;;; 2nd accessor:
(define or-2
  (lambda (v)
    (list-tail v 2)))

;;; predicate:
(define is-quote?
  (lambda (v)
    (and (proper-list-of-given-length? v 2)
         (equal? (car v) 'quote))))

;;; 1st accessor:
(define quote-1
  (lambda (v)
    (list-ref v 1)))

;;; predicate:
(define is-begin?
  (lambda (v)
    (and (list-strictly-longer-than? v 1)
         (equal? (car v) 'begin))))

;;; 1st accessor:
(define begin-1
  (lambda (v)
    (list-ref v 1)))

;;; 2nd accessor:
(define begin-rest
  (lambda (v)
    (list-tail v 2)))

;;; predicate:
(define is-quasiquote?
  (lambda (v)
    (and (proper-list-of-given-length? v 2)
         (equal? (car v) 'quasiquote))))

;;; 1st accessor:
(define quasiquote-1
  (lambda (v)
    (list-ref v 1)))

;;; predicate:
(define is-unquote?
  (lambda (v)
    (and (proper-list-of-given-length? v 2)
         (equal? (car v) 'unquote))))

;;; 1st accessor:
(define unquote-1
  (lambda (v)
    (list-ref v 1)))

;;; predicate:
(define is-unquote-splicing?
  (lambda (v)
    (and (proper-list-of-given-length? v 2)
         (equal? (car v) 'unquote-splicing))))

;;; 1st accessor:
(define unquote-splicing-1
  (lambda (v)
    (list-ref v 1)))

;;; predicate:
(define is-letstar?
  (lambda (v)
    (and (proper-list-of-given-length? v 3)
         (equal? (car v) 'let*))))

;;; predicate:
(define is-let?
  (lambda (v)
    (and (proper-list-of-given-length? v 3)
         (equal? (car v) 'let))))

;;; predicate:
(define is-letrec?
  (lambda (v)
    (and (proper-list-of-given-length? v 3)
         (equal? (car v) 'letrec))))

;;; predicate:
(define is-case?
  (lambda (v)
    (and (list-strictly-longer-than? v 2)
         (equal? (car v) 'case))))

;;; predicate:
(define is-lambda-abstration?
  (lambda (v)
    (or
     (and 
      (proper-list-of-given-length? v 3)
      (equal? (car v) 'lambda))
     (and
      (proper-list-of-given-length? v 4)
      (equal? (car v) 'trace-lambda)))))

;;;predicate
(define is-application?
  (lambda (v)
    (and (list-strictly-longer-than? v 0)
         (check-expression (car v)))))

;;;;;;;;;;
;;; the syntax checker for proper expressions:
;;;;;;;;;;

(define check-expression
  (lambda (v)
    (cond
      [(number? v)
       #t]
      [(boolean? v)
       #t]
      [(char? v)
       #t]
      [(string? v)
       #t]
      [(symbol? v)
       (check-variable v)]
      [(is-time? v)
       (check-time-expression v)]
      [(is-if? v)
       (check-if-expression v)]
      [(is-cond? v)
       (check-cond-expression v)]
      [(is-case? v)
       (check-case-expression v)]
      [(is-and? v)
       (check-and-expression v)]
      [(is-or? v)
       (check-or-expression v)]
      [(is-let? v)
       (check-let-expression v)]
      [(is-letstar? v)
       (check-letstar-expression v)]
      [(is-letrec? v)
       (check-letrec-expression v)]
      [(is-begin? v)
       (check-begin-expression v)]
      [(is-quote? v)
       (check-quote-expression v)]
      [(is-quasiquote? v)
       (check-quasiquote-expression v)]
      [(is-lambda-abstration? v)
       (check-lambda-abstraction-expression v)]
      [(is-application? v)
       (check-application-expression v)]
      [else
       #f
       ])))

(define check-quotation
  (lambda (v)
    (cond
      [(number? v)
       #t]
      [(boolean? v)
       #t]
      [(char? v)
       #t]
      [(string? v)
       #t]
      [(symbol? v)
       #t]
      [(null? v)
       #t]
      [(and
        (pair? v)
        (check-quotation (car v)) 
        (check-quotation (cdr v)))]
      [else
       #f])))

(define member? 
  (lambda (x list)
    (if (null? list)
        #f
        (if (equal? x (car list))
            #t
            (member? x (cdr list))))))
    

(define check-variable
  (lambda (v)
    (cond
      [(or
        (member? v
                 '(time 
                   if 
                   cond 
                   else 
                   case 
                   and 
                   define
                   or 
                   let 
                   let* 
                   letrec 
                   begin 
                   quote 
                   quasiquote 
                   unquote 
                   unquote-splicing 
                   lambda 
                   trace-lambda))
        (not (symbol? v)))
       #f]
      [else
       #t])))

(define check-time-expression
  (lambda (v)
    (check-expression (time-1 v))))

(define kleene
  (lambda (f v)
    (or (null? v)
        (and (pair? v)
             (f (car v))
             (kleene f (cdr v))))))

(define check-if-expression
  (lambda (v)
    (and (check-expression (if-1 v))
         (check-expression (if-2 v))
         (check-expression (if-3 v)))))

(define check-and-expression
  (lambda (v)
    (letrec ([visit (lambda (i)
                      (if (null? i)
                          #t
                          (and (pair? i)
                               (check-expression (car i))
                               (visit (cdr i)))))])
      (visit (cdr v)))))
                             
(define check-or-expression
  (lambda (v)
    (letrec ([visit (lambda (i)
                      (if (null? i)
                          #t
                          (and (pair? i)
                               (check-expression (car i))
                               (visit (cdr i)))))])
      (visit (cdr v)))))

(define check-quote-expression
  (lambda (v)
    (check-quotation (quote-1 v))))

(define check-cond-clause
  (lambda (v)
    (cond 
      [(proper-list-of-given-length? v 1)
       (check-expression (car v))]
      [(proper-list-of-given-length? v 2)
       (and (check-expression (car v))
            (check-expression (cadr v)))]
      [(proper-list-of-given-length? v 3)
       (and (check-expression (car v))
            (equal? (cadr v) '=>)
            (check-expression (list-ref v 2)))]
      [else
       #f])))

(define check-cond-expression
  (lambda (v)
    (cond
      [(letrec ([visit (lambda (e)
                         (or
                          (and   ;;Her ser vi om vi er ved det sidste element
                           (pair? e)
                           (pair? (car e))
                           (null? (cdr e))
                           (equal? (caar e) 'else)
                           (check-expression (cadr (car e))))
                          (and 
                           (pair? e)
                           (check-cond-clause (car e))
                           (visit (cdr e)))))])
         (visit (cdr v)))
       #t]
      [else
       #f])))

(define check-case-expression
  (lambda (v)
    (cond
      [(and (check-expression (car (cdr v)))
            (letrec ([visit (lambda (e)
                              (if (proper-list-of-given-length? e 1)
                                  (and (proper-list-of-given-length? (car e) 2)
                                       (equal? (list-ref (car e) 0) 'else)
                                       (check-expression (list-ref (car e) 1)))
                                  (and (proper-list-of-given-length? (car e) 2)
                                       (kleene check-quotation (list-ref (car e) 0))
                                       (check-expression (list-ref (car e) 1))
                                       (visit (cdr e)))))])
              (visit (cdr (cdr v)))))
       #t]
      [else
       #f])))
                            

;Hjælp til let*
(define list-two-list-letstar?
  (lambda (v)
    (if (null? v)
             #t
             (and (list? v)
                  (proper-list-of-given-length? (car v) 2)
                  (check-variable (list-ref (car v) 0))
                  (check-expression (list-ref (car v) 1))
                  (list-two-list-letstar? (cdr v))))))

;Hjælp til let
(define list-two-list-let?
  (lambda (v list)
    (if (null? v)
             #t
             (and (list? v)
                  (proper-list-of-given-length? (car v) 2)
                  (if (member? (list-ref (car v) 0) list)
                      #f
                      (and (check-variable (list-ref (car v) 0)) 
                           (check-expression (list-ref (car v) 1))
                           (list-two-list-let? (cdr v) (cons (list-ref (car v) 0) list))))))))

;Hjælp til letrec
(define list-two-list-letrec?
  (lambda (v list)
    (if (null? v)
        #t
        (and (list? v)
             (proper-list-of-given-length? (car v) 2)
             (if (member? (list-ref (car v) 0) list)
                 #f
                 (and (check-variable (list-ref (car v) 0))
                      (check-lambda-abstraction-expression (list-ref (car v) 1))
                      (list-two-list-letrec? (cdr v) (cons (list-ref (car v) 0) list))))))))

(define check-let-expression
  (lambda (v)
    (and (list-two-list-let? (list-ref v 1) '())
         (check-expression (list-ref v 2)))))

(define check-letstar-expression
  (lambda (v)
    (and (list-two-list-letstar? (list-ref v 1))
         (check-expression (list-ref v 2)))))

(define check-letrec-expression
  (lambda (v)
    (and (list-two-list-letrec? (list-ref v 1) '())
         (check-expression (list-ref v 2)))))
      
;Hjælpemetode til lambdaformal:
(define laformals
  (lambda (v list)
    (cond 
      [(pair? v)
       (and (check-variable (car v))
            (if (member (car v) list)
                #f
                (laformals (cdr v) (cons (car v) list))))]
      [(check-variable v)
       (if (member v list)
           #f
           #t)]
      [(null? v)
       #t]
      [else
       #f])))

(define check-lambdaformal-expression
  (lambda (v)
    (laformals v '())))

(define check-lambda-abstraction-expression
  (lambda (v)
    (if (list-strictly-longer-than? v 2)
        (or (and (equal? (list-ref v 0) 'lambda)
                 (check-lambdaformal-expression (list-ref v 1))
                 (check-expression (list-ref v 2)))
            (and (equal? (list-ref v 0) 'trace-lambda)
                 (symbol? (list-ref v 1))
                 (check-lambdaformal-expression (list-ref v 2))
                 (check-expression (list-ref v 3))))
        #f)))

(define check-begin-expression
  (lambda (v)
    (letrec ([visit (lambda (i)
                      (if (null? i)
                          #t
                          (and (pair? i)
                               (check-expression (car i))
                               (visit (cdr i)))))])
          (visit (cdr v)))))

;;;quasiquotation_0 og quasiquotation_j
(define check-quasiquote-j
  (lambda (v j)
    (cond
      [(number? v)
       #t]
      [(boolean? v)
       #t]
      [(char? v)
       #t]
      [(string? v)
       #t]
      [(symbol? v)
       #t]
      [(null? v)
       #t]
      [(is-quasiquote? v)
       (check-quasiquote-j (quasiquote-1 v) (+ j 1))]
      [(is-unquote? v)
       (if (= j 0)
           (check-expression (unquote-1 v))
           (check-quasiquote-j (unquote-1 v) (- j 1)))]
      [(is-unquote-splicing? v)
       (if (= j 0)
           (check-expression (unquote-splicing-1 v))
           (check-quasiquote-j (unquote-splicing-1 v) (- j 1)))]
      [(pair? v)
       (and (check-quasiquote-j (car v) j)
            (check-quasiquote-j (cdr v) j))]
      [else
       #f])))
  
(define check-quasiquote-expression
  (lambda (v)
    (check-quasiquote-j (quasiquote-1 v) 0)))

(define check-application-expression
  (lambda (v)
    (letrec ([visit (lambda (i)
                          (if (null? i)
                              #t
                              (and (check-expression (car i))
                                   (visit (cdr i))))
                          )])
             (visit v))))

;;;;;;;;;;
;;; auxiliaries:
;;;;;;;;;;

(define list-strictly-longer-than?
  (lambda (v n)
    (letrec ([visit (lambda (v i)
                      (and (pair? v)
                           (or (= i 0)
                               (visit (cdr v)
                                      (- i 1)))))])
      (if (>= n 0)
          (visit v n)
          (errorf 'list-strictly-longer-than? "negative length: ~s" n)))))

;;; reads an entire file as a list of Scheme data
;;; use: (read-file "filename.scm")
(define read-file
  (lambda (filename)
    (call-with-input-file filename
      (lambda (p)
        (letrec ([visit (lambda ()
                          (let ([in (read p)])
                            (if (eof-object? in)
                                '()
                                (cons in (visit)))))])
          (visit))))))

;;; interface:
(define check-file
  (lambda (filename)
    (if (string? filename)
        (check-program (read-file filename))
        (errorf 'check-file "not a string: ~s" filename))))

;tests                   
(define well-formed-expressions
  '(
    ;numbers
    2
    -3
    ;boolean
    #t
    #f
    ;characters
    #\a
    #\b
    ;strings
    ""
    "hej"
    ;variables
    x
    y
    ;time
    (time 1)
    ;if
    (if (#t) #t #f)
    ;cond
    (cond
      [(#t)
       #t]
      [else
       #f])
    ;case
    (case ((1) 1) (else 1))
    (case "not" ((1 #t #\" "a" ()) 1) (("not") 2) (else 3))
    (case 3 (((quote not) "lol") "serious") (else "stuff"))
    (case 1 ((1 "not" #t (quote lol) #\f (quote ()) (cons (cons 1 "not") (cons #t (cons (quote lol) (quote ()))))) 1) (else 1))
    ;and
    (and 1 2)
    (and 1 2 3 4 5 6)
    (and)
    ;or
    (or)
    (or 1 2 3)
    (or 1)
    ;let
    (let ((a 1)) a)
    (let ((b 2) (c 3)) c)
    ;let*
    (let* ((a 1) (a 2)) a)
    (let* ((a 1)) a)
    ;letrec
    (letrec ([visit (lambda (ws a)
                        (if (null? ws)
                            a
                            (visit (cdr ws) (cons-case (car ws) a))))])
        (visit vs nil-case))
    ;begin
    (begin 1 2 3)
    (begin 1)
    ;quote
    (quote 2)
    (quote #t)
    ;quasiquote
    (quasiquote 2)
    (quasiquote #t)
    (quasiquote quasiquote)
    ;lambda-abstraction
    (lambda ()
    (andmap (trace-lambda ill (e)
              (not (check-expression e)))
            ill-formed-expressions))
    ;application
    (2 3 4)
    ))

(define test-well-formed-expressions
  (lambda ()
    (andmap (trace-lambda well (e)
              (check-expression e))
            well-formed-expressions)))

(define ill-formed-expressions
  '(
    ;time
    (time)
    ;if
    (if)
    (if (something))
    (if (something) #t)
    (if (something) #t #t #f)
    ;cond
    (cond)
    (cond [(lol)])
    (cond [(lol)][(double-lol)])
    (cond [(lol)][else lol][(double-lol)])
    ;let
    (let ((a 1) (a 2)) a)
    (let)
    (let (((cdar distlist)
           (+ (cdr min-pair) (cddr edge)))) 
      '())
    ;letrec
    (letrec)
    (letrec x)
    ;let*
    (let* ((a 1) a))
    (let*)
    ;lambda
    (lambda (x y z . x) 1)
    (lambda (x y x . t) 1)
    (lambda (x x) 1)
    ;begin
    (begin)
    (begin . 3)
    (begin 1 2 . 3)
    ;case
    (case ((1) "not"))
    (case 1 ((1) "not") (else "not" "not"))
    (case 1 ((1)) (else "not"))
    ;quasiquote
    (quasiquote (quasiquote (quasiquote (quasiquote (quasiquote (quasiquote (quasiquote (quasiquote (quasiquote (quasiquote (quasiquote (quasiquote (unquote (unquote-splicing (unquote (unquote-splicing (unquote (unquote-splicing (unquote (unquote-splicing (unquote (unquote-splicing (unquote (unquote-splicing (unquote 1)))))))))))))))))))))))))
    (unquote unquote)
    (unquote-splicing unquote-splicing)
    (quasiquote (unquote (unquote 1)))
    (quasiquote)
    (unquote)
    (unquote-splicing)
    ))

(define test-ill-formed-expressions
  (lambda ()
    (andmap (trace-lambda ill (e)
              (not (check-expression e)))
            ill-formed-expressions)))

(define test
  (lambda ()
    (and (test-well-formed-expressions)
         (test-ill-formed-expressions))))

;Opgave 3
(define curry3
  (lambda (f)
    (lambda (x1)
      (lambda (x2)
        (lambda (x3)
          (f x1 x2 x3))))))

(define uncurry3
  (lambda (f)
    (lambda (x1 x2 x3)
      (((f x1) x2) x3))))


;Opgave 5
(define right-fold-proper-list
  (lambda (nil-case cons-case)
    (lambda (vs)
      (letrec ([visit (lambda (ws)
                        (if (null? ws)
                            nil-case
                            (cons-case (car ws)
                                       (visit (cdr ws)))))])
        (visit vs)))))

(define left-fold-proper-list
  (lambda (nil-case cons-case)
    (lambda (vs)
      (letrec ([visit (lambda (ws a)
                        (if (null? ws)
                            a
                            (visit (cdr ws) (cons-case (car ws) a))))])
        (visit vs nil-case)))))

;Which function does (right-fold-proper-list '() cons) implement?
;Den giver bare den samme liste igen, den laver den samme liste, som den har 
;som input
;Den giver:
;> (right-test '(1 2 3))
;(1 2 3)
(define right-test
  (lambda (xs)
    ((right-fold-proper-list '() cons) xs)))

;Which function does (left-fold-proper-list '() cons) implement?
;Denne laver bare listen i omvendt række. Så det er en list-reverse funktion.
;Den giver:
;> (left-test '(1 2 3))
;(3 2 1)
(define left-test
  (lambda (xs)
    ((left-fold-proper-list '() cons) xs)))
