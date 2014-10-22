(module mk-stx racket
  (require syntax/parse)
  (provide
           symbol
           goal-cons
           goal
           goal-seq
           relation
           builtin-relation?
           relation-id?
           valid-goal-cons?)

  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ; List of built-in relations. Put any identifier here that you wish to sneak by the macro system.
  (define BUILTIN-RELATIONS '(quote quasiquote fresh conde run run* == =/= disj+ conj+))
  
  (define builtin-relation?
    (lambda (id)
      (memq id BUILTIN-RELATIONS)))
  
  (define relation-id?
    (lambda (id)
      (let* ([id-string (symbol->string id)]
             [last (string-ref id-string (sub1 (string-length id-string)))])
            (char=? last #\o)))) ; Relations conventionally end in -o
  
  (define valid-goal-cons?
    (lambda (id)
      (or (builtin-relation? id)
          (relation-id? id))))
  
  ; I don't know why this isn't already a thing. They've got one for all the other primitives.
  (define-syntax-class symbol
    #:description "a symbol"
    #:datum-literals (quote)
    (pattern (quote x:id)))
  
  (define-syntax-class goal-cons
    #:description "a goal constructor"
    (pattern proc:id
             #:fail-unless (valid-goal-cons? (syntax-e #'proc))
                         (let ([id (syntax-e #'proc)])
                           (cond
                             [(eq? id 'cond)
                              (format "did you mean \"conde\"?")]
                             [(eq? id 'freshe)
                              (format "did you mean \"fresh\"?")]
                             [else (format "~a may not be a goal constructor (identifier doesn't end in -o)" id)]))))
  
  (define-syntax-class goal
    #:description "a goal"
    (pattern (~or x:relation
                  (p:goal-cons y:expr ...+)))) ; one or more args to constructor enforced; replace ...+ with ... if 0 or more is desired
  
  (define-syntax-class goal-seq
    #:description "a sequence of goals"
    (pattern (g:goal ...+)))
  
  ; A freshmen relation is a lambda of >0 arguments whose body is a goal.
  (define-syntax-class relation
    #:description "a relation of one or more arguments"
    #:datum-literals (lambda)
    (pattern (lambda (x ...+)
               body:goal)))  
  )