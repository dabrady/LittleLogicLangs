(module freshman-stx racket
  (require (for-syntax syntax/parse
                       "../lib/mk-stx.rkt"))
  (provide (for-syntax (all-from-out "../lib/mk-stx.rkt"))
           freshman-define
           define-relation)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ; A companion for #define which ensures all function definitions are relations.
  (define-syntax (define-relation stx)
    (syntax-parse stx
      ; A >0 arg procedure that ends with -o and begins with #fresh or #conde.
      [(_ id:id rel:relation)
       #:fail-when (not (relation-id? (syntax-e #'id)))
                   (let ([id (syntax-e #'id)])
                     (format "relation identifier must end in -o, suggested change: ~a => ~ao"
                           id
                           id))
       #'(define id rel)]
      ; MIT notation support
      [(_ (id:id arg:id ...+) code:expr)
       #'(define-relation id (lambda (arg ...) code))]
       ))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ; A wrapper for #define which disallows lambdas, effectively restricting definitions to literals (excluding functions).
  (define-syntax (freshman-define stx)
    (syntax-parse stx
       ; A literal.
      [(_ id:id (~or x:boolean x:str x:char x:number x:symbol))
       #'(define id x)]))
  )