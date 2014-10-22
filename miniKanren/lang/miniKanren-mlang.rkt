(module miniKanren-mlang racket
  (provide (all-from-out racket)
           run run* == =/= conde absento symbolo numbero not-pairo fresh prt poke next)
  
  ;; extra stuff for racket
  (define (list-sort f l) (sort l f))
  (define (remp f l) (filter-not f l))
  (define (call-with-string-output-port f)
    (define p (open-output-string))
    (f p)
    (get-output-string p))
  (define (exists f l) (ormap f l))
  (define for-all andmap)
  (define (find f l)
    (cond [(memf f l) => car] [else #f]))
  (define memp memf)
  (define (var*? v) (var? (car v)))
  ;; My 'next' function
  (define poke
    (lambda (n)
      (let ((s (get-stream)))
        (cond
          ((pair? s) (take n (cdr s)))
          (s (take n s))
          (else (void)))))) ; This line catches the cases where the stream is empty (no more answers exist).
  ;; Better name.
  (define next poke)
  
  ;; actual code
  
  (include "mk.scm"))
