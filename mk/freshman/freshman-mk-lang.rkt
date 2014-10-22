(module freshman-mk-lang racket
  (require "../lib/micro-internals.rkt"
           "freshman-stx.rkt"
           (for-syntax syntax/parse))
  (provide (all-from-out racket)
           fresh conde == =/=
           run^ run1 run2 run3 run4 run5 run6 run7 run8 run9
           ;poke next
           conso caro cdro nullo appendo reverseo)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ; A macro specifically designed to be used with goal sequences.
  ; For example, a typical conj+ call looks like this:
  ;         (conj+ goal goal2 ...)
  ; But when using patterns and relation sequences, it might end up looking like this:
  ;         (conj+ (goal goal2 ...))
  ; This macro takes the second form and turns it into the first one.
  (define-syntax macro/splat
    (syntax-rules()
      [(_ macro (arg ...)) (macro arg ...)]))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
 
  ;; We won't have to do that inverse eta delay. Instead, we can
  ;; "snooze" a goal of our choice now.
  
  (define-syntax Zzz
    (syntax-rules ()
      ((_ g) (lambda (s/d/c)
               (lambda ()
                 (g s/d/c))))))
  
  ;; We write a simple, recursive macro that takes an
  ;; arbitrary-but-bigger-than-one number of goals, and nests their
  ;; conjunction.
  
  (define-syntax conj+
    (syntax-rules ()
      ((_ g) g)
      ((_ g0 g* ...)
       (conj g0 (conj+ g* ...)))))
  
  ;; Same deal, but for disjs
  
  (define-syntax disj+
    (syntax-rules ()
      ((_ g) g)
      ((_ g0 g* ...)
       (disj g0 (disj+ g* ...)))))
  
  ;; Sooo, h'bout we build real miniKanren fresh. A list of
  ;; things-which-will-be-variable-names, and a then a bunch of goals,
  ;; and we use those names as the variables in functions which are the
  ;; argument to call/fresh; when we get done, we conj+ up all the goals
  ;; into one big one.
  
;  (define-syntax fresh
;    (syntax-rules ()
;      ((_ () g0 g* ...) (conj+ g0 g* ...))
;      ((_ (x0 x* ...) g0 g* ...)
;       (call/fresh
;        (lambda (x0)
;          (fresh (x* ...) g0 g* ...))))))
  
  (define-syntax (fresh stx)
    (syntax-parse stx
      [(_ () g0:goal g*:goal ...) #'(conj+ g0 g* ...)]
      [(_ (x0:id x*:id ...) g0:goal g*:goal ...)
       #'(call/fresh
          (lambda (x0)
            (fresh (x* ...) g0 g* ...)))]))
  
  ;; What is conde, but a disjunction of conjunctions? We're matching
  ;; conde to miniKanren's spec, so we don't allow empty condes or empty
  ;; clauses in a conde. Which works great, 'cause we already have
  ;; operators which do that. What were the odds, eh? Now, there /is/
  ;; something that bears mention. So, any recursive relations we
  ;; specify, if they're "meaningful", have a recursion and a
  ;; base-case. Ergo, it's got a conde. So if there's recursion, there's
  ;; a conde in there somewhere. So, to guarantee termination we need
  ;; only Zzz around the definition of conde.
  
;  (define-syntax conde
;    (syntax-rules ()
;      ((_ (g0 g* ...) (g0* g** ...) ...)
;       (Zzz (disj+ (conj+ g0 g* ...)
;                   (conj+ g0* g** ...) ...)))))

  (define-syntax (conde stx) 
    (syntax-parse stx
      [(_ gs:goal-seq gs*:goal-seq ...)
       #'(Zzz (disj+ (macro/splat conj+ gs)
                     (macro/splat conj+ gs*) ...))]))
  
  ;; So, the last little bit we need is the run interface. Now, with the
  ;; advent of procedures in streams, it may be I don't have something I
  ;; /can/ reify yet. I might have an immature stream. So h'bout this
  ;; definition of pull below.
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;; Stream-saving  ;;;;;;

  ;; Off, for the moment.
  ;; Can't reify willy-nilly without knowing *the* memory address, methinks
  ;; A side effect of side-effects (a casualty, really)
  ;; --- JBH 9/2/14
  
  ; A place to hold the current stream.
  ;; (define STREAM '())
  ;; ; Save the stream.
  ;; (define set-stream!
  ;;   (lambda (x)
  ;;     (set! STREAM x)))
  ;; ; Get the unreified stream.
  ;; (define get-stream
  ;;   (lambda ()
  ;;     STREAM))      
  ;; ; Get more out of the stream.
  ;; (define poke
  ;;   (lambda (n)
  ;;     (let (($ (get-stream)))
  ;;       (cond
  ;;         ((pair? $) (map reify-1st (take n (cdr $))))
  ;;         ($ (map reify-1st (take n $)))
  ;;         (else '()))))) ; This line catches the cases where the stream is empty (no more answers exist).
  ;; ; Alias.
  ;; (define next poke)
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  
  ;; When we get an immature stream (which is a term we made up meaning
  ;; "a thunk") we just invoke it. We keep invoking it until we get a
  ;; real stream.
  
  (define (pull $) (if (procedure? $) (pull ($)) $))
  
  ;; When we wanna get n answers out of a stream, for (< n 0) we pull
  ;; the stream to maturity, and either return the empty list if the
  ;; stream is empty, otherwise cons the car onto the recursion.
  
  (define (take n $)
    (cond
      ((zero? n) '())
      (else
       (let (($ (pull $)))
         ; Save off the stream.
;;         (set-stream! $)
         (cond
           ((null? $) '())
           (else
            (cons (car $)
                  (take (- n 1) (cdr $)))))))))

  
  (define (take* $)
    (let (($ (pull $)))
      (cond
        ((null? $) '())
        (else
         (cons (car $) (take* (cdr $)))))))
  
  ;; Now to put run together. At this point, it's just putting together
  ;; the pieces. We freshen q and wrap the goals up as the body. We call
  ;; that goal we've built up in the empty-state, returning a stream. We
  ;; take n elements off of the stream, which results in a list. And we
  ;; map reify-1st over that list.
  
;  (define-syntax run
;    (syntax-rules ()
;      ((_ n (q) g0 g ...)
;       (map reify-1st
;            (take n (call/empty-state (fresh (q) (conj+ g0 g ...)))))))))
  
  (define-syntax (run stx)
    (syntax-parse stx
      [(_ n (q) g0:goal g:goal ...)
       #'(let ((q (var 'q)))
           (map (reify-1st q)
                (take n (call/empty-state (conj+ g0 g ...)))))]))
  
  
  ;;;;;;;;;;;
  (define MAX-N 9)
  ;;;;;;;;;;;
  ;; A wrapper for #run. Since numbers are illegal in mk/freshman, this provides a way of getting a
  ;; hard-coded number of answers (at the most) and encouraging the user to use #poke if they wish to 
  ;; see more.
  (define-syntax run^
    (syntax-rules ()
      [(_ (q) g ...)
       (let ([$ (run MAX-N (q) g ...)])
         (if (< (length $) MAX-N)
             $
             (begin
               (printf "There are a lot of results. Here're ~a of them. Poking for more is currently disabled.\n" MAX-N);Try poking for more if you want.\n" MAX-N)
               $)))]))
  
  ;; Some convenience macros
;  (define-syntax-rule (make-runner n)
;    (define-syntax (syntax-e #'(string->symbol (string-append "run" (number->string n))))
;      (syntax-rules ()
;        [(_ (q) g (... ...))
;         (run n (q) g (... ...))])))
  
  ;; There HAS to be a way of generating these.
  
  (define-syntax run1
    (syntax-rules ()
      [(_ (q) g ...)
       (run 1 (q) g ...)]))
  
  (define-syntax run2
    (syntax-rules ()
      [(_ (q) g ...)
       (run 2 (q) g ...)]))
  
  (define-syntax run3
    (syntax-rules ()
      [(_ (q) g ...)
       (run 3 (q) g ...)]))
  
  (define-syntax run4
    (syntax-rules ()
      [(_ (q) g ...)
       (run 4 (q) g ...)]))
  
  (define-syntax run5
    (syntax-rules ()
      [(_ (q) g ...)
       (run 5 (q) g ...)]))
  
  (define-syntax run6
    (syntax-rules ()
      [(_ (q) g ...)
       (run 6 (q) g ...)]))
  
  (define-syntax run7
    (syntax-rules ()
      [(_ (q) g ...)
       (run 7 (q) g ...)]))
  
  (define-syntax run8
    (syntax-rules ()
      [(_ (q) g ...)
       (run 8 (q) g ...)]))
  
  (define-syntax run9
    (syntax-rules ()
      [(_ (q) g ...)
       (run 9 (q) g ...)]))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

  ;; A series of helper relations, more convenience than anything else.
  (define conso
    (lambda (a d out)
      (== (cons a d) out)))
  
  (define caro
    (lambda (pr a)
      (fresh (d)
        (conso a d pr))))
  
  (define cdro
    (lambda (pr d)
      (fresh (a)
        (conso a d pr))))
  
  (define nullo
    (lambda (x)
      (== x '())))
  
  (define appendo
    (lambda (l s out)
      (conde
        [(nullo l) (== s out)]
        [(fresh (a d res)
           (conso a d l)
           (conso a res out)
           (appendo d s res))])))
  
  (define reverseo
    (lambda (ls out)
      (conde
        ((nullo ls) (nullo out))
        ((fresh (a d res)
           (conso a d ls)
           (reverseo d res)
           (appendo res `(,a) out))))))
  
  )
