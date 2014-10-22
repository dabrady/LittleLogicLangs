(module mk/micro racket
  (require "micro-internals.rkt"
           (for-syntax syntax/parse
                       "mk-stx.rkt"))
  (provide (all-from-out racket)
           fresh conde run run* == =/=)
  
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

  (define-syntax (run* stx)
    (syntax-parse stx
      [(_ (q) g0:goal g:goal ...)
       #'(let ((q (var 'q)))
           (map (reify-1st q)
                (take* (call/empty-state (conj+ g0 g ...)))))]))

   
  )

  ;; And that's the story. Don't forget to provide the miniKanren stuff
  ;; out at the top. Which I did when you weren't looking. 