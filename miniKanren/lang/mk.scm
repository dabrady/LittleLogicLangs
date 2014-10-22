;; Recently improved by Jason Hemann and Dan Friedman

;; The code of this system comprises two steps.  The first step is to run
;; a goal and check if the result fails to make sense: we term this
;; "fast fail".  If each goal goes to completion, then we have the reify
;; step.  The work of the reify step is to take the final state of the
;; computation and return a Scheme value.  This also comprises two steps.
;; The first step is to try every funtion in a cycle of functions that try
;; to make a new state, which is then fed to the next function in the cycle.
;; Each cycle function takes a state and returns a state: it cannot fail.
;; When one of the functions does not improve the state, it becomes the
;; function to reach without ever changing the state by the intervening
;; functions.  When no improvements can be made we have found a fixed point.
;; Each of these intervening cycle functions tried to change the state, but
;; couldn't.  Next we turn the value along with the non-empty fields of the
;; state into a list structure.  Reification does not appear to be a
;; bottleneck, since it is just turning an answer into something readable.
;; There may be many answers, and each answer has to be reified.

;; We have just added not-pairo to the system.  It appears to be working
;; and passes our test cases. It's field is called Np.  This field should vanish.

;; This code contains the new bizarre way of doing unifications.
;; We'll see how this works out?  Only time will tell.  See
;; giant-unify, which has changed as of Tuesday morning It has not
;; been very tested, yet.  The substitution has shadowing of
;; variables.  Each binding of a variable looks like this: (x
;; . (payload y z .. x ..)). The list that has the payload in the car
;; is the representative and we can use eq? to compare all the
;; representives of the variables y, z, .. x, .. .  When a variable is
;; introduced, it looks like this: `(,x . (,x)).  As it gets unified with
;; a different variable, say y, it becomes equivalent to
;; (let ((rep `(,x ,y))) `((,x . ,rep) (,y . ,rep))). It appears that the order of
;; the variables in the rep does not matter, but if we keep the
;; length, it might turn out to be of some value.  At any point we
;; might unify y (or x) with a nonvar, say (,z . 5) so then the new rep
;; would look like this `((,z . 5) ,x ,y) and then x's and y's binding
;; would use this new rep.  This would be by extending the
;; substitution, so we can see whene the shadowing happens.
;; See giant-walk below for some additional context.  See walk-var in
;; giant-unify, below for some needed context.  Our plan will be to
;; place the rank (generation, level, etc.) directly in front of the
;; payload and that would become the rep, once again we would maintain
;; the eq property of all reps over the list of variables in the chain.
;; If we include the rank, then (walk-var x S) = (cdr (assq x S))
;; and with that value in hand, so in rhs, then (car rhs) is the
;; rank and (cadr rhs) is the payload.  From there we can determine
;; if the payload signals that all variables are fresh using (var? payload).
;; Otherwise, we know that the payload is a non-variable.   Is it possible
;; that as we are unifying and lowering the ranks, we won't have to worry
;; about binding eigens?   Or do we still have to worry about them being
;; bound when we do =/=?

(define rhs
  (lambda (pr)
    (cdr pr)))

(define lhs
  (lambda (pr)
    (car pr)))

(define-syntax case-value
  (syntax-rules ()
    ((_ u ((t1) e0) ((at dt) e1) ((t2) e2))
     (let ((t u))
       (cond
	 ((var? t) (let ((t1 t)) e0))
	 ((pair? t) (let ((at (car t)) (dt (cdr t))) e1))
	 (else (let ((t2 t)) e2)))))))

(define var
  (lambda (dummy)
    (vector dummy)))

(define var?
  (lambda (x)
    (vector? x)))

(define walk
  (lambda (u S)
    (cond
      ((and (var? u) (assq u S)) =>
       (lambda (pr) (walk (rhs pr) S)))
      (else u))))

(define unify
  (lambda (u v S)
    (let ((u (walk u S))
          (v (walk v S)))
      (cond
        ((and (pair? u) (pair? v))
         (let ((S (unify (car u) (car v) S)))
           (and S
             (unify (cdr u) (cdr v) S))))
        (else (unify-nonpair u v S))))))

(define unify-nonpair
  (lambda (u v S)
    (cond
      ((eq? u v) S)
      ((var? u) (ext-S-check u v S))
      ((var? v) (ext-S-check v u S))
      ((equal? u v) S)
      (else #f))))

(define ext-S-check
  (lambda (x v S)
    (case-value v
      ((v) (ext-S x v S))
      ((au du) (cond
                 ((occurs-check x v S) #f)
                 (else (ext-S x v S))))
      ((v) (ext-S x v S)))))

(define ext-S
  (lambda (x v S)
    (cons `(,x . ,v) S)))

(define occurs-check
  (lambda (x v S)
    (case-value (walk v S)
      ((v) (eq? v x))
      ((av dv)
       (or (occurs-check x av S)
           (occurs-check x dv S)))
      ((v) #f))))

(define walk*
  (lambda (v S)
    (case-value (walk v S)
      ((v) v)
      ((av dv)
       (cons (walk* av S) (walk* dv S)))
      ((v) v))))

(define giant-walk
  (lambda (v s)
    (cond
      ((var? v) (unstar (walk-var v s)))
      (else v))))

(define giant-walk*
  (lambda (v s)
    (let ((v (giant-walk v s)))
      (cond
        ((var? v) v)
        ((pair? v) (cons (giant-walk* (car v) s) (giant-walk* (cdr v) s)))
        (else v)))))

(define apply-env*
  (lambda (env v)
    (cond
      ((var? v) (apply-env env v))
      ((pair? v) (cons (apply-env* env (car v)) (apply-env* env (cdr v))))
      (else v))))

(define apply-env
  (lambda (env x)
    (cdr (assq x env))))

(define reify-with-env
  (lambda (v env)
    (cond
      ((var? v) (cond
                  ((assq v env) env)
                  (else `((,v . ,(reify-name (length env))) . ,env))))
      ((pair? v) (reify-with-env (cdr v) (reify-with-env (car v) env)))
      (else env))))

(define reify-name
  (lambda (num)
    (let ((str_as_num (number->string num)))
      (string->symbol (string-append "_." str_as_num)))))

(define reify
  (lambda (x)
    (lambda (c)
      (let ((c (cycle c)))
        (let ((S (c->S c)))
          (let ((D (giant-walk* (c->D c) S))
                (Y (giant-walk* (c->Y c) S))
                (N (giant-walk* (c->N c) S))
                (Np (giant-walk* (c->Np c) S))
                (A (giant-walk* (c->A c) S))
                (v (giant-walk* x S)))
            (let ((R (reify-with-env v '())))
              (reify+
               v R c S D Y N Np A))))))))

(define reify+
  (lambda (v R c S D Y N Np A)
    (reify++ v R
      (D-subsumed
       (remp
          (lambda (d)
            (anyvar? (giant-walk* d S) R)) 
          (drop-from-D-using-A S
            (c->Y c) (c->N c)
	    (c->Np c) (c->A c)
            (switch-d-to-var-ass-via-unif D S))))
      (remp (lambda (y) (anyvar? y R))
        Y)
      (remp (lambda (n) (anyvar? n R))
        N)
      (remp (lambda (np) (anyvar? np R))
        Np)
      (remp (lambda (a) (anyvar? a R))
        A))))

(define reify++
  (lambda (v R D Y N Np A)
    (form (apply-env* R v)
          (walk* D R)
          (walk* Y R) 
          (walk* N R)
          (walk* Np R)
          (A-subsumed (walk* A R)))))

(define form
  (lambda (v D Y N Np A)
    (let ((fd (sort-D D))
          (fy (sorter Y))
          (fn (sorter N))
          (fnp (sorter Np))
          (fa (sorter A)))
      (let ((fd (if (null? fd) fd
                    (let ((fd (drop-dot-D fd)))
                      `((=/= . ,fd)))))
            (fy (if (null? fy) fy `((sym . ,fy))))
            (fn (if (null? fn) fn `((num . ,fn))))
            (fnp (if (null? fnp) fnp `((not-pair . ,fnp))))
            (fa (if (null? fa) fa
                    (let ((fa (drop-dot fa)))
                      `((absento . ,fa))))))
        (cond
          ((and (null? fd) (null? fy)
                (null? fn) (null? fnp)
                (null? fa))
           v)
          (else (append `(,v) fd fnp fn fy fa)))))))

(define lex<=?
  (lambda (x y)
    (cond
      ((vector? x) #t)
      ((vector? y) #f)
      ((port? x) #t)
      ((port? y) #f)
      ((procedure? x) #t)
      ((procedure? y) #f)
      ((boolean? x)
       (cond
         ((boolean? y) (or (not x) (eq? x y)))
         (else #t)))
      ((boolean? y) #f)
      ((null? x) #t)
      ((null? y) #f)
      ((char? x)
       (cond
         ((char? y) (char<=? x y))
         (else #t)))
      ((char? y) #f)
      ((number? x)
       (cond
         ((number? y) (<= x y))
         (else #t)))
      ((number? y) #f)
      ((string? x)
       (cond
         ((string? y) (string<=? x y))
         (else #t)))
      ((string? y) #f)
      ((symbol? x)
       (cond
         ((symbol? y)
          (string<=? (symbol->string x)
                     (symbol->string y)))
         (else #t)))
      ((symbol? y) #f)
      ((pair? x)
       (cond
         ((pair? y)
          (cond
            ((equal? (car x) (car y))
             (lex<=? (cdr x) (cdr y)))
            (else (lex<=? (car x) (car y)))))))
      ((pair? y) #f)
      (else #t))))

(define sorter
  (lambda (ls)
    (list-sort lex<=? ls)))

(define sort-D
  (lambda (D)
    (sorter
      (map sort-d D))))

(define sort-d
  (lambda (d)
    (list-sort
      (lambda (x y)
        (lex<=? (car x) (car y)))
      (map sort-pr d))))

(define drop-dot
  (lambda (X)
    (map (lambda (t)
           (let ((a (lhs t))
                 (d (rhs t)))
             `(,a ,d)))
         X)))

(define datum->string
  (lambda (x)
    (call-with-string-output-port
      (lambda (p) (display x p)))))

(define drop-dot-D
  (lambda (D)
    (map drop-dot D)))

(define lex<-reified-name?
  (lambda (r)
    (char<?
      (string-ref (datum->string r) 0)
      (string-ref "_" 0))))

(define sort-pr
  (lambda (pr)
    (let ((l (lhs pr))
          (r (rhs pr)))
      (cond
        ((lex<-reified-name? r) pr)
        ((lex<=? r l) `(,r . ,l))
        (else pr)))))

(define giant-unify-safes-pfx
  (letrec
    ((unify-rest
      (lambda (u v s pfx)
        (cond
          ((and (pair? u) (pair? v))
           (let ((s/pfx (giant-unify-safe/pfx (car u) (car v) s pfx)))
             (and s/pfx
               (let ((s (car s/pfx))
                     (pfx (cdr s/pfx)))
                 (giant-unify-safe/pfx (cdr u) (cdr v) s pfx)))))
          ((eqv? u v) `(,s . ,pfx))
          (else #f))))
     (var
      (lambda (dummy)
        (vector dummy)))
     (var?
      (lambda (x)
        (vector? x)))
     (var*?
      (lambda (x*)
        (var? (car x*))))
     (pair*?
      (lambda (x*)
        (pair? (car x*))))
     (append/map
      (lambda (value s)
        (letrec
            ((loop (lambda (x*)
                     (cond
                       ((null? x*) s)
                       (else `((,(car x*) . ,value) . ,(loop (cdr x*))))))))
          loop)))
     (ext-s_
      (lambda (x* nonvar s pfx)
        (let ((z* (cons nonvar x*)))
          (let ((s^ ((append/map z* s) x*))
                (pr `(,(car x*) . ,nonvar)))
            (let ((pfx^ `(,pr . ,pfx)))
              `(,s^ . ,pfx^))))))
     (ext-s*
      (lambda (x* y* s pfx)
        (let ((z* (append y* x*)))
          (let ((s^ ((append/map z* s) z*))
                (pr `(,(car x*) . ,(car y*))))
            (let ((pfx^ `(,pr . ,pfx)))
               `(,s^ . ,pfx^))))))
     (giant-unify-safe/pfx
      (lambda (u v s pfx)
      (cond
        ((var? u) (let ((u* (walk-var u s)))
                    (cond
                      ((var*? u*)
                       (cond
                         ((var? v) (let ((v* (walk-var v s)))
                                     (cond
                                       ((eq? u* v*) `(,s . ,pfx))
                                       ((var*? v*) (ext-s* u* v* s pfx))
                                       ((pair*? v*) (ext-s* u* v* s pfx)) 
                                       (else (ext-s* u* v* s pfx)))))
                         ((pair? v) (ext-s_ u* v s pfx))
                         (else (ext-s_ u* v s pfx))))
                      ((var? v)
                       (let ((v* (walk-var v s)))
                         (cond
                           ((var*? v*) (cond
                                         ((pair*? u*) (ext-s* v* u* s pfx))
                                         (else (ext-s* v* u* s pfx))))
                           (else (giant-unify-safe/pfx (unstar u*) (unstar v*) s pfx)))))
                      (else (unify-rest (unstar u*) v s pfx)))))
        ((var? v)
         (let ((v* (walk-var v s)))
           (cond
             ((var*? v*) (cond
                           ((pair? u) (ext-s_ v* u s pfx))
                           (else (ext-s_ v* u s pfx))))
             (else (unify-rest u (unstar v*) s pfx)))))
        (else (unify-rest u v s pfx))))))
    (lambda (u v s)
      (let ((s/pfx (giant-unify-safe/pfx u v s '())))
        (if s/pfx (cdr s/pfx) s/pfx)))))

(define switch-d-to-var-ass-via-unif
  (lambda (D S)
    (map (lambda (d)
           (let ((d-l (lhs d))
                 (d-r (rhs d)))
             (giant-unify-safes-pfx d-l d-r S)))
         D)))

(define anyvar?
  (lambda (u R)
    (case-value u
      ((u) (not (assq u R)))
      ((au du) (or (anyvar? au R)
                   (anyvar? du R)))
      ((u) #f))))

(define drop-from-D-using-A
  (lambda (S Y N Np A D)
    (remp (lambda (d)
	    (exists
	      (A-superfluous-pr? S Y N Np A)
	      d))
	  D)))

(define A-superfluous-pr?
  (lambda (S Y N Np A)
    (lambda (pr)
      (let ((pr-a (giant-walk (lhs pr) S))
            (pr-d (giant-walk (rhs pr) S)))
        (cond
          ((exists
             (lambda (a)
               (let ((a-a (giant-walk (lhs a) S))
                     (a-d (giant-walk (rhs a) S)))
                 (terms-pairwise=?
                   pr-a pr-d a-a a-d S)))
             A)
           (for-all
             (stays-in-A? S Y N Np pr-a pr-d)
             A))
          (else #f))))))

(define stays-in-A?
  (lambda (S Y N Np pr-a pr-d)
    (lambda (a)
      (let ((a-a (giant-walk (lhs a) S))
            (a-d (giant-walk (rhs a) S)))
        (or
          (not
            (terms-pairwise=?
              pr-a pr-d a-a a-d S))
          (untyped-var? S Y N Np a-d)
          (pair? a-d))))))

(define terms-pairwise=?
  (lambda (pr-a pr-d t-a t-d S)
    (or (and (term=? pr-a t-a S)
             (term=? pr-d t-d S))
        (and (term=? pr-a t-d S)
             (term=? pr-d t-a S)))))

(define D-subsumed
  (lambda (D)
    (let D-subsumed ((D D) (D0 '()))
      (cond
        ((null? D) D0)
        ((or (D-subsumed? (car D) (cdr D))
             (D-subsumed? (car D) D0))
         (D-subsumed (cdr D) D0))
        (else (D-subsumed (cdr D)
                (cons (car D) D0)))))))

(define D-subsumed?
  (lambda (d D0)
    (cond
      ((null? D0) #f)
      (else
       (let ((d^ (unify* (car D0) d)))
         (or (and d^ (eq? d^ d))
             (D-subsumed? d (cdr D0))))))))

(define unify*
  (lambda (d S)
    (unify (map lhs d) (map rhs d) S)))

(define A-subsumed
  (lambda (A)
    (let A-subsumed ((A A) (A0 '()))
      (cond
        ((null? A) A0)
        (else
         (let ((l (lhs (car A)))
               (r (rhs (car A))))
           (cond
             ((or
                (A-subsumed? l r (cdr A))
                (A-subsumed? l r A0))
              (A-subsumed (cdr A) A0))
             (else
              (A-subsumed (cdr A)
                (cons (car A) A0))))))))))

(define A-subsumed?
  (lambda (l r A)
    (cond
      ((null? A) #f)
      (else
       (let ((l^ (lhs (car A)))
             (r^ (rhs (car A))))
         (or
           (and (eq? r r^) (member* l^ l))
           (A-subsumed? l r (cdr A))))))))

(define member*
  (lambda (x u)
    (cond
      ((eq? x u) #t)
      ((pair? u)
       (or (member* x (car u))
           (member* x (cdr u))))
      (else #f))))

(define-syntax lambdag@
  (syntax-rules (:)
    ((_ (c) e) (lambda (c) e))
    ((_ (c : S D Y N Np A) e)
     (lambda (c)
       (let ((S (c->S c)) (D (c->D c))
             (Y (c->Y c)) (N (c->N c))
             (Np (c->Np c)) (A (c->A c)))
         e)))))

(define-syntax lambdaf@
  (syntax-rules ()
    ((_ () e) (lambda () e))))

(define mzero (lambda () #f))
(define unit (lambdag@ (c) c))
(define choice (lambda (c f) (cons c f)))
(define-syntax inc
  (syntax-rules ()
    ((_ e) (lambdaf@ () e))))
(define empty-f (lambdaf@ () (mzero)))

(define State
  (lambda (S D Y N Np A)
    `(,S ,D ,Y ,N ,Np ,A)))

(define empty-c '(() () () () () ()))

(define-syntax case-inf
  (syntax-rules ()
    ((_ e (() e0) ((f^) e1) ((c^) e2) ((c f) e3))
     (let ((c-inf e))
       (cond
         ((not c-inf) e0)
         ((procedure? c-inf)  (let ((f^ c-inf)) e1))
         ((not (and (pair? c-inf)
                 (procedure? (cdr c-inf))))
          (let ((c^ c-inf)) e2))
         (else (let ((c (car c-inf)) (f (cdr c-inf)))
                 e3)))))))

(define make-fresh-association
  (lambda (t)
    `(,t . (,t))))

(define-syntax fresh
  (syntax-rules ()
    ((_ (x ...) g0 g* ...)
     (lambdag@ (c : S D Y N Np A)
       (inc
         (let ((x (var 'x)) ...)
           (let ((x* `(,x ...)))
             (let ((S (append (map make-fresh-association x*) S)))
               (let ((c (State S D Y N Np A)))
                 (bind* (g0 c) g* ...))))))))))

(define bind
  (lambda (c-inf g)
    (case-inf c-inf
      (() (mzero))
      ((f) (inc (bind (f) g)))
      ((c) (g c))
      ((c f) (mplus (g c) (lambdaf@ () (bind (f) g)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;
(define STREAM 'hukarz)
(define set-stream!
  (lambda (x)
    (set! STREAM x)))
(define get-stream
  (lambda ()
    STREAM))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-syntax run
  (syntax-rules ()
    ((_ n (x) g0 g ...)
     (take n
       (lambdaf@ ()
         ((fresh (x) g0 g ...
            (lambdag@ (final-c)
              (let ((z ((reify x) final-c)))
                (choice z empty-f))))
          empty-c))))))

(define-syntax run*
  (syntax-rules ()
    ((_ (x) g ...) (run #f (x) g ...))))

(define take
  (lambda (n f)
    (cond
      ((and n (zero? n)) '())
      (else
       (let ((f (f)))        ;; my modifications: saving off the stream
         (set-stream!  f)
         (case-inf f
           (() '())
           ((f) (take n f))
           ((c) (cons c '()))
           ((c f) (cons c
                        (take (and n (- n 1)) f)))))))))

(define-syntax conde
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (c)
       (inc
         (mplus*
           (bind* (g0 c) g ...)
           (bind* (g1 c) g^ ...) ...))))))

(define-syntax mplus*
  (syntax-rules ()
    ((_ e) e)
    ((_ e0 e ...) (mplus e0
                    (lambdaf@ () (mplus* e ...))))))

(define mplus
  (lambda (c-inf f)
    (case-inf c-inf
      (() (f))
      ((f^) (inc (mplus (f) f^)))
      ((c) (choice c f))
      ((c f^) (choice c (lambdaf@ () (mplus (f) f^)))))))

(define-syntax bind*
  (syntax-rules ()
    ((_ e) e)
    ((_ e g0 g ...) (bind* (bind e g0) g ...))))

(define c->S (lambda (c) (car c)))
(define c->D (lambda (c) (cadr c)))
(define c->Y (lambda (c) (caddr c)))
(define c->N (lambda (c) (cadddr c)))
(define c->Np (lambda (c) (cadddr (cdr c))))
(define c->A (lambda (c) (cadddr (cddr c))))

(define absento
  (lambda (u v)
    (lambdag@ (c : S D Y N Np A)
      (cond
        ((mem-check u v S) (mzero))
        (else
         (unit (State S D Y N Np `((,u . ,v) . ,A))))))))

(define mem-check
  (lambda (u t S)
    (let ((t (giant-walk t S)))
      (cond
        ((pair? t)
         (or (term=? u t S)
             (mem-check u (car t) S)
             (mem-check u (cdr t) S)))
        (else (term=? u t S))))))

(define term=?
  (lambda (u v S)
    (let ((u (giant-walk u S))
          (v (giant-walk v S)))
      (cond
        ((and (pair? u) (pair? v))
         (and (term=? (car u) (car v) S)
              (term=? (cdr u) (cdr v) S)))
        (else (term=?-nonpair u v S))))))

(define term=?-nonpair
  (lambda (u v S)
    (cond
      ((eq? u v) #t)
      ((var? u) #f)
      ((var? v) #f)
      ((equal? u v) #t)
      (else #f))))

(define ground-non-type?
  (lambda (pred)
    (lambda (u S)
      (let ((u (giant-walk u S)))
        (cond
          ((var? u) #f)
          (else (not (pred u))))))))

(define ground-non-symbol?
  (ground-non-type? symbol?))

(define ground-non-number?
  (ground-non-type? number?))

(define not-pair? (lambda (x) (not (pair? x))))

(define ground-pair?
  (ground-non-type? not-pair?))

(define symbolo
  (lambda (u)
    (lambdag@ (c : S D Y N Np A)
      (cond
        ((ground-non-symbol? u S) (mzero))
        ((mem-check u N S) (mzero))
        (else (unit (State S D `(,u . ,Y) N Np A)))))))

(define numbero
  (lambda (u)
    (lambdag@ (c : S D Y N Np A)
      (cond
        ((ground-non-number? u S) (mzero))
        ((mem-check u Y S) (mzero))
        (else (unit (State S D Y `(,u . ,N) Np A)))))))

(define not-pairo
  (lambda (u)
    (lambdag@ (c : S D Y N Np A)
      (cond
        ((ground-pair? u S) (mzero))
        (else (unit (State S D Y N `(,u . ,Np) A)))))))

(define =/=
  (lambda (u v)
    (lambdag@ (c : S D Y N Np A)
      (cond
        ((giant-unify u v S) =>
         (lambda (S0)
           (cond
             ((eq? S0 S) (mzero))
             (else
              (let ((d `(,u . ,v)))
                (unit
                  (State S `(,d . ,D) Y N Np A)))))))
        (else c)))))

;; (define assq-found (hasheq))
;; (define assq-missing (hasheq))

;; (define (assq-instrumented v l)
;;   (let loop ([l l] [n 0])
;;     (cond 
;;       [(null? l)
;;        (set! assq-missing (hash-set assq-missing n (add1 (hash-ref assq-missing n 0))))]
;;       [(eq? (caar l) v)
;;        (set! assq-found (hash-set assq-found n (add1 (hash-ref assq-found n 0))))
;;        (car l)]
;;       [else (loop (cdr l) (add1 n))])))

;; (require racket/pretty)
;; (executable-yield-handler
;;  (λ _ 
;;    (displayln 'found-in-assq)
;;    (pretty-print assq-found)
;;    (displayln 'not-found-in-assq)
;;    (pretty-print assq-missing)))

(define walk-var ;;; x is a variable.
  (lambda (x s)
    (cdr (assq x s))))

(define unstar  ;;; should only be used on a chain that ends in a nonvar.
  (lambda (x*)
    (car x*)))

(define giant-unify
  (letrec
    ((unify-rest ;;; eventually, this will be inlined for efficiency.
      (lambda (u v s)
        (cond
          ((and (pair? u) (pair? v))
           (let ((s (giant-unify (car u) (car v) s)))
             (and s (giant-unify (cdr u) (cdr v) s))))
          ((eqv? u v) s)
          (else #f))))
     (var*?
      (lambda (x*)
        (var? (car x*))))
     (pair*?
      (lambda (x*)
        (pair? (car x*))))
     (append/map
      (lambda (value s)
        (letrec
            ((loop (lambda (x*)
                     (cond
                       ((null? x*) s)
                       (else `((,(car x*) . ,value) . ,(loop (cdr x*))))))))
          loop)))
     (ext-s_
      (lambda (x* nonvar s)
        (let ((z* (cons nonvar x*)))
          ((append/map z* s) x*))))
     (ext-s*
      (lambda (x* y* s)
        (let ((z* (append y* x*)))
          ((append/map z* s) z*))))
     (occurs-check
      (lambda (x* u s)
        (cond
          ((var? u) (let ((u* (walk-var u s)))
                      (cond
                        ((var*? u*) (eq? u* x*))
                        (else (occurs-check x* (unstar u*) s)))))
          ((pair? u)
           (or (occurs-check x* (car u) s) (occurs-check x* (cdr u) s)))
          (else #f)))))
    (lambda (u v s)
      (cond
        ((var? u) (let ((u* (walk-var u s)))
                    (cond
                      ((var*? u*)
                       (cond
                         ((var? v) (let ((v* (walk-var v s)))
                                     (cond
                                       ((eq? u* v*) s)
                                       ((var*? v*) (ext-s* u* v* s))
                                       ((pair*? v*) 
                                        (cond
                                          ((occurs-check u* (unstar v*) s) #f)
                                          (else (ext-s* u* v* s)))) 
                                       (else (ext-s* u* v* s)))))
                         ((pair? v)
                          (cond
                            ((occurs-check u* v s) #f)
                            (else (ext-s_ u* v s))))
                         (else (ext-s_ u* v s))))
                      ((var? v)
                       (let ((v* (walk-var v s)))
                         (cond
                           ((var*? v*) (cond
                                         ((pair*? u*)
                                          (cond
                                            ((occurs-check v* (unstar u*) s) #f)
                                            (else (ext-s* v* u* s))))
                                         (else (ext-s* v* u* s))))
                           (else (giant-unify (unstar u*) (unstar v*) s)))))
                      (else (unify-rest (unstar u*) v s)))))
        ((var? v)
         (let ((v* (walk-var v s)))
           (cond
             ((var*? v*) (cond
                           ((pair? u)
                            (cond
                              ((occurs-check v* u s) #f)
                              (else (ext-s_ v* u s))))
                           (else (ext-s_ v* u s))))
             (else (unify-rest u (unstar v*) s)))))
        (else (unify-rest u v s))))))

(define ==
  (lambda (u v)
    (lambdag@ (c : S D Y N Np A)
      (cond
        ((giant-unify u v S) =>
         (lambda (S0)
           (cond
             ((eq? S0 S) (unit c))
             (else
              (cond
                ((==fail-check S0 D Y N Np A)
                 (mzero))
                (else
                 (unit (State S0 D Y N Np A))))))))
        (else (mzero))))))

(define ==fail-check
  (lambda (S0 D Y N Np A)
    (or (atomic-fail-check S0 Y ground-non-symbol?)
        (atomic-fail-check S0 N ground-non-number?)
        (atomic-fail-check S0 Np ground-pair?)
        (symbolo-numbero-fail-check S0 Y N)
        (=/=-fail-check S0 D)
        (absento-fail-check S0 A))))

(define atomic-fail-check
  (lambda (S Np pred)
    (exists
      (lambda (np)
        (pred (giant-walk np S) S))
      Np)))

(define symbolo-numbero-fail-check
  (lambda (S Y N)
    (let ((N (map (lambda (n) (giant-walk n S)) N)))
      (exists
        (lambda (y)
          (exists (same-var? (giant-walk y S)) N))
        Y))))

(define absento-fail-check
  (lambda (S A)
    (exists
      (lambda (a) (mem-check (lhs a) (rhs a) S))
      A)))

(define =/=-fail-check
  (lambda (S D)
    (exists
      (lambda (d) (term=? (lhs d) (rhs d) S))
      D)))

(define tagged?
  (lambda (S Y y^)
    (exists (lambda (y) (eqv? (giant-walk y S) y^)) Y)))

(define untyped-var?
  (lambda (S Y N Np t)
    (let ((in-type? (lambda (y)
                      (eq? (giant-walk y S) t))))
      (and (var? t)
           (not (exists in-type? Y))
           (not (exists in-type? N))
           (not (exists in-type? Np))))))

(define const?
  (lambda (S)
    (lambda (a)
      (not (var? (giant-walk a S))))))

(define drop-from-N-b/c-const
  (lambdag@ (c : S D Y N Np A)
    (cond
      ((find (const? S) N) =>
       (lambda (n)
         (State S D Y (remq1 n N) Np A)))
      (else c))))

(define drop-from-Y-b/c-const
  (lambdag@ (c : S D Y N Np A)
    (cond
      ((find (const? S) Y) =>
       (lambda (y)
         (State S D (remq1 y Y) N Np A)))
      (else c))))

(define drop-from-Np-b/c-const
  (lambdag@ (c : S D Y N Np A)
    (cond
      ((find (const? S) Np) =>
       (lambda (np)
         (State S D Y N (remq1 np Np) A)))
      ((memp (lambda (x) (not (giant-walk x S))) Np) =>
       (lambda (np*)
         (State S D Y N (remq1 (car np*) Np) A)))
      (else c))))

(define remq1
  (lambda (elem ls)
    (cond
      ((null? ls) '())
      ((eq? (car ls) elem) (cdr ls))
      (else (cons (car ls)
              (remq1 elem (cdr ls)))))))

(define same-var?
  (lambda (v)
    (lambda (v^)
      (and (var? v) (var? v^) (eq? v v^)))))

(define find-dup
  (lambda (f S)
    (lambda (set)
      (let loop ((set set))
        (cond
          ((null? set) #f)
          (else
           (let ((e (car set)))
             (let ((e0 (giant-walk e S)))
               (cond
                 ((find (lambda (e1)
                          ((f e0) (giant-walk e1 S)))
                    (cdr set))
                  e)
                 (else
                  (loop (cdr set))))))))))))

(define drop-from-N-b/c-dup-var
  (lambdag@ (c : S D Y N Np A)
    (cond
      (((find-dup same-var? S) N) =>
       (lambda (n)
         (State S D Y (remq1 n N) Np A)))
      (else c))))

(define drop-from-Y-b/c-dup-var
  (lambdag@ (c : S D Y N Np A)
    (cond
      (((find-dup same-var? S) Y) =>
       (lambda (y)
         (State S D (remq1 y Y) N Np A)))
      (else c))))

(define drop-from-Np-b/c-dup-var
  (lambdag@ (c : S D Y N Np A)
    (cond
      (((find-dup same-var? S) Np) =>
       (lambda (np)
         (State S D Y N (remq1 np Np) A)))
      (else c))))

(define drop-var-from-Np-b/c-Y
  (lambdag@ (c : S D Y N Np A)
    (let ((Y (map (lambda (y) (giant-walk y S)) Y)))
      (cond
        ((find (lambda (np)
                 (exists (same-var? (giant-walk np S)) Y))
               Np) =>
               (lambda (np)
                 (State S D Y N (remq1 np Np) A)))
        (else c)))))

(define drop-var-from-Np-b/c-N
  (lambdag@ (c : S D Y N Np A)
    (let ((N (map (lambda (n) (giant-walk n S)) N)))
      (cond
        ((find (lambda (np)
                 (exists (same-var? (giant-walk np S)) N))
               Np) =>
               (lambda (np)
                 (State S D Y N (remq1 np Np) A)))
        (else c)))))

(define var-type-mismatch?
  (lambda (S Y N Np t1 t2)
    (cond
      ((num? S N t1)
       (not (num? S N t2)))
      ((sym? S Y t1)
       (not (sym? S Y t2)))
      ((not-pr? S Np t1)
       (not (not (pair? t2))))
      (else #f))))

(define term-ununifiable?
  (lambda (S Y N Np t1 t2)
    (let ((t1 (giant-walk t1 S))
          (t2 (giant-walk t2 S)))
      (cond
        ((or (untyped-var? S Y N Np t1)
             (untyped-var? S Y N Np t2)) #f)
        ((var? t1)
         (var-type-mismatch? S Y N Np t1 t2))
        ((var? t2)
         (var-type-mismatch? S Y N Np t2 t1))
        ((and (pair? t1) (pair? t2))
         (or (term-ununifiable? S Y N Np
               (car t1) (car t2))
             (term-ununifiable? S Y N Np
               (cdr t1) (cdr t2))))
        (else (not (eqv? t1 t2)))))))

(define num?
  (lambda (S N n)
    (let ((n (giant-walk n S)))
      (cond
        ((var? n) (tagged? S N n))
        (else (number? n))))))

(define sym?
  (lambda (S Y y)
    (let ((y (giant-walk y S)))
      (cond
        ((var? y) (tagged? S Y y))
        (else (symbol? y))))))

(define not-pr?
  (lambda (S Np np)
    (let ((np (giant-walk np S)))
      (cond
        ((var? np) (tagged? S Np np))
        (else (not-pair? np))))))

;; Not used code, but sitting in here. Why? Why did we think it was needed? 
;; (define drop-from-D-b/c-d1-occurs-d2
;;   (lambdag@ (c : S D Y N Np A)
;;     (cond
;;       ((find (lambda (d)
;;                (tree-occurs-check (lhs d) (rhs d) S))
;;          D) => (lambda (d)
;;                  (State S (remq1 d D) Y N Np A)))
;;       (else c))))

;; here
(define split-a-move-to-D-b/c-pair
  (lambdag@ (c : S D Y N Np A)
    (cond
      ((exists
         (lambda (a)
           (let ((tr (giant-walk (rhs a) S)))
             (cond
               ((pair? tr)
                ((split-a-move-to-D tr a) c))
               (else #f))))
         A))
      (else c))))

(define split-a-move-to-D
  (lambda (tr a)
    (lambdag@ (c : S D Y N Np A)
      (let ((tl (giant-walk (lhs a) S))
            (tr-a (car tr))
            (tr-d (cdr tr)))
        (let ((t1 `(,tl . ,tr-a))
              (t2 `(,tl . ,tr-d))
              (A (remq1 a A)))
          (let ((A `(,t1 . (,t2 . ,A))))
            (cond
              ((giant-unify tl tr S) =>
               (lambda (S0)
                 (cond
                   ((eq? S0 S)
                    (State S D Y N Np A))
                   (else
                     (let ((D `(,a . ,D)))
                       (State S D Y N Np A))))))
              (else (State S D Y N Np A)))))))))

;; this is the one pulled from giant
;; dead code for the moment, check helpers
(define giant-occurs-check
  (lambda (x* u s)
    (cond
      ((var? u) (let ((u* (walk-var u s)))
                  (cond
                    ((var*? u*) (eq? u* x*))
                    (else (giant-occurs-check x* (unstar u*) s)))))
      ((pair? u)
       (or (giant-occurs-check x* (car u) s) (giant-occurs-check x* (cdr u) s)))
      (else #f))))

(define tree-occurs-check
  (lambda (d-a d-b S)
    (let ((d-a (giant-walk d-a S)) ;; here there be dragons
          (d-b (giant-walk d-b S)))
      (cond
        ((var? d-a)
         (giant-occurs-check d-a d-b S))
        ((var? d-b)
         (giant-occurs-check d-b d-a S))
        ((and (pair? d-a) (pair? d-b))
         (or
           (tree-occurs-check (car d-a) (car d-b) S)
           (tree-occurs-check (cdr d-a) (cdr d-b) S)))
        (else #f)))))

(define move-from-A-to-D-b/c-a2-Np
  (lambdag@ (c : S D Y N Np A)
    (cond
      ((exists
         (lambda (a)
           (let ((a2 (rhs a)))
             ((movable-a? (giant-walk a2 S) a2 a) c)))
         A))
      (else c))))

(define movable-a?
  (lambda (a2^ a2 a)
    (lambdag@ (c : S D Y N Np A)
      (cond
        ((and
           (not (untyped-var? S Y N Np a2^))
           (not (pair? a2^)))
           (let ((A (remq1 a A)))
             (cond
               ((giant-unify (lhs a) a2 S) =>
                (lambda (S0)
                  (cond
                    ((eq? S0 S)
                     (State S D Y N Np A))
                    (else
                     (let ((D `(,a . ,D)))
                       (State S D Y N Np A))))))
               (else (State S D Y N Np A)))))
        (else #f)))))

(define drop-from-D-b/c-Y-or-N-or-Np
  (lambdag@ (c : S D Y N Np A)
    (cond
      ((find (lambda (d)
               (term-ununifiable?
                 S Y N Np (lhs d) (rhs d)))
        D) =>
       (lambda (d)
         (State S (remq1 d D) Y N Np A)))
      (else c))))

(define drop-from-A-b/c-a2-occurs-a1
  (lambdag@ (c : S D Y N Np A)
    (cond
      ((find (lambda (a)
               (let ((a-a (giant-walk (lhs a) S))
                     (a-d (giant-walk (rhs a) S)))
                 (mem-check a-d a-a S)))
         A)
       => (lambda (a)
            (State S D Y N Np (remq1 a A))))
      (else c))))

(define LOF
  (list drop-from-Y-b/c-const
        drop-from-N-b/c-const
        drop-from-Np-b/c-const
        drop-var-from-Np-b/c-Y
        drop-var-from-Np-b/c-N
        drop-from-Y-b/c-dup-var
        drop-from-N-b/c-dup-var
        drop-from-Np-b/c-dup-var
        drop-from-D-b/c-Y-or-N-or-Np
        drop-from-A-b/c-a2-occurs-a1
        move-from-A-to-D-b/c-a2-Np
        split-a-move-to-D-b/c-pair
        ))

(define len-LOF (length LOF))

(define cycler
  (lambda (c n fns)
    (cond
      ((zero? n) c)
      ((null? fns) (cycler c len-LOF LOF))
      (else
       (let ((c^ ((car fns) c)))
         (cond
           ((not (eq? c^ c))
            (cycler c^ len-LOF (cdr fns)))
           (else
            (cycler c (- n 1) (cdr fns)))))))))

(define cycle
  (lambdag@ (c)
    (cycler c len-LOF LOF)))

(define-syntax conda
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (c)
       (inc
         (ifa ((g0 c) g ...)
              ((g1 c) g^ ...) ...))))))

(define-syntax ifa
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((c-inf e))
       (case-inf c-inf
         (() (ifa b ...))
         ((f) (inc (loop (f))))
         ((a) (bind* c-inf g ...))
         ((a f) (bind* c-inf g ...)))))))

(define-syntax condu
  (syntax-rules ()
    ((_ (g0 g ...) (g1 g^ ...) ...)
     (lambdag@ (c)
       (inc
         (ifu ((g0 c) g ...)
              ((g1 c) g^ ...) ...))))))

(define-syntax ifu
  (syntax-rules ()
    ((_) (mzero))
    ((_ (e g ...) b ...)
     (let loop ((c-inf e))
       (case-inf c-inf
         (() (ifu b ...))
         ((f) (inc (loop (f))))
         ((c) (bind* c-inf g ...))
         ((c f) (bind* (unit c) g ...)))))))

(define succeed (== #f #f))

(define fail (== #f #t))

(define-syntax project
  (syntax-rules ()
    ((_ (x ...) g g* ...)
     (lambdag@ (c : S D Y N Np A)
       (let ((x (walk* x S)) ...)
         ((fresh () g g* ...) c))))))

(define booleano
  (lambda (x)
    (conde
      ((== #f x))
      ((== #t x)))))

(define onceo
  (lambda (g)
    (condu
      (g))))

(define prt
  (lambda args
    (lambdag@ (c)
      (begin
        (for-each
          (lambda (msg)
            (display msg)
            (newline))
          args)
        (pretty-print c)
        c))))

