#lang racket
(provide conj disj == call/fresh reify-1st call/empty-state var =/=) ;; <- yuk!

;; We introduce a simple abstraction for variables.
;; Variables are numbers.
(define (var x) (vector x))
(define (var? x) (vector? x))

;; At an abstract level, our programs proceed by mandating things be
;; the same. This manifests as a list of things to which variables are
;; bound -- including other variables.

;; (define empty-s '())
(define (ext-s x v s)
  (cond
    ((occurs? x v s) #f)
    (else `((,x . ,v) . ,s))))

(define occurs?
  (lambda (x v s)
    (let ((v (walk v s)))
      (cond
        ((var? v) (eq? x v))
        ((pair? v) (or (occurs? x (car v) s)
                       (occurs? x (cdr v) s)))
        (else #f)))))

;; > (ext-s 3 4 (ext-s 4 5 empty-s))
;; ((3 . 4) (4 . 5))

;; We can find the meaning of a variable by /walking/ it in the
;; substitution. Say, I've seen this function before, haven't I?

(define (walk u s)
  (let ((pr (and (var? u) (assq u s))))
    (if pr (walk (cdr pr) s) u)))

;; > (walk 4 '((5 . 3) (4 . 5)))
;; 3

;; We used it to implement the real driver of the system, unify. When
;; we unify two terms, we embiggen the substitution with that
;; information. If they're already the same, there's no change. If
;; they can't be made the same, we return #f.

;; Let's /walk/ through this slowly. *Ba-dam. Tish*

(define (unify u v s)
  (let ((u (walk u s)) (v (walk v s)))
    (cond
      ((and (var? u) (var? v) (eq? u v)) s)
      ((var? u) (ext-s u v s))
      ((var? v) (ext-s v u s))
      ((and (not (var? u)) (not (var? v)) (eqv? u v)) s)
      (else
       (and (pair? u) (pair? v)
            (let ((s (unify (car u) (car v) s)))
              (and s (unify (cdr u) (cdr v) s))))))))

;; In miniKanren, we return a /stream/ of answers. If there are none,
;; we return the empty-stream. If our unify succeeds, we want to
;; return a list of one answer.

(define mzero '())
;;(define (unit s) (cons s mzero))

;; == is a /goal constructor/. It takes two terms u and v, and returns
;; a /goal/. A goal is a function which takes a state and returns a
;; stream.

;; Here, we unify those two terms in the original state, and produce a
;; new one (or #f). If we have a non-#f state, we return the /unit
;; stream/ of that state. Otherwise, we return the empty stream.

;; (define (== u v)
;;   (lambda (s)
;;     (let ((s (unify u v s)))
;;       (if s (unit s) mzero))))

;; We need a way to introduce new variables. We'll use
;; functions. call/fresh, like call/cc takes a function and passes it
;; a fresh variable, the way call/cc passes the current continuation.

;; call/fresh is a goal constructor. It returns a goal. f is a
;; function of /type/ var -> goal. It takes a var and returns a
;; goal. And goals are the sorts of things which take a state and
;; return a stream.

;; (define (call/fresh f)
;;   (lambda (s)
;;     ((f c) s)))

;; We want c to be a /fresh/ variable. A brand, spankin' new
;; one. Since our variables are numbers it needs to be an unused
;; number. We can just keep track as we go around of the next
;; available number. This'll require re-jimmying with the state just a
;; hare.

(define empty-state '(() () . 0))

;; It's now empty-state for /state/ not substitution. 

(define (call/fresh f)
  (lambda (s/d/c)
    (let ((c (cddr s/d/c)))
      ((f (var c)) `(,(car s/d/c) ,(cadr s/d/c) . ,(+ c 1))))))

(define (== u v)
  (lambda (s/d/c)
    (let ((s (unify u v (car s/d/c))))
      (cond
        (s (cond
             ((ormap (lambda (pr) (eq? s (unify (car pr) (cdr pr) s))) (cadr s/d/c)) mzero)
             (else (unit `(,s . ,(cdr s/d/c))))))
        (else mzero)))))

(define (=/= u v)
  (lambda (s/d/c)
    (let ((s (car s/d/c)))
      (let ((s^ (unify u v s)))
        (cond
          (s^ (cond
                ((eq? s s^) mzero)
                (else (unit `(,s ((,u . ,v) . ,(cadr s/d/c)) . ,(cddr s/d/c))))))
          (else (unit s/d/c)))))))

(define (unit s/d/c) (cons s/d/c mzero))

;; So now we have the ability to introduce variables, unify terms, and
;; extend the substitution, and put things together and see the
;; substituion we get back.

;; > ((call/fresh
;;      (lambda (x)
;;        (call/fresh
;;          (lambda (y)
;;            (== `(cat dog ,x turtle) `(cat dog rabbit ,y))))))
;;    empty-state)
;; ((((1 . turtle) (0 . rabbit)) . 2))

;; disj is the goal constructor which provides a form of disjunction.
;; It takes two goals as arguments, and returns a goal which, when
;; given a state, returns a stream which results from combining the
;; streams from running that state on the first and on the second.

(define (disj g1 g2) (lambda (s/d/c) (mplus (g1 s/d/c) (g2 s/d/c))))

;; The streams are combined through mplus. Can anyone think of another
;; name for mplus?

;; (define (mplus $1 $2)
;;   (cond
;;     ((null? $1) $2)
;;     (else (cons (car $1) (mplus (cdr $1) $2)))))

;; conj is a goal constructor which provides for a form of
;; conjunction.  It takes two goals as arguments, and returns a goal
;; for which the state is run on the first goal, and the resulting
;; stream and the second goal are passed to bind.

(define (conj g1 g2) (lambda (s/d/c) (bind (g1 s/d/c) g2)))

;; Can anyone think of a different name for bind? (Hint: reverse the
;; order of arguments in your head) 

;; (define (bind $ g)
;;   (cond
;;     ((null? $) mzero)
;;     (else (mplus (g (car $)) (bind (cdr $) g)))))

;; Now, we can build relations in Racket, and use them in microKanren.

;; > (define cat-or-dog
;;     (lambda (animal)
;;       (disj
;;        (== animal 'cat)
;;        (== animal 'dog))))
;; > ((call/fresh cat-or-dog) empty-state)
;; ((((0 . cat)) . 1) (((0 . dog)) . 1))

;; But when I said streams here, well, we've kinda got a problem.

;; (define hot-dogs
;;   (lambda (dish)
;;     (disj
;;      (== dish 'dog)
;;      (call/fresh
;;       (lambda (res)
;;         (conj
;;          (== dish `(hot . ,res))
;;          (hot-dogs res)))))))

;; So what's up here. Well, let's see what's happening. There are
;; infinitely many answers. Infinite recursions. That doesn't end well,
;; generally. But, according to a "Law of Dan", infinity's only a problem
;; if you try to print it. If you want 3 answers out of an infinite many,
;; well, we should be able to get'em.

;; Consider, currently, our answer streams are represented by the
;; empty list, or a state consed onto a stream.

;; So, we'll take the recursive call, and at first eta-expand it. 

;; (lambda (s/d/c)
;;   ((hot-dogs res) s/d/c))

;; Still no solution. But we do know a way to prevent invocation of recursive calls. 

;; (lambda (s/d/c)
;;   (lambda ()    
;;     ((hot-dogs res) s/d/c)))

;; We call that an inverse-eta delay. Since a goal takes a state and
;; returns a stream, that must mean that the thunk is a stream.
;; So, streams are now mt | state x stream | () -> stream

;; And we need to be able to combine them in mplus and bind.

;; (define (mplus $1 $2)
;;   (cond
;;     ((procedure? $1) (lambda () (mplus ($1) $2)))
;;     ((null? $1) $2)
;;     (else (cons (car $1) (mplus (cdr $1) $2)))))

;; (define (bind $ g)
;;   (cond
;;     ((procedure? $) (lambda () (bind ($) g)))
;;     ((null? $) mzero)
;;     (else (mplus (g (car $)) (bind (cdr $) g)))))

;; And with this, we can run hot-dogs and get answers.
;; > (define hot-dogs
;;     (lambda (dish)
;;       (disj
;;        (== dish 'dog)
;;        (call/fresh
;;         (lambda (res)
;;           (conj
;;            (== dish `(hot . ,res))
;;            (lambda (s/d/c)
;;              (lambda ()
;;                ((hot-dogs res) s/d/c)))))))))
;; > ((call/fresh hot-dogs) empty-state)
;; ((((0 . dog)) . 1) . #<procedure:...ro-internals.rkt:196:21>)
;; > ((cdr ((call/fresh hot-dogs) empty-state)))
;; ((((1 . dog) (0 hot . 1)) . 2) . #<procedure:...ro-internals.rkt:196:21>)
;; > ((cdr ((cdr ((call/fresh hot-dogs) empty-state)))))
;; ((((2 . dog) (1 hot . 2) (0 hot . 1)) . 3)
;;  .
;;  #<procedure:...ro-internals.rkt:196:21>)

;; (define meals
;;   (lambda (meal)
;;     (disj
;;      (hot-dogs meal)
;;      (== meal 'hamburger))))

;; But we don't have a complete search. Who can eat that many hot dogs?

(define (mplus $1 $2)
  (cond
    ((procedure? $1) (lambda () (mplus $2 ($1))))
    ((null? $1) $2)
    (else (cons (car $1) (mplus (cdr $1) $2)))))

(define (bind $ g)
  (cond
    ((procedure? $) (lambda () (bind ($) g)))
    ((null? $) mzero)
    (else (mplus (g (car $)) (bind (cdr $) g)))))

;; Now we can get some of each.

;; And voila. We're done. So, just what have we wrought?

;; Appendo.
;; (define appendo
;;   (lambda (l s out)
;;     (disj
;;      (conj (== '() l) (== s out))
;;      (call/fresh
;;       (lambda (a)
;;         (call/fresh
;;          (lambda (d)
;;            (conj
;;             (== `(,a . ,d) l)
;;             (call/fresh
;;              (lambda (res)
;;                (conj
;;                 (== `(,a . ,res) out)
;;                 (lambda (s/d/c)
;;                   (lambda ()
;;                     ((appendo d s res) s/d/c))))))))))))))

;; ;; Call appendo.
;; (define call-appendo
;;   (call/fresh
;;    (lambda (q)
;;      (call/fresh
;;       (lambda (l)
;;         (call/fresh
;;          (lambda (s)
;;            (call/fresh
;;             (lambda (out)
;;               (conj
;;                (appendo l s out)
;;                (== `(,l ,s ,out) q)))))))))))
;; Wowza.
;; > (call/empty-state call-appendo)
;; ((((0 1 2 3) (2 . 3) (1)) . 4) . #<procedure:...ro-internals.rkt:241:20>)
;; > ((cdr (call/empty-state call-appendo)))
;; ((((0 1 2 3) (2 . 6) (5) (3 4 . 6) (1 4 . 5)) . 7)
;;  .
;;  #<procedure:...ro-internals.rkt:241:20>)
;; And the answers. Yeah. We're gonna need to do a little more. 

;; To pretty up an answer. 
(define walk*
  (lambda (w s)
    (let ((v (walk w s)))
      (cond
        ((var? v) v)
        ((pair? v) (cons (walk* (car v) s)
                         (walk* (cdr v) s)))
        (else v)))))

(define (reify-r v s)
  (let ((v (walk v s)))
    (cond
      ((var? v)
       (let ((n (reify-name (length s))))
         (cons `(,v . ,n) s)))
      ((pair? v) (reify-r (cdr v) (reify-r (car v) s)))
      (else s))))

(define (reify-name n)
  (string->symbol
    (string-append "_." (number->string n))))

(define (reify-1st q)
  (lambda (s/d/c)
    (let ((s (car s/d/c)))
      (let ((v (walk* q s)))
        (let ((d? (map (lambda (pr) (unify (car pr) (cdr pr) s)) (cadr s/d/c))))
          (let ((d+ (filter (lambda (x) x) (map (find-pfx s) d?))))
            (let ((rename-s (reify-r v '())))
              (let ((d (filter-not (lambda (d) (anyvar? d rename-s)) (rem-subsumed d+))))
                (form (walk* v rename-s) (walk* d rename-s))))))))))

(define form
  (lambda (v d)
    (let ((fd (sort-D d)))
      (cond
        ((null? fd) v)
        (else
         (let ((fd (drop-dot-D fd)))
           `(,v . ((=/= . ,fd)))))))))

(define sorter
  (lambda (ls)
    (sort ls lex<=?)))

(define sort-D
  (lambda (D)
    (sorter (map sort-d D))))

(define sort-d
  (lambda (d)
    (sort
      (map sort-pr d)
      (lambda (x y)
        (lex<=? (car x) (car y))))))

(define drop-dot
  (lambda (X)
    (map (lambda (t)
           (let ((a (car t))
                 (d (cdr t)))
             `(,a ,d)))
         X)))

(define drop-dot-D
  (lambda (D)
    (map drop-dot D)))

(define lex<-reified-name?
  (lambda (r)
    (char<?
      (string-ref (datum->string r) 0)
      (string-ref "_" 0))))

(define (call-with-string-output-port f)
  (define p (open-output-string))
    (f p)
    (get-output-string p))

(define datum->string
  (lambda (x)
    (call-with-string-output-port
      (lambda (p) (display x p)))))

(define sort-pr
  (lambda (pr)
    (let ((l (car pr))
          (r (cdr pr)))
      (cond
        ((lex<-reified-name? r) pr)
        ((lex<=? r l) `(,r . ,l))
        (else pr)))))

(define lex<=?
  (lambda (x y)
    (cond
      ((boolean? x)
       (cond
         ((boolean? y) (or (not x) (eq? x y)))
         (else #t)))
      ((boolean? y) #f)
      ((null? x) #t)
      ((null? y) #f)
      ((number? x)
       (cond
         ((number? y) (<= x y))
         (else #t)))
      ((number? y) #f)
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

(define find-pfx
  (lambda (s)
    (lambda (s^)
      (cond
        ((not s^) #f)
        ((eq? s s^) '())
        (else (cons (car s^) ((find-pfx s) (cdr s^))))))))

(define rem-subsumed
  (lambda (D)
    (let loop ((D D) (D+ '()))
      (cond
        ((null? D) D+)
        ((or (subsumed? (car D) (cdr D))
             (subsumed? (car D) D+))
         (loop (cdr D) D+))
        (else (loop (cdr D)
                (cons (car D) D+)))))))

(define unify*
  (lambda (S+ S)
    (unify (map car S+) (map cdr S+) S)))

(define subsumed?
  (lambda (d D)
    (cond
      ((null? D) #f)
      (else (let ((d^ (unify* (car D) d)))
              (or (and d^ (eq? d^ d))
                  (subsumed? d (cdr D))))))))

(define anyvar?
  (lambda (u S)
    (cond
      ((var? u) (var? (walk u S))) 
      ((pair? u) (or (anyvar? (car u) S)
                     (anyvar? (cdr u) S)))
      (else #f))))

(define call/empty-state
  (lambda (g) (g empty-state)))