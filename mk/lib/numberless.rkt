;; Daniel Brady, 8 June 2014
;;
;; This module provides a macro for preprocessing literals at expansion time
;; such that all number literals are disallowed.
;; > 3
;; Sorry: number literals disallowed in: 3
;; > '3
;; Sorry: number literals disallowed in: 3
;; > '(((((3))) foo) "asdf")
;; Sorry: number literals disallowed in: (((((3))) foo) "asdf")

(module numberless racket
  (provide (rename-out [no-nums #%datum]
                       [no-nums-quote quote]))
  
  ;; Raises a syntax error when a number literal is encountered.
  (define-syntax (no-nums stx)
    ;; Determines if an arbitrarily nested list of syntax objects contains a number.
    (letrec ([stx-contains-num? (lambda (ls*)
                                  ;; Unwrap syntax objects
                                  (let ([ls* (if (syntax? ls*) (syntax-e ls*) ls*)])
                                    (cond
                                      ((not (pair? ls*)) (number? ls*))
                                      ((null? ls*) #f)
                                      (else (let ([a (syntax-e (car ls*))])
                                              (cond
                                                ((pair? a) (or (stx-contains-num? a)
                                                               (stx-contains-num? (cdr ls*))))
                                                (else (or (number? a)
                                                          (stx-contains-num? (cdr ls*))))))))))])
      (syntax-case stx ()
        ((_ . datum)
         (if (stx-contains-num? #'datum)
             (raise-syntax-error 'Sorry "numbers are an advanced feature" #'datum)
             #'(quote datum))))))
  
  ;; All quoted values rerouted from (quote <datum>) to (no-nums-quote <datum>),
  ;; which in turn expands to (no-nums . <datum>), disallowing quoted number literals.
  (define-syntax-rule (no-nums-quote datum)
    (no-nums . datum)))