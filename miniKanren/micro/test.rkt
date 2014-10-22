#lang miniKanren/micro

(define conso
  (lambda (a d p)
    (== (cons a d) p)))

(define hot-dogso
  (lambda (out)
    (conde
     ((== out 'dog))
     ((fresh (res)
        (conso 'hot res out)
        (hot-dogso res))))))