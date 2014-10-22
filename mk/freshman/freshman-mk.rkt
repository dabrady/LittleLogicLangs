;; Daniel Brady, 8 June 2014
;; mk/freshman
;; This module provides a very restricted version of miniKanren:
;
;       - a 'pure' version of mk (i.e. no intermingling Racket/Scheme and mk)
;	- no non-relational code allowed
;	- Numberless
;	- all user-defined functions must be relations (i.e. start with a fresh or conde)
;	- more builtin relations (conso, caro, cdro, etc.)
;	- disallow quasiquote syntax with (read-accept-quasiquote #f)
;	- disallow anonymous lambdas?
;	- perhaps disallow no-arg lambdas? Without side-effects, these aren't generally helpful, and most relations have an 'out' variable
;
;	Syntax checker:
;		- conde/fresh/run disallow non-relational code
;		- relation definitions enforce starting with a fresh or conde
;		- relation defintions can contain only one body
;		- ...

(module freshman-mk "freshman-mk-lang.rkt"
  ;(require "../lib/numberless.rkt")
  (require "freshman-stx.rkt")
  (provide (except-out (all-from-out "freshman-mk-lang.rkt") define)
           ;(all-from-out "../lib/numberless.rkt")
           (rename-out [freshman-define define]))
  
  ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
  

  )