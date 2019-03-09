#lang pie

;; Exercises on Pi types and using the List elimiator from Chapters 4 and 5
;; of The Little Typer
;;
;; Some exercises are adapted from assignments at Indiana University

(claim double (-> Nat Nat))
(define double
  (lambda (a)
    (rec-Nat a a (lambda (k sum) (add1 sum)))))

(claim + (-> Nat Nat Nat))
(define +
  (lambda (a b)
    (rec-Nat a b (lambda (k sum) (add1 sum)))))

(claim at-least-two? (-> Nat Atom))
(define at-least-two?
  (lambda (n)
     (which-Nat n 'f
       (lambda (n)
         (which-Nat n 'f (lambda (n) 't))))))

(claim diff (-> Nat Nat (Either Nat Nat)))
(define diff
  (lambda (l r)
    (iter-Nat l (the (Either Nat Nat) (right r))
      (lambda (acc)
        (ind-Either acc
          (lambda (e) (Either Nat Nat))
          (lambda (acc) (left (add1 acc)))
          (lambda (acc)
            (which-Nat acc (the (Either Nat Nat) (left (add1 zero)))
              (lambda (r-1) (right r-1)))))))))

;; Exercise 4.1
;;
;; Extend the definitions of kar and kdr (frame 4.42) so they work with arbirary
;; Pairs (instead of just for Pair Nat Nat).


;; Exercise 4.2
;;
;; Define a function called compose that takes (in addition to the type
;; arguments A, B, C) an argument of type (-> A B) and an argument of
;; type (-> B C) that and evaluates to a value of type (-> A C), the function
;; composition of the arguments.

(claim compose (Pi ([A U] [B U] [C U])
              (-> (-> A B) (-> B C) (-> A C))))
(define compose
  (lambda (A B C)
    (lambda (f g)
      (lambda (a) (g (f a))))))

(check-same Atom (compose Nat Nat Atom double at-least-two? 1) 't)

;; Exercise 5.1
;;
;; Define a function called sum-List that takes one List Nat argument and
;; evaluates to a Nat, the sum of the Nats in the list.

(claim sum-List (-> (List Nat) Nat))
(define sum-List
  (lambda (list)
    (rec-List list 0
      (lambda (val _ acc) (+ val acc)))))

(check-same Nat (sum-List (:: 1 (:: 2 (:: 4 nil)))) 7)

;; Exercise 5.2
;;
;; Define a function called maybe-last which takes (in addition to the type
;; argument for the list element) one (List E) argument and one E argument and
;; evaluates to an E with value of either the last element in the list, or the
;; value of the second argument if the list is empty.

(claim maybe-last (Pi ([E U]) (-> (List E) E E)))
(define maybe-last
  (lambda (E)
    (lambda (list)
      (rec-List list (the (-> E E) (lambda (fallback) fallback))
        (lambda (e es func)
          (rec-List es (the (-> E E) (lambda (_) e))
            (lambda (_ _ _) func)))))))

(check-same Nat (maybe-last Nat (:: 1 (:: 2 (:: 4 nil))) 9) 4)
(check-same Nat (maybe-last Nat nil 9) 9)

;; Either way!

(claim last (Pi ([E U]) (-> (List E) (Either E Trivial))))
(define last
  (lambda (E)
    (lambda (list)
      (rec-List list (the (Either E Trivial) (right sole))
        (lambda (val _ acc)
          (ind-Either acc
            (lambda (_) (Either E Trivial))
            (lambda (_) acc)
            (lambda (_) (left val))))))))

(check-same (Either Nat Trivial) (last Nat (:: 1 (:: 2 (:: 4 nil)))) (left 4))
(check-same (Either Nat Trivial) (last Nat nil) (right sole))

(claim maybe-last-hard (Pi ([E U]) (-> (List E) E E)))
(define maybe-last-hard
  (lambda (E)
    (lambda (list fallback)
      (ind-Either (last E list)
        (lambda (_) E)
        (lambda (val) val)
        (lambda (_) fallback)))))

(check-same Nat (maybe-last-hard Nat (:: 1 (:: 2 (:: 4 nil))) 9) 4)
(check-same Nat (maybe-last-hard Nat nil 9) 9)

;; Exercise 5.3
;;
;; Define a function called filter-list which takes (in addition to the type
;; argument for the list element) one (-> E Nat) argument representing a
;; predicate and one (List E) argument.
;;
;; The function evaluates to a (List E) consisting of elements from the list
;; argument where the predicate is true.
;;
;; Consider the predicate to be false for an element if it evaluates to zero,
;; and true otherwise.

(claim filter-list-step (Pi ([E U]) (-> (-> E Nat) E (List E) (List E) (List E))))
(define filter-list-step
  (lambda (E)
    (lambda (predicate value _ acc)
      (which-Nat (predicate value) acc
        (lambda (_) (:: value acc))))))

(claim filter-list (Pi ([E U]) (-> (-> E Nat) (List E) (List E))))
(define filter-list
  (lambda (E)
    (lambda (predicate list)
      (rec-List list (the (List E) nil)
        (filter-list-step E predicate)))))

(claim different-from-zero (-> Nat Nat))
(define different-from-zero (lambda (e) e))

(check-same (List Nat) (filter-list Nat different-from-zero (:: 0 (:: 1 (:: 0 nil)))) (:: 1 nil))
(check-same (List Nat) (filter-list Nat different-from-zero (:: 0 (:: 0 (:: 0 nil)))) nil)
(check-same (List Nat) (filter-list Nat different-from-zero nil) nil)


;; Exercise 5.4
;;
;; Define a function called sort-List-Nat which takes one (List Nat) argument
;; and evaluates to a (List Nat) consisting of the elements from the list
;; argument sorted in ascending order.

(claim insert-sorted (-> Nat (List Nat) (List Nat)))
(define insert-sorted
  (lambda (value list)
    (rec-List list (:: value nil)
      (lambda (e es acc)
        (ind-Either (diff value e)
          (lambda (_) (List Nat))
          (lambda (_) (:: e acc))
          (lambda (_) (:: value (:: e es))))))))

(check-same (List Nat) (insert-sorted 4 nil) (:: 4 nil))
(check-same (List Nat) (insert-sorted 4 (:: 3 nil)) (:: 3 (:: 4 nil)))
(check-same (List Nat) (insert-sorted 3 (:: 4 nil)) (:: 3 (:: 4 nil)))

(claim sort-List-Nat (-> (List Nat) (List Nat)))
(define sort-List-Nat
  (lambda (list)
    (rec-List list (the (List Nat) nil)
      (lambda (e _ acc) (insert-sorted e acc)))))

(check-same (List Nat) (sort-List-Nat (:: 4 nil)) (:: 4 nil))
(check-same (List Nat) (sort-List-Nat (:: 3 (:: 4 nil))) (:: 3 (:: 4 nil)))
(check-same (List Nat) (sort-List-Nat (:: 4 (:: 3 nil))) (:: 3 (:: 4 nil)))
