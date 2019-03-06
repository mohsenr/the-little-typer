#lang pie

;; Exercises on using Nat elimiators from Chapter 3 of The Little Typer
;;
;; Some exercises are adapted from assignments at Indiana University

;; Exercise 3.1
;;
;; Define a function called at-least-two? that takes one Nat argument and evaluates to an Atom.
;;
;; at-least-two? evaluates to 't if the Nat is greater than or equal to 2 otherwise it evaluates to 'nil.
;;
;; Note: The only Nat eliminator you should need in the body of at-least-two? is which-Nat.

(claim at-least-two? (-> Nat Atom))
(define at-least-two?
  (lambda (n)
     (which-Nat n 'f
       (lambda (n)
         (which-Nat n 'f (lambda (n) 't))))))

;; Exercise 3.2
;;
;; Rewrite the definition of + (in frame 3.27) using the rec-Nat eliminator instead of the iter-Nat eliminator.

(claim +iter (-> Nat Nat Nat))
(define +iter
  (lambda (a b)
    (iter-Nat a b (lambda (k) (add1 k)))))

(claim + (-> Nat Nat Nat))
(define +
  (lambda (a b)
    (rec-Nat a b (lambda (k sum) (add1 sum)))))

;; Exercise 3.3
;;
;; Define a function called exp that takes two Nat arguments and evaluates to a Nat.
;;
;; exp evaluates to the exponentiation, a^b, of the two passed arguments.

(claim * (-> Nat Nat Nat))
(define *
  (lambda (a b)
    (rec-Nat b 0 (lambda (k acc) (+ a acc)))))

(claim exp (-> Nat Nat Nat))
(define exp
  (lambda (a b)
    (rec-Nat b 1 (lambda (k acc) (* a acc)))))

;; Exercise 3.4
;;
;; Define a function called max that takes two Nat arguments and evaluates to a Nat.
;;
;; max evaluates to the larger of the two passed arguments.

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

(claim max (-> Nat Nat Nat))
(define max
  (lambda (l r)
    (ind-Either (diff l r)
      (lambda (e) Nat)
      (lambda (_) l)
      (lambda (_) r))))

(claim min (-> Nat Nat Nat))
(define min
  (lambda (l r)
    (ind-Either (diff l r)
      (lambda (e) Nat)
      (lambda (_) r)
      (lambda (_) l))))

(check-same Nat (max 3 7) 7)
(check-same Nat (min 3 7) 3)

; The hard way!

(claim rec-NatWithDelta
  (Pi ([X U])
    (-> Nat Nat X (-> Nat Nat X X) X)))
(define rec-NatWithDelta
  (lambda (X)
    (lambda (n delta base step)
      (rec-Nat n base
        (lambda (n-1 acc)
          (step n-1 (+ n-1 delta) acc))))))

(claim rec-NatPair
  (Pi ([X U])
    (-> Nat Nat (-> Nat X) (-> Nat X) (-> Nat Nat X X) X)))
(define rec-NatPair
  (lambda (X)
    (lambda (a b left_base right_base step)
      (ind-Either (diff a b)
        (lambda (e) X)
        (lambda (delta) (rec-NatWithDelta X b delta (left_base delta) step))
        (lambda (delta) (rec-NatWithDelta X a delta (right_base delta) step))))))

(claim min2 (-> Nat Nat Nat))
(define min2
  (lambda (l r)
    (rec-NatPair Nat l r
      (lambda (delta) 0)
      (lambda (delta) 0)
      (lambda (l-1 r-1 res) (add1 res)))))

(claim max2 (-> Nat Nat Nat))
(define max2
  (lambda (l r)
    (rec-NatPair Nat l r
      (lambda (delta) delta)
      (lambda (delta) delta)
      (lambda (l-1 r-1 res) (add1 res)))))

(check-same Nat (min2 17 78) 17)
(check-same Nat (max2 17 78) 78)