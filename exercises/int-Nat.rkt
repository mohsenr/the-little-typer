#lang pie

;; Exercises on Vec and ind-Nat from Chapters 6 and 7 of The Little
;; Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (a-k b+a-k)
               (add1 b+a-k)))))

;; Exercise 7.0
;;
;; Define a function called zip that takes an argument of type (Vec A n) and a
;; second argument of type (Vec B n) and evaluates to a vlue of type (Vec (Pair A B) n),
;; the result of zipping the first and second arguments.
        
(claim zip
  (Pi ([A U] [B U] [n Nat])
    (-> (Vec A n) (Vec B n) (Vec (Pair A B) n))))
(define zip
  (lambda (A B n)
    (ind-Nat n
      (lambda (k) (-> (Vec A k) (Vec B k) (Vec (Pair A B) k)))
      (lambda (_ _) vecnil)
      (lambda (k zip-k)
        (lambda (es fs)
          (vec:: (cons (head es) (head fs))
            (zip-k (tail es) (tail fs))))))))

(check-same (Vec (Pair Nat Atom) 2)
            (zip Nat Atom 2
                 (vec:: 1 (vec:: 2 vecnil))
                 (vec:: 'orange (vec:: 'pear vecnil)))
            (vec:: (cons 1 'orange) (vec:: (cons 2 'pear) vecnil)))

;; Exercise 7.1
;;
;; Define a function called append that takes an argument of type (Vec E n) and an
;; argument of type (Vect E m) and evaluates to a value of type (Vec (+ n m)), the
;; result of appending the elements of the second argument to the end of the first.

(claim append
       (Π ([E U]
           [n Nat]
           [m Nat])
          (-> (Vec E n) (Vec E m)
              (Vec E (+ n m)))))
(define append
  (lambda (E n m)
    (ind-Nat n
      (lambda (k) (-> (Vec E k) (Vec E m) (Vec E (+ k m))))
      (lambda (_ fs) fs)
      (lambda (k append-k)
        (lambda (es fs)
          (vec:: (head es)
            (append-k (tail es) fs)))))))

(check-same (Vec Nat 5)
            (append Nat 2 3
                    (vec:: 0 (vec:: 1 vecnil))
                    (vec:: 2 (vec:: 3 (vec:: 4 vecnil))))
            (vec:: 0 (vec:: 1 (vec:: 2 (vec:: 3 (vec:: 4 vecnil))))))


;; Exercise 7.2
;;
;; Define a function called drop-last-k that takes an argument of type (Vec E ?) and
;; evaluates to a value of type (Vec E ?), the result of dropping the last k elements
;; from the first argument.
;;
;; NB: The type of the function should guarantee that we can't drop more elements
;; than there are in the first argument.

(claim drop-last-k
  (Pi ([E U] [k Nat] [n Nat])
    (-> (Vec E (+ n k)) (Vec E n))))
(define drop-last-k
  (lambda (E k n)
    (ind-Nat n
      (lambda (n) (-> (Vec E (+ n k)) (Vec E n)))
      (lambda (_) vecnil)
      (lambda (k drop-last-k-1)
        (lambda (es)
          (vec:: (head es) (drop-last-k-1 (tail es))))))))

(check-same (Vec Nat 1)
            (drop-last-k Nat 2 1
                         (vec:: 0 (vec:: 1 (vec:: 2 vecnil))))
            (vec:: 0 vecnil))