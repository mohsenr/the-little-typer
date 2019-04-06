#lang pie

;; Exercises on ind-Vec from Chapter 11 of The Little Typer

;; Exercise 11.1
;;
;; Use ind-Vec to define a function called unzip that takes unzips
;; a vector of pairs into a pair of vectors.

(claim unzip
       (Π ([A U]
           [B U]
           [n Nat])
          (-> (Vec (Pair A B) n)
              (Pair (Vec A n) (Vec B n)))))

(define unzip
  (lambda (A B n vector)
    (ind-Vec n vector
      (lambda (n _) (Pair (Vec A n) (Vec B n)))
      (cons vecnil vecnil)
      (lambda (_ e _ es)
        (cons
          (vec:: (car e) (car es))
          (vec:: (cdr e) (cdr es)))))))