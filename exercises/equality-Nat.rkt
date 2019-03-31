#lang pie

;; Exercises on Nat equality from Chapter 8 and 9 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ b+a-k)
               (add1 b+a-k)))))

;; Exercise 8.1
;; Define a function called zero+n=n that states and proves that
;; 0+n = n for all Nat n.

(claim zero+n=n
  (Pi ([n Nat])
    (= Nat (+ 0 n) n)))

(define zero+n=n
  (lambda (n)
    (same n)))

;; Exercise 8.2
;;
;; Define a function called a=b->a+n=b+n that states and proves that
;; a = b implies a+n = b+n for all Nats a, b, n.

(claim a=b->a+n=b+n
  (Pi ([a Nat]
       [b Nat]
       [n Nat])
    (-> (= Nat a b) (= Nat (+ a n) (+ b n)))))

(define a=b->a+n=b+n
  (lambda (a b n a=b)
    (replace a=b
      (lambda (k) (= Nat (+ a n) (+ k n)))
      (same (+ a n)))))

;; Exercise 8.3
;;
;; Define a function called plusAssociative that states and proves that
;; + is associative.

(claim plusAssociative
       (Π ([n Nat]
           [m Nat]
           [k Nat])
          (= Nat (+ k (+ n m)) (+ (+ k n) m))))

(define plusAssociative
  (lambda (n m k)
    (ind-Nat k
      (lambda (k) (= Nat (+ k (+ n m)) (+ (+ k n) m)))
      (same (+ n m))
      (lambda (k-1 plusAssociative-1)
        (cong plusAssociative-1 (+ 1))))))

;; Exercise 9.1
;;
;; Define a function called same-cons that states and proves that
;; if you cons the same value to the front of two equal Lists then
;; the resulting Lists are also equal.

(claim same-cons
       (Π ([E U]
           [l1 (List E)]
           [l2 (List E)]
           [e E])
          (-> (= (List E) l1 l2)
              (= (List E) (:: e l1) (:: e l2)))))

(claim my-cons
  (Pi ([E U])
    (-> E (List E) (List E))))

(define my-cons
  (lambda (E e es)
    (:: e es)))

(define same-cons
  (lambda (E l1 l2 e)
    (lambda (l1=l2)
      (cong l1=l2 (my-cons E e)))))

;; Exercise 9.2
;;
;; Define a function called same-lists that states and proves that
;; if two values, e1 and e2, are equal and two lists, l1 and l2 are
;; equal then the two lists, (:: e1 l1) and (:: e2 l2) are also equal.

(claim same-lists
  (Pi ([E U]
       [l1 (List E)]
       [l2 (List E)]
       [e1 E]
       [e2 E])
    (-> (= E e1 e2) (= (List E) l1 l2)
      (= (List E) (:: e1 l1) (:: e2 l2)))))

(define same-lists
  (lambda (E l1 l2 e1 e2)
    (lambda (e1=e2 l1=l2)
      (replace e1=e2
        (lambda (k) (= (List E) (:: e1 l1) (:: k l2)))
        (same-cons E l1 l2 e1 l1=l2)))))

;; Exercise 9.3 (was previously called Exercise 8.4)
;;
;; Define a function called plusCommutative that states and proves that
;; + is commutative
;;
;; Bonus: Write the solution using the trans elimiator instead of
;; the replace elimiator.
;; https://docs.racket-lang.org/pie/index.html#%28def._%28%28lib._pie%2Fmain..rkt%29._trans%29%29

(claim n=n+zero
  (Pi ([n Nat])
    (= Nat n (+ n 0))))

(define n=n+zero
  (lambda (n)
    (ind-Nat n
      (lambda (k) (= Nat k (+ k 0)))
      (same zero)
      (lambda (_ proof)
        (cong proof (+ 1))))))

(claim type:a+b=b+a
       (Π ([n Nat]
           [m Nat])
         U))

(define type:a+b=b+a
  (lambda (n m)
    (= Nat (+ n m) (+ m n))))

(claim zero+n=n+zero
  (Pi ([n Nat])
    (type:a+b=b+a zero n)))

(define zero+n=n+zero
  (lambda (n)
    (trans (zero+n=n n) (n=n+zero n))))

(claim add1Commutative
  (Pi ([m Nat]
       [n Nat])
    (= Nat (add1 (+ n m)) (+ n (add1 m)))))

(define add1Commutative
  (lambda (m n)
    (ind-Nat n
      (lambda (k) (= Nat (add1 (+ k m)) (+ k (add1 m))))
      (same (add1 m))
      (lambda (_ proof)
        (cong proof (+ 1))))))

(claim plusCommutative
       (Π ([n Nat]
           [m Nat])
          (type:a+b=b+a n m)))

(define plusCommutative
  (lambda (n m)
    (ind-Nat n
      (lambda (k) (type:a+b=b+a k m))
      (zero+n=n+zero m)
      (lambda (k equals)
        (trans (cong equals (+ 1)) (add1Commutative k m))))))
