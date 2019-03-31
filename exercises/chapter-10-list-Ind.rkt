#lang pie

;; Exercises on ind-Nat from Chapter 10 of The Little Typer

(claim +
       (-> Nat Nat
           Nat))

(define +
  (λ (a b)
    (rec-Nat a
             b
             (λ (_ b+a-k)
               (add1 b+a-k)))))

(claim length
       (Π ([E U])
          (-> (List E)
              Nat)))

(define length
  (λ (_)
    (λ (es)
      (rec-List es
                0
                (λ (_ _ almost-length)
                  (add1 almost-length))))))

(claim step-append
       (Π ([E U])
          (-> E (List E) (List E)
              (List E))))

(define step-append
  (λ (E)
    (λ (e es append-es)
      (:: e append-es))))

(claim append
       (Π ([E U])
          (-> (List E) (List E)
              (List E))))

(define append
  (λ (E)
    (λ (start end)
      (rec-List start
                end
                (step-append E)))))

(claim filter-list
       (Π ([E U])
          (-> (-> E Nat) (List E)
              (List E))))

(claim filter-list-step
       (Π ([E U])
          (-> (-> E Nat)
              (-> E (List E) (List E)
                  (List E)))))

(claim if
       (Π ([A U])
          (-> Nat A A
              A)))

(define if
  (λ (A)
    (λ (e if-then if-else)
      (which-Nat e
                 if-else
                 (λ (_) if-then)))))

(define filter-list-step
  (λ (E)
    (λ (p)
      (λ (e es filtered-es)
        (if (List E) (p e)
            (:: e filtered-es)
            filtered-es)))))

(define filter-list
  (λ (E)
    (λ (p es)
      (rec-List es
                (the (List E) nil)
                (filter-list-step E p)))))

;; Previously:

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

(claim zero+n=n
  (Pi ([n Nat])
    (= Nat (+ 0 n) n)))

(define zero+n=n
  (lambda (n)
    (same n)))

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

;; Exercise 10.1
;;
;; Define a function called list-length-append-dist that states and proves that
;; if you append two lists, l1 and l2, and then the length of the result is
;; equal to the sum of the lengths of l1 and l2.

(claim type:list-length-dist
       (Π ([E U]
           [l1 (List E)]
           [l2 (List E)])
         U))

(define type:list-length-dist
  (lambda (E l1 l2)
    (= Nat
             (length E (append E l1 l2))
             (+ (length E l1) (length E l2)))))

(claim list-length-append-dist
       (Π ([E U]
           [l1 (List E)]
           [l2 (List E)])
          (type:list-length-dist E l1 l2)))

(define list-length-append-dist
  (lambda (E l1 l2)
    (ind-List l1
      (lambda (list) (type:list-length-dist E list l2))
      (same (length E l2))
      (lambda (_ _ proof)
        (cong proof (+ 1))))))

;; Exercise 10.2
;;
;; In the following exercises we'll use the function called <= that takes two
;; Nat arguments a, b and evaluates to a type representing the proposition
;; that a is less than or equal to b.

(claim <=
       (-> Nat Nat
           U))

(define <=
  (λ (a b)
    (Σ ([k Nat])
       (= Nat (+ k a) b))))

;; Exercise 10.2.1
;;
;; Using <=, state and prove that 1 is less than or equal to 2.

(claim 1<2 (<= 1 2))

(define 1<2
  (cons 1 (same 2)))

;; Exercise 10.2.2
;;
;; Define a funciton called <=-simplify to state and prove that for all
;; Nats a, b, n we have that n+a <= b implies a <= b
;;
;; NB: You may need to use plusAssociative that was proved in Exercise 8.3.

(claim <=-simplify
       (Π ([a Nat]
           [b Nat]
           [n Nat])
          (-> (<= (+ n a) b)
              (<= a b))))

(define <=-simplify
  (lambda (a b n n+a<=b)
    (cons (+ (car n+a<=b) n)
      ; expecting (= Nat (+ (+ (car n+a<=b) n) a) b)
      ; (cdr  n+a<=b) <-- (= Nat (+ (car n+a<=b) (+ n a)) b)
      (trans
        (symm (plusAssociative n a (car n+a<=b)))
        (cdr  n+a<=b)))))
      

;; Exercise 10.2.3
;;
;; Define a function called <=-trans that states and proves that <= is
;; transitive.

(claim <=-trans
       (Π ([a Nat]
           [b Nat]
           [c Nat])
          (-> (<= a b)
              (<= b c)
              (<= a c))))

(define <=-trans
  (lambda (a b c a<=b b<=c)
    (cons (+  (car b<=c) (car a<=b))
      ; expecting (= Nat (+ (+ (car b<=c) (car a<=b)) a) c)
      ; (cdr a<=b) <-- (= Nat (+ (car a<=b) a) b)
      ; (cdr b<=c) <-- (= Nat (+ (car b<=c) b) c)
      (trans
        (replace (plusAssociative (car a<=b) a (car b<=c))
          (lambda (k) (= Nat k (+ (car b<=c) b)))
          (cong (cdr a<=b) (+ (car b<=c)))) ; <-- (= Nat (+ (car b<=c) (+ (car a<=b) a)) (+ (car b<=c) b))
        (cdr b<=c)))))

;; Exercise 10.3
;;
;; Define a function called length-filter-list that states and proves that
;; filtering a list (in the sense of filter-list from Exercise 5.3) evaluates
;; to a a list no longer than the original list.

(claim type:length-filter-list
       (Π ([E U]
           [l (List E)]
           [p (-> E Nat)])
         U))

(define type:length-filter-list
  (lambda (E l p)
    (<= (length E (filter-list E p l))
      (length E l))))

(claim conditional-cons
  (Pi ([E U]
       [l (List E)]
       [e E]
       [c Nat])
    (List E)))

(define conditional-cons
  (lambda (E l e c)
    (which-Nat c l (lambda (_) (:: e l)))))

(claim type:length-filtered-cons
  (Pi ([E U]
       [l (List E)]
       [e E]
       [c Nat])
    U))

(define type:length-filtered-cons
  (lambda (E l e c)
    (<= (length E (conditional-cons E l e c))
        (length E (:: e l)))))
  
(claim length-filtered-cons
  (Pi ([E U]
       [l (List E)]
       [e E]
       [c Nat])
    (type:length-filtered-cons E l e c)))

(define length-filtered-cons
  (lambda (E l e c)
    (ind-Nat c
      (lambda (k) (type:length-filtered-cons E l e k))
      (cons 1 (same (length E (:: e l))))
      (lambda (_ _) (cons 0 (same (length E (:: e l))))))))

(claim length-filter-list
       (Π ([E U]
           [l (List E)]
           [p (-> E Nat)])
         (type:length-filter-list E l p)))

(claim <=-cong-add1
  (Pi ([a Nat]
       [b Nat])
    (-> (<= a b)
        (<= (add1 a) (add1 b)))))

(define <=-cong-add1
  (lambda (a b a<=b)
    (cons (car a<=b)
      (trans
        (symm (add1Commutative a (car a<=b)))
        (cong (cdr a<=b) (+ 1)))))) ; <-- (= (+ 1 (+ (car a<=b) a)) (+ 1 b))
        

(define length-filter-list
  (lambda (E l p)
    (ind-List l
      (lambda (sublist) (type:length-filter-list E sublist p))
      (cons 0 (same 0))
      (lambda (e es filtered-es<=es)
        (<=-trans
          (length E (filter-list E p (:: e es)))
          (length E (:: e (filter-list E p es)))
          (length E (:: e es))
          (length-filtered-cons E (filter-list E p es) e (p e))
          (<=-cong-add1
            (length E (filter-list E p es))
            (length E es)
            filtered-es<=es))))))