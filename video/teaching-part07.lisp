; Part Seven uses the actual rational phase and finite Mellin constructors.
; Numerical sample-component examples below are explicitly illustrative.
(in-package "ACL2")
(include-book "../acl2/mellin-quadrature")

(local
 (defthm video-seven-product-commutes
   (equal (* left (* middle right)) (* middle (* left right)))
   :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                         (:instance associativity-of-* (x middle) (y left) (z right))
                         (:instance commutativity-of-* (x left) (y middle)))
                   :in-theory (disable associativity-of-* commutativity-of-*)))))

(local
 (defthm video-seven-times-negation
   (implies (and (rationalp left) (rationalp right))
            (equal (* left (- right)) (- (* left right))))
   :hints (("Goal" :use ((:instance distributivity (x left) (y right) (z (- right))))
                   :in-theory (disable distributivity)))))

(defthm video-quarter-turn
  (and (equal (lw-complex-mul '(3/5 . 4/5) '(0 . 1)) '(-4/5 . 3/5))
       (equal (lw-complex-power '(0 . 1) 4) '(1 . 0)))
  :rule-classes nil)

(defthm video-rotation-polynomial
  (implies (rationalp x)
           (equal (+ (* (- 4 (* x x)) (- 4 (* x x)))
                     (* 4 x 4 x))
                  (* (+ 4 (* x x)) (+ 4 (* x x)))))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

(defthm video-rotation-examples
  (and (equal (lw-phase-rotation 1) '(3/5 . 4/5))
       (equal (lw-phase-rotation -1) '(3/5 . -4/5))
       (equal (lw-phase-rotation 1/2) '(15/17 . 8/17)))
  :rule-classes nil)

(defthm video-phase-grid-example
  (and (equal (lw-phase-grid 1 1) '(3/5 . 4/5))
       (equal (lw-phase-grid 1 2) '(161/289 . 240/289)))
  :rule-classes nil)

(defthm video-phase-order
  (and (equal (lw-phase-steps 1 1/4) 9)
       (implies (and (rationalp error) (< 0 error))
                (<= (/ 2 (lw-phase-steps 1 error)) error)))
  :hints (("Goal" :use ((:instance lw-phase-steps-adequate (value 1))
                         (:instance lw-positive-division-bound
                           (numerator 2) (divisor (lw-phase-steps 1 error)) (bound error)))
                  :expand ((lw-phase-steps 1 1/4))
                  :in-theory (disable lw-phase-steps lw-phase-steps-adequate)
                  :nonlinearp t))
  :rule-classes nil)

(defthm video-component-budget-example
  (and (equal (lw-mellin-component-error 1/10 3) 1/120)
       (equal (lw-mellin-component-error 1/10 2) 1/90)
       (equal (lw-mellin-component-error 1/10 6) 1/210)
       (< (+ (* 3 1/120) (* 2 1/90) (* 6 1/210)) 1/10))
  :rule-classes nil)

(defthm video-component-budget-general
  (implies (and (rationalp m) (<= 0 m) (rationalp k) (<= 0 k)
                (rationalp error) (< 0 error))
           (<= (+ (* k (lw-mellin-component-error error k))
                  (* m (lw-mellin-component-error error m))
                  (* m k (lw-mellin-component-error error (* m k))))
               error))
  :hints (("Goal" :use ((:instance lw-mellin-component-error-valid (factor k))
                         (:instance lw-mellin-component-error-valid (factor m))
                         (:instance lw-mellin-component-error-valid (factor (* m k))))
                  :in-theory (disable lw-mellin-component-error lw-mellin-component-error-valid)
                  :nonlinearp t))
  :rule-classes nil)

(defthm video-negative-sample
  (equal (lw-complex-scale (* -2 1/2) '(3/5 . -4/5)) '(-3/5 . 4/5))
  :rule-classes nil)

(defthm video-vector-sum
  (equal (lw-complex-add '(-3/5 . 4/5) '(1/5 . -1/5)) '(-2/5 . 3/5))
  :rule-classes nil)

(defthm video-cell-allocation
  (and (lw-mellin-cellsp '((0 . 1/2) (1/2 . 1/2)))
       (equal (lw-mellin-sum-error '((0 . 1/2) (1/2 . 1/2)) 1/10) 1/30)
       (< (* 2 1/30) 1/10))
  :rule-classes nil)

(assert-event (lw-complex-diskp '(3/5 . 4/5) 1))
(assert-event (not (lw-complex-diskp '(1 . 1) 1)))
(assert-event (equal (lw-phase-value 0 1/10) '(1 . 0)))
