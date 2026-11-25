(in-package "ACL2")

(include-book "phase-bounds")

; Spatial transport for the constructed phase.  This compares different
; arguments, as required by partition refinement, rather than only different
; precisions at one argument.  No trigonometric function or limit is assumed.

(local (defthm lw-pc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-pc-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-pc-times-zero (equal (* 0 a) 0)))
(local (defthm lw-pc-times-minus-one
         (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-pc-negative-times
         (implies (and (rationalp a) (rationalp b))
                  (equal (* (- a) b) (- (* a b))))
         :hints (("Goal" :use ((:instance lw-pc-times-negative (a b) (b a)))
                         :in-theory (disable lw-pc-times-negative)))))
(local (defthm lw-pc-double-negation
         (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-pc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-pc-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-pc-square-nonnegative
         (implies (rationalp a) (<= 0 (* a a)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-pc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-pc-left-commutes)))))
(local (defthm lw-pc-cancel-product
         (implies (and (rationalp a) (rationalp b) (rationalp c) (< 0 c)
                       (equal (* c a) (* c b)))
                  (equal a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-pc-inverse-product
         (implies (and (rationalp a) (rationalp b) (< 0 a) (< 0 b))
                  (equal (/ (* a b)) (* (/ a) (/ b))))
         :hints (("Goal" :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
                              (:instance inverse-of-* (x (* a b)))
                              (:instance lw-pc-cancel-product
                                (c (* a b)) (a (/ (* a b))) (b (* (/ a) (/ b)))))
                         :in-theory (disable inverse-of-*) :nonlinearp t))))

(local
 (defthm lw-pc-normalize
   (implies (and (rationalp divisor) (< 0 divisor) (rationalp radius)
                 (lw-complex-diskp point (* divisor radius)))
            (lw-complex-diskp (lw-complex-scale (/ divisor) point) radius))
   :hints (("Goal" :use ((:instance lw-complex-scale-disk
                          (factor (/ divisor)) (radius (* divisor radius)))
                         (:instance inverse-of-* (x divisor)))
                   :in-theory (disable lw-complex-scale lw-complex-diskp lw-complex-scale-disk
                                       lw-complex-disk-enlarge lw-disk-enlarge inverse-of-*)
                   :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-pc-cross-quotients
   (implies (and (rationalp a) (rationalp b) (rationalp c) (< 0 c) (rationalp d) (< 0 d))
            (equal (- (/ a c) (/ b d)) (/ (- (* a d) (* b c)) (* c d))))
   :hints (("Goal" :in-theory (disable distributivity lw-pc-left-distribute)
                   :use ((:instance lw-pc-inverse-product (a c) (b d))
                         (:instance lw-pc-inverse-factor (divisor d) (coefficient (/ a c)))
                         (:instance lw-pc-inverse-factor (divisor c) (coefficient (/ b d)))))
           (and stable-under-simplificationp '(:in-theory (enable distributivity lw-pc-left-distribute))))
   :rule-classes nil))

(local
 (defthm lw-pc-rotation-difference
   (implies (and (rationalp left) (rationalp right))
            (equal (lw-complex-sub (lw-phase-rotation left) (lw-phase-rotation right))
                   (lw-complex-scale
                    (/ (* (lw-phase-denominator left) (lw-phase-denominator right)))
                    (cons (* -8 (- left right) (+ left right))
                          (* 4 (- left right) (- 4 (* left right)))))))
   :hints (("Goal" :use ((:instance lw-phase-denominator-positive (value left))
                         (:instance lw-phase-denominator-positive (value right))
                         (:instance lw-pc-cross-quotients
                           (a (- 4 (* left left))) (b (- 4 (* right right)))
                           (c (lw-phase-denominator left)) (d (lw-phase-denominator right)))
                         (:instance lw-pc-cross-quotients
                           (a (* 4 left)) (b (* 4 right))
                           (c (lw-phase-denominator left)) (d (lw-phase-denominator right))))
                   :in-theory (disable inverse-of-* lw-pc-inverse-product
                                       lw-complex-disk-enlarge lw-disk-enlarge)
                   :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-pc-raw-norm-identity
   (implies (and (rationalp left) (rationalp right))
            (equal (+ (* (* -8 (- left right) (+ left right)) (* -8 (- left right) (+ left right)))
                      (* (* 4 (- left right) (- 4 (* left right)))
                         (* 4 (- left right) (- 4 (* left right)))))
                   (* 16 (- left right) (- left right)
                      (lw-phase-denominator left) (lw-phase-denominator right))))
   :rule-classes nil))

(local
 (defthm lw-pc-denominator-product
   (implies (and (rationalp left) (rationalp right))
            (<= 16 (* (lw-phase-denominator left) (lw-phase-denominator right))))
   :hints (("Goal" :use ((:instance lw-pc-square-nonnegative (a left))
                         (:instance lw-pc-square-nonnegative (a right))
                         (:instance lw-pc-square-nonnegative (a (* left right))))
                   :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-pc-disk-from-identity
   (implies (and (rationalp x) (rationalp y) (rationalp delta) (rationalp divisor)
                 (<= 16 divisor) (equal (+ (* x x) (* y y)) (* 16 delta delta divisor)))
            (lw-complex-diskp (cons x y) (* divisor (abs delta))))
   :hints (("Goal" :cases ((<= 0 delta)) :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-pc-raw-disk
   (implies (and (rationalp left) (rationalp right))
            (lw-complex-diskp
             (cons (* -8 (- left right) (+ left right)) (* 4 (- left right) (- 4 (* left right))))
             (* (lw-phase-denominator left) (lw-phase-denominator right) (abs (- left right)))))
   :hints (("Goal" :use (lw-pc-raw-norm-identity lw-pc-denominator-product
                         (:instance lw-pc-disk-from-identity
                           (x (* -8 (- left right) (+ left right)))
                           (y (* 4 (- left right) (- 4 (* left right))))
                           (delta (- left right))
                           (divisor (* (lw-phase-denominator left) (lw-phase-denominator right)))))
                   :in-theory (disable lw-complex-diskp lw-phase-denominator
                                       distributivity lw-pc-left-distribute
                                       lw-complex-disk-enlarge lw-disk-enlarge)))
   :rule-classes nil))

(defthm lw-phase-rotation-lipschitz
  (implies (and (rationalp left) (rationalp right))
           (lw-complex-diskp (lw-complex-sub (lw-phase-rotation left) (lw-phase-rotation right))
                             (abs (- left right))))
  :hints (("Goal" :use (lw-pc-rotation-difference lw-pc-raw-disk
                        (:instance lw-pc-normalize
                          (point (cons (* -8 (- left right) (+ left right))
                                       (* 4 (- left right) (- 4 (* left right)))))
                          (divisor (* (lw-phase-denominator left) (lw-phase-denominator right)))
                          (radius (abs (- left right)))))
                  :in-theory (disable lw-phase-rotation lw-phase-denominator lw-complex-sub
                                      lw-complex-scale lw-complex-diskp
                                      lw-complex-disk-enlarge lw-disk-enlarge)
                  :nonlinearp t)))

(local
 (defthm lw-pc-scale-distance
   (implies (and (rationalp left) (rationalp right) (rationalp steps) (< 0 steps))
            (equal (* steps (abs (- (/ left steps) (/ right steps)))) (abs (- left right))))
   :hints (("Goal" :use ((:instance inverse-of-* (x steps)))
                   :in-theory (disable inverse-of-*) :cases ((<= right left)) :nonlinearp t))))

(defthm lw-phase-grid-lipschitz
  (implies (and (rationalp left) (rationalp right) (posp steps))
           (lw-complex-diskp (lw-complex-sub (lw-phase-grid left steps) (lw-phase-grid right steps))
                             (abs (- left right))))
  :hints (("Goal" :use (lw-pc-scale-distance
                        (:instance lw-phase-rotation-lipschitz (left (/ left steps)) (right (/ right steps)))
                        (:instance lw-complex-power-difference
                          (left (lw-phase-rotation (/ left steps)))
                          (right (lw-phase-rotation (/ right steps)))
                          (index steps) (error (abs (- (/ left steps) (/ right steps))))))
                  :in-theory (disable lw-phase-rotation lw-complex-power lw-complex-sub lw-complex-diskp
                                      lw-phase-rotation-lipschitz lw-complex-power-difference
                                      lw-complex-disk-enlarge lw-disk-enlarge))))

(defthm lw-phase-grid-transport
  (implies (and (rationalp left) (rationalp right) (posp left-steps) (posp right-steps))
           (lw-complex-diskp
            (lw-complex-sub (lw-phase-grid left left-steps) (lw-phase-grid right right-steps))
            (+ (abs (- left right)) (/ (* left left) left-steps) (/ (* right right) right-steps))))
  :hints (("Goal"
           :use ((:instance lw-phase-grid-refinement (value left) (steps left-steps) (factor right-steps))
                 (:instance lw-phase-grid-refinement (value right) (steps right-steps) (factor left-steps))
                 (:instance lw-phase-grid-lipschitz (steps (* left-steps right-steps)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-phase-grid right right-steps))
                   (right (lw-phase-grid right (* left-steps right-steps)))
                   (radius (/ (* right right) right-steps)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-phase-grid left left-steps))
                   (middle (lw-phase-grid left (* left-steps right-steps)))
                   (right (lw-phase-grid right (* left-steps right-steps)))
                   (radius (/ (* left left) left-steps)) (other-radius (abs (- left right))))
                 (:instance lw-complex-difference-triangle
                   (left (lw-phase-grid left left-steps))
                   (middle (lw-phase-grid right (* left-steps right-steps)))
                   (right (lw-phase-grid right right-steps))
                   (radius (+ (/ (* left left) left-steps) (abs (- left right))))
                   (other-radius (/ (* right right) right-steps))))
           :in-theory (disable lw-phase-grid lw-complex-sub lw-complex-diskp lw-complexp
                               lw-phase-grid-refinement lw-phase-grid-lipschitz lw-complex-difference-triangle
                               lw-complex-disk-enlarge lw-disk-enlarge)
           :nonlinearp t)))

(defthm lw-phase-value-transport
  (implies (and (rationalp left) (rationalp right)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp (lw-complex-sub (lw-phase-value left left-error) (lw-phase-value right right-error))
                             (+ (abs (- left right)) (/ left-error 2) (/ right-error 2))))
  :hints (("Goal"
           :use ((:instance lw-phase-grid-transport
                   (left-steps (lw-phase-steps left left-error)) (right-steps (lw-phase-steps right right-error)))
                 (:instance lw-phase-steps-adequate (value left) (error left-error))
                 (:instance lw-phase-steps-adequate (value right) (error right-error))
                 (:instance lw-positive-division-bound (numerator (* left left))
                   (divisor (lw-phase-steps left left-error)) (bound (/ left-error 2)))
                 (:instance lw-positive-division-bound (numerator (* right right))
                   (divisor (lw-phase-steps right right-error)) (bound (/ right-error 2)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-phase-value left left-error) (lw-phase-value right right-error)))
                   (radius (+ (abs (- left right))
                              (/ (* left left) (lw-phase-steps left left-error))
                              (/ (* right right) (lw-phase-steps right right-error))))
                   (cap (+ (abs (- left right)) (/ left-error 2) (/ right-error 2)))))
           :in-theory (disable lw-phase-grid lw-phase-steps lw-complex-sub lw-complex-diskp
                               lw-phase-grid-transport lw-phase-steps-adequate
                               lw-complex-disk-enlarge lw-disk-enlarge)
           :nonlinearp t)))

(assert-event
 (and (lw-complex-diskp (lw-complex-sub (lw-phase-rotation -3/2) (lw-phase-rotation 2/3)) 13/6)
      (lw-complex-diskp (lw-complex-sub (lw-phase-grid -1/2 3) (lw-phase-grid 1/3 3)) 5/6)
      (lw-complex-diskp (lw-complex-sub (lw-phase-value 1/2 1/4) (lw-phase-value 1/3 1/5))
                        (+ 1/6 1/8 1/10))))
