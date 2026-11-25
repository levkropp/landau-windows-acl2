(in-package "ACL2")

(include-book "complex-exp-grid")
(include-book "rational-window")

; Choose the grid count and point precision, rather than assuming a fine
; grid. The endpoint primitive and the evaluated finite rectangle sum
; then agree within the requested positive rational error.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-norm-square
                 lw-complex-exp-value lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-exp-uniform-cap lw-complex-exp-grid-step-budget
                 lw-exp-bounds lw-exp-lipschitz-cap lw-precision-fuel
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-ceq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-ceq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ceq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-ceq-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-ceq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-ceq-cancel-equality
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
                       (equal (* factor a) (* factor b))) (equal a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-ceq-inverse-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b))
                  (equal (/ (* a b)) (* (/ a) (/ b))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
                        (:instance inverse-of-* (x (* a b)))
                        (:instance lw-ceq-cancel-equality (factor (* a b))
                          (a (/ (* a b))) (b (* (/ a) (/ b)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))))
(local (defthm lw-ceq-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-ceq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ceq-left-commutes)))))

(defun lw-complex-exp-integration-argument-cap (point start length)
  (* (lw-complex-l1 point) (+ start length)))

(defun lw-complex-exp-integration-weight (point start length)
  (+ (lw-complex-exp-uniform-cap 1)
     (* 2 (lw-complex-exp-uniform-cap
            (lw-complex-exp-integration-argument-cap point start length))) 2))

(defun lw-complex-exp-integration-count (point start length clearance error)
  (+ 2 (lw-precision-fuel (* (lw-complex-l1 point) length) 1)
     (lw-precision-fuel
       (* 4 (lw-complex-exp-uniform-cap
              (lw-complex-exp-integration-argument-cap point start length))
          (lw-complex-l1 point) (lw-complex-l1 point) length length)
       (* clearance error))))

(defun lw-complex-exp-integration-step (point start length clearance error)
  (/ length (lw-complex-exp-integration-count point start length clearance error)))

(defun lw-complex-exp-integration-error (point start length clearance error)
  (min (* 1/16 clearance error)
       (/ (* clearance error)
          (* 16 (lw-complex-exp-integration-count point start length clearance error)
             (lw-complex-exp-integration-weight point start length)))))

(defun lw-complex-exp-integral-value (point start length clearance error)
  (lw-complex-exp-primitive-value point start (+ start length) (* 1/16 clearance error)))

(defun lw-complex-exp-integral-grid (point start length clearance error)
  (lw-complex-exp-grid point start
    (lw-complex-exp-integration-step point start length clearance error)
    (lw-complex-exp-integration-count point start length clearance error)
    (lw-complex-exp-integration-error point start length clearance error)))

(defthm lw-complex-exp-integration-count-natural
  (posp (lw-complex-exp-integration-count point start length clearance error))
  :rule-classes (:rewrite :type-prescription))

(local (defthm lw-ceq-scalar-budget
         (implies
          (and (rationalp mass) (<= 0 mass) (rationalp cap) (<= 1 cap)
               (rationalp weight) (<= 1 weight)
               (rationalp length) (< 0 length) (posp count)
               (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error)
               (<= (* mass length) count)
               (<= (* 4 cap mass mass length length) (* count clearance error)))
          (let ((step (/ length count))
                (point-error (min (* 1/16 clearance error)
                                  (/ (* clearance error) (* 16 count weight)))))
            (and (rationalp step) (< 0 step) (equal (* count step) length)
                 (<= (* mass step) 1)
                 (rationalp point-error) (< 0 point-error)
                 (<= point-error (* 1/16 clearance error))
                 (<= (* count (+ (* cap mass mass step step) (* weight point-error))
                        (/ clearance)) (* 1/2 error))
                 (<= (* 2 (+ point-error (* 1/16 clearance error)) (/ clearance)) (* 1/4 error)))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x count))
                        (:instance inverse-of-* (x clearance))
                        (:instance inverse-of-* (x weight))
                        (:instance lw-ceq-multiply-order
                          (a (min (* 1/16 clearance error)
                                  (/ (* clearance error) (* 16 count weight))))
                          (b (/ (* clearance error) (* 16 count weight)))
                          (factor (* count weight (/ clearance))))
                        (:instance lw-ceq-multiply-order
                          (a (min (* 1/16 clearance error)
                                  (/ (* clearance error) (* 16 count weight))))
                          (b (* 1/16 clearance error)) (factor (* 2 (/ clearance))))
                        (:instance lw-positive-division-bound
                          (numerator (* mass length)) (divisor count) (bound 1))
                        (:instance lw-positive-division-bound
                          (numerator (* cap mass mass length length))
                          (divisor (* count clearance)) (bound (* 1/4 error))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-complex-exp-integration-parameters
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp length) (< 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (let ((count (lw-complex-exp-integration-count point start length clearance error))
         (step (lw-complex-exp-integration-step point start length clearance error))
         (argument-cap (lw-complex-exp-integration-argument-cap point start length))
         (point-error (lw-complex-exp-integration-error point start length clearance error)))
     (and (posp count) (rationalp step) (< 0 step) (equal (* count step) length)
          (rationalp argument-cap) (<= 0 argument-cap)
          (<= (* (lw-complex-l1 point) step) 1)
          (rationalp point-error) (< 0 point-error)
          (<= (* count (lw-complex-exp-grid-step-budget point step argument-cap point-error)
                 (/ clearance)) (* 1/2 error))
          (<= (* 2 (+ point-error (* 1/16 clearance error)) (/ clearance)) (* 1/4 error)))))
  :hints (("Goal"
           :use ((:instance lw-complex-l1-bound)
                 (:instance lw-complex-exp-uniform-cap-data
                   (argument-cap (lw-complex-exp-integration-argument-cap point start length)))
                 (:instance lw-complex-exp-uniform-cap-data (argument-cap 1))
                 (:instance lw-precision-fuel-adequate
                   (width (* (lw-complex-l1 point) length)) (epsilon 1))
                 (:instance lw-precision-fuel-adequate
                   (width (* 4 (lw-complex-exp-uniform-cap
                                  (lw-complex-exp-integration-argument-cap point start length))
                             (lw-complex-l1 point) (lw-complex-l1 point) length length))
                   (epsilon (* clearance error)))
                 (:instance lw-ceq-scalar-budget
                   (mass (lw-complex-l1 point))
                   (cap (lw-complex-exp-uniform-cap
                          (lw-complex-exp-integration-argument-cap point start length)))
                   (weight (lw-complex-exp-integration-weight point start length))
                   (count (lw-complex-exp-integration-count point start length clearance error))))
           :in-theory
           (e/d (lw-complex-exp-grid-step-budget)
                (lw-complex-l1-bound lw-complex-exp-uniform-cap-data lw-precision-fuel-adequate))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory
        (disable lw-complex-exp-integration-count lw-complex-exp-integration-step
                 lw-complex-exp-integration-error lw-complex-exp-integration-weight)))

(defthm lw-complex-exp-integral-value-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp length)
                (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-integral-value point start length clearance error)))
  :hints (("Goal" :nonlinearp t)))

(defthm lw-complex-exp-integral-value-cauchy
  (implies
   (and (lw-complexp point) (rationalp start) (rationalp length)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
   (lw-complex-diskp
    (lw-complex-sub
      (lw-complex-exp-integral-value point start length clearance left-error)
      (lw-complex-exp-integral-value point start length clearance right-error))
    (* 1/8 (+ left-error right-error))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-primitive-cauchy (end (+ start length))
                   (left-error (* 1/16 clearance left-error))
                   (right-error (* 1/16 clearance right-error))))
           :in-theory (disable lw-complex-exp-primitive-cauchy)
           :nonlinearp t :do-not-induct t)))

(defthm lw-complex-exp-computed-quadrature
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp length) (< 0 length)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-exp-integral-value point start length clearance error)
                    (lw-complex-exp-integral-grid point start length clearance error))
    error))
  :hints (("Goal"
           :use (lw-complex-exp-integration-parameters
                 (:instance lw-complex-exp-grid-primitive-error
                   (bound (+ start length))
                   (step (lw-complex-exp-integration-step point start length clearance error))
                   (count (lw-complex-exp-integration-count point start length clearance error))
                   (argument-cap (lw-complex-exp-integration-argument-cap point start length))
                   (error (lw-complex-exp-integration-error point start length clearance error)))
                 (:instance lw-complex-exp-primitive-cauchy (end (+ start length))
                   (left-error (* 1/16 clearance error))
                   (right-error (lw-complex-exp-integration-error point start length clearance error)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-exp-primitive-value point start (+ start length)
                           (* 1/16 clearance error)))
                   (middle (lw-complex-exp-primitive-value point start (+ start length)
                             (lw-complex-exp-integration-error point start length clearance error)))
                   (right (lw-complex-exp-integral-grid point start length clearance error))
                   (radius (* 2 (+ (* 1/16 clearance error)
                                    (lw-complex-exp-integration-error
                                      point start length clearance error)) (/ clearance)))
                   (other-radius
                     (* (lw-complex-exp-integration-count point start length clearance error)
                        (lw-complex-exp-grid-step-budget point
                          (lw-complex-exp-integration-step point start length clearance error)
                          (lw-complex-exp-integration-argument-cap point start length)
                          (lw-complex-exp-integration-error point start length clearance error))
                        (/ clearance))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-integral-value point start length clearance error)
                     (lw-complex-exp-integral-grid point start length clearance error)))
                   (radius
                     (+ (* 2 (+ (* 1/16 clearance error)
                                 (lw-complex-exp-integration-error
                                   point start length clearance error)) (/ clearance))
                        (* (lw-complex-exp-integration-count point start length clearance error)
                           (lw-complex-exp-grid-step-budget point
                             (lw-complex-exp-integration-step point start length clearance error)
                             (lw-complex-exp-integration-argument-cap point start length)
                             (lw-complex-exp-integration-error point start length clearance error))
                           (/ clearance))))
                   (cap error)))
           :in-theory (disable lw-complex-exp-integration-parameters
                               lw-complex-exp-grid-primitive-error lw-complex-exp-primitive-cauchy
                               lw-complex-difference-triangle)
           :do-not-induct t)))
