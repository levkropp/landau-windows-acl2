(in-package "ACL2")

(include-book "complex-exp-moment-grid")
(include-book "rational-window")

; Computed quadrature for u*exp(point*u), including every mesh and
; evaluation error. The endpoint expression is derived by telescoping.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-norm-square
                 lw-complex-exp-value lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-exp-moment-grid lw-complex-exp-moment-primitive
                 lw-complex-exp-moment-step-budget lw-complex-exp-moment-grid-budget
                 lw-complex-exp-uniform-cap lw-complex-exp-grid-step-budget
                 lw-exp-bounds lw-exp-lipschitz-cap lw-precision-fuel
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cemq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cemq-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cemq-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-cemq-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cemq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cemq-cancel-equality
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
                       (equal (* factor a) (* factor b))) (equal a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cemq-inverse-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b))
                  (equal (/ (* a b)) (* (/ a) (/ b))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x a)) (:instance inverse-of-* (x b))
                        (:instance inverse-of-* (x (* a b)))
                        (:instance lw-cemq-cancel-equality (factor (* a b))
                          (a (/ (* a b))) (b (* (/ a) (/ b)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t))))
(local (defthm lw-cemq-fuel-natural
         (natp (lw-precision-fuel width error))
         :hints (("Goal" :in-theory (enable lw-precision-fuel)))
         :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-cemq-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cemq-left-commutes)))))


(defun lw-complex-exp-moment-amplification (start length clearance)
  (+ start length (/ clearance)))

(defun lw-complex-exp-moment-argument-cap (point start length)
  (* (lw-complex-l1 point) (+ start length)))

(defun lw-complex-exp-moment-geometric-cost (point start length clearance)
  (* (lw-complex-exp-uniform-cap (lw-complex-exp-moment-argument-cap point start length))
     (+ (* (lw-complex-exp-moment-amplification start length clearance)
           (lw-complex-l1 point) (lw-complex-l1 point))
        (lw-complex-l1 point))))

(defun lw-complex-exp-moment-evaluation-cost (point start length clearance)
  (* (lw-complex-exp-moment-amplification start length clearance)
     (+ (lw-complex-exp-uniform-cap 1)
        (* 2 (lw-complex-exp-uniform-cap
               (lw-complex-exp-moment-argument-cap point start length))) 2)))

(defun lw-complex-exp-moment-integration-count (point start length clearance error)
  (+ 2 (lw-precision-fuel (* (lw-complex-l1 point) length) 1)
     (lw-precision-fuel
       (* 4 (lw-complex-exp-moment-geometric-cost point start length clearance) length length)
       (* clearance error))))

(defun lw-complex-exp-moment-integration-step (point start length clearance error)
  (/ length (lw-complex-exp-moment-integration-count point start length clearance error)))

(defun lw-complex-exp-moment-endpoint-error (start length clearance error)
  (/ (* clearance error) (* 16 (lw-complex-exp-moment-amplification start length clearance))))

(defun lw-complex-exp-moment-integration-error (point start length clearance error)
  (min (lw-complex-exp-moment-endpoint-error start length clearance error)
       (/ (* clearance error)
          (* 16 (lw-complex-exp-moment-integration-count point start length clearance error)
             (lw-complex-exp-moment-evaluation-cost point start length clearance)))))

(defun lw-complex-exp-moment-integral-value (point start length clearance error)
  (lw-complex-exp-moment-primitive point start (+ start length)
    (lw-complex-exp-moment-endpoint-error start length clearance error)))

(defun lw-complex-exp-moment-integral-grid (point start length clearance error)
  (lw-complex-exp-moment-grid point start
    (lw-complex-exp-moment-integration-step point start length clearance error)
    (lw-complex-exp-moment-integration-count point start length clearance error)
    (lw-complex-exp-moment-integration-error point start length clearance error)))

(defthm lw-complex-exp-moment-integration-count-natural
  (posp (lw-complex-exp-moment-integration-count point start length clearance error))
  :rule-classes (:rewrite :type-prescription))

(local (defthm lw-cemq-scalar-budget
         (implies
          (and (rationalp mass) (<= 0 mass) (rationalp cap) (<= 0 cap)
               (rationalp weight) (< 0 weight) (rationalp amplification) (< 0 amplification)
               (rationalp length) (< 0 length) (posp count)
               (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error)
               (<= (* mass length) count)
               (<= (* 4 cap length length) (* count clearance error)))
          (let* ((step (/ length count))
                 (endpoint-error (/ (* clearance error) (* 16 amplification)))
                 (point-error (min endpoint-error
                                   (/ (* clearance error) (* 16 count weight)))))
            (and (rationalp step) (< 0 step) (equal (* count step) length)
                 (<= (* mass step) 1)
                 (rationalp endpoint-error) (< 0 endpoint-error)
                 (rationalp point-error) (< 0 point-error)
                 (<= point-error endpoint-error)
                 (<= (* count (+ (* cap step step) (* weight point-error))
                        (/ clearance)) (* 1/2 error))
                 (<= (* 2 amplification (+ point-error endpoint-error) (/ clearance))
                     (* 1/4 error)))))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x count))
                        (:instance inverse-of-* (x clearance))
                        (:instance inverse-of-* (x weight))
                        (:instance inverse-of-* (x amplification))
                        (:instance lw-cemq-multiply-order
                          (a (min (/ (* clearance error) (* 16 amplification))
                                  (/ (* clearance error) (* 16 count weight))))
                          (b (/ (* clearance error) (* 16 count weight)))
                          (factor (* count weight (/ clearance))))
                        (:instance lw-cemq-multiply-order
                          (a (min (/ (* clearance error) (* 16 amplification))
                                  (/ (* clearance error) (* 16 count weight))))
                          (b (/ (* clearance error) (* 16 amplification)))
                          (factor (* 2 amplification (/ clearance))))
                        (:instance lw-positive-division-bound
                          (numerator (* mass length)) (divisor count) (bound 1))
                        (:instance lw-positive-division-bound
                          (numerator (* cap length length))
                          (divisor (* count clearance)) (bound (* 1/4 error))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cemq-cost-data
         (implies (and (rationalp mass) (<= 0 mass) (rationalp cap) (<= 1 cap)
                       (rationalp base-cap) (<= 1 base-cap)
                       (rationalp amplification) (< 0 amplification))
                  (and (rationalp (* cap (+ (* amplification mass mass) mass)))
                       (<= 0 (* cap (+ (* amplification mass mass) mass)))
                       (rationalp (* amplification (+ base-cap (* 2 cap) 2)))
                       (< 0 (* amplification (+ base-cap (* 2 cap) 2)))))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-complex-exp-moment-integration-parameters
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp length) (< 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (let ((count (lw-complex-exp-moment-integration-count point start length clearance error))
         (step (lw-complex-exp-moment-integration-step point start length clearance error))
         (argument-cap (lw-complex-exp-moment-argument-cap point start length))
         (endpoint-error (lw-complex-exp-moment-endpoint-error start length clearance error))
         (point-error (lw-complex-exp-moment-integration-error point start length clearance error)))
     (and (posp count) (rationalp step) (< 0 step) (equal (* count step) length)
          (rationalp argument-cap) (<= 0 argument-cap)
          (<= (* (lw-complex-l1 point) step) 1)
          (rationalp endpoint-error) (< 0 endpoint-error)
          (rationalp point-error) (< 0 point-error)
          (<= (lw-complex-exp-moment-grid-budget
                point step (+ start length) argument-cap count clearance point-error)
              (* 1/2 error))
          (<= (* 2 (lw-complex-exp-moment-amplification start length clearance)
                 (+ point-error endpoint-error) (/ clearance)) (* 1/4 error)))))
  :hints (("Goal"
           :use ((:instance lw-complex-l1-bound)
                 (:instance lw-complex-exp-uniform-cap-data
                   (argument-cap (lw-complex-exp-moment-argument-cap point start length)))
                 (:instance lw-complex-exp-uniform-cap-data (argument-cap 1))
                 (:instance lw-cemq-product-nonnegative
                   (a (lw-complex-l1 point)) (b (+ start length)))
                 (:instance lw-cemq-cost-data
                   (mass (lw-complex-l1 point))
                   (cap (lw-complex-exp-uniform-cap
                          (lw-complex-exp-moment-argument-cap point start length)))
                   (base-cap (lw-complex-exp-uniform-cap 1))
                   (amplification (lw-complex-exp-moment-amplification start length clearance)))
                 (:instance lw-precision-fuel-adequate
                   (width (* (lw-complex-l1 point) length)) (epsilon 1))
                 (:instance lw-precision-fuel-adequate
                   (width (* 4 (lw-complex-exp-moment-geometric-cost point start length clearance)
                             length length))
                   (epsilon (* clearance error)))
                 (:instance lw-cemq-scalar-budget
                   (mass (lw-complex-l1 point))
                   (cap (lw-complex-exp-moment-geometric-cost point start length clearance))
                   (weight (lw-complex-exp-moment-evaluation-cost point start length clearance))
                   (amplification (lw-complex-exp-moment-amplification start length clearance))
                   (count (lw-complex-exp-moment-integration-count point start length clearance error))))
           :in-theory
           (e/d (lw-complex-exp-grid-step-budget lw-complex-exp-moment-step-budget
                 lw-complex-exp-moment-grid-budget)
                (lw-complex-l1-bound lw-complex-exp-uniform-cap-data lw-precision-fuel-adequate))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory
        (disable lw-complex-exp-moment-integration-count lw-complex-exp-moment-integration-step
                 lw-complex-exp-moment-integration-error lw-complex-exp-moment-evaluation-cost
                 lw-complex-exp-moment-geometric-cost)))

(defthm lw-complex-exp-moment-integral-value-rational
  (implies (and (lw-complexp point) (rationalp start) (<= 0 start)
                (rationalp length) (< 0 length)
                (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-moment-integral-value point start length clearance error)))
  :hints (("Goal" :nonlinearp t)))

(local (defthm lw-cemq-endpoint-budget-identity
         (implies (and (rationalp clearance) (< 0 clearance)
                       (rationalp amplification) (< 0 amplification)
                       (rationalp left-error) (rationalp right-error))
                  (equal
                   (* 2 amplification
                      (+ (/ (* clearance left-error) (* 16 amplification))
                         (/ (* clearance right-error) (* 16 amplification)))
                      (/ clearance))
                   (* 1/8 (+ left-error right-error))))
         :hints (("Goal" :use ((:instance inverse-of-* (x clearance))
                              (:instance inverse-of-* (x amplification)))
                         :in-theory (disable inverse-of-*) :nonlinearp nil))
         :rule-classes nil))

(defthm lw-complex-exp-moment-integral-value-cauchy
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp length) (< 0 length)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
   (lw-complex-diskp
    (lw-complex-sub
      (lw-complex-exp-moment-integral-value point start length clearance left-error)
      (lw-complex-exp-moment-integral-value point start length clearance right-error))
    (* 1/8 (+ left-error right-error))))
  :hints (("Goal"
           :use ((:instance lw-cemq-endpoint-budget-identity
                   (amplification (+ start length (/ clearance))))
                 (:instance lw-complex-exp-moment-primitive-cauchy
                   (end (+ start length)) (bound (+ start length))
                   (left-error (lw-complex-exp-moment-endpoint-error start length clearance left-error))
                   (right-error (lw-complex-exp-moment-endpoint-error start length clearance right-error))))
           :in-theory (disable lw-complex-exp-moment-primitive-cauchy)
           :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-moment-computed-quadrature
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start)
        (rationalp length) (< 0 length)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub (lw-complex-exp-moment-integral-value point start length clearance error)
                    (lw-complex-exp-moment-integral-grid point start length clearance error))
    error))
  :hints (("Goal"
           :use (lw-complex-exp-moment-integration-parameters
                 (:instance lw-complex-exp-moment-grid-primitive-error
                   (bound (+ start length))
                   (step (lw-complex-exp-moment-integration-step point start length clearance error))
                   (count (lw-complex-exp-moment-integration-count point start length clearance error))
                   (argument-cap (lw-complex-exp-moment-argument-cap point start length))
                   (error (lw-complex-exp-moment-integration-error point start length clearance error)))
                 (:instance lw-complex-exp-moment-primitive-cauchy
                   (end (+ start length)) (bound (+ start length))
                   (left-error (lw-complex-exp-moment-endpoint-error start length clearance error))
                   (right-error (lw-complex-exp-moment-integration-error point start length clearance error)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-exp-moment-primitive point start (+ start length)
                           (lw-complex-exp-moment-endpoint-error start length clearance error)))
                   (middle (lw-complex-exp-moment-primitive point start (+ start length)
                             (lw-complex-exp-moment-integration-error point start length clearance error)))
                   (right (lw-complex-exp-moment-integral-grid point start length clearance error))
                   (radius (* 2 (lw-complex-exp-moment-amplification start length clearance)
                              (+ (lw-complex-exp-moment-endpoint-error start length clearance error)
                                 (lw-complex-exp-moment-integration-error
                                   point start length clearance error)) (/ clearance)))
                   (other-radius
                     (lw-complex-exp-moment-grid-budget point
                       (lw-complex-exp-moment-integration-step point start length clearance error)
                       (+ start length) (lw-complex-exp-moment-argument-cap point start length)
                       (lw-complex-exp-moment-integration-count point start length clearance error)
                       clearance (lw-complex-exp-moment-integration-error point start length clearance error))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-moment-integral-value point start length clearance error)
                     (lw-complex-exp-moment-integral-grid point start length clearance error)))
                   (radius
                     (+ (* 2 (lw-complex-exp-moment-amplification start length clearance)
                           (+ (lw-complex-exp-moment-endpoint-error start length clearance error)
                              (lw-complex-exp-moment-integration-error
                                point start length clearance error)) (/ clearance))
                        (lw-complex-exp-moment-grid-budget point
                          (lw-complex-exp-moment-integration-step point start length clearance error)
                          (+ start length) (lw-complex-exp-moment-argument-cap point start length)
                          (lw-complex-exp-moment-integration-count point start length clearance error)
                          clearance
                          (lw-complex-exp-moment-integration-error point start length clearance error))))
                   (cap error)))
           :in-theory (disable lw-complex-exp-moment-integration-parameters
                               lw-complex-exp-moment-grid-primitive-error
                               lw-complex-exp-moment-primitive-cauchy
                               lw-complex-difference-triangle)
           :nonlinearp nil :do-not-induct t)))

