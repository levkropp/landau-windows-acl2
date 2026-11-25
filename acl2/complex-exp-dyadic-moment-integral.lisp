(in-package "ACL2")

(include-book "complex-exp-dyadic-moment-grid")
(include-book "complex-exp-moment-integral")
(include-book "complex-exp-dyadic-integral")

; Computed clipped first-moment quadrature. The mesh budget controls
; both weighted and unweighted residuals; evaluation errors have their
; own common precision, separate from the endpoint precision.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-norm-square
                 lw-complex-exp-value lw-complex-exp-primitive-value lw-complex-exp-moment-primitive
                 lw-complex-exp-clipped-dyadic lw-complex-exp-clipped-primitive
                 lw-complex-exp-clipped-primitive-endpoint
                 lw-complex-exp-clipped-moment-dyadic lw-complex-exp-clipped-moment-primitive
                 lw-complex-exp-clipped-moment-primitive-endpoint
                 lw-complex-exp-grid-step-budget lw-complex-exp-moment-step-budget lw-complex-exp-moment-grid-budget
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-exp-bounds
                 lw-complex-exp-moment-amplification lw-complex-exp-moment-argument-cap
                 lw-complex-exp-moment-geometric-cost lw-complex-exp-moment-evaluation-cost
                 lw-complex-exp-dyadic-target lw-dyadic-leaf-count lw-halved-width lw-halving-depth lw-precision-fuel
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cmi-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cmi-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cmi-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-cmi-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cmi-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-cmi-left-commutes)))))
(local (defthm lw-cmi-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cmi-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cmi-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cmi-mesh-scale
         (implies (and (rationalp width) (rationalp factor))
                  (equal (lw-halved-width (* factor width) depth) (* factor (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))
(local (defthm lw-cmi-mesh-data
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth))
                       (<= 0 (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))


(defun lw-complex-exp-dyadic-moment-slope (point start length clearance)
  (+ (lw-complex-l1 point) (* (lw-complex-exp-moment-geometric-cost point start length clearance) length)))

(defun lw-complex-exp-dyadic-moment-depth (point start length clearance error)
  (let ((width (* length (lw-complex-exp-dyadic-moment-slope point start length clearance)))
        (target (lw-complex-exp-dyadic-target clearance error)))
    (lw-halving-depth width target (lw-precision-fuel width target))))

(defun lw-complex-exp-dyadic-moment-endpoint-error (start length clearance error)
  (/ (* clearance error) (* 16 (+ 1 (lw-complex-exp-moment-amplification start length clearance)))))

(defun lw-complex-exp-dyadic-moment-error (point start length clearance error)
  (min (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error)
       (/ (* clearance error)
          (* 16 (+ 1 (* (lw-dyadic-leaf-count
                         (lw-complex-exp-dyadic-moment-depth point start length clearance error))
                        (lw-complex-exp-moment-evaluation-cost point start length clearance)))))))

(defun lw-complex-exp-dyadic-moment-integral-grid (point start length cutpoint clearance error)
  (lw-complex-exp-clipped-moment-dyadic
   point start (+ start length) (lw-complex-exp-dyadic-moment-depth point start length clearance error) cutpoint
   (lw-complex-exp-dyadic-moment-error point start length clearance error)))

(defun lw-complex-exp-dyadic-moment-integral-value (point start length cutpoint clearance error)
  (lw-complex-exp-clipped-moment-primitive point start (+ start length) cutpoint
                                         (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error)))

(local (defthm lw-cmi-cost-data
         (implies (and (rationalp mass) (<= 0 mass) (rationalp cap) (<= 1 cap)
                       (rationalp base-cap) (<= 1 base-cap)
                       (rationalp amplification) (< 0 amplification))
                  (and (rationalp (* cap (+ (* amplification mass mass) mass)))
                       (<= 0 (* cap (+ (* amplification mass mass) mass)))
                       (rationalp (* amplification (+ base-cap (* 2 cap) 2)))
                       (< 0 (* amplification (+ base-cap (* 2 cap) 2)))))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))


(local (defthm lw-cmi-costs-valid
         (implies
          (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
               (rationalp clearance) (< 0 clearance))
          (and (rationalp (lw-complex-exp-moment-argument-cap point start length))
               (<= 0 (lw-complex-exp-moment-argument-cap point start length))
               (rationalp (lw-complex-exp-moment-amplification start length clearance))
               (< 0 (lw-complex-exp-moment-amplification start length clearance))
               (rationalp (lw-complex-exp-moment-geometric-cost point start length clearance))
               (<= 0 (lw-complex-exp-moment-geometric-cost point start length clearance))
               (rationalp (lw-complex-exp-moment-evaluation-cost point start length clearance))
               (< 0 (lw-complex-exp-moment-evaluation-cost point start length clearance))))
         :hints (("Goal"
                  :use (lw-complex-l1-bound
                        (:instance lw-complex-exp-uniform-cap-data
                          (argument-cap (lw-complex-exp-moment-argument-cap point start length)))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap 1))
                        (:instance lw-cmi-nonnegative-product (a (lw-complex-l1 point)) (b (+ start length)))
                        (:instance lw-cmi-cost-data
                          (mass (lw-complex-l1 point))
                          (cap (lw-complex-exp-uniform-cap (lw-complex-exp-moment-argument-cap point start length)))
                          (base-cap (lw-complex-exp-uniform-cap 1))
                          (amplification (lw-complex-exp-moment-amplification start length clearance))))
                  :in-theory
                  (e/d (lw-complex-exp-moment-argument-cap lw-complex-exp-moment-amplification
                        lw-complex-exp-moment-geometric-cost lw-complex-exp-moment-evaluation-cost)
                       (lw-complex-l1-bound lw-complex-exp-uniform-cap-data))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmi-slope-data
         (implies
          (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
               (rationalp clearance) (< 0 clearance))
          (and (rationalp (lw-complex-exp-dyadic-moment-slope point start length clearance))
               (<= 0 (lw-complex-exp-dyadic-moment-slope point start length clearance))
               (<= (lw-complex-l1 point) (lw-complex-exp-dyadic-moment-slope point start length clearance))
               (<= (* (lw-complex-exp-moment-geometric-cost point start length clearance) length)
                   (lw-complex-exp-dyadic-moment-slope point start length clearance))))
         :hints (("Goal"
                  :use (lw-cmi-costs-valid lw-complex-l1-bound
                        (:instance lw-cmi-nonnegative-product
                          (a (lw-complex-exp-moment-geometric-cost point start length clearance)) (b length)))
                  :in-theory (e/d (lw-complex-exp-dyadic-moment-slope) (lw-complex-l1-bound))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmi-target-data
         (implies (and (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
                  (and (rationalp (lw-complex-exp-dyadic-target clearance error))
                       (< 0 (lw-complex-exp-dyadic-target clearance error))
                       (<= (lw-complex-exp-dyadic-target clearance error) 1)
                       (<= (lw-complex-exp-dyadic-target clearance error) (* 1/4 clearance error))))
         :hints (("Goal" :use ((:instance lw-cmi-positive-product (a clearance) (b error)))
                         :in-theory (enable lw-complex-exp-dyadic-target) :nonlinearp nil))
         :rule-classes nil))

(defthm lw-complex-exp-dyadic-moment-depth-adequate
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (let* ((depth (lw-complex-exp-dyadic-moment-depth point start length clearance error))
          (mesh (lw-halved-width length depth)))
     (and (natp depth) (<= (* (lw-complex-l1 point) mesh) 1)
          (<= (* (lw-complex-exp-moment-geometric-cost point start length clearance) length mesh)
              (* 1/4 clearance error)))))
  :hints (("Goal"
           :use (lw-cmi-costs-valid lw-cmi-slope-data lw-cmi-target-data lw-complex-l1-bound
                 (:instance lw-cmi-mesh-data
                   (width length) (depth (lw-complex-exp-dyadic-moment-depth point start length clearance error)))
                 (:instance lw-cmi-nonnegative-product
                   (a length) (b (lw-complex-exp-dyadic-moment-slope point start length clearance)))
                 (:instance lw-precision-fuel-adequate
                   (width (* length (lw-complex-exp-dyadic-moment-slope point start length clearance)))
                   (epsilon (lw-complex-exp-dyadic-target clearance error)))
                 (:instance lw-halving-depth-adequate
                   (width (* length (lw-complex-exp-dyadic-moment-slope point start length clearance)))
                   (epsilon (lw-complex-exp-dyadic-target clearance error))
                   (fuel (lw-precision-fuel (* length (lw-complex-exp-dyadic-moment-slope point start length clearance))
                                           (lw-complex-exp-dyadic-target clearance error))))
                 (:instance lw-cmi-mesh-scale
                   (width length) (factor (lw-complex-exp-dyadic-moment-slope point start length clearance))
                   (depth (lw-complex-exp-dyadic-moment-depth point start length clearance error)))
                 (:instance lw-cmi-multiply-order
                   (a (lw-complex-l1 point)) (b (lw-complex-exp-dyadic-moment-slope point start length clearance))
                   (factor (lw-halved-width length (lw-complex-exp-dyadic-moment-depth point start length clearance error))))
                 (:instance lw-cmi-multiply-order
                   (a (* (lw-complex-exp-moment-geometric-cost point start length clearance) length))
                   (b (lw-complex-exp-dyadic-moment-slope point start length clearance))
                   (factor (lw-halved-width length (lw-complex-exp-dyadic-moment-depth point start length clearance error)))))
           :in-theory (e/d (lw-complex-exp-dyadic-moment-depth)
                           (lw-complex-exp-dyadic-moment-slope lw-complex-l1-bound
                            lw-precision-fuel-adequate lw-halving-depth-adequate))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory
        (disable lw-complex-exp-dyadic-moment-slope lw-complex-exp-dyadic-moment-depth
                 lw-complex-exp-dyadic-moment-endpoint-error lw-complex-exp-dyadic-moment-error
                 lw-complex-exp-dyadic-moment-integral-grid lw-complex-exp-dyadic-moment-integral-value)))

(local (defthm lw-cmi-precision-scalar
         (implies (and (rationalp numerator) (< 0 numerator) (rationalp factor) (<= 0 factor))
                  (let ((delta (/ numerator (* 16 (+ 1 factor)))))
                    (and (rationalp delta) (< 0 delta) (<= delta (* 1/16 numerator))
                         (<= (* factor delta) (* 1/16 numerator)))))
         :hints (("Goal"
                  :use ((:instance lw-positive-division-bound
                          (numerator numerator) (divisor (* 16 (+ 1 factor))) (bound (* 1/16 numerator)))
                        (:instance lw-positive-division-bound
                          (numerator (* factor numerator)) (divisor (* 16 (+ 1 factor))) (bound (* 1/16 numerator))))
                  :nonlinearp t :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmi-endpoint-data
         (implies
          (and (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
               (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
          (let ((tau (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error)))
            (and (rationalp tau) (< 0 tau) (<= tau (* 1/16 clearance error))
                 (<= (* (lw-complex-exp-moment-amplification start length clearance) tau) (* 1/16 clearance error)))))
         :hints (("Goal"
                  :use ((:instance lw-cmi-positive-product (a clearance) (b error))
                        (:instance lw-cmi-precision-scalar
                          (numerator (* clearance error)) (factor (lw-complex-exp-moment-amplification start length clearance))))
                  :in-theory (enable lw-complex-exp-dyadic-moment-endpoint-error lw-complex-exp-moment-amplification)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmi-cauchy-budget
         (implies
          (and (rationalp amplification) (<= 0 amplification)
               (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error)
               (rationalp delta) (rationalp tau) (<= delta tau)
               (<= (* amplification tau) (* 1/16 clearance error)))
          (<= (* 2 amplification (+ delta tau) (/ clearance)) (* 1/4 error)))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x clearance))
                        (:instance lw-cmi-multiply-order (a delta) (b tau) (factor amplification))
                        (:instance lw-cmi-multiply-order
                          (a (+ (* amplification delta) (* amplification tau))) (b (* 1/8 clearance error))
                          (factor (* 2 (/ clearance)))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-complex-exp-dyadic-moment-error-valid
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (let ((tau (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error))
         (delta (lw-complex-exp-dyadic-moment-error point start length clearance error))
         (count (lw-dyadic-leaf-count (lw-complex-exp-dyadic-moment-depth point start length clearance error))))
     (and (rationalp tau) (< 0 tau) (<= tau (* 1/16 clearance error))
          (rationalp delta) (< 0 delta) (<= delta tau)
          (<= (* (lw-complex-exp-moment-amplification start length clearance) tau) (* 1/16 clearance error))
          (<= (* count (lw-complex-exp-moment-evaluation-cost point start length clearance) delta)
              (* 1/16 clearance error))
          (<= (* 2 (lw-complex-exp-moment-amplification start length clearance)
                 (+ delta tau) (/ clearance)) (* 1/4 error)))))
  :hints (("Goal"
           :use (lw-cmi-costs-valid lw-cmi-endpoint-data
                 (:instance lw-cmi-positive-product (a clearance) (b error))
                 (:instance lw-cmi-positive-product
                   (a (lw-dyadic-leaf-count (lw-complex-exp-dyadic-moment-depth point start length clearance error)))
                   (b (lw-complex-exp-moment-evaluation-cost point start length clearance)))
                 (:instance lw-cmi-precision-scalar
                   (numerator (* clearance error))
                   (factor (* (lw-dyadic-leaf-count (lw-complex-exp-dyadic-moment-depth point start length clearance error))
                              (lw-complex-exp-moment-evaluation-cost point start length clearance))))
                 (:instance lw-cmi-multiply-order
                   (a (lw-complex-exp-dyadic-moment-error point start length clearance error))
                   (b (/ (* clearance error)
                         (* 16 (+ 1 (* (lw-dyadic-leaf-count
                                        (lw-complex-exp-dyadic-moment-depth point start length clearance error))
                                       (lw-complex-exp-moment-evaluation-cost point start length clearance))))))
                   (factor (* (lw-dyadic-leaf-count
                               (lw-complex-exp-dyadic-moment-depth point start length clearance error))
                              (lw-complex-exp-moment-evaluation-cost point start length clearance))))
                 (:instance lw-cmi-cauchy-budget
                   (amplification (lw-complex-exp-moment-amplification start length clearance))
                   (delta (lw-complex-exp-dyadic-moment-error point start length clearance error))
                   (tau (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error))))
           :in-theory (enable lw-complex-exp-dyadic-moment-error) :nonlinearp nil :do-not-induct t)))

(local (defthm lw-cmi-multiply-equality
         (implies (equal a b) (equal (* a factor) (* b factor)))
         :rule-classes nil))

(local (defthm lw-cmi-total-budget
         (implies
          (and (rationalp count) (rationalp mesh) (rationalp length) (equal (* count mesh) length)
               (rationalp geometry) (rationalp weight) (rationalp delta)
               (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error)
               (<= (* geometry length mesh) (* 1/4 clearance error))
               (<= (* count weight delta) (* 1/16 clearance error)))
          (<= (* count (+ (* geometry mesh mesh) (* weight delta)) (/ clearance)) (* 1/2 error)))
         :hints (("Goal"
                  :use ((:instance lw-cmi-multiply-equality
                          (a (* count mesh)) (b length) (factor (* geometry mesh)))
                        (:instance lw-cmi-positive-product (a clearance) (b error))
                        (:instance inverse-of-* (x clearance))
                        (:instance lw-cmi-multiply-order
                          (a (+ (* geometry length mesh) (* count weight delta)))
                          (b (* 1/2 clearance error)) (factor (/ clearance))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmi-budget-form
         (equal
          (lw-complex-exp-moment-grid-budget
           point step (+ start length) (lw-complex-exp-moment-argument-cap point start length) count clearance error)
          (* count
             (+ (* (lw-complex-exp-moment-geometric-cost point start length clearance) step step)
                (* (lw-complex-exp-moment-evaluation-cost point start length clearance) error))
             (/ clearance)))
         :hints (("Goal"
                  :in-theory (enable lw-complex-exp-moment-grid-budget lw-complex-exp-moment-step-budget
                                     lw-complex-exp-grid-step-budget lw-complex-exp-moment-geometric-cost
                                     lw-complex-exp-moment-evaluation-cost lw-complex-exp-moment-amplification)
                  :do-not-induct t))))

(defthm lw-complex-exp-dyadic-moment-total-budget
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (<= (lw-complex-exp-moment-grid-budget
        point (lw-halved-width length (lw-complex-exp-dyadic-moment-depth point start length clearance error))
        (+ start length) (lw-complex-exp-moment-argument-cap point start length)
        (lw-dyadic-leaf-count (lw-complex-exp-dyadic-moment-depth point start length clearance error)) clearance
        (lw-complex-exp-dyadic-moment-error point start length clearance error))
       (* 1/2 error)))
  :hints (("Goal"
           :use (lw-cmi-costs-valid lw-complex-exp-dyadic-moment-depth-adequate lw-complex-exp-dyadic-moment-error-valid
                 (:instance lw-cmi-mesh-data
                   (width length) (depth (lw-complex-exp-dyadic-moment-depth point start length clearance error)))
                 (:instance lw-dyadic-leaf-count-mesh
                   (width length) (depth (lw-complex-exp-dyadic-moment-depth point start length clearance error)))
                 (:instance lw-cmi-total-budget
                   (count (lw-dyadic-leaf-count (lw-complex-exp-dyadic-moment-depth point start length clearance error)))
                   (mesh (lw-halved-width length (lw-complex-exp-dyadic-moment-depth point start length clearance error)))
                   (geometry (lw-complex-exp-moment-geometric-cost point start length clearance))
                   (weight (lw-complex-exp-moment-evaluation-cost point start length clearance))
                   (delta (lw-complex-exp-dyadic-moment-error point start length clearance error))))
           :in-theory (disable lw-complex-exp-dyadic-moment-depth-adequate lw-complex-exp-dyadic-moment-error-valid
                               lw-dyadic-leaf-count-mesh)
           :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-dyadic-moment-values-rational
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp cutpoint) (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (and (lw-complexp (lw-complex-exp-dyadic-moment-integral-grid point start length cutpoint clearance error))
        (lw-complexp (lw-complex-exp-dyadic-moment-integral-value point start length cutpoint clearance error))))
  :hints (("Goal"
           :use (lw-complex-exp-dyadic-moment-error-valid)
           :in-theory (e/d (lw-complex-exp-dyadic-moment-integral-grid lw-complex-exp-dyadic-moment-integral-value)
                           (lw-complex-exp-dyadic-moment-error-valid))
           :do-not-induct t)))

(defthm lw-complex-exp-clipped-computed-dyadic-moment-quadrature
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp cutpoint) (<= 0 cutpoint) (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point)) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-clipped-moment-primitive point start (+ start length) cutpoint
       (lw-complex-exp-dyadic-moment-error point start length clearance error))
     (lw-complex-exp-dyadic-moment-integral-grid point start length cutpoint clearance error))
    (* 1/2 error)))
  :hints (("Goal"
           :use (lw-cmi-costs-valid lw-complex-exp-dyadic-moment-depth-adequate
                 lw-complex-exp-dyadic-moment-error-valid lw-complex-exp-dyadic-moment-total-budget
                 (:instance lw-complex-exp-clipped-moment-dyadic-primitive-error
                   (end (+ start length)) (bound (+ start length))
                   (depth (lw-complex-exp-dyadic-moment-depth point start length clearance error))
                   (argument-cap (lw-complex-exp-moment-argument-cap point start length))
                   (error (lw-complex-exp-dyadic-moment-error point start length clearance error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-clipped-moment-primitive point start (+ start length) cutpoint
                       (lw-complex-exp-dyadic-moment-error point start length clearance error))
                     (lw-complex-exp-dyadic-moment-integral-grid point start length cutpoint clearance error)))
                   (radius (lw-complex-exp-moment-grid-budget
                     point (lw-halved-width length (lw-complex-exp-dyadic-moment-depth point start length clearance error))
                     (+ start length) (lw-complex-exp-moment-argument-cap point start length)
                     (lw-dyadic-leaf-count (lw-complex-exp-dyadic-moment-depth point start length clearance error)) clearance
                     (lw-complex-exp-dyadic-moment-error point start length clearance error)))
                   (cap (* 1/2 error))))
           :in-theory
           (e/d (lw-complex-exp-dyadic-moment-integral-grid lw-complex-exp-moment-argument-cap)
                (lw-complex-exp-dyadic-moment-depth-adequate lw-complex-exp-dyadic-moment-error-valid
                 lw-complex-exp-dyadic-moment-total-budget lw-complex-exp-clipped-moment-dyadic-primitive-error))
           :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-clipped-computed-dyadic-moment-endpoint
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp cutpoint) (<= 0 cutpoint) (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point)) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-dyadic-moment-integral-value point start length cutpoint clearance error)
     (lw-complex-exp-dyadic-moment-integral-grid point start length cutpoint clearance error))
    error))
  :hints (("Goal"
           :use
           (lw-complex-exp-clipped-computed-dyadic-moment-quadrature lw-complex-exp-dyadic-moment-error-valid
            lw-complex-exp-dyadic-moment-values-rational
            (:instance lw-complex-exp-clipped-moment-primitive-rational
              (end (+ start length)) (error (lw-complex-exp-dyadic-moment-error point start length clearance error)))
            (:instance lw-complex-exp-clipped-moment-primitive-cauchy
              (end (+ start length)) (bound (+ start length))
              (left-error (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error))
              (right-error (lw-complex-exp-dyadic-moment-error point start length clearance error)))
            (:instance lw-complex-difference-triangle
              (left (lw-complex-exp-dyadic-moment-integral-value point start length cutpoint clearance error))
              (middle (lw-complex-exp-clipped-moment-primitive point start (+ start length) cutpoint
                        (lw-complex-exp-dyadic-moment-error point start length clearance error)))
              (right (lw-complex-exp-dyadic-moment-integral-grid point start length cutpoint clearance error))
              (radius (* 2 (lw-complex-exp-moment-amplification start length clearance)
                         (+ (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error)
                            (lw-complex-exp-dyadic-moment-error point start length clearance error))
                         (/ clearance)))
              (other-radius (* 1/2 error)))
            (:instance lw-complex-disk-enlarge
              (point (lw-complex-sub
                (lw-complex-exp-dyadic-moment-integral-value point start length cutpoint clearance error)
                (lw-complex-exp-dyadic-moment-integral-grid point start length cutpoint clearance error)))
              (radius (+ (* 2 (lw-complex-exp-moment-amplification start length clearance)
                            (+ (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error)
                               (lw-complex-exp-dyadic-moment-error point start length clearance error))
                            (/ clearance))
                         (* 1/2 error)))
              (cap error)))
           :in-theory
           (e/d (lw-complex-exp-dyadic-moment-integral-value lw-complex-exp-moment-amplification)
                (lw-complex-exp-clipped-computed-dyadic-moment-quadrature lw-complex-exp-dyadic-moment-error-valid
                 lw-complex-exp-dyadic-moment-values-rational lw-complex-exp-clipped-moment-primitive-rational
                 lw-complex-exp-clipped-moment-primitive-cauchy lw-complex-difference-triangle))
           :nonlinearp nil :do-not-induct t)))
