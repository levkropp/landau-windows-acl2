(in-package "ACL2")

(include-book "complex-exp-dyadic-moment-integral")

; Refine the first-moment mesh without changing the computed endpoint.
; Point precision is recomputed from the actual refined leaf count.


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

(local (defthm lw-cmr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cmr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cmr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cmr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cmr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-cmr-left-commutes)))))

(local (defthm lw-cmr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cmr-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cmr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cmr-mesh-data
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth))
                       (<= 0 (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))

(local (defthm lw-cmr-cost-data
         (implies (and (rationalp mass) (<= 0 mass) (rationalp cap) (<= 1 cap)
                       (rationalp base-cap) (<= 1 base-cap)
                       (rationalp amplification) (< 0 amplification))
                  (and (rationalp (* cap (+ (* amplification mass mass) mass)))
                       (<= 0 (* cap (+ (* amplification mass mass) mass)))
                       (rationalp (* amplification (+ base-cap (* 2 cap) 2)))
                       (< 0 (* amplification (+ base-cap (* 2 cap) 2)))))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cmr-costs-valid
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
                        (:instance lw-cmr-nonnegative-product (a (lw-complex-l1 point)) (b (+ start length)))
                        (:instance lw-cmr-cost-data
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

(local (in-theory
        (disable lw-complex-exp-dyadic-moment-slope lw-complex-exp-dyadic-moment-depth
                 lw-complex-exp-dyadic-moment-endpoint-error lw-complex-exp-dyadic-moment-error
                 lw-complex-exp-dyadic-moment-integral-grid lw-complex-exp-dyadic-moment-integral-value)))

(local (defthm lw-cmr-mesh-monotone
  (implies (and (rationalp width) (<= 0 width) (natp small) (natp large) (<= small large))
           (<= (lw-halved-width width large) (lw-halved-width width small)))
  :hints (("Goal" :induct (lw-halved-width width large)
                  :in-theory (enable (:induction lw-halved-width)))
          (and stable-under-simplificationp
               '(:cases ((equal small large))
                 :use ((:instance lw-cmr-mesh-data (depth (- large 1))))
                 :expand ((lw-halved-width width large))
                 :do-not-induct t)))
  :rule-classes nil))

(local (defthm lw-cmr-refine-bounds
  (implies
   (and (rationalp slope) (<= 0 slope) (rationalp geometry) (<= 0 geometry)
        (rationalp length) (<= 0 length)
        (rationalp fine) (<= 0 fine) (rationalp coarse) (<= fine coarse)
        (rationalp budget)
        (<= (* slope coarse) 1) (<= (* geometry length coarse) budget))
   (and (<= (* slope fine) 1) (<= (* geometry length fine) budget)))
  :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-complex-exp-refined-moment-error (point start length clearance error depth)
  (min (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error)
       (/ (* clearance error)
          (* 16 (+ 1 (* (lw-dyadic-leaf-count
                         depth)
                        (lw-complex-exp-moment-evaluation-cost point start length clearance)))))))

(defun lw-complex-exp-refined-moment-grid (point start length cutpoint clearance error depth)
  (lw-complex-exp-clipped-moment-dyadic
   point start (+ start length) depth cutpoint
   (lw-complex-exp-refined-moment-error point start length clearance error depth)))

(local (in-theory (disable lw-complex-exp-refined-moment-error lw-complex-exp-refined-moment-grid)))

(defthm lw-complex-exp-refined-moment-depth-adequate
  (implies
   (and (natp depth) (<= (lw-complex-exp-dyadic-moment-depth point start length clearance error) depth)
        (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (let ((mesh (lw-halved-width length depth)))
     (and (<= (* (lw-complex-l1 point) mesh) 1)
          (<= (* (lw-complex-exp-moment-geometric-cost point start length clearance) length mesh)
              (* 1/4 clearance error)))))
  :hints (("Goal"
    :use (lw-complex-exp-dyadic-moment-depth-adequate lw-complex-l1-bound lw-cmr-costs-valid
          (:instance lw-cmr-mesh-data (width length))
          (:instance lw-cmr-mesh-data (width length)
            (depth (lw-complex-exp-dyadic-moment-depth point start length clearance error)))
          (:instance lw-cmr-mesh-monotone (width length)
            (small (lw-complex-exp-dyadic-moment-depth point start length clearance error)) (large depth))
          (:instance lw-cmr-refine-bounds (slope (lw-complex-l1 point))
            (geometry (lw-complex-exp-moment-geometric-cost point start length clearance))
            (fine (lw-halved-width length depth))
            (coarse (lw-halved-width length (lw-complex-exp-dyadic-moment-depth point start length clearance error)))
            (budget (* 1/4 clearance error))))
    :in-theory (disable lw-complex-exp-dyadic-moment-depth-adequate lw-complex-l1-bound)
    :nonlinearp nil :do-not-induct t)))

(local (defthm lw-cmr-precision-scalar
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

(local (defthm lw-cmr-endpoint-data
         (implies
          (and (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
               (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
          (let ((tau (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error)))
            (and (rationalp tau) (< 0 tau) (<= tau (* 1/16 clearance error))
                 (<= (* (lw-complex-exp-moment-amplification start length clearance) tau) (* 1/16 clearance error)))))
         :hints (("Goal"
                  :use ((:instance lw-cmr-positive-product (a clearance) (b error))
                        (:instance lw-cmr-precision-scalar
                          (numerator (* clearance error)) (factor (lw-complex-exp-moment-amplification start length clearance))))
                  :in-theory (enable lw-complex-exp-dyadic-moment-endpoint-error lw-complex-exp-moment-amplification)
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmr-cauchy-budget
         (implies
          (and (rationalp amplification) (<= 0 amplification)
               (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error)
               (rationalp delta) (rationalp tau) (<= delta tau)
               (<= (* amplification tau) (* 1/16 clearance error)))
          (<= (* 2 amplification (+ delta tau) (/ clearance)) (* 1/4 error)))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x clearance))
                        (:instance lw-cmr-multiply-order (a delta) (b tau) (factor amplification))
                        (:instance lw-cmr-multiply-order
                          (a (+ (* amplification delta) (* amplification tau))) (b (* 1/8 clearance error))
                          (factor (* 2 (/ clearance)))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-complex-exp-refined-moment-error-valid
  (implies
   (and (natp depth)
        (<= (lw-complex-exp-dyadic-moment-depth point start length clearance error) depth)
        (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (let ((tau (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error))
         (delta (lw-complex-exp-refined-moment-error point start length clearance error depth))
         (count (lw-dyadic-leaf-count depth)))
     (and (rationalp tau) (< 0 tau) (<= tau (* 1/16 clearance error))
          (rationalp delta) (< 0 delta) (<= delta tau)
          (<= (* (lw-complex-exp-moment-amplification start length clearance) tau) (* 1/16 clearance error))
          (<= (* count (lw-complex-exp-moment-evaluation-cost point start length clearance) delta)
              (* 1/16 clearance error))
          (<= (* 2 (lw-complex-exp-moment-amplification start length clearance)
                 (+ delta tau) (/ clearance)) (* 1/4 error)))))
  :hints (("Goal"
           :use (lw-cmr-costs-valid lw-cmr-endpoint-data
                 (:instance lw-cmr-positive-product (a clearance) (b error))
                 (:instance lw-cmr-positive-product
                   (a (lw-dyadic-leaf-count depth))
                   (b (lw-complex-exp-moment-evaluation-cost point start length clearance)))
                 (:instance lw-cmr-precision-scalar
                   (numerator (* clearance error))
                   (factor (* (lw-dyadic-leaf-count depth)
                              (lw-complex-exp-moment-evaluation-cost point start length clearance))))
                 (:instance lw-cmr-multiply-order
                   (a (lw-complex-exp-refined-moment-error point start length clearance error depth))
                   (b (/ (* clearance error)
                         (* 16 (+ 1 (* (lw-dyadic-leaf-count
                                        depth)
                                       (lw-complex-exp-moment-evaluation-cost point start length clearance))))))
                   (factor (* (lw-dyadic-leaf-count
                               depth)
                              (lw-complex-exp-moment-evaluation-cost point start length clearance))))
                 (:instance lw-cmr-cauchy-budget
                   (amplification (lw-complex-exp-moment-amplification start length clearance))
                   (delta (lw-complex-exp-refined-moment-error point start length clearance error depth))
                   (tau (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error))))
           :in-theory (enable lw-complex-exp-refined-moment-error) :nonlinearp nil :do-not-induct t)))

(local (defthm lw-cmr-multiply-equality
         (implies (equal a b) (equal (* a factor) (* b factor)))
         :rule-classes nil))

(local (defthm lw-cmr-total-budget
         (implies
          (and (rationalp count) (rationalp mesh) (rationalp length) (equal (* count mesh) length)
               (rationalp geometry) (rationalp weight) (rationalp delta)
               (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error)
               (<= (* geometry length mesh) (* 1/4 clearance error))
               (<= (* count weight delta) (* 1/16 clearance error)))
          (<= (* count (+ (* geometry mesh mesh) (* weight delta)) (/ clearance)) (* 1/2 error)))
         :hints (("Goal"
                  :use ((:instance lw-cmr-multiply-equality
                          (a (* count mesh)) (b length) (factor (* geometry mesh)))
                        (:instance lw-cmr-positive-product (a clearance) (b error))
                        (:instance inverse-of-* (x clearance))
                        (:instance lw-cmr-multiply-order
                          (a (+ (* geometry length mesh) (* count weight delta)))
                          (b (* 1/2 clearance error)) (factor (/ clearance))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmr-budget-form
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

(defthm lw-complex-exp-refined-moment-total-budget
  (implies
   (and (natp depth)
        (<= (lw-complex-exp-dyadic-moment-depth point start length clearance error) depth)
        (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (<= (lw-complex-exp-moment-grid-budget
        point (lw-halved-width length depth)
        (+ start length) (lw-complex-exp-moment-argument-cap point start length)
        (lw-dyadic-leaf-count depth) clearance
        (lw-complex-exp-refined-moment-error point start length clearance error depth))
       (* 1/2 error)))
  :hints (("Goal"
           :use (lw-cmr-costs-valid lw-complex-exp-refined-moment-depth-adequate lw-complex-exp-refined-moment-error-valid
                 (:instance lw-cmr-mesh-data
                   (width length) (depth depth))
                 (:instance lw-dyadic-leaf-count-mesh
                   (width length) (depth depth))
                 (:instance lw-cmr-total-budget
                   (count (lw-dyadic-leaf-count depth))
                   (mesh (lw-halved-width length depth))
                   (geometry (lw-complex-exp-moment-geometric-cost point start length clearance))
                   (weight (lw-complex-exp-moment-evaluation-cost point start length clearance))
                   (delta (lw-complex-exp-refined-moment-error point start length clearance error depth))))
           :in-theory (disable lw-complex-exp-refined-moment-depth-adequate lw-complex-exp-refined-moment-error-valid
                               lw-dyadic-leaf-count-mesh)
           :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-refined-moment-values-rational
  (implies
   (and (natp depth)
        (<= (lw-complex-exp-dyadic-moment-depth point start length clearance error) depth)
        (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp cutpoint) (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (and (lw-complexp (lw-complex-exp-refined-moment-grid point start length cutpoint clearance error depth))
        (lw-complexp (lw-complex-exp-dyadic-moment-integral-value point start length cutpoint clearance error))))
  :hints (("Goal"
           :use (lw-complex-exp-refined-moment-error-valid)
           :in-theory (e/d (lw-complex-exp-refined-moment-grid lw-complex-exp-dyadic-moment-integral-value)
                           (lw-complex-exp-refined-moment-error-valid))
           :do-not-induct t)))

(defthm lw-complex-exp-clipped-refined-moment-quadrature
  (implies
   (and (natp depth)
        (<= (lw-complex-exp-dyadic-moment-depth point start length clearance error) depth)
        (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp cutpoint) (<= 0 cutpoint) (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point)) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-clipped-moment-primitive point start (+ start length) cutpoint
       (lw-complex-exp-refined-moment-error point start length clearance error depth))
     (lw-complex-exp-refined-moment-grid point start length cutpoint clearance error depth))
    (* 1/2 error)))
  :hints (("Goal"
           :use (lw-cmr-costs-valid lw-complex-exp-refined-moment-depth-adequate
                 lw-complex-exp-refined-moment-error-valid lw-complex-exp-refined-moment-total-budget
                 (:instance lw-complex-exp-clipped-moment-dyadic-primitive-error
                   (end (+ start length)) (bound (+ start length))
                   (depth depth)
                   (argument-cap (lw-complex-exp-moment-argument-cap point start length))
                   (error (lw-complex-exp-refined-moment-error point start length clearance error depth)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-clipped-moment-primitive point start (+ start length) cutpoint
                       (lw-complex-exp-refined-moment-error point start length clearance error depth))
                     (lw-complex-exp-refined-moment-grid point start length cutpoint clearance error depth)))
                   (radius (lw-complex-exp-moment-grid-budget
                     point (lw-halved-width length depth)
                     (+ start length) (lw-complex-exp-moment-argument-cap point start length)
                     (lw-dyadic-leaf-count depth) clearance
                     (lw-complex-exp-refined-moment-error point start length clearance error depth)))
                   (cap (* 1/2 error))))
           :in-theory
           (e/d (lw-complex-exp-refined-moment-grid lw-complex-exp-moment-argument-cap)
                (lw-complex-exp-refined-moment-depth-adequate lw-complex-exp-refined-moment-error-valid
                 lw-complex-exp-refined-moment-total-budget lw-complex-exp-clipped-moment-dyadic-primitive-error))
           :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-clipped-refined-moment-endpoint
  (implies
   (and (natp depth)
        (<= (lw-complex-exp-dyadic-moment-depth point start length clearance error) depth)
        (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp cutpoint) (<= 0 cutpoint) (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point)) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-dyadic-moment-integral-value point start length cutpoint clearance error)
     (lw-complex-exp-refined-moment-grid point start length cutpoint clearance error depth))
    error))
  :hints (("Goal"
           :use
           (lw-complex-exp-clipped-refined-moment-quadrature lw-complex-exp-refined-moment-error-valid
            lw-complex-exp-refined-moment-values-rational
            (:instance lw-complex-exp-clipped-moment-primitive-rational
              (end (+ start length)) (error (lw-complex-exp-refined-moment-error point start length clearance error depth)))
            (:instance lw-complex-exp-clipped-moment-primitive-cauchy
              (end (+ start length)) (bound (+ start length))
              (left-error (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error))
              (right-error (lw-complex-exp-refined-moment-error point start length clearance error depth)))
            (:instance lw-complex-difference-triangle
              (left (lw-complex-exp-dyadic-moment-integral-value point start length cutpoint clearance error))
              (middle (lw-complex-exp-clipped-moment-primitive point start (+ start length) cutpoint
                        (lw-complex-exp-refined-moment-error point start length clearance error depth)))
              (right (lw-complex-exp-refined-moment-grid point start length cutpoint clearance error depth))
              (radius (* 2 (lw-complex-exp-moment-amplification start length clearance)
                         (+ (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error)
                            (lw-complex-exp-refined-moment-error point start length clearance error depth))
                         (/ clearance)))
              (other-radius (* 1/2 error)))
            (:instance lw-complex-disk-enlarge
              (point (lw-complex-sub
                (lw-complex-exp-dyadic-moment-integral-value point start length cutpoint clearance error)
                (lw-complex-exp-refined-moment-grid point start length cutpoint clearance error depth)))
              (radius (+ (* 2 (lw-complex-exp-moment-amplification start length clearance)
                            (+ (lw-complex-exp-dyadic-moment-endpoint-error start length clearance error)
                               (lw-complex-exp-refined-moment-error point start length clearance error depth))
                            (/ clearance))
                         (* 1/2 error)))
              (cap error)))
           :in-theory
           (e/d (lw-complex-exp-dyadic-moment-integral-value lw-complex-exp-moment-amplification)
                (lw-complex-exp-clipped-refined-moment-quadrature lw-complex-exp-refined-moment-error-valid
                 lw-complex-exp-refined-moment-values-rational lw-complex-exp-clipped-moment-primitive-rational
                 lw-complex-exp-clipped-moment-primitive-cauchy lw-complex-difference-triangle))
           :nonlinearp nil :do-not-induct t)))

