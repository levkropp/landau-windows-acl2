(in-package "ACL2")

(include-book "mellin-clipped-exponential")
(include-book "complex-exp-dyadic-integral")

; Computed endpoint comparisons for the actual frozen constant and
; exponential components, retaining their independent fixed precisions.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-norm-square
                 lw-mellin-basis-exponential-point lw-mellin-exponential-component-error
                 lw-mellin-exponential-moment-cap lw-mellin-clipped-exponential-grid
                 lw-mellin-clipped-basis-dyadic lw-mellin-frozen-basis-dyadic
                 lw-mellin-clipped-basis-before-cutpoint lw-mellin-clipped-ramp-linearization
                 lw-mellin-frozen-ramp-before-cutpoint lw-mellin-frozen-ramp-after-cutpoint
                 lw-complex-exp-clipped-dyadic lw-complex-exp-clipped-moment-dyadic
                 lw-complex-exp-clipped-primitive lw-complex-exp-clipped-primitive-endpoint
                 lw-complex-exp-dyadic-integral-value lw-complex-exp-dyadic-integral-grid
                 lw-complex-exp-dyadic-depth lw-complex-exp-dyadic-error
                 lw-complex-exp-dyadic-slope lw-complex-exp-dyadic-target
                 lw-complex-exp-uniform-cap lw-complex-exp-grid-step-budget
                 lw-exp-lipschitz-cap lw-exp-bounds lw-halving-depth lw-precision-fuel lw-halved-width
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mep-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mep-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mep-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-mep-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mep-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mep-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mep-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mep-times-negative (a b) (b a)))
                         :in-theory (disable lw-mep-times-negative)))))
(local (defthm lw-mep-square-nonnegative
         (implies (rationalp a) (<= 0 (* a a)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-mellin-basis-clearance (kind sigma)
  (if (equal kind 3) sigma (- sigma 1)))

(defthm lw-mellin-basis-clearance-valid
  (implies (and (rationalp sigma) (< 1 sigma) (rationalp height))
           (and (lw-complexp (lw-mellin-basis-exponential-point kind sigma height))
                (rationalp (lw-mellin-basis-clearance kind sigma))
                (< 0 (lw-mellin-basis-clearance kind sigma))
                (<= (* (lw-mellin-basis-clearance kind sigma) (lw-mellin-basis-clearance kind sigma))
                    (lw-complex-norm-square (lw-mellin-basis-exponential-point kind sigma height)))))
  :hints (("Goal"
           :use ((:instance lw-mep-square-nonnegative (a height)))
           :in-theory (enable lw-mellin-basis-exponential-point lw-complexp lw-complex-norm-square)
           :nonlinearp t :do-not-induct t)))

(defun lw-mellin-component-endpoint-target (kind sigma length error)
  (/ error (* 4 (+ 1 length) (+ 1 (lw-mellin-basis-clearance kind sigma)))))

(defun lw-mellin-component-endpoint-value (kind start length cutpoint sigma height error)
  (lw-complex-exp-dyadic-integral-value
   (lw-mellin-basis-exponential-point kind sigma height) start length cutpoint
   (lw-mellin-basis-clearance kind sigma) (lw-mellin-component-endpoint-target kind sigma length error)))

(defun lw-mellin-component-endpoint-grid
  (kind start length cutpoint sigma height exp-error sample-error error)
  (lw-mellin-clipped-basis-dyadic
   kind start (+ start length)
   (lw-complex-exp-dyadic-depth
    (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
    (lw-mellin-component-endpoint-target kind sigma length error))
   cutpoint sigma height 0 exp-error 2 1 sample-error))

(local (in-theory (disable lw-mellin-basis-clearance lw-mellin-component-endpoint-target
                           lw-mellin-component-endpoint-value lw-mellin-component-endpoint-grid)))

(local (defthm lw-mep-target-scalar
         (implies
          (and (rationalp length) (<= 0 length) (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
          (let ((target (/ error (* 4 (+ 1 length) (+ 1 clearance)))))
            (and (rationalp target) (< 0 target) (<= target (* 1/4 error))
                 (<= (* length clearance target) (* 1/4 error)))))
         :hints (("Goal"
                  :use ((:instance lw-mep-positive-product (a (+ 1 length)) (b (+ 1 clearance)))
                        (:instance lw-positive-division-bound
                          (numerator error) (divisor (* 4 (+ 1 length) (+ 1 clearance))) (bound (* 1/4 error)))
                        (:instance lw-positive-division-bound
                          (numerator (* length clearance error)) (divisor (* 4 (+ 1 length) (+ 1 clearance)))
                          (bound (* 1/4 error))))
                  :nonlinearp t :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-component-endpoint-target-valid
  (implies (and (rationalp sigma) (< 1 sigma) (rationalp length) (<= 0 length) (rationalp error) (< 0 error))
           (let ((target (lw-mellin-component-endpoint-target kind sigma length error)))
             (and (rationalp target) (< 0 target) (<= target (* 1/4 error))
                  (<= (* length (lw-mellin-basis-clearance kind sigma) target) (* 1/4 error)))))
  :hints (("Goal"
           :use ((:instance lw-mellin-basis-clearance-valid (height 0))
                 (:instance lw-mep-target-scalar (clearance (lw-mellin-basis-clearance kind sigma))))
           :in-theory (e/d (lw-mellin-component-endpoint-target) (lw-mellin-basis-clearance-valid))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mep-extra-budget
         (implies
          (and (rationalp length) (<= 0 length) (rationalp clearance) (< 0 clearance)
               (rationalp target) (<= target (* 1/4 error))
               (<= (* length clearance target) (* 1/4 error))
               (rationalp delta) (<= delta (* 1/16 clearance target))
               (rationalp exp-error) (rationalp kernel) (rationalp sample-error)
               (rationalp error) (< 0 error))
          (<= (+ (* length (+ exp-error (* 2 kernel sample-error) delta)) target)
              (+ (* length (+ exp-error (* 2 kernel sample-error))) error)))
         :hints (("Goal"
                  :use ((:instance lw-mep-multiply-order
                          (a delta) (b (* 1/16 clearance target)) (factor length)))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mep-telescope
         (equal (lw-complex-sub left right)
                (lw-complex-add (lw-complex-sub left middle) (lw-complex-sub middle right)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))
         :rule-classes nil))
(local (defthm lw-mep-triangle
         (implies (and (lw-complex-diskp (lw-complex-sub left middle) radius)
                       (lw-complex-diskp (lw-complex-sub middle right) other-radius))
                  (lw-complex-diskp (lw-complex-sub left right) (+ radius other-radius)))
         :hints (("Goal"
                  :use (lw-mep-telescope
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub left middle)) (right (lw-complex-sub middle right))))
                  :in-theory (disable lw-complex-add-disk) :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-component-endpoint-comparison
  (implies
   (and (or (equal kind 0) (equal kind 3))
        (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (<= (+ start length) cap) (rationalp cutpoint) (<= 0 cutpoint)
        (rationalp sigma) (< 1 sigma) (rationalp height)
        (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-component-endpoint-grid kind start length cutpoint sigma height exp-error sample-error error)
     (lw-mellin-component-endpoint-value kind start length cutpoint sigma height error))
    (+ (* length (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error)))
  :hints
  (("Goal"
    :use
    (lw-mellin-basis-clearance-valid lw-mellin-component-endpoint-target-valid
     (:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
     (:instance lw-complex-exp-dyadic-depth-adequate
       (point (lw-mellin-basis-exponential-point kind sigma height))
       (clearance (lw-mellin-basis-clearance kind sigma))
       (error (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-complex-exp-dyadic-error-valid
       (point (lw-mellin-basis-exponential-point kind sigma height))
       (clearance (lw-mellin-basis-clearance kind sigma))
       (error (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-mellin-clipped-basis-exponential-comparison
       (end (+ start length))
       (depth (lw-complex-exp-dyadic-depth
         (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error)))
       (prime 2) (log-error 1)
       (complex-error (lw-complex-exp-dyadic-error
         (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error))))
     (:instance lw-complex-exp-clipped-computed-dyadic-endpoint
       (point (lw-mellin-basis-exponential-point kind sigma height))
       (clearance (lw-mellin-basis-clearance kind sigma))
       (error (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-complex-exp-dyadic-integral-grid-rational
       (point (lw-mellin-basis-exponential-point kind sigma height))
       (clearance (lw-mellin-basis-clearance kind sigma))
       (error (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-complex-exp-dyadic-integral-value-rational
       (point (lw-mellin-basis-exponential-point kind sigma height))
       (clearance (lw-mellin-basis-clearance kind sigma))
       (error (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-complex-difference-symmetric
       (left (lw-complex-exp-dyadic-integral-value
         (lw-mellin-basis-exponential-point kind sigma height) start length cutpoint (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error)))
       (right (lw-complex-exp-dyadic-integral-grid
         (lw-mellin-basis-exponential-point kind sigma height) start length cutpoint (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error)))
       (radius (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-mep-extra-budget
       (clearance (lw-mellin-basis-clearance kind sigma))
       (target (lw-mellin-component-endpoint-target kind sigma length error))
       (kernel (lw-complex-exp-uniform-cap cap))
       (delta (lw-complex-exp-dyadic-error
         (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error))))
     (:instance lw-mep-triangle
       (left (lw-mellin-component-endpoint-grid kind start length cutpoint sigma height exp-error sample-error error))
       (middle (lw-complex-exp-dyadic-integral-grid
         (lw-mellin-basis-exponential-point kind sigma height) start length cutpoint (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error)))
       (right (lw-mellin-component-endpoint-value kind start length cutpoint sigma height error))
       (radius (* length
         (lw-mellin-exponential-component-error cap exp-error sample-error
           (lw-complex-exp-dyadic-error
            (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
            (lw-mellin-component-endpoint-target kind sigma length error)))))
       (other-radius (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-complex-disk-enlarge
       (point (lw-complex-sub
         (lw-mellin-component-endpoint-grid kind start length cutpoint sigma height exp-error sample-error error)
         (lw-mellin-component-endpoint-value kind start length cutpoint sigma height error)))
       (radius (+ (* length
         (lw-mellin-exponential-component-error cap exp-error sample-error
           (lw-complex-exp-dyadic-error
            (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
            (lw-mellin-component-endpoint-target kind sigma length error))))
         (lw-mellin-component-endpoint-target kind sigma length error)))
       (cap (+ (* length (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error))))
    :cases ((equal kind 3))
    :in-theory
    (e/d (lw-mellin-component-endpoint-grid lw-mellin-component-endpoint-value
          lw-complex-exp-dyadic-integral-grid lw-mellin-clipped-exponential-grid
          lw-mellin-exponential-moment-cap lw-mellin-exponential-component-error)
         (lw-mellin-basis-clearance-valid lw-mellin-component-endpoint-target-valid
          lw-complex-exp-uniform-cap-data lw-complex-exp-dyadic-depth-adequate lw-complex-exp-dyadic-error-valid
          lw-mellin-clipped-basis-exponential-comparison lw-complex-exp-clipped-computed-dyadic-endpoint
          lw-complex-exp-dyadic-integral-grid-rational lw-complex-exp-dyadic-integral-value-rational))
    :nonlinearp nil :do-not-induct t)))
