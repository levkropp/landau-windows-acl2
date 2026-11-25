(in-package "ACL2")

(include-book "mellin-clipped-moment-endpoints")

(include-book "complex-exp-dyadic-refinement")

(include-book "complex-exp-dyadic-moment-refinement")

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

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-norm-square
                 lw-mellin-basis-exponential-point lw-mellin-basis-clearance
                 lw-mellin-exponential-component-error lw-mellin-exponential-moment-cap
                 lw-mellin-clipped-exponential-grid lw-mellin-clipped-basis-dyadic lw-mellin-frozen-basis-dyadic
                 lw-mellin-clipped-basis-before-cutpoint lw-mellin-clipped-ramp-linearization
                 lw-mellin-frozen-ramp-before-cutpoint lw-mellin-frozen-ramp-after-cutpoint
                 lw-complex-exp-clipped-dyadic lw-complex-exp-clipped-moment-dyadic
                 lw-complex-exp-clipped-moment-primitive lw-complex-exp-clipped-moment-primitive-endpoint
                 lw-complex-exp-dyadic-moment-integral-value lw-complex-exp-dyadic-moment-integral-grid
                 lw-complex-exp-dyadic-moment-depth lw-complex-exp-dyadic-moment-error
                 lw-complex-exp-dyadic-moment-endpoint-error lw-complex-exp-dyadic-moment-slope
                 lw-complex-exp-moment-amplification lw-complex-exp-moment-geometric-cost
                 lw-complex-exp-moment-evaluation-cost lw-complex-exp-moment-argument-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-exp-bounds
                 lw-complex-disk-enlarge lw-disk-enlarge
                 lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (in-theory (disable lw-mellin-basis-clearance lw-mellin-component-endpoint-target
                           lw-mellin-component-endpoint-value lw-mellin-component-endpoint-grid)))

(local (in-theory (disable lw-mellin-moment-endpoint-target lw-mellin-moment-endpoint-value
                           lw-mellin-moment-endpoint-grid)))

(local (defthm lw-mer-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mer-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mer-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mer-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mer-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mer-extra-budget
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
                  :use ((:instance lw-mer-multiply-order
                          (a delta) (b (* 1/16 clearance target)) (factor length)))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mer-telescope
         (equal (lw-complex-sub left right)
                (lw-complex-add (lw-complex-sub left middle) (lw-complex-sub middle right)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))
         :rule-classes nil))

(local (defthm lw-mer-triangle
         (implies (and (lw-complex-diskp (lw-complex-sub left middle) radius)
                       (lw-complex-diskp (lw-complex-sub middle right) other-radius))
                  (lw-complex-diskp (lw-complex-sub left right) (+ radius other-radius)))
         :hints (("Goal"
                  :use (lw-mer-telescope
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub left middle)) (right (lw-complex-sub middle right))))
                  :in-theory (disable lw-complex-add-disk) :do-not-induct t))
         :rule-classes nil))

(defun lw-mellin-component-refined-grid
  (kind start length cutpoint sigma height exp-error sample-error depth)
  (lw-mellin-clipped-basis-dyadic
   kind start (+ start length)
   depth
   cutpoint sigma height 0 exp-error 2 1 sample-error))

(local (in-theory (disable lw-mellin-component-refined-grid lw-complex-exp-refined-error lw-complex-exp-refined-grid)))

(defthm lw-mellin-component-refined-comparison
  (implies
   (and (natp depth)
        (<= (lw-complex-exp-dyadic-depth
         (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error)) depth)
        (or (equal kind 0) (equal kind 3))
        (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (<= (+ start length) cap) (rationalp cutpoint) (<= 0 cutpoint)
        (rationalp sigma) (< 1 sigma) (rationalp height)
        (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-component-refined-grid kind start length cutpoint sigma height exp-error sample-error depth)
     (lw-mellin-component-endpoint-value kind start length cutpoint sigma height error))
    (+ (* length (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error)))
  :hints
  (("Goal"
    :use
    (lw-mellin-basis-clearance-valid lw-mellin-component-endpoint-target-valid
     (:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
     (:instance lw-complex-exp-refined-depth-adequate
       (point (lw-mellin-basis-exponential-point kind sigma height))
       (clearance (lw-mellin-basis-clearance kind sigma))
       (error (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-complex-exp-refined-error-valid
       (point (lw-mellin-basis-exponential-point kind sigma height))
       (clearance (lw-mellin-basis-clearance kind sigma))
       (error (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-mellin-clipped-basis-exponential-comparison
       (end (+ start length))
       (depth depth)
       (prime 2) (log-error 1)
       (complex-error (lw-complex-exp-refined-error
         (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error) depth)))
     (:instance lw-complex-exp-clipped-refined-endpoint
       (point (lw-mellin-basis-exponential-point kind sigma height))
       (clearance (lw-mellin-basis-clearance kind sigma))
       (error (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-complex-exp-refined-grid-rational
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
       (right (lw-complex-exp-refined-grid
         (lw-mellin-basis-exponential-point kind sigma height) start length cutpoint (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error) depth))
       (radius (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-mer-extra-budget
       (clearance (lw-mellin-basis-clearance kind sigma))
       (target (lw-mellin-component-endpoint-target kind sigma length error))
       (kernel (lw-complex-exp-uniform-cap cap))
       (delta (lw-complex-exp-refined-error
         (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error) depth)))
     (:instance lw-mer-triangle
       (left (lw-mellin-component-refined-grid kind start length cutpoint sigma height exp-error sample-error depth))
       (middle (lw-complex-exp-refined-grid
         (lw-mellin-basis-exponential-point kind sigma height) start length cutpoint (lw-mellin-basis-clearance kind sigma)
         (lw-mellin-component-endpoint-target kind sigma length error) depth))
       (right (lw-mellin-component-endpoint-value kind start length cutpoint sigma height error))
       (radius (* length
         (lw-mellin-exponential-component-error cap exp-error sample-error
           (lw-complex-exp-refined-error
            (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
            (lw-mellin-component-endpoint-target kind sigma length error) depth))))
       (other-radius (lw-mellin-component-endpoint-target kind sigma length error)))
     (:instance lw-complex-disk-enlarge
       (point (lw-complex-sub
         (lw-mellin-component-refined-grid kind start length cutpoint sigma height exp-error sample-error depth)
         (lw-mellin-component-endpoint-value kind start length cutpoint sigma height error)))
       (radius (+ (* length
         (lw-mellin-exponential-component-error cap exp-error sample-error
           (lw-complex-exp-refined-error
            (lw-mellin-basis-exponential-point kind sigma height) start length (lw-mellin-basis-clearance kind sigma)
            (lw-mellin-component-endpoint-target kind sigma length error) depth)))
         (lw-mellin-component-endpoint-target kind sigma length error)))
       (cap (+ (* length (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error))))
    :cases ((equal kind 3))
    :in-theory
    (e/d (lw-mellin-component-refined-grid lw-mellin-component-endpoint-value
          lw-complex-exp-refined-grid lw-mellin-clipped-exponential-grid
          lw-mellin-exponential-moment-cap lw-mellin-exponential-component-error)
         (lw-mellin-basis-clearance-valid lw-mellin-component-endpoint-target-valid
          lw-complex-exp-uniform-cap-data lw-complex-exp-refined-depth-adequate lw-complex-exp-refined-error-valid
          lw-mellin-clipped-basis-exponential-comparison lw-complex-exp-clipped-refined-endpoint
          lw-complex-exp-refined-grid-rational lw-complex-exp-dyadic-integral-value-rational))
    :nonlinearp nil :do-not-induct t)))

(local (defthm lw-mmr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mmr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mmr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-mmr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mmr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mmr-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mmr-extra-budget
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
                  :use ((:instance lw-mmr-multiply-order
                          (a delta) (b (* 1/16 clearance target)) (factor length)))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mmr-telescope
         (equal (lw-complex-sub left right)
                (lw-complex-add (lw-complex-sub left middle) (lw-complex-sub middle right)))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))
         :rule-classes nil))

(local (defthm lw-mmr-triangle
         (implies (and (lw-complex-diskp (lw-complex-sub left middle) radius)
                       (lw-complex-diskp (lw-complex-sub middle right) other-radius))
                  (lw-complex-diskp (lw-complex-sub left right) (+ radius other-radius)))
         :hints (("Goal"
                  :use (lw-mmr-telescope
                        (:instance lw-complex-add-disk
                          (left (lw-complex-sub left middle)) (right (lw-complex-sub middle right))))
                  :in-theory (disable lw-complex-add-disk) :do-not-induct t))
         :rule-classes nil))

(local (in-theory (disable lw-mellin-component-refined-grid lw-complex-exp-refined-moment-error lw-complex-exp-refined-moment-grid)))

(defthm lw-mellin-moment-refined-comparison
  (implies
   (and (natp depth)
        (<= (lw-complex-exp-dyadic-moment-depth
         (lw-mellin-basis-exponential-point 1 sigma height) start length (lw-mellin-basis-clearance 1 sigma)
         (lw-mellin-moment-endpoint-target cap sigma length error)) depth)
        (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (<= (+ start length) cap) (rationalp cutpoint) (<= 0 cutpoint)
        (rationalp sigma) (< 1 sigma) (rationalp height)
        (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-component-refined-grid 1 start length cutpoint sigma height exp-error sample-error depth)
     (lw-mellin-moment-endpoint-value cap start length cutpoint sigma height error))
    (+ (* length cap (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error)))
  :hints
  (("Goal"
    :use
    ((:instance lw-mellin-basis-clearance-valid (kind 1)) lw-mellin-moment-endpoint-target-valid
     (:instance lw-mmr-nonnegative-product (a cap) (b length))
     (:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
     (:instance lw-complex-exp-refined-moment-depth-adequate
       (point (lw-mellin-basis-exponential-point 1 sigma height))
       (clearance (lw-mellin-basis-clearance 1 sigma))
       (error (lw-mellin-moment-endpoint-target cap sigma length error)))
     (:instance lw-complex-exp-refined-moment-error-valid
       (point (lw-mellin-basis-exponential-point 1 sigma height))
       (clearance (lw-mellin-basis-clearance 1 sigma))
       (error (lw-mellin-moment-endpoint-target cap sigma length error)))
     (:instance lw-mellin-clipped-basis-exponential-comparison
       (kind 1)
       (end (+ start length))
       (depth depth)
       (prime 2) (log-error 1)
       (complex-error (lw-complex-exp-refined-moment-error
         (lw-mellin-basis-exponential-point 1 sigma height) start length (lw-mellin-basis-clearance 1 sigma)
         (lw-mellin-moment-endpoint-target cap sigma length error) depth)))
     (:instance lw-complex-exp-clipped-refined-moment-endpoint
       (point (lw-mellin-basis-exponential-point 1 sigma height))
       (clearance (lw-mellin-basis-clearance 1 sigma))
       (error (lw-mellin-moment-endpoint-target cap sigma length error)))
     (:instance lw-complex-exp-refined-moment-values-rational
       (point (lw-mellin-basis-exponential-point 1 sigma height))
       (clearance (lw-mellin-basis-clearance 1 sigma))
       (error (lw-mellin-moment-endpoint-target cap sigma length error)))
     (:instance lw-complex-difference-symmetric
       (left (lw-complex-exp-dyadic-moment-integral-value
         (lw-mellin-basis-exponential-point 1 sigma height) start length cutpoint (lw-mellin-basis-clearance 1 sigma)
         (lw-mellin-moment-endpoint-target cap sigma length error)))
       (right (lw-complex-exp-refined-moment-grid
         (lw-mellin-basis-exponential-point 1 sigma height) start length cutpoint (lw-mellin-basis-clearance 1 sigma)
         (lw-mellin-moment-endpoint-target cap sigma length error) depth))
       (radius (lw-mellin-moment-endpoint-target cap sigma length error)))
     (:instance lw-mmr-extra-budget
       (length (* cap length))
       (clearance (lw-mellin-basis-clearance 1 sigma))
       (target (lw-mellin-moment-endpoint-target cap sigma length error))
       (kernel (lw-complex-exp-uniform-cap cap))
       (delta (lw-complex-exp-refined-moment-error
         (lw-mellin-basis-exponential-point 1 sigma height) start length (lw-mellin-basis-clearance 1 sigma)
         (lw-mellin-moment-endpoint-target cap sigma length error) depth)))
     (:instance lw-mmr-triangle
       (left (lw-mellin-component-refined-grid 1 start length cutpoint sigma height exp-error sample-error depth))
       (middle (lw-complex-exp-refined-moment-grid
         (lw-mellin-basis-exponential-point 1 sigma height) start length cutpoint (lw-mellin-basis-clearance 1 sigma)
         (lw-mellin-moment-endpoint-target cap sigma length error) depth))
       (right (lw-mellin-moment-endpoint-value cap start length cutpoint sigma height error))
       (radius (* length cap
         (lw-mellin-exponential-component-error cap exp-error sample-error
           (lw-complex-exp-refined-moment-error
            (lw-mellin-basis-exponential-point 1 sigma height) start length (lw-mellin-basis-clearance 1 sigma)
            (lw-mellin-moment-endpoint-target cap sigma length error) depth))))
       (other-radius (lw-mellin-moment-endpoint-target cap sigma length error)))
     (:instance lw-complex-disk-enlarge
       (point (lw-complex-sub
         (lw-mellin-component-refined-grid 1 start length cutpoint sigma height exp-error sample-error depth)
         (lw-mellin-moment-endpoint-value cap start length cutpoint sigma height error)))
       (radius (+ (* length cap
         (lw-mellin-exponential-component-error cap exp-error sample-error
           (lw-complex-exp-refined-moment-error
            (lw-mellin-basis-exponential-point 1 sigma height) start length (lw-mellin-basis-clearance 1 sigma)
            (lw-mellin-moment-endpoint-target cap sigma length error) depth)))
         (lw-mellin-moment-endpoint-target cap sigma length error)))
       (cap (+ (* length cap (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error))) error))))
    :in-theory
    (e/d (lw-mellin-component-refined-grid lw-mellin-moment-endpoint-value
          lw-complex-exp-refined-moment-grid lw-mellin-clipped-exponential-grid
          lw-mellin-exponential-moment-cap lw-mellin-exponential-component-error)
         (lw-mellin-basis-clearance-valid lw-mellin-moment-endpoint-target-valid
          lw-complex-exp-uniform-cap-data lw-complex-exp-refined-moment-depth-adequate lw-complex-exp-refined-moment-error-valid
          lw-mellin-clipped-basis-exponential-comparison lw-complex-exp-clipped-refined-moment-endpoint
          lw-complex-exp-refined-moment-values-rational lw-complex-exp-dyadic-moment-error-valid))
    :nonlinearp nil :do-not-induct t)))

