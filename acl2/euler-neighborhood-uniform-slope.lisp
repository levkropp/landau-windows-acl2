(in-package "ACL2")

(include-book "euler-disk-native-value-cap")
(include-book "euler-nonzero-neighborhood")
(include-book "cauchy-boundary-geometric-bound")

; A local disk inside a fixed larger disk inherits a uniform value cap.

(local (defthm lw-enus-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-enus-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-enus-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-enus-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-enus-times-negative (a b) (b a)))
                 :in-theory (disable lw-enus-times-negative)))))

(local (defthm lw-enus-zero-times (equal (* 0 a) 0)))

(local (defthm lw-enus-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-enus-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-enus-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-enus-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-enus-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-enus-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-enus-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enus-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enus-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-enus-left-commutes)))))

(local
 (defthm lw-enus-shifted-point-data
   (implies
    (and (rationalp rate) (rationalp height) (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp global-rate) (rationalp global-height)
       (rationalp global-radius) (< 0 global-radius) (< global-radius global-rate)
       (lw-complex-diskp (lw-complex-sub (cons rate height) (cons global-rate global-height)) displacement)
       (<= (+ displacement outer-radius) global-radius)
         (lw-complex-diskp point 1))
    (and (lw-complexp point)
         (lw-complex-diskp (lw-complex-scale outer-radius point) outer-radius)
         (lw-complex-diskp (lw-complex-add (lw-complex-sub (cons rate height) (cons global-rate global-height)) (lw-complex-scale outer-radius point)) global-radius)
         (equal (+ global-rate (car (lw-complex-add (lw-complex-sub (cons rate height) (cons global-rate global-height)) (lw-complex-scale outer-radius point)))) (+ rate (car (lw-complex-scale outer-radius point))))
         (equal (+ global-height (cdr (lw-complex-add (lw-complex-sub (cons rate height) (cons global-rate global-height)) (lw-complex-scale outer-radius point)))) (+ height (cdr (lw-complex-scale outer-radius point))))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (radius 1))
                  (:instance lw-complex-disk-data (point (lw-complex-sub (cons rate height) (cons global-rate global-height))) (radius displacement))
                  (:instance lw-complex-scale-rational (factor outer-radius))
                  (:instance lw-complex-scale-disk (radius 1) (factor outer-radius))
                  (:instance lw-complex-add-disk
                    (left (lw-complex-sub (cons rate height) (cons global-rate global-height))) (right (lw-complex-scale outer-radius point))
                    (radius displacement) (other-radius outer-radius))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-add (lw-complex-sub (cons rate height) (cons global-rate global-height)) (lw-complex-scale outer-radius point)))
                    (radius (+ displacement outer-radius)) (cap global-radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-add lw-complex-sub lw-complex-scale lw-complexp abs
              lw-enus-left-commutes lw-enus-left-distributes lw-enus-fold-constants
              lw-enus-times-negative lw-enus-negative-times lw-enus-zero-times
              lw-enus-minus-one lw-enus-double-negative lw-enus-add-cancel lw-enus-double lw-enus-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-local-polynomial-unit-value-cap
  (implies
   (and (rationalp rate) (rationalp height) (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp global-rate) (rationalp global-height)
       (rationalp global-radius) (< 0 global-radius) (< global-radius global-rate)
       (lw-complex-diskp (lw-complex-sub (cons rate height) (cons global-rate global-height)) displacement)
       (<= (+ displacement outer-radius) global-radius)
        (rationalp error) (< 0 error) (<= error 1) (lw-complex-diskp point 1))
   (lw-complex-diskp (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height outer-radius 0 error) point 0) (+ 4 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius))))
  :hints (("Goal"
           :use (lw-enus-shifted-point-data
                 (:instance lw-complex-disk-data (point (lw-complex-scale outer-radius point)) (radius outer-radius))
                 (:instance lw-euler-disk-native-value-cap
                   (rate global-rate) (height global-height) (radius global-radius)
                   (point (lw-complex-add (lw-complex-sub (cons rate height) (cons global-rate global-height)) (lw-complex-scale outer-radius point))) (error 1))
                 (:instance lw-euler-disk-point-data (radius outer-radius) (offset (lw-complex-scale outer-radius point)))
                 (:instance lw-euler-uniform-coefficient-cap-valid (rate global-rate) (height global-height) (radius global-radius))
                 (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (target 0))
                 (:instance lw-polynomial-rescale-evaluation (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 error)) (factor outer-radius) (offset 0))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 error)) (point (lw-complex-scale outer-radius point)) (offset 0))
                 (:instance lw-complex-euler-continuation-value-rational
                   (rate (+ rate (car (lw-complex-scale outer-radius point)))) (height (+ height (cdr (lw-complex-scale outer-radius point)))) (error 1))
                 (:instance lw-complex-euler-uniform-polynomial-comparison
                   (radius outer-radius) (point (lw-complex-scale outer-radius point)) (target 0) (value-error 1))
                 (:instance lw-complex-sub-zero (point (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale outer-radius point))) (+ height (cdr (lw-complex-scale outer-radius point))) 1)))
                 (:instance lw-complex-sub-zero (point (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 error) (lw-complex-scale outer-radius point) 0)))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 error) (lw-complex-scale outer-radius point) 0)) (middle (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale outer-radius point))) (+ height (cdr (lw-complex-scale outer-radius point))) 1)) (right (cons 0 0))
                   (radius (+ error 1/4)) (other-radius (+ 2 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius))))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius 0 error) (lw-complex-scale outer-radius point) 0))
                   (radius (+ (+ error 1/4) (+ 2 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius)))) (cap (+ 4 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-coefficient-polynomial
              lw-enus-left-commutes lw-enus-left-distributes lw-enus-fold-constants
              lw-enus-times-negative lw-enus-negative-times lw-enus-zero-times
              lw-enus-minus-one lw-enus-double-negative lw-enus-add-cancel lw-enus-double lw-enus-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-enus-local-boundary-check
   (implies
    (and (rationalp rate) (rationalp height) (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp global-rate) (rationalp global-height)
       (rationalp global-radius) (< 0 global-radius) (< global-radius global-rate)
       (lw-complex-diskp (lw-complex-sub (cons rate height) (cons global-rate global-height)) displacement)
       (<= (+ displacement outer-radius) global-radius)
         (rationalp error) (< 0 error) (<= error 1) (lw-complex-diskp rotation 1))
    (lw-cauchy-boundary-check (lw-euler-coefficient-polynomial rate height outer-radius 0 error) rotation 0 count (+ 4 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius))))
   :hints (("Goal"
            :induct (lw-cauchy-boundary-check (lw-euler-coefficient-polynomial rate height outer-radius 0 error) rotation 0 count (+ 4 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cauchy-boundary-check
              lw-enus-left-commutes lw-enus-left-distributes lw-enus-fold-constants
              lw-enus-times-negative lw-enus-negative-times lw-enus-zero-times
              lw-enus-minus-one lw-enus-double-negative lw-enus-add-cancel lw-enus-double lw-enus-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory)))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-unit-power (point rotation) (index (- count 1)))
                        (:instance lw-euler-local-polynomial-unit-value-cap (point (lw-complex-power rotation (- count 1))))))))
   :rule-classes nil))

(defthm lw-euler-neighborhood-uniform-slope
  (implies
   (and (rationalp rate) (rationalp height) (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp global-rate) (rationalp global-height)
       (rationalp global-radius) (< 0 global-radius) (< global-radius global-rate)
       (lw-complex-diskp (lw-complex-sub (cons rate height) (cons global-rate global-height)) displacement)
       (<= (+ displacement outer-radius) global-radius) (rationalp error) (< 0 error) (<= error 1))
   (let ((slope (* 4 (+ 5 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius)) (/ outer-radius))))
     (and (rationalp slope) (< 0 slope)
          (<= (lw-euler-neighborhood-slope-cap rate height outer-radius error) slope))))
  :hints (("Goal"
           :use ((:instance lw-euler-uniform-coefficient-cap-valid
                   (rate global-rate) (height global-height) (radius global-radius))
                 (:instance lw-reciprocal-positive (value outer-radius))
                 (:instance lw-enus-positive-product (a (+ 5 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius))) (b (/ outer-radius)))
                 (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (target 0))
                 (:instance lw-polynomial-rescale-valid (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 error)) (factor outer-radius) (offset 0))
                 (:instance lw-cauchy-orbit-data (degree (len (lw-euler-coefficient-polynomial rate height outer-radius 0 error))))
                 (:instance lw-enus-local-boundary-check
                   (rotation (lw-cauchy-orbit-rotation (len (lw-euler-coefficient-polynomial rate height outer-radius 0 error))))
                   (count (lw-cauchy-coefficient-count (lw-euler-coefficient-polynomial rate height outer-radius 0 error) (len (lw-euler-coefficient-polynomial rate height outer-radius 0 error)) 1)))
                 (:instance lw-cauchy-boundary-coefficient-caps
                   (coefficients (lw-euler-coefficient-polynomial rate height outer-radius 0 error)) (degree (len (lw-euler-coefficient-polynomial rate height outer-radius 0 error))) (cap (+ 4 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius))) (error 1))
                 (:instance lw-polynomial-half-disk-slope-upper
                   (coefficients (lw-euler-uniform-polynomial rate height outer-radius 0 error)) (outer outer-radius) (cap (+ 5 (lw-euler-uniform-coefficient-cap global-rate global-height global-radius)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-coefficient-polynomial lw-euler-neighborhood-slope-cap (:type-prescription len)
              lw-enus-left-commutes lw-enus-left-distributes lw-enus-fold-constants
              lw-enus-times-negative lw-enus-negative-times lw-enus-zero-times
              lw-enus-minus-one lw-enus-double-negative lw-enus-add-cancel lw-enus-double lw-enus-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
