(in-package "ACL2")

(include-book "complex-log-ramp-independent")

(include-book "smoothed-ramp-sums")

; Normalize the whole finite Mangoldt-weighted family at its fixed
; logarithmic cutpoints. Node precision is chosen independently of the
; frozen logarithm and coefficient precisions.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-lrf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-lrf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-lrf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-lrf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-lrf-times-negative (a b) (b a)))
                 :in-theory (disable lw-lrf-times-negative)))))

(local (defthm lw-lrf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-lrf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-lrf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-lrf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-lrf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-lrf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-lrf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-lrf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lrf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lrf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-lrf-left-commutes)))))

(local (defthm lw-lrf-point-data
         (implies (and (rationalp rate) (< 1 rate) (rationalp height)
                       (rationalp start) (<= 0 start) (rationalp index) (<= start index))
                  (and
                   (lw-complexp (cons start 0))
                   (lw-complexp (lw-complex-scale start (lw-complex-laplace-point rate height)))
                   (<= 0 (* rate start))
                   (<= 0 (* (+ rate (abs height)) index))
                   (<= (lw-complex-l1 (cons start 0)) index)
                   (<= (lw-complex-l1 (lw-complex-scale start (lw-complex-laplace-point rate height)))
                       (* (+ rate (abs height)) index))
                   (equal (lw-complex-add (cons start 0)
                             (lw-complex-scale start (lw-complex-laplace-point rate height)))
                          (lw-complex-scale start (lw-complex-laplace-point (- rate 1) height)))))
         :hints (("Goal" :cases ((<= 0 height))
                         :in-theory (enable lw-complexp lw-complex-add lw-complex-scale
                                            lw-complex-laplace-point lw-complex-l1)
                         :nonlinearp t))))

(local (defthm lw-lrf-cap-data
         (implies (and (rationalp rate) (< 1 rate) (rationalp height) (rationalp index) (< 1 index))
                  (and (rationalp (lw-complex-log-ramp-cap rate height index))
                       (<= 4 (lw-complex-log-ramp-cap rate height index))
                       (rationalp (lw-exp-lipschitz-cap index))
                       (<= 1 (lw-exp-lipschitz-cap index))))
         :hints (("Goal"
                  :use ((:instance lw-lrf-point-data (start 0))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap index))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap (* (+ rate (abs height)) index)))
                        (:instance lw-exp-lipschitz-cap-valid (cap index)))
                  :in-theory (e/d (lw-complex-log-ramp-cap)
                                  (lw-lrf-point-data lw-complex-exp-uniform-cap-data lw-exp-lipschitz-cap-valid))
                  :do-not-induct t))))

(local (defthm lw-lrf-unit-data
 (implies (and (natp total) (rationalp model-error) (< 0 model-error))
  (and (rationalp (lw-smoothed-ramp-unit-error total model-error))
       (< 0 (lw-smoothed-ramp-unit-error total model-error))))
 :hints (("Goal" :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t))
 :rule-classes nil))

(defun lw-complex-log-ramp-family-cost (rate height count)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) 0
  (+ (lw-complex-log-ramp-cap rate height count) 4
     (lw-complex-log-ramp-family-cost rate height (- count 1)))))

(defun lw-complex-log-ramp-family (normalizedp rate height count total model-error primitive-error delta)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) (cons 0 0)
  (let ((eta (lw-smoothed-ramp-log-error count total model-error)))
   (lw-complex-add
    (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error))
     (if normalizedp
      (lw-complex-log-ramp-independent-model rate height count eta delta)
      (lw-complex-log-ramp-independent-endpoint rate height count eta delta)))
    (lw-complex-log-ramp-family normalizedp rate height (- count 1) total model-error primitive-error delta)))))

(defun lw-complex-dirichlet-prime-sum (rate height count total model-error primitive-error delta)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (equal count 1)) (cons 0 0)
  (lw-complex-add
   (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error))
    (lw-complex-log-ramp-independent-exp
     rate height count (lw-smoothed-ramp-log-error count total model-error) delta))
   (lw-complex-dirichlet-prime-sum rate height (- count 1) total model-error primitive-error delta))))

(defthm lw-complex-log-ramp-family-cost-valid
 (implies (and (rationalp rate) (< 1 rate) (rationalp height) (natp count))
  (and (rationalp (lw-complex-log-ramp-family-cost rate height count))
       (<= 0 (lw-complex-log-ramp-family-cost rate height count))))
 :hints (("Goal" :induct (lw-complex-log-ramp-family-cost rate height count))
         (and stable-under-simplificationp
          '(:use ((:instance lw-lrf-cap-data (index count)))
            :in-theory (disable lw-lrf-cap-data) :do-not-induct t))))

(local (in-theory (disable lw-complex-log-ramp-family-cost lw-complex-log-ramp-family lw-complex-dirichlet-prime-sum)))

(defthm lw-complex-log-ramp-family-rational
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta))
  (lw-complexp (lw-complex-log-ramp-family normalizedp rate height count total model-error primitive-error delta)))
 :hints (("Goal"
   :induct (lw-complex-log-ramp-family normalizedp rate height count total model-error primitive-error delta)
   :in-theory (enable (:induction lw-complex-log-ramp-family) (:definition lw-complex-log-ramp-family)
                      lw-complexp lw-complex-add lw-complex-scale))
  (and stable-under-simplificationp
   '(:use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
           (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
           (:instance lw-complex-log-ramp-independent-endpoints-rational
            (index count) (log-error (lw-smoothed-ramp-log-error count total model-error))))
     :in-theory (e/d (lw-complexp lw-complex-add lw-complex-scale)
       (lw-complex-log-ramp-independent-endpoints-rational lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse))
     :do-not-induct t))))

(defthm lw-complex-dirichlet-prime-sum-rational
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta))
  (lw-complexp (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error delta)))
 :hints (("Goal"
   :induct (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error delta)
   :in-theory (enable (:induction lw-complex-dirichlet-prime-sum) (:definition lw-complex-dirichlet-prime-sum)
                      lw-complexp lw-complex-add lw-complex-scale))
  (and stable-under-simplificationp
   '(:use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
           (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
           (:instance lw-complex-log-ramp-independent-exp-rational
            (index count) (log-error (lw-smoothed-ramp-log-error count total model-error))))
     :in-theory (e/d (lw-complexp lw-complex-add lw-complex-scale)
       (lw-complex-log-ramp-independent-exp-rational lw-smoothed-ramp-log-error-adequate lw-mangoldt-lower-coarse))
     :do-not-induct t))))

(local (defthm lw-lrf-factor-sum
 (equal
  (lw-complex-add (lw-complex-scale weight (lw-complex-mul point factor)) (lw-complex-mul rest factor))
  (lw-complex-mul (lw-complex-add (lw-complex-scale weight point) rest) factor))
 :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-mul lw-complex-scale)))))

(local (defthm lw-lrf-zero-product
 (equal (lw-complex-mul (cons 0 0) point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-mul)))))

(defthm lw-complex-log-ramp-family-factorization
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta))
  (equal
   (lw-complex-log-ramp-family t rate height count total model-error primitive-error delta)
   (lw-complex-mul
    (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error delta)
    (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height))))))
 :hints (("Goal"
   :induct (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error delta)
   :in-theory (enable (:induction lw-complex-dirichlet-prime-sum)
                      (:definition lw-complex-dirichlet-prime-sum) (:definition lw-complex-log-ramp-family)))
  (and stable-under-simplificationp
   '(:use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
           (:instance lw-complex-log-ramp-independent-model-identity
            (index count) (log-error (lw-smoothed-ramp-log-error count total model-error))))
     :in-theory (disable lw-complex-log-ramp-independent-model-identity lw-smoothed-ramp-log-error-adequate)
     :do-not-induct t))))

(local (in-theory (disable lw-complex-log-ramp-family-factorization)))

(local (defthm lw-lrf-scale-difference
 (equal (lw-complex-sub (lw-complex-scale factor left) (lw-complex-scale factor right))
        (lw-complex-scale factor (lw-complex-sub left right)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))

(local (defthm lw-lrf-weighted-radius
 (implies
  (and (rationalp index) (< 0 index) (rationalp weight) (<= 0 weight) (<= weight index)
       (rationalp raw) (<= 0 raw) (rationalp budget) (<= raw budget)
       (rationalp clearance) (< 0 clearance))
  (<= (* weight raw (/ index) (/ clearance)) (* budget (/ clearance))))
 :hints (("Goal"
   :use ((:instance lw-positive-division-bound (numerator weight) (divisor index) (bound 1))
         (:instance lw-lrf-multiply-order (a (* weight (/ index))) (b 1) (factor raw))
         (:instance lw-lrf-multiply-order (a (* weight raw (/ index))) (b raw) (factor (/ clearance)))
         (:instance lw-lrf-multiply-order (a raw) (b budget) (factor (/ clearance))))
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-lrf-raw-radius
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp delta) (<= 0 delta)
       (rationalp slope) (<= 0 slope) (rationalp eta) (<= 0 eta)
       (rationalp budget) (<= (* slope eta) budget))
  (and (rationalp (+ (* (+ cap 4) delta) (* 2 slope eta)))
       (<= 0 (+ (* (+ cap 4) delta) (* 2 slope eta)))
       (<= (+ (* (+ cap 4) delta) (* 2 slope eta)) (+ (* (+ cap 4) delta) (* 2 budget)))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-lrf-weighted-normalization
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (< 1 count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta) (<= delta 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-complex-log-ramp-independent-endpoint rate height count (lw-smoothed-ramp-log-error count total model-error) delta)) (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-complex-log-ramp-independent-model rate height count (lw-smoothed-ramp-log-error count total model-error) delta))) (* (+ (* (+ (lw-complex-log-ramp-cap rate height count) 4) delta) (* 2 (lw-smoothed-ramp-unit-error total model-error))) (/ (- rate 1)))))
 :hints (("Goal"
   :use ((:instance lw-smoothed-ramp-log-error-adequate (index count) (error model-error))
         lw-lrf-unit-data (:instance lw-lrf-cap-data (index count))
         (:instance lw-mangoldt-lower-coarse (index count) (epsilon primitive-error))
         (:instance lw-complex-log-ramp-independent-endpoint-normalization (index count) (log-error (lw-smoothed-ramp-log-error count total model-error)))
         (:instance lw-lrf-raw-radius (cap (lw-complex-log-ramp-cap rate height count)) (slope (lw-exp-lipschitz-cap count)) (eta (lw-smoothed-ramp-log-error count total model-error)) (budget (lw-smoothed-ramp-unit-error total model-error)))
         (:instance lw-lrf-weighted-radius
          (index count) (weight (car (lw-mangoldt-bounds count primitive-error))) (raw (+ (* (+ (lw-complex-log-ramp-cap rate height count) 4) delta) (* 2 (lw-exp-lipschitz-cap count) (lw-smoothed-ramp-log-error count total model-error))))
          (budget (+ (* (+ (lw-complex-log-ramp-cap rate height count) 4) delta) (* 2 (lw-smoothed-ramp-unit-error total model-error)))) (clearance (- rate 1)))
         (:instance lw-complex-scale-disk
          (factor (car (lw-mangoldt-bounds count primitive-error))) (point (lw-complex-sub (lw-complex-log-ramp-independent-endpoint rate height count (lw-smoothed-ramp-log-error count total model-error) delta) (lw-complex-log-ramp-independent-model rate height count (lw-smoothed-ramp-log-error count total model-error) delta))) (radius (* (+ (* (+ (lw-complex-log-ramp-cap rate height count) 4) delta) (* 2 (lw-exp-lipschitz-cap count) (lw-smoothed-ramp-log-error count total model-error))) (/ count) (/ (- rate 1)))))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-complex-log-ramp-independent-endpoint rate height count (lw-smoothed-ramp-log-error count total model-error) delta)) (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-complex-log-ramp-independent-model rate height count (lw-smoothed-ramp-log-error count total model-error) delta))))
          (radius (* (car (lw-mangoldt-bounds count primitive-error)) (+ (* (+ (lw-complex-log-ramp-cap rate height count) 4) delta) (* 2 (lw-exp-lipschitz-cap count) (lw-smoothed-ramp-log-error count total model-error))) (/ count) (/ (- rate 1)))) (cap (* (+ (* (+ (lw-complex-log-ramp-cap rate height count) 4) delta) (* 2 (lw-smoothed-ramp-unit-error total model-error))) (/ (- rate 1))))))
   :in-theory (disable lw-smoothed-ramp-log-error-adequate lw-lrf-cap-data lw-mangoldt-lower-coarse
                       lw-complex-log-ramp-independent-endpoint-normalization lw-complex-scale-disk)
   :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-lrf-add-differences
 (equal (lw-complex-sub (lw-complex-add left rest) (lw-complex-add right other))
        (lw-complex-add (lw-complex-sub left right) (lw-complex-sub rest other)))
 :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))
(local (defthm lw-lrf-sub-self (equal (lw-complex-sub point point) (cons 0 0))
 :hints (("Goal" :in-theory (enable lw-complex-sub)))))
(local (defthm lw-lrf-zero-disk (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (defthm lw-lrf-family-zero
 (implies (or (zp count) (equal count 1))
  (equal (lw-complex-log-ramp-family normalizedp rate height count total model-error primitive-error delta) (cons 0 0)))
 :hints (("Goal" :in-theory (enable lw-complex-log-ramp-family)))))
(local (defthm lw-lrf-cost-zero
 (implies (or (zp count) (equal count 1))
  (equal (lw-complex-log-ramp-family-cost rate height count) 0))
 :hints (("Goal" :in-theory (enable lw-complex-log-ramp-family-cost)))))

(defthm lw-complex-log-ramp-family-normalization
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp delta) (< 0 delta) (<= delta 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-log-ramp-family nil rate height count total model-error primitive-error delta)
    (lw-complex-log-ramp-family t rate height count total model-error primitive-error delta))
   (* (+ (* delta (lw-complex-log-ramp-family-cost rate height count)) (* 2 (nfix (- count 1)) (lw-smoothed-ramp-unit-error total model-error)))
      (/ (- rate 1)))))
 :hints (("Goal"
   :induct (lw-complex-log-ramp-family nil rate height count total model-error primitive-error delta)
   :in-theory (enable (:induction lw-complex-log-ramp-family)))
  (and stable-under-simplificationp
   '(:use (lw-lrf-unit-data lw-lrf-weighted-normalization
           lw-complex-log-ramp-family-cost-valid
           (:instance lw-complex-log-ramp-family-cost-valid (count (- count 1)))
           (:instance lw-lrf-cap-data (index count))
           (:instance lw-complex-add-disk
            (left (lw-complex-sub (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-complex-log-ramp-independent-endpoint rate height count (lw-smoothed-ramp-log-error count total model-error) delta)) (lw-complex-scale (car (lw-mangoldt-bounds count primitive-error)) (lw-complex-log-ramp-independent-model rate height count (lw-smoothed-ramp-log-error count total model-error) delta))))
            (right (lw-complex-sub
              (lw-complex-log-ramp-family nil rate height (- count 1) total model-error primitive-error delta)
              (lw-complex-log-ramp-family t rate height (- count 1) total model-error primitive-error delta)))
            (radius (* (+ (* (+ (lw-complex-log-ramp-cap rate height count) 4) delta) (* 2 (lw-smoothed-ramp-unit-error total model-error))) (/ (- rate 1))))
            (other-radius
             (* (+ (* delta (lw-complex-log-ramp-family-cost rate height (- count 1)))
                   (* 2 (nfix (- count 2)) (lw-smoothed-ramp-unit-error total model-error))) (/ (- rate 1)))))
           (:instance lw-complex-disk-enlarge
            (point (lw-complex-sub
              (lw-complex-log-ramp-family nil rate height count total model-error primitive-error delta)
              (lw-complex-log-ramp-family t rate height count total model-error primitive-error delta)))
            (radius (+ (* (+ (* (+ (lw-complex-log-ramp-cap rate height count) 4) delta) (* 2 (lw-smoothed-ramp-unit-error total model-error))) (/ (- rate 1)))
              (* (+ (* delta (lw-complex-log-ramp-family-cost rate height (- count 1)))
                    (* 2 (nfix (- count 2)) (lw-smoothed-ramp-unit-error total model-error))) (/ (- rate 1)))))
            (cap (* (+ (* delta (lw-complex-log-ramp-family-cost rate height count))
                       (* 2 (nfix (- count 1)) (lw-smoothed-ramp-unit-error total model-error))) (/ (- rate 1))))))
     :expand ((lw-complex-log-ramp-family-cost rate height count)
              (lw-complex-log-ramp-family nil rate height count total model-error primitive-error delta)
              (lw-complex-log-ramp-family t rate height count total model-error primitive-error delta))
     :in-theory (disable lw-complex-log-ramp-family lw-complex-log-ramp-family-cost lw-complex-add-disk
                         lw-complex-log-ramp-family-factorization lw-complex-log-ramp-family-cost-valid lw-lrf-cap-data)
     :nonlinearp nil :do-not-induct t))))

(defun lw-complex-log-ramp-family-precision (rate height count error)
 (min 1 (/ (* (- rate 1) error) (* 16 (+ 1 (lw-complex-log-ramp-family-cost rate height count))))))

(local (in-theory (disable lw-complex-log-ramp-family-precision)))

(local (defthm lw-lrf-precision-scalar
 (implies (and (rationalp cost) (<= 0 cost) (rationalp clearance) (< 0 clearance)
               (rationalp error) (< 0 error))
  (let ((delta (min 1 (/ (* clearance error) (* 16 (+ 1 cost))))))
   (and (rationalp delta) (< 0 delta) (<= delta 1)
        (<= (* cost delta (/ clearance)) (* 1/16 error)))))
 :hints (("Goal"
   :use ((:instance inverse-of-* (x clearance))
         (:instance lw-positive-division-bound
          (numerator (* cost error)) (divisor (* 16 (+ 1 cost))) (bound (* 1/16 error)))
         (:instance lw-lrf-multiply-order
          (a (min 1 (/ (* clearance error) (* 16 (+ 1 cost)))))
          (b (/ (* clearance error) (* 16 (+ 1 cost)))) (factor (* cost (/ clearance)))))
   :in-theory (disable inverse-of-*) :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-log-ramp-family-precision-valid
 (implies (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (rationalp error) (< 0 error))
  (let ((delta (lw-complex-log-ramp-family-precision rate height count error)))
   (and (rationalp delta) (< 0 delta) (<= delta 1)
        (<= (* (lw-complex-log-ramp-family-cost rate height count) delta (/ (- rate 1))) (* 1/16 error)))))
 :hints (("Goal"
   :use (lw-complex-log-ramp-family-cost-valid
         (:instance lw-lrf-precision-scalar (cost (lw-complex-log-ramp-family-cost rate height count)) (clearance (- rate 1))))
   :in-theory (e/d (lw-complex-log-ramp-family-precision) (lw-complex-log-ramp-family-cost-valid))
   :nonlinearp nil :do-not-induct t)))

(local (defthm lw-lrf-log-budget-scalar
 (implies (and (natp count) (natp total) (<= count total) (rationalp model-error) (< 0 model-error))
  (<= (* 2 (nfix (- count 1)) (lw-smoothed-ramp-unit-error total model-error)) (* 1/8 model-error)))
 :hints (("Goal"
   :use ((:instance lw-positive-division-bound
          (numerator (* (nfix (- count 1)) model-error))
          (divisor (+ 1 total)) (bound model-error)))
   :in-theory (enable lw-smoothed-ramp-unit-error) :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-log-ramp-family-log-budget
 (implies
  (and (rationalp rate) (< 1 rate) (natp count) (natp total) (<= count total)
       (rationalp model-error) (< 0 model-error))
  (<= (* 2 (nfix (- count 1)) (lw-smoothed-ramp-unit-error total model-error) (/ (- rate 1))) (* 1/8 model-error (/ (- rate 1)))))
 :hints (("Goal"
   :use (lw-lrf-unit-data lw-lrf-log-budget-scalar
         (:instance lw-lrf-multiply-order
          (a (* 2 (nfix (- count 1)) (lw-smoothed-ramp-unit-error total model-error))) (b (* 1/8 model-error)) (factor (/ (- rate 1)))))
   :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-log-ramp-family-computed-normalization
 (implies
  (and (rationalp rate) (< 1 rate) (rationalp height) (natp count) (natp total) (<= count total)
       (rationalp model-error) (< 0 model-error) (rationalp primitive-error) (< 0 primitive-error)
       (rationalp error) (< 0 error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-log-ramp-family nil rate height count total model-error primitive-error (lw-complex-log-ramp-family-precision rate height count error)) (lw-complex-mul
      (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error (lw-complex-log-ramp-family-precision rate height count error))
      (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))))
                   (+ (* 1/16 error) (* 1/8 model-error (/ (- rate 1))))))
 :hints (("Goal"
   :use (lw-complex-log-ramp-family-precision-valid lw-complex-log-ramp-family-log-budget
         (:instance lw-complex-log-ramp-family-normalization (delta (lw-complex-log-ramp-family-precision rate height count error)))
         (:instance lw-complex-log-ramp-family-factorization (delta (lw-complex-log-ramp-family-precision rate height count error)))
         (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (lw-complex-log-ramp-family nil rate height count total model-error primitive-error (lw-complex-log-ramp-family-precision rate height count error)) (lw-complex-mul
      (lw-complex-dirichlet-prime-sum rate height count total model-error primitive-error (lw-complex-log-ramp-family-precision rate height count error))
      (lw-complex-reciprocal (lw-complex-mul (cons (- rate 1) height) (cons rate height)))))) (radius (* (+ (* (lw-complex-log-ramp-family-precision rate height count error) (lw-complex-log-ramp-family-cost rate height count)) (* 2 (nfix (- count 1)) (lw-smoothed-ramp-unit-error total model-error))) (/ (- rate 1))))
          (cap (+ (* 1/16 error) (* 1/8 model-error (/ (- rate 1)))))))
   :in-theory (disable lw-complex-log-ramp-family-precision-valid lw-complex-log-ramp-family-log-budget
                       lw-complex-log-ramp-family-normalization lw-complex-log-ramp-family-factorization)
   :nonlinearp nil :do-not-induct t)))



