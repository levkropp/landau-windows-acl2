; Failed window search bounds the actual normalized Euler coefficients.
(in-package "ACL2")
(include-book "euler-mellin-native-coefficients")
(include-book "mellin-dyadic-normalization")
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

(local (in-theory (disable lw-complex-log-ramp-exp lw-complex-log-ramp-endpoint lw-complex-log-ramp-model)))
(local (in-theory (disable lw-landau-window-search lw-kernel-window-threshold
 (:executable-counterpart lw-kernel-window-threshold) lw-window-index lw-log-bounds
 lw-complex-mellin-euler-coefficient-value lw-mellin-integral lw-rational-power)))
(local (defthm lw-ewc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewc-times-negative)))))

(local (defthm lw-ewc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewc-left-commutes)))))
(local (defthm lw-ewc-index-natural
 (natp (lw-window-index start))
 :hints (("Goal" :use ((:instance lw-window-index-natural (lower (car (lw-log-bounds start 1/1000)))))
 :in-theory (union-theories
 '(lw-window-index lw-ewc-left-commutes lw-ewc-left-distributes lw-ewc-fold-constants lw-ewc-times-negative lw-ewc-negative-times lw-ewc-zero-times lw-ewc-minus-one lw-ewc-double-negative lw-ewc-add-cancel lw-ewc-double lw-ewc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))))
(defun lw-euler-window-mass (ceiling numerator denominator index)
 (* (+ (* 8 ceiling) 10) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))))
(defun lw-euler-window-coefficient-radius-at (index ceiling numerator denominator coefficient-error real-error)
 (+ (lw-euler-window-mass ceiling numerator denominator index) (- (car (lw-complex-mellin-euler-coefficient-value 252 0 index real-error))) (* 1/2 (+ coefficient-error real-error))))

(defun lw-euler-window-coefficient-radius (start ceiling numerator denominator coefficient-error real-error)
  (lw-euler-window-coefficient-radius-at (lw-window-index start)
    ceiling numerator denominator coefficient-error real-error))

(local (in-theory (disable lw-euler-window-mass lw-euler-window-coefficient-radius lw-euler-window-coefficient-radius-at)))

(defthm lw-euler-window-mass-data
 (implies (and (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator) (natp index))
 (and (rationalp (lw-euler-window-mass ceiling numerator denominator index)) (< 0 (lw-euler-window-mass ceiling numerator denominator index))))
 :hints (("Goal"
 :use ((:instance lw-positive-division-bound (numerator numerator) (divisor denominator) (bound 1))
       (:instance lw-reciprocal-positive (value (- 252 (/ numerator denominator))))
       (:instance lw-rational-power-rational (base (/ (- 252 (/ numerator denominator)))) (exponent (+ 1 index)))
       (:instance lw-rational-power-positive (base (/ (- 252 (/ numerator denominator)))) (exponent (+ 1 index)))
       (:instance lw-ewc-positive-product (a (+ (* 8 ceiling) 10)) (b (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index)))))
 :in-theory (union-theories
 '(lw-euler-window-mass lw-ewc-left-commutes lw-ewc-left-distributes lw-ewc-fold-constants lw-ewc-times-negative lw-ewc-negative-times lw-ewc-zero-times lw-ewc-minus-one lw-ewc-double-negative lw-ewc-add-cancel lw-ewc-double lw-ewc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-ewc-coefficient-at-data
 (implies (and (natp index) (rationalp height) (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator) (rationalp coefficient-error) (< 0 coefficient-error) (rationalp real-error) (< 0 real-error))
 (and (natp index) (lw-complexp (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error)) (lw-complexp (lw-complex-mellin-euler-coefficient-value 252 0 index real-error)) (rationalp (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error))))
 :hints (("Goal"
 :use ((:instance lw-euler-window-mass-data (index index))
       (:instance lw-complex-mellin-euler-coefficient-rational (rate 252) (index index) (error coefficient-error))
       (:instance lw-complex-mellin-euler-coefficient-rational (rate 252) (height 0) (index index) (error real-error)))
 :in-theory (union-theories
 '(lw-euler-window-coefficient-radius-at lw-complexp lw-ewc-left-commutes lw-ewc-left-distributes lw-ewc-fold-constants lw-ewc-times-negative lw-ewc-negative-times lw-ewc-zero-times lw-ewc-minus-one lw-ewc-double-negative lw-ewc-add-cancel lw-ewc-double lw-ewc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
  :rule-classes nil))

(local (defthm lw-ewc-real-replacement
 (implies (and (lw-complexp value) (lw-complexp other) (rationalp error)
 (lw-complex-diskp (lw-complex-sub value other) error))
 (<= (- (car other) (car value)) error))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-real-bound (point (lw-complex-sub value other)) (radius error)))
 :in-theory (union-theories
 '(lw-complexp lw-complex-sub abs lw-ewc-left-commutes lw-ewc-left-distributes lw-ewc-fold-constants lw-ewc-times-negative lw-ewc-negative-times lw-ewc-zero-times lw-ewc-minus-one lw-ewc-double-negative lw-ewc-add-cancel lw-ewc-double lw-ewc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ewc-bound-at-with-margin
 (implies (and (rationalp start) (< 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp index)
                (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000))) index)
                (<= index (* 625/2 (car (lw-log-bounds start 1/1000))))
                (<= (lw-geometric-index 5000/4977 128) index)
 (rationalp height) (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
 (not (lw-landau-window-search start ceiling numerator denominator))
 (rationalp coefficient-error) (< 0 coefficient-error) (rationalp real-error) (< 0 real-error) (rationalp margin) (< 0 margin))
 (lw-complex-diskp (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error) (+ (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error) (* 11 margin))))
 :hints (("Goal"
 :use (lw-ewc-coefficient-at-data
       (:instance lw-rational-power-rational (base (/ (- 252 (/ numerator denominator)))) (exponent (+ 1 index)))
       (:instance lw-mellin-integral-rational (sigma 252) (index index) (error margin))
       (:instance lw-mellin-integral-rational (sigma 252) (height 0) (index index) (error margin))
       (:instance lw-failed-search-improper-coefficient-normalized (error margin))
       (:instance lw-mellin-euler-native-moment-comparison (rate 252) (index index) (integral-error margin))
       (:instance lw-mellin-euler-native-moment-comparison (rate 252) (height 0) (index index) (coefficient-error real-error) (integral-error margin))
       (:instance lw-ewc-real-replacement (value (lw-mellin-integral 252 0 index margin)) (other (lw-complex-mellin-euler-coefficient-value 252 0 index real-error)) (error (+ (* 5 margin) (* 1/2 real-error))))
       (:instance lw-complex-difference-symmetric (left (lw-mellin-integral 252 height index margin)) (right (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error)) (radius (+ (* 5 margin) (* 1/2 coefficient-error))))
       (:instance lw-complex-difference-triangle (left (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error)) (middle (lw-mellin-integral 252 height index margin)) (right (cons 0 0))
        (radius (+ (* 5 margin) (* 1/2 coefficient-error))) (other-radius (+ (lw-euler-window-mass ceiling numerator denominator index) (- (car (lw-mellin-integral 252 0 index margin))) margin)))
       (:instance lw-complex-disk-enlarge (point (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error)) (radius (+ (+ (* 5 margin) (* 1/2 coefficient-error)) (+ (lw-euler-window-mass ceiling numerator denominator index) (- (car (lw-mellin-integral 252 0 index margin))) margin)))
        (cap (+ (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error) (* 11 margin)))))
 :in-theory (union-theories
 '(lw-euler-window-mass lw-euler-window-coefficient-radius-at lw-complex-sub-zero (:executable-counterpart lw-complexp) lw-complexp lw-ewc-left-commutes lw-ewc-left-distributes lw-ewc-fold-constants lw-ewc-times-negative lw-ewc-negative-times lw-ewc-zero-times lw-ewc-minus-one lw-ewc-double-negative lw-ewc-add-cancel lw-ewc-double lw-ewc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-ewc-radius-at-nonnegative
 (implies (and (rationalp start) (< 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp index)
                (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000))) index)
                (<= index (* 625/2 (car (lw-log-bounds start 1/1000))))
                (<= (lw-geometric-index 5000/4977 128) index)
 (rationalp height) (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
 (not (lw-landau-window-search start ceiling numerator denominator))
 (rationalp coefficient-error) (< 0 coefficient-error) (rationalp real-error) (< 0 real-error))
 (<= 0 (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error)))
 :hints (("Goal"
 :cases ((< (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error) 0))
 :use (lw-ewc-coefficient-at-data
       (:instance lw-ewc-bound-at-with-margin (margin (if (< (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error) 0) (- (* 1/22 (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error))) 1)))
       (:instance lw-complex-disk-data (point (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error)) (radius (+ (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error) (* 11 (if (< (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error) 0) (- (* 1/22 (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error))) 1))))))
 :in-theory (union-theories
 '( lw-ewc-left-commutes lw-ewc-left-distributes lw-ewc-fold-constants lw-ewc-times-negative lw-ewc-negative-times lw-ewc-zero-times lw-ewc-minus-one lw-ewc-double-negative lw-ewc-add-cancel lw-ewc-double lw-ewc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
  :rule-classes nil))

(defthm lw-failed-search-euler-coefficient-bound-at
 (implies (and (rationalp start) (< 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp index)
                (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000))) index)
                (<= index (* 625/2 (car (lw-log-bounds start 1/1000))))
                (<= (lw-geometric-index 5000/4977 128) index)
 (rationalp height) (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
 (not (lw-landau-window-search start ceiling numerator denominator))
 (rationalp coefficient-error) (< 0 coefficient-error) (rationalp real-error) (< 0 real-error))
 (lw-complex-diskp (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error) (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error)))
 :hints (("Goal"
 :cases ((lw-complex-diskp (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error) (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error)))
 :use (lw-ewc-coefficient-at-data lw-ewc-radius-at-nonnegative
       (:instance lw-complex-disk-gap-refinement-excludes (point (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error)) (radius (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error)) (cost 11))
       (:instance lw-ewc-bound-at-with-margin (margin (lw-disk-gap-refinement (lw-complex-mellin-euler-coefficient-value 252 height index coefficient-error) (lw-euler-window-coefficient-radius-at index ceiling numerator denominator coefficient-error real-error) 11))))
 :in-theory (union-theories
 '( lw-ewc-left-commutes lw-ewc-left-distributes lw-ewc-fold-constants lw-ewc-times-negative lw-ewc-negative-times lw-ewc-zero-times lw-ewc-minus-one lw-ewc-double-negative lw-ewc-add-cancel lw-ewc-double lw-ewc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-window-coefficient-data
 (implies (and (rationalp height) (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator) (rationalp coefficient-error) (< 0 coefficient-error) (rationalp real-error) (< 0 real-error))
 (and (natp (lw-window-index start)) (lw-complexp (lw-complex-mellin-euler-coefficient-value 252 height (lw-window-index start) coefficient-error)) (lw-complexp (lw-complex-mellin-euler-coefficient-value 252 0 (lw-window-index start) real-error)) (rationalp (lw-euler-window-coefficient-radius start ceiling numerator denominator coefficient-error real-error))))
 :hints (("Goal"
          :use ((:instance lw-ewc-coefficient-at-data (index (lw-window-index start)))
                lw-ewc-index-natural)
          :in-theory
          (union-theories
           '(lw-euler-window-coefficient-radius lw-kernel-window-threshold
             max natp lw-geometric-index-natural)
           (theory 'minimal-theory))
          :do-not-induct t)))

(defthm lw-euler-window-coefficient-radius-nonnegative
 (implies (and (rationalp start) (< 1 start) (<= (lw-kernel-window-threshold) start)
 (rationalp height) (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
 (not (lw-landau-window-search start ceiling numerator denominator))
 (rationalp coefficient-error) (< 0 coefficient-error) (rationalp real-error) (< 0 real-error))
 (<= 0 (lw-euler-window-coefficient-radius start ceiling numerator denominator coefficient-error real-error)))
 :hints (("Goal"
          :use ((:instance lw-ewc-radius-at-nonnegative (index (lw-window-index start)))
                (:instance lw-eventual-kernel-window-data
                  (target (max 64 (lw-geometric-index 5000/4977 128)))))
          :in-theory
          (union-theories
           '(lw-euler-window-coefficient-radius lw-kernel-window-threshold
             max natp lw-geometric-index-natural)
           (theory 'minimal-theory))
          :do-not-induct t)))

(defthm lw-eventual-failed-search-euler-coefficient-bound
 (implies (and (rationalp start) (< 1 start) (<= (lw-kernel-window-threshold) start)
 (rationalp height) (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
 (not (lw-landau-window-search start ceiling numerator denominator))
 (rationalp coefficient-error) (< 0 coefficient-error) (rationalp real-error) (< 0 real-error))
 (lw-complex-diskp (lw-complex-mellin-euler-coefficient-value 252 height (lw-window-index start) coefficient-error) (lw-euler-window-coefficient-radius start ceiling numerator denominator coefficient-error real-error)))
 :hints (("Goal"
          :use ((:instance lw-failed-search-euler-coefficient-bound-at (index (lw-window-index start)))
                (:instance lw-eventual-kernel-window-data
                  (target (max 64 (lw-geometric-index 5000/4977 128)))))
          :in-theory
          (union-theories
           '(lw-euler-window-coefficient-radius lw-kernel-window-threshold
             max natp lw-geometric-index-natural)
           (theory 'minimal-theory))
          :do-not-induct t)))

(defthm lw-eventual-failed-search-euler-coefficient-same-error
 (implies (and (rationalp start) (< 1 start) (<= (lw-kernel-window-threshold) start)
 (rationalp height) (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
 (not (lw-landau-window-search start ceiling numerator denominator)) (rationalp error) (< 0 error))
 (lw-complex-diskp (lw-complex-mellin-euler-coefficient-value 252 height (lw-window-index start) error)
  (+ (lw-euler-window-mass ceiling numerator denominator (lw-window-index start)) (- (car (lw-complex-mellin-euler-coefficient-value 252 0 (lw-window-index start) error))) error)))
 :hints (("Goal"
 :use ((:instance lw-eventual-failed-search-euler-coefficient-bound (coefficient-error error) (real-error error)))
 :in-theory (union-theories
 '(lw-euler-window-coefficient-radius lw-euler-window-coefficient-radius-at lw-ewc-left-commutes lw-ewc-left-distributes lw-ewc-fold-constants lw-ewc-times-negative lw-ewc-negative-times lw-ewc-zero-times lw-ewc-minus-one lw-ewc-double-negative lw-ewc-add-cancel lw-ewc-double lw-ewc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))


