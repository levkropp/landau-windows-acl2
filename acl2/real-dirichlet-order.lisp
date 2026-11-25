(in-package "ACL2")

(include-book "real-dirichlet-damping")
(include-book "signal-exponential-growth")
(include-book "log-growth")

; With a common precision, the finite real samples inherit approximate order.

(local (defthm lw-rdo-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rdo-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rdo-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rdo-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rdo-times-negative (a b) (b a)))
                 :in-theory (disable lw-rdo-times-negative)))))

(local (defthm lw-rdo-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rdo-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rdo-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rdo-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rdo-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rdo-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rdo-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rdo-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdo-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdo-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rdo-left-commutes)))))

(local (deftheory lw-rdo-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-rdo-left-commutes lw-rdo-left-distributes lw-rdo-fold-constants
              lw-rdo-times-negative lw-rdo-negative-times lw-rdo-zero-times
              lw-rdo-minus-one lw-rdo-double-negative lw-rdo-add-cancel lw-rdo-double lw-rdo-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defthm lw-real-dirichlet-sample-real-part-bounds
  (implies
   (and (rationalp rate) (<= 0 rate) (rationalp index) (< 1 index)
       (rationalp limit) (<= index limit) (rationalp error) (< 0 error))
   (and (rationalp (car (lw-dirichlet-sample rate 0 index error error)))
        (<= (- (car (lw-exp-neg-bounds (lw-real-dirichlet-damping-argument rate index error) error)) (* (lw-real-dirichlet-damping-gain rate limit) error)) (car (lw-dirichlet-sample rate 0 index error error)))
        (<= (car (lw-dirichlet-sample rate 0 index error error)) (+ (car (lw-exp-neg-bounds (lw-real-dirichlet-damping-argument rate index error) error)) (* (lw-real-dirichlet-damping-gain rate limit) error)))))
  :hints (("Goal"
           :use (lw-real-dirichlet-sample-damping
                 (:instance lw-dirichlet-sample-rational (height 0) (log-error error) (node-error error))
                 (:instance lw-complex-disk-data
                   (point (lw-complex-sub (lw-dirichlet-sample rate 0 index error error) (cons (car (lw-exp-neg-bounds (lw-real-dirichlet-damping-argument rate index error) error)) 0))) (radius (* (lw-real-dirichlet-damping-gain rate limit) error)))
                 (:instance lw-complex-disk-coordinates
                   (point (lw-complex-sub (lw-dirichlet-sample rate 0 index error error) (cons (car (lw-exp-neg-bounds (lw-real-dirichlet-damping-argument rate index error) error)) 0))) (radius (* (lw-real-dirichlet-damping-gain rate limit) error))))
           :in-theory (union-theories '(lw-complex-sub lw-complexp abs) (theory 'lw-rdo-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defun lw-real-dirichlet-order-gain (rate limit)
  (+ 3 (* 2 (lw-real-dirichlet-damping-gain rate limit))
     (* rate (lw-exp-lipschitz-cap (* rate limit)))))

(local
 (defthm lw-rdo-log-decay-order
   (implies
    (and (rationalp rate) (<= 0 rate) (rationalp left) (< 1 left)
       (rationalp right) (<= left right) (rationalp limit) (<= right limit)
       (rationalp error) (< 0 error) (<= error 1))
    (and (rationalp (lw-real-dirichlet-damping-argument rate left error)) (rationalp (lw-real-dirichlet-damping-argument rate right error)) (rationalp (* rate (cdr (lw-log-bounds right error))))
         (<= 0 (lw-real-dirichlet-damping-argument rate left error)) (<= 0 (lw-real-dirichlet-damping-argument rate right error)) (<= 0 (* rate (cdr (lw-log-bounds right error))))
         (<= (lw-real-dirichlet-damping-argument rate left error) (* rate (cdr (lw-log-bounds right error)))) (<= (lw-real-dirichlet-damping-argument rate right error) (* rate (cdr (lw-log-bounds right error)))) (<= (* rate (cdr (lw-log-bounds right error))) (* rate limit))
         (<= (- (* rate (cdr (lw-log-bounds right error))) (lw-real-dirichlet-damping-argument rate right error)) (* rate error))))
   :hints (("Goal"
            :use ((:instance lw-log-bounds-interval (value left) (epsilon error))
                  (:instance lw-log-bounds-interval (value right) (epsilon error))
                  (:instance lw-log-bounds-lower-coarse (value left) (epsilon error))
                  (:instance lw-log-bounds-lower-coarse (value right) (epsilon error))
                  (:instance lw-log-bounds-width (value right) (epsilon error))
                  (:instance lw-log-bounds-monotone-overlap (left-error error) (right-error error))
                  (:instance lw-rdo-multiply-order (a 0) (b (car (lw-log-bounds left error))) (factor rate))
                  (:instance lw-rdo-multiply-order (a 0) (b (car (lw-log-bounds right error))) (factor rate))
                  (:instance lw-rdo-multiply-order (a (car (lw-log-bounds left error))) (b (cdr (lw-log-bounds right error))) (factor rate))
                  (:instance lw-rdo-multiply-order (a (car (lw-log-bounds right error))) (b (cdr (lw-log-bounds right error))) (factor rate))
                  (:instance lw-rdo-multiply-order (a (cdr (lw-log-bounds right error))) (b limit) (factor rate))
                  (:instance lw-rdo-multiply-order (a (- (cdr (lw-log-bounds right error)) (car (lw-log-bounds right error)))) (b error) (factor rate)))
            :in-theory (union-theories '(lw-real-dirichlet-damping-argument lw-complex-log-ramp-start lw-intervalp) (theory 'lw-rdo-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-rdo-damping-order
   (implies (and (rationalp rate) (<= 0 rate) (rationalp left) (< 1 left)
       (rationalp right) (<= left right) (rationalp limit) (<= right limit)
       (rationalp error) (< 0 error) (<= error 1))
            (<= (car (lw-exp-neg-bounds (lw-real-dirichlet-damping-argument rate right error) error)) (+ (car (lw-exp-neg-bounds (lw-real-dirichlet-damping-argument rate left error) error)) (* (+ 3 (* rate (lw-exp-lipschitz-cap (* rate limit)))) error))))
   :hints (("Goal"
            :use (lw-rdo-log-decay-order
                  (:instance lw-exp-lipschitz-cap-valid (cap (* rate limit)))
                  (:instance lw-exp-neg-bounds-decreasing-overlap
                    (left (lw-real-dirichlet-damping-argument rate left error)) (right (* rate (cdr (lw-log-bounds right error)))) (left-error error) (right-error error))
                  (:instance lw-exp-neg-bounds-valid (value (lw-real-dirichlet-damping-argument rate left error)) (epsilon error))
                  (:instance lw-exp-neg-bounds-valid (value (lw-real-dirichlet-damping-argument rate right error)) (epsilon error))
                  (:instance lw-exp-neg-bounds-valid (value (* rate (cdr (lw-log-bounds right error)))) (epsilon error))
                  (:instance lw-exp-neg-bounds-width (value (lw-real-dirichlet-damping-argument rate left error)) (epsilon error))
                  (:instance lw-exp-neg-bounds-spatial-cauchy
                    (left (lw-real-dirichlet-damping-argument rate right error)) (right (* rate (cdr (lw-log-bounds right error)))) (cap (* rate limit)) (left-error error) (right-error error))
                  (:instance lw-rdo-multiply-order (a (- (* rate (cdr (lw-log-bounds right error))) (lw-real-dirichlet-damping-argument rate right error))) (b (* rate error)) (factor (lw-exp-lipschitz-cap (* rate limit)))))
            :in-theory (union-theories '(lw-intervalp abs) (theory 'lw-rdo-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-real-dirichlet-sample-order
  (implies
   (and (rationalp rate) (<= 0 rate) (rationalp left) (< 1 left)
       (rationalp right) (<= left right) (rationalp limit) (<= right limit)
       (rationalp error) (< 0 error) (<= error 1))
   (<= (car (lw-dirichlet-sample rate 0 right error error)) (+ (car (lw-dirichlet-sample rate 0 left error error)) (* (lw-real-dirichlet-order-gain rate limit) error))))
  :hints (("Goal"
           :use (lw-rdo-damping-order
                 (:instance lw-real-dirichlet-sample-real-part-bounds (index left))
                 (:instance lw-real-dirichlet-sample-real-part-bounds (index right)))
           :in-theory (union-theories '(lw-real-dirichlet-order-gain) (theory 'lw-rdo-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-rdo-log-two-lower
   (implies (and (rationalp error) (< 0 error))
            (<= 1/2 (car (lw-log-bounds 2 error))))
   :hints (("Goal"
            :use ((:instance lw-log-grid-endpoint (value 2) (epsilon error))
                  (:instance lw-log-step-positive (value 2) (epsilon error))
                  (:instance lw-log-lower-constant-cap
                    (start 1) (step (/ (lw-log-count 2 error))) (count (lw-log-count 2 error)) (cap 2)))
            :in-theory (union-theories '(lw-log-bounds (:type-prescription lw-log-count)) (theory 'lw-rdo-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defun lw-real-dirichlet-first-gap (rate)
  (- 1 (/ (+ 1 (* 1/2 rate)))))

(defthm lw-real-dirichlet-first-gap-positive
  (implies (and (rationalp rate) (< 0 rate))
           (and (rationalp (lw-real-dirichlet-first-gap rate))
                (< 0 (lw-real-dirichlet-first-gap rate))))
  :hints (("Goal"
           :use ((:instance inverse-of-* (x (+ 1 (* 1/2 rate))))
                 (:instance lw-reciprocal-positive (value (+ 1 (* 1/2 rate))))
                 (:instance lw-rdo-positive-product (a rate) (b (/ (+ 1 (* 1/2 rate))))))
           :in-theory (union-theories '(lw-real-dirichlet-first-gap) (theory 'lw-rdo-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-real-dirichlet-first-pair
  (implies (and (rationalp rate) (<= 0 rate)
                (rationalp limit) (<= 2 limit) (rationalp error) (< 0 error))
           (<= (- (lw-real-dirichlet-first-gap rate) (* (lw-real-dirichlet-damping-gain rate limit) error))
               (- (car (lw-dirichlet-sample rate 0 1 error error)) (car (lw-dirichlet-sample rate 0 2 error error)))))
  :hints (("Goal"
           :use (lw-rdo-log-two-lower
                 (:instance lw-log-bounds-interval (value 2) (epsilon error))
                 (:instance lw-rdo-multiply-order (a 1/2) (b (car (lw-log-bounds 2 error))) (factor rate))
                 (:instance lw-exp-bounds-linear-lower (value (lw-real-dirichlet-damping-argument rate 2 error)))
                 (:instance lw-exp-bounds-valid (value (lw-real-dirichlet-damping-argument rate 2 error)) (epsilon error))
                 (:instance lw-reciprocal-antitone
                   (left (+ 1 (* 1/2 rate)))
                   (right (cdr (lw-exp-bounds (lw-real-dirichlet-damping-argument rate 2 error) error))))
                 (:instance lw-real-dirichlet-sample-real-part-bounds (index 2)))
           :expand ((lw-dirichlet-sample rate 0 1 error error))
           :in-theory (union-theories '(lw-real-dirichlet-damping-argument lw-complex-log-ramp-start lw-exp-neg-bounds lw-intervalp lw-real-dirichlet-first-gap) (theory 'lw-rdo-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
