(in-package "ACL2")

(include-book "mangoldt-dirichlet-convolution")
(include-book "complex-exp-negative")

; Real Dirichlet samples agree with rational bounds for positive damping.

(local (defthm lw-rdd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-rdd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-rdd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-rdd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-rdd-times-negative (a b) (b a)))
                 :in-theory (disable lw-rdd-times-negative)))))

(local (defthm lw-rdd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-rdd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-rdd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-rdd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-rdd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-rdd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-rdd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-rdd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-rdd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-rdd-left-commutes)))))

(local (deftheory lw-rdd-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-rdd-left-commutes lw-rdd-left-distributes lw-rdd-fold-constants
              lw-rdd-times-negative lw-rdd-negative-times lw-rdd-zero-times
              lw-rdd-minus-one lw-rdd-double-negative lw-rdd-add-cancel lw-rdd-double lw-rdd-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defthm lw-exp-neg-bounds-decreasing-overlap
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right))
           (<= (car (lw-exp-neg-bounds right right-error))
               (cdr (lw-exp-neg-bounds left left-error))))
  :hints (("Goal"
           :use (lw-exp-bounds-monotone-overlap
                 (:instance lw-exp-bounds-valid (value left) (epsilon left-error))
                 (:instance lw-exp-bounds-valid (value right) (epsilon right-error))
                 (:instance lw-reciprocal-antitone
                   (left (car (lw-exp-bounds left left-error)))
                   (right (cdr (lw-exp-bounds right right-error)))))
           :in-theory (union-theories '(lw-exp-neg-bounds lw-intervalp) (theory 'lw-rdd-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defun lw-real-dirichlet-damping-argument (rate index error)
  (* rate (lw-complex-log-ramp-start index error)))

(defun lw-real-dirichlet-damping-gain (rate limit)
  (+ 4 (* 2 (lw-complex-exp-uniform-cap (* rate limit)))))

(local
 (defthm lw-rdd-decay-data
   (implies
    (and (rationalp rate) (<= 0 rate) (rationalp index) (< 1 index)
       (rationalp limit) (<= index limit) (rationalp error) (< 0 error))
    (and (rationalp (lw-real-dirichlet-damping-argument rate index error)) (<= 0 (lw-real-dirichlet-damping-argument rate index error)) (<= (lw-real-dirichlet-damping-argument rate index error) (* rate limit))
         (rationalp (lw-complex-exp-cap (cons (lw-real-dirichlet-damping-argument rate index error) 0))) (<= (lw-complex-exp-cap (cons (lw-real-dirichlet-damping-argument rate index error) 0)) (lw-complex-exp-uniform-cap (* rate limit)))))
   :hints (("Goal"
            :use ((:instance lw-log-bounds-interval (value index) (epsilon error))
                  (:instance lw-log-bounds-lower-coarse (value index) (epsilon error))
                  (:instance lw-rdd-multiply-order (a 0) (b (car (lw-log-bounds index error))) (factor rate))
                  (:instance lw-rdd-multiply-order (a (car (lw-log-bounds index error))) (b limit) (factor rate))
                  (:instance lw-rdd-multiply-order (a 0) (b limit) (factor rate))
                  (:instance lw-complex-exp-cap-valid (point (cons (lw-real-dirichlet-damping-argument rate index error) 0)))
                  (:instance lw-complex-exp-cap-uniform (point (cons (lw-real-dirichlet-damping-argument rate index error) 0)) (argument-cap (* rate limit))))
            :in-theory (union-theories '(lw-real-dirichlet-damping-argument lw-complex-log-ramp-start lw-intervalp lw-complexp lw-complex-l1 abs) (theory 'lw-rdd-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-real-dirichlet-sample-damping
  (implies
   (and (rationalp rate) (<= 0 rate) (rationalp index) (< 1 index)
       (rationalp limit) (<= index limit) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub (lw-dirichlet-sample rate 0 index error error) (cons (car (lw-exp-neg-bounds (lw-real-dirichlet-damping-argument rate index error) error)) 0))
    (* (lw-real-dirichlet-damping-gain rate limit) error)))
  :hints (("Goal"
           :use (lw-rdd-decay-data
                 (:instance lw-complex-exp-uniform-cap-data (argument-cap (* rate limit)))
                 (:instance lw-rdd-multiply-order (a (+ 3 (* 2 (lw-complex-exp-cap (cons (lw-real-dirichlet-damping-argument rate index error) 0))))) (b (+ 3 (* 2 (lw-complex-exp-uniform-cap (* rate limit))))) (factor error))
                 (:instance lw-complex-exp-negative-agreement (value (lw-real-dirichlet-damping-argument rate index error)) (left-error error) (right-error error))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-dirichlet-sample rate 0 index error error) (cons (car (lw-exp-neg-bounds (lw-real-dirichlet-damping-argument rate index error) error)) 0)))
                   (radius (+ (* (+ 3 (* 2 (lw-complex-exp-cap (cons (lw-real-dirichlet-damping-argument rate index error) 0)))) error) error)) (cap (* (lw-real-dirichlet-damping-gain rate limit) error))))
           :in-theory (union-theories '(lw-dirichlet-sample lw-complex-log-ramp-independent-exp lw-complex-laplace-point
              lw-complex-scale lw-real-dirichlet-damping-argument lw-real-dirichlet-damping-gain) (theory 'lw-rdd-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
