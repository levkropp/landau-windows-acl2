(in-package "ACL2")

(include-book "euler-dirichlet-prefix")

; Sum actual Euler corrections over one dyadic block. Reciprocal cell
; masses total at most one; every numerical error has a computed cost.

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

(local (in-theory
 (disable lw-log-bounds-nonnegative lw-log-bounds-lower-coarse
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (in-theory (disable lw-complex-euler-dirichlet-cell
 lw-euler-dirichlet-cell-cap lw-euler-dirichlet-cell-rounding
 lw-rational-power)))

(local (defthm lw-edb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-edb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-edb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-edb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-edb-times-negative (a b) (b a)))
                 :in-theory (disable lw-edb-times-negative)))))

(local (defthm lw-edb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-edb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-edb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-edb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-edb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-edb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-edb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-edb-left-commutes)))))

(defun lw-euler-cell-segment-mass (start count)
 (declare (xargs :measure (nfix count)))
 (if (zp count) 0
  (+ (/ (+ start count -1)) (lw-euler-cell-segment-mass start (- count 1)))))

(defun lw-euler-cell-segment-rounding (rate height start count)
 (declare (xargs :measure (nfix count)))
 (if (zp count) 0
  (+ (lw-euler-dirichlet-cell-rounding rate height (+ start count -1))
     (lw-euler-cell-segment-rounding rate height start (- count 1)))))

(defun lw-complex-euler-cell-segment (rate height start count error)
 (declare (xargs :measure (nfix count)))
 (if (zp count) (cons 0 0)
  (lw-complex-add
   (lw-complex-euler-dirichlet-cell rate height (+ start count -1) error)
   (lw-complex-euler-cell-segment rate height start (- count 1) error))))

(local (in-theory (disable lw-euler-cell-segment-mass lw-euler-cell-segment-rounding
 lw-complex-euler-cell-segment)))

(defthm lw-euler-cell-segment-mass-nonnegative
 (implies (and (posp start) (natp count))
  (and (rationalp (lw-euler-cell-segment-mass start count))
       (<= 0 (lw-euler-cell-segment-mass start count))))
 :hints (("Goal" :induct (lw-euler-cell-segment-mass start count)
                 :in-theory (enable lw-euler-cell-segment-mass))))

(defthm lw-euler-cell-segment-mass-bound
 (implies (and (posp start) (natp count))
  (<= (lw-euler-cell-segment-mass start count) (* count (/ start))))
 :hints (("Goal" :induct (lw-euler-cell-segment-mass start count)
                 :in-theory (enable lw-euler-cell-segment-mass))
         (and stable-under-simplificationp
          '(:use ((:instance lw-reciprocal-antitone (left start) (right (+ start count -1))))
            :in-theory (disable lw-reciprocal-antitone) :do-not-induct t))))

(defthm lw-euler-cell-segment-rounding-nonnegative
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (posp start) (< 1 start) (natp count))
  (and (rationalp (lw-euler-cell-segment-rounding rate height start count))
       (<= 0 (lw-euler-cell-segment-rounding rate height start count))))
 :hints (("Goal" :induct (lw-euler-cell-segment-rounding rate height start count)
                 :in-theory (e/d (lw-euler-cell-segment-rounding)
                                   (lw-euler-dirichlet-cell-rounding-valid)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-euler-dirichlet-cell-rounding-valid (index (+ start count -1))))
            :do-not-induct t))))

(defthm lw-complex-euler-cell-segment-rational
 (implies (and (rationalp rate) (rationalp height) (posp start) (< 1 start)
               (natp count) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-cell-segment rate height start count error)))
 :hints (("Goal" :induct (lw-complex-euler-cell-segment rate height start count error)
                 :in-theory (enable lw-complex-euler-cell-segment lw-complexp))))

(local (defthm lw-edb-zero-disk (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(defthm lw-complex-euler-cell-segment-dyadic-bound
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (posp start) (< 1 start) (<= (+ rate (abs height)) start) (natp count)
               (rationalp error) (< 0 error) (<= error 1)
               (natp block) (<= 2 block) (<= (lw-rational-power 2 block) start))
  (lw-complex-diskp (lw-complex-euler-cell-segment rate height start count error)
   (+ (* 32 (lw-euler-dirichlet-cell-cap rate height)
            (/ rate) (/ rate) (/ block) (/ block)
            (lw-euler-cell-segment-mass start count))
      (* (lw-euler-cell-segment-rounding rate height start count) error))))
 :hints (("Goal" :induct (lw-complex-euler-cell-segment rate height start count error)
                 :in-theory (e/d ((:induction lw-complex-euler-cell-segment))
                  (lw-complex-euler-dirichlet-cell-dyadic-bound lw-complex-add-disk)))
         (and stable-under-simplificationp
          '(:expand ((lw-complex-euler-cell-segment rate height start count error)
                     (lw-euler-cell-segment-mass start count)
                     (lw-euler-cell-segment-rounding rate height start count)
                     (lw-complex-euler-cell-segment rate height start 0 error)
                     (lw-euler-cell-segment-mass start 0)
                     (lw-euler-cell-segment-rounding rate height start 0))
            :use ((:instance lw-complex-euler-dirichlet-cell-dyadic-bound (index (+ start count -1)))
                  (:instance lw-complex-add-disk
                   (left (lw-complex-euler-dirichlet-cell rate height (+ start count -1) error))
                   (right (lw-complex-euler-cell-segment rate height start (- count 1) error))
                   (radius
                    (+ (* 32 (lw-euler-dirichlet-cell-cap rate height)
                             (/ rate) (/ rate) (/ block) (/ block) (/ (+ start count -1)))
                       (* (lw-euler-dirichlet-cell-rounding rate height (+ start count -1)) error)))
                   (other-radius
                    (+ (* 32 (lw-euler-dirichlet-cell-cap rate height)
                             (/ rate) (/ rate) (/ block) (/ block)
                             (lw-euler-cell-segment-mass start (- count 1)))
                       (* (lw-euler-cell-segment-rounding rate height start (- count 1)) error)))))
            :nonlinearp nil :do-not-induct t))))

(local (defthm lw-edb-power-two-natural
 (natp (lw-rational-power 2 block))
 :hints (("Goal" :in-theory (enable lw-rational-power)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-edb-power-two-four
 (implies (and (natp block) (<= 2 block))
  (<= 4 (lw-rational-power 2 block)))
 :hints (("Goal" :use ((:instance lw-rational-power-monotone-exponent
                       (base 2) (small 2) (large block)))
                 :in-theory (disable lw-rational-power-monotone-exponent)))
 :rule-classes nil))

(defun lw-complex-euler-dirichlet-block (rate height block error)
 (let ((start (lw-rational-power 2 block)))
  (lw-complex-euler-cell-segment rate height start start error)))

(defun lw-euler-dirichlet-block-rounding (rate height block)
 (let ((start (lw-rational-power 2 block)))
  (lw-euler-cell-segment-rounding rate height start start)))

(local (in-theory (disable lw-complex-euler-dirichlet-block lw-euler-dirichlet-block-rounding)))

(defthm lw-complex-euler-dirichlet-block-bound
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (natp block) (<= 2 block)
               (<= (+ rate (abs height)) (lw-rational-power 2 block))
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-euler-dirichlet-block rate height block error)
   (+ (* 32 (lw-euler-dirichlet-cell-cap rate height)
            (/ rate) (/ rate) (/ block) (/ block))
      (* (lw-euler-dirichlet-block-rounding rate height block) error))))
 :hints (("Goal"
  :use (lw-edb-power-two-four lw-edb-power-two-natural lw-euler-dirichlet-cell-cap-valid
        (:instance lw-euler-cell-segment-mass-nonnegative
         (start (lw-rational-power 2 block)) (count (lw-rational-power 2 block)))
        (:instance lw-euler-cell-segment-rounding-nonnegative
         (start (lw-rational-power 2 block)) (count (lw-rational-power 2 block)))
        (:instance lw-euler-cell-segment-mass-bound
         (start (lw-rational-power 2 block)) (count (lw-rational-power 2 block)))
        (:instance lw-edb-inverse-factor (divisor (lw-rational-power 2 block)) (coefficient 1))
        (:instance lw-complex-euler-cell-segment-dyadic-bound
         (start (lw-rational-power 2 block)) (count (lw-rational-power 2 block)))
        (:instance lw-edb-multiply-order
         (a (lw-euler-cell-segment-mass (lw-rational-power 2 block) (lw-rational-power 2 block)))
         (b 1)
         (factor (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate) (/ block) (/ block))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-euler-dirichlet-block rate height block error))
         (radius
          (+ (* 32 (lw-euler-dirichlet-cell-cap rate height)
                   (/ rate) (/ rate) (/ block) (/ block)
                   (lw-euler-cell-segment-mass (lw-rational-power 2 block) (lw-rational-power 2 block)))
             (* (lw-euler-dirichlet-block-rounding rate height block) error)))
         (cap
          (+ (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate) (/ block) (/ block))
             (* (lw-euler-dirichlet-block-rounding rate height block) error)))))
  :in-theory
   (union-theories
    '(lw-complex-euler-dirichlet-block lw-euler-dirichlet-block-rounding
      natp posp fix lw-edb-left-commutes lw-edb-left-distributes
      lw-edb-fold-constants commutativity-of-* associativity-of-*
      commutativity-of-+ associativity-of-+ unicity-of-1 unicity-of-0)
    (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

