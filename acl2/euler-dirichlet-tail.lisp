(in-package "ACL2")

(include-book "euler-dirichlet-telescoping")
(include-book "hyperbola-majorants")

; Tail bounds for actual Euler prefixes at dyadic endpoints.
; All finite rounding costs are retained and computed explicitly.

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

(local (in-theory (disable lw-complex-euler-dirichlet-prefix
 lw-complex-euler-dirichlet-prefix-step lw-complex-euler-dirichlet-prefix-telescope
 lw-complex-euler-cell-segment lw-complex-euler-cell-segment-telescope
 lw-complex-euler-cell-segment-difference lw-complex-euler-dirichlet-block
 lw-complex-euler-dirichlet-block-difference lw-complex-euler-dirichlet-block-bound
 lw-complex-euler-dirichlet-prefix-block-bound lw-euler-dirichlet-block-rounding
 lw-euler-dirichlet-cell-cap lw-euler-dirichlet-cell-rounding
 lw-euler-cell-segment-rounding lw-rational-power
 lw-rational-power-monotone-exponent lw-reciprocal-square-tail)))

(local (defthm lw-edtail-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-edtail-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-edtail-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-edtail-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-edtail-times-negative (a b) (b a)))
                 :in-theory (disable lw-edtail-times-negative)))))

(local (defthm lw-edtail-zero-times (equal (* 0 a) 0)))

(local (defthm lw-edtail-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-edtail-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-edtail-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-edtail-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edtail-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-edtail-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-edtail-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edtail-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-edtail-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-edtail-left-commutes)))))

(local (defthm lw-edtail-power-two-natural
 (natp (lw-rational-power 2 block))
 :hints (("Goal" :in-theory (enable lw-rational-power)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-edtail-power-two-four
 (implies (and (natp block) (<= 2 block))
  (<= 4 (lw-rational-power 2 block)))
 :hints (("Goal" :use ((:instance lw-rational-power-monotone-exponent
                       (base 2) (small 2) (large block)))))
 :rule-classes nil))

(defthm lw-complex-euler-dirichlet-block-rational
 (implies (and (rationalp rate) (rationalp height) (natp block) (<= 2 block)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-dirichlet-block rate height block error)))
 :hints (("Goal"
  :use (lw-edtail-power-two-four lw-edtail-power-two-natural
        (:instance lw-complex-euler-cell-segment-rational
         (start (lw-rational-power 2 block)) (count (lw-rational-power 2 block))))
  :in-theory (union-theories '(lw-complex-euler-dirichlet-block natp posp fix)
                             (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-euler-dirichlet-block-rounding-nonnegative
 (implies (and (rationalp rate) (< 0 rate) (rationalp height) (natp block) (<= 2 block))
  (and (rationalp (lw-euler-dirichlet-block-rounding rate height block))
       (<= 0 (lw-euler-dirichlet-block-rounding rate height block))))
 :hints (("Goal"
  :use (lw-edtail-power-two-four lw-edtail-power-two-natural
        (:instance lw-euler-cell-segment-rounding-nonnegative
         (start (lw-rational-power 2 block)) (count (lw-rational-power 2 block))))
  :in-theory (union-theories '(lw-euler-dirichlet-block-rounding natp posp fix)
                             (theory 'minimal-theory))
  :do-not-induct t)))

(defun lw-complex-euler-dyadic-prefix (rate height count error)
 (lw-complex-euler-dirichlet-prefix rate height (- (lw-rational-power 2 count) 1) error))

(defun lw-complex-euler-dyadic-tail (rate height count start error)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (<= count start)) (cons 0 0)
  (lw-complex-add (lw-complex-euler-dirichlet-block rate height (- count 1) error)
   (lw-complex-euler-dyadic-tail rate height (- count 1) start error))))

(defun lw-euler-dyadic-tail-rounding (rate height count start)
 (declare (xargs :measure (nfix count)))
 (if (or (zp count) (<= count start)) 0
  (+ (lw-euler-dirichlet-block-rounding rate height (- count 1))
     (lw-euler-dyadic-tail-rounding rate height (- count 1) start))))

(local (in-theory (disable lw-complex-euler-dyadic-prefix lw-complex-euler-dyadic-tail
 lw-euler-dyadic-tail-rounding)))

(defthm lw-complex-euler-dyadic-prefix-rational
 (implies (and (rationalp rate) (rationalp height) (natp count) (<= 2 count)
               (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-dyadic-prefix rate height count error)))
 :hints (("Goal"
  :use ((:instance lw-edtail-power-two-four (block count))
        (:instance lw-edtail-power-two-natural (block count))
        (:instance lw-complex-euler-dirichlet-prefix-rational
         (count (- (lw-rational-power 2 count) 1))))
  :in-theory (union-theories '(lw-complex-euler-dyadic-prefix natp posp fix)
                             (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-dyadic-tail-rational
 (implies (and (rationalp rate) (rationalp height) (natp count)
               (natp start) (<= 2 start) (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-euler-dyadic-tail rate height count start error)))
 :hints (("Goal" :induct (lw-complex-euler-dyadic-tail rate height count start error)
                 :in-theory (e/d (lw-complex-euler-dyadic-tail lw-complexp lw-complex-add)
                                   (lw-complex-euler-dirichlet-block-rational)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-complex-euler-dirichlet-block-rational (block (- count 1))))
            :do-not-induct t))))

(defthm lw-euler-dyadic-tail-rounding-nonnegative
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (natp count) (natp start) (<= 2 start))
  (and (rationalp (lw-euler-dyadic-tail-rounding rate height count start))
       (<= 0 (lw-euler-dyadic-tail-rounding rate height count start))))
 :hints (("Goal" :induct (lw-euler-dyadic-tail-rounding rate height count start)
                 :in-theory (e/d (lw-euler-dyadic-tail-rounding)
                                   (lw-euler-dirichlet-block-rounding-nonnegative)))
         (and stable-under-simplificationp
          '(:use ((:instance lw-euler-dirichlet-block-rounding-nonnegative (block (- count 1))))
            :do-not-induct t))))

(local (defthm lw-edtail-add-zero
 (implies (lw-complexp point) (equal (lw-complex-add point (cons 0 0)) point))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(local (defthm lw-edtail-reassociate
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
  (equal (lw-complex-add (lw-complex-add a b) c)
         (lw-complex-add a (lw-complex-add c b))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(local (defthm lw-edtail-difference
 (implies (and (lw-complexp point) (lw-complexp rest))
  (equal (lw-complex-sub (lw-complex-add point rest) point) rest))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(local (defthm lw-edtail-add-difference
 (implies (and (lw-complexp point) (lw-complexp rest))
  (equal (lw-complex-add rest (lw-complex-sub point rest)) point))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(local (defthm lw-edtail-prefix-step
 (implies (and (rationalp rate) (rationalp height) (natp count) (< 2 count)
               (rationalp error) (< 0 error))
  (equal (lw-complex-euler-dyadic-prefix rate height count error)
   (lw-complex-add (lw-complex-euler-dyadic-prefix rate height (- count 1) error)
    (lw-complex-euler-dirichlet-block rate height (- count 1) error))))
 :hints (("Goal"
  :use ((:instance lw-complex-euler-dirichlet-block-difference (block (- count 1)))
        (:instance lw-complex-euler-dyadic-prefix-rational (count (- count 1)))
        lw-complex-euler-dyadic-prefix-rational)
  :in-theory (e/d (lw-complex-euler-dyadic-prefix)
   (lw-complex-euler-dyadic-prefix-rational))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-edtail-tail-empty
 (implies (<= count start)
  (equal (lw-complex-euler-dyadic-tail rate height count start error) (cons 0 0)))
 :hints (("Goal" :expand ((lw-complex-euler-dyadic-tail rate height count start error))))))

(local (defthm lw-edtail-rounding-empty
 (implies (<= count start)
  (equal (lw-euler-dyadic-tail-rounding rate height count start) 0))
 :hints (("Goal" :expand ((lw-euler-dyadic-tail-rounding rate height count start))))))

(local (defthm lw-edtail-square-empty
 (implies (<= count start)
  (equal (lw-reciprocal-square-tail count start) 0))
 :hints (("Goal" :expand ((lw-reciprocal-square-tail count start))))))

(defthm lw-complex-euler-dyadic-tail-telescope
 (implies (and (rationalp rate) (rationalp height)
               (natp count) (natp start) (<= 2 start) (<= start count)
               (rationalp error) (< 0 error))
  (equal (lw-complex-euler-dyadic-prefix rate height count error)
   (lw-complex-add (lw-complex-euler-dyadic-prefix rate height start error)
    (lw-complex-euler-dyadic-tail rate height count start error))))
 :hints (("Goal" :induct (lw-complex-euler-dyadic-tail rate height count start error)
                 :in-theory (enable (:induction lw-complex-euler-dyadic-tail)))
         (and stable-under-simplificationp
          '(:expand ((lw-complex-euler-dyadic-tail rate height count start error)
                     (lw-complex-euler-dyadic-tail rate height start start error))
            :use (lw-edtail-prefix-step) :do-not-induct t))))

(local (in-theory (disable lw-complex-euler-dyadic-tail-telescope)))

(defthm lw-complex-euler-dyadic-tail-difference
 (implies (and (rationalp rate) (rationalp height)
               (natp count) (natp start) (<= 2 start) (<= start count)
               (rationalp error) (< 0 error))
  (equal
   (lw-complex-sub (lw-complex-euler-dyadic-prefix rate height count error)
                   (lw-complex-euler-dyadic-prefix rate height start error))
   (lw-complex-euler-dyadic-tail rate height count start error)))
 :hints (("Goal" :use (lw-complex-euler-dyadic-tail-telescope) :do-not-induct t)))

(local (in-theory (disable lw-complex-euler-dyadic-tail-difference)))

(local (defthm lw-edtail-zero-disk (lw-complex-diskp (cons 0 0) 0)
 :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(defthm lw-complex-euler-dyadic-tail-square-bound
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (natp count) (natp start) (<= 2 start)
               (<= (+ rate (abs height)) (lw-rational-power 2 start))
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp (lw-complex-euler-dyadic-tail rate height count start error)
   (+ (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate)
            (lw-reciprocal-square-tail (- count 1) (- start 1)))
      (* (lw-euler-dyadic-tail-rounding rate height count start) error))))
 :hints (("Goal" :induct (lw-complex-euler-dyadic-tail rate height count start error)
                 :in-theory
                  (union-theories
                   '((:induction lw-complex-euler-dyadic-tail)
                     lw-edtail-tail-empty lw-edtail-rounding-empty lw-edtail-square-empty
                     lw-edtail-zero-disk lw-edtail-left-commutes lw-edtail-left-distributes
                     lw-edtail-fold-constants lw-edtail-zero-times lw-edtail-times-negative
                     lw-edtail-negative-times lw-edtail-minus-one lw-edtail-double-negative
                     lw-edtail-add-cancel lw-edtail-double lw-edtail-add-double
                     natp posp zp fix commutativity-of-+ commutativity-2-of-+
                     associativity-of-+ commutativity-of-* associativity-of-*
                     distributivity unicity-of-0 unicity-of-1)
                   (theory 'minimal-theory)))
         (and stable-under-simplificationp
          '(:expand ((lw-complex-euler-dyadic-tail rate height count start error)
                     (lw-euler-dyadic-tail-rounding rate height count start)
                     (lw-reciprocal-square-tail (- count 1) (- start 1))
                     (lw-complex-euler-dyadic-tail rate height start start error)
                     (lw-euler-dyadic-tail-rounding rate height start start)
                     (lw-reciprocal-square-tail (- start 1) (- start 1)))
            :use ((:instance lw-rational-power-monotone-exponent
                   (base 2) (small start) (large (- count 1)))
                  (:instance lw-complex-euler-dirichlet-block-bound (block (- count 1)))
                  (:instance lw-complex-add-disk
                   (left (lw-complex-euler-dirichlet-block rate height (- count 1) error))
                   (right (lw-complex-euler-dyadic-tail rate height (- count 1) start error))
                   (radius
                    (+ (* 32 (lw-euler-dirichlet-cell-cap rate height)
                             (/ rate) (/ rate) (/ (- count 1)) (/ (- count 1)))
                       (* (lw-euler-dirichlet-block-rounding rate height (- count 1)) error)))
                   (other-radius
                    (+ (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate)
                             (lw-reciprocal-square-tail (- count 2) (- start 1)))
                       (* (lw-euler-dyadic-tail-rounding rate height (- count 1) start) error)))))
            :nonlinearp nil :do-not-induct t))))

(local (in-theory (disable lw-complex-euler-dyadic-tail-square-bound)))

(defthm lw-complex-euler-dyadic-prefix-tail-bound
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (natp count) (natp start) (<= 2 start) (<= start count)
               (<= (+ rate (abs height)) (lw-rational-power 2 start))
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-dyadic-prefix rate height count error)
                   (lw-complex-euler-dyadic-prefix rate height start error))
   (+ (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate) (/ (- start 1)))
      (* (lw-euler-dyadic-tail-rounding rate height count start) error))))
 :hints (("Goal"
  :use (lw-complex-euler-dyadic-tail-square-bound lw-complex-euler-dyadic-tail-difference
        lw-euler-dirichlet-cell-cap-valid lw-euler-dyadic-tail-rounding-nonnegative
        (:instance lw-reciprocal-square-tail-data (count (- count 1)) (start (- start 1)))
        (:instance lw-reciprocal-square-tail-bound (count (- count 1)) (start (- start 1)))
        (:instance lw-edtail-multiply-order
         (a (lw-reciprocal-square-tail (- count 1) (- start 1))) (b (/ (- start 1)))
         (factor (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-euler-dyadic-tail rate height count start error))
         (radius (+ (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate)
                       (lw-reciprocal-square-tail (- count 1) (- start 1)))
                    (* (lw-euler-dyadic-tail-rounding rate height count start) error)))
         (cap (+ (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate) (/ (- start 1)))
                 (* (lw-euler-dyadic-tail-rounding rate height count start) error)))))
  :in-theory (union-theories
   '(natp posp fix lw-edtail-left-commutes lw-edtail-fold-constants
     commutativity-of-* associativity-of-* commutativity-of-+ commutativity-2-of-+
     associativity-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


