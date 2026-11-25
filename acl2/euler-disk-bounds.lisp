(in-package "ACL2")

(include-book "euler-fixed-truncation")

; Uniform Euler truncation over a closed disk in the positive half-plane.
; A synthetic envelope point has the smallest real part and largest size.

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

(local (in-theory (disable lw-complex-euler-dirichlet-prefix
 lw-complex-euler-dirichlet-prefix-step lw-complex-euler-dirichlet-prefix-telescope
 lw-complex-euler-dyadic-prefix lw-complex-euler-continuation-value
 lw-euler-continuation-tail-cap lw-euler-continuation-block-cutoff
 lw-euler-dyadic-transport-cost lw-euler-prefix-transport-cost
 lw-euler-dirichlet-cell-cap lw-euler-rounding-precision
 lw-complex-euler-cell-segment-telescope lw-complex-euler-cell-segment-difference
 lw-complex-euler-dyadic-tail-telescope lw-complex-euler-dyadic-tail-difference)))

(local (defthm lw-udb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-udb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-udb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-udb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-udb-times-negative (a b) (b a)))
                 :in-theory (disable lw-udb-times-negative)))))

(local (defthm lw-udb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-udb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-udb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-udb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-udb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-udb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-udb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-udb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-udb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-udb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-udb-left-commutes)))))


(local (defthm lw-udb-abs-nonnegative
 (implies (and (rationalp value) (<= 0 value)) (equal (abs value) value))
 :hints (("Goal" :in-theory (enable abs)))))

(defthm lw-euler-disk-envelope-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate))
  (and (< 0 (- rate radius)) (rationalp (+ (abs height) (* 3 radius))) (<= 0 (+ (abs height) (* 3 radius)))
       (rationalp (abs height)) (<= 0 (abs height))
       (rationalp (abs (+ (abs height) (* 3 radius))))
       (equal (+ (- rate radius) (abs (+ (abs height) (* 3 radius))))
              (+ rate (abs height) (* 2 radius)))))
 :hints (("Goal" :in-theory (union-theories
   '(abs lw-udb-abs-nonnegative lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     (:executable-counterpart abs) natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory)) :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-disk-point-data
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp offset radius))
  (and (rationalp (car offset)) (rationalp (cdr offset))
       (rationalp (+ rate (car offset))) (< 0 (+ rate (car offset)))
       (rationalp (+ height (cdr offset)))
       (rationalp (abs (+ height (cdr offset)))) (<= 0 (abs (+ height (cdr offset))))
       (<= (- rate radius) (+ rate (car offset)))
       (<= (+ (+ rate (car offset)) (abs (+ height (cdr offset))))
           (+ (- rate radius) (abs (+ (abs height) (* 3 radius)))))))
 :hints (("Goal"
  :use (lw-euler-disk-envelope-data
        (:instance lw-complex-disk-data (point offset))
        (:instance lw-complex-disk-coordinates (point offset)))
  :in-theory (union-theories
   '(lw-complexp abs lw-udb-abs-nonnegative lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     (:executable-counterpart abs) natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(local (defthm lw-udb-cell-cap-monotone
 (implies (and (rationalp size) (<= 0 size) (rationalp cap) (<= size cap))
  (and (<= 0 (+ cap (* 2 cap cap)))
       (<= (+ size (* 2 size size)) (+ cap (* 2 cap cap)))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-udb-tail-majorant
 (implies (and (rationalp rate) (< 0 rate) (rationalp floor) (< 0 floor) (<= floor rate)
               (rationalp size) (<= 0 size) (rationalp cap) (<= size cap))
  (<= (* 32 (+ size (* 2 size size)) (/ rate) (/ rate))
      (* 32 (+ cap (* 2 cap cap)) (/ floor) (/ floor))))
 :hints (("Goal"
  :use (lw-udb-cell-cap-monotone
        (:instance lw-reciprocal-antitone (left floor) (right rate))
        (:instance lw-reciprocal-positive (value rate))
        (:instance lw-reciprocal-positive (value floor))
        (:instance lw-udb-multiply-order
         (a (+ size (* 2 size size))) (b (+ cap (* 2 cap cap))) (factor (* 32 (/ rate) (/ rate))))
        (:instance lw-udb-multiply-order
         (a (/ rate)) (b (/ floor)) (factor (* 32 (+ cap (* 2 cap cap)) (/ rate))))
        (:instance lw-udb-multiply-order
         (a (/ rate)) (b (/ floor)) (factor (* 32 (+ cap (* 2 cap cap)) (/ floor)))))
  :in-theory (union-theories
   '( lw-udb-abs-nonnegative lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     (:executable-counterpart abs) natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)) :rule-classes nil))

(local (defthm lw-udb-transport-size
 (implies (and (rationalp rate) (rationalp height) (natp count))
  (equal (lw-euler-prefix-transport-cost rate height count)
         (lw-euler-prefix-transport-cost (+ rate (abs height)) 0 count)))
 :hints (("Goal" :in-theory (union-theories
   '(lw-euler-prefix-transport-cost lw-udb-abs-nonnegative lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     (:executable-counterpart abs) natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
                 :do-not-induct t)) :rule-classes nil))

(local (defthm lw-udb-transport-monotone
 (implies (and (rationalp size) (<= 0 size) (rationalp cap) (<= size cap) (natp count))
  (<= (lw-euler-prefix-transport-cost size 0 count)
      (lw-euler-prefix-transport-cost cap 0 count)))
 :hints (("Goal"
  :use ((:instance lw-udb-multiply-order
         (a (+ size 1)) (b (+ cap 1)) (factor (* count (+ (* 2 size) 32))))
        (:instance lw-udb-multiply-order
         (a (+ (* 2 size) 32)) (b (+ (* 2 cap) 32)) (factor (* (+ cap 1) count)))
        (:instance lw-udb-multiply-order
         (a (+ (* 2 size) 32)) (b (+ (* 2 cap) 32)) (factor (+ count 1))))
  :in-theory (union-theories
   '(lw-euler-prefix-transport-cost lw-udb-abs-nonnegative lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     (:executable-counterpart abs) natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp t :do-not-induct t)) :rule-classes nil))

(local (defthm lw-udb-power-two-natural
 (natp (lw-rational-power 2 block))
 :hints (("Goal" :in-theory (enable lw-rational-power)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-udb-power-two-large
 (implies (and (natp block) (<= 2 block)) (<= 3 (lw-rational-power 2 block)))
 :hints (("Goal" :use ((:instance lw-rational-power-bernoulli (base 2) (exponent block)))
                 :in-theory (union-theories
   '( lw-udb-abs-nonnegative lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))))
 :rule-classes nil))

(defun lw-euler-disk-tail-cap (rate height radius)
 (lw-euler-continuation-tail-cap (- rate radius) (+ (abs height) (* 3 radius))))

(defun lw-euler-disk-transport-cost (rate height radius block)
 (lw-euler-dyadic-transport-cost (- rate radius) (+ (abs height) (* 3 radius)) block))

(defun lw-euler-disk-block-cutoff (rate height radius error)
 (lw-euler-continuation-block-cutoff (- rate radius) (+ (abs height) (* 3 radius)) error))

(local (in-theory (disable lw-euler-disk-tail-cap lw-euler-disk-transport-cost lw-euler-disk-block-cutoff)))

(defthm lw-euler-disk-tail-cap-bound
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp offset radius))
  (<= (lw-euler-continuation-tail-cap (+ rate (car offset)) (+ height (cdr offset)))
      (lw-euler-disk-tail-cap rate height radius)))
 :hints (("Goal"
  :use (lw-euler-disk-envelope-data lw-euler-disk-point-data
        (:instance lw-udb-tail-majorant
         (rate (+ rate (car offset))) (floor (- rate radius))
         (size (+ (+ rate (car offset)) (abs (+ height (cdr offset)))))
         (cap (+ (- rate radius) (abs (+ (abs height) (* 3 radius)))))))
  :in-theory (union-theories
   '(lw-euler-disk-tail-cap lw-euler-continuation-tail-cap lw-euler-dirichlet-cell-cap lw-udb-abs-nonnegative lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     (:executable-counterpart abs) natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-disk-transport-cost-bound
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp offset radius) (natp block) (<= 2 block))
  (<= (lw-euler-dyadic-transport-cost (+ rate (car offset)) (+ height (cdr offset)) block)
      (lw-euler-disk-transport-cost rate height radius block)))
 :hints (("Goal"
  :use (lw-euler-disk-envelope-data lw-euler-disk-point-data
        lw-udb-power-two-natural lw-udb-power-two-large
        (:instance lw-udb-transport-size (rate (+ rate (car offset))) (height (+ height (cdr offset)))
         (count (- (lw-rational-power 2 block) 1)))
        (:instance lw-udb-transport-size (rate (- rate radius)) (height (+ (abs height) (* 3 radius)))
         (count (- (lw-rational-power 2 block) 1)))
        (:instance lw-udb-transport-monotone
         (size (+ (+ rate (car offset)) (abs (+ height (cdr offset)))))
         (cap (+ (- rate radius) (abs (+ (abs height) (* 3 radius)))))
         (count (- (lw-rational-power 2 block) 1))))
  :in-theory (union-theories
   '(lw-euler-disk-transport-cost lw-euler-dyadic-transport-cost lw-udb-abs-nonnegative lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     (:executable-counterpart abs) natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-disk-constructors-valid
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (natp block) (<= 2 block) (rationalp error) (< 0 error))
  (and (rationalp (lw-euler-disk-tail-cap rate height radius)) (< 0 (lw-euler-disk-tail-cap rate height radius))
       (rationalp (lw-euler-disk-transport-cost rate height radius block))
       (< 0 (lw-euler-disk-transport-cost rate height radius block))
       (natp (lw-euler-disk-block-cutoff rate height radius error))
       (<= 2 (lw-euler-disk-block-cutoff rate height radius error))))
 :hints (("Goal"
  :use (lw-euler-disk-envelope-data
        (:instance lw-euler-continuation-tail-cap-valid (rate (- rate radius)) (height (+ (abs height) (* 3 radius))))
        (:instance lw-euler-dyadic-transport-cost-valid (rate (- rate radius)) (height (+ (abs height) (* 3 radius))) (count block))
        (:instance lw-euler-continuation-block-cutoff-natural (rate (- rate radius)) (height (+ (abs height) (* 3 radius)))))
  :in-theory (union-theories
   '(lw-euler-disk-tail-cap lw-euler-disk-transport-cost lw-euler-disk-block-cutoff lw-udb-abs-nonnegative lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     (:executable-counterpart abs) natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-euler-disk-truncation-budget
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp offset radius) (rationalp target-error) (< 0 target-error)
               (natp block) (<= (lw-euler-disk-block-cutoff rate height radius target-error) block)
               (rationalp request) (< 0 request)
               (<= request (lw-euler-rounding-precision
                (lw-euler-disk-transport-cost rate height radius block) target-error)))
  (and (<= 2 block)
       (<= (+ (+ rate (car offset)) (abs (+ height (cdr offset)))) (lw-rational-power 2 block))
       (<= (* (lw-euler-continuation-tail-cap (+ rate (car offset)) (+ height (cdr offset)))
              (/ (- block 1))) (/ target-error 2))
       (<= (* (lw-euler-dyadic-transport-cost (+ rate (car offset)) (+ height (cdr offset)) block) request)
           (/ target-error 2))))
 :hints (("Goal"
  :use (lw-euler-disk-envelope-data lw-euler-disk-point-data
        (:instance lw-euler-disk-constructors-valid (error target-error))
        lw-euler-disk-tail-cap-bound lw-euler-disk-transport-cost-bound
        (:instance lw-euler-continuation-tail-cutoff-sufficient
         (rate (- rate radius)) (height (+ (abs height) (* 3 radius))) (error target-error) (start block))
        (:instance lw-euler-continuation-tail-cap-valid
         (rate (+ rate (car offset))) (height (+ height (cdr offset))))
        (:instance lw-euler-dyadic-transport-cost-valid
         (rate (+ rate (car offset))) (height (+ height (cdr offset))) (count block))
        (:instance lw-euler-rounding-precision-valid
         (cost (lw-euler-disk-transport-cost rate height radius block)) (error target-error))
        (:instance lw-udb-multiply-order
         (a (lw-euler-continuation-tail-cap (+ rate (car offset)) (+ height (cdr offset))))
         (b (lw-euler-disk-tail-cap rate height radius)) (factor (/ (- block 1))))
        (:instance lw-udb-multiply-order
         (a (lw-euler-dyadic-transport-cost (+ rate (car offset)) (+ height (cdr offset)) block))
         (b (lw-euler-disk-transport-cost rate height radius block)) (factor request))
        (:instance lw-udb-multiply-order
         (a request)
         (b (lw-euler-rounding-precision (lw-euler-disk-transport-cost rate height radius block) target-error))
         (factor (lw-euler-disk-transport-cost rate height radius block))))
  :in-theory (union-theories
   '(lw-euler-disk-tail-cap lw-euler-disk-transport-cost lw-euler-disk-block-cutoff lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-euler-disk-fixed-truncation
 (implies (and (rationalp rate) (rationalp height) (rationalp radius) (<= 0 radius) (< radius rate)
               (lw-complex-diskp offset radius) (rationalp target-error) (< 0 target-error)
               (rationalp error) (< 0 error)
               (natp block) (<= (lw-euler-disk-block-cutoff rate height radius target-error) block)
               (rationalp request) (< 0 request)
               (<= request (lw-euler-rounding-precision
                (lw-euler-disk-transport-cost rate height radius block) target-error)))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) error)
                   (lw-complex-euler-dyadic-prefix (+ rate (car offset)) (+ height (cdr offset)) block request))
   (+ (* 1/4 error) target-error)))
 :hints (("Goal"
  :use (lw-euler-disk-truncation-budget lw-euler-disk-point-data
        (:instance lw-complex-euler-fixed-truncation
         (rate (+ rate (car offset))) (height (+ height (cdr offset))))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub
          (lw-complex-euler-continuation-value (+ rate (car offset)) (+ height (cdr offset)) error)
          (lw-complex-euler-dyadic-prefix (+ rate (car offset)) (+ height (cdr offset)) block request)))
         (radius (+ (* 1/4 error)
                    (* (lw-euler-continuation-tail-cap (+ rate (car offset)) (+ height (cdr offset))) (/ (- block 1)))
                    (* (lw-euler-dyadic-transport-cost (+ rate (car offset)) (+ height (cdr offset)) block) request)))
         (cap (+ (* 1/4 error) target-error))))
  :in-theory (union-theories
   '( lw-udb-left-commutes lw-udb-left-distributes lw-udb-fold-constants lw-udb-times-negative lw-udb-negative-times lw-udb-zero-times lw-udb-minus-one lw-udb-double-negative lw-udb-add-cancel lw-udb-double lw-udb-add-double
     natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
     commutativity-of-+ commutativity-2-of-+ associativity-of-+
     distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :nonlinearp nil :do-not-induct t)))


