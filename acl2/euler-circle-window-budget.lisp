(in-package "ACL2")

(include-book "euler-circle-window-cluster")
(include-book "euler-circle-mellin-precision")
(include-book "circle-pole-tail-budget")
(include-book "euler-window-quadratic-tail-budget")

(defun lw-circle-pole-block-floor (inner count start)
  (* (lw-circle-interior-pole-count-cap count (+ 2 start))
     (/ (lw-rational-power (max 1 inner) (+ 2 start count)))))

(local (defthm lw-ecwb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecwb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecwb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecwb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecwb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecwb-times-negative)))))

(local (defthm lw-ecwb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecwb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecwb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecwb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecwb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecwb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecwb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecwb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecwb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecwb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecwb-left-commutes)))))

; A single precision uses this lower bound for every selectable order.
(defthm lw-circle-pole-block-floor-data
  (implies (and (rationalp inner) (< 0 inner) (posp count) (natp start)
                (natp index) (<= start index) (< index (+ start count)))
           (and (rationalp (lw-circle-pole-block-floor inner count start)) (< 0 (lw-circle-pole-block-floor inner count start))
                (<= (lw-circle-pole-block-floor inner count start) (* (lw-circle-interior-pole-count-cap count (+ 2 start)) (/ (lw-rational-power inner (+ 3 index)))))))
  :hints (("Goal"
           :use ((:instance lw-rational-power-positive
                   (base inner) (exponent (+ 3 index)))
                 (:instance lw-rational-power-at-least-one (base (max 1 inner)) (exponent (+ 2 start count)))
                 (:instance lw-rational-power-monotone-base
                   (left inner) (right (max 1 inner)) (exponent (+ 3 index)))
                 (:instance lw-rational-power-monotone-exponent
                   (base (max 1 inner)) (small (+ 3 index)) (large (+ 2 start count)))
                 (:instance lw-reciprocal-antitone (left (lw-rational-power inner (+ 3 index))) (right (lw-rational-power (max 1 inner) (+ 2 start count))))
                 (:instance lw-power-domination-factor-valid (index (+ (+ 2 start) count)))
                 (:instance lw-ecwb-positive-product (a (lw-circle-interior-pole-count-cap count (+ 2 start))) (b (/ (lw-rational-power (max 1 inner) (+ 2 start count)))))
                 (:instance lw-ecwb-multiply-order (a (/ (lw-rational-power (max 1 inner) (+ 2 start count)))) (b (/ (lw-rational-power inner (+ 3 index)))) (factor (lw-circle-interior-pole-count-cap count (+ 2 start)))))
           :in-theory
           (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-pole-block-floor lw-circle-interior-pole-count-cap max
              lw-rational-power-rational lw-reciprocal-positive
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defun lw-euler-circle-window-minimum-index
    (center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass)
  (let ((inner (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)))
        (count (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
        (distance (- 252 (/ numerator denominator))))
    (max (lw-circle-pole-tail-minimum-order inner radius count (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) 1/8)
         (max (lw-circle-pole-tail-minimum-order inner distance count
                (* (+ (* 8 ceiling) 10) (/ distance) (lw-euler-window-weighted-tail (cdr center) distance)) 1/8)
              (lw-circle-pole-tail-minimum-order inner real-radius count (* real-mass (lw-euler-window-weighted-tail (cdr center) real-radius)) 1/8)))))

(defun lw-euler-circle-computed-window-threshold
    (center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass)
  (lw-kernel-window-block-threshold (lw-euler-circle-window-minimum-index center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass) (+ 1 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))))

(defun lw-euler-circle-window-budget-tolerance
    (center radius plus-arcs minus-arcs start)
  (/ (* 1/8 (lw-circle-pole-block-floor (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) (lw-window-index start))) (+ 1 (* 3 (lw-euler-window-weighted-tail (cdr center) 1)))))

(defun lw-euler-circle-window-budget-request
    (center radius plus-arcs minus-arcs anchor-error start)
  (lw-euler-circle-mellin-precision center radius anchor-error (lw-window-index start) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) (lw-euler-circle-window-budget-tolerance center radius plus-arcs minus-arcs start)))

(local
 (defthm lw-ecwb-window-index-natural
   (natp (lw-window-index start))
   :hints (("Goal"
            :use ((:instance lw-window-index-natural (lower (car (lw-log-bounds start 1/1000)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-window-index
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-ecwb-minimum-index-natural
   (natp (lw-euler-circle-window-minimum-index center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-window-minimum-index lw-circle-pole-tail-minimum-order
              lw-polynomial-decay-index lw-resolvent-truncation-count-natural max
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-ecwb-tolerance-budget
   (implies (and (rationalp floor) (< 0 floor)
                 (rationalp gain) (<= 0 gain))
            (let ((tolerance (/ (* 1/8 floor) (+ 1 gain))))
              (and (rationalp tolerance) (< 0 tolerance)
                   (<= tolerance (* 1/8 floor))
                   (<= (* gain tolerance) (* 1/8 floor)))))
   :hints (("Goal"
            :use ((:instance lw-ecwb-multiply-order (a 1) (b (+ 1 gain))
                    (factor (/ (* 1/8 floor) (+ 1 gain))))
                  (:instance lw-ecwb-multiply-order (a gain) (b (+ 1 gain))
                    (factor (/ (* 1/8 floor) (+ 1 gain))))
                  (:instance lw-ecwb-inverse-factor (divisor (+ 1 gain)) (coefficient (* 1/8 floor))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-reciprocal-positive
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp t :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecwb-precision-allocation
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (car center) 252)
                (rationalp start)
                (posp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                 (natp index) (<= (lw-window-index start) index) (< index (+ (lw-window-index start) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))))
            (let* ((request (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))
                   (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error request)))
              (and (rationalp request) (< 0 request)
                   (rationalp error) (< 0 error)
                   (rationalp (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index)) (< 0 (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index))
                   (<= (lw-euler-circle-mellin-coefficient-error center radius anchor-error error error index error error error error) (* 1/8 (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index)))
                   (<= (* 3 (lw-euler-window-weighted-tail (cdr center) 1) error) (* 1/8 (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index))))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data
                  (:instance lw-euler-circle-joint-root-data (target 0) (request 1))
                  (:instance lw-euler-window-weighted-tail-data (height (cdr center)) (radius 1))
                  (:instance lw-circle-pole-block-floor-data (inner (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (count (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)) (start (lw-window-index start)))
                  (:instance lw-ecwb-tolerance-budget (floor (lw-circle-pole-block-floor (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) (lw-window-index start))) (gain (* 3 (lw-euler-window-weighted-tail (cdr center) 1))))
                  (:instance lw-euler-circle-mellin-block-precision-adequate
                    (start (lw-window-index start)) (count (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)) (tolerance (lw-euler-circle-window-budget-tolerance center radius plus-arcs minus-arcs start)))
                  (:instance lw-ecwb-multiply-order
                    (a (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))) (b (lw-euler-circle-window-budget-tolerance center radius plus-arcs minus-arcs start)) (factor (* 3 (lw-euler-window-weighted-tail (cdr center) 1))))
                  (:instance lw-ecwb-multiply-order
                    (a (lw-circle-pole-block-floor (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) (lw-window-index start))) (b (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index)) (factor 1/8))
                  (:instance lw-power-domination-factor-valid (count (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)) (index (+ 2 (lw-window-index start) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))))
                  (:instance lw-rational-power-positive (base (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (exponent (+ 3 index)))
                  (:instance lw-ecwb-positive-product
                    (a (* 1/8 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
                    (b (/ (lw-power-domination-factor (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) (+ 2 (lw-window-index start) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))))))
                  (:instance lw-ecwb-positive-product
                    (a (lw-circle-interior-pole-count-cap (lw-euler-circle-interior-count center radius plus-arcs minus-arcs) (+ 2 (lw-window-index start))))
                    (b (/ (lw-rational-power (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (+ 3 index))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-window-budget-request lw-euler-circle-window-budget-tolerance
              lw-euler-circle-mellin-precision lw-euler-circle-window-pole-limit lw-circle-interior-pole-count-cap
              lw-ecwb-window-index-natural lw-rational-power-rational lw-reciprocal-positive min
              (:type-prescription lw-euler-circle-mellin-block-gain)
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local (defthm lw-ecwb-right-one (equal (* value 1) (fix value))))

(local
 (defthm lw-ecwb-inverse-unique
   (implies (and (rationalp scale) (rationalp bound) (< 0 scale)
                 (equal (* scale bound) 1))
            (equal bound (/ scale)))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x scale))
                  (:instance associativity-of-* (x (/ scale)) (y scale) (z bound))
                  (:instance commutativity-of-* (x (/ scale)) (y scale)))
            :in-theory (disable inverse-of-* associativity-of-*
                                commutativity-of-* lw-ecwb-left-commutes
                                lw-ecwb-left-distributes distributivity)))
   :rule-classes nil))

(local
 (defthm lw-ecwb-reciprocal-power
   (implies (and (rationalp radius) (< 0 radius) (natp index))
            (equal (lw-rational-power (/ radius) index)
                   (/ (lw-rational-power radius index))))
   :hints (("Goal"
            :use ((:instance lw-rational-power-reciprocal-pair (value radius))
                  (:instance lw-rational-power-positive (base radius) (exponent index))
                  (:instance lw-ecwb-inverse-unique
                    (scale (lw-rational-power radius index))
                    (bound (lw-rational-power (/ radius) index))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power-rational lw-reciprocal-positive
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecwb-tail-allocations
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (car center) 252)
                (rationalp start)
                (posp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                 (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
                 (rationalp real-radius) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) real-radius) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (- 252 (/ numerator denominator)))
                (rationalp real-mass) (<= 0 real-mass)
                 (natp index) (<= (lw-window-index start) index) (< index (+ (lw-window-index start) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
                 (<= (lw-euler-circle-computed-window-threshold center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass) start))
            (and (<= (* (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs) (/ (lw-rational-power radius (+ 2 index)))) (* 1/8 (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index)))
                 (<= (* (* (+ (* 8 ceiling) 10) (/ (- 252 (/ numerator denominator))) (lw-euler-window-weighted-tail (cdr center) (- 252 (/ numerator denominator)))) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 2 index))) (* 1/8 (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index)))
                 (<= (* (* real-mass (lw-euler-window-weighted-tail (cdr center) real-radius)) (lw-rational-power (/ real-radius) (+ 2 index))) (* 1/8 (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index)))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-euler-circle-factor-sum-cap-data
                  (:instance lw-euler-circle-joint-root-data (target 0) (request 1))
                  (:instance lw-positive-division-bound (numerator numerator) (divisor denominator) (bound 1))
                  (:instance lw-euler-window-weighted-tail-data (height (cdr center)) (radius (- 252 (/ numerator denominator))))
                  (:instance lw-euler-window-weighted-tail-data (height (cdr center)) (radius real-radius))
                  (:instance lw-ecwb-positive-product (a (- 252 (/ numerator denominator))) (b (- 252 (/ numerator denominator))))
                  (:instance lw-ecwb-positive-product (a real-radius) (b real-radius))
                  (:instance lw-ecwb-positive-product (a (+ (* 8 ceiling) 10)) (b (/ (- 252 (/ numerator denominator)))))
                  (:instance lw-ecwb-multiply-order (a 0) (b (lw-euler-window-weighted-tail (cdr center) (- 252 (/ numerator denominator)))) (factor (* (+ (* 8 ceiling) 10) (/ (- 252 (/ numerator denominator))))))
                  (:instance lw-ecwb-multiply-order (a 0) (b (lw-euler-window-weighted-tail (cdr center) real-radius)) (factor real-mass))
                  (:instance lw-kernel-window-index-block-data (minimum-index (lw-euler-circle-window-minimum-index center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass))
                    (width (+ 1 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))) (index (lw-window-index start)))
                  (:instance lw-ecwb-reciprocal-power (index (+ 2 index)))
                  (:instance lw-circle-pole-tail-computed-budget
                     (inner (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (clearance radius) (count (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                     (mass (lw-euler-circle-factor-sum-cap center radius plus-arcs minus-arcs)) (fraction 1/8) (start (lw-window-index start)) (order (+ 2 index)))
                  (:instance lw-circle-pole-tail-computed-budget
                     (inner (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (clearance (- 252 (/ numerator denominator))) (count (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                     (mass (* (+ (* 8 ceiling) 10) (/ (- 252 (/ numerator denominator))) (lw-euler-window-weighted-tail (cdr center) (- 252 (/ numerator denominator))))) (fraction 1/8) (start (lw-window-index start)) (order (+ 2 index)))
                  (:instance lw-circle-pole-tail-computed-budget
                     (inner (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs))) (clearance real-radius) (count (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                     (mass (* real-mass (lw-euler-window-weighted-tail (cdr center) real-radius))) (fraction 1/8) (start (lw-window-index start)) (order (+ 2 index))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-window-minimum-index lw-euler-circle-computed-window-threshold
              lw-euler-circle-window-pole-limit lw-ecwb-window-index-natural lw-ecwb-minimum-index-natural
              lw-reciprocal-positive max
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defun lw-euler-window-real-coefficient-check (radius mass index error)
  (and
   (<= (- (car (lw-complex-mellin-euler-coefficient-value 252 0 index error)))
       (+ (* mass (lw-rational-power (/ radius) index)) error))
   (<= (- (car (lw-complex-mellin-euler-coefficient-value 252 0 (+ 1 index) error)))
       (+ (* mass (lw-rational-power (/ radius) (+ 1 index))) error))
   (<= (- (car (lw-complex-mellin-euler-coefficient-value 252 0 (+ 2 index) error)))
       (+ (* mass (lw-rational-power (/ radius) (+ 2 index))) error))))

(defthm lw-euler-circle-window-budget-request-data
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (car center) 252)
                (rationalp start)
                (posp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
            (and (rationalp (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)) (< 0 (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
   :hints (("Goal"
            :use ((:instance lw-ecwb-precision-allocation (index (lw-window-index start))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ecwb-window-index-natural
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecwb-budget-check
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (car center) 252)
                (rationalp start)
                (posp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp real-radius) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) real-radius) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (- 252 (/ numerator denominator)))
                (rationalp real-mass) (<= 0 real-mass)
                (<= (lw-euler-circle-computed-window-threshold center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass) start)
                 (natp index) (<= (lw-window-index start) index) (< index (+ (lw-window-index start) (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
                 (lw-euler-window-real-coefficient-check real-radius real-mass index (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
            (<= (lw-euler-circle-window-coefficient-upper center radius plus-arcs minus-arcs anchor-error ceiling numerator denominator index (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))) (lw-euler-circle-window-pole-limit center radius plus-arcs minus-arcs start index)))
   :hints (("Goal"
            :use (lw-ecwb-precision-allocation lw-ecwb-tail-allocations lw-euler-circle-outer-data
                  lw-euler-circle-collar-width-data
                  (:instance lw-euler-window-quadratic-tail-budget-adequate
                    (height (cdr center)) (error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))) (real-error (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-window-real-coefficient-check lw-euler-window-quadratic-tail-budget
              lw-euler-circle-window-coefficient-upper
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

; The only coefficient hypothesis is the real-centered bound on the
; three orders used by the selected cluster coefficient.
(defthm lw-euler-circle-computed-window-witness
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (car center) 252)
                (rationalp start)
                (posp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp real-radius) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) real-radius) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (- 252 (/ numerator denominator)))
                (rationalp real-mass) (<= 0 real-mass)
                (<= (lw-euler-circle-computed-window-threshold center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass) start)
                (lw-euler-window-real-coefficient-check real-radius real-mass (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
           (lw-landau-window-search start ceiling numerator denominator))
  :hints (("Goal"
           :use (lw-euler-circle-window-budget-request-data
                 (:instance lw-euler-circle-window-coefficient-index-data (request (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)))
                 (:instance lw-ecwb-budget-check (index (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
                 (:instance lw-euler-circle-window-cluster-witness
                   (request (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)) (minimum-index (lw-euler-circle-window-minimum-index center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-computed-window-threshold
              lw-ecwb-minimum-index-natural
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-computed-window-certificate
  (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
                (equal (car center) 252)
                (rationalp start)
                (posp (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp real-radius) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) real-radius) (< (- radius (lw-euler-circle-collar-width center radius plus-arcs minus-arcs)) (- 252 (/ numerator denominator)))
                (rationalp real-mass) (<= 0 real-mass)
                (<= (lw-euler-circle-computed-window-threshold center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass) start)
                (lw-euler-window-real-coefficient-check real-radius real-mass (lw-euler-circle-window-coefficient-index center radius plus-arcs minus-arcs anchor-error start (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start)) (lw-euler-circle-joint-request center radius plus-arcs minus-arcs anchor-error (lw-euler-circle-window-budget-request center radius plus-arcs minus-arcs anchor-error start))))
           (let* ((found (lw-landau-window-search start ceiling numerator denominator))
                  (address (lw-landau-window-address start ceiling found)))
             (and found (rationalp address)
                  (<= start address)
                  (<= (* address address) (* start start start))
                  (< 0 (cadr found))
                  (equal (cdr found) (lw-signal-bounds address ceiling numerator denominator 1/4)))))
  :hints (("Goal"
           :use (lw-euler-circle-computed-window-witness
                 lw-landau-window-search-certificate
                 (:instance lw-kernel-window-index-block-data (minimum-index (lw-euler-circle-window-minimum-index center radius plus-arcs minus-arcs ceiling numerator denominator real-radius real-mass))
                   (width (+ 1 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))) (index (lw-window-index start))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-computed-window-threshold
              lw-ecwb-minimum-index-natural lw-ecwb-window-index-natural
              lw-ecwb-left-commutes lw-ecwb-left-distributes lw-ecwb-fold-constants
              lw-ecwb-times-negative lw-ecwb-negative-times lw-ecwb-zero-times
              lw-ecwb-minus-one lw-ecwb-double-negative lw-ecwb-add-cancel lw-ecwb-double lw-ecwb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
