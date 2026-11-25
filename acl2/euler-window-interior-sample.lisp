(in-package "ACL2")

(include-book "euler-circle-positive-count-witness")

; Translate the physical interior disk into a strictly smaller
; normalized disk for the positive-count test.

(local (defthm lw-ewis-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewis-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewis-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewis-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewis-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewis-times-negative)))))

(local (defthm lw-ewis-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewis-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewis-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewis-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewis-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewis-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewis-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewis-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewis-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewis-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewis-left-commutes)))))

(local (deftheory lw-ewis-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ewis-left-commutes lw-ewis-left-distributes lw-ewis-fold-constants
              lw-ewis-times-negative lw-ewis-negative-times lw-ewis-zero-times
              lw-ewis-minus-one lw-ewis-double-negative lw-ewis-add-cancel lw-ewis-double lw-ewis-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-interior-scale (radius inner-radius)
  (* 1/2 (+ radius inner-radius)))

(defun lw-euler-window-interior-sample-request (height radius inner-radius)
  (let* ((middle (lw-euler-window-interior-scale radius inner-radius))
         (outer (lw-euler-circle-outer-radius (cons 252 height) radius))
         (scale (* middle (/ outer)))
         (inner (* inner-radius (/ middle))))
    (* 1/8 (lw-euler-circle-inner-distance-floor 252 height outer scale inner (lw-euler-zeta-clearance-request 252 height)))))

(defthm lw-euler-window-interior-sample-request-positive
  (and (rationalp (lw-euler-window-interior-sample-request height radius inner-radius)) (< 0 (lw-euler-window-interior-sample-request height radius inner-radius)))
  :hints (("Goal"
           :use ((:instance lw-euler-circle-inner-distance-floor-data (rate 252)
                  (radius (lw-euler-circle-outer-radius (cons 252 height) radius)) (scale (* (lw-euler-window-interior-scale radius inner-radius) (/ (lw-euler-circle-outer-radius (cons 252 height) radius)))) (inner (* inner-radius (/ (lw-euler-window-interior-scale radius inner-radius)))) (anchor-error (lw-euler-zeta-clearance-request 252 height))))
           :in-theory (union-theories '(lw-euler-window-interior-sample-request) (theory 'lw-ewis-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ewis-strict-product
   (implies (and (rationalp a) (rationalp b) (< a b) (rationalp factor) (< 0 factor))
            (< (* a factor) (* b factor)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-ewis-ratio-data
   (implies (and (rationalp a) (<= 0 a) (rationalp b) (< a b))
            (and (rationalp (/ b)) (< 0 (/ b))
                 (rationalp (* a (/ b))) (<= 0 (* a (/ b))) (< (* a (/ b)) 1)))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value b))
                  (:instance lw-ewis-strict-product (factor (/ b)))
                  (:instance lw-ewis-multiply-order (a 0) (b a) (factor (/ b)))
                  (:instance inverse-of-* (x b)))
            :in-theory (theory 'lw-ewis-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ewis-two-inverse-factors
   (implies (and (rationalp a) (not (equal a 0))
                 (rationalp b) (not (equal b 0)) (rationalp value))
            (equal (* a (/ a) b (/ b) value) value))
   :hints (("Goal"
            :use ((:instance lw-ewis-inverse-factor (divisor a) (coefficient (* b (/ b) value)))
                  (:instance lw-ewis-inverse-factor (divisor b) (coefficient value)))
            :in-theory (theory 'lw-ewis-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ewis-cutoff-data
   (implies (and (rationalp middle) (< 0 middle) (rationalp radius) (< middle radius)
                 (rationalp outer) (< radius outer))
            (let* ((scale (* middle (/ outer)))
                   (boundary (* radius (/ outer)))
                   (cut (* 1/2 (+ (* scale scale) (* boundary boundary)))))
              (and (rationalp scale) (< 0 scale)
                   (rationalp cut) (< (* scale scale) cut) (< cut 1)
                   (< (* outer outer cut) (* radius radius)))))
   :hints (("Goal"
            :use ((:instance lw-ewis-ratio-data (a middle) (b outer))
                  (:instance lw-ewis-ratio-data (a radius) (b outer))
                  (:instance lw-ewis-positive-product (a middle) (b (/ outer)))
                  (:instance lw-ewis-positive-product (a outer) (b outer))
                  (:instance lw-ewis-strict-product (a middle) (b radius) (factor (/ outer)))
                  (:instance lw-ewis-strict-product (a (* middle (/ outer))) (b (* radius (/ outer))) (factor (* middle (/ outer))))
                  (:instance lw-ewis-strict-product (a (* middle (/ outer))) (b (* radius (/ outer))) (factor (* radius (/ outer))))
                  (:instance lw-ewis-strict-product (a (* radius (/ outer))) (b 1) (factor (* radius (/ outer))))
                  (:instance lw-ewis-strict-product
                   (a (* 1/2 (+ (* middle (/ outer) middle (/ outer)) (* radius (/ outer) radius (/ outer)))))
                   (b (* radius (/ outer) radius (/ outer))) (factor (* outer outer)))
                  (:instance lw-ewis-two-inverse-factors (a outer) (b outer) (value (* radius radius))))
            :in-theory (theory 'lw-ewis-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ewis-normalized-offset
   (implies (and (rationalp outer) (< 0 outer) (rationalp middle) (< 0 middle)
                 (lw-complex-diskp offset inner-radius))
            (let ((normalized (lw-complex-scale (/ middle) offset)))
              (and (lw-complex-diskp normalized (* inner-radius (/ middle)))
                   (equal (lw-complex-scale outer (lw-complex-scale (* middle (/ outer)) normalized)) offset))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (point offset) (radius inner-radius))
                  (:instance lw-complex-scale-disk (point offset) (radius inner-radius) (factor (/ middle)))
                  (:instance lw-reciprocal-positive (value middle))
                  (:instance lw-ewis-two-inverse-factors (a outer) (b middle) (value (car offset)))
                  (:instance lw-ewis-two-inverse-factors (a outer) (b middle) (value (cdr offset))))
            :in-theory (union-theories '(lw-complexp lw-complex-scale abs cons-car-cdr)
                                        (theory 'lw-ewis-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-window-positive-count-from-interior-sample
  (implies
   (and (rationalp height) (rationalp radius) (< radius 252)
        (lw-euler-circle-coverp (cons 252 height) radius plus-arcs minus-arcs)
        (rationalp inner-radius) (<= 0 inner-radius) (< inner-radius radius)
        (lw-complex-diskp offset inner-radius)
        (rationalp error) (< 0 error) (<= error (lw-euler-window-interior-sample-request height radius inner-radius))
        (lw-complex-diskp
         (lw-complex-euler-continuation-value (+ 252 (car offset)) (+ height (cdr offset)) error)
         (lw-euler-window-interior-sample-request height radius inner-radius)))
   (< 0 (lw-euler-circle-interior-count (cons 252 height) radius plus-arcs minus-arcs)))
  :hints (("Goal"
           :use (lw-euler-window-interior-sample-request-positive
                 (:instance lw-ewis-cutoff-data (outer (lw-euler-circle-outer-radius (cons 252 height) radius)) (middle (lw-euler-window-interior-scale radius inner-radius)))
                 (:instance lw-ewis-ratio-data (a inner-radius) (b (lw-euler-window-interior-scale radius inner-radius)))
                 (:instance lw-ewis-normalized-offset (outer (lw-euler-circle-outer-radius (cons 252 height) radius)) (middle (lw-euler-window-interior-scale radius inner-radius)))
                 (:instance lw-euler-zeta-clearance-check (rate 252))
                 (:instance lw-euler-circle-inner-distance-floor-data (rate 252)
                   (radius (lw-euler-circle-outer-radius (cons 252 height) radius)) (scale (* (lw-euler-window-interior-scale radius inner-radius) (/ (lw-euler-circle-outer-radius (cons 252 height) radius)))) (inner (* inner-radius (/ (lw-euler-window-interior-scale radius inner-radius)))) (anchor-error (lw-euler-zeta-clearance-request 252 height)))
                 (:instance lw-complex-disk-data (point offset) (radius inner-radius))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-euler-continuation-value (+ 252 (car offset)) (+ height (cdr offset)) error))
                   (radius (lw-euler-window-interior-sample-request height radius inner-radius))
                   (cap (* 1/2 (lw-euler-circle-inner-distance-floor 252 height (lw-euler-circle-outer-radius (cons 252 height) radius) (* (lw-euler-window-interior-scale radius inner-radius) (/ (lw-euler-circle-outer-radius (cons 252 height) radius))) (* inner-radius (/ (lw-euler-window-interior-scale radius inner-radius))) (lw-euler-zeta-clearance-request 252 height)))))
                 (:instance lw-euler-circle-positive-count-from-small-value
                   (rate 252) (anchor-error (lw-euler-zeta-clearance-request 252 height)) (scale (* (lw-euler-window-interior-scale radius inner-radius) (/ (lw-euler-circle-outer-radius (cons 252 height) radius)))) (inner (* inner-radius (/ (lw-euler-window-interior-scale radius inner-radius)))) (cutoff-square (* 1/2 (+ (* (* (lw-euler-window-interior-scale radius inner-radius) (/ (lw-euler-circle-outer-radius (cons 252 height) radius))) (* (lw-euler-window-interior-scale radius inner-radius) (/ (lw-euler-circle-outer-radius (cons 252 height) radius)))) (* (* radius (/ (lw-euler-circle-outer-radius (cons 252 height) radius))) (* radius (/ (lw-euler-circle-outer-radius (cons 252 height) radius)))))))
                   (point (lw-complex-scale (/ (lw-euler-window-interior-scale radius inner-radius)) offset)) (value-error error)))
           :in-theory (union-theories '(lw-euler-window-interior-sample-request
                  lw-euler-window-interior-scale lw-euler-circle-outer-radius lw-complexp)
                (theory 'lw-ewis-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
