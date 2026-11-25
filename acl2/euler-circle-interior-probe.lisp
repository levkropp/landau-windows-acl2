(in-package "ACL2")

(include-book "circle-interior-factor-point")
(include-book "euler-circle-count-requests")

; A positive checked count gives an interior rational offset at any requested accuracy.

(local (defthm lw-ecip-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecip-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecip-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecip-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecip-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecip-times-negative)))))

(local (defthm lw-ecip-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecip-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecip-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecip-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecip-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecip-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecip-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecip-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecip-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecip-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecip-left-commutes)))))

(local (deftheory lw-ecip-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ecip-left-commutes lw-ecip-left-distributes lw-ecip-fold-constants
              lw-ecip-times-negative lw-ecip-negative-times lw-ecip-zero-times
              lw-ecip-minus-one lw-ecip-double-negative lw-ecip-add-cancel lw-ecip-double lw-ecip-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-circle-interior-probe-request (center radius tolerance)
  (/ (* 1/4 tolerance) (+ 1 (lw-euler-circle-outer-gap center radius))))

(defun lw-euler-circle-interior-probe-offset (center radius plus-arcs minus-arcs tolerance)
  (let ((error (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))))
    (car (lw-circle-pole-roots (lw-euler-circle-factor-roots center radius 0 error error) radius))))

(local
 (defthm lw-ecip-raw-budget
   (implies (and (rationalp tolerance) (< 0 tolerance) (rationalp cost) (< 0 cost))
            (let ((request (/ (* 1/4 tolerance) (+ 1 cost))))
              (and (rationalp request) (< 0 request)
                   (<= request (* 1/4 tolerance)) (<= (* cost request) (* 1/4 tolerance)))))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value (+ 1 cost)))
                  (:instance lw-ecip-positive-product (a (* 1/4 tolerance)) (b (/ (+ 1 cost))))
                  (:instance lw-ecip-positive-product (a cost) (b tolerance))
                  (:instance lw-positive-division-bound
                    (numerator (* 1/4 tolerance)) (divisor (+ 1 cost)) (bound (* 1/4 tolerance)))
                  (:instance lw-positive-division-bound
                    (numerator (* cost 1/4 tolerance)) (divisor (+ 1 cost)) (bound (* 1/4 tolerance))))
            :in-theory (theory 'lw-ecip-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecip-fit-request
   (implies (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
       (rationalp tolerance) (< 0 tolerance))
            (and (rationalp (lw-euler-circle-interior-probe-request center radius tolerance)) (< 0 (lw-euler-circle-interior-probe-request center radius tolerance))
                 (rationalp (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))) (< 0 (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))) (<= (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)) (* 1/4 tolerance))
                 (rationalp (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (< 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (<= (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))) (* 1/4 tolerance))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data
                  (:instance lw-ecip-raw-budget (cost (lw-euler-circle-outer-gap center radius)))
                  (:instance lw-euler-circle-count-request-adequate (target 0) (request (lw-euler-circle-interior-probe-request center radius tolerance)))
                  (:instance lw-ecip-multiply-order (a (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))) (b (lw-euler-circle-interior-probe-request center radius tolerance)) (factor (lw-euler-circle-outer-gap center radius)))
                  (:instance lw-ecip-positive-product (a (lw-euler-circle-outer-gap center radius)) (b (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))))
            :in-theory (union-theories '(lw-euler-circle-interior-probe-request lw-euler-circle-count-modelp) (theory 'lw-ecip-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecip-first-factor-offset
   (implies
    (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
       (rationalp tolerance) (< 0 tolerance) (< 0 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs)))
    (and (lw-complex-diskp (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance) radius)
         (equal (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (lw-euler-circle-outer-radius center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))) (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance) 0) (cons 0 0))))
   :hints (("Goal"
            :use (lw-euler-circle-outer-data lw-ecip-fit-request
                  (:instance lw-euler-circle-request-count-exact (target 0) (request (lw-euler-circle-interior-probe-request center radius tolerance)))
                  (:instance lw-euler-uniform-polynomial-valid
                    (rate (car center)) (height (cdr center)) (radius (lw-euler-circle-outer-radius center radius)) (target 0) (error (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))))
                  (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))))) (outer-radius (lw-euler-circle-outer-radius center radius)) (epsilon (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))))
                  (:instance lw-circle-first-interior-factor-disk (roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (lw-euler-circle-outer-radius center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))))
                  (:instance lw-circle-first-interior-factor-zero
                    (roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (lw-euler-circle-outer-radius center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))))))))
            :in-theory (union-theories '(lw-euler-circle-interior-probe-offset lw-euler-circle-factor-roots lw-euler-circle-global-polynomial
               lw-polynomial-disk-factor-polynomial len endp) (theory 'lw-ecip-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-interior-probe-small-value
  (implies
   (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
       (rationalp tolerance) (< 0 tolerance) (< 0 (lw-euler-circle-interior-count center radius plus-arcs minus-arcs))
        (rationalp value-error) (< 0 value-error) (<= value-error tolerance))
   (and (lw-complex-diskp (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance) radius) (lw-complex-diskp (lw-complex-euler-continuation-value (+ (car center) (car (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) (+ (cdr center) (cdr (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) value-error) tolerance)))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data lw-ecip-fit-request lw-ecip-first-factor-offset
                 (:instance lw-complex-disk-enlarge (point (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance)) (cap (lw-euler-circle-outer-radius center radius)))
                 (:instance lw-complex-disk-data (point (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance)))
                 (:instance lw-euler-disk-point-data (rate (car center)) (height (cdr center)) (radius (lw-euler-circle-outer-radius center radius)) (offset (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance)))
                 (:instance lw-euler-uniform-polynomial-valid
                   (rate (car center)) (height (cdr center)) (radius (lw-euler-circle-outer-radius center radius)) (target 0) (error (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))))
                 (:instance lw-polynomial-disk-factor-value-error
                   (coefficients (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))))) (outer-radius (lw-euler-circle-outer-radius center radius)) (epsilon (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))) (point (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance)))
                 (:instance lw-complex-euler-uniform-polynomial-comparison
                   (rate (car center)) (height (cdr center)) (radius (lw-euler-circle-outer-radius center radius)) (target 0) (error (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (point (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance)))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))))) (point (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance)) (offset 0))
                 (:instance lw-complex-euler-continuation-value-rational
                   (rate (+ (car center) (car (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance)))) (height (+ (cdr center) (cdr (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance)))) (error value-error))
                 (:instance lw-complex-sub-zero (point (lw-complex-polynomial (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance) 0)))
                 (:instance lw-complex-sub-zero (point (lw-complex-euler-continuation-value (+ (car center) (car (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) (+ (cdr center) (cdr (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) value-error)))
                 (:instance lw-complex-difference-symmetric
                   (left (lw-complex-polynomial (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance) 0)) (right (lw-complex-euler-continuation-value (+ (car center) (car (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) (+ (cdr center) (cdr (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) value-error)) (radius (+ (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))) (* 1/4 value-error))))
                 (:instance lw-complex-difference-triangle (left (lw-complex-euler-continuation-value (+ (car center) (car (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) (+ (cdr center) (cdr (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) value-error)) (middle (lw-complex-polynomial (lw-euler-uniform-polynomial (car center) (cdr center) (lw-euler-circle-outer-radius center radius) 0 (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance) 0)) (right (cons 0 0))
                   (radius (+ (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))) (* 1/4 value-error))) (other-radius (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-euler-continuation-value (+ (car center) (car (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) (+ (cdr center) (cdr (lw-euler-circle-interior-probe-offset center radius plus-arcs minus-arcs tolerance))) value-error)) (radius (+ (+ (* (lw-euler-circle-outer-gap center radius) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance))) (* 1/4 value-error)) (lw-euler-circle-count-request center radius plus-arcs minus-arcs (lw-euler-circle-interior-probe-request center radius tolerance)))) (cap tolerance)))
           :in-theory (theory 'lw-ecip-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
