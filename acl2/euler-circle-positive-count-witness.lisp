(in-package "ACL2")

(include-book "euler-physical-factor-model")
(include-book "euler-circle-count-requests")

; The approximating factors used by the checked cover have its fixed count.

(local (defthm lw-ecpw-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecpw-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecpw-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecpw-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecpw-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecpw-times-negative)))))

(local (defthm lw-ecpw-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecpw-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecpw-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecpw-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecpw-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecpw-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecpw-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecpw-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecpw-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecpw-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecpw-left-commutes)))))

(local (deftheory lw-ecpw-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ecpw-left-commutes lw-ecpw-left-distributes lw-ecpw-fold-constants
              lw-ecpw-times-negative lw-ecpw-negative-times lw-ecpw-zero-times
              lw-ecpw-minus-one lw-ecpw-double-negative lw-ecpw-add-cancel lw-ecpw-double lw-ecpw-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-circle-interior-value-request (rate height radius scale inner anchor-error)
  (/ (min 1 (min (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-circle-inner-distance-floor rate height (lw-euler-circle-outer-radius (cons rate height) radius) scale inner anchor-error))))
     (+ 1 (lw-euler-circle-outer-gap (cons rate height) radius))))

(local
 (defthm lw-ecpw-share-budget
   (implies (and (rationalp budget) (< 0 budget) (rationalp cost) (< 0 cost))
            (and (rationalp (/ budget (+ 1 cost)))
                 (< 0 (/ budget (+ 1 cost)))
                 (<= (/ budget (+ 1 cost)) budget)
                 (<= (* cost (/ budget (+ 1 cost))) budget)))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value (+ 1 cost)))
                  (:instance lw-ecpw-positive-product (a budget) (b (/ (+ 1 cost))))
                  (:instance lw-ecpw-positive-product (a cost) (b budget))
                  (:instance lw-positive-division-bound (numerator budget) (divisor (+ 1 cost)) (bound budget))
                  (:instance lw-positive-division-bound (numerator (* cost budget)) (divisor (+ 1 cost)) (bound budget)))
            :in-theory (theory 'lw-ecpw-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecpw-positive-request
   (implies (and (lw-euler-circle-coverp (cons rate height) radius plus-arcs minus-arcs)
       (lw-euler-value-clearance-check rate height anchor-error))
            (and (rationalp (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)) (< 0 (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))
                 (<= (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error) 1) (<= (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error) (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))) (<= (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error) (* 1/8 (lw-euler-circle-inner-distance-floor rate height (lw-euler-circle-outer-radius (cons rate height) radius) scale inner anchor-error)))
                 (<= (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)) 1)
                 (<= (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)) (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
                 (<= (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)) (* 1/8 (lw-euler-circle-inner-distance-floor rate height (lw-euler-circle-outer-radius (cons rate height) radius) scale inner anchor-error)))))
   :hints (("Goal"
            :use (lw-euler-value-clearance-data
                  (:instance lw-euler-circle-outer-data (center (cons rate height)))
                  (:instance lw-euler-circle-inner-distance-floor-data (radius (lw-euler-circle-outer-radius (cons rate height) radius)))
                  (:instance lw-ecpw-share-budget
                    (budget (min 1 (min (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-circle-inner-distance-floor rate height (lw-euler-circle-outer-radius (cons rate height) radius) scale inner anchor-error))))) (cost (lw-euler-circle-outer-gap (cons rate height) radius))))
            :in-theory (union-theories '(lw-euler-circle-interior-value-request min) (theory 'lw-ecpw-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecpw-request-data
   (implies (and (lw-euler-circle-coverp (cons rate height) radius plus-arcs minus-arcs)
       (lw-euler-value-clearance-check rate height anchor-error))
            (and (rationalp (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))) (< 0 (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))) (<= (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)) 1)
        (<= (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)) (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))) (<= (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)) (* 1/8 (lw-euler-circle-inner-distance-floor rate height (lw-euler-circle-outer-radius (cons rate height) radius) scale inner anchor-error)))
        (rationalp (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)))) (< 0 (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)))) (<= (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))) 1)
        (<= (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))) (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))) (<= (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))) (* 1/8 (lw-euler-circle-inner-distance-floor rate height (lw-euler-circle-outer-radius (cons rate height) radius) scale inner anchor-error)))))
   :hints (("Goal"
            :use (lw-ecpw-positive-request
                  (:instance lw-euler-circle-outer-data (center (cons rate height)))
                  (:instance lw-euler-circle-count-request-adequate (center (cons rate height)) (target 0) (request (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)))
                  (:instance lw-ecpw-multiply-order (a (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))) (b (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)) (factor (lw-euler-circle-outer-gap (cons rate height) radius)))
                  (:instance lw-ecpw-positive-product (a (lw-euler-circle-outer-gap (cons rate height) radius)) (b (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)))))
            :in-theory (union-theories '(lw-euler-circle-count-modelp) (theory 'lw-ecpw-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecpw-count-identity
   (implies (and (lw-euler-circle-coverp (cons rate height) radius plus-arcs minus-arcs)
       (lw-euler-value-clearance-check rate height anchor-error))
            (equal (len (lw-circle-pole-roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height (lw-euler-circle-outer-radius (cons rate height) radius) 0 (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)))) (lw-euler-circle-outer-radius (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))) radius)) (lw-euler-circle-interior-count (cons rate height) radius plus-arcs minus-arcs)))
   :hints (("Goal"
            :use (lw-ecpw-positive-request
                  (:instance lw-euler-circle-request-count-exact (center (cons rate height)) (target 0) (request (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))))
            :in-theory (union-theories '(lw-euler-circle-factor-roots lw-euler-circle-global-polynomial) (theory 'lw-ecpw-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecpw-empty-length
   (iff (equal (len items) 0) (endp items))
   :hints (("Goal" :in-theory (union-theories '(len endp (:type-prescription len)) (theory 'lw-ecpw-arithmetic))))))

(defthm lw-euler-circle-positive-count-from-small-value
  (implies
   (and (lw-euler-circle-coverp (cons rate height) radius plus-arcs minus-arcs)
       (lw-euler-value-clearance-check rate height anchor-error) (rationalp scale) (< 0 scale) (rationalp cutoff-square)
       (< (* scale scale) cutoff-square) (< cutoff-square 1)
       (< (* (lw-euler-circle-outer-radius (cons rate height) radius) (lw-euler-circle-outer-radius (cons rate height) radius) cutoff-square) (* radius radius))
       (lw-complex-diskp point inner) (< inner 1)
        (rationalp value-error) (< 0 value-error) (<= value-error (* 1/8 (lw-euler-circle-inner-distance-floor rate height (lw-euler-circle-outer-radius (cons rate height) radius) scale inner anchor-error)))
        (lw-complex-diskp (lw-complex-euler-continuation-value (+ rate (car (lw-complex-scale (lw-euler-circle-outer-radius (cons rate height) radius) (lw-complex-scale scale point)))) (+ height (cdr (lw-complex-scale (lw-euler-circle-outer-radius (cons rate height) radius) (lw-complex-scale scale point)))) value-error) (* 1/2 (lw-euler-circle-inner-distance-floor rate height (lw-euler-circle-outer-radius (cons rate height) radius) scale inner anchor-error))))
   (< 0 (lw-euler-circle-interior-count (cons rate height) radius plus-arcs minus-arcs)))
  :hints (("Goal"
           :use (lw-ecpw-request-data lw-ecpw-count-identity
                 (:instance lw-euler-circle-outer-data (center (cons rate height)))
                 (:instance lw-euler-physical-factor-model-data
                   (radius (lw-euler-circle-outer-radius (cons rate height) radius)) (target 0) (error (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)))) (factor-error (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))))
                 (:instance lw-euler-physical-factor-small-value-positive-count
                   (radius (lw-euler-circle-outer-radius (cons rate height) radius)) (target 0) (error (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)))) (factor-error (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error))))
                 (:instance lw-circle-normalized-inner-count-empty (roots (lw-polynomial-normalized-factor-roots (lw-euler-uniform-polynomial rate height (lw-euler-circle-outer-radius (cons rate height) radius) 0 (* (lw-euler-circle-outer-gap (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)))) (lw-euler-circle-outer-radius (cons rate height) radius) (lw-euler-circle-count-request (cons rate height) radius plus-arcs minus-arcs (lw-euler-circle-interior-value-request rate height radius scale inner anchor-error)))) (scale (lw-euler-circle-outer-radius (cons rate height) radius))))
           :in-theory (union-theories '(lw-ecpw-empty-length (:type-prescription len)) (theory 'lw-ecpw-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
