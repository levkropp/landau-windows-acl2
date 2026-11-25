(in-package "ACL2")

(include-book "euler-circle-real-normalized-model")
(include-book "complex-cancelled-normalization")
(include-book "normalized-local-polynomial")

(defun lw-euler-circle-real-anchor-numerator-cap (rate radius inner plus-arcs minus-arcs local-radius)
  (* (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0))))) (+ 1 (lw-normalized-local-point-cap (cons rate 0) local-radius)) (+ 1 (lw-euler-circle-reflected-log-cap (cons rate 0) radius plus-arcs minus-arcs inner))))

(local (defthm lw-ercn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ercn-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ercn-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ercn-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ercn-times-negative (a b) (b a)))
                 :in-theory (disable lw-ercn-times-negative)))))

(local (defthm lw-ercn-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ercn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ercn-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ercn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ercn-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ercn-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ercn-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ercn-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ercn-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ercn-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ercn-left-commutes)))))

(local
 (defthm lw-ercn-anchor-disk
   (implies (and (rationalp rate) (<= 1 rate) (rationalp radius)
                 (<= (- rate 1) radius))
            (lw-complex-diskp (cons (- rate 1) 0) radius))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (point (cons (- rate 1) 0)))
                  (:instance lw-ercn-multiply-order (a (- rate 1)) (b radius) (factor radius))
                  (:instance lw-ercn-multiply-order (a (- rate 1)) (b radius) (factor (- rate 1))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-norm-square
              lw-ercn-left-commutes lw-ercn-left-distributes lw-ercn-fold-constants
              lw-ercn-times-negative lw-ercn-negative-times lw-ercn-zero-times
              lw-ercn-minus-one lw-ercn-double-negative lw-ercn-add-cancel lw-ercn-double lw-ercn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ercn-cons-equal
   (equal (equal (cons a b) (cons c d))
          (and (equal a c) (equal b d)))))

(local
 (defthm lw-ercn-real-shifts
   (implies (and (rationalp rate) (< 1 rate) (lw-complexp point))
            (and (lw-complexp (cons rate 0)) (not (equal (cons rate 0) (cons 0 0)))
                 (not (equal (lw-complex-sub (cons rate 0) (cons 1 0)) (cons 0 0)))
                 (equal (lw-complex-add (cons rate 0) (lw-complex-scale -1 point)) (lw-complex-sub (cons rate 0) point))
                 (equal (lw-complex-add (lw-complex-sub (cons rate 0) (cons 1 0)) (lw-complex-scale -1 point)) (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)))
                 (equal (lw-complex-add (cons 1 0) (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0))) (lw-complex-sub (cons rate 0) point))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-scale lw-complex-add lw-complex-sub lw-ercn-cons-equal
              lw-ercn-left-commutes lw-ercn-left-distributes lw-ercn-fold-constants
              lw-ercn-times-negative lw-ercn-negative-times lw-ercn-zero-times
              lw-ercn-minus-one lw-ercn-double-negative lw-ercn-add-cancel lw-ercn-double lw-ercn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-real-normalized-point-data
   (implies (and (rationalp rate) (< 1 rate) (rationalp local-radius) (<= 0 local-radius) (<= local-radius inner)
                (<= local-radius (* 1/4 (lw-complex-l1 (cons rate 0))))
                (<= local-radius (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0)))))
                (lw-complex-diskp point local-radius))
            (and (lw-complexp (lw-complex-sub (cons rate 0) point)) (lw-complexp (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)))
                 (not (equal (lw-complex-sub (cons rate 0) point) (cons 0 0))) (not (equal (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (cons 0 0)))
                 (equal (lw-complex-add (cons 1 0) (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0))) (lw-complex-sub (cons rate 0) point))
                 (equal (lw-complex-add (cons rate 0) (lw-complex-scale -1 point)) (lw-complex-sub (cons rate 0) point))
                 (equal (lw-complex-add (lw-complex-sub (cons rate 0) (cons 1 0)) (lw-complex-scale -1 point)) (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)))
                 (lw-complex-diskp (lw-complex-sub (cons rate 0) point) (lw-normalized-local-point-cap (cons rate 0) local-radius))
                 (lw-complex-diskp (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (+ 1 (lw-normalized-local-point-cap (cons rate 0) local-radius)))
                 (lw-complex-diskp (lw-complex-reciprocal (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0))))))
                 (lw-complex-diskp (lw-complex-reciprocal (lw-complex-mul (lw-complex-sub (cons rate 0) point) (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)))) (* (/ (* 1/4 (lw-complex-l1 (cons rate 0)))) (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0)))))))))
   :hints (("Goal"
            :use (lw-ercn-real-shifts
                  (:instance lw-complex-disk-data (radius local-radius))
                  (:instance lw-complex-scale-disk (factor -1) (radius local-radius))
                  (:instance lw-normalized-local-point-data (anchor (cons rate 0)) (point (lw-complex-scale -1 point)) (radius local-radius))
                  (:instance lw-complex-sub-disk (left (lw-complex-sub (cons rate 0) point)) (radius (lw-normalized-local-point-cap (cons rate 0) local-radius)) (right (cons 1 0)) (other-radius 1)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs (:executable-counterpart lw-complex-diskp)
              lw-ercn-left-commutes lw-ercn-left-distributes lw-ercn-fold-constants
              lw-ercn-times-negative lw-ercn-negative-times lw-ercn-zero-times
              lw-ercn-minus-one lw-ercn-double-negative lw-ercn-add-cancel lw-ercn-double lw-ercn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ercn-numerator-cap
   (implies (and (lw-complexp shifted) (not (equal shifted (cons 0 0)))
                 (lw-complexp numerator)
                 (lw-complex-diskp shifted (+ 1 point-cap))
                 (lw-complex-diskp s point-cap)
                 (lw-complex-diskp (lw-complex-reciprocal shifted) inverse-cap)
                 (lw-complex-diskp value log-cap) (lw-complex-diskp gamma log-cap)
                 (equal (lw-complex-mul shifted numerator)
                        (lw-complex-sub (lw-complex-add shifted (lw-complex-mul s gamma)) value)))
            (lw-complex-diskp numerator (* inverse-cap (+ 1 point-cap) (+ 1 log-cap))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (point s) (radius point-cap))
                  (:instance lw-complex-disk-data (point value) (radius log-cap))
                  (:instance lw-complex-disk-data (point (lw-complex-reciprocal shifted)) (radius inverse-cap))
                  (:instance lw-complex-mul-disk (left s) (right gamma) (radius point-cap) (other-radius log-cap))
                  (:instance lw-complex-add-disk (left shifted) (radius (+ 1 point-cap))
                    (right (lw-complex-mul s gamma)) (other-radius (* point-cap log-cap)))
                  (:instance lw-complex-sub-disk (left (lw-complex-add shifted (lw-complex-mul s gamma)))
                    (radius (+ (+ 1 point-cap) (* point-cap log-cap))) (right value) (other-radius log-cap))
                  (:instance lw-complex-mul-disk (left (lw-complex-reciprocal shifted)) (radius inverse-cap)
                    (right (lw-complex-sub (lw-complex-add shifted (lw-complex-mul s gamma)) value))
                    (other-radius (+ (+ 1 point-cap) (* point-cap log-cap) log-cap)))
                  (:instance lw-complex-reciprocal-cancel-product (a shifted) (b numerator)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ercn-left-commutes lw-ercn-left-distributes lw-ercn-fold-constants
              lw-ercn-times-negative lw-ercn-negative-times lw-ercn-zero-times
              lw-ercn-minus-one lw-ercn-double-negative lw-ercn-add-cancel lw-ercn-double lw-ercn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-real-normalized-model-comparison
  (implies (and (lw-euler-circle-coverp (cons rate 0) radius plus-arcs minus-arcs)
                (lw-euler-value-clearance-check rate 0 anchor-error)
                (equal (lw-euler-circle-interior-count (cons rate 0) radius plus-arcs minus-arcs) 0)
                (rationalp request) (< 0 request)
                (rationalp approximation-error) (< 0 approximation-error)
                (<= approximation-error 1)
                (rationalp rate) (< 1 rate) (rationalp inner)
                (< (- rate 1) inner) (< inner radius) (rationalp local-radius) (<= 0 local-radius) (<= local-radius inner)
                (<= local-radius (* 1/4 (lw-complex-l1 (cons rate 0))))
                (<= local-radius (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0)))))
                (lw-complex-diskp point local-radius))
           (and (lw-complexp (lw-complex-polynomial (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) point 0))
                (lw-complexp (lw-complex-normalized-euler (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) point 0) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) (cons (- rate 1) 0) 0)))
                (lw-complex-diskp (lw-complex-sub (lw-complex-normalized-euler (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0)) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) point 0) (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) (cons (- rate 1) 0) 0)) (lw-complex-polynomial (lw-euler-circle-real-normalized-polynomial rate radius inner plus-arcs minus-arcs anchor-error request approximation-error) point 0))
                             (* (lw-euler-circle-real-anchor-numerator-cap rate radius inner plus-arcs minus-arcs local-radius) approximation-error))))
  :hints (("Goal"
           :use ((:instance lw-euler-circle-outer-data (center (cons rate 0)))
                 (:instance lw-complex-disk-data (radius local-radius))
                 lw-ercn-real-shifts lw-euler-circle-real-normalized-point-data
                 (:instance lw-complex-disk-enlarge (radius local-radius) (cap inner))
                 (:instance lw-complex-disk-enlarge (radius local-radius) (cap radius))
                 (:instance lw-ercn-anchor-disk (radius inner))
                 (:instance lw-euler-circle-reflected-log-comparison (center (cons rate 0)))
                 (:instance lw-euler-circle-reflected-log-bound (center (cons rate 0)))
                 (:instance lw-euler-circle-reflected-log-bound (center (cons rate 0)) (point (cons (- rate 1) 0)))
                 (:instance lw-complex-disk-data (point (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (radius (lw-euler-circle-reflected-log-cap (cons rate 0) radius plus-arcs minus-arcs inner)))
                 (:instance lw-complex-disk-data (point (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) (cons (- rate 1) 0) 0)) (radius (lw-euler-circle-reflected-log-cap (cons rate 0) radius plus-arcs minus-arcs inner)))
                 (:instance lw-polynomial-real-anchor-numerator-identity (coefficients (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error)))
                 (:instance lw-polynomial-wide-linear-inverse-data (radius inner) (target 0) (error approximation-error))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-real-anchor-numerator (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) rate)) (offset 0))
                 (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-wide-linear-inverse rate inner 0 approximation-error)) (offset 0))
                 (:instance lw-complex-reciprocal-rational (point (lw-complex-sub (cons rate 0) point)))
                 (:instance lw-complex-normalized-euler-cancelled
                   (point (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0))) (value (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (anchor (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) (cons (- rate 1) 0) 0)) (numerator (lw-complex-polynomial (lw-polynomial-real-anchor-numerator (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) rate) point 0)))
                 (:instance lw-ercn-numerator-cap
                   (s (lw-complex-sub (cons rate 0) point)) (shifted (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0))) (numerator (lw-complex-polynomial (lw-polynomial-real-anchor-numerator (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) rate) point 0)) (value (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (gamma (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) (cons (- rate 1) 0) 0))
                   (point-cap (lw-normalized-local-point-cap (cons rate 0) local-radius)) (inverse-cap (/ (* 1/4 (lw-complex-l1 (lw-complex-sub (cons rate 0) (cons 1 0)))))) (log-cap (lw-euler-circle-reflected-log-cap (cons rate 0) radius plus-arcs minus-arcs inner)))
                 (:instance lw-complex-normalized-euler-rational (point (lw-complex-sub (lw-complex-sub (cons rate 0) point) (cons 1 0))) (value (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) point 0)) (anchor (lw-complex-polynomial (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) (cons (- rate 1) 0) 0)))
                 (:instance lw-polynomial-product-evaluation (left (lw-polynomial-real-anchor-numerator (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) rate)) (right (lw-polynomial-wide-linear-inverse rate inner 0 approximation-error)))
                 (:instance lw-complex-left-product-error (factor (lw-complex-polynomial (lw-polynomial-real-anchor-numerator (lw-euler-circle-reflected-log-polynomial (cons rate 0) radius plus-arcs minus-arcs anchor-error request approximation-error) rate) point 0)) (a (lw-complex-reciprocal (lw-complex-sub (cons rate 0) point))) (b (lw-complex-polynomial (lw-polynomial-wide-linear-inverse rate inner 0 approximation-error) point 0))
                   (cap (lw-euler-circle-real-anchor-numerator-cap rate radius inner plus-arcs minus-arcs local-radius)) (error approximation-error)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-real-normalized-polynomial lw-euler-circle-real-anchor-numerator-cap lw-complex-ring-rational
              lw-ercn-left-commutes lw-ercn-left-distributes lw-ercn-fold-constants
              lw-ercn-times-negative lw-ercn-negative-times lw-ercn-zero-times
              lw-ercn-minus-one lw-ercn-double-negative lw-ercn-add-cancel lw-ercn-double lw-ercn-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
