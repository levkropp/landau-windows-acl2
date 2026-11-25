(in-package "ACL2")

(include-book "euler-circle-bounded-radius")
(include-book "circle-factor-uniform-clearance")

; Compute the contour floor before choosing a polynomial or factor request.

(local (defthm lw-ecub-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecub-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecub-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecub-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecub-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecub-times-negative)))))

(local (defthm lw-ecub-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecub-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecub-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecub-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecub-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecub-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecub-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecub-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecub-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-euler-circle-uniform-distance
    (rate height outer-radius lower upper scale cutoff-square)
  (lw-circle-square-floor-to-distance (lw-circle-factor-uniform-clearance-square lower upper cutoff-square scale (* (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))) (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height)))) (+ 1 (lw-euler-uniform-coefficient-cap rate height outer-radius)) (lw-euler-circle-jensen-count-budget rate height outer-radius cutoff-square))))

(defun lw-euler-circle-uniform-approximation-limit
    (rate height outer-radius lower upper scale cutoff-square)
  (min 1 (min (* 1/64 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))) (* 1/16 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)))))

(defthm lw-euler-circle-jensen-count-budget-natural
   (natp (lw-euler-circle-jensen-count-budget rate height outer-radius cutoff-square))
   :hints (("Goal"
            :use ((:instance lw-resolvent-truncation-count-natural
                    (radius cutoff-square)
                    (error (/ (* (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))) (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height)))) (* 2 (+ 1 (+ 1 (lw-euler-uniform-coefficient-cap rate height outer-radius))) (+ 1 (+ 1 (lw-euler-uniform-coefficient-cap rate height outer-radius))))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-jensen-count-budget lw-circle-inner-factor-count-limit
              lw-ecub-left-commutes lw-ecub-left-distributes lw-ecub-fold-constants
              lw-ecub-times-negative lw-ecub-negative-times lw-ecub-zero-times
              lw-ecub-minus-one lw-ecub-double-negative lw-ecub-add-cancel lw-ecub-double lw-ecub-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil)

(defthm lw-euler-circle-uniform-clearance-budget-data
  (implies (and (rationalp rate) (< 3 rate) (rationalp height)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                (rationalp scale) (< upper scale)
                (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1))
           (and (rationalp (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)) (< 0 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)) (<= (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square) 1)
                (<= (* (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square) (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)) (lw-circle-factor-uniform-clearance-square lower upper cutoff-square scale (* (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))) (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height)))) (+ 1 (lw-euler-uniform-coefficient-cap rate height outer-radius)) (lw-euler-circle-jensen-count-budget rate height outer-radius cutoff-square)))
                (rationalp (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square)) (< 0 (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square)) (<= (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square) 1)
                (<= (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square) (* 1/64 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))))
                (<= (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square) (* 1/16 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)))))
  :hints (("Goal"
           :use (lw-euler-zeta-clearance-check
                 (:instance lw-euler-value-clearance-data (anchor-error (lw-euler-zeta-clearance-request rate height)))
                 lw-euler-circle-jensen-count-budget-natural
                 (:instance lw-ecub-multiply-order (a upper) (b scale) (factor upper))
                 (:instance lw-ecub-multiply-order (a upper) (b scale) (factor scale))
                 (:instance lw-circle-factor-uniform-clearance-square-positive
                   (center-lower (* (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))) (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))))) (cap (+ 1 (lw-euler-uniform-coefficient-cap rate height outer-radius))) (budget (lw-euler-circle-jensen-count-budget rate height outer-radius cutoff-square)))
                 (:instance lw-circle-square-floor-to-distance-valid (square (lw-circle-factor-uniform-clearance-square lower upper cutoff-square scale (* (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))) (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height)))) (+ 1 (lw-euler-uniform-coefficient-cap rate height outer-radius)) (lw-euler-circle-jensen-count-budget rate height outer-radius cutoff-square)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-uniform-distance lw-euler-circle-uniform-approximation-limit min
              lw-ecub-left-commutes lw-ecub-left-distributes lw-ecub-fold-constants
              lw-ecub-times-negative lw-ecub-negative-times lw-ecub-zero-times
              lw-ecub-minus-one lw-ecub-double-negative lw-ecub-add-cancel lw-ecub-double lw-ecub-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
