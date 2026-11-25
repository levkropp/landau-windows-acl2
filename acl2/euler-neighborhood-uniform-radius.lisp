(in-package "ACL2")

(include-book "euler-local-normalized-model")

; Uniform input bounds give a common radius for regular contour patches.

(local (defthm lw-enur-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-enur-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-enur-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-enur-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-enur-times-negative (a b) (b a)))
                 :in-theory (disable lw-enur-times-negative)))))

(local (defthm lw-enur-zero-times (equal (* 0 a) 0)))

(local (defthm lw-enur-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-enur-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-enur-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-enur-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-enur-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-enur-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-enur-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enur-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-enur-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-enur-left-commutes)))))

(defun lw-euler-uniform-neighborhood-radius (outer-radius floor slope)
  (min (/ outer-radius 2) (lw-euler-rounding-precision slope (/ floor 32))))

(defun lw-euler-uniform-patch-radius (outer-radius floor slope origin-clearance pole-clearance)
  (min (lw-euler-uniform-neighborhood-radius outer-radius floor slope)
       (* 1/4 (min origin-clearance pole-clearance))))

(defthm lw-euler-uniform-patch-radius-positive
  (implies (and (rationalp outer-radius) (< 0 outer-radius)
       (rationalp floor) (< 0 floor) (rationalp slope) (<= 0 slope)
       (rationalp origin-clearance) (< 0 origin-clearance)
       (rationalp pole-clearance) (< 0 pole-clearance))
           (and (rationalp (lw-euler-uniform-patch-radius outer-radius floor slope origin-clearance pole-clearance)) (< 0 (lw-euler-uniform-patch-radius outer-radius floor slope origin-clearance pole-clearance))))
  :hints (("Goal"
           :use ((:instance lw-euler-rounding-precision-valid (cost slope) (error (/ floor 32))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-uniform-patch-radius lw-euler-uniform-neighborhood-radius min
              lw-enur-left-commutes lw-enur-left-distributes lw-enur-fold-constants
              lw-enur-times-negative lw-enur-negative-times lw-enur-zero-times
              lw-enur-minus-one lw-enur-double-negative lw-enur-add-cancel lw-enur-double lw-enur-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-enur-positive-quotient-order
   (implies (and (rationalp low) (<= 0 low) (rationalp high) (<= low high)
                 (rationalp small) (< 0 small) (rationalp large) (<= small large))
            (<= (/ low large) (/ high small)))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value small))
                  (:instance lw-reciprocal-positive (value large))
                  (:instance lw-enur-multiply-order (a low) (b high) (factor (/ large)))
                  (:instance lw-enur-multiply-order (a small) (b large) (factor (* high (/ large))))
                  (:instance lw-enur-multiply-order
                    (a (* small (* high (/ large)))) (b high) (factor (/ small)))
                  (:instance lw-enur-inverse-factor (divisor small) (coefficient (* high (/ large))))
                  (:instance lw-enur-inverse-factor (divisor large) (coefficient high)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-enur-left-commutes lw-enur-left-distributes lw-enur-fold-constants
              lw-enur-times-negative lw-enur-negative-times lw-enur-zero-times
              lw-enur-minus-one lw-enur-double-negative lw-enur-add-cancel lw-enur-double lw-enur-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-uniform-neighborhood-radius-positive
  (implies (and (rationalp outer-radius) (< 0 outer-radius)
       (rationalp floor) (< 0 floor) (rationalp slope) (<= 0 slope))
           (and (rationalp (lw-euler-uniform-neighborhood-radius outer-radius floor slope)) (< 0 (lw-euler-uniform-neighborhood-radius outer-radius floor slope))))
  :hints (("Goal"
           :use ((:instance lw-euler-rounding-precision-valid (cost slope) (error (/ floor 32))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-uniform-neighborhood-radius min
              lw-enur-left-commutes lw-enur-left-distributes lw-enur-fold-constants
              lw-enur-times-negative lw-enur-negative-times lw-enur-zero-times
              lw-enur-minus-one lw-enur-double-negative lw-enur-add-cancel lw-enur-double lw-enur-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-neighborhood-radius-uniform-lower
  (implies
   (and (rationalp outer-radius) (< 0 outer-radius)
       (rationalp floor) (< 0 floor) (rationalp slope) (<= 0 slope) (lw-euler-value-clearance-check rate height anchor-error) (< outer-radius rate)
       (<= floor (lw-euler-value-clearance-size rate height anchor-error))
       (<= (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error) slope))
   (<= (lw-euler-uniform-neighborhood-radius outer-radius floor slope)
       (lw-euler-neighborhood-radius rate height outer-radius anchor-error)))
  :hints (("Goal"
           :use (lw-euler-neighborhood-data
                 (:instance lw-enur-positive-quotient-order
                   (low (/ floor 32))
                   (high (/ (lw-euler-value-clearance-size rate height anchor-error) 32))
                   (small (+ 2 (* 2 (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error))))
                   (large (+ 2 (* 2 slope)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-uniform-neighborhood-radius lw-euler-neighborhood-radius
              lw-euler-rounding-precision min
              lw-enur-left-commutes lw-enur-left-distributes lw-enur-fold-constants
              lw-enur-times-negative lw-enur-negative-times lw-enur-zero-times
              lw-enur-minus-one lw-enur-double-negative lw-enur-add-cancel lw-enur-double lw-enur-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-local-normalized-radius-uniform-lower
  (implies
   (and (rationalp outer-radius) (< 0 outer-radius)
       (rationalp floor) (< 0 floor) (rationalp slope) (<= 0 slope)
       (rationalp origin-clearance) (< 0 origin-clearance)
       (rationalp pole-clearance) (< 0 pole-clearance)
        (lw-euler-value-clearance-check rate height anchor-error)
        (< outer-radius rate)
        (<= floor (lw-euler-value-clearance-size rate height anchor-error))
        (<= (lw-euler-neighborhood-slope-cap rate height outer-radius anchor-error) slope)
        (<= origin-clearance (lw-complex-l1 (cons rate height)))
        (<= pole-clearance (lw-complex-l1 (lw-complex-sub (cons rate height) (cons 1 0)))))
   (<= (lw-euler-uniform-patch-radius outer-radius floor slope origin-clearance pole-clearance)
       (lw-euler-local-normalized-radius rate height outer-radius anchor-error)))
  :hints (("Goal"
           :use (lw-euler-neighborhood-radius-uniform-lower lw-euler-neighborhood-data)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-uniform-patch-radius lw-euler-local-normalized-radius
              lw-euler-normalized-disk-radius lw-complex-l1 lw-complex-sub abs min
              lw-enur-left-commutes lw-enur-left-distributes lw-enur-fold-constants
              lw-enur-times-negative lw-enur-negative-times lw-enur-zero-times
              lw-enur-minus-one lw-enur-double-negative lw-enur-add-cancel lw-enur-double lw-enur-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
