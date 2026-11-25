(in-package "ACL2")

(include-book "circle-factor-clearance")
(include-book "euler-value-clearance")
(include-book "euler-uniform-polynomial")

; A finite polynomial lower bound gives a native Euler anchor whenever
; the uniform model error fits within that bound.

(local (defthm lw-efc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-efc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-efc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-efc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-efc-times-negative (a b) (b a)))
                 :in-theory (disable lw-efc-times-negative)))))

(local (defthm lw-efc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-efc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-efc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-efc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-efc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-efc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-efc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-efc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-efc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-efc-quarter-square
   (implies (and (rationalp lower) (< 0 lower))
            (< (* (* 3/4 lower) (* 3/4 lower)) (* lower lower)))
   :hints (("Goal"
            :use ((:instance lw-efc-positive-product (a lower) (b lower)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-efc-left-commutes lw-efc-left-distributes lw-efc-fold-constants
              lw-efc-times-negative lw-efc-negative-times lw-efc-zero-times
              lw-efc-minus-one lw-efc-double-negative lw-efc-add-cancel lw-efc-double lw-efc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-efc-l1-bound-with-error
   (implies (and (lw-complexp model) (lw-complexp value)
                 (rationalp lower) (< 0 lower)
                 (<= (* lower lower) (lw-complex-norm-square model))
                 (lw-complex-diskp (lw-complex-sub model value) (* 1/4 lower)))
            (<= (* 1/2 lower) (lw-complex-l1 value)))
   :hints (("Goal"
            :use (lw-efc-quarter-square
                  (:instance lw-complex-l1-bound (point value))
                  (:instance lw-complex-disk-enlarge (point value) (radius (lw-complex-l1 value)) (cap (* 1/2 lower)))
                  (:instance lw-complex-difference-triangle (left model) (middle value) (right (cons 0 0))
                    (radius (* 1/4 lower)) (other-radius (* 1/2 lower)))
                  (:instance lw-complex-sub-zero (point value))
                  (:instance lw-complex-sub-zero (point model))
                  (:instance lw-complex-disk-norm-square (point model) (radius (+ (* 1/4 lower) (* 1/2 lower)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-efc-left-commutes lw-efc-left-distributes lw-efc-fold-constants
              lw-efc-times-negative lw-efc-negative-times lw-efc-zero-times
              lw-efc-minus-one lw-efc-double-negative lw-efc-add-cancel lw-efc-double lw-efc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-value-clearance-from-approximation
   (implies (and (rationalp rate) (< 0 rate) (rationalp height)
                 (rationalp error) (< 0 error) (rationalp lower) (< 0 lower)
                 (<= error (* 1/32 lower)) (lw-complexp model)
                 (<= (* lower lower) (lw-complex-norm-square model))
                 (lw-complex-diskp
                  (lw-complex-sub model (lw-complex-euler-continuation-value rate height error))
                  (* 1/4 lower)))
            (and (<= (* 1/2 lower) (lw-euler-value-clearance-size rate height error))
                 (lw-euler-value-clearance-check rate height error)))
   :hints (("Goal"
            :use (lw-complex-euler-continuation-value-rational
                  (:instance lw-efc-l1-bound-with-error (value (lw-complex-euler-continuation-value rate height error))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-value-clearance-check lw-euler-value-clearance-size
              lw-efc-left-commutes lw-efc-left-distributes lw-efc-fold-constants
              lw-efc-times-negative lw-efc-negative-times lw-efc-zero-times
              lw-efc-minus-one lw-efc-double-negative lw-efc-add-cancel lw-efc-double lw-efc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil)

(defthm lw-euler-circle-factor-anchor
  (implies (and (rationalp rate) (rationalp height) (rationalp outer-radius)
                (rationalp radius) (< 0 radius) (<= radius outer-radius) (< outer-radius rate)
                (lw-complexp point) (equal (lw-complex-norm-square point) (* radius radius))
                (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                (rationalp gap) (< 0 gap) (lw-circle-radial-bracket-clear roots radius radius gap)
                (natp target) (rationalp polynomial-error) (< 0 polynomial-error)
                (rationalp anchor-error) (< 0 anchor-error)
                (<= polynomial-error (* 1/16 (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap))))
                (<= anchor-error (* 1/32 (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap))))
                (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0) (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target polynomial-error) point 0))
                                  (* 1/8 (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap)))))
           (and (<= (* 1/2 (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap)))
                    (lw-euler-value-clearance-size (+ rate (car point)) (+ height (cdr point)) anchor-error))
                (lw-euler-value-clearance-check (+ rate (car point)) (+ height (cdr point)) anchor-error)))
  :hints (("Goal"
           :use (lw-circle-factor-coefficients-clearance
                 lw-polynomial-factor-coefficients-valid
                 (:instance lw-complex-polynomial-rational
                   (coefficients (lw-polynomial-factor-coefficients roots leading)) (offset 0))
                 (:instance lw-euler-uniform-polynomial-valid (radius outer-radius) (error polynomial-error))
                 (:instance lw-complex-polynomial-rational
                   (coefficients (lw-euler-uniform-polynomial rate height outer-radius target polynomial-error)) (offset 0))
                 (:instance lw-complex-disk-norm-square)
                 (:instance lw-complex-disk-enlarge (cap outer-radius))
                 (:instance lw-euler-disk-point-data (offset point))
                 (:instance lw-complex-euler-continuation-value-rational
                   (rate (+ rate (car point))) (height (+ height (cdr point))) (error anchor-error))
                 (:instance lw-complex-euler-uniform-polynomial-comparison
                   (radius outer-radius) (error polynomial-error) (value-error anchor-error))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0)) (middle (lw-complex-polynomial (lw-euler-uniform-polynomial rate height outer-radius target polynomial-error) point 0)) (right (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) anchor-error))
                   (radius (* 1/8 (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap)))) (other-radius (+ polynomial-error (* 1/4 anchor-error))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0) (lw-complex-euler-continuation-value (+ rate (car point)) (+ height (cdr point)) anchor-error)))
                   (radius (+ (* 1/8 (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap))) polynomial-error (* 1/4 anchor-error)))
                   (cap (* 1/4 (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap)))))
                 (:instance lw-euler-value-clearance-from-approximation
                   (rate (+ rate (car point))) (height (+ height (cdr point))) (error anchor-error)
                   (lower (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap))) (model (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-efc-left-commutes lw-efc-left-distributes lw-efc-fold-constants
              lw-efc-times-negative lw-efc-negative-times lw-efc-zero-times
              lw-efc-minus-one lw-efc-double-negative lw-efc-add-cancel lw-efc-double lw-efc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t :nonlinearp nil))
  :rule-classes nil)
