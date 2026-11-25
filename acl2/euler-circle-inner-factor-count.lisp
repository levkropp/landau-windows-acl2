(in-package "ACL2")

(include-book "circle-inner-factor-count-bound")
(include-book "euler-coefficient-bounds")
(include-book "euler-value-clearance")
(include-book "polynomial-disk-factorization")

; Use the same checked Euler center and numerical cap across all fine
; polynomial and factorization requests on the normalized unit disk.

(local (defthm lw-ecic-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecic-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecic-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecic-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecic-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecic-times-negative)))))

(local (defthm lw-ecic-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecic-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecic-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecic-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecic-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecic-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecic-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecic-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecic-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-ecic-factor-cap
   (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
                 (natp target) (rationalp error) (< 0 error)
                 (rationalp factor-error) (< 0 factor-error)
                 (<= error 1) (<= factor-error 1) (lw-complex-diskp point 1))
            (lw-complex-diskp (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) point 0) (+ 1 (lw-euler-uniform-coefficient-cap rate height radius))))
   :hints (("Goal"
            :use ((:instance lw-euler-polynomial-coefficient-rational (index 0))
                  lw-euler-uniform-coefficient-cap-valid lw-complex-euler-polynomial-uniform-cap
                  (:instance lw-polynomial-disk-factor-data
                    (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (outer-radius 1) (epsilon factor-error))
                  (:instance lw-polynomial-disk-factor-value-error
                    (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (outer-radius 1) (epsilon factor-error))
                  (:instance lw-complex-disk-data (radius 1))
                  (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (offset 0))
                  (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error)) (offset 0))
                  (:instance lw-complex-difference-symmetric
                    (left (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) point 0)) (right (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) point 0)) (radius factor-error))
                  (:instance lw-complex-sub-zero (point (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) point 0)))
                  (:instance lw-complex-sub-zero (point (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) point 0)))
                  (:instance lw-complex-difference-triangle
                    (left (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) point 0)) (middle (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) point 0)) (right (cons 0 0))
                    (radius factor-error) (other-radius (+ -1 (lw-euler-uniform-coefficient-cap rate height radius) error)))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) point 0))
                    (radius (+ factor-error -1 (lw-euler-uniform-coefficient-cap rate height radius) error)) (cap (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-ecic-left-commutes lw-ecic-left-distributes lw-ecic-fold-constants
              lw-ecic-times-negative lw-ecic-negative-times lw-ecic-zero-times
              lw-ecic-minus-one lw-ecic-double-negative lw-ecic-add-cancel lw-ecic-double lw-ecic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defun lw-ecic-countdown (samples)
   (declare (xargs :measure (nfix samples) :hints (("Goal" :in-theory (theory 'ground-zero)))))
   (if (zp samples) 0 (lw-ecic-countdown (- samples 1)))))

(local
 (defthm lw-ecic-boundary-check
   (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
                 (natp target) (rationalp error) (< 0 error)
                 (rationalp factor-error) (< 0 factor-error)
                 (<= error 1) (<= factor-error 1) (natp degree) (natp samples))
            (lw-cauchy-boundary-check (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-cauchy-orbit-rotation degree) 0 samples (+ 1 (lw-euler-uniform-coefficient-cap rate height radius))))
   :hints (("Goal" :induct (lw-ecic-countdown samples)
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-ecic-countdown) lw-cauchy-boundary-check
              lw-ecic-left-commutes lw-ecic-left-distributes lw-ecic-fold-constants
              lw-ecic-times-negative lw-ecic-negative-times lw-ecic-zero-times
              lw-ecic-minus-one lw-ecic-double-negative lw-ecic-add-cancel lw-ecic-double lw-ecic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-cauchy-orbit-data
                        (:instance lw-complex-unit-power
                          (point (lw-cauchy-orbit-rotation degree)) (index (- samples 1)))
                        (:instance lw-ecic-factor-cap (point (lw-complex-power (lw-cauchy-orbit-rotation degree) (- samples 1)))))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-ecic-center-lower-transfer
   (implies (and (lw-complexp model) (lw-complexp value)
                 (rationalp lower) (< 0 lower)
                 (<= (* lower lower) (lw-complex-norm-square value))
                 (lw-complex-diskp (lw-complex-sub value model) (* 1/4 lower)))
            (<= (* (* 1/2 lower) (* 1/2 lower)) (lw-complex-norm-square model)))
   :hints (("Goal"
            :use ((:instance lw-ecic-positive-product (a lower) (b lower))
                  (:instance lw-complex-difference-triangle (left value) (middle model) (right (cons 0 0))
                    (radius (* 1/4 lower)) (other-radius (* 1/2 lower)))
                  (:instance lw-complex-sub-zero (point value))
                  (:instance lw-complex-sub-zero (point model))
                  (:instance lw-complex-disk-norm-square (point model) (radius (* 1/2 lower)))
                  (:instance lw-complex-disk-norm-square (point value) (radius (+ (* 1/4 lower) (* 1/2 lower)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-ecic-left-commutes lw-ecic-left-distributes lw-ecic-fold-constants
              lw-ecic-times-negative lw-ecic-negative-times lw-ecic-zero-times
              lw-ecic-minus-one lw-ecic-double-negative lw-ecic-add-cancel lw-ecic-double lw-ecic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecic-native-center
   (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
                 (natp target) (rationalp error) (< 0 error)
                 (rationalp factor-error) (< 0 factor-error)
                 (rationalp anchor-error) (< 0 anchor-error))
            (lw-complex-diskp (lw-complex-sub (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) (cons 0 0) 0) (lw-complex-euler-continuation-value rate height anchor-error))
                              (+ error (* 1/4 anchor-error))))
   :hints (("Goal"
            :use ((:instance lw-euler-uniform-polynomial-valid)
                  (:instance lw-polynomial-rescale-evaluation
                    (coefficients (lw-euler-uniform-polynomial rate height radius target error)) (point (cons 0 0)) (factor radius) (offset 0))
                  (:instance lw-complex-euler-uniform-polynomial-comparison (point (cons 0 0)) (value-error anchor-error))
                  (:instance lw-complex-zero-disk)
                  (:instance lw-complex-scale-zero (factor radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-coefficient-polynomial
              lw-ecic-left-commutes lw-ecic-left-distributes lw-ecic-fold-constants
              lw-ecic-times-negative lw-ecic-negative-times lw-ecic-zero-times
              lw-ecic-minus-one lw-ecic-double-negative lw-ecic-add-cancel lw-ecic-double lw-ecic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecic-factor-center
   (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
                 (natp target) (rationalp error) (< 0 error)
                 (rationalp factor-error) (< 0 factor-error)
                 (lw-euler-value-clearance-check rate height anchor-error)
                 (<= error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
                 (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error))))
            (<= (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))
                (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (cons 0 0) 0))))
   :hints (("Goal"
            :use (lw-euler-value-clearance-data
                  (:instance lw-complex-euler-value-clearance (request anchor-error))
                  lw-ecic-native-center
                  (:instance lw-euler-polynomial-coefficient-rational (index 0))
                  (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (outer-radius 1) (epsilon factor-error))
                  (:instance lw-polynomial-disk-factor-value-error
                    (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (outer-radius 1) (epsilon factor-error) (point (cons 0 0)))
                  (:instance lw-complex-zero-disk (radius 1))
                  (:instance lw-complex-polynomial-rational (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (point (cons 0 0)) (offset 0))
                  (:instance lw-complex-polynomial-rational (coefficients (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error)) (point (cons 0 0)) (offset 0))
                  (:instance lw-complex-difference-symmetric (left (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) (cons 0 0) 0)) (right (lw-complex-euler-continuation-value rate height anchor-error)) (radius (+ error (* 1/4 anchor-error))))
                  (:instance lw-complex-difference-triangle
                    (left (lw-complex-euler-continuation-value rate height anchor-error)) (middle (lw-complex-polynomial (lw-euler-coefficient-polynomial rate height radius target error) (cons 0 0) 0)) (right (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (cons 0 0) 0)) (radius (+ error (* 1/4 anchor-error))) (other-radius factor-error))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-euler-continuation-value rate height anchor-error) (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (cons 0 0) 0)))
                    (radius (+ error (* 1/4 anchor-error) factor-error)) (cap (* 1/16 (lw-euler-value-clearance-size rate height anchor-error))))
                  (:instance lw-ecic-center-lower-transfer (value (lw-complex-euler-continuation-value rate height anchor-error)) (model (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (cons 0 0) 0)) (lower (* 1/4 (lw-euler-value-clearance-size rate height anchor-error)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-value-clearance-lower
              lw-ecic-left-commutes lw-ecic-left-distributes lw-ecic-fold-constants
              lw-ecic-times-negative lw-ecic-negative-times lw-ecic-zero-times
              lw-ecic-minus-one lw-ecic-double-negative lw-ecic-add-cancel lw-ecic-double lw-ecic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecic-length-natural
   (natp (len coefficients))
   :hints (("Goal" :induct (len coefficients) :in-theory (enable len)))
   :rule-classes (:rewrite :type-prescription)))

(defthm lw-euler-circle-factor-model-data
  (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
                 (natp target) (rationalp error) (< 0 error)
                 (rationalp factor-error) (< 0 factor-error)
                (lw-euler-value-clearance-check rate height anchor-error)
                 (<= error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
                 (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
                (<= error 1) (<= factor-error 1)
                (rationalp cutoff-square) (<= 0 cutoff-square) (< cutoff-square 1))
           (and (lw-ray-pointsp (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error))
                (lw-complexp (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error))))
                (rationalp (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))) (< 0 (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))
                (rationalp (+ 1 (lw-euler-uniform-coefficient-cap rate height radius))) (<= 0 (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)))
                (<= (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)))
                    (lw-complex-norm-square
                     (lw-complex-polynomial (lw-polynomial-factor-coefficients (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error)))) (cons 0 0) 0)))
                (lw-circle-factor-boundary-check (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error))) cutoff-square (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)))))
  :hints (("Goal"
           :use (lw-ecic-factor-center lw-euler-value-clearance-data lw-euler-uniform-coefficient-cap-valid
                 (:instance lw-ecic-positive-product (a (lw-euler-value-clearance-size rate height anchor-error)) (b (lw-euler-value-clearance-size rate height anchor-error)))
                 (:instance lw-euler-polynomial-coefficient-rational (index 0))
                 (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-coefficient-polynomial rate height radius target error)) (outer-radius 1) (epsilon factor-error))
                 (:instance lw-ecic-boundary-check
                   (degree (len (lw-circle-reflected-factor-polynomial (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error))) cutoff-square)))
                   (samples
                    (lw-cauchy-coefficient-count
                     (lw-circle-reflected-factor-polynomial (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error))) cutoff-square)
                     (len (lw-circle-reflected-factor-polynomial (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error))) cutoff-square)) 1)))
                 (:instance lw-cauchy-coefficient-count-natural
                   (coefficients (lw-circle-reflected-factor-polynomial (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error))) cutoff-square))
                   (degree (len (lw-circle-reflected-factor-polynomial (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error))) cutoff-square)))
                   (error 1)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ecic-length-natural lw-polynomial-disk-factor-polynomial lw-circle-factor-boundary-check
              lw-ecic-left-commutes lw-ecic-left-distributes lw-ecic-fold-constants
              lw-ecic-times-negative lw-ecic-negative-times lw-ecic-zero-times
              lw-ecic-minus-one lw-ecic-double-negative lw-ecic-add-cancel lw-ecic-double lw-ecic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-inner-factor-count
  (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius) (< radius rate)
                 (natp target) (rationalp error) (< 0 error)
                 (rationalp factor-error) (< 0 factor-error)
                (lw-euler-value-clearance-check rate height anchor-error)
                 (<= error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
                 (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height anchor-error)))
                (<= error 1) (<= factor-error 1)
                (rationalp cutoff-square) (<= 0 cutoff-square) (< cutoff-square 1))
           (< (lw-circle-inner-factor-count (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error) cutoff-square)
              (lw-circle-inner-factor-count-limit cutoff-square (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))) (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)))))
  :hints (("Goal"
           :use (lw-euler-circle-factor-model-data
                 (:instance lw-circle-inner-factor-count-bound
                   (roots (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height radius target error) 1 factor-error)) (leading (lw-polynomial-leading (lw-polynomial-trim (lw-euler-coefficient-polynomial rate height radius target error)))) (cap (+ 1 (lw-euler-uniform-coefficient-cap rate height radius)))
                   (center-square (* (* 1/8 (lw-euler-value-clearance-size rate height anchor-error)) (* 1/8 (lw-euler-value-clearance-size rate height anchor-error))))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ecic-left-commutes lw-ecic-left-distributes lw-ecic-fold-constants
              lw-ecic-times-negative lw-ecic-negative-times lw-ecic-zero-times
              lw-ecic-minus-one lw-ecic-double-negative lw-ecic-add-cancel lw-ecic-double lw-ecic-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
