(in-package "ACL2")

(include-book "circle-reflected-logarithm-polynomial")
(include-book "circle-reflected-logarithm-increment")

; Each factor contributes one Taylor comparison and a bounded signed
; logarithm product error. The radius and precisions are common.

(local (defthm lw-crlc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crlc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crlc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crlc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crlc-times-negative (a b) (b a)))
                 :in-theory (disable lw-crlc-times-negative)))))

(local (defthm lw-crlc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crlc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crlc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crlc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crlc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crlc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crlc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crlc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crlc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-crlc-zero-polynomial
   (implies (lw-complexp point)
            (equal (lw-complex-polynomial (list (cons 0 0)) point 0) (cons 0 0)))
   :hints (("Goal"
            :use ((:instance lw-complex-mul-zero (point (lw-complex-power point 0)))
                  (:instance lw-complex-power-rational (index 0)))
            :expand ((lw-complex-polynomial (list (cons 0 0)) point 0)
                     (lw-complex-polynomial nil point 1))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:executable-counterpart lw-complex-add)
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-crlc-length-natural
   (natp (len roots))
   :hints (("Goal" :induct (len roots) :in-theory (enable len)))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-crlc-combine-error
   (implies (and (rationalp current) (rationalp previous) (rationalp unit)
                 (rationalp head) (rationalp tail) (rationalp full)
                 (rationalp tolerance) (rationalp error) (natp count)
                 (equal full (+ head tail))
                 (<= (abs (- current (+ previous unit))) (* 9 error))
                 (<= (abs (+ unit (* 2 head))) tolerance)
                 (<= (abs (+ previous (* 2 tail))) (* count (+ tolerance (* 9 error)))))
            (<= (abs (+ current (* 2 full))) (* (+ 1 count) (+ tolerance (* 9 error)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crlc-evaluation-real-data
   (implies (and (lw-complexp full) (lw-complexp head) (lw-complexp tail)
                 (equal full (lw-complex-add head tail)))
            (and (rationalp (car full)) (rationalp (car head)) (rationalp (car tail))
                 (equal (car full) (+ (car head) (car tail)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crlc-log-ratio-type
   (implies (and (rationalp left) (< 0 left) (rationalp right) (< 0 right)
                 (rationalp error) (< 0 error))
            (rationalp (- (car (lw-signed-log-bounds left error)) (car (lw-signed-log-bounds right error)))))
   :hints (("Goal"
            :use ((:instance lw-signed-log-bounds-data (value left))
                  (:instance lw-signed-log-bounds-data (value right)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-intervalp
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crlc-scale-data
   (implies (and (lw-complex-diskp point 1) (rationalp scale) (< 0 scale)
                 (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1))
            (and (lw-complexp point) (lw-complexp (lw-complex-scale scale point)) (lw-complex-diskp (lw-complex-scale scale point) scale)
                 (< 0 cutoff-square) (lw-complex-diskp (cons 0 0) scale)))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (radius 1))
                  (:instance lw-complex-scale-rational (factor scale))
                  (:instance lw-complex-scale-disk (factor scale) (radius 1))
                  (:instance lw-crlc-positive-product (a scale) (b scale))
                  (:instance lw-complex-zero-disk (radius scale)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crlc-current-ratio-type
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (lw-complex-diskp point scale) (rationalp scale) (< 0 scale)
                 (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1)
                 (rationalp error) (< 0 error))
            (rationalp (lw-circle-reflected-log-ratio roots leading cutoff-square point error)))
   :hints (("Goal"
            :use ((:instance lw-circle-reflected-square-positive (radius scale))
                  (:instance lw-complex-zero-disk (radius scale))
                  (:instance lw-circle-reflected-square-positive (point (cons 0 0)) (radius scale))
                  (:instance lw-crlc-log-ratio-type (left (lw-circle-reflected-value-square roots leading cutoff-square point)) (right (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-log-ratio
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crlc-polynomial-sum
   (implies (and (lw-ray-pointsp roots) (consp roots) (lw-complexp point)
                 (rationalp cutoff-square) (< 0 cutoff-square) (< cutoff-square 1)
                 (rationalp scale) (natp count))
            (let ((head (car (lw-complex-polynomial (lw-complex-log-series-polynomial count) (lw-complex-mul (lw-circle-reflected-factor-parameter (car roots) cutoff-square) (lw-complex-scale scale point)) 0)))
                  (tail (car (lw-complex-polynomial (lw-circle-reflected-log-polynomial (cdr roots) cutoff-square scale count) point 0)))
                  (full (car (lw-complex-polynomial (lw-circle-reflected-log-polynomial roots cutoff-square scale count) point 0))))
              (and (rationalp head) (rationalp tail) (rationalp full)
                   (equal full (+ head tail)))))
   :hints (("Goal"
            :use (lw-circle-reflected-log-polynomial-step
                  (:instance lw-circle-reflected-log-polynomial-data)
                  (:instance lw-circle-reflected-log-polynomial-data (roots (cdr roots)))
                  lw-circle-reflected-log-series-data
                  (:instance lw-circle-reflected-factor-parameter-data (root (car roots)))
                  (:instance lw-complex-scale-rational (factor scale))
                  (:instance lw-complex-ring-rational (left (lw-circle-reflected-factor-parameter (car roots) cutoff-square)) (right (lw-complex-scale scale point)))
                  (:instance lw-complex-polynomial-rational (coefficients (lw-complex-log-series-polynomial count)) (point (lw-complex-mul (lw-circle-reflected-factor-parameter (car roots) cutoff-square) (lw-complex-scale scale point))) (offset 0))
                  (:instance lw-complex-polynomial-rational (coefficients (lw-circle-reflected-log-polynomial roots cutoff-square scale count)) (offset 0))
                  (:instance lw-complex-polynomial-rational (coefficients (lw-circle-reflected-log-polynomial (cdr roots) cutoff-square scale count)) (offset 0))
                  (:instance lw-crlc-evaluation-real-data
                    (full (lw-complex-polynomial (lw-circle-reflected-log-polynomial roots cutoff-square scale count) point 0)) (head (lw-complex-polynomial (lw-complex-log-series-polynomial count) (lw-complex-mul (lw-circle-reflected-factor-parameter (car roots) cutoff-square) (lw-complex-scale scale point)) 0)) (tail (lw-complex-polynomial (lw-circle-reflected-log-polynomial (cdr roots) cutoff-square scale count) point 0))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ray-pointsp endp
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crlc-series-head
   (implies (and (lw-complexp (car roots)) (lw-complex-diskp point 1) (rationalp scale) (< 0 scale)
                 (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1) (rationalp tolerance) (< 0 tolerance) (rationalp error) (< 0 error) (<= error (lw-complex-log-series-request (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance)))
            (and (natp (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance))
                 (rationalp (car (lw-signed-log-bounds (lw-complex-norm-square (lw-circle-reflected-unit-factor (car roots) cutoff-square (lw-complex-scale scale point))) error)))
                 (<= (abs (+ (car (lw-signed-log-bounds (lw-complex-norm-square (lw-circle-reflected-unit-factor (car roots) cutoff-square (lw-complex-scale scale point))) error)) (* 2 (car (lw-complex-polynomial (lw-complex-log-series-polynomial (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance)) (lw-complex-mul (lw-circle-reflected-factor-parameter (car roots) cutoff-square) (lw-complex-scale scale point)) 0))))) tolerance)))
   :hints (("Goal"
            :use (lw-crlc-scale-data
                  (:instance lw-circle-reflected-factor-argument-disk (root (car roots)) (point (lw-complex-scale scale point)) (inner-radius scale))
                  (:instance lw-complex-log-series-request-data (ratio (lw-circle-reflected-factor-ratio scale cutoff-square)))
                  (:instance lw-complex-log-series-computed-precision (point (lw-complex-mul (lw-circle-reflected-factor-parameter (car roots) cutoff-square) (lw-complex-scale scale point))) (ratio (lw-circle-reflected-factor-ratio scale cutoff-square)))
                  (:instance lw-circle-reflected-unit-square-positive (root (car roots)) (point (lw-complex-scale scale point)) (radius scale))
                  (:instance lw-signed-log-bounds-data (value (lw-complex-norm-square (lw-circle-reflected-unit-factor (car roots) cutoff-square (lw-complex-scale scale point))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-unit-factor lw-intervalp
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crlc-empty-log-ratio
   (implies (and (lw-complexp leading) (not (equal leading (cons 0 0)))
                 (lw-complexp point) (rationalp error) (< 0 error))
            (equal (lw-circle-reflected-log-ratio nil leading cutoff-square point error) 0))
   :hints (("Goal"
            :use ((:instance lw-complex-norm-square-valid (point leading))
                  (:instance lw-complex-norm-square-positive (point leading))
                  (:instance lw-signed-log-bounds-data (value (lw-complex-norm-square leading))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-log-ratio lw-circle-reflected-square-empty lw-intervalp
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))))

(defthm lw-circle-reflected-logarithm-comparison
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                (lw-complex-diskp point 1) (rationalp scale) (< 0 scale)
                 (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1) (rationalp tolerance) (< 0 tolerance) (rationalp error) (< 0 error) (<= error (lw-complex-log-series-request (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance)))
           (<= (abs (+ (lw-circle-reflected-log-ratio roots leading cutoff-square (lw-complex-scale scale point) error) (* 2 (car (lw-complex-polynomial (lw-circle-reflected-log-polynomial roots cutoff-square scale (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance)) point 0)))))
               (* (len roots) (+ tolerance (* 9 error)))))
  :hints (("Goal"
           :induct (lw-circle-reflected-log-polynomial roots cutoff-square scale (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-reflected-log-polynomial)
              lw-crlc-empty-log-ratio lw-crlc-zero-polynomial lw-crlc-length-natural
              lw-ray-pointsp len endp (:executable-counterpart abs)
              lw-crlc-left-commutes lw-crlc-left-distributes lw-crlc-fold-constants
              lw-crlc-times-negative lw-crlc-negative-times lw-crlc-zero-times
              lw-crlc-minus-one lw-crlc-double-negative lw-crlc-add-cancel lw-crlc-double lw-crlc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use (lw-crlc-scale-data lw-crlc-series-head
                       (:instance lw-crlc-polynomial-sum (count (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance)))
                       (:instance lw-crlc-current-ratio-type (point (lw-complex-scale scale point)))
                       (:instance lw-crlc-current-ratio-type (point (lw-complex-scale scale point)) (roots (cdr roots)))
                       (:instance lw-circle-reflected-log-ratio-increment (point (lw-complex-scale scale point)) (radius scale))
                       (:instance lw-crlc-combine-error
                         (current (lw-circle-reflected-log-ratio roots leading cutoff-square (lw-complex-scale scale point) error)) (previous (lw-circle-reflected-log-ratio (cdr roots) leading cutoff-square (lw-complex-scale scale point) error)) (unit (car (lw-signed-log-bounds (lw-complex-norm-square (lw-circle-reflected-unit-factor (car roots) cutoff-square (lw-complex-scale scale point))) error)))
                         (head (car (lw-complex-polynomial (lw-complex-log-series-polynomial (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance)) (lw-complex-mul (lw-circle-reflected-factor-parameter (car roots) cutoff-square) (lw-complex-scale scale point)) 0))) (tail (car (lw-complex-polynomial (lw-circle-reflected-log-polynomial (cdr roots) cutoff-square scale (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance)) point 0)))
                         (full (car (lw-complex-polynomial (lw-circle-reflected-log-polynomial roots cutoff-square scale (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance)) point 0))) (count (len (cdr roots)))))
                 :expand ((lw-circle-reflected-log-polynomial nil cutoff-square scale (lw-complex-log-series-count (lw-circle-reflected-factor-ratio scale cutoff-square) tolerance)))
                 :do-not-induct t)))
  :rule-classes nil)
