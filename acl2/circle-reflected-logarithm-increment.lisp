(in-package "ACL2")

(include-book "circle-reflected-square-product")
(include-book "signed-log-multiplication")

; The center factors cancel exactly in each log ratio increment.

(local (defthm lw-crli-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crli-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crli-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crli-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crli-times-negative (a b) (b a)))
                 :in-theory (disable lw-crli-times-negative)))))

(local (defthm lw-crli-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crli-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crli-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crli-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crli-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crli-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crli-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crli-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crli-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-reflected-log-ratio (roots leading cutoff-square point error)
  (- (car (lw-signed-log-bounds (lw-circle-reflected-value-square roots leading cutoff-square point) error))
     (car (lw-signed-log-bounds (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)) error))))

(local
 (defthm lw-crli-center-unit
   (implies (and (lw-complexp root) (rationalp cutoff-square)
                 (< 0 cutoff-square) (< cutoff-square 1))
            (equal (lw-complex-norm-square (lw-circle-reflected-unit-factor root cutoff-square (cons 0 0))) 1))
   :hints (("Goal"
            :use (lw-circle-reflected-factor-parameter-data
                  (:instance lw-complex-mul-zero (point (lw-circle-reflected-factor-parameter root cutoff-square)))
                  (:instance lw-complex-sub-zero (point (cons 1 0))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-unit-factor (:executable-counterpart lw-complex-norm-square)
              lw-crli-left-commutes lw-crli-left-distributes lw-crli-fold-constants
              lw-crli-times-negative lw-crli-negative-times lw-crli-zero-times
              lw-crli-minus-one lw-crli-double-negative lw-crli-add-cancel lw-crli-double lw-crli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-crli-scalar-log-combine
   (implies (and (rationalp lc) (rationalp lu) (rationalp lx) (rationalp ly)
                 (rationalp lmiddle) (rationalp lfull) (rationalp lcenter)
                 (rationalp error)
                 (<= (abs (- (+ lu lx) lmiddle)) (* 3 error))
                 (<= (abs (- (+ lc lmiddle) lfull)) (* 3 error))
                 (<= (abs (- (+ lc ly) lcenter)) (* 3 error)))
            (<= (abs (- (- lfull lcenter) (+ (- lx ly) lu))) (* 9 error)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-crli-left-commutes lw-crli-left-distributes lw-crli-fold-constants
              lw-crli-times-negative lw-crli-negative-times lw-crli-zero-times
              lw-crli-minus-one lw-crli-double-negative lw-crli-add-cancel lw-crli-double lw-crli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crli-log-step
   (implies (and (rationalp constant) (< 0 constant) (rationalp unit) (< 0 unit)
                 (rationalp value) (< 0 value) (rationalp center) (< 0 center)
                 (rationalp error) (< 0 error)
                 (equal full (* constant unit value))
                 (equal full-center (* constant center)))
            (<= (abs (- (- (car (lw-signed-log-bounds full error)) (car (lw-signed-log-bounds full-center error)))
                        (+ (- (car (lw-signed-log-bounds value error)) (car (lw-signed-log-bounds center error))) (car (lw-signed-log-bounds unit error)))))
                (* 9 error)))
   :hints (("Goal"
            :use ((:instance lw-crli-positive-product (a unit) (b value))
                  (:instance lw-crli-positive-product (a constant) (b center))
                  (:instance lw-crli-positive-product (a constant) (b (* unit value)))
                  (:instance lw-signed-log-bounds-data (value constant))
                  (:instance lw-signed-log-bounds-data (value unit))
                  (:instance lw-signed-log-bounds-data (value value))
                  (:instance lw-signed-log-bounds-data (value center))
                  (:instance lw-signed-log-bounds-data (value (* unit value)))
                  (:instance lw-signed-log-bounds-data (value full))
                  (:instance lw-signed-log-bounds-data (value full-center))
                  (:instance lw-signed-log-lower-multiplication (left unit) (right value)
                    (left-error error) (right-error error) (product-error error))
                  (:instance lw-signed-log-lower-multiplication (left constant) (right (* unit value))
                    (left-error error) (right-error error) (product-error error))
                  (:instance lw-signed-log-lower-multiplication (left constant) (right center)
                    (left-error error) (right-error error) (product-error error))
                  (:instance lw-crli-scalar-log-combine
                    (lc (car (lw-signed-log-bounds constant error))) (lu (car (lw-signed-log-bounds unit error))) (lx (car (lw-signed-log-bounds value error))) (ly (car (lw-signed-log-bounds center error)))
                    (lmiddle (car (lw-signed-log-bounds (* unit value) error))) (lfull (car (lw-signed-log-bounds full error))) (lcenter (car (lw-signed-log-bounds full-center error)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-intervalp
              lw-crli-left-commutes lw-crli-left-distributes lw-crli-fold-constants
              lw-crli-times-negative lw-crli-negative-times lw-crli-zero-times
              lw-crli-minus-one lw-crli-double-negative lw-crli-add-cancel lw-crli-double lw-crli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-log-ratio-increment
  (implies (and (lw-ray-pointsp roots) (consp roots) (lw-complexp leading) (not (equal leading (cons 0 0)))
                (lw-complex-diskp point radius) (rationalp radius) (< 0 radius)
                (rationalp cutoff-square) (< (* radius radius) cutoff-square) (< cutoff-square 1)
                (rationalp error) (< 0 error))
           (<= (abs (- (lw-circle-reflected-log-ratio roots leading cutoff-square point error) (+ (lw-circle-reflected-log-ratio (cdr roots) leading cutoff-square point error) (car (lw-signed-log-bounds (lw-complex-norm-square (lw-circle-reflected-unit-factor (car roots) cutoff-square point)) error)))))
               (* 9 error)))
  :hints (("Goal"
           :use (lw-complex-disk-data
                 (:instance lw-crli-positive-product (a radius) (b radius))
                 (:instance lw-complex-zero-disk)
                 (:instance lw-circle-reflected-square-positive (roots (cdr roots)))
                 (:instance lw-circle-reflected-square-positive (roots (cdr roots)) (point (cons 0 0)))
                 (:instance lw-circle-reflected-unit-square-positive (root (car roots)))
                 (:instance lw-crli-center-unit (root (car roots)))
                 lw-circle-reflected-square-step
                 (:instance lw-circle-reflected-square-step (point (cons 0 0)))
                 (:instance lw-crli-log-step
                   (constant (lw-complex-norm-square (lw-circle-reflected-factor-normalization (car roots) cutoff-square))) (unit (lw-complex-norm-square (lw-circle-reflected-unit-factor (car roots) cutoff-square point)))
                   (value (lw-circle-reflected-value-square (cdr roots) leading cutoff-square point))
                   (center (lw-circle-reflected-value-square (cdr roots) leading cutoff-square (cons 0 0)))
                   (full (lw-circle-reflected-value-square roots leading cutoff-square point))
                   (full-center (lw-circle-reflected-value-square roots leading cutoff-square (cons 0 0)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-log-ratio lw-ray-pointsp endp
              lw-crli-left-commutes lw-crli-left-distributes lw-crli-fold-constants
              lw-crli-times-negative lw-crli-negative-times lw-crli-zero-times
              lw-crli-minus-one lw-crli-double-negative lw-crli-add-cancel lw-crli-double lw-crli-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
