(in-package "ACL2")

(include-book "complex-log-series-comparison")
(include-book "pole-dominance")

; Choose the geometric truncation and mesh before evaluating any points.

(local (defthm lw-clsp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-clsp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-clsp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-clsp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-clsp-times-negative (a b) (b a)))
                 :in-theory (disable lw-clsp-times-negative)))))

(local (defthm lw-clsp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-clsp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-clsp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-clsp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-clsp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-clsp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-clsp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-clsp-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clsp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-clsp-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-clsp-left-commutes)))))

(defun lw-complex-log-series-slope-budget (ratio)
  (/ ratio (- 1 ratio)))

(defun lw-complex-log-series-count (ratio tolerance)
  (lw-resolvent-truncation-count ratio
    (/ tolerance (* 8 (+ 1 (lw-complex-log-series-slope-budget ratio))))))

(defun lw-complex-log-series-mesh (ratio tolerance)
  (let* ((slope (lw-complex-log-series-slope-budget ratio))
         (count (lw-complex-log-series-count ratio tolerance))
         (size (+ (* 4 slope) (/ (* 4 (+ (* 19 slope slope) (* 2 count))) tolerance))))
    (+ 1 (lw-precision-fuel size 1))))

(defun lw-complex-log-series-request (ratio tolerance)
  (/ tolerance (* 16 (lw-complex-log-series-mesh ratio tolerance))))

(local
 (defthm lw-clsp-budget-data
   (implies (and (rationalp ratio) (<= 0 ratio) (< ratio 1)
                 (rationalp tolerance) (< 0 tolerance))
            (let* ((slope (lw-complex-log-series-slope-budget ratio))
                   (count (lw-complex-log-series-count ratio tolerance))
                   (request (/ tolerance (* 8 (+ 1 slope)))))
              (and (rationalp slope) (<= 0 slope) (natp count)
                   (rationalp request) (< 0 request)
                   (<= (* 2 slope (lw-rational-power ratio count)) (* 1/4 tolerance)))))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value (- 1 ratio)))
                  (:instance lw-clsp-multiply-order (a 0) (b ratio) (factor (/ (- 1 ratio))))
                  (:instance lw-resolvent-truncation-count-natural
                    (radius ratio) (error (/ tolerance (* 8 (+ 1 (lw-complex-log-series-slope-budget ratio))))))
                  (:instance lw-reciprocal-positive (value (* 8 (+ 1 (lw-complex-log-series-slope-budget ratio)))))
                  (:instance lw-clsp-positive-product (a tolerance) (b (/ (* 8 (+ 1 (lw-complex-log-series-slope-budget ratio))))))
                  (:instance lw-rational-power-computed-decay
                    (error (/ tolerance (* 8 (+ 1 (lw-complex-log-series-slope-budget ratio)))))
                    (index (lw-complex-log-series-count ratio tolerance)))
                  (:instance lw-clsp-multiply-order
                    (a (lw-rational-power ratio (lw-complex-log-series-count ratio tolerance)))
                    (b (/ tolerance (* 8 (+ 1 (lw-complex-log-series-slope-budget ratio)))))
                    (factor (* 2 (lw-complex-log-series-slope-budget ratio))))
                  (:instance lw-clsp-multiply-order
                    (a (lw-complex-log-series-slope-budget ratio))
                    (b (+ 1 (lw-complex-log-series-slope-budget ratio)))
                    (factor (* 2 (/ tolerance (* 8 (+ 1 (lw-complex-log-series-slope-budget ratio)))))))
                  (:instance lw-clsp-inverse-factor
                    (divisor (* 8 (+ 1 (lw-complex-log-series-slope-budget ratio)))) (coefficient tolerance)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-series-slope-budget lw-complex-log-series-count
              lw-rational-power-rational
              lw-clsp-left-commutes lw-clsp-left-distributes lw-clsp-fold-constants
              lw-clsp-times-negative lw-clsp-negative-times lw-clsp-zero-times
              lw-clsp-minus-one lw-clsp-double-negative lw-clsp-add-cancel lw-clsp-double lw-clsp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clsp-precision-fuel-natural
   (natp (lw-precision-fuel width epsilon))
   :hints (("Goal" :in-theory (enable lw-precision-fuel)))
   :rule-classes (:type-prescription)))

(local
 (defthm lw-clsp-mesh-bound
   (implies (and (rationalp slope) (<= 0 slope) (natp count)
                 (rationalp tolerance) (< 0 tolerance))
            (let* ((cost (+ (* 19 slope slope) (* 2 count)))
                   (width (+ (* 4 slope) (/ (* 4 cost) tolerance)))
                   (mesh (+ 1 (lw-precision-fuel width 1))))
              (and (posp mesh) (<= (* 4 slope) mesh)
                   (<= (* 4 cost) (* mesh tolerance)))))
   :hints (("Goal"
            :use ((:instance lw-clsp-multiply-order (a 0) (b slope) (factor slope))
                  (:instance lw-reciprocal-positive (value tolerance))
                  (:instance lw-clsp-multiply-order
                    (a 0) (b (* 4 (+ (* 19 slope slope) (* 2 count)))) (factor (/ tolerance)))
                  (:instance lw-precision-fuel-adequate
                    (width (+ (* 4 slope) (/ (* 4 (+ (* 19 slope slope) (* 2 count))) tolerance))) (epsilon 1))
                  (:instance lw-clsp-multiply-order
                    (a (/ (* 4 (+ (* 19 slope slope) (* 2 count))) tolerance))
                    (b (+ 1 (lw-precision-fuel (+ (* 4 slope) (/ (* 4 (+ (* 19 slope slope) (* 2 count))) tolerance)) 1)))
                    (factor tolerance))
                  (:instance lw-clsp-inverse-factor
                    (divisor tolerance) (coefficient (* 4 (+ (* 19 slope slope) (* 2 count))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:type-prescription lw-clsp-precision-fuel-natural)
              lw-clsp-left-commutes lw-clsp-left-distributes lw-clsp-fold-constants
              lw-clsp-times-negative lw-clsp-negative-times lw-clsp-zero-times
              lw-clsp-minus-one lw-clsp-double-negative lw-clsp-add-cancel lw-clsp-double lw-clsp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-clsp-scalar-precision
   (implies (and (rationalp slope) (<= 0 slope) (natp count)
                 (rationalp tolerance) (< 0 tolerance)
                 (posp mesh) (<= (* 4 slope) mesh)
                 (<= (* 4 (+ (* 19 slope slope) (* 2 count))) (* mesh tolerance))
                 (rationalp geometric-tail) (<= (* 2 slope geometric-tail) (* 1/4 tolerance))
                 (rationalp error) (< 0 error) (<= error (/ tolerance (* 16 mesh))))
            (let ((delta (* (/ mesh) slope)))
              (and (<= delta 1/4)
                   (<= (+ (* mesh (+ (* 4 error) (* 19 delta delta)))
                          (* 2 mesh delta geometric-tail)
                          (* 2 count (/ mesh))) tolerance))))
   :hints (("Goal"
            :use ((:instance lw-reciprocal-positive (value mesh))
                  (:instance lw-clsp-multiply-order (a (* 4 slope)) (b mesh) (factor (/ mesh)))
                  (:instance lw-clsp-multiply-order
                    (a (* 4 (+ (* 19 slope slope) (* 2 count)))) (b (* mesh tolerance)) (factor (/ mesh)))
                  (:instance lw-clsp-multiply-order (a error) (b (/ tolerance (* 16 mesh))) (factor (* 16 mesh)))
                  (:instance lw-clsp-inverse-factor (divisor (* 16 mesh)) (coefficient tolerance))
                  (:instance lw-clsp-inverse-factor (divisor mesh) (coefficient 1))
                  (:instance lw-clsp-inverse-factor (divisor mesh) (coefficient tolerance))
                  (:instance lw-clsp-inverse-factor (divisor mesh) (coefficient (* 19 (/ mesh) slope slope)))
                  (:instance lw-clsp-inverse-factor (divisor mesh) (coefficient (* 2 slope geometric-tail))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-clsp-left-commutes lw-clsp-left-distributes lw-clsp-fold-constants
              lw-clsp-times-negative lw-clsp-negative-times lw-clsp-zero-times
              lw-clsp-minus-one lw-clsp-double-negative lw-clsp-add-cancel lw-clsp-double lw-clsp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-log-series-request-data
  (implies (and (rationalp ratio) (<= 0 ratio) (< ratio 1)
                (rationalp tolerance) (< 0 tolerance))
           (let ((count (lw-complex-log-series-count ratio tolerance))
                 (mesh (lw-complex-log-series-mesh ratio tolerance))
                 (request (lw-complex-log-series-request ratio tolerance)))
             (and (natp count) (posp mesh) (rationalp request) (< 0 request))))
  :hints (("Goal"
           :use (lw-clsp-budget-data
                 (:instance lw-clsp-mesh-bound (slope (lw-complex-log-series-slope-budget ratio)) (count (lw-complex-log-series-count ratio tolerance)))
                 (:instance lw-reciprocal-positive (value (* 16 (lw-complex-log-series-mesh ratio tolerance))))
                 (:instance lw-clsp-positive-product (a tolerance) (b (/ (* 16 (lw-complex-log-series-mesh ratio tolerance))))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-series-mesh lw-complex-log-series-request
              lw-clsp-left-commutes lw-clsp-left-distributes lw-clsp-fold-constants
              lw-clsp-times-negative lw-clsp-negative-times lw-clsp-zero-times
              lw-clsp-minus-one lw-clsp-double-negative lw-clsp-add-cancel lw-clsp-double lw-clsp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-complex-log-series-computed-precision
  (implies (and (lw-complex-diskp point ratio) (< ratio 1)
                (rationalp tolerance) (< 0 tolerance)
                (rationalp error) (< 0 error)
                (<= error (lw-complex-log-series-request ratio tolerance)))
           (let* ((count (lw-complex-log-series-count ratio tolerance))
                  (logarithm (car (lw-signed-log-bounds (lw-complex-norm-square (lw-complex-sub (cons 1 0) point)) error)))
                  (polynomial (lw-complex-polynomial (lw-complex-log-series-polynomial count) point 0)))
             (<= (abs (+ logarithm (* 2 (car polynomial)))) tolerance)))
  :hints (("Goal"
           :use ((:instance lw-complex-disk-data (radius ratio))
                 lw-clsp-budget-data lw-complex-log-series-request-data
                 (:instance lw-clsp-mesh-bound (slope (lw-complex-log-series-slope-budget ratio)) (count (lw-complex-log-series-count ratio tolerance)))
                 (:instance lw-clsp-scalar-precision
                   (slope (lw-complex-log-series-slope-budget ratio))
                   (count (lw-complex-log-series-count ratio tolerance))
                   (mesh (lw-complex-log-series-mesh ratio tolerance))
                   (geometric-tail (lw-rational-power ratio (lw-complex-log-series-count ratio tolerance))))
                 (:instance lw-rational-power-rational (base ratio) (exponent (lw-complex-log-series-count ratio tolerance)))
                 (:instance lw-complex-log-series-comparison
                   (count (lw-complex-log-series-count ratio tolerance)) (mesh (lw-complex-log-series-mesh ratio tolerance))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-log-series-request lw-complex-log-series-mesh
              lw-complex-log-series-slope-budget lw-complex-log-series-budget
              lw-clsp-left-commutes lw-clsp-left-distributes lw-clsp-fold-constants
              lw-clsp-times-negative lw-clsp-negative-times lw-clsp-zero-times
              lw-clsp-minus-one lw-clsp-double-negative lw-clsp-add-cancel lw-clsp-double lw-clsp-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
