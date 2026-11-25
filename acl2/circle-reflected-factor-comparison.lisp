(in-package "ACL2")

(include-book "circle-factor-reflection")
(include-book "circle-radial-clearance")
(include-book "rpow-continuity")

; A separated circle gives a uniform ratio between the original and
; reflected products when the inner factor count has a fixed bound.

(local (defthm lw-crfc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-crfc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-crfc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-crfc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-crfc-times-negative (a b) (b a)))
                 :in-theory (disable lw-crfc-times-negative)))))

(local (defthm lw-crfc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-crfc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-crfc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-crfc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-crfc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-crfc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-crfc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-crfc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-crfc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-reflection-retention (gap)
  (let ((distance (lw-circle-radial-clearance 1 gap)))
    (* 1/4 distance distance)))

(local
 (defthm lw-crfc-reflected-value-disk
   (implies (and (lw-complex-diskp root 1) (lw-complex-diskp point 1))
            (lw-complex-diskp (lw-circle-reflected-factor-value root point) 2))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (point root) (radius 1))
                  (:instance lw-complex-disk-data (radius 1))
                  (:instance lw-complex-conjugate-disk (point root) (radius 1))
                  (:instance lw-complex-scale-disk (point (lw-complex-conjugate root)) (factor -1) (radius 1))
                  (:instance lw-complex-mul-disk (left (lw-circle-reflected-factor-slope root)) (right point)
                    (radius 1) (other-radius 1))
                  (:instance lw-complex-disk-norm-square (point (cons 1 0)) (radius 1))
                  (:instance lw-complex-add-disk
                    (left (cons 1 0)) (right (lw-complex-mul (lw-circle-reflected-factor-slope root) point))
                    (radius 1) (other-radius 1)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-factor-slope lw-circle-reflected-factor-value lw-complex-norm-square abs
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crfc-distance-order
   (implies (and (rationalp radius) (< 0 radius) (<= radius 1)
                 (rationalp gap) (< 0 gap))
            (and (rationalp (lw-circle-radial-clearance 1 gap)) (< 0 (lw-circle-radial-clearance 1 gap)) (< (lw-circle-radial-clearance 1 gap) 1)
                 (rationalp (lw-circle-radial-clearance radius gap)) (<= (lw-circle-radial-clearance 1 gap) (lw-circle-radial-clearance radius gap))
                 (<= (* (lw-circle-radial-clearance 1 gap) (lw-circle-radial-clearance 1 gap)) (* (lw-circle-radial-clearance radius gap) (lw-circle-radial-clearance radius gap)))))
   :hints (("Goal"
            :use ((:instance lw-circle-radial-clearance-budget (radius 1))
                  lw-circle-radial-clearance-budget
                  (:instance lw-reciprocal-antitone (left (+ 1 gap (* 4 radius))) (right (+ 5 gap)))
                  (:instance lw-crfc-multiply-order (a (/ (+ 5 gap))) (b (/ (+ 1 gap (* 4 radius)))) (factor gap))
                  (:instance lw-crfc-multiply-order (a (lw-circle-radial-clearance 1 gap)) (b (lw-circle-radial-clearance radius gap)) (factor (lw-circle-radial-clearance 1 gap)))
                  (:instance lw-crfc-multiply-order (a (lw-circle-radial-clearance 1 gap)) (b (lw-circle-radial-clearance radius gap)) (factor (lw-circle-radial-clearance radius gap))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-radial-clearance
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crfc-head-budget
   (implies (and (rationalp distance) (< 0 distance) (< distance 1)
                 (rationalp ordinary-square) (<= (* distance distance) ordinary-square)
                 (rationalp reflected-square) (<= reflected-square 4))
            (and (< 0 (* 1/4 distance distance)) (< (* 1/4 distance distance) 1)
                 (<= (* 1/4 distance distance reflected-square) ordinary-square)))
   :hints (("Goal"
            :use ((:instance lw-crfc-positive-product (a distance) (b distance))
                  (:instance lw-crfc-multiply-order (a distance) (b 1) (factor distance))
                  (:instance lw-crfc-multiply-order (a reflected-square) (b 4) (factor (* 1/4 distance distance))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crfc-reflected-head
   (implies (and (lw-complexp root) (lw-complexp point)
                 (rationalp radius) (< 0 radius) (<= radius 1)
                 (rationalp gap) (< 0 gap)
                 (rationalp cutoff-square) (<= (lw-complex-norm-square root) cutoff-square) (< cutoff-square 1)
                 (equal (lw-complex-norm-square point) (* radius radius))
                 (or (<= (+ (lw-complex-norm-square root) gap) (* radius radius))
                     (<= (+ (* radius radius) gap) (lw-complex-norm-square root))))
            (and (rationalp (lw-circle-reflection-retention gap)) (< 0 (lw-circle-reflection-retention gap)) (< (lw-circle-reflection-retention gap) 1)
                 (<= (* (lw-circle-reflection-retention gap) (lw-complex-norm-square (lw-circle-reflected-factor-value root point))) (lw-complex-norm-square (lw-complex-sub point root)))))
   :hints (("Goal"
            :use (lw-crfc-distance-order lw-circle-radial-clearance-valid lw-crfc-reflected-value-disk
                  (:instance lw-crfc-head-budget
                    (distance (lw-circle-radial-clearance 1 gap)) (ordinary-square (lw-complex-norm-square (lw-complex-sub point root))) (reflected-square (lw-complex-norm-square (lw-circle-reflected-factor-value root point))))
                  (:instance lw-complex-norm-square-valid (point root))
                  (:instance lw-complex-ring-rational (left point) (right root))
                  (:instance lw-complex-norm-square-valid (point (lw-complex-sub point root)))
                  (:instance lw-complex-disk-data (point (lw-circle-reflected-factor-value root point)) (radius 2))
                  (:instance lw-complex-norm-square-valid (point (lw-circle-reflected-factor-value root point)))
                  (:instance lw-complex-disk-norm-square (point (lw-circle-reflected-factor-value root point)) (radius 2))
                  (:instance lw-complex-disk-norm-square (point root) (radius 1))
                  (:instance lw-complex-disk-norm-square (radius 1))
                  (:instance lw-crfc-multiply-order (a radius) (b 1) (factor radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflection-retention
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crfc-retention-data
   (implies (and (rationalp gap) (< 0 gap))
            (and (rationalp (lw-circle-reflection-retention gap)) (< 0 (lw-circle-reflection-retention gap)) (< (lw-circle-reflection-retention gap) 1)))
   :hints (("Goal"
            :use ((:instance lw-circle-radial-clearance-budget (radius 1))
                  (:instance lw-crfc-head-budget (distance (lw-circle-radial-clearance 1 gap)) (ordinary-square (* (lw-circle-radial-clearance 1 gap) (lw-circle-radial-clearance 1 gap))) (reflected-square 0)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflection-retention
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-crfc-product-step
   (implies (and (rationalp ordinary-head) (<= 0 ordinary-head)
                 (rationalp reflected-head) (<= 0 reflected-head)
                 (rationalp ordinary-tail) (rationalp reflected-tail) (<= 0 reflected-tail)
                 (rationalp head-weight) (<= 0 head-weight)
                 (rationalp tail-weight) (<= 0 tail-weight)
                 (<= (* head-weight reflected-head) ordinary-head)
                 (<= (* tail-weight reflected-tail) ordinary-tail)
                 (equal reflected (* reflected-head reflected-tail)))
            (<= (* head-weight tail-weight reflected) (* ordinary-head ordinary-tail)))
   :hints (("Goal"
            :use ((:instance lw-crfc-multiply-order
                    (a (* head-weight reflected-head)) (b ordinary-head) (factor (* tail-weight reflected-tail)))
                  (:instance lw-crfc-multiply-order
                    (a (* tail-weight reflected-tail)) (b ordinary-tail) (factor ordinary-head))
                  (:instance lw-crfc-multiply-order (a 0) (b tail-weight) (factor reflected-tail)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-crfc-power-zero
   (equal (lw-rational-power base 0) 1)
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-crfc-power-successor
   (implies (natp n)
            (equal (lw-rational-power base (+ 1 n)) (* base (lw-rational-power base n))))
   :hints (("Goal" :expand ((lw-rational-power base (+ 1 n)))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-crfc-reflected-empty
   (implies (and (lw-complexp leading) (lw-complexp point))
            (equal (lw-complex-polynomial (lw-circle-reflected-factor-polynomial nil leading cutoff-square) point 0) leading))
   :hints (("Goal" :use ((:instance lw-circle-reflected-factor-evaluation (roots nil)))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:executable-counterpart lw-ray-pointsp) endp
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-crfc-reflected-value-rational
   (implies (and (lw-complexp root) (lw-complexp point))
            (lw-complexp (lw-circle-reflected-factor-value root point)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-factor-value
              lw-circle-reflected-factor-slope lw-complex-conjugate-rational
              lw-complex-scale-rational lw-complex-ring-rational
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-crfc-product-comparison
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point)
                 (rationalp radius) (< 0 radius) (<= radius 1)
                 (rationalp cutoff-square) (< cutoff-square 1)
                 (rationalp gap) (< 0 gap)
                 (equal (lw-complex-norm-square point) (* radius radius))
                 (lw-circle-radial-bracket-clear roots radius radius gap))
            (<= (* (lw-rational-power (lw-circle-reflection-retention gap) (lw-circle-inner-factor-count roots cutoff-square)) (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0))) (lw-complex-norm-square (lw-polynomial-linear-factor-value roots leading point))))
   :hints (("Goal"
            :induct (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-reflected-factor-polynomial)
              lw-crfc-power-zero lw-crfc-power-successor lw-crfc-reflected-empty
              lw-crfc-reflected-value-rational lw-circle-reflected-factor-polynomial-valid
              lw-complex-polynomial-rational lw-complex-norm-square-valid lw-complex-norm-square-product
              lw-polynomial-linear-factor-value lw-polynomial-linear-factor-value-rational
              lw-complex-ring-rational lw-circle-inner-factor-count (:type-prescription lw-circle-inner-factor-count)
              lw-rational-power-rational lw-circle-radial-bracket-clear lw-ray-pointsp endp
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-circle-reflected-factor-evaluation
                        lw-crfc-retention-data
                        (:instance lw-crfc-reflected-head (root (car roots)))
                        (:instance lw-rational-power-nonnegative
                          (base (lw-circle-reflection-retention gap)) (exponent (lw-circle-inner-factor-count (cdr roots) cutoff-square)))
                        (:instance lw-complex-norm-square-product
                          (left (lw-complex-sub point (car roots))) (right (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) point 0)))
                        (:instance lw-complex-norm-square-product
                          (left (lw-circle-reflected-factor-value (car roots) point)) (right (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) point 0)))
                        (:instance lw-crfc-product-step
                          (ordinary-head (lw-complex-norm-square (lw-complex-sub point (car roots)))) (reflected-head (lw-complex-norm-square (lw-complex-sub point (car roots))))
                          (ordinary-tail (lw-complex-norm-square (lw-polynomial-linear-factor-value (cdr roots) leading point)))
                          (reflected-tail (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) point 0)))
                          (tail-weight (lw-rational-power (lw-circle-reflection-retention gap) (lw-circle-inner-factor-count (cdr roots) cutoff-square)))
                          (head-weight 1) (reflected (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0))))
                        (:instance lw-crfc-product-step
                          (ordinary-head (lw-complex-norm-square (lw-complex-sub point (car roots)))) (reflected-head (lw-complex-norm-square (lw-circle-reflected-factor-value (car roots) point)))
                          (ordinary-tail (lw-complex-norm-square (lw-polynomial-linear-factor-value (cdr roots) leading point)))
                          (reflected-tail (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) point 0)))
                          (tail-weight (lw-rational-power (lw-circle-reflection-retention gap) (lw-circle-inner-factor-count (cdr roots) cutoff-square)))
                          (head-weight (lw-circle-reflection-retention gap)) (reflected (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0)))))
                  :do-not-induct t)))
   :rule-classes nil))

(local
 (defthm lw-crfc-power-order
   (implies (and (rationalp ratio) (<= 0 ratio) (<= ratio 1)
                 (natp count) (natp budget) (<= count budget))
            (<= (lw-rational-power ratio budget) (lw-rational-power ratio count)))
   :hints (("Goal"
            :use ((:instance lw-rational-power-add-exponents
                    (base ratio) (left count) (right (- budget count)))
                  (:instance lw-rational-power-rational (base ratio) (exponent count))
                  (:instance lw-rational-power-rational (base ratio) (exponent (- budget count)))
                  (:instance lw-rational-power-nonnegative (base ratio) (exponent count))
                  (:instance lw-rational-power-monotone-base (left ratio) (right 1) (exponent (- budget count)))
                  (:instance lw-crfc-multiply-order
                    (a (lw-rational-power ratio (- budget count))) (b 1)
                    (factor (lw-rational-power ratio count))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power-one
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-reflected-factor-lower-transfer
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point)
                 (rationalp radius) (< 0 radius) (<= radius 1)
                 (rationalp cutoff-square) (< cutoff-square 1)
                 (rationalp gap) (< 0 gap)
                 (equal (lw-complex-norm-square point) (* radius radius))
                 (lw-circle-radial-bracket-clear roots radius radius gap)
                (rationalp reflected-square) (< 0 reflected-square)
                (<= reflected-square (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0)))
                (natp budget) (<= (lw-circle-inner-factor-count roots cutoff-square) budget))
           (let ((lower (* reflected-square (lw-rational-power (lw-circle-reflection-retention gap) budget))))
             (and (rationalp lower) (< 0 lower)
                  (<= lower
                      (lw-complex-norm-square
                       (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0))))))
  :hints (("Goal"
           :use (lw-crfc-retention-data lw-crfc-product-comparison lw-polynomial-factor-coefficients-evaluation
                 lw-circle-reflected-factor-polynomial-valid
                 (:instance lw-complex-polynomial-rational (coefficients (lw-circle-reflected-factor-polynomial roots leading cutoff-square)) (offset 0))
                 (:instance lw-complex-norm-square-valid (point (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0)))
                 (:instance lw-crfc-power-order (ratio (lw-circle-reflection-retention gap)) (count (lw-circle-inner-factor-count roots cutoff-square)))
                 (:instance lw-rational-power-positive (base (lw-circle-reflection-retention gap)) (exponent budget))
                 (:instance lw-crfc-positive-product (a reflected-square) (b (lw-rational-power (lw-circle-reflection-retention gap) budget)))
                 (:instance lw-crfc-multiply-order
                   (a reflected-square) (b (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0))) (factor (lw-rational-power (lw-circle-reflection-retention gap) budget)))
                 (:instance lw-crfc-multiply-order
                   (a (lw-rational-power (lw-circle-reflection-retention gap) budget)) (b (lw-rational-power (lw-circle-reflection-retention gap) (lw-circle-inner-factor-count roots cutoff-square))) (factor (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:type-prescription lw-circle-inner-factor-count) lw-rational-power-rational
              lw-crfc-left-commutes lw-crfc-left-distributes lw-crfc-fold-constants
              lw-crfc-times-negative lw-crfc-negative-times lw-crfc-zero-times
              lw-crfc-minus-one lw-crfc-double-negative lw-crfc-add-cancel lw-crfc-double lw-crfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
