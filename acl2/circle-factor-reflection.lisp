(in-package "ACL2")

(include-book "polynomial-factor-coefficients")

; Reflect small-root factors across the unit circle without changing the
; boundary norm. The value at zero then controls how many were reflected.

(local (defthm lw-cfrf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cfrf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cfrf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cfrf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cfrf-times-negative (a b) (b a)))
                 :in-theory (disable lw-cfrf-times-negative)))))

(local (defthm lw-cfrf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cfrf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cfrf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cfrf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cfrf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cfrf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cfrf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cfrf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfrf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-reflected-factor-slope (root)
  (lw-complex-scale -1 (lw-complex-conjugate root)))

(defun lw-circle-reflected-factor-value (root point)
  (lw-complex-add (cons 1 0) (lw-complex-mul (lw-circle-reflected-factor-slope root) point)))

(local
 (defthm lw-cfrf-boundary-identity
   (implies (and (lw-complexp root) (lw-complexp point))
            (equal
             (lw-complex-norm-square (lw-circle-reflected-factor-value root point))
             (+ (lw-complex-norm-square (lw-complex-sub point root))
                (* (- (lw-complex-norm-square root) 1)
                   (- (lw-complex-norm-square point) 1)))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-sub lw-complex-scale
              lw-circle-reflected-factor-value lw-circle-reflected-factor-slope
              lw-complex-conjugate lw-complex-mul lw-complex-norm-square
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp t))
   :rule-classes nil))

(defthm lw-circle-reflected-factor-unit-norm
  (implies (and (lw-complexp root) (lw-complexp point)
                (equal (lw-complex-norm-square point) 1))
           (equal (lw-complex-norm-square (lw-circle-reflected-factor-value root point))
                  (lw-complex-norm-square (lw-complex-sub point root))))
  :hints (("Goal" :use (lw-cfrf-boundary-identity
                        (:instance lw-complex-ring-rational (left point) (right root))
                        (:instance lw-complex-norm-square-valid (point (lw-complex-sub point root))))
                  :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                  :do-not-induct t))
  :rule-classes nil)

(defun lw-circle-reflected-factor-polynomial (roots leading cutoff-square)
  (declare (xargs :measure (acl2-count roots)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp roots)
      (list leading)
    (let* ((root (car roots))
           (tail (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square))
           (reflectp (<= (lw-complex-norm-square root) cutoff-square)))
      (lw-polynomial-multiply-linear
       (if reflectp (cons 1 0) (lw-complex-scale -1 root))
       (if reflectp (lw-circle-reflected-factor-slope root) (cons 1 0))
       tail))))

(defun lw-circle-inner-factor-count (roots cutoff-square)
  (declare (xargs :measure (acl2-count roots)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp roots)
      0
    (+ (if (<= (lw-complex-norm-square (car roots)) cutoff-square) 1 0)
       (lw-circle-inner-factor-count (cdr roots) cutoff-square))))

(defthm lw-circle-reflected-factor-polynomial-valid
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading))
           (lw-complex-coefficientsp (lw-circle-reflected-factor-polynomial roots leading cutoff-square)))
  :hints (("Goal"
           :induct (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-reflected-factor-polynomial)
              lw-circle-reflected-factor-polynomial lw-circle-reflected-factor-slope
              lw-complex-conjugate-rational lw-polynomial-multiply-linear-valid
              lw-complex-scale-rational lw-ray-pointsp lw-complex-coefficientsp endp
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))))

(local
 (defthm lw-cfrf-reflected-value-data
   (implies (and (lw-complexp root) (lw-complexp point))
            (and (lw-complexp (lw-circle-reflected-factor-slope root))
                 (lw-complexp (lw-circle-reflected-factor-value root point))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-factor-value
              lw-circle-reflected-factor-slope lw-complex-conjugate-rational
              lw-complex-scale-rational lw-complex-ring-rational
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cfrf-linear-factor-value
   (implies (and (lw-complexp root) (lw-complexp point))
            (and (equal (lw-complex-add (lw-complex-scale -1 root) (lw-complex-mul (cons 1 0) point))
                        (lw-complex-sub point root))
                 (equal (lw-complex-add (cons 1 0) (lw-complex-mul (lw-circle-reflected-factor-slope root) point))
                        (lw-circle-reflected-factor-value root point))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-scale
              lw-complex-sub lw-complex-mul lw-circle-reflected-factor-value
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cfrf-single-value
   (implies (and (lw-complexp leading) (lw-complexp point))
            (equal (lw-complex-polynomial (list leading) point 0) leading))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-polynomial lw-complexp lw-complex-power
              lw-complex-mul lw-complex-add lw-complex-scale endp
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(defthm lw-circle-reflected-factor-evaluation
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point))
            (equal (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0)
                   (if (endp roots)
                       leading
                     (lw-complex-mul
                      (if (<= (lw-complex-norm-square (car roots)) cutoff-square)
                          (lw-circle-reflected-factor-value (car roots) point)
                        (lw-complex-sub point (car roots)))
                      (lw-complex-polynomial
                       (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) point 0)))))
   :hints (("Goal" :expand ((lw-circle-reflected-factor-polynomial roots leading cutoff-square))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-reflected-factor-polynomial lw-cfrf-single-value lw-cfrf-linear-factor-value lw-cfrf-reflected-value-data
              lw-circle-reflected-factor-polynomial-valid lw-polynomial-multiply-linear-evaluation
              lw-complex-scale-rational lw-ray-pointsp endp
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil)

(local
 (defthm lw-cfrf-boundary-norm
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point)
                 (equal (lw-complex-norm-square point) 1))
            (equal (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0))
                   (lw-complex-norm-square (lw-polynomial-linear-factor-value roots leading point))))
   :hints (("Goal"
            :induct (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-reflected-factor-polynomial)
              lw-cfrf-reflected-value-data
              lw-circle-reflected-factor-polynomial-valid lw-complex-polynomial-rational
              lw-polynomial-linear-factor-value lw-polynomial-linear-factor-value-rational
              lw-complex-ring-rational lw-complex-norm-square-product
              lw-ray-pointsp endp
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-circle-reflected-factor-evaluation
                        (:instance lw-circle-reflected-factor-evaluation (roots nil))
                        (:instance lw-circle-reflected-factor-unit-norm (root (car roots)))
                        (:instance lw-complex-norm-square-product
                          (left (lw-complex-sub point (car roots))) (right (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) point 0)))
                        (:instance lw-complex-norm-square-product
                          (left (lw-circle-reflected-factor-value (car roots) point)) (right (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) point 0))))
                  :do-not-induct t)))))

(defthm lw-circle-reflected-factor-boundary-norm
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading) (lw-complexp point)
                (equal (lw-complex-norm-square point) 1))
           (equal (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) point 0))
                  (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0))))
  :hints (("Goal" :use (lw-cfrf-boundary-norm lw-polynomial-factor-coefficients-evaluation)
                  :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                  :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-cfrf-center-factor-norm
   (implies (lw-complexp root)
            (and (equal (lw-complex-norm-square (lw-circle-reflected-factor-value root (cons 0 0))) 1)
                 (equal (lw-complex-norm-square (lw-complex-sub (cons 0 0) root))
                        (lw-complex-norm-square root))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-sub lw-complex-scale
              lw-circle-reflected-factor-value lw-circle-reflected-factor-slope
              lw-complex-conjugate lw-complex-mul lw-complex-norm-square
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cfrf-power-zero
   (equal (lw-rational-power cutoff-square 0) 1)
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-cfrf-reflected-empty
   (implies (and (lw-complexp leading) (lw-complexp point))
            (equal (lw-complex-polynomial (lw-circle-reflected-factor-polynomial nil leading cutoff-square) point 0)
                   leading))
   :hints (("Goal" :use ((:instance lw-circle-reflected-factor-evaluation (roots nil)))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:executable-counterpart lw-ray-pointsp)

              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cfrf-power-successor
   (implies (natp n)
            (equal (lw-rational-power cutoff-square (+ 1 n))
                   (* cutoff-square (lw-rational-power cutoff-square n))))
   :hints (("Goal" :expand ((lw-rational-power cutoff-square (+ 1 n)))
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-rational-power
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cfrf-center-step
   (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= 0 right)
                 (rationalp product) (<= 0 product)
                 (rationalp root-square) (<= 0 root-square)
                 (rationalp cutoff-square) (<= 0 cutoff-square)
                 (<= left (* product right)))
            (and (<= (* root-square left) (* root-square product right))
                 (implies (<= root-square cutoff-square)
                          (<= (* root-square left) (* cutoff-square product right)))))
   :hints (("Goal"
            :use ((:instance lw-cfrf-multiply-order (a left) (b (* product right)) (factor root-square))
                  (:instance lw-cfrf-multiply-order (a root-square) (b cutoff-square) (factor (* product right)))
                  (:instance lw-cfrf-multiply-order (a 0) (b product) (factor right)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-cfrf-scaled-norm
   (implies (and (rationalp weight) (rationalp a) (rationalp b)
                 (equal value (* a b)))
            (equal (* weight value) (* a weight b)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-cfrf-center-growth
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                 (rationalp cutoff-square) (<= 0 cutoff-square))
            (<= (lw-complex-norm-square (lw-polynomial-linear-factor-value roots leading (cons 0 0)))
                (* (lw-rational-power cutoff-square (lw-circle-inner-factor-count roots cutoff-square)) (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (cons 0 0) 0)))))
   :hints (("Goal"
            :induct (lw-circle-reflected-factor-polynomial roots leading cutoff-square)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-circle-reflected-factor-polynomial)
              lw-cfrf-reflected-value-data lw-cfrf-center-factor-norm lw-cfrf-power-successor lw-cfrf-power-zero lw-cfrf-reflected-empty
              lw-circle-reflected-factor-polynomial-valid lw-complex-polynomial-rational
              lw-circle-inner-factor-count (:type-prescription lw-circle-inner-factor-count)
              (:executable-counterpart lw-rational-power) lw-rational-power-rational
              lw-polynomial-linear-factor-value lw-polynomial-linear-factor-value-rational
              lw-complex-ring-rational lw-complex-norm-square-product lw-complex-norm-square-valid
              lw-ray-pointsp endp
              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-circle-reflected-factor-evaluation (point (cons 0 0)))
                        (:instance lw-circle-reflected-factor-evaluation (roots nil) (point (cons 0 0)))
                        (:instance lw-rational-power-nonnegative
                         (base cutoff-square) (exponent (lw-circle-inner-factor-count (cdr roots) cutoff-square)))
                        (:instance lw-cfrf-center-step (left (lw-complex-norm-square (lw-polynomial-linear-factor-value (cdr roots) leading (cons 0 0))))
                          (right (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) (cons 0 0) 0)))
                          (product (lw-rational-power cutoff-square (lw-circle-inner-factor-count (cdr roots) cutoff-square)))
                          (root-square (lw-complex-norm-square (car roots))))
                        (:instance lw-cfrf-scaled-norm
                          (a (lw-complex-norm-square (car roots)))
                          (b (lw-complex-norm-square
                              (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) (cons 0 0) 0)))
                          (weight (lw-rational-power cutoff-square (lw-circle-inner-factor-count (cdr roots) cutoff-square)))
                          (value (lw-complex-norm-square
                                  (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (cons 0 0) 0))))
                        (:instance lw-complex-norm-square-product
                          (left (lw-complex-sub (cons 0 0) (car roots))) (right (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) (cons 0 0) 0)))
                        (:instance lw-complex-norm-square-product
                          (left (lw-circle-reflected-factor-value (car roots) (cons 0 0))) (right (lw-complex-polynomial (lw-circle-reflected-factor-polynomial (cdr roots) leading cutoff-square) (cons 0 0) 0))))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-circle-reflected-factor-center-growth
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                (rationalp cutoff-square) (<= 0 cutoff-square))
           (<= (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) (cons 0 0) 0))
               (* (lw-rational-power cutoff-square (lw-circle-inner-factor-count roots cutoff-square)) (lw-complex-norm-square (lw-complex-polynomial (lw-circle-reflected-factor-polynomial roots leading cutoff-square) (cons 0 0) 0)))))
  :hints (("Goal" :use (lw-cfrf-center-growth (:instance lw-polynomial-factor-coefficients-evaluation (point (cons 0 0))))
                  :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfrf-left-commutes lw-cfrf-left-distributes lw-cfrf-fold-constants
              lw-cfrf-times-negative lw-cfrf-negative-times lw-cfrf-zero-times
              lw-cfrf-minus-one lw-cfrf-double-negative lw-cfrf-add-cancel lw-cfrf-double lw-cfrf-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                  :do-not-induct t))
  :rule-classes nil)
