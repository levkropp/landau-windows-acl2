(in-package "ACL2")

(include-book "circle-exterior-resolvent")
(include-book "cauchy-resolvents")
(include-book "polynomial-maps")

; The finite pole model retains the requested Taylor coefficient exactly.

(local (defthm lw-cep-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cep-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cep-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cep-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cep-times-negative (a b) (b a)))
                 :in-theory (disable lw-cep-times-negative)))))

(local (defthm lw-cep-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cep-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cep-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cep-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cep-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cep-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cep-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cep-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cep-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cep-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cep-left-commutes)))))

(defun lw-circle-exterior-pole-count (root radius target error)
 (max (+ 1 target)
      (lw-resolvent-truncation-count
       (lw-circle-exterior-ratio-cap root radius)
       (lw-pole-coefficient-precision (cons 1 0) (lw-complex-scale -1 root) error))))

(defun lw-circle-exterior-pole-polynomial (root radius target error)
 (let* ((offset (lw-complex-scale -1 root))
        (ratio (lw-pole-resolvent-ratio offset (- radius)))
        (factor (lw-pole-resolvent-factor (cons 1 0) offset)))
  (lw-polynomial-multiply-coefficients
   factor (lw-resolvent-coefficients ratio 0 (lw-circle-exterior-pole-count root radius target error)))))

(local (defthm lw-cep-model-data
 (implies (and (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (* radius radius) (lw-complex-norm-square root))) (natp target) (rationalp error) (< 0 error))
  (and (natp (lw-circle-exterior-pole-count root radius target error)) (< target (lw-circle-exterior-pole-count root radius target error))
       (<= (lw-resolvent-truncation-count (lw-circle-exterior-ratio-cap root radius) (lw-pole-coefficient-precision (cons 1 0) (lw-complex-scale -1 root) error)) (lw-circle-exterior-pole-count root radius target error))
       (lw-complexp (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius))) (lw-complexp (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root)))
       (lw-complex-coefficientsp (lw-resolvent-coefficients (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) 0 (lw-circle-exterior-pole-count root radius target error)))
       (equal (len (lw-resolvent-coefficients (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) 0 (lw-circle-exterior-pole-count root radius target error))) (lw-circle-exterior-pole-count root radius target error))))
 :hints (("Goal"
  :use (lw-circle-exterior-resolvent-data
        (:instance lw-pole-resolvent-data (residue (cons 1 0)) (offset (lw-complex-scale -1 root)) (radius (- radius)))
        (:instance lw-pole-coefficient-precision-adequate (residue (cons 1 0)) (offset (lw-complex-scale -1 root)))
        (:instance lw-resolvent-truncation-count-natural (radius (lw-circle-exterior-ratio-cap root radius)) (error (lw-pole-coefficient-precision (cons 1 0) (lw-complex-scale -1 root) error)))
        (:instance lw-resolvent-coefficients-valid (ratio (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius))) (offset 0) (count (lw-circle-exterior-pole-count root radius target error))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-pole-count max (:executable-counterpart lw-complexp) lw-cep-left-commutes lw-cep-left-distributes lw-cep-fold-constants lw-cep-times-negative lw-cep-negative-times lw-cep-zero-times lw-cep-minus-one lw-cep-double-negative lw-cep-add-cancel lw-cep-double lw-cep-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-circle-exterior-pole-polynomial-valid
 (implies (and (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (* radius radius) (lw-complex-norm-square root))) (natp target) (rationalp error) (< 0 error)) (lw-complex-coefficientsp (lw-circle-exterior-pole-polynomial root radius target error)))
 :hints (("Goal"
  :use (lw-cep-model-data
        (:instance lw-polynomial-multiply-coefficients-valid (factor (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root))) (coefficients (lw-resolvent-coefficients (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) 0 (lw-circle-exterior-pole-count root radius target error)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-pole-polynomial lw-cep-left-commutes lw-cep-left-distributes lw-cep-fold-constants lw-cep-times-negative lw-cep-negative-times lw-cep-zero-times lw-cep-minus-one lw-cep-double-negative lw-cep-add-cancel lw-cep-double lw-cep-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-circle-exterior-pole-polynomial-coefficient
 (implies (and (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (* radius radius) (lw-complex-norm-square root))) (natp target) (rationalp error) (< 0 error))
  (equal (lw-complex-coefficient-at (lw-circle-exterior-pole-polynomial root radius target error) target 0)
         (lw-pole-unit-coefficient (cons 1 0) (lw-complex-scale -1 root) (- radius) target)))
 :hints (("Goal"
  :use (lw-cep-model-data
        (:instance lw-polynomial-multiply-coefficients-valid (factor (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root))) (coefficients (lw-resolvent-coefficients (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) 0 (lw-circle-exterior-pole-count root radius target error))))
        (:instance lw-complex-coefficient-at-nth (coefficients (lw-circle-exterior-pole-polynomial root radius target error)) (offset 0))
        (:instance lw-polynomial-multiply-coefficients-nth (factor (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root))) (coefficients (lw-resolvent-coefficients (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) 0 (lw-circle-exterior-pole-count root radius target error))) (index target))
        (:instance lw-resolvent-coefficient-nth (ratio (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius))) (offset 0) (count (lw-circle-exterior-pole-count root radius target error)) (index target)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-pole-polynomial lw-pole-unit-coefficient lw-cep-left-commutes lw-cep-left-distributes lw-cep-fold-constants lw-cep-times-negative lw-cep-negative-times lw-cep-zero-times lw-cep-minus-one lw-cep-double-negative lw-cep-add-cancel lw-cep-double lw-cep-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-circle-exterior-pole-polynomial-error
 (implies (and (and (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (* radius radius) (lw-complex-norm-square root))) (natp target) (rationalp error) (< 0 error)) (lw-complex-diskp point 1))
  (lw-complex-diskp (lw-complex-sub (lw-complex-reciprocal (lw-complex-sub (lw-complex-scale radius point) root)) (lw-complex-polynomial (lw-circle-exterior-pole-polynomial root radius target error) point 0)) error))
 :hints (("Goal"
  :use (lw-circle-exterior-resolvent-data lw-circle-exterior-resolvent-identity lw-cep-model-data
        (:instance lw-complex-disk-data (radius 1))
        (:instance lw-pole-coefficient-precision-adequate (residue (cons 1 0)) (offset (lw-complex-scale -1 root)))
        (:instance lw-resolvent-computed-polynomial-error
          (ratio (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius))) (radius (lw-circle-exterior-ratio-cap root radius)) (error (lw-pole-coefficient-precision (cons 1 0) (lw-complex-scale -1 root) error)) (count (lw-circle-exterior-pole-count root radius target error)))
        (:instance lw-polynomial-multiply-coefficients-evaluation
          (factor (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root))) (coefficients (lw-resolvent-coefficients (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) 0 (lw-circle-exterior-pole-count root radius target error))) (offset 0))
        (:instance lw-complex-polynomial-rational (coefficients (lw-resolvent-coefficients (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) 0 (lw-circle-exterior-pole-count root radius target error))) (offset 0))
        (:instance lw-resolvent-value-rational (ratio (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius))))
        (:instance lw-complex-l1-bound (point (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root))))
        (:instance lw-complex-left-product-error (factor (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root))) (cap (lw-complex-l1 (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root))))
         (a (lw-resolvent-value (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) point)) (b (lw-complex-polynomial (lw-resolvent-coefficients (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) 0 (lw-circle-exterior-pole-count root radius target error)) point 0)) (error (lw-pole-coefficient-precision (cons 1 0) (lw-complex-scale -1 root) error)))
        (:instance lw-complex-disk-enlarge
          (point (lw-complex-sub (lw-complex-reciprocal (lw-complex-sub (lw-complex-scale radius point) root)) (lw-complex-polynomial (lw-circle-exterior-pole-polynomial root radius target error) point 0)))
          (radius (* (lw-complex-l1 (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root))) (lw-pole-coefficient-precision (cons 1 0) (lw-complex-scale -1 root) error))) (cap error)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-exterior-pole-polynomial (:executable-counterpart lw-complexp) lw-cep-left-commutes lw-cep-left-distributes lw-cep-fold-constants lw-cep-times-negative lw-cep-negative-times lw-cep-zero-times lw-cep-minus-one lw-cep-double-negative lw-cep-add-cancel lw-cep-double lw-cep-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
