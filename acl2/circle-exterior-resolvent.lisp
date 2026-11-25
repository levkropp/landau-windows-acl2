(in-package "ACL2")

(include-book "pole-resolvents")

; Exterior factors have a strictly contracting resolvent on the unit disk.

(local (defthm lw-cer-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cer-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cer-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cer-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cer-times-negative (a b) (b a)))
                 :in-theory (disable lw-cer-times-negative)))))

(local (defthm lw-cer-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cer-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cer-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cer-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cer-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cer-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cer-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cer-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cer-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cer-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cer-left-commutes)))))

(local (defthm lw-cer-inverse-rational
 (implies (rationalp a) (rationalp (/ a))) :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-cer-product-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (* a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-cer-sum-rational
 (implies (and (rationalp a) (rationalp b)) (rationalp (+ a b)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-cer-offset-norm
 (implies (lw-complexp root)
  (and (lw-complexp (lw-complex-scale -1 root))
       (equal (lw-complex-norm-square (lw-complex-scale -1 root)) (lw-complex-norm-square root))))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-scale lw-complex-norm-square lw-complexp lw-cer-left-commutes lw-cer-left-distributes lw-cer-fold-constants lw-cer-times-negative lw-cer-negative-times lw-cer-zero-times lw-cer-minus-one lw-cer-double-negative lw-cer-add-cancel lw-cer-double lw-cer-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defun lw-circle-exterior-ratio-cap (root radius)
 (* 1/2 (+ 1 (* radius radius (/ (lw-complex-norm-square root))))))

(local (defthm lw-cer-multiply-strict
 (implies (and (rationalp a) (rationalp b) (< a b) (rationalp factor) (< 0 factor))
  (< (* a factor) (* b factor)))
 :rule-classes nil
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-cer-left-commutes lw-cer-left-distributes lw-cer-fold-constants lw-cer-times-negative lw-cer-negative-times lw-cer-zero-times lw-cer-minus-one lw-cer-double-negative lw-cer-add-cancel lw-cer-double lw-cer-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(local (defthm lw-cer-square-nonnegative
 (implies (rationalp x) (<= 0 (* x x)))
 :rule-classes nil
 :hints (("Goal" :cases ((<= 0 x))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-cer-left-commutes lw-cer-left-distributes lw-cer-fold-constants lw-cer-times-negative lw-cer-negative-times lw-cer-zero-times lw-cer-minus-one lw-cer-double-negative lw-cer-add-cancel lw-cer-double lw-cer-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t :do-not-induct t))))

(local (defthm lw-cer-half-sum-square
 (implies (rationalp s)
  (<= s (* 1/2 (+ 1 s) 1/2 (+ 1 s))))
 :rule-classes nil
 :hints (("Goal" :use ((:instance lw-cer-square-nonnegative (x (* 1/2 (- s 1))))) :in-theory (union-theories
 '(fold-consts-in-+ lw-cer-left-commutes lw-cer-left-distributes lw-cer-fold-constants lw-cer-times-negative lw-cer-negative-times lw-cer-zero-times lw-cer-minus-one lw-cer-double-negative lw-cer-add-cancel lw-cer-double lw-cer-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp nil :do-not-induct t))))

(local (defthm lw-cer-cap-calculation
 (implies (and (rationalp norm) (rationalp radius) (< 0 radius) (< (* radius radius) norm))
  (let* ((s (* radius radius (/ norm)))
         (cap (* 1/2 (+ 1 s))))
   (and (< 0 norm) (rationalp cap) (<= 0 cap) (< cap 1) (<= s (* cap cap)))))
 :hints (("Goal"
  :use ((:instance lw-cer-inverse-factor (divisor norm) (coefficient 1))
        (:instance lw-reciprocal-positive (value norm))
        (:instance lw-cer-multiply-strict (a (* radius radius)) (b norm) (factor (/ norm)))
        (:instance lw-cer-positive-product (a (* radius radius)) (b (/ norm)))
        (:instance lw-cer-positive-product (a radius) (b radius))
        (:instance lw-cer-half-sum-square (s (* radius radius (/ norm)))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-cer-inverse-rational lw-cer-product-rational lw-cer-sum-rational lw-cer-left-commutes lw-cer-left-distributes lw-cer-fold-constants lw-cer-times-negative lw-cer-negative-times lw-cer-zero-times lw-cer-minus-one lw-cer-double-negative lw-cer-add-cancel lw-cer-double lw-cer-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-circle-exterior-resolvent-data
 (implies (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (* radius radius) (lw-complex-norm-square root))) (and (lw-complexp (lw-complex-scale -1 root)) (not (equal (lw-complex-scale -1 root) (cons 0 0)))
                      (rationalp (lw-circle-exterior-ratio-cap root radius)) (<= 0 (lw-circle-exterior-ratio-cap root radius)) (< (lw-circle-exterior-ratio-cap root radius) 1)
                      (lw-complex-diskp (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) (lw-circle-exterior-ratio-cap root radius))))
 :hints (("Goal"
  :use (lw-complex-norm-square-valid lw-cer-offset-norm
        (:instance lw-cer-cap-calculation (norm (lw-complex-norm-square root)))
        (:instance lw-complex-norm-lower-nonzero (point (lw-complex-scale -1 root)) (lower radius))
        (:instance lw-pole-resolvent-data (residue (cons 1 0)) (offset (lw-complex-scale -1 root)) (radius (- radius)))
        (:instance lw-complex-reciprocal-rational (point (lw-complex-scale -1 root)))
        (:instance lw-complex-norm-square-reciprocal (point (lw-complex-scale -1 root)))
        (:instance lw-complex-norm-square-product (left (cons (- radius) 0))
                    (right (lw-complex-reciprocal (lw-complex-scale -1 root))))
        (:instance lw-complex-disk-norm-square (point (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius))) (radius (lw-circle-exterior-ratio-cap root radius))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-resolvent-ratio lw-circle-exterior-ratio-cap lw-complexp lw-complex-norm-square lw-cer-product-rational lw-cer-sum-rational lw-cer-left-commutes lw-cer-left-distributes lw-cer-fold-constants lw-cer-times-negative lw-cer-negative-times lw-cer-zero-times lw-cer-minus-one lw-cer-double-negative lw-cer-add-cancel lw-cer-double lw-cer-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))

(local (defthm lw-cer-offset-law
 (implies (and (lw-complexp root) (lw-complexp point) (rationalp radius))
  (equal (lw-complex-sub (lw-complex-scale -1 root) (lw-complex-mul (cons (- radius) 0) point))
         (lw-complex-sub (lw-complex-scale radius point) root)))
 :hints (("Goal"
  :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-scale lw-complex-mul lw-complex-sub lw-complexp lw-cer-left-commutes lw-cer-left-distributes lw-cer-fold-constants lw-cer-times-negative lw-cer-negative-times lw-cer-zero-times lw-cer-minus-one lw-cer-double-negative lw-cer-add-cancel lw-cer-double lw-cer-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t))))

(defthm lw-circle-exterior-resolvent-identity
 (implies (and (and (lw-complexp root) (rationalp radius) (< 0 radius) (< (* radius radius) (lw-complex-norm-square root))) (lw-complex-diskp point 1))
  (equal (lw-complex-reciprocal (lw-complex-sub (lw-complex-scale radius point) root))
         (lw-complex-mul (lw-pole-resolvent-factor (cons 1 0) (lw-complex-scale -1 root)) (lw-resolvent-value (lw-pole-resolvent-ratio (lw-complex-scale -1 root) (- radius)) point))))
 :hints (("Goal"
  :use (lw-circle-exterior-resolvent-data
        (:instance lw-pole-unit-value-as-resolvent (residue (cons 1 0))
                   (offset (lw-complex-scale -1 root)) (radius (- radius)) (cap (lw-circle-exterior-ratio-cap root radius)))
        (:instance lw-pole-unit-value-rational (residue (cons 1 0)) (offset (lw-complex-scale -1 root)) (radius (- radius)))
        (:instance lw-complex-disk-data (radius 1)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-pole-unit-value lw-cer-offset-law lw-complex-ring-rational lw-complex-scale-rational lw-complex-reciprocal-rational lw-complex-mul-one (:executable-counterpart lw-complexp) lw-cer-left-commutes lw-cer-left-distributes lw-cer-fold-constants lw-cer-times-negative lw-cer-negative-times lw-cer-zero-times lw-cer-minus-one lw-cer-double-negative lw-cer-add-cancel lw-cer-double lw-cer-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :do-not-induct t)))
