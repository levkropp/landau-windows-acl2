(in-package "ACL2")

(include-book "polynomial-geometric-bounds")
(include-book "polynomial-coefficient-maps")
(include-book "complex-exp")

; The increment bound uses the coefficients in unit-disk coordinates.
; On a half disk their tail has a degree-independent geometric bound.

(local (defthm lw-phds-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-phds-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-phds-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-phds-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-phds-times-negative (a b) (b a)))
                 :in-theory (disable lw-phds-times-negative)))))

(local (defthm lw-phds-zero-times (equal (* 0 a) 0)))

(local (defthm lw-phds-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-phds-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-phds-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-phds-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-phds-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-phds-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-phds-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-phds-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-polynomial-max-coefficient-size (coefficients)
  (declare (xargs :measure (acl2-count coefficients)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp coefficients) 0
    (max (lw-complex-l1 (car coefficients))
         (lw-polynomial-max-coefficient-size (cdr coefficients)))))

(defun lw-polynomial-half-disk-slope (coefficients outer)
  (* 2 (/ outer) (lw-polynomial-max-coefficient-size (cdr (lw-polynomial-rescale coefficients outer 0)))))

(local
 (defthm lw-phds-caps-enlarge
   (implies (and (lw-polynomial-coefficient-caps coefficients cap)
                 (rationalp larger) (<= cap larger))
            (lw-polynomial-coefficient-caps coefficients larger))
   :hints (("Goal"
            :induct (lw-polynomial-coefficient-caps coefficients cap)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-coefficient-caps endp
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-disk-enlarge (point (car coefficients)) (radius cap) (cap larger)))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-polynomial-max-coefficient-size-data
  (implies (lw-complex-coefficientsp coefficients)
           (and (rationalp (lw-polynomial-max-coefficient-size coefficients)) (<= 0 (lw-polynomial-max-coefficient-size coefficients))
                (lw-polynomial-coefficient-caps coefficients (lw-polynomial-max-coefficient-size coefficients))))
  :hints (("Goal"
           :induct (lw-polynomial-max-coefficient-size coefficients)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-polynomial-max-coefficient-size)
              lw-polynomial-max-coefficient-size lw-polynomial-coefficient-caps
              lw-complex-coefficientsp max endp
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-l1-bound (point (car coefficients)))
                       (:instance lw-complex-disk-enlarge (point (car coefficients))
                         (radius (lw-complex-l1 (car coefficients))) (cap (lw-polynomial-max-coefficient-size (cdr coefficients))))
                       (:instance lw-phds-caps-enlarge (coefficients (cdr coefficients))
                         (cap (lw-polynomial-max-coefficient-size (cdr coefficients))) (larger (lw-complex-l1 (car coefficients)))))
                 :do-not-induct t)))
  :rule-classes nil)

(defthm lw-polynomial-max-coefficient-size-upper
  (implies (and (lw-complex-coefficientsp coefficients)
                (lw-polynomial-coefficient-caps coefficients cap)
                (rationalp cap) (<= 0 cap))
           (<= (lw-polynomial-max-coefficient-size coefficients) (* 2 cap)))
  :hints (("Goal"
           :induct (lw-polynomial-max-coefficient-size coefficients)
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-polynomial-max-coefficient-size)
              lw-polynomial-max-coefficient-size lw-polynomial-coefficient-caps
              lw-complex-coefficientsp lw-complex-l1 lw-complexp max abs endp
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-disk-coordinates (point (car coefficients)) (radius cap)))
                 :do-not-induct t)))
  :rule-classes nil)

(defthm lw-polynomial-half-disk-slope-data
  (implies (and (lw-complex-coefficientsp coefficients) (rationalp outer) (< 0 outer))
           (and (rationalp (lw-polynomial-half-disk-slope coefficients outer)) (<= 0 (lw-polynomial-half-disk-slope coefficients outer))))
  :hints (("Goal"
           :use ((:instance lw-polynomial-rescale-valid (factor outer) (offset 0))
                 (:instance lw-polynomial-max-coefficient-size-data (coefficients (cdr (lw-polynomial-rescale coefficients outer 0))))
                 (:instance lw-reciprocal-positive (value outer))
                 (:instance lw-phds-multiply-order (a 0) (b (lw-polynomial-max-coefficient-size (cdr (lw-polynomial-rescale coefficients outer 0)))) (factor (* 2 (/ outer)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-half-disk-slope lw-complex-coefficientsp endp
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-polynomial-half-disk-slope-upper
  (implies (and (lw-complex-coefficientsp coefficients) (rationalp outer) (< 0 outer)
                (lw-polynomial-coefficient-caps (lw-polynomial-rescale coefficients outer 0) cap)
                (rationalp cap) (<= 0 cap))
           (<= (lw-polynomial-half-disk-slope coefficients outer) (* 4 cap (/ outer))))
  :hints (("Goal"
           :use ((:instance lw-polynomial-rescale-valid (factor outer) (offset 0))
                 (:instance lw-polynomial-max-coefficient-size-data (coefficients (cdr (lw-polynomial-rescale coefficients outer 0))))
                 (:instance lw-polynomial-max-coefficient-size-upper (coefficients (cdr (lw-polynomial-rescale coefficients outer 0))))
                 (:instance lw-reciprocal-positive (value outer))
                 (:instance lw-phds-multiply-order (a (lw-polynomial-max-coefficient-size (cdr (lw-polynomial-rescale coefficients outer 0)))) (b (* 2 cap)) (factor (* 2 (/ outer)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-half-disk-slope lw-polynomial-coefficient-caps lw-complex-coefficientsp endp
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-phds-sum-sub-constant
   (implies (and (lw-complexp constant) (lw-complexp tail))
            (equal (lw-complex-sub (lw-complex-add constant tail) constant) tail))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-sub
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-phds-polynomial-increment
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point))
            (equal (lw-complex-sub (lw-complex-polynomial coefficients point 0) (lw-complex-polynomial coefficients (cons 0 0) 0))
                   (lw-complex-mul point (lw-complex-polynomial (cdr coefficients) point 0))))
   :hints (("Goal"
            :cases ((consp coefficients))
            :use (lw-complex-polynomial-horner
                  (:instance lw-complex-polynomial-horner (point (cons 0 0)))
                  (:instance lw-complex-polynomial-rational (coefficients (cdr coefficients)) (point (cons 0 0)) (offset 0))
                  (:instance lw-complex-polynomial-rational (coefficients (cdr coefficients)) (offset 0))
                  (:instance lw-complex-mul-zero (point (lw-complex-polynomial (cdr coefficients) (cons 0 0) 0)))
                  (:instance lw-complex-ring-rational (left point) (right (lw-complex-polynomial (cdr coefficients) point 0))))
            :expand ((lw-complex-polynomial nil point 0)
                     (lw-complex-polynomial nil (cons 0 0) 0))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-phds-sum-sub-constant lw-complex-coefficientsp
              lw-complex-add-zero lw-complex-mul-zero (:executable-counterpart lw-complex-sub) endp
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-phds-half-tail-bound
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complex-diskp point 1/2))
            (lw-complex-diskp (lw-complex-polynomial coefficients point 0)
                              (* 2 (lw-polynomial-max-coefficient-size coefficients))))
   :hints (("Goal"
            :use (lw-polynomial-max-coefficient-size-data
                  (:instance lw-complex-polynomial-geometric-tail-bound
                    (cap (lw-polynomial-max-coefficient-size coefficients)) (radius 1/2) (offset 0)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-geometric-disk-gain (:executable-counterpart lw-rational-power)
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-phds-normalized-disk-data
   (implies (and (rationalp outer) (< 0 outer) (lw-complex-diskp point radius)
                 (<= radius (/ outer 2)))
            (and (lw-complexp point) (lw-complexp (lw-complex-scale (/ outer) point))
                 (lw-complex-diskp (lw-complex-scale (/ outer) point) (* radius (/ outer))) (lw-complex-diskp (lw-complex-scale (/ outer) point) 1/2)
                 (equal (lw-complex-scale outer (lw-complex-scale (/ outer) point)) point)))
   :hints (("Goal"
            :use (lw-complex-disk-data
                  (:instance lw-reciprocal-positive (value outer))
                  (:instance lw-complex-scale-disk (factor (/ outer)))
                  (:instance lw-phds-multiply-order (a radius) (b (/ outer 2)) (factor (/ outer)))
                  (:instance inverse-of-* (x outer))
                  (:instance lw-complex-scale-rational (factor (/ outer)))
                  (:instance lw-complex-disk-enlarge
                    (point (lw-complex-scale (/ outer) point)) (radius (* radius (/ outer))) (cap 1/2))
                  (:instance lw-complex-scale-compose (left outer) (right (/ outer))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-scale-one abs
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-complex-polynomial-half-disk-increment-bound
  (implies (and (lw-complex-coefficientsp coefficients) (rationalp outer) (< 0 outer)
                (lw-complex-diskp point radius) (<= radius (/ outer 2)))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-polynomial coefficients point 0) (lw-complex-polynomial coefficients (cons 0 0) 0))
            (* radius (lw-polynomial-half-disk-slope coefficients outer))))
  :hints (("Goal"
           :use (lw-phds-normalized-disk-data
                 (:instance lw-polynomial-rescale-valid (factor outer) (offset 0))
                 (:instance lw-polynomial-rescale-evaluation (factor outer) (offset 0) (point (lw-complex-scale (/ outer) point)))
                 (:instance lw-polynomial-rescale-evaluation (factor outer) (offset 0) (point (cons 0 0)))
                 (:instance lw-phds-polynomial-increment (coefficients (lw-polynomial-rescale coefficients outer 0)) (point (lw-complex-scale (/ outer) point)))
                 (:instance lw-phds-half-tail-bound (coefficients (cdr (lw-polynomial-rescale coefficients outer 0))) (point (lw-complex-scale (/ outer) point)))
                 (:instance lw-complex-mul-disk (left (lw-complex-scale (/ outer) point)) (right (lw-complex-polynomial (cdr (lw-polynomial-rescale coefficients outer 0)) (lw-complex-scale (/ outer) point) 0))
                   (radius (* radius (/ outer))) (other-radius (* 2 (lw-polynomial-max-coefficient-size (cdr (lw-polynomial-rescale coefficients outer 0)))))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-polynomial-half-disk-slope lw-complex-coefficientsp lw-complex-scale-zero endp
              lw-phds-left-commutes lw-phds-left-distributes lw-phds-fold-constants
              lw-phds-times-negative lw-phds-negative-times lw-phds-zero-times
              lw-phds-minus-one lw-phds-double-negative lw-phds-add-cancel lw-phds-double lw-phds-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
