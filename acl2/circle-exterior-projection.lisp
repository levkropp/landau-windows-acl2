(in-package "ACL2")

(include-book "polynomial-circle-reflection")
(include-book "circle-interior-count-polynomial")
(include-book "circle-exterior-coefficient-model")
(include-book "polynomial-coefficient-maps")
(include-book "pole-resolvents")
(include-book "complex-exp")

; Multiplying the complete reciprocal sum by w^(degree+1) moves the
; interior terms below the degrees used by the exterior coefficients.
(defun lw-circle-projection-interior (roots radius error)
  (lw-circle-interior-count-polynomial (lw-circle-pole-roots roots radius) radius (* radius (* 1/2 error))))

(defun lw-circle-exterior-projection (roots radius target error degree)
  (lw-polynomial-add (lw-polynomial-multiply-coefficients (cons (/ radius) 0) (lw-polynomial-circle-reflection (lw-circle-projection-interior roots radius error) degree))
                     (lw-polynomial-power-shift (lw-circle-exterior-polynomial (lw-circle-exterior-roots roots radius) radius target (* 1/2 error)) (+ 1 degree))))

(local (defthm lw-cxp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cxp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cxp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cxp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cxp-times-negative (a b) (b a)))
                 :in-theory (disable lw-cxp-times-negative)))))

(local (defthm lw-cxp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cxp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cxp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cxp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cxp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cxp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cxp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-cxp-inverse-data
   (implies (and (rationalp radius) (< 0 radius) (rationalp error) (< 0 error))
            (and (rationalp (/ radius)) (< 0 (/ radius))
                 (rationalp (* 1/2 error)) (< 0 (* 1/2 error))
                 (rationalp (* radius (* 1/2 error))) (< 0 (* radius (* 1/2 error)))
                 (equal (+ (* 1/2 error) (* 1/2 error)) error)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-reciprocal-positive lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :nonlinearp t))))

(local
 (defthm lw-cxp-real-pair
   (implies (rationalp factor) (lw-complexp (cons factor 0)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp consp lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-circle-projection-interior-valid
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)
                (rationalp error) (< 0 error))
           (lw-complex-coefficientsp (lw-circle-projection-interior roots radius error)))
  :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-projection-interior lw-circle-interior-count-polynomial-data lw-circle-selected-interior-rootsp lw-cxp-inverse-data lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-cxp-length-natural
         (natp (len coefficients))
         :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-cxp-coefficient-offset
   (implies (and (lw-complex-coefficientsp coefficients)
                 (natp target) (natp offset) (natp delta))
            (equal (lw-complex-coefficient-at coefficients (+ delta target) (+ delta offset))
                   (lw-complex-coefficient-at coefficients target offset)))
   :hints (("Goal" :induct (lw-complex-coefficient-at coefficients target offset)
                   :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-coefficient-at lw-complex-coefficientsp endp lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))
   :rule-classes nil))

(defthm lw-circle-exterior-projection-data
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)
                (not (lw-circle-boundary-root roots radius))
                (rationalp error) (< 0 error) (natp degree)
                (<= (len (lw-circle-projection-interior roots radius error)) (+ 1 degree)) (natp target))
           (and (lw-complex-coefficientsp (lw-circle-exterior-projection roots radius target error degree))
                (equal (lw-complex-coefficient-at (lw-circle-exterior-projection roots radius target error degree) (+ 1 degree target) 0)
                       (lw-circle-exterior-coefficient (lw-circle-exterior-roots roots radius) radius target))))
  :hints (("Goal"
           :use ((:instance lw-complex-coefficient-at-outside
                   (coefficients (lw-polynomial-multiply-coefficients (cons (/ radius) 0) (lw-polynomial-circle-reflection (lw-circle-projection-interior roots radius error) degree))) (target (+ 1 degree target)) (offset 0))
                 (:instance lw-cxp-coefficient-offset
                   (coefficients (lw-circle-exterior-polynomial (lw-circle-exterior-roots roots radius) radius target (* 1/2 error))) (offset 0) (delta (+ 1 degree))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-exterior-projection lw-cxp-inverse-data lw-cxp-real-pair lw-cxp-length-natural lw-circle-projection-interior-valid lw-circle-exterior-roots-data lw-circle-exterior-polynomial-valid lw-circle-exterior-polynomial-coefficient lw-polynomial-circle-reflection-data lw-polynomial-multiply-coefficients-valid lw-polynomial-power-shift-valid lw-polynomial-power-shift-coefficient lw-polynomial-add-valid lw-polynomial-add-coefficient lw-complex-coefficient-at-rational lw-complex-add-zero lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t)))

(local
 (defthm lw-cxp-real-mul
   (implies (and (lw-complexp point) (rationalp factor))
            (equal (lw-complex-mul (cons factor 0) point) (lw-complex-scale factor point)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complexp lw-complex-mul lw-complex-scale consp lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-cxp-scale-product
   (implies (and (rationalp factor) (lw-complexp a) (lw-complexp b))
            (equal (lw-complex-mul (lw-complex-scale factor a) b)
                   (lw-complex-scale factor (lw-complex-mul a b))))
   :hints (("Goal"
            :use ((:instance lw-complex-mul-scales (left factor) (right 1)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-scale-one lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-cxp-power-step
   (implies (and (lw-complexp point) (natp degree))
            (equal (lw-complex-power point (+ 1 degree))
                   (lw-complex-mul (lw-complex-power point degree) point)))
   :hints (("Goal"
            :use ((:instance lw-complex-power-add (left degree) (right 1)))
            :expand ((lw-complex-power point 1) (lw-complex-power point 0))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-mul-one lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-cxp-unit-weight
   (implies (and (lw-complexp point) (natp degree) (rationalp radius) (< 0 radius))
            (equal (lw-complex-mul (lw-complex-scale (/ radius) (lw-complex-power point degree)) (lw-complex-scale radius point)) (lw-complex-power point (+ 1 degree))))
   :hints (("Goal"
            :use ((:instance lw-complex-mul-scales
                    (left (/ radius)) (right radius)
                    (a (lw-complex-power point degree)) (b point))
                  (:instance inverse-of-* (x radius)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-scale-one lw-cxp-power-step lw-complex-power-rational lw-complex-ring-rational lw-cxp-inverse-data lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-cxp-inverse-error
   (implies (and (rationalp radius) (< 0 radius) (rationalp error))
            (equal (* error radius (/ radius)) error))
   :hints (("Goal"
            :use ((:instance inverse-of-* (x radius))
                  (:instance commutativity-of-* (x error) (y 1)))
            :in-theory (disable associativity-of-* commutativity-of-* inverse-of-*)))))

(local
 (defthm lw-cxp-mul-associate-left
   (implies (and (lw-complexp left) (lw-complexp middle) (lw-complexp right))
            (equal (lw-complex-mul left (lw-complex-mul middle right))
                   (lw-complex-mul (lw-complex-mul left middle) right)))
   :hints (("Goal" :use (lw-complex-mul-associative)
                   :in-theory (disable lw-complex-mul-associative)))))

(local
 (defthm lw-cxp-unit-powers
   (implies (and (lw-complexp point) (equal (lw-complex-norm-square point) 1) (natp index))
            (and (lw-complex-diskp point 1)
                 (lw-complex-diskp (lw-complex-power point index) 1)))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (radius 1))
                  (:instance lw-complex-power-disk (radius 1)))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-rational-power-one lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-cxp-interior-evaluation
   (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)
                (not (lw-circle-boundary-root roots radius))
                (rationalp error) (< 0 error) (natp degree)
                (<= (len (lw-circle-projection-interior roots radius error)) (+ 1 degree))
                 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (equal (lw-complex-polynomial (lw-polynomial-multiply-coefficients (cons (/ radius) 0) (lw-polynomial-circle-reflection (lw-circle-projection-interior roots radius error) degree)) point 0) (lw-complex-mul (lw-complex-scale (/ radius) (lw-complex-power point degree)) (lw-complex-conjugate (lw-complex-polynomial (lw-circle-projection-interior roots radius error) point 0)))))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-projection-interior-valid lw-cxp-real-pair lw-cxp-real-mul lw-cxp-inverse-data lw-polynomial-circle-reflection-data lw-polynomial-circle-reflection-evaluation lw-polynomial-multiply-coefficients-evaluation lw-cxp-scale-product lw-complex-power-rational lw-complex-polynomial-rational lw-complex-conjugate-rational lw-complex-ring-rational lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cxp-interior-error
   (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)
                (not (lw-circle-boundary-root roots radius))
                (rationalp error) (< 0 error) (natp degree)
                (<= (len (lw-circle-projection-interior roots radius error)) (+ 1 degree))
                 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (lw-complex-diskp (lw-complex-sub (lw-complex-mul (lw-complex-power point (+ 1 degree)) (lw-polynomial-factor-log-sum (lw-circle-pole-roots roots radius) (lw-complex-scale radius point))) (lw-complex-polynomial (lw-polynomial-multiply-coefficients (cons (/ radius) 0) (lw-polynomial-circle-reflection (lw-circle-projection-interior roots radius error) degree)) point 0)) (* 1/2 error)))
   :hints (("Goal"
            :use (lw-cxp-interior-evaluation
                  (:instance lw-circle-interior-count-polynomial-error
                    (roots (lw-circle-pole-roots roots radius)) (error (* radius (* 1/2 error))))
                  (:instance lw-cxp-unit-powers (index degree))
                  (:instance lw-complex-scale-disk
                    (factor (/ radius)) (point (lw-complex-power point degree)) (radius 1))
                  (:instance lw-complex-left-product-error
                    (factor (lw-complex-scale (/ radius) (lw-complex-power point degree))) (cap (/ radius)) (a (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum (lw-circle-pole-roots roots radius) (lw-complex-scale radius point)))) (b (lw-complex-conjugate (lw-complex-polynomial (lw-circle-projection-interior roots radius error) point 0)))
                    (error (* radius (* 1/2 error)))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-projection-interior lw-cxp-unit-weight lw-cxp-mul-associate-left lw-cxp-inverse-error abs lw-cxp-inverse-data lw-circle-interior-count-polynomial-data lw-circle-selected-interior-rootsp lw-circle-pole-split-valid lw-complex-power-rational lw-complex-scale-rational lw-polynomial-factor-log-sum-rational lw-complex-polynomial-rational lw-complex-conjugate-rational lw-complex-ring-rational lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-cxp-exterior-error
   (implies (and (lw-circle-exterior-rootsp exterior radius)
                 (natp target) (natp degree) (rationalp radius) (< 0 radius)
                 (rationalp error) (< 0 error)
                 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (lw-complex-diskp
             (lw-complex-sub
              (lw-complex-mul (lw-complex-power point (+ 1 degree)) (lw-polynomial-factor-log-sum exterior (lw-complex-scale radius point)))
              (lw-complex-polynomial (lw-polynomial-power-shift (lw-circle-exterior-polynomial exterior radius target (* 1/2 error)) (+ 1 degree)) point 0)) (* 1/2 error)))
   :hints (("Goal"
            :use ((:instance lw-cxp-unit-powers (index (+ 1 degree)))
                  (:instance lw-circle-exterior-polynomial-error (roots exterior) (error (* 1/2 error)))
                  (:instance lw-complex-left-product-error
                    (factor (lw-complex-power point (+ 1 degree))) (cap 1) (a (lw-polynomial-factor-log-sum exterior (lw-complex-scale radius point)))
                    (b (lw-complex-polynomial (lw-circle-exterior-polynomial exterior radius target (* 1/2 error)) point 0)) (error (* 1/2 error))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-cxp-inverse-data lw-polynomial-power-shift-evaluation lw-circle-exterior-polynomial-valid lw-circle-exterior-roots-typed lw-polynomial-factor-log-sum-rational lw-complex-scale-rational lw-complex-polynomial-rational lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(defthm lw-circle-exterior-projection-error
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)
                (not (lw-circle-boundary-root roots radius))
                (rationalp error) (< 0 error) (natp degree)
                (<= (len (lw-circle-projection-interior roots radius error)) (+ 1 degree)) (natp target)
                (lw-complexp point) (equal (lw-complex-norm-square point) 1))
           (lw-complex-diskp
            (lw-complex-sub (lw-complex-mul (lw-complex-power point (+ 1 degree)) (lw-polynomial-factor-log-sum roots (lw-complex-scale radius point)))
                            (lw-complex-polynomial (lw-circle-exterior-projection roots radius target error degree) point 0)) error))
  :hints (("Goal"
           :use (lw-cxp-interior-error
                 (:instance lw-cxp-exterior-error (exterior (lw-circle-exterior-roots roots radius)))
                 (:instance lw-circle-factor-log-sum-split (point (lw-complex-scale radius point)))
                 (:instance lw-complex-add-disk
                   (left (lw-complex-sub (lw-complex-mul (lw-complex-power point (+ 1 degree)) (lw-polynomial-factor-log-sum (lw-circle-pole-roots roots radius) (lw-complex-scale radius point))) (lw-complex-polynomial (lw-polynomial-multiply-coefficients (cons (/ radius) 0) (lw-polynomial-circle-reflection (lw-circle-projection-interior roots radius error) degree)) point 0)))
                   (right (lw-complex-sub (lw-complex-mul (lw-complex-power point (+ 1 degree)) (lw-polynomial-factor-log-sum (lw-circle-exterior-roots roots radius) (lw-complex-scale radius point))) (lw-complex-polynomial (lw-polynomial-power-shift (lw-circle-exterior-polynomial (lw-circle-exterior-roots roots radius) radius target (* 1/2 error)) (+ 1 degree)) point 0)))
                   (radius (* 1/2 error)) (other-radius (* 1/2 error))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-circle-exterior-projection lw-cxp-inverse-data lw-cxp-real-pair lw-circle-projection-interior-valid lw-circle-exterior-roots-data lw-circle-pole-split-valid lw-circle-exterior-polynomial-valid lw-polynomial-circle-reflection-data lw-polynomial-multiply-coefficients-valid lw-polynomial-power-shift-valid lw-polynomial-add-evaluation lw-complex-sub-add lw-complex-mul-distribute lw-complex-power-rational lw-complex-scale-rational lw-complex-polynomial-rational lw-complex-ring-rational lw-polynomial-factor-log-sum-rational lw-cxp-left-commutes lw-cxp-left-distributes lw-cxp-fold-constants lw-cxp-times-negative lw-cxp-negative-times lw-cxp-zero-times lw-cxp-minus-one lw-cxp-double-negative lw-cxp-add-cancel lw-cxp-double lw-cxp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
