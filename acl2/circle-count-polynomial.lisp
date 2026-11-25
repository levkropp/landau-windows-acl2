(in-package "ACL2")

(include-book "circle-interior-count-polynomial")
(include-book "circle-exterior-coefficient-model")
(include-book "polynomial-affine")
(include-book "pole-resolvents")

; Multiplying the exterior sum by radius times the unit contour point
; shifts its polynomial by one degree, so it contributes zero to the count.
(defun lw-circle-count-weighted-exterior (exterior radius error)
  (lw-polynomial-multiply-linear (cons 0 0) (cons radius 0)
    (lw-circle-exterior-polynomial exterior radius 0 (* (/ radius) error))))

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul
                 lw-complex-scale lw-complex-diskp lw-complex-polynomial
                 lw-complex-coefficient-at lw-complex-coefficientsp
                 lw-polynomial-multiply-linear lw-polynomial-add
                 lw-circle-exterior-polynomial lw-circle-interior-count-polynomial
                 lw-circle-boundary-root lw-circle-pole-roots lw-circle-exterior-roots
                 lw-polynomial-factor-log-sum lw-circle-factor-log-sum-split)))

(local (defthm lw-ccp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ccp-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ccp-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ccp-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ccp-times-negative (a b) (b a)))
                 :in-theory (disable lw-ccp-times-negative)))))

(local (defthm lw-ccp-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ccp-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ccp-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ccp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ccp-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ccp-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ccp-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ccp-half-data
  (implies (and (rationalp error) (< 0 error))
           (and (rationalp (* 1/2 error)) (< 0 (* 1/2 error))
                (equal (+ (* 1/2 error) (* 1/2 error)) error)))))

(local
 (defthm lw-ccp-division
   (implies (and (rationalp radius) (< 0 radius) (rationalp error) (< 0 error))
            (and (< 0 (* (/ radius) error))
                 (equal (* radius (* (/ radius) error)) error)))
   :hints (("Goal" :use ((:instance associativity-of-* (x radius) (y (/ radius)) (z error)))
                   :in-theory (disable associativity-of-* commutativity-of-*)
                   :nonlinearp t))))

(local
 (defthm lw-ccp-real-inline
   (implies (rationalp radius) (lw-complexp (cons radius 0)))
   :hints (("Goal" :in-theory (enable lw-complexp)))))

(local
 (defthm lw-ccp-real-weight
   (implies (and (rationalp radius) (lw-complexp point))
            (equal (lw-complex-add (cons 0 0) (lw-complex-mul (cons radius 0) point))
                   (lw-complex-scale radius point)))
   :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-mul lw-complex-scale)))))

(local
 (defthm lw-ccp-linear-zero-head
   (implies (and (consp coefficients) (lw-complex-coefficientsp coefficients))
            (and (consp (lw-polynomial-multiply-linear (cons 0 0) slope coefficients))
                 (equal (car (lw-polynomial-multiply-linear (cons 0 0) slope coefficients))
                        (cons 0 0))))
   :hints (("Goal" :expand ((lw-polynomial-multiply-linear (cons 0 0) slope coefficients))
                   :in-theory (e/d (lw-complex-coefficientsp lw-complex-scale)
                                   (lw-polynomial-add-constant))))))

(local
 (defthm lw-ccp-linear-zero-constant
   (implies (and (lw-complexp slope) (lw-complex-coefficientsp coefficients))
            (equal (lw-complex-coefficient-at
                    (lw-polynomial-multiply-linear (cons 0 0) slope coefficients) 0 0)
                   (cons 0 0)))
   :hints (("Goal" :cases ((consp coefficients))
                   :use ((:instance lw-complex-coefficient-at-nth
                           (coefficients (lw-polynomial-multiply-linear (cons 0 0) slope coefficients))
                           (target 0) (offset 0)))
                   :in-theory (e/d (lw-complex-coefficientsp)
                                   (lw-complex-coefficient-at-nth)))
           ("Subgoal 2" :in-theory (enable lw-polynomial-multiply-linear lw-complex-coefficient-at)))))

(local
 (defthm lw-ccp-exterior-data
   (implies (and (lw-circle-exterior-rootsp exterior radius)
                 (rationalp radius) (< 0 radius) (rationalp error) (< 0 error))
            (and (lw-complex-coefficientsp (lw-circle-count-weighted-exterior exterior radius error))
                 (equal (lw-complex-coefficient-at (lw-circle-count-weighted-exterior exterior radius error) 0 0) (cons 0 0))))
   :hints (("Goal"  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-count-weighted-exterior lw-ccp-division lw-ccp-real-inline lw-ccp-linear-zero-constant lw-polynomial-multiply-linear-valid lw-circle-exterior-polynomial-valid lw-ccp-left-commutes lw-ccp-left-distributes lw-ccp-fold-constants lw-ccp-times-negative lw-ccp-negative-times lw-ccp-zero-times lw-ccp-minus-one lw-ccp-double-negative lw-ccp-add-cancel lw-ccp-double lw-ccp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ccp-exterior-eval
   (implies (and (lw-circle-exterior-rootsp exterior radius)
                 (rationalp radius) (< 0 radius) (rationalp error) (< 0 error)
                 (lw-complexp point))
            (equal (lw-complex-polynomial (lw-circle-count-weighted-exterior exterior radius error) point 0)
                   (lw-complex-mul (lw-complex-scale radius point) (lw-complex-polynomial (lw-circle-exterior-polynomial exterior radius 0 (* (/ radius) error)) point 0))))
   :hints (("Goal"  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-count-weighted-exterior lw-ccp-division lw-ccp-real-inline lw-ccp-real-weight lw-polynomial-multiply-linear-evaluation lw-circle-exterior-polynomial-valid lw-ccp-left-commutes lw-ccp-left-distributes lw-ccp-fold-constants lw-ccp-times-negative lw-ccp-negative-times lw-ccp-zero-times lw-ccp-minus-one lw-ccp-double-negative lw-ccp-add-cancel lw-ccp-double lw-ccp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local (defthm lw-ccp-times-one
         (implies (rationalp value) (equal (* value 1) value))))

(local
 (defthm lw-ccp-exterior-error
   (implies (and (lw-circle-exterior-rootsp exterior radius)
                 (rationalp radius) (< 0 radius) (rationalp error) (< 0 error)
                 (lw-complexp point) (equal (lw-complex-norm-square point) 1))
            (lw-complex-diskp (lw-complex-sub (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum exterior (lw-complex-scale radius point))) (lw-complex-polynomial (lw-circle-count-weighted-exterior exterior radius error) point 0))
                              error))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-norm-square (radius 1))
                  (:instance lw-complex-scale-disk (factor radius) (radius 1))
                  (:instance lw-circle-exterior-polynomial-error
                    (roots exterior) (target 0) (error (* (/ radius) error)))
                  (:instance lw-complex-left-product-error
                    (factor (lw-complex-scale radius point)) (cap radius)
                    (a (lw-polynomial-factor-log-sum exterior (lw-complex-scale radius point)))
                    (b (lw-complex-polynomial (lw-circle-exterior-polynomial exterior radius 0 (* (/ radius) error)) point 0)) (error (* (/ radius) error))))
             :in-theory (union-theories
 '(fold-consts-in-+ abs lw-ccp-times-one lw-ccp-exterior-eval lw-ccp-division lw-complex-polynomial-rational lw-circle-exterior-polynomial-valid lw-circle-exterior-roots-typed lw-polynomial-factor-log-sum-rational lw-complex-scale-rational lw-ccp-left-distributes lw-ccp-fold-constants lw-ccp-times-negative lw-ccp-negative-times lw-ccp-zero-times lw-ccp-minus-one lw-ccp-double-negative lw-ccp-add-cancel lw-ccp-double lw-ccp-add-double
 natp posp zp fix car-cons cdr-cons associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(defun lw-circle-count-polynomial (roots radius error)
  (lw-polynomial-add (lw-circle-interior-count-polynomial (lw-circle-pole-roots roots radius) radius (* 1/2 error)) (lw-circle-count-weighted-exterior (lw-circle-exterior-roots roots radius) radius (* 1/2 error))))

(local
 (defthm lw-ccp-length-natural
   (natp (len roots))
   :rule-classes (:rewrite :type-prescription)))

(defthm lw-circle-count-polynomial-data
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)
                (not (lw-circle-boundary-root roots radius)) (rationalp error) (< 0 error))
           (and (lw-complex-coefficientsp (lw-circle-count-polynomial roots radius error))
                (equal (lw-complex-coefficient-at (lw-circle-count-polynomial roots radius error) 0 0)
                       (cons (len (lw-circle-pole-roots roots radius)) 0))))
  :hints (("Goal"  :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-count-polynomial lw-ccp-half-data lw-ccp-length-natural lw-circle-interior-count-polynomial-data lw-circle-selected-interior-rootsp lw-circle-exterior-roots-data lw-ccp-exterior-data lw-polynomial-add-valid lw-polynomial-add-coefficient lw-complex-add-zero lw-ccp-real-inline lw-ccp-left-commutes lw-ccp-left-distributes lw-ccp-fold-constants lw-ccp-times-negative lw-ccp-negative-times lw-ccp-zero-times lw-ccp-minus-one lw-ccp-double-negative lw-ccp-add-cancel lw-ccp-double lw-ccp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t)))

(local
 (defthm lw-ccp-real-add-error
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
                 (rationalp left-error) (rationalp right-error)
                 (lw-complex-diskp (lw-complex-sub a (lw-complex-conjugate c)) left-error)
                 (lw-complex-diskp (lw-complex-sub b d) right-error))
            (<= (abs (- (car (lw-complex-add a b)) (car (lw-complex-add c d))))
                (+ left-error right-error)))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-coordinates
                    (point (lw-complex-sub a (lw-complex-conjugate c))) (radius left-error))
                  (:instance lw-complex-disk-coordinates (point (lw-complex-sub b d)) (radius right-error)))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-add lw-complex-sub lw-complex-conjugate abs consp lw-ccp-left-commutes lw-ccp-left-distributes lw-ccp-fold-constants lw-ccp-times-negative lw-ccp-negative-times lw-ccp-zero-times lw-ccp-minus-one lw-ccp-double-negative lw-ccp-add-cancel lw-ccp-double lw-ccp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-circle-count-polynomial-error
  (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius)
                (not (lw-circle-boundary-root roots radius)) (rationalp error) (< 0 error)
                (lw-complexp point) (equal (lw-complex-norm-square point) 1))
           (<= (abs (- (car (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum roots (lw-complex-scale radius point))))
                       (car (lw-complex-polynomial (lw-circle-count-polynomial roots radius error) point 0))))
               error))
  :hints (("Goal"
           :use ((:instance lw-circle-factor-log-sum-split (point (lw-complex-scale radius point)))
                 (:instance lw-circle-interior-count-polynomial-error (roots (lw-circle-pole-roots roots radius)) (error (* 1/2 error)))
                 (:instance lw-ccp-exterior-error (exterior (lw-circle-exterior-roots roots radius)) (error (* 1/2 error)))
                 (:instance lw-ccp-real-add-error
                   (a (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum (lw-circle-pole-roots roots radius) (lw-complex-scale radius point)))) (b (lw-complex-mul (lw-complex-scale radius point) (lw-polynomial-factor-log-sum (lw-circle-exterior-roots roots radius) (lw-complex-scale radius point)))) (c (lw-complex-polynomial (lw-circle-interior-count-polynomial (lw-circle-pole-roots roots radius) radius (* 1/2 error)) point 0)) (d (lw-complex-polynomial (lw-circle-count-weighted-exterior (lw-circle-exterior-roots roots radius) radius (* 1/2 error)) point 0))
                   (left-error (* 1/2 error)) (right-error (* 1/2 error))))
            :in-theory (union-theories
 '(fold-consts-in-+ lw-circle-count-polynomial lw-ccp-half-data lw-circle-interior-count-polynomial-data lw-circle-selected-interior-rootsp lw-circle-exterior-roots-data lw-circle-pole-split-valid lw-ccp-exterior-data lw-polynomial-add-evaluation lw-complex-scale-rational lw-complex-mul-distribute lw-polynomial-factor-log-sum-rational lw-complex-ring-rational lw-complex-polynomial-rational lw-ccp-left-commutes lw-ccp-left-distributes lw-ccp-fold-constants lw-ccp-times-negative lw-ccp-negative-times lw-ccp-zero-times lw-ccp-minus-one lw-ccp-double-negative lw-ccp-add-cancel lw-ccp-double lw-ccp-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))
  :rule-classes nil)
