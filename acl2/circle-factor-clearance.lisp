(in-package "ACL2")

(include-book "circle-radial-clearance")
(include-book "polynomial-factor-coefficients")
(include-book "polynomial-leading-radius")

; One annular gap bounds the distance to every factor on the selected circle.
; The product bound includes the leading coefficient and counts repeated factors.

(local (defthm lw-cfc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cfc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cfc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cfc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cfc-times-negative (a b) (b a)))
                 :in-theory (disable lw-cfc-times-negative)))))

(local (defthm lw-cfc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cfc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cfc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cfc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cfc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cfc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cfc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cfc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-circle-factor-lower (roots leading distance)
  (declare (xargs :measure (acl2-count roots)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp roots)
      (lw-complex-nonzero-lower leading)
    (* distance (lw-circle-factor-lower (cdr roots) leading distance))))

(local
 (defthm lw-cfc-product-bound
   (implies (and (rationalp a) (rationalp b) (rationalp left) (rationalp right)
                 (< 0 a) (< 0 b)
                 (<= (* a a) left) (<= (* b b) right))
            (and (< 0 (* a b))
                 (<= (* (* a b) (* a b)) (* left right))))
   :hints (("Goal"
            :use (lw-cfc-positive-product
                  (:instance lw-cfc-multiply-order (a (* a a)) (b left) (factor (* b b)))
                  (:instance lw-cfc-multiply-order (a (* b b)) (b right) (factor left)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfc-left-commutes lw-cfc-left-distributes lw-cfc-fold-constants
              lw-cfc-times-negative lw-cfc-negative-times lw-cfc-zero-times
              lw-cfc-minus-one lw-cfc-double-negative lw-cfc-add-cancel lw-cfc-double lw-cfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-cfc-factor-bound
   (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                 (not (equal leading (cons 0 0))) (lw-complexp point)
                 (rationalp radius) (< 0 radius)
                 (rationalp gap) (< 0 gap)
                 (equal (lw-complex-norm-square point) (* radius radius))
                 (lw-circle-radial-bracket-clear roots radius radius gap))
            (let ((lower (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap))))
              (and (rationalp lower) (< 0 lower)
                   (<= (* lower lower)
                       (lw-complex-norm-square (lw-polynomial-linear-factor-value roots leading point))))))
   :hints (("Goal"
            :induct (lw-polynomial-linear-factor-value roots leading point)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              (:induction lw-polynomial-linear-factor-value)
              lw-circle-factor-lower lw-circle-radial-bracket-clear
              lw-polynomial-linear-factor-value lw-polynomial-linear-factor-value-rational
              lw-ray-pointsp lw-complex-ring-rational endp
              lw-cfc-left-commutes lw-cfc-left-distributes lw-cfc-fold-constants
              lw-cfc-times-negative lw-cfc-negative-times lw-cfc-zero-times
              lw-cfc-minus-one lw-cfc-double-negative lw-cfc-add-cancel lw-cfc-double lw-cfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-nonzero-lower-valid (point leading))
                        (:instance lw-circle-radial-clearance-valid (root (car roots)))
                        (:instance lw-complex-norm-square-valid (point (lw-complex-sub point (car roots))))
                        (:instance lw-complex-norm-square-valid (point (lw-polynomial-linear-factor-value (cdr roots) leading point)))
                        (:instance lw-complex-norm-square-product
                          (left (lw-complex-sub point (car roots)))
                          (right (lw-polynomial-linear-factor-value (cdr roots) leading point)))
                        (:instance lw-cfc-product-bound
                          (a (lw-circle-radial-clearance radius gap))
                          (b (lw-circle-factor-lower (cdr roots) leading (lw-circle-radial-clearance radius gap)))
                          (left (lw-complex-norm-square (lw-complex-sub point (car roots))))
                          (right (lw-complex-norm-square (lw-polynomial-linear-factor-value (cdr roots) leading point)))))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-circle-factor-coefficients-clearance
  (implies (and (lw-ray-pointsp roots) (lw-complexp leading)
                (not (equal leading (cons 0 0))) (lw-complexp point)
                (rationalp radius) (< 0 radius)
                (rationalp gap) (< 0 gap)
                (equal (lw-complex-norm-square point) (* radius radius))
                (lw-circle-radial-bracket-clear roots radius radius gap))
           (let ((lower (lw-circle-factor-lower roots leading (lw-circle-radial-clearance radius gap))))
             (and (rationalp lower) (< 0 lower)
                  (<= (* lower lower)
                      (lw-complex-norm-square
                       (lw-complex-polynomial (lw-polynomial-factor-coefficients roots leading) point 0))))))
  :hints (("Goal" :use (lw-cfc-factor-bound lw-polynomial-factor-coefficients-evaluation)
                  :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfc-left-commutes lw-cfc-left-distributes lw-cfc-fold-constants
              lw-cfc-times-negative lw-cfc-negative-times lw-cfc-zero-times
              lw-cfc-minus-one lw-cfc-double-negative lw-cfc-add-cancel lw-cfc-double lw-cfc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                  :do-not-induct t))
  :rule-classes nil)
