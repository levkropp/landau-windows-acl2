(in-package "ACL2")

(include-book "polygon-products")
(include-book "grid-index")

; Positive half-plane checks on the triangular part of a product grid.
; They imply exact zero triangle and strip indices; no index equality
; is an input to the checker.

(local (defthm lw-ppc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppc-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppc-times-negative)))))

(local (defthm lw-ppc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppc-left-commutes)))))

(local (defthm lw-ppc-dot-det-identity
 (implies (and (lw-complexp h) (lw-complexp a) (lw-complexp b))
  (equal (* (lw-complex-norm-square a) (lw-complex-dot h b))
         (+ (* (lw-complex-dot a b) (lw-complex-dot h a))
            (* (lw-complex-det a b) (lw-complex-det a h)))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complexp lw-complex-dot lw-complex-det lw-complex-norm-square lw-ppc-left-commutes lw-ppc-left-distributes lw-ppc-fold-constants lw-ppc-times-negative lw-ppc-negative-times lw-ppc-zero-times lw-ppc-minus-one lw-ppc-double-negative lw-ppc-add-cancel lw-ppc-double lw-ppc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppc-positive-dot-nonzero
 (implies (and (lw-complexp h) (lw-complexp a) (< 0 (lw-complex-dot h a)))
          (not (equal a (cons 0 0))))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-complex-dot lw-ppc-left-commutes lw-ppc-left-distributes lw-ppc-fold-constants lw-ppc-times-negative lw-ppc-negative-times lw-ppc-zero-times lw-ppc-minus-one lw-ppc-double-negative lw-ppc-add-cancel lw-ppc-double lw-ppc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-halfplane-safe-edge
 (implies (and (lw-complex-positive-halfplanep h a) (lw-complex-positive-halfplanep h b))
  (lw-ray-safe-edgep a b))
 :hints (("Goal"
  :use (lw-ppc-dot-det-identity lw-ppc-positive-dot-nonzero
        lw-complex-orientation-rational
        (:instance lw-complex-orientation-rational (a h))
        (:instance lw-complex-orientation-rational (a h) (b a))
        (:instance lw-complex-norm-square-positive (point a))
        (:instance lw-complex-norm-square-valid (point a))
        (:instance lw-ppc-positive-product
          (a (lw-complex-norm-square a)) (b (lw-complex-dot h b))))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-safe-edgep lw-complex-positive-halfplanep lw-ppc-left-commutes lw-ppc-left-distributes lw-ppc-fold-constants lw-ppc-times-negative lw-ppc-negative-times lw-ppc-zero-times lw-ppc-minus-one lw-ppc-double-negative lw-ppc-add-cancel lw-ppc-double lw-ppc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
  :cases ((equal (lw-complex-det a b) 0)) :nonlinearp t)))

(defun lw-ray-product-strip-check (points lower upper)
 (if (or (endp points) (endp (cdr points))) t
  (let ((anchor (lw-complex-mul lower (car points))))
   (and (lw-complex-positive-halfplanep anchor anchor)
        (lw-complex-positive-halfplanep anchor (lw-complex-mul lower (cadr points)))
        (lw-complex-positive-halfplanep anchor (lw-complex-mul upper (cadr points)))
        (lw-complex-positive-halfplanep anchor (lw-complex-mul upper (car points)))
        (lw-ray-product-strip-check (cdr points) lower upper)))))

(defun lw-ray-product-path-check (left right)
 (if (or (endp left) (endp (cdr left))) t
  (and (lw-ray-product-strip-check left (car right) (cadr right))
       (lw-ray-product-path-check (cdr left) (cdr right)))))

(defthm lw-ray-product-strip-check-tail
 (implies (lw-ray-product-strip-check points lower upper)
          (lw-ray-product-strip-check (cdr points) lower upper))
 :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-product-strip-check lw-ppc-left-commutes lw-ppc-left-distributes lw-ppc-fold-constants lw-ppc-times-negative lw-ppc-negative-times lw-ppc-zero-times lw-ppc-minus-one lw-ppc-double-negative lw-ppc-add-cancel lw-ppc-double lw-ppc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-product-check-first-triangle
 (implies (and (consp points) (consp (cdr points))
               (lw-ray-product-strip-check points lower upper))
  (equal
   (lw-ray-triangle-index (lw-complex-mul lower (car points))
                          (lw-complex-mul lower (cadr points))
                          (lw-complex-mul upper (cadr points))) 0))
 :hints (("Goal"
  :use ((:instance lw-ray-triangle-halfplane-zero
    (h (lw-complex-mul lower (car points))) (a (lw-complex-mul lower (car points)))
    (b (lw-complex-mul lower (cadr points))) (c (lw-complex-mul upper (cadr points)))))
  :expand ((lw-ray-product-strip-check points lower upper))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppc-left-commutes lw-ppc-left-distributes lw-ppc-fold-constants lw-ppc-times-negative lw-ppc-negative-times lw-ppc-zero-times lw-ppc-minus-one lw-ppc-double-negative lw-ppc-add-cancel lw-ppc-double lw-ppc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local (defthm lw-ppc-first-quadrilateral
 (implies (and (consp points) (consp (cdr points))
               (lw-ray-product-strip-check points lower upper))
  (equal
   (lw-ray-quadrilateral-index (lw-complex-mul lower (car points))
                               (lw-complex-mul lower (cadr points))
                               (lw-complex-mul upper (cadr points))
                               (lw-complex-mul upper (car points))) 0))
 :hints (("Goal"
  :use ((:instance lw-ray-quadrilateral-halfplane-zero
    (h (lw-complex-mul lower (car points))) (a (lw-complex-mul lower (car points)))
    (b (lw-complex-mul lower (cadr points))) (c (lw-complex-mul upper (cadr points)))
    (d (lw-complex-mul upper (car points)))))
  :expand ((lw-ray-product-strip-check points lower upper))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppc-left-commutes lw-ppc-left-distributes lw-ppc-fold-constants lw-ppc-times-negative lw-ppc-negative-times lw-ppc-zero-times lw-ppc-minus-one lw-ppc-double-negative lw-ppc-add-cancel lw-ppc-double lw-ppc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-ppc-map-head
 (implies (consp points)
  (and (consp (lw-ray-multiply-points factor points))
       (equal (car (lw-ray-multiply-points factor points)) (lw-complex-mul factor (car points)))
       (equal (cdr (lw-ray-multiply-points factor points)) (lw-ray-multiply-points factor (cdr points)))))
 :hints (("Goal" :expand ((lw-ray-multiply-points factor points))
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ppc-left-commutes lw-ppc-left-distributes lw-ppc-fold-constants lw-ppc-times-negative lw-ppc-negative-times lw-ppc-zero-times lw-ppc-minus-one lw-ppc-double-negative lw-ppc-add-cancel lw-ppc-double lw-ppc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-product-check-strip-zero
 (implies (lw-ray-product-strip-check points lower upper)
  (equal
   (lw-ray-row-strip-index (lw-ray-multiply-points lower points)
                           (lw-ray-multiply-points upper points)) 0))
 :hints (("Goal" :induct (lw-ray-product-strip-check points lower upper)
          :in-theory (union-theories
 '(fold-consts-in-+ lw-ray-product-strip-check lw-ray-multiply-points lw-ray-row-strip-index lw-ppc-map-head lw-ppc-first-quadrilateral lw-ppc-left-commutes lw-ppc-left-distributes lw-ppc-fold-constants lw-ppc-times-negative lw-ppc-negative-times lw-ppc-zero-times lw-ppc-minus-one lw-ppc-double-negative lw-ppc-add-cancel lw-ppc-double lw-ppc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-product-check-diagonal-edge
 (implies (and (consp left) (consp (cdr left))
               (lw-ray-product-path-check left right))
  (lw-ray-safe-edgep
   (lw-complex-mul (car right) (car left))
   (lw-complex-mul (cadr right) (cadr left))))
 :hints (("Goal"
  :use ((:instance lw-ray-halfplane-safe-edge
          (h (lw-complex-mul (car right) (car left)))
          (a (lw-complex-mul (car right) (car left)))
          (b (lw-complex-mul (cadr right) (cadr left)))))
  :expand ((lw-ray-product-path-check left right)
           (lw-ray-product-strip-check left (car right) (cadr right)))
  :in-theory (union-theories
 '(fold-consts-in-+ lw-ppc-left-commutes lw-ppc-left-distributes lw-ppc-fold-constants lw-ppc-times-negative lw-ppc-negative-times lw-ppc-zero-times lw-ppc-minus-one lw-ppc-double-negative lw-ppc-add-cancel lw-ppc-double lw-ppc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

