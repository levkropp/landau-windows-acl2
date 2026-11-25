; Exact box geometry for computed square covers and rational circles.
(in-package "ACL2")
(include-book "polynomial-sublevel-cover")
(include-book "box-circles")
(local (in-theory (disable lw-polynomial-grid-point lw-polynomial-grid-step
 lw-square-cell-containsp lw-square-cover-containsp lw-square-address-listp
 lw-complexp lw-plane-pointp lw-boxp lw-box-contains lw-distance-box lw-distance-squared
 lw-point-in-boxes)))
(local (defthm lw-scc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-scc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-scc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-scc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-scc-times-negative (a b) (b a)))
                 :in-theory (disable lw-scc-times-negative)))))

(local (defthm lw-scc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-scc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-scc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-scc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-scc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-scc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-scc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-scc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-scc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-scc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-scc-left-commutes)))))
(defun lw-square-cell-box (anchor side count row column)
 (let ((base (lw-polynomial-grid-point anchor side count row column))
       (step (lw-polynomial-grid-step side count)))
 (list (car base) (+ (car base) step) (cdr base) (+ (cdr base) step))))
(defun lw-square-cover-boxes (anchor side count addresses)
 (if (endp addresses) nil
 (cons (lw-square-cell-box anchor side count (caar addresses) (cdar addresses))
       (lw-square-cover-boxes anchor side count (cdr addresses)))))
(defun lw-box-avoids-circlep (sigma height radius-square box)
 (and (lw-boxp box)
      (or (< (cdr (lw-distance-box sigma height box)) radius-square)
          (< radius-square (car (lw-distance-box sigma height box))))))
(defun lw-boxes-avoid-circlep (sigma height radius-square boxes)
 (if (endp boxes) (equal boxes nil)
 (and (lw-box-avoids-circlep sigma height radius-square (car boxes))
      (lw-boxes-avoid-circlep sigma height radius-square (cdr boxes)))))
(local (in-theory (disable lw-square-cell-box lw-square-cover-boxes
 lw-box-avoids-circlep lw-boxes-avoid-circlep)))

(defthm lw-square-cell-box-valid
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (posp count)
               (natp row) (< row count) (natp column) (< column count))
 (lw-boxp (lw-square-cell-box anchor side count row column)))
 :hints (("Goal" :use (lw-polynomial-grid-step-data lw-polynomial-grid-point-rational)
 :in-theory (union-theories
 '(lw-square-cell-box lw-boxp lw-intervalp lw-complexp cons lw-scc-left-commutes lw-scc-left-distributes lw-scc-fold-constants lw-scc-times-negative lw-scc-negative-times lw-scc-zero-times lw-scc-minus-one lw-scc-double-negative lw-scc-add-cancel lw-scc-double lw-scc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-square-cell-box-contains
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (posp count)
               (natp row) (< row count) (natp column) (< column count))
 (equal (lw-box-contains (lw-square-cell-box anchor side count row column) point)
        (lw-square-cell-containsp anchor side count row column point)))
 :hints (("Goal" :use (lw-square-cell-box-valid)
 :in-theory (union-theories
 '(lw-box-contains lw-boxp lw-square-cell-containsp lw-square-cell-box lw-contains lw-plane-pointp lw-complexp cons lw-scc-left-commutes lw-scc-left-distributes lw-scc-fold-constants lw-scc-times-negative lw-scc-negative-times lw-scc-zero-times lw-scc-minus-one lw-scc-double-negative lw-scc-add-cancel lw-scc-double lw-scc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-square-cover-boxes-contains
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (posp count)
               (lw-square-address-listp addresses count))
 (equal (lw-point-in-boxes point (lw-square-cover-boxes anchor side count addresses))
        (lw-square-cover-containsp anchor side count point addresses)))
 :hints (("Goal" :induct (lw-square-cover-boxes anchor side count addresses)
 :in-theory (union-theories
 '(lw-square-cover-boxes lw-square-address-listp lw-point-in-boxes lw-square-cover-containsp lw-square-cell-box-contains lw-scc-left-commutes lw-scc-left-distributes lw-scc-fold-constants lw-scc-times-negative lw-scc-negative-times lw-scc-zero-times lw-scc-minus-one lw-scc-double-negative lw-scc-add-cancel lw-scc-double lw-scc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-box-avoids-circle-sound
 (implies (and (rationalp sigma) (rationalp height)
               (lw-box-avoids-circlep sigma height radius-square box)
               (equal (lw-distance-squared sigma height point) radius-square))
 (not (lw-box-contains box point)))
 :hints (("Goal" :use (lw-distance-box-sound)
 :in-theory (union-theories
 '(lw-box-avoids-circlep lw-contains lw-scc-left-commutes lw-scc-left-distributes lw-scc-fold-constants lw-scc-times-negative lw-scc-negative-times lw-scc-zero-times lw-scc-minus-one lw-scc-double-negative lw-scc-add-cancel lw-scc-double lw-scc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-boxes-avoid-circle-sound
 (implies (and (rationalp sigma) (rationalp height)
               (lw-boxes-avoid-circlep sigma height radius-square boxes)
               (equal (lw-distance-squared sigma height point) radius-square))
 (not (lw-point-in-boxes point boxes)))
 :hints (("Goal" :induct (lw-boxes-avoid-circlep sigma height radius-square boxes)
 :in-theory (union-theories
 '(lw-boxes-avoid-circlep lw-point-in-boxes lw-box-avoids-circle-sound lw-scc-left-commutes lw-scc-left-distributes lw-scc-fold-constants lw-scc-times-negative lw-scc-negative-times lw-scc-zero-times lw-scc-minus-one lw-scc-double-negative lw-scc-add-cancel lw-scc-double lw-scc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-square-cover-avoids-circle
 (implies (and (lw-complexp anchor) (rationalp side) (< 0 side) (posp count)
               (lw-square-address-listp addresses count)
               (rationalp sigma) (rationalp height)
               (lw-boxes-avoid-circlep sigma height radius-square
                  (lw-square-cover-boxes anchor side count addresses))
               (equal (lw-distance-squared sigma height point) radius-square))
 (not (lw-square-cover-containsp anchor side count point addresses)))
 :hints (("Goal"
 :use (lw-square-cover-boxes-contains
       (:instance lw-boxes-avoid-circle-sound
        (boxes (lw-square-cover-boxes anchor side count addresses))))
 :in-theory (union-theories
 '( lw-scc-left-commutes lw-scc-left-distributes lw-scc-fold-constants lw-scc-times-negative lw-scc-negative-times lw-scc-zero-times lw-scc-minus-one lw-scc-double-negative lw-scc-add-cancel lw-scc-double lw-scc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

