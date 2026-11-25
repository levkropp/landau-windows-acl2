; Computed refinement of actual polynomial values along finite paths.
(in-package "ACL2")
(include-book "polynomial-edge-refinement")
(local (in-theory (disable lw-complexp lw-complex-polynomial lw-complex-coefficientsp lw-complex-segment
 lw-polynomial-edge-check lw-polynomial-edge-samples lw-ray-refine-path lw-ray-refine-polygon
 lw-ray-refinement-check lw-ray-refinement-anchors lw-ray-pointsp lw-ray-polygon-index lw-complex-positive-halfplanep)))
(local (defthm lw-ppf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ppf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ppf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ppf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ppf-times-negative (a b) (b a)))
                 :in-theory (disable lw-ppf-times-negative)))))

(local (defthm lw-ppf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ppf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ppf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ppf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ppf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ppf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ppf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ppf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ppf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ppf-left-commutes)))))
(defun lw-polynomial-path-values (coefficients points)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) nil
 (cons (lw-complex-polynomial coefficients (car points) 0)
       (lw-polynomial-path-values coefficients (cdr points)))))
(defun lw-polynomial-path-blocks (coefficients current points count)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) nil
 (cons (lw-polynomial-edge-samples coefficients current (car points) count)
       (lw-polynomial-path-blocks coefficients (car points) (cdr points) count))))
(defun lw-polynomial-path-check (coefficients current points bound radius)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) (equal points nil)
 (and (lw-polynomial-edge-check coefficients current (car points) bound radius)
      (lw-polynomial-path-check coefficients (car points) (cdr points) bound radius))))
(defun lw-polynomial-path-refinement (coefficients points count)
 (lw-ray-refine-polygon (lw-polynomial-path-values coefficients points)
 (lw-polynomial-path-blocks coefficients (car points) (cdr points) count)))
(local (in-theory (disable lw-polynomial-path-values lw-polynomial-path-blocks lw-polynomial-path-check lw-polynomial-path-refinement)))

(defthm lw-polynomial-path-values-data
 (implies (and (lw-complex-coefficientsp coefficients) (lw-ray-pointsp points))
 (lw-ray-pointsp (lw-polynomial-path-values coefficients points)))
 :hints (("Goal" :induct (lw-polynomial-path-values coefficients points)
 :in-theory (union-theories
 '(lw-polynomial-path-values lw-ray-pointsp endp lw-ppf-left-commutes lw-ppf-left-distributes lw-ppf-fold-constants lw-ppf-times-negative lw-ppf-negative-times lw-ppf-zero-times lw-ppf-minus-one lw-ppf-double-negative lw-ppf-add-cancel lw-ppf-double lw-ppf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-complex-polynomial-rational (point (car points)) (offset 0))) :do-not-induct t))))

(defthm lw-polynomial-path-refinement-check
 (implies (and (posp count) (lw-polynomial-path-check coefficients current points bound radius))
 (lw-ray-refinement-check
  (lw-complex-polynomial coefficients current 0)
  (lw-polynomial-path-values coefficients points)
  (lw-polynomial-path-blocks coefficients current points count)
  (lw-ray-refinement-anchors (lw-complex-polynomial coefficients current 0)
                             (lw-polynomial-path-values coefficients points))))
 :hints (("Goal" :induct (lw-polynomial-path-check coefficients current points bound radius)
 :in-theory (union-theories
 '(lw-polynomial-path-check lw-polynomial-path-values lw-polynomial-path-blocks lw-ray-refinement-check lw-ray-refinement-anchors lw-polynomial-edge-check endp lw-ppf-left-commutes lw-ppf-left-distributes lw-ppf-fold-constants lw-ppf-times-negative lw-ppf-negative-times lw-ppf-zero-times lw-ppf-minus-one lw-ppf-double-negative lw-ppf-add-cancel lw-ppf-double lw-ppf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-polynomial-edge-sample-halfplane (left current) (right (car points)) (parameter 0))
         (:instance lw-polynomial-edge-sample-halfplane (left current) (right (car points)) (parameter 1))
         (:instance lw-polynomial-edge-samples-halfplane (left current) (right (car points)))
         (:instance lw-complex-segment-endpoints (left current) (right (car points)))) :do-not-induct t))))

(defthm lw-polynomial-path-refinement-index
 (implies (and (posp count) (lw-ray-pointsp points)
 (lw-polynomial-path-check coefficients (car points) (cdr points) bound radius))
 (equal (lw-ray-polygon-index (lw-polynomial-path-refinement coefficients points count))
        (lw-ray-polygon-index (lw-polynomial-path-values coefficients points))))
 :hints (("Goal"
 :use ((:instance lw-polynomial-path-refinement-check (current (car points)) (points (cdr points)))
       (:instance lw-ray-refinement-polygon-index
        (points (lw-polynomial-path-values coefficients points))
        (blocks (lw-polynomial-path-blocks coefficients (car points) (cdr points) count))
        (anchors (lw-ray-refinement-anchors (lw-complex-polynomial coefficients (car points) 0)
                     (lw-polynomial-path-values coefficients (cdr points))))))
 :in-theory (union-theories
 '(lw-polynomial-path-refinement lw-polynomial-path-values lw-ray-pointsp lw-ray-refine-polygon lw-ray-polygon-index endp lw-ppf-left-commutes lw-ppf-left-distributes lw-ppf-fold-constants lw-ppf-times-negative lw-ppf-negative-times lw-ppf-zero-times lw-ppf-minus-one lw-ppf-double-negative lw-ppf-add-cancel lw-ppf-double lw-ppf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-polynomial-path-refinement-nonzero
 (implies (and (posp count) (lw-ray-pointsp points)
 (lw-polynomial-path-check coefficients (car points) (cdr points) bound radius)
 (not (equal (lw-ray-polygon-index (lw-polynomial-path-values coefficients points)) 0)))
 (not (equal (lw-ray-polygon-index (lw-polynomial-path-refinement coefficients points count)) 0)))
 :hints (("Goal" :use lw-polynomial-path-refinement-index
 :in-theory (union-theories
 '( lw-ppf-left-commutes lw-ppf-left-distributes lw-ppf-fold-constants lw-ppf-times-negative lw-ppf-negative-times lw-ppf-zero-times lw-ppf-minus-one lw-ppf-double-negative lw-ppf-add-cancel lw-ppf-double lw-ppf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
