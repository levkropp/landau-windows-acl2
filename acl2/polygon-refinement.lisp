; Certified replacement of polygon edges by finite rational chains.
(in-package "ACL2")
(include-book "polygon-index")
(local (in-theory (disable lw-complexp lw-complex-det lw-complex-dot
 lw-complex-positive-halfplanep lw-ray-crossing lw-ray-triangle-index
 lw-ray-path-index lw-ray-path-last lw-ray-polygon-index
 lw-ray-pointsp lw-ray-halfplane-points)))
(local (defthm lw-prf-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-prf-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-prf-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-prf-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-prf-times-negative (a b) (b a)))
                 :in-theory (disable lw-prf-times-negative)))))

(local (defthm lw-prf-zero-times (equal (* 0 a) 0)))

(local (defthm lw-prf-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-prf-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-prf-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-prf-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-prf-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-prf-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-prf-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-prf-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-prf-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-prf-left-commutes)))))
(defun lw-ray-refine-path (current points blocks)
 (declare (ignore current) (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) nil
 (append (car blocks)
 (cons (car points) (lw-ray-refine-path (car points) (cdr points) (cdr blocks))))))
(defun lw-ray-refinement-check (current points blocks anchors)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) (and (equal points nil) (equal blocks nil) (equal anchors nil))
 (and (consp blocks) (consp anchors)
      (lw-complex-positive-halfplanep (car anchors) current)
      (lw-complex-positive-halfplanep (car anchors) (car points))
      (lw-ray-halfplane-points (car anchors) (car blocks))
      (lw-ray-refinement-check (car points) (cdr points) (cdr blocks) (cdr anchors)))))
(defun lw-ray-refine-polygon (points blocks)
 (if (endp points) nil
 (cons (car points) (lw-ray-refine-path (car points) (cdr points) blocks))))
(local (in-theory (disable lw-ray-refine-path lw-ray-refinement-check lw-ray-refine-polygon)))

(defthm lw-ray-halfplane-chain-replacement
 (implies (and (lw-complex-positive-halfplanep h current)
               (lw-complex-positive-halfplanep h next)
               (lw-ray-halfplane-points h points))
 (equal (+ (lw-ray-path-index current points)
           (lw-ray-crossing (lw-ray-path-last current points) next))
        (lw-ray-crossing current next)))
 :hints (("Goal"
 :use (lw-ray-path-halfplane-potential
       lw-ray-path-last-halfplane
       (:instance lw-ray-halfplane-potential (a (lw-ray-path-last current points)) (b next))
       (:instance lw-ray-halfplane-potential (a current) (b next))
       (:instance lw-ray-crossing-data (a h) (b current))
       (:instance lw-ray-crossing-data (a h) (b next))
       (:instance lw-ray-crossing-data (a h) (b (lw-ray-path-last current points))))
 :in-theory (union-theories
 '( lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-prf-pointsp-true-list
 (implies (lw-ray-pointsp points) (true-listp points))
 :hints (("Goal" :induct (lw-ray-pointsp points)
 :in-theory (union-theories
 '(lw-ray-pointsp true-listp endp lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local (defthm lw-prf-pointsp-append
 (implies (and (lw-ray-pointsp left) (lw-ray-pointsp right))
 (lw-ray-pointsp (append left right)))
 :hints (("Goal" :induct (append left right)
 :in-theory (union-theories
 '(lw-ray-pointsp append endp lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-ray-refinement-data
 (implies (lw-ray-refinement-check current points blocks anchors)
 (and (true-listp (lw-ray-refine-path current points blocks))
      (lw-ray-pointsp (lw-ray-refine-path current points blocks))
      (lw-ray-pointsp points)))
 :hints (("Goal" :induct (lw-ray-refinement-check current points blocks anchors)
 :in-theory (union-theories
 '(lw-ray-refinement-check lw-ray-refine-path lw-ray-pointsp lw-prf-pointsp-append lw-prf-pointsp-true-list true-listp append endp lw-complex-positive-halfplanep lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-halfplane-points-data (h (car anchors)) (points (car blocks)))) :do-not-induct t))))

(defthm lw-ray-refinement-last
 (implies (lw-ray-refinement-check current points blocks anchors)
 (equal (lw-ray-path-last current (lw-ray-refine-path current points blocks))
        (lw-ray-path-last current points)))
 :hints (("Goal" :induct (lw-ray-refinement-check current points blocks anchors)
 :in-theory (union-theories
 '(lw-ray-refinement-check lw-ray-refine-path lw-ray-path-last-append lw-ray-path-last endp lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-ray-refinement-path-index
 (implies (lw-ray-refinement-check current points blocks anchors)
 (equal (lw-ray-path-index current (lw-ray-refine-path current points blocks))
        (lw-ray-path-index current points)))
 :hints (("Goal" :induct (lw-ray-refinement-check current points blocks anchors)
 :in-theory (union-theories
 '(lw-ray-refinement-check lw-ray-refine-path lw-ray-path-index-append lw-ray-path-index lw-ray-path-index-integer endp lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-ray-halfplane-chain-replacement (h (car anchors)) (next (car points)) (points (car blocks)))
         (:instance lw-ray-crossing-data (a current) (b (car points)))
         (:instance lw-ray-crossing-data (a (lw-ray-path-last current (car blocks))) (b (car points))))
 :do-not-induct t))))

(defthm lw-ray-refinement-polygon-index
 (implies (lw-ray-refinement-check (car points) (cdr points) blocks anchors)
 (equal (lw-ray-polygon-index (lw-ray-refine-polygon points blocks))
        (lw-ray-polygon-index points)))
 :hints (("Goal"
 :use ((:instance lw-ray-refinement-path-index (current (car points)) (points (cdr points)))
       (:instance lw-ray-refinement-last (current (car points)) (points (cdr points))))
 :in-theory (union-theories
 '(lw-ray-polygon-index lw-ray-refine-polygon endp lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defun lw-ray-near-points (anchor points epsilon)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) (equal points nil)
 (and (lw-complexp (car points))
      (lw-complex-diskp (lw-complex-sub (car points) anchor) epsilon)
      (lw-ray-near-points anchor (cdr points) epsilon))))
(defun lw-ray-refinement-anchors (current points)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) nil
 (cons current (lw-ray-refinement-anchors (car points) (cdr points)))))
(defun lw-ray-refinement-near-check (current points blocks epsilon)
 (declare (xargs :measure (acl2-count points) :hints (("Goal" :in-theory (theory 'ground-zero)))))
 (if (endp points) (and (equal points nil) (equal blocks nil))
 (and (consp blocks) (lw-complexp current) (lw-complexp (car points))
      (not (lw-complex-diskp current epsilon))
      (lw-complex-diskp (lw-complex-sub (car points) current) epsilon)
      (lw-ray-near-points current (car blocks) epsilon)
      (lw-ray-refinement-near-check (car points) (cdr points) (cdr blocks) epsilon))))
(local (in-theory (disable lw-ray-near-points lw-ray-refinement-anchors lw-ray-refinement-near-check)))

(local (defthm lw-prf-near-halfplane
 (implies (and (lw-complexp anchor) (lw-complexp point)
 (rationalp epsilon) (< 0 epsilon)
 (not (lw-complex-diskp anchor epsilon))
 (lw-complex-diskp (lw-complex-sub point anchor) epsilon))
 (and (lw-complex-positive-halfplanep anchor anchor)
      (lw-complex-positive-halfplanep anchor point)))
 :hints (("Goal"
 :use ((:instance lw-complex-disk-norm-square (point anchor) (radius epsilon))
       (:instance lw-complex-dot-self (point anchor))
       (:instance lw-prf-positive-product (a epsilon) (b epsilon))
       (:instance lw-complex-disk-positive-halfplane (radius epsilon)))
 :in-theory (union-theories
 '(lw-complex-positive-halfplanep lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t))
 :rule-classes nil))

(defthm lw-ray-near-points-halfplane
 (implies (and (lw-complexp anchor) (rationalp epsilon) (< 0 epsilon)
 (not (lw-complex-diskp anchor epsilon)) (lw-ray-near-points anchor points epsilon))
 (lw-ray-halfplane-points anchor points))
 :hints (("Goal" :induct (lw-ray-near-points anchor points epsilon)
 :in-theory (union-theories
 '(lw-ray-near-points lw-ray-halfplane-points endp lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-prf-near-halfplane (point (car points)))) :do-not-induct t))))

(defthm lw-ray-refinement-near-check-sound
 (implies (and (rationalp epsilon) (< 0 epsilon)
 (lw-ray-refinement-near-check current points blocks epsilon))
 (lw-ray-refinement-check current points blocks (lw-ray-refinement-anchors current points)))
 :hints (("Goal" :induct (lw-ray-refinement-near-check current points blocks epsilon)
 :in-theory (union-theories
 '(lw-ray-refinement-near-check lw-ray-refinement-check lw-ray-refinement-anchors endp lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))
 (and stable-under-simplificationp
 '(:use ((:instance lw-prf-near-halfplane (anchor current) (point (car points)))
         (:instance lw-ray-near-points-halfplane (anchor current) (points (car blocks)))) :do-not-induct t))))

(defthm lw-ray-refinement-near-path-index
 (implies (and (rationalp epsilon) (< 0 epsilon)
 (lw-ray-refinement-near-check current points blocks epsilon))
 (equal (lw-ray-path-index current (lw-ray-refine-path current points blocks))
        (lw-ray-path-index current points)))
 :hints (("Goal"
 :use (lw-ray-refinement-near-check-sound
       (:instance lw-ray-refinement-path-index (anchors (lw-ray-refinement-anchors current points))))
 :in-theory (union-theories
 '( lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-ray-refinement-near-polygon-index
 (implies (and (rationalp epsilon) (< 0 epsilon)
 (lw-ray-refinement-near-check (car points) (cdr points) blocks epsilon))
 (equal (lw-ray-polygon-index (lw-ray-refine-polygon points blocks))
        (lw-ray-polygon-index points)))
 :hints (("Goal"
 :use ((:instance lw-ray-refinement-near-check-sound (current (car points)) (points (cdr points)))
       (:instance lw-ray-refinement-polygon-index (anchors (lw-ray-refinement-anchors (car points) (cdr points)))))
 :in-theory (union-theories
 '( lw-prf-left-commutes lw-prf-left-distributes lw-prf-fold-constants lw-prf-times-negative lw-prf-negative-times lw-prf-zero-times lw-prf-minus-one lw-prf-double-negative lw-prf-add-cancel lw-prf-double lw-prf-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))
