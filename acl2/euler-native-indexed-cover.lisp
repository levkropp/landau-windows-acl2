; One native coarse index controls resolved Euler covers at every requested accuracy.
(in-package "ACL2")
(include-book "euler-square-line-refinement")
(include-book "euler-native-polygon-index")
(include-book "polynomial-indexed-cover")
(local (in-theory (disable lw-euler-square-index-check lw-euler-polygon-index-check
 lw-euler-native-polygon-index lw-euler-positive-square-model lw-polynomial-grid-step
 lw-polynomial-grid lw-ray-grid-boundary-index lw-polynomial-square-crossings
 lw-polynomial-line-crossings lw-euler-square-line-clearancep
 lw-polynomial-indexed-cover lw-polynomial-indexed-cover-count lw-polynomial-indexed-cover-address
 lw-polynomial-sublevel-cover lw-polynomial-sublevel-index-address lw-polynomial-cover-index
 lw-complex-polynomial lw-complex-diskp lw-complex-sub lw-complexp
 lw-positive-squarep lw-square-containsp lw-square-cover-containsp)))
(local (defthm lw-nic-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-nic-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-nic-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-nic-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-nic-times-negative (a b) (b a)))
                 :in-theory (disable lw-nic-times-negative)))))

(local (defthm lw-nic-zero-times (equal (* 0 a) 0)))

(local (defthm lw-nic-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-nic-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-nic-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-nic-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-nic-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-nic-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-nic-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nic-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-nic-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-nic-left-commutes)))))
(defun lw-euler-native-cover-request (eta epsilon) (min eta epsilon))
(defun lw-euler-native-indexed-cover-count (anchor side coarse eta target width epsilon)
 (lw-polynomial-indexed-cover-count (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side coarse width epsilon))
(defun lw-euler-native-indexed-cover (anchor side coarse eta target width epsilon)
 (lw-polynomial-indexed-cover (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side coarse width epsilon))
(defun lw-euler-native-indexed-cover-address (anchor side coarse eta target width epsilon)
 (lw-polynomial-indexed-cover-address (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side coarse width epsilon))
(local (in-theory (disable lw-euler-native-cover-request lw-euler-native-indexed-cover-count
 lw-euler-native-indexed-cover lw-euler-native-indexed-cover-address)))

(local (defthm lw-nic-positive-count-product
 (implies (and (posp a) (posp b)) (posp (* a b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes (:rewrite :type-prescription)))

(defthm lw-euler-square-model-grid-refinement
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (posp factor)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (equal (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side target error) anchor side (* coarse factor)))
        (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side target error) anchor side coarse))))
 :hints (("Goal"
 :use ((:instance lw-euler-square-line-clearance-generated (edge 0))
       (:instance lw-euler-square-line-clearance-generated (edge 1))
       (:instance lw-euler-square-line-clearance-generated (edge 2))
       (:instance lw-euler-square-line-clearance-generated (edge 3))
       (:instance lw-euler-square-model-line-refinement-index (edge 0) (index 0) (remaining coarse))
       (:instance lw-euler-square-model-line-refinement-index (edge 1) (index 0) (remaining coarse))
       (:instance lw-euler-square-model-line-refinement-index (edge 2) (index 0) (remaining coarse))
       (:instance lw-euler-square-model-line-refinement-index (edge 3) (index 0) (remaining coarse))
       (:instance lw-polynomial-grid-boundary-as-crossings (coefficients (lw-euler-positive-square-model anchor side target error)) (count coarse))
       (:instance lw-polynomial-grid-boundary-as-crossings (coefficients (lw-euler-positive-square-model anchor side target error)) (count (* coarse factor))))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-polynomial-square-crossings lw-nic-positive-count-product lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-square-grid-refinement-index
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (posp factor)
               (natp target) (rationalp error) (< 0 error) (<= error eta))
 (equal (lw-ray-grid-boundary-index (lw-polynomial-grid (lw-euler-positive-square-model anchor side target error) anchor side (* coarse factor)))
        (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error)))
 :hints (("Goal"
 :use (lw-euler-square-model-grid-refinement
       (:instance lw-euler-native-square-index-model-agreement
        (count coarse) (step (lw-polynomial-grid-step side coarse)) (value-error base-error)))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-cover-request-data
 (implies (and (rationalp eta) (< 0 eta) (rationalp epsilon) (< 0 epsilon))
 (and (rationalp (lw-euler-native-cover-request eta epsilon)) (< 0 (lw-euler-native-cover-request eta epsilon)) (<= (lw-euler-native-cover-request eta epsilon) eta) (<= (lw-euler-native-cover-request eta epsilon) epsilon)))
 :hints (("Goal" :in-theory (union-theories
 '(lw-euler-native-cover-request min lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(defthm lw-euler-native-indexed-cover-count-data
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon))
 (and (posp (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon))
      (rationalp (lw-polynomial-grid-step side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon))) (< 0 (lw-polynomial-grid-step side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)))
      (<= (lw-polynomial-grid-step side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)) width)
      (rationalp (lw-polynomial-cell-variation (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)))
      (<= 0 (lw-polynomial-cell-variation (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)))
      (<= (lw-polynomial-cell-variation (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)) epsilon)))
 :hints (("Goal"
 :use (lw-euler-native-cover-request-data
       (:instance lw-euler-positive-square-model-valid (error (lw-euler-native-cover-request eta epsilon)))
       (:instance lw-polynomial-indexed-cover-count-data (coefficients (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)))))
 :in-theory (union-theories
 '(lw-euler-native-indexed-cover-count lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-indexed-cover-index
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon))
 (equal (lw-polynomial-cover-index (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon)) (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error)))
 :hints (("Goal"
 :use (lw-euler-native-cover-request-data lw-euler-native-indexed-cover-count-data
       (:instance lw-euler-positive-square-model-valid (error (lw-euler-native-cover-request eta epsilon)))
       (:instance lw-polynomial-resolved-cover-count-data (coefficients (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon))))
       (:instance lw-euler-native-square-grid-refinement-index (factor (lw-polynomial-resolved-cover-count (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side width epsilon)) (error (lw-euler-native-cover-request eta epsilon)))
       (:instance lw-polynomial-sublevel-cover-index-conservation (coefficients (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon))) (count (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon))))
 :in-theory (union-theories
 '(lw-euler-native-indexed-cover lw-euler-native-indexed-cover-count lw-polynomial-indexed-cover lw-polynomial-indexed-cover-count lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-indexed-cover-data
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon))
 (and (lw-square-address-listp (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon) (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon))
      (lw-polynomial-active-coverp (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) epsilon (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon))
      (<= (len (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon)) (* (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)))))
 :hints (("Goal"
 :use (lw-euler-native-cover-request-data
       (:instance lw-euler-positive-square-model-valid (error (lw-euler-native-cover-request eta epsilon)))
       (:instance lw-polynomial-indexed-cover-data (coefficients (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)))))
 :in-theory (union-theories
 '(lw-euler-native-indexed-cover lw-euler-native-indexed-cover-count lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-positive-square-model-small-value
 (implies (and (lw-positive-squarep anchor side) (lw-square-containsp anchor side point)
               (natp target) (rationalp error) (< 0 error) (<= error epsilon)
               (rationalp epsilon) (< 0 epsilon)
               (rationalp value-error) (< 0 value-error) (<= value-error epsilon)
               (lw-complex-diskp
                (lw-complex-euler-continuation-value (car point) (cdr point) value-error) (/ epsilon 2)))
 (lw-complex-diskp (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) point 0) epsilon))
 :hints (("Goal"
 :use (lw-euler-positive-square-model-comparison lw-euler-positive-square-model-valid
       lw-positive-square-point-data
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side target error)) (offset 0))
       (:instance lw-complex-euler-continuation-value-rational (rate (car point)) (height (cdr point)) (error value-error))
       (:instance lw-complex-difference-triangle
        (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) point 0))
        (middle (lw-complex-euler-continuation-value (car point) (cdr point) value-error)) (right (cons 0 0))
        (radius (+ (/ error 4) (/ value-error 4))) (other-radius (/ epsilon 2)))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-polynomial (lw-euler-positive-square-model anchor side target error) point 0))
        (radius (+ (/ error 4) (/ value-error 4) (/ epsilon 2))) (cap epsilon)))
 :in-theory (union-theories
 '(lw-complexp lw-complex-sub-zero cons lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(defthm lw-euler-native-indexed-cover-complete
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon)
               (lw-square-containsp anchor side point)
               (rationalp value-error) (< 0 value-error) (<= value-error epsilon)
               (lw-complex-diskp
                (lw-complex-euler-continuation-value (car point) (cdr point) value-error) (/ epsilon 2)))
 (and (member-equal (lw-square-cell-address anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) point) (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon))
      (lw-square-cover-containsp anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) point (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon))))
 :hints (("Goal"
 :use (lw-euler-native-cover-request-data
       (:instance lw-euler-positive-square-model-valid (error (lw-euler-native-cover-request eta epsilon)))
       (:instance lw-euler-positive-square-model-small-value (error (lw-euler-native-cover-request eta epsilon)))
       (:instance lw-polynomial-indexed-cover-complete (coefficients (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)))))
 :in-theory (union-theories
 '(lw-euler-native-indexed-cover lw-euler-native-indexed-cover-count lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-indexed-cover-address-witness
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (not (equal (lw-euler-native-polygon-index (lw-polynomial-square-boundary anchor side coarse) base-error) 0))
               (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon))
 (let ((address (lw-euler-native-indexed-cover-address anchor side coarse eta target width epsilon)))
 (and (consp address) (member-equal address (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon))
      (natp (car address)) (< (car address) (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)) (natp (cdr address)) (< (cdr address) (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon))
      (not (equal (lw-polynomial-cell-index (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) (car address) (cdr address)) 0))
      (lw-complex-diskp (lw-polynomial-grid-value (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) (car address) (cdr address)) (* 2 epsilon)))))
 :hints (("Goal"
 :use (lw-euler-native-cover-request-data lw-euler-native-indexed-cover-count-data
       (:instance lw-euler-positive-square-model-valid (error (lw-euler-native-cover-request eta epsilon)))
       (:instance lw-polynomial-resolved-cover-count-data (coefficients (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon))))
       (:instance lw-euler-native-square-grid-refinement-index (factor (lw-polynomial-resolved-cover-count (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side width epsilon)) (error (lw-euler-native-cover-request eta epsilon)))
       (:instance lw-polynomial-sublevel-index-address-witness (coefficients (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon))) (count (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)))
       (:instance lw-complex-disk-enlarge
        (point (lw-polynomial-grid-value (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) (car (lw-euler-native-indexed-cover-address anchor side coarse eta target width epsilon)) (cdr (lw-euler-native-indexed-cover-address anchor side coarse eta target width epsilon))))
        (radius (+ epsilon (lw-polynomial-cell-variation (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon)))) (cap (* 2 epsilon))))
 :in-theory (union-theories
 '(lw-euler-native-indexed-cover-address lw-euler-native-indexed-cover lw-euler-native-indexed-cover-count lw-polynomial-indexed-cover-address lw-polynomial-indexed-cover lw-polynomial-indexed-cover-count lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-indexed-cover-value-bound
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon) (lw-square-cover-containsp anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) point (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon)) (rationalp value-error) (< 0 value-error))
 (and (lw-square-containsp anchor side point)
      (lw-complex-diskp
       (lw-complex-euler-continuation-value (car point) (cdr point) value-error)
       (+ (* 13/4 epsilon) (/ value-error 4)))))
 :hints (("Goal"
 :use (lw-euler-native-cover-request-data
       (:instance lw-euler-positive-square-model-valid (error (lw-euler-native-cover-request eta epsilon)))
       (:instance lw-polynomial-indexed-cover-value-bound (coefficients (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon))))
       (:instance lw-euler-positive-square-model-comparison (error (lw-euler-native-cover-request eta epsilon)))
       lw-positive-square-point-data
       (:instance lw-complex-polynomial-rational (coefficients (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon))) (offset 0))
       (:instance lw-complex-euler-continuation-value-rational (rate (car point)) (height (cdr point)) (error value-error))
       (:instance lw-complex-difference-symmetric
        (left (lw-complex-polynomial (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) point 0))
        (right (lw-complex-euler-continuation-value (car point) (cdr point) value-error))
        (radius (+ (/ (lw-euler-native-cover-request eta epsilon) 4) (/ value-error 4))))
       (:instance lw-complex-difference-triangle
        (left (lw-complex-euler-continuation-value (car point) (cdr point) value-error))
        (middle (lw-complex-polynomial (lw-euler-positive-square-model anchor side target (lw-euler-native-cover-request eta epsilon)) point 0)) (right (cons 0 0))
        (radius (+ (/ (lw-euler-native-cover-request eta epsilon) 4) (/ value-error 4))) (other-radius (* 3 epsilon)))
       (:instance lw-complex-disk-enlarge
        (point (lw-complex-euler-continuation-value (car point) (cdr point) value-error))
        (radius (+ (/ (lw-euler-native-cover-request eta epsilon) 4) (/ value-error 4) (* 3 epsilon)))
        (cap (+ (* 13/4 epsilon) (/ value-error 4)))))
 :in-theory (union-theories
 '(lw-euler-native-indexed-cover lw-euler-native-indexed-cover-count lw-euler-square-index-check lw-euler-polygon-index-check lw-positive-squarep lw-complexp lw-complex-sub-zero cons lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(defthm lw-euler-native-indexed-cover-complement
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon) (lw-square-containsp anchor side point) (not (lw-square-cover-containsp anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) point (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon)))
               (rationalp value-error) (< 0 value-error) (<= value-error epsilon))
 (not (lw-complex-diskp
       (lw-complex-euler-continuation-value (car point) (cdr point) value-error) (/ epsilon 2))))
 :hints (("Goal" :use (lw-euler-native-indexed-cover-complete)
 :in-theory (union-theories
 '( lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)))

(local (defthm lw-nic-not-small-l1
 (implies (and (lw-complexp value) (rationalp epsilon) (< 0 epsilon)
               (not (lw-complex-diskp value (/ epsilon 2))))
 (< (/ epsilon 2) (lw-complex-l1 value)))
 :hints (("Goal"
 :use ((:instance lw-complex-l1-bound (point value))
       (:instance lw-complex-disk-enlarge (point value) (radius (lw-complex-l1 value)) (cap (/ epsilon 2))))
 :in-theory (union-theories
 '( lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :do-not-induct t)) :rule-classes nil))

(defthm lw-euler-native-indexed-cover-uncovered-check
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon) (lw-square-containsp anchor side point) (not (lw-square-cover-containsp anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) point (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon))))
 (and (lw-euler-value-clearance-check (car point) (cdr point) (/ epsilon 64))
      (<= (/ epsilon 8) (lw-euler-value-clearance-lower (car point) (cdr point) (/ epsilon 64)))))
 :hints (("Goal"
 :use ((:instance lw-euler-native-indexed-cover-complement (value-error (/ epsilon 64)))
       lw-positive-square-point-data
       (:instance lw-complex-euler-continuation-value-rational (rate (car point)) (height (cdr point)) (error (/ epsilon 64)))
       (:instance lw-nic-not-small-l1
        (value (lw-complex-euler-continuation-value (car point) (cdr point) (/ epsilon 64)))))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-euler-value-clearance-check lw-euler-value-clearance-size lw-euler-value-clearance-lower lw-complexp lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))

(local (defthm lw-nic-square-order
 (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b)) (<= (* a a) (* b b)))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-euler-native-indexed-cover-uncovered-denominator
 (implies (and (lw-euler-square-index-check anchor side coarse base-target base-error (lw-polynomial-grid-step side coarse) eta) (natp target) (rationalp width) (< 0 width) (rationalp epsilon) (< 0 epsilon) (lw-square-containsp anchor side point) (not (lw-square-cover-containsp anchor side (lw-euler-native-indexed-cover-count anchor side coarse eta target width epsilon) point (lw-euler-native-indexed-cover anchor side coarse eta target width epsilon)))
               (rationalp request) (< 0 request) (<= request (/ epsilon 32)))
 (let ((value (lw-complex-euler-continuation-value (car point) (cdr point) request)))
 (and (lw-complexp value) (not (equal value (cons 0 0)))
      (<= (* (/ epsilon 8) (/ epsilon 8)) (lw-complex-norm-square value))
      (lw-complex-diskp (lw-complex-reciprocal value) (/ (/ epsilon 8))))))
 :hints (("Goal"
 :use (lw-euler-native-indexed-cover-uncovered-check
       (:instance lw-euler-value-clearance-data (rate (car point)) (height (cdr point)) (anchor-error (/ epsilon 64)))
       (:instance lw-complex-euler-value-clearance (rate (car point)) (height (cdr point)) (anchor-error (/ epsilon 64)))
       (:instance lw-nic-square-order (a (/ epsilon 8))
        (b (lw-euler-value-clearance-lower (car point) (cdr point) (/ epsilon 64))))
       (:instance lw-complex-reciprocal-disk-bound
        (point (lw-complex-euler-continuation-value (car point) (cdr point) request)) (lower (/ epsilon 8))))
 :in-theory (union-theories
 '(lw-euler-square-index-check lw-euler-polygon-index-check lw-nic-left-commutes lw-nic-left-distributes lw-nic-fold-constants lw-nic-times-negative lw-nic-negative-times lw-nic-zero-times lw-nic-minus-one lw-nic-double-negative lw-nic-add-cancel lw-nic-double lw-nic-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
 :do-not-induct t)))


