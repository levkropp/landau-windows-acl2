(in-package "ACL2")

(include-book "euler-circle-grid")

; Fix the local outer radius across both parameter charts.

(local (defthm lw-ecfg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecfg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecfg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecfg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecfg-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecfg-times-negative)))))

(local (defthm lw-ecfg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecfg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecfg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecfg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecfg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecfg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecfg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecfg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecfg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecfg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecfg-left-commutes)))))

(defun lw-euler-fixed-grid-patch (center radius sign count outer error index)
  (let ((point (lw-circle-grid-point center radius sign count index)))
    (lw-euler-contour-patch (car point) (cdr point) outer error)))

(defun lw-euler-fixed-grid-arc (center radius sign count outer error index)
  (lw-euler-circle-arc sign
    (lw-circle-grid-parameter count index)
    (lw-circle-grid-parameter count (+ 1 index))
    (lw-euler-fixed-grid-patch center radius sign count outer error index)))

(defun lw-euler-fixed-grid-nodep (center radius sign count outer error index)
  (and (lw-euler-contour-patchp (lw-euler-fixed-grid-patch center radius sign count outer error index))
       (<= (lw-circle-grid-reach radius count) (lw-euler-contour-radius (lw-euler-fixed-grid-patch center radius sign count outer error index)))))

(defun lw-euler-fixed-grid-arcs (center radius sign count outer error index remaining)
  (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp remaining) nil
    (cons (lw-euler-fixed-grid-arc center radius sign count outer error index) (lw-euler-fixed-grid-arcs center radius sign count outer error (+ 1 index) (- remaining 1)))))

(defun lw-euler-fixed-grid-nodesp (center radius sign count outer error index remaining)
  (declare (xargs :measure (nfix remaining) :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp remaining) t
    (and (lw-euler-fixed-grid-nodep center radius sign count outer error index) (lw-euler-fixed-grid-nodesp center radius sign count outer error (+ 1 index) (- remaining 1)))))

(defun lw-euler-fixed-grid-count (radius reach)
  (+ 1 (lw-precision-fuel (* 2 radius) reach)))

(defthm lw-euler-fixed-grid-count-data
  (implies (and (rationalp radius) (< 0 radius) (rationalp reach) (< 0 reach))
           (and (posp (lw-euler-fixed-grid-count radius reach))
                (<= (lw-circle-grid-reach radius (lw-euler-fixed-grid-count radius reach)) reach)))
  :hints (("Goal"
           :use ((:instance lw-precision-fuel-adequate (width (* 2 radius)) (epsilon reach))
                 (:instance lw-positive-division-bound
                   (numerator (* 2 radius)) (divisor (+ 1 (lw-precision-fuel (* 2 radius) reach))) (bound reach)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-fixed-grid-count lw-circle-grid-reach (:type-prescription lw-precision-fuel)
              lw-ecfg-left-commutes lw-ecfg-left-distributes lw-ecfg-fold-constants
              lw-ecfg-times-negative lw-ecfg-negative-times lw-ecfg-zero-times
              lw-ecfg-minus-one lw-ecfg-double-negative lw-ecfg-add-cancel lw-ecfg-double lw-ecfg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecfg-arc-fields
   (and (equal (lw-euler-circle-arc-sign (lw-euler-fixed-grid-arc center radius sign count outer error index)) sign)
        (equal (lw-euler-circle-arc-left (lw-euler-fixed-grid-arc center radius sign count outer error index)) (lw-circle-grid-parameter count index))
        (equal (lw-euler-circle-arc-right (lw-euler-fixed-grid-arc center radius sign count outer error index)) (lw-circle-grid-parameter count (+ 1 index)))
        (equal (lw-euler-circle-arc-patch (lw-euler-fixed-grid-arc center radius sign count outer error index)) (lw-euler-fixed-grid-patch center radius sign count outer error index)))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-fixed-grid-arc lw-euler-circle-arc lw-euler-circle-arc-sign
               lw-euler-circle-arc-left lw-euler-circle-arc-right lw-euler-circle-arc-patch nth endp
              lw-ecfg-left-commutes lw-ecfg-left-distributes lw-ecfg-fold-constants
              lw-ecfg-times-negative lw-ecfg-negative-times lw-ecfg-zero-times
              lw-ecfg-minus-one lw-ecfg-double-negative lw-ecfg-add-cancel lw-ecfg-double lw-ecfg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))))

(local
 (defthm lw-ecfg-arc-valid
   (implies
    (and (lw-complexp center) (rationalp radius) (< 0 radius) (or (equal sign 1) (equal sign -1))
         (posp count) (natp index) (< index count) (lw-euler-fixed-grid-nodep center radius sign count outer error index))
    (lw-euler-circle-arcp center radius (lw-euler-fixed-grid-arc center radius sign count outer error index)))
   :hints (("Goal"
            :use (lw-circle-grid-cell-data lw-circle-grid-point-rational
                  (:instance lw-circle-grid-parameter-data)
                  (:instance lw-circle-grid-parameter-data (index (+ 1 index)))
                  (:instance lw-euler-contour-patch-data (patch (lw-euler-fixed-grid-patch center radius sign count outer error index)))
                  (:instance lw-complex-zero-disk
                    (radius (- (lw-euler-contour-radius (lw-euler-fixed-grid-patch center radius sign count outer error index)) (lw-circle-grid-reach radius count)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-arcp lw-euler-fixed-grid-nodep lw-euler-fixed-grid-arc lw-euler-fixed-grid-patch
               lw-euler-circle-arc lw-euler-circle-arc-sign lw-euler-circle-arc-left lw-euler-circle-arc-right
               lw-euler-circle-arc-midpoint lw-euler-circle-arc-reach lw-euler-circle-arc-patch lw-euler-circle-arc-point
               lw-euler-contour-patch lw-euler-contour-center lw-circle-grid-point
               lw-complexp lw-complex-sub true-listp len nth endp
              lw-ecfg-left-commutes lw-ecfg-left-distributes lw-ecfg-fold-constants
              lw-ecfg-times-negative lw-ecfg-negative-times lw-ecfg-zero-times
              lw-ecfg-minus-one lw-ecfg-double-negative lw-ecfg-add-cancel lw-ecfg-double lw-ecfg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-ecfg-chart-valid
   (implies
    (and (lw-complexp center) (rationalp radius) (< 0 radius) (or (equal sign 1) (equal sign -1))
         (posp count) (natp index) (natp remaining) (equal (+ index remaining) count)
         (lw-euler-fixed-grid-nodesp center radius sign count outer error index remaining))
    (lw-euler-circle-chart-coverp center radius sign (lw-euler-fixed-grid-arcs center radius sign count outer error index remaining)
      (lw-circle-grid-parameter count index)))
   :hints (("Goal"
            :induct (lw-euler-fixed-grid-arcs center radius sign count outer error index remaining)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ecfg-arc-fields lw-ecfg-arc-valid lw-circle-grid-endpoints lw-circle-grid-parameter-data
               lw-euler-fixed-grid-arcs lw-euler-fixed-grid-nodesp lw-euler-circle-chart-coverp endp
              lw-ecfg-left-commutes lw-ecfg-left-distributes lw-ecfg-fold-constants
              lw-ecfg-times-negative lw-ecfg-negative-times lw-ecfg-zero-times
              lw-ecfg-minus-one lw-ecfg-double-negative lw-ecfg-add-cancel lw-ecfg-double lw-ecfg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(defthm lw-euler-fixed-grid-cover
  (implies
   (and (lw-complexp center) (rationalp radius) (< 0 radius) (posp count)
        (lw-euler-fixed-grid-nodesp center radius 1 count outer error 0 count)
        (lw-euler-fixed-grid-nodesp center radius -1 count outer error 0 count))
   (lw-euler-circle-coverp center radius (lw-euler-fixed-grid-arcs center radius 1 count outer error 0 count) (lw-euler-fixed-grid-arcs center radius -1 count outer error 0 count)))
  :hints (("Goal"
           :use (lw-circle-grid-endpoints
                 (:instance lw-ecfg-chart-valid (sign 1) (index 0) (remaining count))
                 (:instance lw-ecfg-chart-valid (sign -1) (index 0) (remaining count)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-coverp
              lw-ecfg-left-commutes lw-ecfg-left-distributes lw-ecfg-fold-constants
              lw-ecfg-times-negative lw-ecfg-negative-times lw-ecfg-zero-times
              lw-ecfg-minus-one lw-ecfg-double-negative lw-ecfg-add-cancel lw-ecfg-double lw-ecfg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
