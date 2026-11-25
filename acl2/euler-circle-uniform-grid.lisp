(in-package "ACL2")

(include-book "euler-circle-uniform-anchor")
(include-book "euler-circle-regular-grid")

; The same factor model generates the contour and the clearance for its grid.

(local (defthm lw-ecug-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecug-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecug-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecug-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecug-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecug-times-negative)))))

(local (defthm lw-ecug-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecug-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecug-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecug-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecug-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecug-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecug-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecug-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecug-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecug-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecug-left-commutes)))))

(defun lw-euler-circle-anchored-grid (rate height outer-radius radius gap clearance)
  (let ((count (lw-euler-circle-uniform-grid-count rate height radius outer-radius gap (* 1/2 clearance)))
        (local-outer (lw-euler-circle-local-outer radius outer-radius))
        (anchor-error (* 1/32 clearance)))
    (list (lw-euler-fixed-grid-arcs (cons rate height) radius 1 count local-outer anchor-error 0 count)
          (lw-euler-fixed-grid-arcs (cons rate height) radius -1 count local-outer anchor-error 0 count))))

(local
 (defthm lw-ecug-scale-order
   (implies (and (rationalp value) (< 0 value) (rationalp cap) (< value cap))
            (< (* value value) (* cap cap)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(defthm lw-euler-circle-uniform-radius-data
   (implies
    (and (rationalp rate) (< 3 rate) (rationalp height)
       (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
       (rationalp scale) (< upper scale)
       (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1) (natp target) (rationalp error) (< 0 error) (rationalp factor-error) (< 0 factor-error)
       (<= error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square))
       (<= factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square)))
    (and (rationalp (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (< 0 (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (< (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)) 1)
         (< lower (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (< (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)) upper)
         (rationalp (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))) (< 0 (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))) (< (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) outer-radius)))
   :hints (("Goal"
            :use (lw-euler-circle-uniform-clearance-budget-data
                  lw-euler-circle-bounded-radius-valid
                  (:instance lw-ecug-scale-order (value upper) (cap scale))
                  (:instance lw-ecug-multiply-order (a 0) (b upper) (factor upper))
                  (:instance lw-ecug-multiply-order (a 1) (b scale) (factor scale))
                  (:instance lw-ecug-positive-product (a (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (b outer-radius))
                  (:instance lw-ecug-positive-product (a (- 1 (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))) (b outer-radius)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ecug-left-commutes lw-ecug-left-distributes lw-ecug-fold-constants
              lw-ecug-times-negative lw-ecug-negative-times lw-ecug-zero-times
              lw-ecug-minus-one lw-ecug-double-negative lw-ecug-add-cancel lw-ecug-double lw-ecug-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil)

(local
 (defthm lw-ecug-grid-projection
   (implies
    (and (rationalp rate) (rationalp height) (rationalp outer-radius)
         (rationalp normalized-radius) (or (equal sign 1) (equal sign -1))
         (posp count) (natp index) (rationalp (lw-circle-grid-midpoint count index)))
    (and (lw-complexp (lw-complex-circle-point (cons 0 0) normalized-radius sign (lw-circle-grid-midpoint count index)))
         (equal (lw-complex-norm-square (lw-complex-circle-point (cons 0 0) normalized-radius sign (lw-circle-grid-midpoint count index))) (* normalized-radius normalized-radius))
         (equal (car (lw-circle-grid-point (cons rate height) (* outer-radius normalized-radius) sign count index)) (+ rate (car (lw-complex-scale outer-radius (lw-complex-circle-point (cons 0 0) normalized-radius sign (lw-circle-grid-midpoint count index))))))
         (equal (cdr (lw-circle-grid-point (cons rate height) (* outer-radius normalized-radius) sign count index)) (+ height (cdr (lw-complex-scale outer-radius (lw-complex-circle-point (cons 0 0) normalized-radius sign (lw-circle-grid-midpoint count index))))))))
   :hints (("Goal"
            :use ((:instance lw-complex-circle-point-rational
                    (center (cons 0 0)) (radius normalized-radius) (parameter (lw-circle-grid-midpoint count index)))
                  (:instance lw-complex-circle-point-distance
                    (center (cons 0 0)) (radius normalized-radius) (parameter (lw-circle-grid-midpoint count index)))
                  (:instance lw-complex-sub-zero (point (lw-complex-circle-point (cons 0 0) normalized-radius sign (lw-circle-grid-midpoint count index))))
                  (:instance lw-phase-rotation-rational (value (lw-circle-grid-midpoint count index))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-grid-point lw-complex-circle-point lw-complex-add lw-complex-scale lw-complexp
              lw-ecug-left-commutes lw-ecug-left-distributes lw-ecug-fold-constants
              lw-ecug-times-negative lw-ecug-negative-times lw-ecug-zero-times
              lw-ecug-minus-one lw-ecug-double-negative lw-ecug-add-cancel lw-ecug-double lw-ecug-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecug-checked-node
   (implies
    (and (rationalp rate) (< 3 rate) (rationalp height)
       (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
       (rationalp scale) (< upper scale)
       (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1) (natp target) (rationalp error) (< 0 error) (rationalp factor-error) (< 0 factor-error)
       (<= error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square))
       (<= factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square))
         (equal normalized-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))
         (rationalp normalized-radius) (< 0 normalized-radius) (< normalized-radius 1)
         (equal clearance (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)) (rationalp clearance) (< 0 clearance) (<= clearance 1)
         (rationalp gap) (< 0 gap) (or (<= (+ (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))) gap) (* (* outer-radius normalized-radius) (* outer-radius normalized-radius)))
            (<= (+ (* (* outer-radius normalized-radius) (* outer-radius normalized-radius)) gap) (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height)))))
         (or (equal sign 1) (equal sign -1)) (posp count) (natp index) (< index count)
         (<= (lw-circle-grid-reach (* outer-radius normalized-radius) count)
             (lw-euler-circle-uniform-grid-reach rate height
               (* outer-radius normalized-radius) outer-radius gap (* 1/2 clearance))))
    (lw-euler-fixed-grid-nodep (cons rate height) (* outer-radius normalized-radius) sign count
      (lw-euler-circle-local-outer (* outer-radius normalized-radius) outer-radius) (* 1/32 clearance) index))
   :hints (("Goal"
            :use (lw-euler-circle-uniform-radius-data lw-ecug-grid-projection
                  (:instance lw-circle-grid-cell-data (radius (* outer-radius normalized-radius)))
                  (:instance lw-euler-circle-uniform-anchor (point (lw-complex-circle-point (cons 0 0) normalized-radius sign (lw-circle-grid-midpoint count index))) (anchor-error (* 1/32 clearance)))
                  (:instance lw-euler-regular-circle-grid-node
                    (radius (* outer-radius normalized-radius)) (floor (* 1/2 clearance)) (error (* 1/32 clearance))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              
              lw-ecug-left-commutes lw-ecug-left-distributes lw-ecug-fold-constants
              lw-ecug-times-negative lw-ecug-negative-times lw-ecug-zero-times
              lw-ecug-minus-one lw-ecug-double-negative lw-ecug-add-cancel lw-ecug-double lw-ecug-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecug-checked-chart
   (implies
    (and (rationalp rate) (< 3 rate) (rationalp height)
       (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
       (rationalp scale) (< upper scale)
       (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1) (natp target) (rationalp error) (< 0 error) (rationalp factor-error) (< 0 factor-error)
       (<= error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square))
       (<= factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square))
         (equal normalized-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))
         (rationalp normalized-radius) (< 0 normalized-radius) (< normalized-radius 1)
         (equal clearance (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)) (rationalp clearance) (< 0 clearance) (<= clearance 1)
         (rationalp gap) (< 0 gap) (or (<= (+ (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))) gap) (* (* outer-radius normalized-radius) (* outer-radius normalized-radius)))
            (<= (+ (* (* outer-radius normalized-radius) (* outer-radius normalized-radius)) gap) (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height)))))
         (or (equal sign 1) (equal sign -1)) (posp count)
         (natp index) (natp remaining) (<= (+ index remaining) count)
         (<= (lw-circle-grid-reach (* outer-radius normalized-radius) count)
             (lw-euler-circle-uniform-grid-reach rate height (* outer-radius normalized-radius) outer-radius gap (* 1/2 clearance))))
    (lw-euler-fixed-grid-nodesp (cons rate height) (* outer-radius normalized-radius) sign count
      (lw-euler-circle-local-outer (* outer-radius normalized-radius) outer-radius) (* 1/32 clearance) index remaining))
   :hints (("Goal"
            :induct (lw-euler-fixed-grid-nodesp (cons rate height) (* outer-radius normalized-radius) sign count
      (lw-euler-circle-local-outer (* outer-radius normalized-radius) outer-radius) (* 1/32 clearance) index remaining)
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-fixed-grid-nodesp
              lw-ecug-left-commutes lw-ecug-left-distributes lw-ecug-fold-constants
              lw-ecug-times-negative lw-ecug-negative-times lw-ecug-zero-times
              lw-ecug-minus-one lw-ecug-double-negative lw-ecug-add-cancel lw-ecug-double lw-ecug-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-ecug-checked-node (sign 1)
                          (normalized-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))
                          (clearance (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)))
                       (:instance lw-ecug-checked-node (sign -1)
                          (normalized-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))
                          (clearance (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square))))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-euler-circle-anchored-grid-valid
  (implies
   (and (rationalp rate) (< 3 rate) (rationalp height)
       (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
       (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
       (rationalp scale) (< upper scale)
       (rationalp cutoff-square) (< (* scale scale) cutoff-square) (< cutoff-square 1) (natp target) (rationalp error) (< 0 error) (rationalp factor-error) (< 0 factor-error)
       (<= error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square))
       (<= factor-error (lw-euler-circle-uniform-approximation-limit rate height outer-radius lower upper scale cutoff-square))
        (rationalp gap) (< 0 gap) (or (<= (+ (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))) gap) (* (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))))
            (<= (+ (* (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))) gap) (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))))))
   (and (rationalp (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (< lower (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (< (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)) upper)
        (lw-euler-circle-coverp (cons rate height) (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))
          (car (lw-euler-circle-anchored-grid rate height outer-radius (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) gap (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square))) (cadr (lw-euler-circle-anchored-grid rate height outer-radius (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) gap (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square))))))
  :hints (("Goal"
           :use (lw-euler-circle-uniform-radius-data lw-euler-circle-uniform-clearance-budget-data
                 (:instance lw-euler-circle-uniform-grid-count-data
                   (radius (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square)))) (floor (* 1/2 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square))))
                 (:instance lw-ecug-checked-chart
                   (normalized-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (clearance (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square))
                   (sign 1) (count (lw-euler-circle-uniform-grid-count rate height (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) outer-radius gap (* 1/2 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)))) (index 0) (remaining (lw-euler-circle-uniform-grid-count rate height (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) outer-radius gap (* 1/2 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)))))
                 (:instance lw-ecug-checked-chart
                   (normalized-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) (clearance (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square))
                   (sign -1) (count (lw-euler-circle-uniform-grid-count rate height (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) outer-radius gap (* 1/2 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)))) (index 0) (remaining (lw-euler-circle-uniform-grid-count rate height (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) outer-radius gap (* 1/2 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)))))
                 (:instance lw-euler-fixed-grid-cover (center (cons rate height)) (radius (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))))
                   (count (lw-euler-circle-uniform-grid-count rate height (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) outer-radius gap (* 1/2 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)))) (outer (lw-euler-circle-local-outer (* outer-radius (car (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))) outer-radius)) (error (* 1/32 (lw-euler-circle-uniform-distance rate height outer-radius lower upper scale cutoff-square)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-anchored-grid lw-complexp
              lw-ecug-left-commutes lw-ecug-left-distributes lw-ecug-fold-constants
              lw-ecug-times-negative lw-ecug-negative-times lw-ecug-zero-times
              lw-ecug-minus-one lw-ecug-double-negative lw-ecug-add-cancel lw-ecug-double lw-ecug-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
