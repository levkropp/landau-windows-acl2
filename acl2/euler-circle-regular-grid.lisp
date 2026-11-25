(in-package "ACL2")

(include-book "euler-circle-regular-geometry")
(include-book "euler-circle-fixed-grid")
(include-book "euler-neighborhood-uniform-radius")
(include-book "euler-neighborhood-uniform-slope")

; Choose a mesh from the common lower radius, then check the anchor at each node.

(local (defthm lw-ecrd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecrd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecrd-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecrd-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecrd-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecrd-times-negative)))))

(local (defthm lw-ecrd-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecrd-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecrd-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecrd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecrd-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecrd-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecrd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecrd-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecrd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ecrd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ecrd-left-commutes)))))

(defun lw-euler-circle-uniform-grid-reach (rate height radius outer-radius gap floor)
  (lw-euler-uniform-patch-radius
    (lw-euler-circle-local-outer radius outer-radius) floor
    (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate height outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius)))
    (- rate outer-radius)
    (lw-circle-radial-clearance radius gap)))

(defun lw-euler-circle-uniform-grid-count (rate height radius outer-radius gap floor)
  (lw-euler-fixed-grid-count radius (lw-euler-circle-uniform-grid-reach rate height radius outer-radius gap floor)))

(local
 (defthm lw-ecrd-positive-parameters
   (implies (and (rationalp rate) (rationalp height)
       (rationalp radius) (< 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate))
            (and (rationalp (lw-euler-circle-local-outer radius outer-radius)) (< 0 (lw-euler-circle-local-outer radius outer-radius))
                 (rationalp (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate height outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius)))) (< 0 (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate height outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius))))))
   :hints (("Goal"
            :use ((:instance lw-euler-uniform-coefficient-cap-valid (radius outer-radius))
                  (:instance lw-reciprocal-positive (value (lw-euler-circle-local-outer radius outer-radius)))
                  (:instance lw-ecrd-positive-product
                    (a (+ 5 (lw-euler-uniform-coefficient-cap rate height outer-radius))) (b (/ (lw-euler-circle-local-outer radius outer-radius)))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-local-outer
              lw-ecrd-left-commutes lw-ecrd-left-distributes lw-ecrd-fold-constants
              lw-ecrd-times-negative lw-ecrd-negative-times lw-ecrd-zero-times
              lw-ecrd-minus-one lw-ecrd-double-negative lw-ecrd-add-cancel lw-ecrd-double lw-ecrd-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-circle-uniform-grid-count-data
  (implies
   (and (rationalp rate) (rationalp height)
       (rationalp radius) (< 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate)
        (rationalp gap) (< 0 gap) (rationalp floor) (< 0 floor))
   (and (posp (lw-euler-circle-uniform-grid-count rate height radius outer-radius gap floor))
        (<= (lw-circle-grid-reach radius (lw-euler-circle-uniform-grid-count rate height radius outer-radius gap floor)) (lw-euler-circle-uniform-grid-reach rate height radius outer-radius gap floor))))
  :hints (("Goal"
           :use (lw-ecrd-positive-parameters
                 lw-circle-radial-clearance-budget
                 (:instance lw-euler-uniform-patch-radius-positive
                   (outer-radius (lw-euler-circle-local-outer radius outer-radius)) (slope (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate height outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius))))
                   (origin-clearance (- rate outer-radius)) (pole-clearance (lw-circle-radial-clearance radius gap)))
                 (:instance lw-euler-fixed-grid-count-data (reach (lw-euler-circle-uniform-grid-reach rate height radius outer-radius gap floor))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-uniform-grid-count lw-euler-circle-uniform-grid-reach
              lw-ecrd-left-commutes lw-ecrd-left-distributes lw-ecrd-fold-constants
              lw-ecrd-times-negative lw-ecrd-negative-times lw-ecrd-zero-times
              lw-ecrd-minus-one lw-ecrd-double-negative lw-ecrd-add-cancel lw-ecrd-double lw-ecrd-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ecrd-node-on-circle
   (implies (and (rationalp rate) (rationalp height) (rationalp radius) (< 0 radius)
                 (or (equal sign 1) (equal sign -1))
                 (posp count) (natp index) (< index count))
            (and (lw-complexp (lw-circle-grid-point (cons rate height) radius sign count index))
                 (equal (lw-complex-norm-square (lw-complex-sub (lw-circle-grid-point (cons rate height) radius sign count index) (cons rate height))) (* radius radius))))
   :hints (("Goal"
            :use ((:instance lw-circle-grid-point-rational (center (cons rate height)))
                  lw-circle-grid-cell-data
                  (:instance lw-complex-circle-point-distance
                    (center (cons rate height)) (parameter (lw-circle-grid-midpoint count index))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-grid-point lw-complexp
              lw-ecrd-left-commutes lw-ecrd-left-distributes lw-ecrd-fold-constants
              lw-ecrd-times-negative lw-ecrd-negative-times lw-ecrd-zero-times
              lw-ecrd-minus-one lw-ecrd-double-negative lw-ecrd-add-cancel lw-ecrd-double lw-ecrd-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ecrd-reconstruct-point
   (implies (consp point) (equal (cons (car point) (cdr point)) point))))

(defthm lw-euler-regular-circle-grid-node
  (implies
   (and (rationalp rate) (rationalp height)
       (rationalp radius) (< 0 radius)
       (rationalp outer-radius) (< radius outer-radius) (< outer-radius rate) (rationalp gap) (< 0 gap)
       (or (<= (+ (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height))) gap) (* radius radius))
           (<= (+ (* radius radius) gap) (lw-complex-norm-square (lw-complex-sub (cons 1 0) (cons rate height)))))
        (rationalp floor) (< 0 floor) (rationalp error) (< 0 error) (<= error 1)
        (or (equal sign 1) (equal sign -1)) (posp count) (natp index) (< index count)
        (<= (lw-circle-grid-reach radius count) (lw-euler-circle-uniform-grid-reach rate height radius outer-radius gap floor))
        (lw-euler-value-clearance-check (car (lw-circle-grid-point (cons rate height) radius sign count index)) (cdr (lw-circle-grid-point (cons rate height) radius sign count index)) error) (<= floor (lw-euler-value-clearance-size (car (lw-circle-grid-point (cons rate height) radius sign count index)) (cdr (lw-circle-grid-point (cons rate height) radius sign count index)) error)))
   (lw-euler-fixed-grid-nodep (cons rate height) radius sign count (lw-euler-circle-local-outer radius outer-radius) error index))
  :hints (("Goal"
           :use (lw-ecrd-node-on-circle lw-ecrd-positive-parameters
                 (:instance lw-ecrd-reconstruct-point (point (lw-circle-grid-point (cons rate height) radius sign count index)))
                 (:instance lw-euler-circle-regular-point-data (point (lw-circle-grid-point (cons rate height) radius sign count index)))
                 (:instance lw-euler-neighborhood-uniform-slope
                   (rate (car (lw-circle-grid-point (cons rate height) radius sign count index))) (height (cdr (lw-circle-grid-point (cons rate height) radius sign count index)))
                   (outer-radius (lw-euler-circle-local-outer radius outer-radius))
                   (global-rate rate) (global-height height) (global-radius outer-radius)
                   (displacement radius))
                 (:instance lw-euler-contour-patch-valid
                   (rate (car (lw-circle-grid-point (cons rate height) radius sign count index))) (height (cdr (lw-circle-grid-point (cons rate height) radius sign count index)))
                   (outer-radius (lw-euler-circle-local-outer radius outer-radius)) (anchor-error error))
                 (:instance lw-euler-local-normalized-radius-uniform-lower
                   (rate (car (lw-circle-grid-point (cons rate height) radius sign count index))) (height (cdr (lw-circle-grid-point (cons rate height) radius sign count index)))
                   (outer-radius (lw-euler-circle-local-outer radius outer-radius)) (anchor-error error)
                   (slope (* 4 (+ 5 (lw-euler-uniform-coefficient-cap rate height outer-radius)) (/ (lw-euler-circle-local-outer radius outer-radius)))) (origin-clearance (- rate outer-radius))
                   (pole-clearance (lw-circle-radial-clearance radius gap))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-fixed-grid-nodep lw-euler-fixed-grid-patch lw-euler-contour-patch
              lw-euler-contour-radius lw-euler-circle-uniform-grid-reach lw-ecrd-reconstruct-point lw-complexp nth endp
              lw-ecrd-left-commutes lw-ecrd-left-distributes lw-ecrd-fold-constants
              lw-ecrd-times-negative lw-ecrd-negative-times lw-ecrd-zero-times
              lw-ecrd-minus-one lw-ecrd-double-negative lw-ecrd-add-cancel lw-ecrd-double lw-ecrd-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
