(in-package "ACL2")

(include-book "euler-window-quadratic-coefficients")

(defun lw-euler-window-weighted-tail (height radius)
  (+ (lw-complex-l1 (lw-zeta-residue-denominator (cons 252 height))) (* (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons 252 height)))) radius) (* radius radius)))

(defun lw-euler-window-quadratic-tail-budget
    (height ceiling numerator denominator index error real-radius real-mass real-error)
  (let ((distance (- 252 (/ numerator denominator)))
        (order (+ 2 index)))
    (+ (* (+ (* 8 ceiling) 10) (/ distance)
          (lw-euler-window-weighted-tail height distance) (lw-rational-power (/ distance) order))
       (* real-mass (lw-euler-window-weighted-tail height real-radius) (lw-rational-power (/ real-radius) order))
       (* (+ real-error (* 2 error)) (lw-euler-window-weighted-tail height 1)))))

(local (defthm lw-ewtb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewtb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewtb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewtb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewtb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewtb-times-negative)))))

(local (defthm lw-ewtb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewtb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewtb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewtb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewtb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewtb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewtb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewtb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewtb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewtb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewtb-left-commutes)))))

(local
 (defthm lw-ewtb-weights-data
   (implies (rationalp height)
            (and (rationalp (lw-complex-l1 (lw-zeta-residue-denominator (cons 252 height)))) (<= 0 (lw-complex-l1 (lw-zeta-residue-denominator (cons 252 height))))
                 (rationalp (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons 252 height))))) (<= 0 (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons 252 height)))))))
   :hints (("Goal"
            :in-theory
            (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complex-l1 lw-zeta-residue-denominator car-cons cdr-cons
              lw-complex-mul lw-complex-scale lw-complex-sub abs
              lw-ewtb-left-commutes lw-ewtb-left-distributes lw-ewtb-fold-constants
              lw-ewtb-times-negative lw-ewtb-negative-times lw-ewtb-zero-times
              lw-ewtb-minus-one lw-ewtb-double-negative lw-ewtb-add-cancel lw-ewtb-double lw-ewtb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-window-weighted-tail-data
  (implies (and (rationalp height) (rationalp radius) (<= 0 radius))
           (and (rationalp (lw-euler-window-weighted-tail height radius))
                (<= (* radius radius) (lw-euler-window-weighted-tail height radius))))
  :hints (("Goal"
           :use (lw-ewtb-weights-data
                 (:instance lw-ewtb-multiply-order (a 0) (b (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons 252 height))))) (factor radius)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-window-weighted-tail
              lw-ewtb-left-commutes lw-ewtb-left-distributes lw-ewtb-fold-constants
              lw-ewtb-times-negative lw-ewtb-negative-times lw-ewtb-zero-times
              lw-ewtb-minus-one lw-ewtb-double-negative lw-ewtb-add-cancel lw-ewtb-double lw-ewtb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ewtb-tail-identity
   (implies (and (rationalp radius) (< 0 radius) (natp index)
                 (rationalp first) (rationalp second) (rationalp mass))
            (equal (* mass (+ (* first (lw-rational-power (/ radius) (+ 2 index)))
                              (* second (lw-rational-power (/ radius) (+ 1 index)))
                              (lw-rational-power (/ radius) index)))
                   (* mass (+ first (* second radius) (* radius radius))
                      (lw-rational-power (/ radius) (+ 2 index)))))
   :hints (("Goal"
            :use ((:instance lw-rational-power-add-exponents
                    (base (/ radius)) (left 1) (right index))
                  (:instance lw-rational-power-add-exponents
                    (base (/ radius)) (left 1) (right (+ 1 index)))
                  (:instance lw-ewtb-inverse-factor
                    (divisor radius) (coefficient (lw-rational-power (/ radius) index)))
                  (:instance lw-ewtb-inverse-factor
                    (divisor radius) (coefficient (lw-rational-power (/ radius) (+ 1 index)))))
            :expand ((lw-rational-power (/ radius) 1) (lw-rational-power (/ radius) 0))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-reciprocal-positive lw-rational-power-rational
              lw-ewtb-left-commutes lw-ewtb-left-distributes lw-ewtb-fold-constants
              lw-ewtb-times-negative lw-ewtb-negative-times lw-ewtb-zero-times
              lw-ewtb-minus-one lw-ewtb-double-negative lw-ewtb-add-cancel lw-ewtb-double lw-ewtb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ewtb-window-mass
   (implies (and (rationalp distance) (< 0 distance) (natp index) (rationalp mass))
            (equal (* mass (lw-rational-power (/ distance) (+ 1 index)))
                   (* mass (/ distance) (lw-rational-power (/ distance) index))))
   :hints (("Goal"
            :use ((:instance lw-rational-power-add-exponents
                    (base (/ distance)) (left 1) (right index)))
            :expand ((lw-rational-power (/ distance) 1) (lw-rational-power (/ distance) 0))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-reciprocal-positive lw-rational-power-rational
              lw-ewtb-left-commutes lw-ewtb-left-distributes lw-ewtb-fold-constants
              lw-ewtb-times-negative lw-ewtb-negative-times lw-ewtb-zero-times
              lw-ewtb-minus-one lw-ewtb-double-negative lw-ewtb-add-cancel lw-ewtb-double lw-ewtb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-window-quadratic-tail-budget-adequate
  (implies (and (rationalp height) (natp index)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp error) (< 0 error)
                (rationalp real-radius) (< 0 real-radius)
                (rationalp real-mass) (<= 0 real-mass)
                (rationalp real-error) (<= 0 real-error)
                (<= (- (car (lw-complex-mellin-euler-coefficient-value 252 0 index error))) (+ (* real-mass (lw-rational-power (/ real-radius) index)) real-error))
                (<= (- (car (lw-complex-mellin-euler-coefficient-value 252 0 (+ 1 index) error))) (+ (* real-mass (lw-rational-power (/ real-radius) (+ 1 index))) real-error))
                (<= (- (car (lw-complex-mellin-euler-coefficient-value 252 0 (+ 2 index) error))) (+ (* real-mass (lw-rational-power (/ real-radius) (+ 2 index))) real-error)))
           (<= (lw-euler-window-quadratic-radius height ceiling numerator denominator index error)
               (lw-euler-window-quadratic-tail-budget height ceiling numerator denominator index error
                 real-radius real-mass real-error)))
  :hints (("Goal"
           :use (lw-ewtb-weights-data
                 (:instance lw-positive-division-bound
                    (numerator numerator) (divisor denominator) (bound 1))
                 (:instance lw-complex-mellin-euler-coefficient-rational
                    (rate 252) (height 0) (index index))
                 (:instance lw-ewtb-window-mass (distance (- 252 (/ numerator denominator))) (mass (+ (* 8 ceiling) 10)) (index index))
                 (:instance lw-complex-mellin-euler-coefficient-rational
                    (rate 252) (height 0) (index (+ 1 index)))
                 (:instance lw-ewtb-window-mass (distance (- 252 (/ numerator denominator))) (mass (+ (* 8 ceiling) 10)) (index (+ 1 index)))
                 (:instance lw-complex-mellin-euler-coefficient-rational
                    (rate 252) (height 0) (index (+ 2 index)))
                 (:instance lw-ewtb-window-mass (distance (- 252 (/ numerator denominator))) (mass (+ (* 8 ceiling) 10)) (index (+ 2 index)))
                 (:instance lw-ewtb-tail-identity
                   (radius (- 252 (/ numerator denominator))) (mass (* (+ (* 8 ceiling) 10) (/ (- 252 (/ numerator denominator)))))
                   (first (lw-complex-l1 (lw-zeta-residue-denominator (cons 252 height)))) (second (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons 252 height))))))
                 (:instance lw-ewtb-tail-identity
                   (radius real-radius) (mass real-mass)
                   (first (lw-complex-l1 (lw-zeta-residue-denominator (cons 252 height)))) (second (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons 252 height))))))
                 (:instance lw-ewtb-multiply-order
                   (a (- (car (lw-complex-mellin-euler-coefficient-value 252 0 (+ 2 index) error)))) (b (+ (* real-mass (lw-rational-power (/ real-radius) (+ 2 index))) real-error)) (factor (lw-complex-l1 (lw-zeta-residue-denominator (cons 252 height)))))
                 (:instance lw-ewtb-multiply-order
                   (a (- (car (lw-complex-mellin-euler-coefficient-value 252 0 (+ 1 index) error)))) (b (+ (* real-mass (lw-rational-power (/ real-radius) (+ 1 index))) real-error)) (factor (lw-complex-l1 (lw-complex-sub (cons 1 0) (lw-complex-scale 2 (cons 252 height)))))))
           :in-theory
           (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-window-quadratic-radius lw-euler-window-local-coefficient-radius
              lw-euler-window-coefficient-radius-at lw-euler-window-mass
              lw-euler-window-quadratic-tail-budget lw-euler-window-weighted-tail
              lw-complexp lw-reciprocal-positive lw-rational-power-rational
              lw-ewtb-left-commutes lw-ewtb-left-distributes lw-ewtb-fold-constants
              lw-ewtb-times-negative lw-ewtb-negative-times lw-ewtb-zero-times
              lw-ewtb-minus-one lw-ewtb-double-negative lw-ewtb-add-cancel lw-ewtb-double lw-ewtb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :nonlinearp t
           :do-not-induct t))
  :rule-classes nil)
