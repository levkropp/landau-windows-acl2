(in-package "ACL2")

(include-book "euler-near-real-clearance")
(include-book "euler-right-clearance")

; A sufficiently small sample in a real-centered disk has a positive
; separation between its horizontal displacement and the circle radius.

(local (defthm lw-erg-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-erg-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-erg-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-erg-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-erg-times-negative (a b) (b a)))
                 :in-theory (disable lw-erg-times-negative)))))

(local (defthm lw-erg-zero-times (equal (* 0 a) 0)))

(local (defthm lw-erg-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-erg-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-erg-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-erg-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-erg-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-erg-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-erg-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erg-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-erg-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-erg-left-commutes)))))

(local (deftheory lw-erg-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-erg-left-commutes lw-erg-left-distributes lw-erg-fold-constants
              lw-erg-times-negative lw-erg-negative-times lw-erg-zero-times
              lw-erg-minus-one lw-erg-double-negative lw-erg-add-cancel lw-erg-double lw-erg-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-real-circle-probe-request (outer-radius gap)
  (min (lw-euler-right-floor (+ 1 gap)) (min (lw-euler-near-real-request (- 252 outer-radius)) (* 1/16 (lw-euler-real-axis-floor (- 252 outer-radius))))))

(defthm lw-euler-real-circle-probe-request-data
  (implies (and (rationalp outer-radius) (< outer-radius 252)
                (rationalp gap) (< 0 gap))
           (and (rationalp (lw-euler-real-circle-probe-request outer-radius gap)) (< 0 (lw-euler-real-circle-probe-request outer-radius gap))
                (<= (lw-euler-real-circle-probe-request outer-radius gap) (lw-euler-right-floor (+ 1 gap))) (<= (lw-euler-real-circle-probe-request outer-radius gap) (lw-euler-near-real-request (- 252 outer-radius)))
                (<= (lw-euler-real-circle-probe-request outer-radius gap) (* 1/16 (lw-euler-real-axis-floor (- 252 outer-radius))))))
  :hints (("Goal"
           :use ((:instance lw-euler-right-floor-data (rate (+ 1 gap)))
                 (:instance lw-euler-real-axis-budget-data (lower (- 252 outer-radius)))
                 (:instance lw-euler-near-real-request-data (lower (- 252 outer-radius))))
           :in-theory (union-theories '(lw-euler-real-circle-probe-request min) (theory 'lw-erg-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-erg-square-order
   (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= a b))
            (<= (* a a) (* b b)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-erg-strict-square
   (implies (and (rationalp a) (<= 0 a) (rationalp b) (< a b))
            (< (* a a) (* b b)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-erg-sample-small-excludes-near-real
   (implies (and (rationalp outer-radius) (< outer-radius 252)
                 (rationalp cap) (<= 0 cap) (< cap outer-radius)
                 (rationalp gap) (< 0 gap) (lw-complex-diskp offset cap)
                 (rationalp error) (< 0 error) (<= error (lw-euler-real-circle-probe-request outer-radius gap))
                 (lw-complex-diskp (lw-complex-euler-continuation-value (+ 252 (car offset)) (cdr offset) error) (lw-euler-real-circle-probe-request outer-radius gap)))
            (< (lw-euler-near-real-radius 252 outer-radius cap) (abs (cdr offset))))
   :hints (("Goal"
            :use (lw-euler-real-circle-probe-request-data
                  (:instance lw-complex-disk-data (point offset) (radius cap))
                  (:instance lw-complex-disk-coordinates (point offset) (radius cap))
                  (:instance lw-euler-real-axis-budget-data (lower (- 252 outer-radius)))
                  (:instance lw-complex-euler-near-real-clearance (rate 252) (radius cap) (point-rate (+ 252 (car offset))) (height (cdr offset)))
                  (:instance lw-complex-disk-norm-square (point (lw-complex-euler-continuation-value (+ 252 (car offset)) (cdr offset) error)) (radius (lw-euler-real-circle-probe-request outer-radius gap)))
                  (:instance lw-erg-strict-square (a (lw-euler-real-circle-probe-request outer-radius gap)) (b (* 1/8 (lw-euler-real-axis-floor (- 252 outer-radius))))))
            :in-theory (union-theories '(lw-complexp) (theory 'lw-erg-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-erg-sample-small-excludes-right
   (implies (and (rationalp outer-radius) (< outer-radius 252)
                 (rationalp gap) (< 0 gap) (lw-complexp offset)
                 (rationalp error) (< 0 error) (<= error (lw-euler-real-circle-probe-request outer-radius gap))
                 (lw-complex-diskp (lw-complex-euler-continuation-value (+ 252 (car offset)) (cdr offset) error) (lw-euler-real-circle-probe-request outer-radius gap)))
            (< (+ 252 (car offset)) (+ 1 gap)))
   :hints (("Goal"
            :use (lw-euler-real-circle-probe-request-data
                  (:instance lw-complex-euler-right-uniform-clearance (lower (+ 1 gap)) (rate (+ 252 (car offset))) (height (cdr offset)))
                  (:instance lw-complex-disk-enlarge (point (lw-complex-euler-continuation-value (+ 252 (car offset)) (cdr offset) error)) (radius (lw-euler-real-circle-probe-request outer-radius gap)) (cap (lw-euler-right-floor (+ 1 gap))))
                  (:instance lw-euler-right-floor-data (rate (+ 1 gap))))
            :in-theory (union-theories '(lw-complexp) (theory 'lw-erg-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-erg-radial-gap-square
   (implies (and (rationalp x) (<= 0 x) (<= x 252)
                 (rationalp gap) (< 0 gap) (<= gap 1/4))
            (< (* (+ x (* 8 gap)) (+ x (* 8 gap)))
               (+ (* x x) (* 8192 gap))))
   :hints (("Goal"
            :use ((:instance lw-erg-multiply-order (a x) (b 252) (factor (* 16 gap)))
                  (:instance lw-erg-multiply-order (a gap) (b 1/4) (factor (* 64 gap))))
            :in-theory (theory 'lw-erg-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-erg-radial-separation
   (implies (and (rationalp x) (<= 0 x) (<= x 252)
                 (rationalp y) (rationalp radius) (<= 0 radius)
                 (<= (+ (* x x) (* y y)) (* radius radius))
                 (rationalp delta) (< 0 delta) (< delta (abs y))
                 (rationalp gap) (< 0 gap) (<= gap 1/4)
                 (<= (* 8192 gap) (* delta delta)))
            (< (+ x (* 8 gap)) radius))
   :hints (("Goal"
            :use (lw-erg-radial-gap-square
                  (:instance lw-erg-strict-square (a delta) (b (abs y)))
                  (:instance lw-erg-square-order (a radius) (b (+ x (* 8 gap)))))
            :in-theory (union-theories '(abs) (theory 'lw-erg-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-real-circle-small-probe-geometry
  (implies (and (rationalp outer-radius) (< outer-radius 252)
                (rationalp cap) (<= 0 cap) (< cap outer-radius)
                (rationalp radius) (<= radius cap) (lw-complex-diskp offset radius)
                (rationalp gap) (< 0 gap) (<= gap 1/4)
                (<= (* 8192 gap) (* (lw-euler-near-real-radius 252 outer-radius cap) (lw-euler-near-real-radius 252 outer-radius cap)))
                (rationalp error) (< 0 error) (<= error (lw-euler-real-circle-probe-request outer-radius gap))
                (lw-complex-diskp (lw-complex-euler-continuation-value (+ 252 (car offset)) (cdr offset) error) (lw-euler-real-circle-probe-request outer-radius gap)))
           (and (< (lw-euler-near-real-radius 252 outer-radius cap) (abs (cdr offset)))
                (< (- 251 gap) (- (car offset)))
                (< (+ (- (car offset)) (* 8 gap)) radius)
                (< (+ 251 (* 7 gap)) radius)))
  :hints (("Goal"
           :use (lw-euler-real-circle-probe-request-data
                 (:instance lw-euler-near-real-radius-positive (rate 252) (radius cap))
                 (:instance lw-complex-disk-data (point offset))
                 (:instance lw-complex-disk-enlarge (point offset) (cap cap))
                 (:instance lw-complex-disk-coordinates (point offset))
                 (:instance lw-complex-disk-norm-square (point offset))
                 lw-erg-sample-small-excludes-near-real lw-erg-sample-small-excludes-right
                 (:instance lw-erg-radial-separation (x (- (car offset))) (y (cdr offset)) (delta (lw-euler-near-real-radius 252 outer-radius cap))))
           :in-theory (union-theories '(lw-complexp lw-complex-norm-square abs) (theory 'lw-erg-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
