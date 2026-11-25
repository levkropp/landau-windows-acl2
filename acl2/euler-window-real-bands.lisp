(in-package "ACL2")

(include-book "euler-real-circle-checked-probe")
(include-book "euler-window-circle-cover")

; Scan narrow radius bands from 251 toward cap. The bands are disjoint
; and consecutive selected radii differ by less than the probe gap.

(local (defthm lw-ewrb-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewrb-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewrb-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewrb-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewrb-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewrb-times-negative)))))

(local (defthm lw-ewrb-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewrb-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewrb-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewrb-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewrb-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewrb-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewrb-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewrb-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewrb-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewrb-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewrb-left-commutes)))))

(local (deftheory lw-ewrb-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ewrb-left-commutes lw-ewrb-left-distributes lw-ewrb-fold-constants
              lw-ewrb-times-negative lw-ewrb-negative-times lw-ewrb-zero-times
              lw-ewrb-minus-one lw-ewrb-double-negative lw-ewrb-add-cancel lw-ewrb-double lw-ewrb-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-real-outer (cap) (* 1/2 (+ 252 cap)))

(defun lw-euler-window-real-gap (cap slack)
  (let ((width (lw-euler-near-real-radius 252 (lw-euler-window-real-outer cap) cap)))
    (min 1/4 (min (* 1/8192 width width)
                  (min (* 1/8 (- cap 251)) (* 1/8 slack))))))

(defun lw-euler-window-real-band-count (cap gap)
  (lw-ceiling-rational (* 4 (- cap (+ 251 (* 2 gap))) (/ gap))))

(defun lw-euler-window-real-band-step (cap gap)
  (/ (- cap (+ 251 (* 2 gap))) (+ 1 (lw-euler-window-real-band-count cap gap))))

(defun lw-euler-window-real-band (cap step remaining)
  (lw-euler-window-circle-cover 0 (- cap (* (+ 1 remaining) step)) (- cap (* (+ 1/2 remaining) step))))

(defthm lw-euler-window-real-gap-data
  (implies (and (rationalp cap) (< 251 cap) (< cap 252)
                (rationalp slack) (< 0 slack))
           (and (rationalp (lw-euler-window-real-outer cap)) (< cap (lw-euler-window-real-outer cap)) (< (lw-euler-window-real-outer cap) 252)
                (rationalp (lw-euler-window-real-gap cap slack)) (< 0 (lw-euler-window-real-gap cap slack)) (<= (lw-euler-window-real-gap cap slack) 1/4)
                (< (+ 251 (* 2 (lw-euler-window-real-gap cap slack))) cap) (<= (* 8 (lw-euler-window-real-gap cap slack)) slack)
                (<= (* 8192 (lw-euler-window-real-gap cap slack)) (* (lw-euler-near-real-radius 252 (lw-euler-window-real-outer cap) cap) (lw-euler-near-real-radius 252 (lw-euler-window-real-outer cap) cap)))))
  :hints (("Goal"
           :use ((:instance lw-euler-near-real-radius-positive (rate 252) (radius cap) (outer-radius (lw-euler-window-real-outer cap)))
                 (:instance lw-ewrb-positive-product (a (lw-euler-near-real-radius 252 (lw-euler-window-real-outer cap) cap)) (b (lw-euler-near-real-radius 252 (lw-euler-window-real-outer cap) cap))))
           :in-theory (union-theories '(lw-euler-window-real-gap lw-euler-window-real-outer min)
                                      (theory 'lw-ewrb-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-ewrb-step-arithmetic
   (implies (and (rationalp width) (< 0 width) (rationalp gap) (< 0 gap) (natp count)
                 (<= (* 4 width (/ gap)) count))
            (and (rationalp (/ width (+ 1 count))) (< 0 (/ width (+ 1 count)))
                 (<= (/ width (+ 1 count)) (* 1/4 gap))
                 (equal (* (+ 1 count) (/ width (+ 1 count))) width)))
   :hints (("Goal"
            :use ((:instance lw-ewrb-inverse-factor (divisor (+ 1 count)) (coefficient width))
                  (:instance lw-ewrb-inverse-factor (divisor gap) (coefficient (* 4 width)))
                  (:instance lw-reciprocal-positive (value (+ 1 count)))
                  (:instance lw-ewrb-positive-product (a width) (b (/ (+ 1 count))))
                  (:instance lw-ewrb-multiply-order (a (* 4 width (/ gap))) (b (+ 1 count)) (factor gap))
                  (:instance lw-positive-division-bound
                    (numerator width) (divisor (+ 1 count)) (bound (* 1/4 gap))))
            :in-theory (theory 'lw-ewrb-arithmetic)
            :do-not-induct t))
   :rule-classes nil))

(defthm lw-euler-window-real-band-step-data
  (implies (and (rationalp cap) (rationalp gap) (< 0 gap) (< (+ 251 (* 2 gap)) cap))
           (and (natp (lw-euler-window-real-band-count cap gap)) (rationalp (lw-euler-window-real-band-step cap gap)) (< 0 (lw-euler-window-real-band-step cap gap)) (<= (lw-euler-window-real-band-step cap gap) (* 1/4 gap))
                (equal (- cap (* (+ 1 (lw-euler-window-real-band-count cap gap)) (lw-euler-window-real-band-step cap gap))) (+ 251 (* 2 gap)))))
  :hints (("Goal"
           :use ((:instance lw-ceiling-rational-bracket (value (* 4 (- cap (+ 251 (* 2 gap))) (/ gap))))
                 (:instance lw-reciprocal-positive (value gap))
                 (:instance lw-ewrb-positive-product (a (- cap (+ 251 (* 2 gap)))) (b (/ gap)))
                 (:instance lw-ewrb-step-arithmetic (width (- cap (+ 251 (* 2 gap)))) (count (lw-euler-window-real-band-count cap gap))))
           :in-theory (union-theories '(lw-euler-window-real-band-count lw-euler-window-real-band-step
                                       (:type-prescription lw-ceiling-rational))
                                      (theory 'lw-ewrb-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-window-real-band-valid
  (implies (and (rationalp cap) (< cap 252) (rationalp step) (< 0 step)
                (natp remaining) (<= 0 (- cap (* (+ 1 remaining) step))))
           (let ((data (lw-euler-window-real-band cap step remaining)))
             (and (rationalp (car data)) (< (- cap (* (+ 1 remaining) step)) (car data)) (< (car data) (- cap (* (+ 1/2 remaining) step)))
                  (lw-euler-circle-coverp (cons 252 0) (car data) (cadr data) (caddr data)))))
  :hints (("Goal"
           :use ((:instance lw-euler-window-circle-cover-valid (height 0)
                   (lower (- cap (* (+ 1 remaining) step))) (upper (- cap (* (+ 1/2 remaining) step))))
                 (:instance lw-ewrb-positive-product (a (+ 1/2 remaining)) (b step)))
           :in-theory (union-theories '(lw-euler-window-real-band) (theory 'lw-ewrb-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
