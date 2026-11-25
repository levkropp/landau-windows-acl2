(in-package "ACL2")

(include-book "euler-window-ceiling-reduction")

; An encoded zero has arbitrarily accurate rational probes in a fixed
; disk. At the computed request, one such probe suffices for reduction.

(local (defthm lw-ewez-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewez-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewez-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewez-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewez-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewez-times-negative)))))

(local (defthm lw-ewez-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewez-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewez-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewez-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewez-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewez-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewez-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewez-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewez-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewez-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewez-left-commutes)))))

(local (deftheory lw-ewez-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ewez-left-commutes lw-ewez-left-distributes lw-ewez-fold-constants
              lw-ewez-times-negative lw-ewez-negative-times lw-ewez-zero-times
              lw-ewez-minus-one lw-ewez-double-negative lw-ewez-add-cancel lw-ewez-double lw-ewez-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-approximate-zerop (cap slack seed-height offset error)
  (and (rationalp error) (< 0 error)
       (lw-complex-diskp offset (- cap slack))
       (lw-complex-diskp (lw-complex-euler-continuation-value (+ 252 (car offset)) (+ seed-height (cdr offset)) error) error)))

(defthm lw-euler-window-approximate-zero-admitted
  (implies (and (rationalp cap) (< 251 cap) (< cap 252)
                (rationalp slack) (< 0 slack) (rationalp seed-height)
                (lw-euler-window-approximate-zerop cap slack seed-height offset error)
                (<= error (* 1/4 (lw-euler-window-zero-sample-request cap slack seed-height))))
           (lw-euler-window-small-samplep cap slack seed-height offset))
  :hints (("Goal"
           :use (lw-euler-window-prepared-circles-valid
                 (:instance lw-complex-disk-data (point offset) (radius (- cap slack)))
                 (:instance lw-complex-disk-coordinates (point offset) (radius (- cap slack)))
                 (:instance lw-complex-euler-continuation-value-rational (rate (+ 252 (car offset)))
                   (height (+ seed-height (cdr offset))) (error (* 1/4 (lw-euler-window-zero-sample-request cap slack seed-height))))
                 (:instance lw-complex-euler-continuation-value-rational (rate (+ 252 (car offset)))
                   (height (+ seed-height (cdr offset))))
                 (:instance lw-complex-euler-continuation-value-cauchy (rate (+ 252 (car offset)))
                   (height (+ seed-height (cdr offset))) (left-error (* 1/4 (lw-euler-window-zero-sample-request cap slack seed-height))) (right-error error))
                 (:instance lw-complex-difference-triangle
                   (left (lw-complex-euler-continuation-value (+ 252 (car offset)) (+ seed-height (cdr offset)) (* 1/4 (lw-euler-window-zero-sample-request cap slack seed-height)))) (middle (lw-complex-euler-continuation-value (+ 252 (car offset)) (+ seed-height (cdr offset)) error)) (right (cons 0 0))
                   (radius (+ (* 1/4 (lw-euler-window-zero-sample-request cap slack seed-height)) error)) (other-radius error))
                 (:instance lw-complex-disk-enlarge (point (lw-complex-euler-continuation-value (+ 252 (car offset)) (+ seed-height (cdr offset)) (* 1/4 (lw-euler-window-zero-sample-request cap slack seed-height)))) (radius (+ (* 1/4 (lw-euler-window-zero-sample-request cap slack seed-height)) error error))
                   (cap (lw-euler-window-zero-sample-request cap slack seed-height))))
           :in-theory (union-theories '(lw-euler-window-approximate-zerop lw-euler-window-small-samplep
                                       lw-complexp lw-complex-sub-zero abs)
                                      (theory 'lw-ewez-arithmetic))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-window-encoded-zero-reduction
  (implies
   (and (rationalp cap) (< 251 cap) (< cap (- 252 (/ numerator denominator)))
       (rationalp slack) (< 0 slack) (rationalp seed-height)
       (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
       (rationalp start) (<= (lw-euler-window-ceiling-threshold cap slack seed-height ceiling numerator denominator) start)
        (lw-euler-window-approximate-zerop cap slack seed-height offset error)
        (<= error (* 1/4 (lw-euler-window-zero-sample-request cap slack seed-height))))
   (let* ((found (lw-landau-window-search start ceiling numerator denominator))
          (address (lw-landau-window-address start ceiling found)))
     (and found (rationalp address) (<= start address)
          (<= (* address address) (* start start start))
          (< 0 (cadr found))
          (equal (cdr found) (lw-signal-bounds address ceiling numerator denominator 1/4)))))
  :hints (("Goal"
           :use (lw-euler-window-approximate-zero-admitted lw-euler-window-ceiling-reduction
                 (:instance lw-reciprocal-positive (value denominator))
                 (:instance lw-ewez-multiply-order (a 0) (b numerator) (factor (/ denominator))))
           :in-theory (theory 'lw-ewez-arithmetic)
           :do-not-induct t))
  :rule-classes nil)
