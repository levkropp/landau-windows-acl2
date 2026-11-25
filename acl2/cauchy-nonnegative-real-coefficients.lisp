(in-package "ACL2")

(include-book "cauchy-real-part-moments")

; Use one sample count for the constant, the selected coefficient and
; the shifted positive-frequency sum.

(local (defthm lw-cnrc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cnrc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cnrc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cnrc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cnrc-times-negative (a b) (b a)))
                 :in-theory (disable lw-cnrc-times-negative)))))

(local (defthm lw-cnrc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cnrc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cnrc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cnrc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cnrc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cnrc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cnrc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cnrc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnrc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cnrc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cnrc-left-commutes)))))

(defun lw-cauchy-shifted-average (coefficients degree offset samples)
  (lw-complex-scale (/ samples)
   (lw-cauchy-evaluation-sum coefficients (lw-cauchy-orbit-rotation degree) 0 offset samples)))

(local
 (defthm lw-cnrc-scale-real
   (implies (and (lw-complexp point) (rationalp factor))
            (equal (car (lw-complex-scale factor point)) (* factor (car point))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-scale
              lw-cnrc-left-commutes lw-cnrc-left-distributes lw-cnrc-fold-constants
              lw-cnrc-times-negative lw-cnrc-negative-times lw-cnrc-zero-times
              lw-cnrc-minus-one lw-cnrc-double-negative lw-cnrc-add-cancel lw-cnrc-double lw-cnrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cnrc-reciprocal-type
   (implies (rationalp value) (rationalp (/ value)))
   :hints (("Goal" :in-theory (theory 'ground-zero)))))

(local
 (defthm lw-cnrc-real-average-disk
   (implies (and (lw-complex-coefficientsp coefficients) (natp degree) (natp target) (posp samples)
                 (lw-cauchy-nonnegative-real-check coefficients (lw-cauchy-orbit-rotation degree) samples))
            (lw-complex-diskp (lw-complex-add (lw-cauchy-polynomial-average coefficients degree target samples) (lw-complex-conjugate (lw-cauchy-shifted-average coefficients degree target samples))) (* 2 (car (lw-cauchy-polynomial-average coefficients degree 0 samples)))))
   :hints (("Goal"
            :use (lw-cauchy-orbit-data
                  (:instance lw-cnrc-reciprocal-type (value samples))
                  (:instance lw-cauchy-evaluation-sum-rational (point (lw-cauchy-orbit-rotation degree)) (count samples) (offset 0))
                  (:instance lw-cauchy-evaluation-sum-rational (point (lw-cauchy-orbit-rotation degree)) (count samples) (target 0) (offset target))
                  (:instance lw-cauchy-evaluation-sum-rational (point (lw-cauchy-orbit-rotation degree)) (count samples) (target 0) (offset 0))
                  (:instance lw-cauchy-real-part-sum-bound (point (lw-cauchy-orbit-rotation degree)))
                  (:instance lw-cauchy-real-part-sum-identity (point (lw-cauchy-orbit-rotation degree)))
                  (:instance lw-reciprocal-positive (value samples))
                  (:instance lw-complex-scale-disk (point (lw-cauchy-real-part-sum coefficients (lw-cauchy-orbit-rotation degree) target samples)) (factor (/ samples))
                    (radius (* 2 (car (lw-cauchy-evaluation-sum coefficients (lw-cauchy-orbit-rotation degree) 0 0 samples))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cauchy-polynomial-average lw-cauchy-shifted-average lw-cnrc-scale-real
              lw-complex-conjugate-rational lw-complex-scale-add lw-complex-conjugate-scale abs
              lw-cnrc-left-commutes lw-cnrc-left-distributes lw-cnrc-fold-constants
              lw-cnrc-times-negative lw-cnrc-negative-times lw-cnrc-zero-times
              lw-cnrc-minus-one lw-cnrc-double-negative lw-cnrc-add-cancel lw-cnrc-double lw-cnrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cnrc-shifted-to-moments
   (implies (and (lw-complex-coefficientsp coefficients) (natp degree) (natp target) (posp samples))
            (equal (lw-cauchy-shifted-average coefficients degree target samples) (lw-cauchy-moment-expansion coefficients degree 0 target samples)))
   :hints (("Goal"
            :use (lw-cauchy-orbit-data
                  (:instance lw-cauchy-evaluation-sum-expansion (point (lw-cauchy-orbit-rotation degree))
                    (target 0) (offset target) (count samples))
                  (:instance lw-cauchy-scaled-expansion (target 0) (offset target) (count samples)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cauchy-shifted-average
              lw-cnrc-left-commutes lw-cnrc-left-distributes lw-cnrc-fold-constants
              lw-cnrc-times-negative lw-cnrc-negative-times lw-cnrc-zero-times
              lw-cnrc-minus-one lw-cnrc-double-negative lw-cnrc-add-cancel lw-cnrc-double lw-cnrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cnrc-shifted-average-small
   (implies (and (lw-complex-coefficientsp coefficients) (natp degree) (posp target)
                 (<= (+ target (len coefficients)) (+ 1 degree))
                 (rationalp error) (< 0 error))
            (lw-complex-diskp
             (lw-cauchy-shifted-average coefficients degree target
               (lw-cauchy-coefficient-count coefficients degree error)) error))
   :hints (("Goal"
            :use (lw-cauchy-coefficient-count-natural lw-cauchy-coefficient-precision-adequate
                  (:instance lw-cnrc-shifted-to-moments (samples (lw-cauchy-coefficient-count coefficients degree error)))
                  (:instance lw-cauchy-moment-expansion-rational (target 0) (offset target) (count (lw-cauchy-coefficient-count coefficients degree error)))
                  (:instance lw-complex-coefficient-at-below-offset (target 0) (offset target))
                  (:instance lw-cauchy-residual-expansion-identity (target 0) (offset target)
                    (count (lw-cauchy-coefficient-count coefficients degree error)))
                  (:instance lw-cauchy-residual-expansion-bound (target 0) (offset target)
                    (error (lw-cauchy-coefficient-precision coefficients error)))
                  (:instance lw-complex-sub-zero (point (lw-cauchy-moment-expansion coefficients degree 0 target (lw-cauchy-coefficient-count coefficients degree error))))
                  (:instance lw-complex-disk-enlarge
                    (point (lw-cauchy-shifted-average coefficients degree target (lw-cauchy-coefficient-count coefficients degree error)))
                    (radius (* (lw-complex-coefficient-mass coefficients) (lw-cauchy-coefficient-precision coefficients error))) (cap error)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cauchy-coefficient-count
              lw-cnrc-left-commutes lw-cnrc-left-distributes lw-cnrc-fold-constants
              lw-cnrc-times-negative lw-cnrc-negative-times lw-cnrc-zero-times
              lw-cnrc-minus-one lw-cnrc-double-negative lw-cnrc-add-cancel lw-cnrc-double lw-cnrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cnrc-add-sub
   (implies (and (lw-complexp average) (lw-complexp offset))
            (equal (lw-complex-sub (lw-complex-add average offset) average) offset))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-add lw-complex-sub
              lw-cnrc-left-commutes lw-cnrc-left-distributes lw-cnrc-fold-constants
              lw-cnrc-times-negative lw-cnrc-negative-times lw-cnrc-zero-times
              lw-cnrc-minus-one lw-cnrc-double-negative lw-cnrc-add-cancel lw-cnrc-double lw-cnrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))))

(local
 (defthm lw-cnrc-compose-estimates
   (implies (and (lw-complexp coefficient) (lw-complexp average)
                 (lw-complex-diskp (lw-complex-sub average coefficient) error)
                 (lw-complex-diskp offset error)
                 (lw-complex-diskp (lw-complex-add average offset) cap))
            (lw-complex-diskp coefficient (+ cap (* 2 error))))
   :hints (("Goal"
            :use ((:instance lw-complex-disk-data (point offset) (radius error))
                  (:instance lw-complex-disk-data (point (lw-complex-add average offset)) (radius cap))
                  (:instance lw-complex-difference-symmetric (left average) (right coefficient) (radius error))
                  (:instance lw-complex-difference-symmetric (left (lw-complex-add average offset)) (right average) (radius error))
                  (:instance lw-complex-difference-triangle
                    (left coefficient) (middle average) (right (lw-complex-add average offset))
                    (radius error) (other-radius error))
                  (:instance lw-complex-sub-zero (point (lw-complex-add average offset)))
                  (:instance lw-complex-sub-zero (point coefficient))
                  (:instance lw-complex-difference-triangle
                    (left coefficient) (middle (lw-complex-add average offset)) (right (cons 0 0))
                    (radius (* 2 error)) (other-radius cap)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-cnrc-add-sub
              lw-cnrc-left-commutes lw-cnrc-left-distributes lw-cnrc-fold-constants
              lw-cnrc-times-negative lw-cnrc-negative-times lw-cnrc-zero-times
              lw-cnrc-minus-one lw-cnrc-double-negative lw-cnrc-add-cancel lw-cnrc-double lw-cnrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cnrc-real-difference
   (implies (and (lw-complexp left) (lw-complexp right))
            (and (rationalp (car left)) (rationalp (car right))
                 (equal (car (lw-complex-sub left right)) (- (car left) (car right)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-complexp lw-complex-sub
              lw-cnrc-left-commutes lw-cnrc-left-distributes lw-cnrc-fold-constants
              lw-cnrc-times-negative lw-cnrc-negative-times lw-cnrc-zero-times
              lw-cnrc-minus-one lw-cnrc-double-negative lw-cnrc-add-cancel lw-cnrc-double lw-cnrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not-induct t))
   :rule-classes nil))

(defthm lw-cauchy-nonnegative-real-coefficient-cap
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (posp target) (< target (len coefficients))
                (<= (+ target (len coefficients)) (+ 1 degree))
                (rationalp error) (< 0 error)
                (lw-cauchy-nonnegative-real-check coefficients (lw-cauchy-orbit-rotation degree) (lw-cauchy-coefficient-count coefficients degree error)))
           (lw-complex-diskp (nth target coefficients)
             (+ (* 2 (car (nth 0 coefficients))) (* 4 error))))
  :hints (("Goal"
           :use (lw-cauchy-coefficient-count-natural lw-cnrc-shifted-average-small
                 (:instance lw-cnrc-real-average-disk (samples (lw-cauchy-coefficient-count coefficients degree error)))
                 lw-cauchy-computed-coefficient-recovery
                 (:instance lw-cauchy-computed-coefficient-recovery (target 0))
                 (:instance lw-complex-coefficient-at-rational (offset 0))
                 (:instance lw-complex-coefficient-at-rational (offset 0) (target 0))
                 (:instance lw-complex-coefficient-at-nth (offset 0))
                 (:instance lw-complex-coefficient-at-nth (offset 0) (target 0))
                 (:instance lw-cauchy-moment-expansion-rational (offset 0) (target 0) (count (lw-cauchy-coefficient-count coefficients degree error)))
                 (:instance lw-cauchy-moment-expansion-rational (offset 0) (count (lw-cauchy-coefficient-count coefficients degree error)))
                 (:instance lw-cauchy-polynomial-average-moments (count (lw-cauchy-coefficient-count coefficients degree error)))
                 (:instance lw-cauchy-polynomial-average-moments (count (lw-cauchy-coefficient-count coefficients degree error)) (target 0))
                 (:instance lw-complex-disk-coordinates
                   (point (lw-complex-sub (lw-cauchy-polynomial-average coefficients degree 0 (lw-cauchy-coefficient-count coefficients degree error)) (nth 0 coefficients))) (radius error))
                 (:instance lw-cnrc-real-difference (left (lw-cauchy-polynomial-average coefficients degree 0 (lw-cauchy-coefficient-count coefficients degree error))) (right (nth 0 coefficients)))
                 (:instance lw-complex-conjugate-disk (point (lw-cauchy-shifted-average coefficients degree target (lw-cauchy-coefficient-count coefficients degree error))) (radius error))
                 (:instance lw-cnrc-compose-estimates
                   (coefficient (nth target coefficients)) (average (lw-cauchy-polynomial-average coefficients degree target (lw-cauchy-coefficient-count coefficients degree error)))
                   (offset (lw-complex-conjugate (lw-cauchy-shifted-average coefficients degree target (lw-cauchy-coefficient-count coefficients degree error)))) (cap (* 2 (car (lw-cauchy-polynomial-average coefficients degree 0 (lw-cauchy-coefficient-count coefficients degree error))))))
                 (:instance lw-complex-disk-enlarge (point (nth target coefficients))
                   (radius (+ (* 2 (car (lw-cauchy-polynomial-average coefficients degree 0 (lw-cauchy-coefficient-count coefficients degree error)))) (* 2 error))) (cap (+ (* 2 (car (nth 0 coefficients))) (* 4 error)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              abs
              lw-cnrc-left-commutes lw-cnrc-left-distributes lw-cnrc-fold-constants
              lw-cnrc-times-negative lw-cnrc-negative-times lw-cnrc-zero-times
              lw-cnrc-minus-one lw-cnrc-double-negative lw-cnrc-add-cancel lw-cnrc-double lw-cnrc-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
