(in-package "ACL2")

(include-book "zeta-tails")
(include-book "dirichlet-finite-cauchy")

; A common, finer auxiliary family compares independently computed zeta
; partial sums at different counts. Both coefficient modes are explicit.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-reciprocal lw-complex-norm-square
                 lw-complex-l1 lw-rational-power lw-complex-exp-value lw-complex-exp-cap
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-log-bounds
                 lw-complex-laplace-point lw-complex-laplace-shifted-value
                 lw-complex-laplace-shifted-grid lw-complex-mul-subtract
                 lw-complex-mul-commutative lw-complex-mul-left-commutes
                 lw-exp-bounds lw-exp-neg-bounds lw-exp-index lw-exp-band lw-exp-sum lw-exp-term
                 lw-damped-phase-sample lw-phase-value
                 lw-complex-exp-integral-value lw-complex-exp-integral-grid
                 lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-disk-enlarge lw-disk-enlarge lw-precision-fuel)))

(local (in-theory
 (disable lw-complex-log-ramp-start lw-complex-log-ramp-cap
          lw-complex-log-ramp-independent-exp lw-complex-log-ramp-independent-endpoint
          lw-complex-log-ramp-independent-model
          lw-complex-log-ramp-independent-model-identity
          lw-smoothed-ramp-log-error lw-smoothed-ramp-unit-error lw-mangoldt-bounds
          lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-zfc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-zfc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-zfc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-zfc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-zfc-times-negative (a b) (b a)))
                 :in-theory (disable lw-zfc-times-negative)))))

(local (defthm lw-zfc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-zfc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-zfc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-zfc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-zfc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-zfc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-zfc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-zfc-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zfc-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-zfc-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-zfc-left-commutes)))))

(local (in-theory
 (disable lw-dirichlet-cubic-cost lw-dirichlet-cubic-node-cost
          lw-complex-zeta-partial-sum lw-complex-zeta-finite-value
          lw-dirichlet-finite-model-precision lw-dirichlet-finite-coefficient-precision
          lw-dirichlet-finite-node-precision lw-dirichlet-finite-precisions-valid
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (defthm lw-zfc-count-mass-data
 (implies (natp count)
  (and (rationalp (* count (+ 1 count))) (<= 0 (* count (+ 1 count)))))
 :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (in-theory (disable lw-dirichlet-tail-node-precision)))

(defun lw-complex-zeta-tail-value (logp rate height count total error)
 (lw-complex-zeta-partial-sum logp rate height count total
  (lw-dirichlet-finite-model-precision rate height error)
  (lw-dirichlet-finite-coefficient-precision total error)
  (lw-dirichlet-tail-node-precision rate height total error)))

(local (in-theory (disable lw-complex-zeta-tail-value lw-dirichlet-tail-precisions-valid)))

(local (defthm lw-zfc-prefix-budget
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height)
       (natp count) (natp total) (<= count total) (rationalp error) (< 0 error))
  (<= (+ (* (* 2 (+ rate (abs height))) 1/16
            (lw-dirichlet-finite-model-precision rate height error))
         (* 16 (* count (+ 1 count))
            (lw-dirichlet-tail-node-precision rate height total error))
         (* 2 count (lw-dirichlet-finite-coefficient-precision total error)))
      error))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-tail-precisions-valid (count total))
        (:instance lw-zfc-multiply-order
         (a (* count (+ 1 count))) (b (* total (+ 1 total)))
         (factor (* 16 (lw-dirichlet-tail-node-precision rate height total error))))
        (:instance lw-zfc-multiply-order (a count) (b total)
         (factor (* 2 (lw-dirichlet-finite-coefficient-precision total error)))))
  :nonlinearp t :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zfc-tail-rational
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height) (natp count) (natp total)
       (rationalp error) (< 0 error))
  (lw-complexp (lw-complex-zeta-tail-value logp rate height count total error)))
 :hints (("Goal"
  :use ((:instance lw-dirichlet-tail-precisions-valid (count total))
        (:instance lw-complex-zeta-partial-sum-rational
         (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision total error)) (delta (lw-dirichlet-tail-node-precision rate height total error))))
  :in-theory (e/d (lw-complex-zeta-tail-value)
                  (lw-complex-zeta-partial-sum-rational))
  :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zfc-prefix-comparison
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height)
       (natp count) (natp total) (<= count total)
       (rationalp error) (< 0 error) (rationalp finite-error) (< 0 finite-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-tail-value logp rate height count total error) (lw-complex-zeta-finite-value logp rate height count finite-error))
                    (+ error finite-error)))
 :hints (("Goal"
  :use (lw-zfc-prefix-budget
        (:instance lw-dirichlet-tail-precisions-valid (count total))
        (:instance lw-complex-zeta-partial-sum-finite-comparison
         (model-error (lw-dirichlet-finite-model-precision rate height error)) (primitive-error (lw-dirichlet-finite-coefficient-precision total error)) (delta (lw-dirichlet-tail-node-precision rate height total error)) (error finite-error))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-zeta-partial-sum logp rate height count total (lw-dirichlet-finite-model-precision rate height error) (lw-dirichlet-finite-coefficient-precision total error) (lw-dirichlet-tail-node-precision rate height total error)) (lw-complex-zeta-finite-value logp rate height count finite-error)))
         (radius (+ (* (* 2 (+ rate (abs height))) 1/16 (lw-dirichlet-finite-model-precision rate height error)) (* 16 (* count (+ 1 count)) (lw-dirichlet-tail-node-precision rate height total error)) (* 2 count (lw-dirichlet-finite-coefficient-precision total error)) finite-error)) (cap (+ error finite-error))))
  :in-theory (e/d (lw-complex-zeta-tail-value)
                  (lw-complex-zeta-partial-sum-finite-comparison))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zfc-auxiliary-tail
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height)
       (posp start) (natp count) (<= start count) (rationalp error) (< 0 error))
  (lw-complex-diskp
   (lw-complex-sub (lw-complex-zeta-tail-value logp rate height count count error) (lw-complex-zeta-tail-value logp rate height start count error))
   (+ (* 2 (/ start)) error)))
 :hints (("Goal"
  :use (lw-dirichlet-tail-precisions-valid
        (:instance lw-complex-zeta-uniform-tail (total count)
         (model-error (lw-dirichlet-finite-model-precision rate height error))
         (primitive-error (lw-dirichlet-finite-coefficient-precision count error))
         (error (lw-dirichlet-tail-node-precision rate height count error)))
        (:instance lw-complex-disk-enlarge
         (point (lw-complex-sub (lw-complex-zeta-tail-value logp rate height count count error) (lw-complex-zeta-tail-value logp rate height start count error)))
         (radius (+ (* 2 (/ start))
                    (* (lw-dirichlet-cubic-cost rate height count)
                       (lw-dirichlet-tail-node-precision rate height count error))
                    (* 3/8 (lw-dirichlet-finite-model-precision rate height error))))
         (cap (+ (* 2 (/ start)) error))))
  :in-theory (e/d (lw-complex-zeta-tail-value)
                  (lw-complex-zeta-uniform-tail))
  :nonlinearp nil :do-not-induct t))
 :rule-classes nil))

(local (defthm lw-zfc-four-point
 (implies
  (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
       (lw-complex-diskp (lw-complex-sub b a) ra)
       (lw-complex-diskp (lw-complex-sub b c) rb)
       (lw-complex-diskp (lw-complex-sub c d) rc))
  (lw-complex-diskp (lw-complex-sub a d) (+ (+ ra rb) rc)))
 :hints (("Goal"
  :use ((:instance lw-complex-difference-symmetric (left b) (right a) (radius ra))
        (:instance lw-complex-difference-triangle
         (left a) (middle b) (right c) (radius ra) (other-radius rb))
        (:instance lw-complex-difference-triangle
         (left a) (middle c) (right d) (radius (+ ra rb)) (other-radius rc)))
  :in-theory (disable lw-complex-difference-triangle)
  :do-not-induct t))
 :rule-classes nil))

(defthm lw-complex-zeta-finite-value-truncation-cauchy
 (implies
  (and (rationalp rate) (< 3 rate) (rationalp height)
       (posp start) (natp count) (<= start count)
       (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
  (lw-complex-diskp (lw-complex-sub (lw-complex-zeta-finite-value logp rate height count left-error) (lw-complex-zeta-finite-value logp rate height start right-error))
   (+ (* 2 (/ start)) (* 4 (+ left-error right-error)))))
 :hints (("Goal"
  :use ((:instance lw-zfc-tail-rational (total count) (error (+ left-error right-error)))
        (:instance lw-zfc-tail-rational (count start) (total count) (error (+ left-error right-error)))
        (:instance lw-complex-zeta-finite-value-rational (error left-error))
        (:instance lw-complex-zeta-finite-value-rational (count start) (error right-error))
        (:instance lw-zfc-prefix-comparison (total count) (error (+ left-error right-error)) (finite-error left-error))
        (:instance lw-zfc-prefix-comparison (count start) (total count) (error (+ left-error right-error)) (finite-error right-error))
        (:instance lw-zfc-auxiliary-tail (error (+ left-error right-error)))
        (:instance lw-zfc-four-point (a (lw-complex-zeta-finite-value logp rate height count left-error)) (b (lw-complex-zeta-tail-value logp rate height count count (+ left-error right-error))) (c (lw-complex-zeta-tail-value logp rate height start count (+ left-error right-error))) (d (lw-complex-zeta-finite-value logp rate height start right-error))
         (ra (+ (+ left-error right-error) left-error)) (rb (+ (* 2 (/ start)) (+ left-error right-error))) (rc (+ (+ left-error right-error) right-error)))
        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-complex-zeta-finite-value logp rate height count left-error) (lw-complex-zeta-finite-value logp rate height start right-error)))
         (radius (+ (+ (+ (+ left-error right-error) left-error) (+ (* 2 (/ start)) (+ left-error right-error))) (+ (+ left-error right-error) right-error)))
         (cap (+ (* 2 (/ start)) (* 4 (+ left-error right-error))))))
  :in-theory (disable lw-complex-zeta-finite-value-rational)
  :nonlinearp nil :do-not-induct t)))

