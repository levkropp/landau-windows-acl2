(in-package "ACL2")

(include-book "mellin-cutoffs")

; A cutoff chosen at a lower abscissa dominates every shifted default
; cutoff. This lets one finite grid use the existing arithmetic tail bound.

(local (in-theory
        (disable lw-ceiling-rational lw-ceiling-loop lw-precision-fuel
                 lw-rational-power lw-mellin-tail-coefficient lw-mellin-tail-cutoff lw-mellin-integral-cutoff
                 lw-mellin-integral lw-mellin-bounded-integral
                 lw-mellin-cutoff-prefix lw-mellin-cutoff-tail
                 lw-mellin-cutoff-mesh lw-mellin-cutoff-precision lw-mellin-mesh-depth
                 lw-mellin-integral-depth lw-mellin-integral-precision lw-halved-width
                 lw-mellin-spatial-slope lw-mellin-spatial-error-factor
                 lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope
                 lw-kernel-spatial-cap lw-kernel-spatial-slope lw-exp-lipschitz-cap lw-log-signal-bounds
                 lw-complexp lw-complex-diskp lw-complex-add lw-complex-sub lw-complex-scale
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mco-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mco-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mco-product-nonnegative
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mco-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-ceiling-rational-monotone
  (implies (and (rationalp left) (rationalp right) (<= 0 left) (<= left right))
           (<= (lw-ceiling-rational left) (lw-ceiling-rational right)))
  :hints (("Goal" :use ((:instance lw-ceiling-rational-bracket (value left))
                        (:instance lw-ceiling-rational-bracket (value right)))
                  :in-theory (disable lw-ceiling-rational-bracket))))

(defthm lw-mellin-tail-coefficient-antitone-rate
  (implies (and (rationalp left) (< 0 left) (rationalp right) (<= left right)
                (natp index) (rationalp mass) (<= 0 mass))
           (<= (lw-mellin-tail-coefficient right index mass)
               (lw-mellin-tail-coefficient left index mass)))
  :hints (("Goal" :use (
    lw-reciprocal-antitone
    (:instance lw-rational-power-monotone-base (left (/ right)) (right (/ left)) (exponent (+ 2 index)))
    (:instance lw-mco-product-nonnegative (a mass) (b (* (+ 1 index) (+ 2 index))))
    (:instance lw-mco-multiply-order
      (a (lw-rational-power (/ right) (+ 2 index))) (b (lw-rational-power (/ left) (+ 2 index)))
      (factor (* mass (+ 1 index) (+ 2 index)))))
    :in-theory (e/d (lw-mellin-tail-coefficient)
                    (lw-reciprocal-antitone lw-rational-power-monotone-base))
    :nonlinearp t)))

(defthm lw-mellin-tail-cutoff-antitone-rate
  (implies (and (rationalp left) (< 0 left) (rationalp right) (<= left right)
                (natp index) (rationalp mass) (<= 0 mass) (rationalp error) (< 0 error))
           (<= (lw-mellin-tail-cutoff right index mass error)
               (lw-mellin-tail-cutoff left index mass error)))
  :hints (("Goal" :use (
    lw-reciprocal-antitone lw-mellin-tail-coefficient-antitone-rate
    (:instance lw-mellin-tail-coefficient-nonnegative (rate left))
    (:instance lw-mellin-tail-coefficient-nonnegative (rate right))
    (:instance lw-mco-multiply-order (a (/ right)) (b (/ left)) (factor (+ 2 index)))
    (:instance lw-mco-multiply-order
      (a (lw-mellin-tail-coefficient right index mass))
      (b (lw-mellin-tail-coefficient left index mass)) (factor (/ 2 error)))
    (:instance lw-ceiling-rational-monotone
      (left (/ (* 2 (lw-mellin-tail-coefficient right index mass)) error))
      (right (/ (* 2 (lw-mellin-tail-coefficient left index mass)) error))))
    :in-theory (e/d (lw-mellin-tail-cutoff)
                    (lw-reciprocal-antitone lw-mellin-tail-coefficient-antitone-rate
                     lw-mellin-tail-coefficient-nonnegative lw-ceiling-rational-monotone))
    :nonlinearp t)))

(defthm lw-mellin-integral-cutoff-antitone-abscissa
  (implies (and (rationalp left) (< 2 left) (rationalp right) (<= left right)
                (natp index) (rationalp error) (< 0 error))
           (<= (lw-mellin-integral-cutoff right index error)
               (lw-mellin-integral-cutoff left index error)))
  :hints (("Goal" :use ((:instance lw-mellin-tail-cutoff-antitone-rate
                          (left (- left 2)) (right (- right 2)) (mass 4)))
                  :in-theory (e/d (lw-mellin-integral-cutoff) (lw-mellin-tail-cutoff-antitone-rate)))))


(local (defthm lw-mco-half-half
         (implies (rationalp value) (equal (* 1/2 1/2 value) (* 1/4 value)))
         :hints (("Goal" :use ((:instance associativity-of-* (x 1/2) (y 1/2) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mco-left-commutes)))))

(local (defthm lw-mco-prefix-tail-identity
         (implies (and (lw-complexp prefix) (lw-complexp tail) (lw-complexp small))
                  (equal (lw-complex-sub (lw-complex-add prefix tail) small)
                         (lw-complex-add (lw-complex-sub prefix small) tail)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(local (defthm lw-mco-three-term-bound
         (implies (and (lw-complexp big) (lw-complexp small) (lw-complexp prefix) (lw-complexp tail)
                       (lw-complex-diskp (lw-complex-sub big (lw-complex-add prefix tail)) big-error)
                       (lw-complex-diskp (lw-complex-sub prefix small) small-error)
                       (lw-complex-diskp tail tail-error))
                  (lw-complex-diskp (lw-complex-sub big small) (+ big-error small-error tail-error)))
         :hints (("Goal" :use ((:instance lw-complex-add-disk
                                 (left (lw-complex-sub prefix small)) (radius small-error)
                                 (right tail) (other-radius tail-error))
                               (:instance lw-complex-difference-triangle
                                 (left big) (middle (lw-complex-add prefix tail)) (right small)
                                 (radius big-error) (other-radius (+ small-error tail-error))))
                         :in-theory (disable lw-complex-add-disk lw-complex-difference-triangle)))
         :rule-classes nil))

(defthm lw-mellin-bounded-above-cutoff-comparison
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (rationalp integral-error) (< 0 integral-error)
                (rationalp bounded-error) (< 0 bounded-error) (rationalp cap) (<= (lw-mellin-integral-cutoff sigma index integral-error) cap))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-bounded-integral cap sigma height index bounded-error)
               (lw-mellin-integral sigma height index integral-error))
             (* 5 (+ bounded-error integral-error))))
  :hints (("Goal" :use (
    (:instance lw-mellin-integral-cutoff-valid (error integral-error))
    (:instance lw-mellin-integral-rational (error integral-error))
    (:instance lw-mellin-bounded-integral-rational (error bounded-error))
    (:instance lw-mellin-cutoff-refinement-rational
      (cut (lw-mellin-integral-cutoff sigma index integral-error))
      (error (+ bounded-error integral-error)))
    (:instance lw-mellin-bounded-split-refinement
      (cut (lw-mellin-integral-cutoff sigma index integral-error))
      (error bounded-error)
      (refinement-error (+ bounded-error integral-error)))
    (:instance lw-mellin-bounded-prefix-refinement
      (cut (lw-mellin-integral-cutoff sigma index integral-error))
      (error (* 1/2 integral-error))
      (refinement-error (+ bounded-error integral-error)))
    (:instance lw-mellin-refined-tail-at-integral-cutoff
      (cutoff-error integral-error)
      (error (+ bounded-error integral-error)))
    (:instance lw-mco-three-term-bound
      (big (lw-mellin-bounded-integral cap sigma height index bounded-error))
      (small (lw-mellin-integral sigma height index integral-error))
      (prefix
        (lw-mellin-cutoff-prefix
          cap
          (lw-mellin-integral-cutoff sigma index integral-error)
          sigma
          height
          index
          (+ bounded-error integral-error)))
      (tail
        (lw-mellin-cutoff-tail
          cap
          (lw-mellin-integral-cutoff sigma index integral-error)
          sigma
          height
          index
          (+ bounded-error integral-error)))
      (big-error (+ (* 1/2 bounded-error) (* 1/8 (+ bounded-error integral-error))))
      (small-error (+ (* 1/4 integral-error) (* 1/8 (+ bounded-error integral-error))))
      (tail-error (* 17/4 integral-error)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-bounded-integral cap sigma height index bounded-error)
          (lw-mellin-integral sigma height index integral-error)))
      (radius
        (+
          (+ (* 1/2 bounded-error) (* 1/8 (+ bounded-error integral-error)))
          (+ (* 1/4 integral-error) (* 1/8 (+ bounded-error integral-error)))
          (* 17/4 integral-error)))
      (cap (* 5 (+ bounded-error integral-error)))))
    :in-theory (e/d (lw-mellin-integral)
                    (lw-mellin-integral-cutoff-valid lw-mellin-integral-rational
                     lw-mellin-bounded-integral-rational lw-mellin-cutoff-refinement-rational
                     lw-mellin-bounded-split-refinement lw-mellin-bounded-prefix-refinement
                     lw-mellin-refined-tail-at-integral-cutoff)))))

(assert-event
 (and (<= (lw-mellin-integral-cutoff 5 2 1/4) (lw-mellin-integral-cutoff 4 2 1/4))
      (<= (lw-ceiling-rational 7/3) (lw-ceiling-rational 10/3))))

