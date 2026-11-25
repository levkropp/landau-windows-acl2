(in-package "ACL2")

(include-book "euler-dirichlet-blocks")

; Exact connection between the computed Euler segments, dyadic blocks
; and the original common-precision zeta prefixes.

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

(local (in-theory
 (disable lw-log-bounds-nonnegative lw-log-bounds-lower-coarse
          lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data)))

(local (in-theory (disable lw-complex-euler-dirichlet-prefix
 lw-complex-euler-dirichlet-cell lw-complex-euler-cell-segment
 lw-complex-euler-dirichlet-block lw-euler-dirichlet-block-rounding
 lw-rational-power lw-complex-euler-dirichlet-prefix-telescope)))

(local (defthm lw-edt-add-zero
 (implies (lw-complexp point)
  (equal (lw-complex-add point (cons 0 0)) point))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(local (defthm lw-edt-double
 (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-edt-reassociate
 (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c))
  (equal (lw-complex-add (lw-complex-add a b) c)
         (lw-complex-add a (lw-complex-add c b))))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(defthm lw-complex-euler-cell-segment-telescope
 (implies (and (rationalp rate) (rationalp height)
               (posp start) (< 1 start) (natp count)
               (rationalp error) (< 0 error))
  (equal (lw-complex-euler-dirichlet-prefix rate height (+ start count -1) error)
   (lw-complex-add
    (lw-complex-euler-dirichlet-prefix rate height (- start 1) error)
    (lw-complex-euler-cell-segment rate height start count error))))
 :hints (("Goal"
  :induct (lw-complex-euler-cell-segment rate height start count error)
  :in-theory (e/d ((:induction lw-complex-euler-cell-segment))
                  (lw-complex-euler-dirichlet-prefix-step)))
         (and stable-under-simplificationp
          '(:expand ((lw-complex-euler-cell-segment rate height start count error)
                     (lw-complex-euler-cell-segment rate height start 0 error))
            :use ((:instance lw-complex-euler-dirichlet-prefix-step (count (+ start count -1))))
            :do-not-induct t))))

(local (defthm lw-edt-difference
 (implies (and (lw-complexp point) (lw-complexp rest))
  (equal (lw-complex-sub (lw-complex-add point rest) point) rest))
 :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(defthm lw-complex-euler-cell-segment-difference
 (implies (and (rationalp rate) (rationalp height)
               (posp start) (< 1 start) (natp count)
               (rationalp error) (< 0 error))
  (equal
   (lw-complex-sub
    (lw-complex-euler-dirichlet-prefix rate height (+ start count -1) error)
    (lw-complex-euler-dirichlet-prefix rate height (- start 1) error))
   (lw-complex-euler-cell-segment rate height start count error)))
 :hints (("Goal" :use (lw-complex-euler-cell-segment-telescope)
                 :in-theory (disable lw-complex-euler-cell-segment-telescope)
                 :do-not-induct t)))

(local (defthm lw-edt-power-two-natural
 (natp (lw-rational-power 2 block))
 :hints (("Goal" :in-theory (enable lw-rational-power)))
 :rule-classes (:rewrite :type-prescription)))

(local (defthm lw-edt-power-two-four
 (implies (and (natp block) (<= 2 block))
  (<= 4 (lw-rational-power 2 block)))
 :hints (("Goal" :use ((:instance lw-rational-power-monotone-exponent
                       (base 2) (small 2) (large block)))
                 :in-theory (disable lw-rational-power-monotone-exponent)))
 :rule-classes nil))

(local (defthm lw-edt-power-two-successor
 (implies (natp block)
  (equal (lw-rational-power 2 (+ 1 block)) (* 2 (lw-rational-power 2 block))))
 :hints (("Goal" :expand ((lw-rational-power 2 (+ 1 block)))))))

(defthm lw-complex-euler-dirichlet-block-difference
 (implies (and (rationalp rate) (rationalp height) (natp block) (<= 2 block)
               (rationalp error) (< 0 error))
  (equal
   (lw-complex-sub
    (lw-complex-euler-dirichlet-prefix rate height (- (lw-rational-power 2 (+ 1 block)) 1) error)
    (lw-complex-euler-dirichlet-prefix rate height (- (lw-rational-power 2 block) 1) error))
   (lw-complex-euler-dirichlet-block rate height block error)))
 :hints (("Goal"
  :use (lw-edt-power-two-four lw-edt-power-two-natural
        (:instance lw-complex-euler-cell-segment-difference
         (start (lw-rational-power 2 block)) (count (lw-rational-power 2 block))))
  :in-theory (union-theories
   '(lw-complex-euler-dirichlet-block lw-edt-power-two-successor lw-edt-double
     natp posp fix commutativity-of-+ commutativity-2-of-+ associativity-of-+
     unicity-of-0 unicity-of-1)
   (theory 'minimal-theory))
  :do-not-induct t)))

(defthm lw-complex-euler-dirichlet-prefix-block-bound
 (implies (and (rationalp rate) (< 0 rate) (rationalp height)
               (natp block) (<= 2 block)
               (<= (+ rate (abs height)) (lw-rational-power 2 block))
               (rationalp error) (< 0 error) (<= error 1))
  (lw-complex-diskp
   (lw-complex-sub
    (lw-complex-euler-dirichlet-prefix rate height (- (lw-rational-power 2 (+ 1 block)) 1) error)
    (lw-complex-euler-dirichlet-prefix rate height (- (lw-rational-power 2 block) 1) error))
   (+ (* 32 (lw-euler-dirichlet-cell-cap rate height) (/ rate) (/ rate) (/ block) (/ block))
      (* (lw-euler-dirichlet-block-rounding rate height block) error))))
 :hints (("Goal"
  :use (lw-complex-euler-dirichlet-block-difference lw-complex-euler-dirichlet-block-bound)
  :in-theory (theory 'minimal-theory)
  :do-not-induct t)))

