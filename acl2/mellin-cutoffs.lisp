(in-package "ACL2")

(include-book "mellin-window")
(include-book "mellin-meshes")

; Compare cutoffs using the existing dyadic evaluator. Cell weights stay
; outside unit-weight samples, exactly as in mellin-partitions.lisp.
(local (in-theory
        (disable lw-log-signal-bounds (:executable-counterpart lw-log-signal-bounds)
                 lw-mellin-sample lw-mellin-sample-growth-kernel-bound lw-mellin-sample-rational
                 lw-kernel-weight-bounds lw-kernel-weight-bounds-valid lw-kernel-upper-inverse-square
                 lw-mellin-tail-coefficient lw-mellin-tail-coefficient-nonnegative
                 lw-mellin-tail-cutoff lw-mellin-tail-cutoff-adequate
                 lw-mellin-dyadic-rational
                 lw-complexp lw-complex-diskp lw-complex-add lw-complex-sub lw-complex-scale
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mcft-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mcft-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mcft-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-mcft-times-zero (equal (* 0 a) 0)))
(local (defthm lw-mcft-times-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-mcft-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-mcft-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mcft-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mcft-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mcft-left-commutes)))))
(local (defthm lw-mcft-reciprocal-difference
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b) (rationalp coefficient))
                  (equal (* a b coefficient (- (/ a) (/ b))) (* coefficient (- b a))))
         :hints (("Goal" :use ((:instance lw-mcft-inverse-factor (divisor a) (coefficient (* b coefficient)))
                              (:instance lw-mcft-inverse-factor (divisor b) (coefficient (* a coefficient))))))
         :rule-classes nil))
(local (defthm lw-mcft-cancel-positive
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
                       (<= (* factor a) (* factor b))) (<= a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mcft-rectangle-potential
         (implies (and (rationalp start) (< 0 start) (rationalp end) (<= start end) (<= end (* 2 start))
                       (rationalp coefficient) (<= 0 coefficient) (rationalp term) (<= 0 term)
                       (<= (* start start term) (* (- end start) coefficient)))
                  (<= term (* 2 coefficient (- (/ start) (/ end)))))
         :hints (("Goal" :use ((:instance lw-mcft-reciprocal-difference (a start) (b end) (coefficient (* 2 coefficient)))
                              (:instance lw-mcft-multiply-order (a end) (b (* 2 start)) (factor (* start term)))
                              (:instance lw-mcft-multiply-order
                                (a (* start start term)) (b (* (- end start) coefficient)) (factor 2))
                              (:instance lw-mcft-cancel-positive (a term)
                                (b (* 2 coefficient (- (/ start) (/ end)))) (factor (* start end))))
                         :nonlinearp t))
         :rule-classes nil))

(defthm lw-mellin-weighted-tail-sample
  (implies (and (rationalp start) (< 0 start) (rationalp end) (<= start end) (<= end (* 2 start))
                (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (<= (+ 2 index) (* (- sigma 2) start)) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-scale (- end start) (lw-mellin-sample start sigma height index 1 error))
            (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ end)))))
  :hints (("Goal"
           :use ((:instance lw-mellin-sample-growth-kernel-bound (value start) (step 1) (shifted-error 1))
                 (:instance lw-kernel-upper-inverse-square (value start) (rate (- sigma 2)) (step 1) (error 1))
                 (:instance lw-kernel-weight-bounds-valid (value start) (sigma (- sigma 2)) (step 1) (error 1))
                 (:instance lw-mellin-tail-coefficient-nonnegative (rate (- sigma 2)) (mass 1))
                 (:instance lw-complex-scale-disk (point (lw-mellin-sample start sigma height index 1 error))
                   (radius (* 17 (cdr (lw-kernel-weight-bounds start (- sigma 2) index 1 1)))) (factor (- end start)))
                 (:instance lw-mcft-rectangle-potential
                   (coefficient (* 17 (lw-mellin-tail-coefficient (- sigma 2) index 1)))
                   (term (* (- end start) 17 (cdr (lw-kernel-weight-bounds start (- sigma 2) index 1 1)))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-scale (- end start) (lw-mellin-sample start sigma height index 1 error)))
                   (radius (* (- end start) 17 (cdr (lw-kernel-weight-bounds start (- sigma 2) index 1 1))))
                   (cap (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ end))))))
           :in-theory (e/d (lw-mellin-tail-coefficient) (lw-complex-scale-disk)) :nonlinearp t)))

(local (defthm lw-mcft-zero-mesh
         (implies (zp depth) (equal (lw-halved-width width depth) width))
         :hints (("Goal" :in-theory (enable lw-halved-width)))))
(local (defthm lw-mcft-left-span
         (implies (and (rationalp start) (rationalp end))
                  (equal (- (/ (+ start end) 2) start) (* 1/2 (- end start))))
         :hints (("Goal" :nonlinearp t))))
(local (defthm lw-mcft-right-span
         (implies (and (rationalp start) (rationalp end))
                  (equal (- end (/ (+ start end) 2)) (* 1/2 (- end start))))
         :hints (("Goal" :nonlinearp t))))
(local (defthm lw-mcft-potential-telescope
         (implies (and (rationalp coefficient) (rationalp start) (rationalp middle) (rationalp end))
                  (equal (+ (* coefficient (- (/ start) (/ middle))) (* coefficient (- (/ middle) (/ end))))
                         (* coefficient (- (/ start) (/ end)))))
         :hints (("Goal" :nonlinearp t))))

; This is the actual dyadic tail, with external weights and arbitrary
; positive point precision. A telescoping radius handles any finite end.
(defthm lw-mellin-dyadic-tail-potential
  (implies (and (rationalp start) (< 0 start) (rationalp end) (<= start end) (natp depth)
                (<= (lw-halved-width (- end start) depth) start)
                (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (<= (+ 2 index) (* (- sigma 2) start)) (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-mellin-dyadic-sum start end depth sigma height index error)
                             (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ end)))))
  :hints (("Goal" :induct (lw-mellin-dyadic-sum start end depth sigma height index error)
                  :do-not '(generalize eliminate-destructors)
                  :in-theory (disable (:definition lw-mellin-dyadic-sum) distributivity lw-mcft-left-distribute
                                      lw-mcft-left-span lw-mcft-right-span))
          (and stable-under-simplificationp
               '(:use (lw-mellin-weighted-tail-sample lw-mcft-left-span lw-mcft-right-span
                       (:instance lw-mellin-tail-coefficient-nonnegative (rate (- sigma 2)) (mass 1))
                       (:instance lw-mcft-multiply-order (a start) (b (/ (+ start end) 2)) (factor (- sigma 2)))
                       (:instance lw-mcft-potential-telescope
                         (coefficient (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1))) (middle (/ (+ start end) 2)))
                       (:instance lw-halved-width-half (width (- end start)) (steps (- depth 1)))
                       (:instance lw-complex-add-disk
                         (left (lw-mellin-dyadic-sum start (/ (+ start end) 2) (- depth 1) sigma height index error))
                         (radius (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ (/ (+ start end) 2)))))
                         (right (lw-mellin-dyadic-sum (/ (+ start end) 2) end (- depth 1) sigma height index error))
                         (other-radius (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ (/ (+ start end) 2)) (/ end))))))
                 :expand ((lw-mellin-dyadic-sum start end depth sigma height index error)
                          (lw-halved-width (- end start) depth))
                 :in-theory (disable lw-mellin-weighted-tail-sample lw-complex-add-disk lw-halved-width-half
                                     distributivity lw-mcft-left-distribute lw-mcft-left-span lw-mcft-right-span)
                 :do-not '(generalize eliminate-destructors)
                 :do-not-induct t
                 :nonlinearp t))))

(local (in-theory (disable lw-mellin-dyadic-sum lw-mellin-dyadic-tail-potential lw-mellin-weighted-tail-sample)))

(defthm lw-mellin-dyadic-tail-bound
  (implies (and (rationalp start) (< 0 start) (rationalp end) (<= start end) (natp depth)
                (<= (lw-halved-width (- end start) depth) start)
                (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (<= (+ 2 index) (* (- sigma 2) start)) (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-mellin-dyadic-sum start end depth sigma height index error)
                             (/ (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1)) start)))
  :hints (("Goal" :use (lw-mellin-dyadic-tail-potential
                        (:instance lw-mellin-tail-coefficient-nonnegative (rate (- sigma 2)) (mass 1))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-mellin-dyadic-sum start end depth sigma height index error))
                          (radius (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ end))))
                          (cap (/ (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1)) start))))
                  :nonlinearp t)))

; The original improper evaluator's mass-4 cutoff is already enough for
; a uniform arithmetic dyadic tail bound, with a larger error constant.
(defthm lw-mellin-dyadic-tail-at-integral-cutoff
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (rationalp cutoff-error) (< 0 cutoff-error) (rationalp error) (< 0 error)
                (rationalp end) (<= (lw-mellin-integral-cutoff sigma index cutoff-error) end) (natp depth)
                (<= (lw-halved-width (- end (lw-mellin-integral-cutoff sigma index cutoff-error)) depth)
                    (lw-mellin-integral-cutoff sigma index cutoff-error)))
           (lw-complex-diskp
            (lw-mellin-dyadic-sum (lw-mellin-integral-cutoff sigma index cutoff-error) end depth sigma height index error)
            (* 17/4 cutoff-error)))
  :hints (("Goal"
           :use ((:instance lw-mellin-integral-cutoff-valid (error cutoff-error))
                 (:instance lw-mellin-tail-cutoff-adequate (rate (- sigma 2)) (mass 4) (error cutoff-error))
                 (:instance lw-mellin-dyadic-tail-bound (start (lw-mellin-integral-cutoff sigma index cutoff-error)))
                 (:instance lw-positive-division-bound
                   (numerator (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1)))
                   (divisor (lw-mellin-integral-cutoff sigma index cutoff-error)) (bound (* 17/4 cutoff-error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-dyadic-sum (lw-mellin-integral-cutoff sigma index cutoff-error) end depth sigma height index error))
                   (radius (/ (* 34 (lw-mellin-tail-coefficient (- sigma 2) index 1)) (lw-mellin-integral-cutoff sigma index cutoff-error)))
                   (cap (* 17/4 cutoff-error))))
           :in-theory (e/d (lw-mellin-integral-cutoff lw-mellin-tail-coefficient)
                           (lw-mellin-dyadic-tail-bound lw-mellin-integral-cutoff-valid lw-rational-power))
           :nonlinearp t)))

(defun lw-mellin-tail-depth (start end)
  (lw-halving-depth (- end start) start (lw-precision-fuel (- end start) start)))

(defthm lw-mellin-tail-depth-adequate
  (implies (and (rationalp start) (< 0 start) (rationalp end) (<= start end))
           (and (natp (lw-mellin-tail-depth start end))
                (<= (lw-halved-width (- end start) (lw-mellin-tail-depth start end)) start)))
  :hints (("Goal" :use ((:instance lw-precision-fuel-adequate (width (- end start)) (epsilon start))
                        (:instance lw-halving-depth-adequate (width (- end start)) (epsilon start)
                          (fuel (lw-precision-fuel (- end start) start))))
                  :in-theory (disable lw-halving-depth lw-precision-fuel lw-precision-fuel-adequate lw-halving-depth-adequate))))

(defthm lw-mellin-computed-tail-at-integral-cutoff
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (rationalp cutoff-error) (< 0 cutoff-error) (rationalp error) (< 0 error)
                (rationalp end) (<= (lw-mellin-integral-cutoff sigma index cutoff-error) end))
           (lw-complex-diskp
            (lw-mellin-dyadic-sum
             (lw-mellin-integral-cutoff sigma index cutoff-error) end
             (lw-mellin-tail-depth (lw-mellin-integral-cutoff sigma index cutoff-error) end) sigma height index error)
            (* 17/4 cutoff-error)))
  :hints (("Goal" :use ((:instance lw-mellin-integral-cutoff-valid (error cutoff-error))
                        (:instance lw-mellin-tail-depth-adequate (start (lw-mellin-integral-cutoff sigma index cutoff-error)))
                        (:instance lw-mellin-dyadic-tail-at-integral-cutoff
                          (depth (lw-mellin-tail-depth (lw-mellin-integral-cutoff sigma index cutoff-error) end))))
                  :in-theory (disable lw-mellin-tail-depth lw-mellin-integral-cutoff lw-mellin-integral-cutoff-valid
                                      lw-mellin-tail-depth-adequate lw-mellin-dyadic-tail-at-integral-cutoff))))

(local (in-theory
        (disable lw-mellin-dyadic-split-comparison lw-mellin-dyadic-cross-depth
                 lw-mellin-spatial-slope lw-mellin-spatial-error-factor lw-mellin-spatial-parameters
                 lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope
                 lw-mellin-integral-depth lw-mellin-integral-precision lw-mellin-bounded-integral
                 lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
                 lw-complex-difference-triangle)))

(defun lw-mellin-mesh-depth (width mesh)
  (lw-halving-depth width mesh (lw-precision-fuel width mesh)))

(defthm lw-mellin-mesh-depth-adequate
  (implies (and (rationalp width) (<= 0 width) (rationalp mesh) (< 0 mesh))
           (and (natp (lw-mellin-mesh-depth width mesh))
                (<= (lw-halved-width width (lw-mellin-mesh-depth width mesh)) mesh)))
  :hints (("Goal" :use ((:instance lw-precision-fuel-adequate (epsilon mesh))
                        (:instance lw-halving-depth-adequate (epsilon mesh) (fuel (lw-precision-fuel width mesh))))
                  :in-theory (disable lw-halving-depth lw-precision-fuel lw-precision-fuel-adequate lw-halving-depth-adequate))))

; One common fine mesh/precision pays for comparisons on both [0,cap]
; and [0,cut], without assuming monotonicity of their coarse moduli.
(defun lw-mellin-cutoff-mesh (cap cut sigma height error)
  (min cut (/ error (* 16 (+ 1 (* cap (lw-mellin-spatial-slope cap sigma height 1))
                               (* cut (lw-mellin-spatial-slope cut sigma height 1)))))))
(defun lw-mellin-cutoff-precision (cap cut error)
  (/ error (* 16 (+ 1 (* cap (lw-mellin-spatial-error-factor cap 1))
                       (* cut (lw-mellin-spatial-error-factor cut 1))))))

(local (defthm lw-mcft-two-budget
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b) (rationalp error) (< 0 error))
                  (let ((precision (/ error (* 16 (+ 1 a b)))))
                    (and (rationalp precision) (< 0 precision)
                         (<= (* a precision) (/ error 16)) (<= (* b precision) (/ error 16)))))
         :hints (("Goal" :use ((:instance lw-positive-division-bound
                                (numerator (* a error)) (divisor (* 16 (+ 1 a b))) (bound (/ error 16)))
                              (:instance lw-positive-division-bound
                                (numerator (* b error)) (divisor (* 16 (+ 1 a b))) (bound (/ error 16))))
                         :nonlinearp t))
         :rule-classes nil))

(defthm lw-mellin-cutoff-refinement-parameters
  (implies (and (rationalp cap) (rationalp cut) (< 0 cut) (<= cut cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-cutoff-mesh cap cut sigma height error))
                (< 0 (lw-mellin-cutoff-mesh cap cut sigma height error))
                (<= (lw-mellin-cutoff-mesh cap cut sigma height error) cut)
                (rationalp (lw-mellin-cutoff-precision cap cut error)) (< 0 (lw-mellin-cutoff-precision cap cut error))
                (<= (* cap (lw-mellin-spatial-slope cap sigma height 1) (lw-mellin-cutoff-mesh cap cut sigma height error)) (/ error 16))
                (<= (* cut (lw-mellin-spatial-slope cut sigma height 1) (lw-mellin-cutoff-mesh cap cut sigma height error)) (/ error 16))
                (<= (* cap (lw-mellin-spatial-error-factor cap 1) (lw-mellin-cutoff-precision cap cut error)) (/ error 16))
                (<= (* cut (lw-mellin-spatial-error-factor cut 1) (lw-mellin-cutoff-precision cap cut error)) (/ error 16))))
  :hints (("Goal" :use ((:instance lw-mellin-spatial-parameters (step 1))
                        (:instance lw-mellin-spatial-parameters (cap cut) (step 1))
                        (:instance lw-mcft-two-budget (a (* cap (lw-mellin-spatial-slope cap sigma height 1)))
                          (b (* cut (lw-mellin-spatial-slope cut sigma height 1))))
                        (:instance lw-mcft-two-budget (a (* cap (lw-mellin-spatial-error-factor cap 1)))
                          (b (* cut (lw-mellin-spatial-error-factor cut 1)))))
                  :nonlinearp t)))

(defun lw-mellin-cutoff-prefix (cap cut sigma height index error)
  (lw-mellin-dyadic-sum 0 cut (lw-mellin-mesh-depth cut (lw-mellin-cutoff-mesh cap cut sigma height error))
                        sigma height index (lw-mellin-cutoff-precision cap cut error)))
(defun lw-mellin-cutoff-tail (cap cut sigma height index error)
  (lw-mellin-dyadic-sum cut cap (lw-mellin-mesh-depth (- cap cut) (lw-mellin-cutoff-mesh cap cut sigma height error))
                        sigma height index (lw-mellin-cutoff-precision cap cut error)))

(defthm lw-mellin-cutoff-refinement-depths
  (implies (and (rationalp cap) (rationalp cut) (< 0 cut) (<= cut cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (and (natp (lw-mellin-mesh-depth cut (lw-mellin-cutoff-mesh cap cut sigma height error)))
                (natp (lw-mellin-mesh-depth (- cap cut) (lw-mellin-cutoff-mesh cap cut sigma height error)))
                (<= (lw-halved-width cut (lw-mellin-mesh-depth cut (lw-mellin-cutoff-mesh cap cut sigma height error)))
                    (lw-mellin-cutoff-mesh cap cut sigma height error))
                (<= (lw-halved-width (- cap cut) (lw-mellin-mesh-depth (- cap cut) (lw-mellin-cutoff-mesh cap cut sigma height error)))
                    (lw-mellin-cutoff-mesh cap cut sigma height error))))
  :hints (("Goal" :use (lw-mellin-cutoff-refinement-parameters
                        (:instance lw-mellin-mesh-depth-adequate (width cut) (mesh (lw-mellin-cutoff-mesh cap cut sigma height error)))
                        (:instance lw-mellin-mesh-depth-adequate (width (- cap cut)) (mesh (lw-mellin-cutoff-mesh cap cut sigma height error))))
                  :in-theory (disable lw-mellin-cutoff-mesh lw-mellin-cutoff-precision lw-mellin-mesh-depth
                                      lw-mellin-cutoff-refinement-parameters lw-mellin-mesh-depth-adequate))))

(defthm lw-mellin-cutoff-refinement-rational
  (implies (and (rationalp cap) (rationalp cut) (< 0 cut) (<= cut cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (and (lw-complexp (lw-mellin-cutoff-prefix cap cut sigma height index error))
                (lw-complexp (lw-mellin-cutoff-tail cap cut sigma height index error))))
  :hints (("Goal" :use (lw-mellin-cutoff-refinement-parameters
                        (:instance lw-mellin-dyadic-rational (start 0) (end cut)
                          (depth (lw-mellin-mesh-depth cut (lw-mellin-cutoff-mesh cap cut sigma height error)))
                          (point-error (lw-mellin-cutoff-precision cap cut error)))
                        (:instance lw-mellin-dyadic-rational (start cut) (end cap)
                          (depth (lw-mellin-mesh-depth (- cap cut) (lw-mellin-cutoff-mesh cap cut sigma height error)))
                          (point-error (lw-mellin-cutoff-precision cap cut error))))
                  :in-theory (disable lw-mellin-cutoff-mesh lw-mellin-cutoff-precision lw-mellin-mesh-depth
                                      lw-mellin-cutoff-refinement-parameters))))

(local (in-theory
        (disable lw-mellin-cutoff-mesh lw-mellin-cutoff-precision lw-mellin-mesh-depth
                 lw-mellin-mesh-depth-adequate
                 lw-mellin-cutoff-refinement-parameters lw-mellin-cutoff-refinement-depths lw-mellin-cutoff-refinement-rational
                 lw-mellin-cutoff-prefix lw-mellin-cutoff-tail lw-mellin-mesh-pair-radius)))

(local (defthm lw-mcft-mesh-nonnegative
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth)) (<= 0 (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))
         :rule-classes (:rewrite :type-prescription)))

(defthm lw-mellin-bounded-split-refinement
  (implies (and (rationalp cap) (rationalp cut) (< 0 cut) (<= cut cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                (rationalp error) (< 0 error) (rationalp refinement-error) (< 0 refinement-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-bounded-integral cap sigma height index error)
                            (lw-complex-add (lw-mellin-cutoff-prefix cap cut sigma height index refinement-error)
                                            (lw-mellin-cutoff-tail cap cut sigma height index refinement-error)))
            (+ (/ error 2) (/ refinement-error 8))))
  :hints (("Goal"
           :use ((:instance lw-mellin-spatial-parameters (step 1))
                 lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
                 (:instance lw-mellin-cutoff-refinement-parameters (error refinement-error))
                 (:instance lw-mellin-cutoff-refinement-depths (error refinement-error))
                 (:instance lw-mcft-mesh-nonnegative (width cap) (depth (lw-mellin-integral-depth cap sigma height error)))
                 (:instance lw-mellin-dyadic-split-comparison
                   (depth (lw-mellin-integral-depth cap sigma height error))
                   (prefix-depth (lw-mellin-mesh-depth cut (lw-mellin-cutoff-mesh cap cut sigma height refinement-error)))
                   (tail-depth (lw-mellin-mesh-depth (- cap cut) (lw-mellin-cutoff-mesh cap cut sigma height refinement-error)))
                   (left-mesh (lw-halved-width cap (lw-mellin-integral-depth cap sigma height error)))
                   (right-mesh (lw-mellin-cutoff-mesh cap cut sigma height refinement-error))
                   (left-error (lw-mellin-integral-precision cap error)) (right-error (lw-mellin-cutoff-precision cap cut refinement-error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-mellin-bounded-integral cap sigma height index error)
                                          (lw-complex-add (lw-mellin-cutoff-prefix cap cut sigma height index refinement-error)
                                                          (lw-mellin-cutoff-tail cap cut sigma height index refinement-error))))
                   (radius (* cap (lw-mellin-mesh-pair-radius cap sigma height
                                   (lw-halved-width cap (lw-mellin-integral-depth cap sigma height error))
                                   (lw-mellin-cutoff-mesh cap cut sigma height refinement-error)
                                   (lw-mellin-integral-precision cap error) (lw-mellin-cutoff-precision cap cut refinement-error))))
                   (cap (+ (/ error 2) (/ refinement-error 8)))))
           :in-theory (enable lw-mellin-bounded-integral lw-mellin-cutoff-prefix lw-mellin-cutoff-tail lw-mellin-mesh-pair-radius)
           :nonlinearp t)))

(defthm lw-mellin-bounded-prefix-refinement
  (implies (and (rationalp cap) (rationalp cut) (< 0 cut) (<= cut cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                (rationalp error) (< 0 error) (rationalp refinement-error) (< 0 refinement-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-cutoff-prefix cap cut sigma height index refinement-error)
                            (lw-mellin-bounded-integral cut sigma height index error))
            (+ (/ error 2) (/ refinement-error 8))))
  :hints (("Goal"
           :use ((:instance lw-mellin-spatial-parameters (cap cut) (step 1))
                 (:instance lw-mellin-integral-depth-adequate (cap cut))
                 (:instance lw-mellin-integral-precision-valid (cap cut))
                 (:instance lw-mellin-cutoff-refinement-parameters (error refinement-error))
                 (:instance lw-mellin-cutoff-refinement-depths (error refinement-error))
                 (:instance lw-mcft-multiply-order
                   (a (lw-halved-width cut (lw-mellin-mesh-depth cut (lw-mellin-cutoff-mesh cap cut sigma height refinement-error))))
                   (b (lw-mellin-cutoff-mesh cap cut sigma height refinement-error))
                   (factor (* cut (lw-mellin-spatial-slope cut sigma height 1))))
                 (:instance lw-mellin-dyadic-cross-depth (cap cut)
                   (left-depth (lw-mellin-mesh-depth cut (lw-mellin-cutoff-mesh cap cut sigma height refinement-error)))
                   (right-depth (lw-mellin-integral-depth cut sigma height error))
                   (left-error (lw-mellin-cutoff-precision cap cut refinement-error)) (right-error (lw-mellin-integral-precision cut error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-mellin-cutoff-prefix cap cut sigma height index refinement-error)
                                          (lw-mellin-bounded-integral cut sigma height index error)))
                   (radius (* cut (+ (* (lw-mellin-spatial-slope cut sigma height 1)
                                        (+ (lw-halved-width cut (lw-mellin-mesh-depth cut (lw-mellin-cutoff-mesh cap cut sigma height refinement-error)))
                                           (lw-halved-width cut (lw-mellin-integral-depth cut sigma height error))))
                                     (* (lw-mellin-spatial-error-factor cut 1)
                                        (+ (lw-mellin-cutoff-precision cap cut refinement-error) (lw-mellin-integral-precision cut error))))))
                   (cap (+ (/ error 2) (/ refinement-error 8)))))
           :in-theory (enable lw-mellin-bounded-integral lw-mellin-cutoff-prefix)
           :nonlinearp t)))

(defthm lw-mellin-refined-tail-at-integral-cutoff
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (rationalp cutoff-error) (< 0 cutoff-error) (rationalp error) (< 0 error)
                (rationalp cap) (<= (lw-mellin-integral-cutoff sigma index cutoff-error) cap))
           (lw-complex-diskp
            (lw-mellin-cutoff-tail cap (lw-mellin-integral-cutoff sigma index cutoff-error) sigma height index error)
            (* 17/4 cutoff-error)))
  :hints (("Goal" :use ((:instance lw-mellin-integral-cutoff-valid (error cutoff-error))
                        (:instance lw-mellin-cutoff-refinement-parameters (cut (lw-mellin-integral-cutoff sigma index cutoff-error)))
                        (:instance lw-mellin-cutoff-refinement-depths (cut (lw-mellin-integral-cutoff sigma index cutoff-error)))
                        (:instance lw-mellin-dyadic-tail-at-integral-cutoff
                          (end cap) (depth (lw-mellin-mesh-depth (- cap (lw-mellin-integral-cutoff sigma index cutoff-error))
                                           (lw-mellin-cutoff-mesh cap (lw-mellin-integral-cutoff sigma index cutoff-error) sigma height error)))
                          (error (lw-mellin-cutoff-precision cap (lw-mellin-integral-cutoff sigma index cutoff-error) error))))
                  :in-theory (e/d (lw-mellin-cutoff-tail)
                                  (lw-mellin-integral-cutoff lw-mellin-integral-cutoff-valid lw-mellin-dyadic-tail-at-integral-cutoff)))))

(local (in-theory
        (disable lw-mellin-bounded-split-refinement lw-mellin-bounded-prefix-refinement
                 lw-mellin-refined-tail-at-integral-cutoff lw-mellin-integral-rational lw-mellin-bounded-integral-rational)))

(local (defthm lw-mcft-prefix-tail-identity
         (implies (and (lw-complexp prefix) (lw-complexp tail) (lw-complexp small))
                  (equal (lw-complex-sub (lw-complex-add prefix tail) small)
                         (lw-complex-add (lw-complex-sub prefix small) tail)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(local (defthm lw-mcft-three-term-bound
         (implies (and (lw-complexp big) (lw-complexp small) (lw-complexp prefix) (lw-complexp tail)
                       (lw-complex-diskp (lw-complex-sub big (lw-complex-add prefix tail)) big-error)
                       (lw-complex-diskp (lw-complex-sub prefix small) small-error)
                       (lw-complex-diskp tail tail-error))
                  (lw-complex-diskp (lw-complex-sub big small) (+ big-error small-error tail-error)))
         :hints (("Goal" :use ((:instance lw-complex-add-disk (left (lw-complex-sub prefix small))
                                (radius small-error) (right tail) (other-radius tail-error))
                              (:instance lw-complex-difference-triangle
                                (left big) (middle (lw-complex-add prefix tail)) (right small)
                                (radius big-error) (other-radius (+ small-error tail-error))))
                         :in-theory (e/d (lw-complexp lw-complex-add lw-complex-sub)
                                         (lw-complex-add-disk))))
         :rule-classes nil))

; Compare the exact default evaluator outputs. The auxiliary meshes are
; computed finite rational objects; all three error bounds are theorems.
(defthm lw-mellin-integral-cauchy-ordered
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error)
                (<= (lw-mellin-integral-cutoff sigma index left-error) (lw-mellin-integral-cutoff sigma index right-error)))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-integral sigma height index right-error) (lw-mellin-integral sigma height index left-error))
            (* 5 (+ left-error right-error))))
  :hints (("Goal"
           :use ((:instance lw-mellin-integral-cutoff-valid (error left-error))
                 (:instance lw-mellin-integral-cutoff-valid (error right-error))
                 (:instance lw-mellin-integral-rational (error left-error))
                 (:instance lw-mellin-integral-rational (error right-error))
                 (:instance lw-mellin-cutoff-refinement-rational
                   (cap (lw-mellin-integral-cutoff sigma index right-error)) (cut (lw-mellin-integral-cutoff sigma index left-error))
                   (error (+ left-error right-error)))
                 (:instance lw-mellin-bounded-split-refinement
                   (cap (lw-mellin-integral-cutoff sigma index right-error)) (cut (lw-mellin-integral-cutoff sigma index left-error))
                   (error (/ right-error 2)) (refinement-error (+ left-error right-error)))
                 (:instance lw-mellin-bounded-prefix-refinement
                   (cap (lw-mellin-integral-cutoff sigma index right-error)) (cut (lw-mellin-integral-cutoff sigma index left-error))
                   (error (/ left-error 2)) (refinement-error (+ left-error right-error)))
                 (:instance lw-mellin-refined-tail-at-integral-cutoff
                   (cap (lw-mellin-integral-cutoff sigma index right-error)) (cutoff-error left-error) (error (+ left-error right-error)))
                 (:instance lw-mcft-three-term-bound
                   (big (lw-mellin-integral sigma height index right-error)) (small (lw-mellin-integral sigma height index left-error))
                   (prefix (lw-mellin-cutoff-prefix (lw-mellin-integral-cutoff sigma index right-error)
                                                   (lw-mellin-integral-cutoff sigma index left-error) sigma height index (+ left-error right-error)))
                   (tail (lw-mellin-cutoff-tail (lw-mellin-integral-cutoff sigma index right-error)
                                               (lw-mellin-integral-cutoff sigma index left-error) sigma height index (+ left-error right-error)))
                   (big-error (+ (/ right-error 4) (/ (+ left-error right-error) 8)))
                   (small-error (+ (/ left-error 4) (/ (+ left-error right-error) 8))) (tail-error (* 17/4 left-error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-mellin-integral sigma height index right-error) (lw-mellin-integral sigma height index left-error)))
                   (radius (+ (+ (/ right-error 4) (/ (+ left-error right-error) 8))
                              (+ (/ left-error 4) (/ (+ left-error right-error) 8)) (* 17/4 left-error)))
                   (cap (* 5 (+ left-error right-error)))))
           :in-theory (e/d (lw-mellin-integral)
                           (lw-mellin-integral-cutoff lw-mellin-integral-cutoff-valid)))))

(defthm lw-mellin-integral-cauchy
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-integral sigma height index left-error) (lw-mellin-integral sigma height index right-error))
            (* 5 (+ left-error right-error))))
  :hints (("Goal" :cases ((<= (lw-mellin-integral-cutoff sigma index left-error) (lw-mellin-integral-cutoff sigma index right-error)))
                  :use (lw-mellin-integral-cauchy-ordered
                        (:instance lw-mellin-integral-cauchy-ordered (left-error right-error) (right-error left-error))
                        (:instance lw-mellin-integral-rational (error left-error))
                        (:instance lw-mellin-integral-rational (error right-error))
                        (:instance lw-complex-difference-symmetric
                          (left (lw-mellin-integral sigma height index right-error)) (right (lw-mellin-integral sigma height index left-error))
                          (radius (* 5 (+ left-error right-error)))))
                  :in-theory (disable lw-mellin-integral lw-mellin-integral-cutoff lw-mellin-integral-cauchy-ordered))))

(defthm lw-mellin-integral-cauchy-budget
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (rationalp target-error) (< 0 target-error)
                (rationalp left-error) (< 0 left-error) (<= left-error (/ target-error 10))
                (rationalp right-error) (< 0 right-error) (<= right-error (/ target-error 10)))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-integral sigma height index left-error) (lw-mellin-integral sigma height index right-error))
            target-error))
  :hints (("Goal" :use (lw-mellin-integral-cauchy
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-mellin-integral sigma height index left-error) (lw-mellin-integral sigma height index right-error)))
                          (radius (* 5 (+ left-error right-error))) (cap target-error)))
                  :in-theory (disable lw-mellin-integral lw-mellin-integral-cauchy))))
