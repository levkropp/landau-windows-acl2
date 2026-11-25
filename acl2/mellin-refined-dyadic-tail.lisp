(in-package "ACL2")

(include-book "mellin-refined-tail")

(include-book "mellin-frozen-quadrature")

(include-book "mellin-cutoffs")

; Tail control for the same dyadic leaves used by the endpoint machinery.
; The construction cap and all coefficients stay frozen while the point
; exponential precision may be chosen arbitrarily fine. The actual
; improper evaluator's mass-four cutoff gives a 5/4 tail-error factor.

(local (in-theory
        (disable lw-log-signal-bounds (:executable-counterpart lw-log-signal-bounds)
                 lw-mellin-sample lw-mellin-refined-sample-kernel-bound lw-mellin-refined-sample-rational
                 lw-kernel-weight-bounds lw-kernel-weight-bounds-valid lw-kernel-upper-inverse-square
                 lw-mellin-tail-coefficient lw-mellin-tail-coefficient-nonnegative
                 lw-mellin-tail-cutoff lw-mellin-tail-cutoff-adequate
                 lw-mellin-dyadic-rational
                 lw-complexp lw-complex-diskp lw-complex-add lw-complex-sub lw-complex-scale
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (in-theory (disable lw-mellin-refined-sample lw-signal-exponential-refined-value
                          lw-mellin-frozen-sample lw-mellin-frozen-dyadic lw-signal-exponential-precision)))

(local (defthm lw-mrd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-mrd-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mrd-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))

(local (defthm lw-mrd-times-zero (equal (* 0 a) 0)))

(local (defthm lw-mrd-times-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-mrd-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-mrd-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-mrd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mrd-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mrd-left-commutes)))))

(local (defthm lw-mrd-reciprocal-difference
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b) (rationalp coefficient))
                  (equal (* a b coefficient (- (/ a) (/ b))) (* coefficient (- b a))))
         :hints (("Goal" :use ((:instance lw-mrd-inverse-factor (divisor a) (coefficient (* b coefficient)))
                              (:instance lw-mrd-inverse-factor (divisor b) (coefficient (* a coefficient))))))
         :rule-classes nil))

(local (defthm lw-mrd-cancel-positive
         (implies (and (rationalp a) (rationalp b) (rationalp factor) (< 0 factor)
                       (<= (* factor a) (* factor b))) (<= a b))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mrd-rectangle-potential
         (implies (and (rationalp start) (< 0 start) (rationalp end) (<= start end) (<= end (* 2 start))
                       (rationalp coefficient) (<= 0 coefficient) (rationalp term) (<= 0 term)
                       (<= (* start start term) (* (- end start) coefficient)))
                  (<= term (* 2 coefficient (- (/ start) (/ end)))))
         :hints (("Goal" :use ((:instance lw-mrd-reciprocal-difference (a start) (b end) (coefficient (* 2 coefficient)))
                              (:instance lw-mrd-multiply-order (a end) (b (* 2 start)) (factor (* start term)))
                              (:instance lw-mrd-multiply-order
                                (a (* start start term)) (b (* (- end start) coefficient)) (factor 2))
                              (:instance lw-mrd-cancel-positive (a term)
                                (b (* 2 coefficient (- (/ start) (/ end)))) (factor (* start end))))
                         :nonlinearp t))
         :rule-classes nil))

(defun lw-mellin-refined-dyadic (cap start end depth sigma height index model-error error exp-error)
 (declare (xargs :measure (nfix depth)))
 (if (zp depth)
  (lw-complex-scale (- end start) (lw-mellin-refined-sample cap start sigma height index 1 model-error error exp-error))
  (let ((middle (/ (+ start end) 2)))
   (lw-complex-add
    (lw-mellin-refined-dyadic cap start middle (- depth 1) sigma height index model-error error exp-error)
    (lw-mellin-refined-dyadic cap middle end (- depth 1) sigma height index model-error error exp-error)))))

(defthm lw-mellin-refined-dyadic-rational
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start) (rationalp end) (<= start end)
       (rationalp sigma) (<= 0 sigma) (rationalp height)
       (rationalp model-error) (< 0 model-error) (rationalp error) (< 0 error) (rationalp exp-error) (< 0 exp-error))
  (lw-complexp (lw-mellin-refined-dyadic cap start end depth sigma height index model-error error exp-error)))
 :hints (("Goal"
  :induct (lw-mellin-refined-dyadic cap start end depth sigma height index model-error error exp-error)
  :in-theory (enable lw-complexp lw-complex-add lw-complex-scale))
  (and stable-under-simplificationp
   '(:use ((:instance lw-mellin-refined-sample-rational (value start) (step 1) (sample-error error)))
     :in-theory (e/d (lw-complexp lw-complex-add lw-complex-scale) (lw-mellin-refined-sample-rational))
     :do-not-induct t))))

(local (in-theory (disable (:definition lw-mellin-refined-dyadic))))

(local (defthm lw-mrd-refined-leaf
 (implies (zp depth)
  (equal (lw-mellin-refined-dyadic cap start end depth sigma height index model-error error exp-error)
         (lw-complex-scale (- end start)
          (lw-mellin-refined-sample cap start sigma height index 1 model-error error exp-error))))
 :hints (("Goal" :in-theory (enable (:definition lw-mellin-refined-dyadic))))))
(local (defthm lw-mrd-frozen-leaf
 (implies (zp depth)
  (equal (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error error)
         (lw-complex-scale (- end start)
          (lw-mellin-frozen-sample cap start sigma height index 1 model-error error))))
 :hints (("Goal" :in-theory (enable (:definition lw-mellin-frozen-dyadic))))))

(defthm lw-mellin-refined-dyadic-native
 (equal
  (lw-mellin-refined-dyadic cap start end depth sigma height index model-error error
                           (lw-signal-exponential-precision cap model-error))
  (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error error))
 :hints (("Goal"
  :induct (lw-mellin-refined-dyadic cap start end depth sigma height index model-error error
                                  (lw-signal-exponential-precision cap model-error))
  :in-theory (enable (:induction lw-mellin-refined-dyadic)))
  (and stable-under-simplificationp
   '(:expand ((lw-mellin-refined-dyadic cap start end depth sigma height index model-error error
                                      (lw-signal-exponential-precision cap model-error))
              (lw-mellin-frozen-dyadic cap start end depth sigma height index model-error error))
     :do-not-induct t))))

(defthm lw-mellin-refined-weighted-tail-sample
  (implies (and (rationalp cap) (<= 0 cap)
                (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap model-error))
                (rationalp start) (< 0 start) (rationalp end) (<= start end) (<= end (* 2 start))
                (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (<= (+ 2 index) (* (- sigma 2) start)) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-scale (- end start) (lw-mellin-refined-sample cap start sigma height index 1 model-error error exp-error))
            (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ end)))))
  :hints (("Goal"
           :use ((:instance lw-mellin-refined-sample-kernel-bound (value start) (step 1) (shifted-error 1) (sample-error error))
                 (:instance lw-kernel-upper-inverse-square (value start) (rate (- sigma 2)) (step 1) (error 1))
                 (:instance lw-kernel-weight-bounds-valid (value start) (sigma (- sigma 2)) (step 1) (error 1))
                 (:instance lw-mellin-tail-coefficient-nonnegative (rate (- sigma 2)) (mass 1))
                 (:instance lw-complex-scale-disk (point (lw-mellin-refined-sample cap start sigma height index 1 model-error error exp-error))
                   (radius (* 5 (cdr (lw-kernel-weight-bounds start (- sigma 2) index 1 1)))) (factor (- end start)))
                 (:instance lw-mrd-rectangle-potential
                   (coefficient (* 5 (lw-mellin-tail-coefficient (- sigma 2) index 1)))
                   (term (* (- end start) 5 (cdr (lw-kernel-weight-bounds start (- sigma 2) index 1 1)))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-scale (- end start) (lw-mellin-refined-sample cap start sigma height index 1 model-error error exp-error)))
                   (radius (* (- end start) 5 (cdr (lw-kernel-weight-bounds start (- sigma 2) index 1 1))))
                   (cap (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ end))))))
           :in-theory (e/d (lw-mellin-tail-coefficient) (lw-complex-scale-disk)) :nonlinearp t)))

(local (defthm lw-mrd-zero-mesh
         (implies (zp depth) (equal (lw-halved-width width depth) width))
         :hints (("Goal" :in-theory (enable lw-halved-width)))))

(local (defthm lw-mrd-left-span
         (implies (and (rationalp start) (rationalp end))
                  (equal (- (/ (+ start end) 2) start) (* 1/2 (- end start))))
         :hints (("Goal" :nonlinearp t))))

(local (defthm lw-mrd-right-span
         (implies (and (rationalp start) (rationalp end))
                  (equal (- end (/ (+ start end) 2)) (* 1/2 (- end start))))
         :hints (("Goal" :nonlinearp t))))

(local (defthm lw-mrd-potential-telescope
         (implies (and (rationalp coefficient) (rationalp start) (rationalp middle) (rationalp end))
                  (equal (+ (* coefficient (- (/ start) (/ middle))) (* coefficient (- (/ middle) (/ end))))
                         (* coefficient (- (/ start) (/ end)))))
         :hints (("Goal" :nonlinearp t))))

(defthm lw-mellin-refined-dyadic-tail-potential
  (implies (and (rationalp cap) (<= 0 cap)
                (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap model-error))
                (rationalp start) (< 0 start) (rationalp end) (<= start end) (natp depth)
                (<= (lw-halved-width (- end start) depth) start)
                (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (<= (+ 2 index) (* (- sigma 2) start)) (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-mellin-refined-dyadic cap start end depth sigma height index model-error error exp-error)
                             (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ end)))))
  :hints (("Goal" :induct (lw-mellin-refined-dyadic cap start end depth sigma height index model-error error exp-error)
                  :do-not '(generalize eliminate-destructors)
                  :in-theory (disable (:definition lw-mellin-refined-dyadic) distributivity lw-mrd-left-distribute
                                      lw-mrd-left-span lw-mrd-right-span))
          (and stable-under-simplificationp
               '(:use (lw-mellin-refined-weighted-tail-sample lw-mrd-left-span lw-mrd-right-span
                       (:instance lw-mellin-tail-coefficient-nonnegative (rate (- sigma 2)) (mass 1))
                       (:instance lw-mrd-multiply-order (a start) (b (/ (+ start end) 2)) (factor (- sigma 2)))
                       (:instance lw-mrd-potential-telescope
                         (coefficient (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1))) (middle (/ (+ start end) 2)))
                       (:instance lw-halved-width-half (width (- end start)) (steps (- depth 1)))
                       (:instance lw-complex-add-disk
                         (left (lw-mellin-refined-dyadic cap start (/ (+ start end) 2) (- depth 1) sigma height index model-error error exp-error))
                         (radius (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ (/ (+ start end) 2)))))
                         (right (lw-mellin-refined-dyadic cap (/ (+ start end) 2) end (- depth 1) sigma height index model-error error exp-error))
                         (other-radius (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ (/ (+ start end) 2)) (/ end))))))
                 :expand ((lw-mellin-refined-dyadic cap start end depth sigma height index model-error error exp-error)
                          (lw-halved-width (- end start) depth))
                 :in-theory (disable lw-mellin-refined-weighted-tail-sample lw-complex-add-disk lw-halved-width-half
                                     distributivity lw-mrd-left-distribute lw-mrd-left-span lw-mrd-right-span)
                 :do-not '(generalize eliminate-destructors)
                 :do-not-induct t
                 :nonlinearp t))))

(local (in-theory (disable lw-mellin-refined-dyadic lw-mellin-refined-dyadic-tail-potential lw-mellin-refined-weighted-tail-sample)))

(defthm lw-mellin-refined-dyadic-tail-bound
  (implies (and (rationalp cap) (<= 0 cap)
                (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap model-error))
                (rationalp start) (< 0 start) (rationalp end) (<= start end) (natp depth)
                (<= (lw-halved-width (- end start) depth) start)
                (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (<= (+ 2 index) (* (- sigma 2) start)) (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-mellin-refined-dyadic cap start end depth sigma height index model-error error exp-error)
                             (/ (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1)) start)))
  :hints (("Goal" :use (lw-mellin-refined-dyadic-tail-potential
                        (:instance lw-mellin-tail-coefficient-nonnegative (rate (- sigma 2)) (mass 1))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-mellin-refined-dyadic cap start end depth sigma height index model-error error exp-error))
                          (radius (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1) (- (/ start) (/ end))))
                          (cap (/ (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1)) start))))
                  :nonlinearp t)))

(defthm lw-mellin-refined-dyadic-tail-at-integral-cutoff
  (implies (and (rationalp cap) (<= 0 cap)
                (rationalp model-error) (< 0 model-error) (<= model-error 1)
                (rationalp exp-error) (< 0 exp-error) (<= exp-error (lw-signal-exponential-precision cap model-error))
                (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
                (rationalp cutoff-error) (< 0 cutoff-error) (rationalp error) (< 0 error)
                (rationalp end) (<= (lw-mellin-integral-cutoff sigma index cutoff-error) end) (natp depth)
                (<= (lw-halved-width (- end (lw-mellin-integral-cutoff sigma index cutoff-error)) depth)
                    (lw-mellin-integral-cutoff sigma index cutoff-error)))
           (lw-complex-diskp
            (lw-mellin-refined-dyadic cap (lw-mellin-integral-cutoff sigma index cutoff-error) end depth sigma height index model-error error exp-error)
            (* 5/4 cutoff-error)))
  :hints (("Goal"
           :use ((:instance lw-mellin-integral-cutoff-valid (error cutoff-error))
                 (:instance lw-mellin-tail-cutoff-adequate (rate (- sigma 2)) (mass 4) (error cutoff-error))
                 (:instance lw-mellin-refined-dyadic-tail-bound (start (lw-mellin-integral-cutoff sigma index cutoff-error)))
                 (:instance lw-positive-division-bound
                   (numerator (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1)))
                   (divisor (lw-mellin-integral-cutoff sigma index cutoff-error)) (bound (* 5/4 cutoff-error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-refined-dyadic cap (lw-mellin-integral-cutoff sigma index cutoff-error) end depth sigma height index model-error error exp-error))
                   (radius (/ (* 10 (lw-mellin-tail-coefficient (- sigma 2) index 1)) (lw-mellin-integral-cutoff sigma index cutoff-error)))
                   (cap (* 5/4 cutoff-error))))
           :in-theory (e/d (lw-mellin-integral-cutoff lw-mellin-tail-coefficient)
                           (lw-mellin-refined-dyadic-tail-bound lw-mellin-integral-cutoff-valid lw-rational-power))
           :nonlinearp t)))

(defthm lw-mellin-refined-computed-tail-at-integral-cutoff
 (implies
  (and (rationalp cap) (<= 0 cap) (rationalp sigma) (< 2 sigma) (rationalp height) (natp index)
       (rationalp model-error) (< 0 model-error) (<= model-error 1)
       (rationalp error) (< 0 error) (rationalp exp-error) (< 0 exp-error)
       (<= exp-error (lw-signal-exponential-precision cap model-error))
       (rationalp cutoff-error) (< 0 cutoff-error)
       (rationalp end) (<= (lw-mellin-integral-cutoff sigma index cutoff-error) end))
  (lw-complex-diskp
   (lw-mellin-refined-dyadic cap (lw-mellin-integral-cutoff sigma index cutoff-error) end
    (lw-mellin-tail-depth (lw-mellin-integral-cutoff sigma index cutoff-error) end)
    sigma height index model-error error exp-error)
   (* 5/4 cutoff-error)))
 :hints (("Goal"
  :use ((:instance lw-mellin-integral-cutoff-valid (error cutoff-error))
        (:instance lw-mellin-tail-depth-adequate (start (lw-mellin-integral-cutoff sigma index cutoff-error)))
        (:instance lw-mellin-refined-dyadic-tail-at-integral-cutoff
          (depth (lw-mellin-tail-depth (lw-mellin-integral-cutoff sigma index cutoff-error) end))))
  :in-theory (disable lw-mellin-integral-cutoff lw-mellin-integral-cutoff-valid
                      lw-mellin-tail-depth lw-mellin-tail-depth-adequate lw-mellin-refined-dyadic-tail-at-integral-cutoff)
  :nonlinearp nil :do-not-induct t)))

