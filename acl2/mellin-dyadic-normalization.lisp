(in-package "ACL2")

(include-book "mellin-normalization")
(include-book "mellin-cutoffs")

; Decode the actual dyadic budget as a uniform sum, then refine the default
; evaluator to a grid satisfying the normalized kernel bound.
(local (in-theory
        (disable lw-mellin-grid-window-budget lw-mellin-grid-window-budget-normalized
                 lw-mellin-dyadic-window-rows lw-mellin-computed-window-row lw-mellin-budget
                 lw-mellin-window-cap lw-log-signal-window-cap lw-mellin-weight lw-mellin-signal-error
                 lw-rpow-bounds lw-signal-precision lw-log-signal-point lw-log-signal-bounds
                 (:executable-counterpart lw-log-signal-bounds)
                 lw-mellin-sample lw-mellin-signal lw-mellin-phase
                 lw-rational-power lw-rational-power-add-exponents lw-rational-power-product
                 lw-rational-power-at-least-one lw-rational-power-nonnegative lw-rational-power-positive
                 lw-halved-width lw-log-bounds (:executable-counterpart lw-log-bounds))))

(local (defthm lw-dn-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-dn-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-dn-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-dn-zero-times (equal (* 0 a) 0)))
(local (defthm lw-dn-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-dn-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-dn-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-dn-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-dn-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-dn-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defun lw-dn-concat-induction (address left)
         (declare (xargs :measure (nfix left)))
         (if (zp left) address (lw-dn-concat-induction (+ address 1) (- left 1)))))
(local (defthm lw-dn-grid-zero
         (implies (zp count) (equal (lw-mellin-grid-window-budget address count index step error start ceiling numerator denominator) 0))
         :hints (("Goal" :in-theory (enable lw-mellin-grid-window-budget)))))
(local (defthm lw-dn-grid-one
         (equal (lw-mellin-grid-window-budget address 1 index step error start ceiling numerator denominator)
                (* step (lw-mellin-window-cap (* address step) 252 index error start ceiling numerator denominator)
                        (lw-mellin-weight (* address step) 252 index 1 error)))
         :hints (("Goal" :expand ((lw-mellin-grid-window-budget address 1 index step error start ceiling numerator denominator))))))

(defthm lw-mellin-grid-window-budget-concatenate
  (implies (and (natp address) (natp left) (natp right))
           (equal (lw-mellin-grid-window-budget address (+ left right) index step error start ceiling numerator denominator)
                  (+ (lw-mellin-grid-window-budget address left index step error start ceiling numerator denominator)
                     (lw-mellin-grid-window-budget (+ address left) right index step error start ceiling numerator denominator))))
  :hints (("Goal" :induct (lw-dn-concat-induction address left)
                  :in-theory (enable lw-mellin-grid-window-budget))))

(local (defthm lw-dn-power-two-valid
         (and (natp (lw-rational-power 2 depth)) (<= 1 (lw-rational-power 2 depth)))
         :hints (("Goal" :induct (lw-rational-power 2 depth) :in-theory (enable lw-rational-power)))
         :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-dn-power-two-zero
         (implies (zp depth) (equal (lw-rational-power 2 depth) 1))
         :hints (("Goal" :in-theory (enable lw-rational-power)))))
(local (defthm lw-dn-power-two-step
         (implies (posp depth) (equal (lw-rational-power 2 depth) (* 2 (lw-rational-power 2 (- depth 1)))))
         :hints (("Goal" :expand ((lw-rational-power 2 depth))))))
(local (defthm lw-dn-add-double
         (implies (rationalp value) (equal (+ value value) (* 2 value)))))
(local (defthm lw-dn-tail-double
         (implies (and (rationalp a) (rationalp b)) (equal (+ a b b) (+ a (* 2 b))))))
(local (defthm lw-dn-two-halves
         (implies (rationalp value) (equal (* 2 1/2 value) value))
         :hints (("Goal" :use ((:instance associativity-of-* (x 2) (y 1/2) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-dn-left-commutes)))))
(local (defthm lw-dn-add-halves
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ (* 1/2 a) (* 1/2 a) b) (+ a b)))
         :hints (("Goal" :nonlinearp t))))

(local (defun lw-dn-grid-induction (address depth)
         (declare (xargs :measure (nfix depth)))
         (if (zp depth) address
           (list (lw-dn-grid-induction address (- depth 1))
                 (lw-dn-grid-induction (+ address (lw-rational-power 2 (- depth 1))) (- depth 1))))))

(local (defthm lw-dn-budget-append
         (equal (lw-mellin-budget (append first second)) (+ (lw-mellin-budget first) (lw-mellin-budget second)))
         :hints (("Goal" :induct (append first second) :in-theory (enable lw-mellin-budget)))))
(local (defthm lw-dn-dyadic-zero
         (implies (zp depth)
                  (equal (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator)
                         (list (lw-mellin-computed-window-row left (- right left) sigma height index error start ceiling numerator denominator))))
         :hints (("Goal" :in-theory (enable lw-mellin-dyadic-window-rows)))))
(local (defthm lw-dn-dyadic-positive
         (implies (not (zp depth))
                  (equal (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator)
                         (append (lw-mellin-dyadic-window-rows left (/ (+ left right) 2) (- depth 1) sigma height index error start ceiling numerator denominator)
                                 (lw-mellin-dyadic-window-rows (/ (+ left right) 2) right (- depth 1) sigma height index error start ceiling numerator denominator))))
         :hints (("Goal" :expand ((lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator))))
         :rule-classes nil))

(local (in-theory (disable lw-mellin-grid-window-budget-concatenate)))

(defthm lw-mellin-dyadic-window-budget-grid
  (implies (and (natp address) (natp depth) (rationalp step) (< 0 step))
           (equal (lw-mellin-budget
                   (lw-mellin-dyadic-window-rows (* address step) (* (+ address (lw-rational-power 2 depth)) step)
                                                depth 252 height index error start ceiling numerator denominator))
                  (lw-mellin-grid-window-budget address (lw-rational-power 2 depth) index step error start ceiling numerator denominator)))
  :hints (("Goal" :induct (lw-dn-grid-induction address depth))
          (and stable-under-simplificationp
               '(:use (lw-dn-power-two-step
                       (:instance lw-dn-dyadic-positive (left (* address step)) (right (* (+ address (lw-rational-power 2 depth)) step)) (sigma 252))
                       (:instance lw-mellin-grid-window-budget-concatenate
                         (left (lw-rational-power 2 (- depth 1))) (right (lw-rational-power 2 (- depth 1)))))
                 :expand ((lw-mellin-dyadic-window-rows (* address step) (* (+ address (lw-rational-power 2 depth)) step)
                                                       depth 252 height index error start ceiling numerator denominator))
                 :do-not-induct t))))

(local (defthm lw-dn-half-zero
         (implies (zp depth) (equal (lw-halved-width width depth) width))
         :hints (("Goal" :in-theory (enable lw-halved-width)))))
(local (defthm lw-dn-half-rational
         (implies (rationalp width) (rationalp (lw-halved-width width depth)))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))
         :rule-classes (:rewrite :type-prescription)))
(local (defthm lw-dn-half-nonnegative
         (implies (and (rationalp width) (<= 0 width)) (<= 0 (lw-halved-width width depth)))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))))
(local (defthm lw-dn-half-positive
         (implies (and (rationalp width) (< 0 width)) (< 0 (lw-halved-width width depth)))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))))

(defthm lw-dyadic-grid-length
  (implies (and (rationalp width) (natp depth))
           (equal (* (lw-rational-power 2 depth) (lw-halved-width width depth)) width))
  :hints (("Goal" :induct (lw-dn-grid-induction 0 depth))
          (and stable-under-simplificationp
               '(:expand ((lw-halved-width width depth)) :do-not-induct t))))

(defthm lw-halved-width-monotone-depth
  (implies (and (rationalp width) (<= 0 width) (natp small) (natp large) (<= small large))
           (<= (lw-halved-width width large) (lw-halved-width width small)))
  :hints (("Goal" :induct (lw-halved-width width large)
                  :in-theory (enable (:induction lw-halved-width)))
          (and stable-under-simplificationp
               '(:cases ((equal small large))
                 :use ((:instance lw-dn-half-nonnegative (depth (- large 1))))
                 :in-theory (disable lw-dn-half-nonnegative)
                 :expand ((lw-halved-width width large))
                 :do-not-induct t))))

(local (in-theory (disable lw-mellin-dyadic-window-budget-grid lw-dyadic-grid-length lw-halved-width-monotone-depth
                           lw-geometric-index (:executable-counterpart lw-geometric-index))))

(defthm lw-mellin-dyadic-window-budget-normalized
  (implies (and (rationalp start) (<= 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp index) (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000))) index)
                (<= index (* 625/2 (car (lw-log-bounds start 1/1000))))
                (<= (lw-geometric-index 5000/4977 128) index)
                (rationalp cap) (< 0 cap) (natp depth) (<= (* 600 (lw-halved-width cap depth) (+ 1 index)) 1)
                (rationalp error) (< 0 error) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator))
           (<= (lw-mellin-budget (lw-mellin-dyadic-window-rows 0 cap depth 252 height index error start ceiling numerator denominator))
               (* (+ (* 4 ceiling) 5) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index)))))
  :hints (("Goal" :use ((:instance lw-mellin-dyadic-window-budget-grid (address 0) (step (lw-halved-width cap depth)))
                        (:instance lw-dyadic-grid-length (width cap))
                        (:instance lw-mellin-grid-window-budget-normalized
                          (count (lw-rational-power 2 depth)) (step (lw-halved-width cap depth)))))))

(local (in-theory (disable lw-mellin-dyadic-window-budget-normalized lw-mellin-mesh-depth lw-mellin-mesh-depth-adequate)))

(defun lw-mellin-normalization-depth (cap index)
  (lw-mellin-mesh-depth cap (/ (* 600 (+ 1 (nfix index))))))

(defthm lw-mellin-normalization-depth-adequate
  (implies (and (rationalp cap) (< 0 cap) (natp index))
           (and (natp (lw-mellin-normalization-depth cap index))
                (<= (* 600 (+ 1 index) (lw-halved-width cap (lw-mellin-normalization-depth cap index))) 1)))
  :hints (("Goal" :use ((:instance lw-mellin-mesh-depth-adequate (width cap) (mesh (/ (* 600 (+ 1 index)))))
                        (:instance inverse-of-* (x (* 600 (+ 1 index))))
                        (:instance lw-dn-multiply-order
                          (a (lw-halved-width cap (lw-mellin-normalization-depth cap index))) (b (/ (* 600 (+ 1 index))))
                          (factor (* 600 (+ 1 index)))))
                  :in-theory (disable inverse-of-*) :nonlinearp t)))

(local (in-theory (disable lw-mellin-normalization-depth lw-mellin-normalization-depth-adequate
                           lw-mellin-integral-depth lw-mellin-integral-depth-adequate lw-mellin-integral-precision
                           lw-mellin-integral-precision-valid lw-mellin-spatial-slope lw-mellin-spatial-error-factor
                           lw-mellin-spatial-parameters lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope)))

(defun lw-mellin-coefficient-depth (cap height index error)
  (+ (nfix (lw-mellin-integral-depth cap 252 height (/ error 2))) (nfix (lw-mellin-integral-depth cap 252 0 (/ error 2))) (lw-mellin-normalization-depth cap index)))

(defun lw-mellin-coefficient-refined-sum (cap driver-height height index error)
  (lw-mellin-dyadic-sum 0 cap (lw-mellin-coefficient-depth cap driver-height index error) 252 height index (lw-mellin-integral-precision cap (/ error 2))))

(defthm lw-mellin-coefficient-refinement-checks
  (implies (and (rationalp cap) (< 0 cap) (rationalp height) (natp index) (rationalp error) (< 0 error))
           (and (natp (lw-mellin-coefficient-depth cap height index error)) (natp (lw-mellin-integral-depth cap 252 height (/ error 2))) (natp (lw-mellin-integral-depth cap 252 0 (/ error 2)))
                (rationalp (lw-mellin-integral-precision cap (/ error 2))) (< 0 (lw-mellin-integral-precision cap (/ error 2)))
                (<= (* 600 (+ 1 index) (lw-halved-width cap (lw-mellin-coefficient-depth cap height index error))) 1)
                (<= (* cap (+ (* (lw-mellin-spatial-slope cap 252 height 1) (+ (lw-halved-width cap (lw-mellin-coefficient-depth cap height index error)) (lw-halved-width cap (lw-mellin-integral-depth cap 252 height (/ error 2))))) (* (lw-mellin-spatial-error-factor cap 1) (+ (lw-mellin-integral-precision cap (/ error 2)) (lw-mellin-integral-precision cap (/ error 2)))))) (/ error 2))
                (<= (* cap (+ (* (lw-mellin-spatial-slope cap 252 0 1) (+ (lw-halved-width cap (lw-mellin-coefficient-depth cap height index error)) (lw-halved-width cap (lw-mellin-integral-depth cap 252 0 (/ error 2))))) (* (lw-mellin-spatial-error-factor cap 1) (+ (lw-mellin-integral-precision cap (/ error 2)) (lw-mellin-integral-precision cap (/ error 2)))))) (/ error 2))))
  :hints (("Goal" :use ((:instance lw-mellin-normalization-depth-adequate)
                        (:instance lw-mellin-integral-depth-adequate (sigma 252) (height height) (error (/ error 2)))
                        (:instance lw-mellin-integral-depth-adequate (sigma 252) (height 0) (error (/ error 2)))
                        (:instance lw-mellin-integral-precision-valid (sigma 252) (error (/ error 2)))
                        (:instance lw-mellin-spatial-parameters (sigma 252) (height height) (step 1))
                        (:instance lw-mellin-spatial-parameters (sigma 252) (height 0) (step 1))
                        (:instance lw-dn-nonnegative-product (a cap) (b (lw-mellin-spatial-slope cap 252 height 1)))
                        (:instance lw-dn-nonnegative-product (a cap) (b (lw-mellin-spatial-slope cap 252 0 1)))
                        (:instance lw-halved-width-monotone-depth (width cap) (small (lw-mellin-normalization-depth cap index)) (large (lw-mellin-coefficient-depth cap height index error)))
                        (:instance lw-halved-width-monotone-depth (width cap) (small (lw-mellin-integral-depth cap 252 height (/ error 2))) (large (lw-mellin-coefficient-depth cap height index error)))
                        (:instance lw-halved-width-monotone-depth (width cap) (small (lw-mellin-integral-depth cap 252 0 (/ error 2))) (large (lw-mellin-coefficient-depth cap height index error)))
                        (:instance lw-dn-multiply-order (a (lw-halved-width cap (lw-mellin-coefficient-depth cap height index error))) (b (lw-halved-width cap (lw-mellin-normalization-depth cap index))) (factor (* 600 (+ 1 index))))
                        (:instance lw-dn-multiply-order (a (lw-halved-width cap (lw-mellin-coefficient-depth cap height index error))) (b (lw-halved-width cap (lw-mellin-integral-depth cap 252 height (/ error 2)))) (factor (* cap (lw-mellin-spatial-slope cap 252 height 1))))
                        (:instance lw-dn-multiply-order (a (lw-halved-width cap (lw-mellin-coefficient-depth cap height index error))) (b (lw-halved-width cap (lw-mellin-integral-depth cap 252 0 (/ error 2)))) (factor (* cap (lw-mellin-spatial-slope cap 252 0 1))))) :nonlinearp nil)))

(local (in-theory (disable lw-mellin-coefficient-depth lw-mellin-coefficient-refinement-checks
                           lw-mellin-dyadic-cross-depth lw-mellin-dyadic-sum lw-mellin-bounded-integral
                           lw-mellin-dyadic-rational lw-complex-diskp lw-complex-disk-enlarge lw-disk-enlarge)))

(defthm lw-mellin-coefficient-refinement-rational
  (implies (and (rationalp cap) (< 0 cap) (rationalp driver-height) (rationalp height)
                (natp index) (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-coefficient-refined-sum cap driver-height height index error)))
  :hints (("Goal" :use ((:instance lw-mellin-coefficient-refinement-checks (height driver-height))
                        (:instance lw-mellin-dyadic-rational (start 0) (end cap) (depth (lw-mellin-coefficient-depth cap driver-height index error)) (sigma 252) (point-error (lw-mellin-integral-precision cap (/ error 2))))))))

(defthm lw-mellin-coefficient-refinement-comparison
  (implies (and (rationalp cap) (< 0 cap) (rationalp driver-height) (rationalp height)
                (or (equal height driver-height) (equal height 0))
                (natp index) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-coefficient-refined-sum cap driver-height height index error)
                            (lw-mellin-bounded-integral cap 252 height index (/ error 2))) (/ error 2)))
  :hints (("Goal" :use ((:instance lw-mellin-coefficient-refinement-checks (height driver-height))
                        (:instance lw-mellin-spatial-parameters (sigma 252) (step 1))
                        (:instance lw-mellin-dyadic-cross-depth (left-depth (lw-mellin-coefficient-depth cap driver-height index error)) (right-depth (lw-mellin-integral-depth cap 252 height (/ error 2))) (sigma 252) (left-error (lw-mellin-integral-precision cap (/ error 2))) (right-error (lw-mellin-integral-precision cap (/ error 2))))
                        (:instance lw-complex-disk-enlarge (point (lw-complex-sub (lw-mellin-dyadic-sum 0 cap (lw-mellin-coefficient-depth cap driver-height index error) 252 height index (lw-mellin-integral-precision cap (/ error 2))) (lw-mellin-dyadic-sum 0 cap (lw-mellin-integral-depth cap 252 height (/ error 2)) 252 height index (lw-mellin-integral-precision cap (/ error 2))))) (radius (* cap (+ (* (lw-mellin-spatial-slope cap 252 height 1) (+ (lw-halved-width cap (lw-mellin-coefficient-depth cap driver-height index error)) (lw-halved-width cap (lw-mellin-integral-depth cap 252 height (/ error 2))))) (* (lw-mellin-spatial-error-factor cap 1) (+ (lw-mellin-integral-precision cap (/ error 2)) (lw-mellin-integral-precision cap (/ error 2))))))) (cap (/ error 2))))
                  :in-theory (enable lw-mellin-bounded-integral) :nonlinearp nil)))

(local (in-theory (disable lw-mellin-coefficient-refined-sum lw-mellin-coefficient-refinement-rational
                           lw-mellin-coefficient-refinement-comparison lw-failed-search-dyadic-mellin-bound
                           lw-landau-window-search)))

(defthm lw-failed-search-refined-coefficient-normalized
  (implies (and (rationalp start) (< 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp index) (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000))) index)
                (<= index (* 625/2 (car (lw-log-bounds start 1/1000))))
                (<= (lw-geometric-index 5000/4977 128) index)
                (rationalp cap) (< 0 cap) (rationalp height) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator)))
           (lw-complex-diskp
            (lw-mellin-coefficient-refined-sum cap height height index error)
            (- (* (+ (* 8 ceiling) 10) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))) (car (lw-mellin-coefficient-refined-sum cap height 0 index error)))))
  :hints (("Goal" :use (lw-mellin-coefficient-refinement-checks
                        (:instance lw-mellin-coefficient-refinement-rational (driver-height height) (height 0))
                        (:instance lw-failed-search-dyadic-mellin-bound (left 0) (right cap) (depth (lw-mellin-coefficient-depth cap height index error)) (sigma 252) (error (lw-mellin-integral-precision cap (/ error 2))))
                        (:instance lw-mellin-dyadic-window-budget-normalized (depth (lw-mellin-coefficient-depth cap height index error)) (error (lw-mellin-integral-precision cap (/ error 2))))
                        (:instance lw-complex-disk-enlarge (point (lw-mellin-dyadic-sum 0 cap (lw-mellin-coefficient-depth cap height index error) 252 height index (lw-mellin-integral-precision cap (/ error 2)))) (radius (- (* 2 (lw-mellin-budget (lw-mellin-dyadic-window-rows 0 cap (lw-mellin-coefficient-depth cap height index error) 252 height index (lw-mellin-integral-precision cap (/ error 2)) start ceiling numerator denominator))) (car (lw-mellin-dyadic-sum 0 cap (lw-mellin-coefficient-depth cap height index error) 252 0 index (lw-mellin-integral-precision cap (/ error 2)))))) (cap (- (* (+ (* 8 ceiling) 10) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))) (car (lw-mellin-dyadic-sum 0 cap (lw-mellin-coefficient-depth cap height index error) 252 0 index (lw-mellin-integral-precision cap (/ error 2))))))))
                  :in-theory (enable lw-mellin-coefficient-refined-sum) :nonlinearp nil)))

(local (in-theory (disable lw-complex-sub lw-complex-add lw-complexp lw-complex-add-disk
                           lw-complex-disk-real-bound
                           lw-failed-search-refined-coefficient-normalized)))

(local (defthm lw-dn-cancel-difference
         (implies (and (lw-complexp coarse) (lw-complexp fine))
                  (equal (lw-complex-add (lw-complex-sub coarse fine) fine) coarse))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))))

(local (defthm lw-dn-real-difference-bound
         (implies (and (lw-complexp a) (lw-complexp b) (rationalp radius)
                       (lw-complex-diskp (lw-complex-sub a b) radius))
                  (<= (- (car b) (car a)) radius))
         :hints (("Goal" :use ((:instance lw-complex-disk-real-bound (point (lw-complex-sub a b))))
                         :in-theory (enable lw-complexp lw-complex-sub)))
         :rule-classes nil))

(local (defthm lw-dn-coefficient-transport
         (implies (and (lw-complexp coarse) (lw-complexp fine) (lw-complexp unmodulated) (lw-complexp fine-unmodulated)
                       (rationalp cap) (rationalp error) (<= 0 error)
                       (lw-complex-diskp fine (- cap (car fine-unmodulated)))
                       (lw-complex-diskp (lw-complex-sub fine coarse) (/ error 2))
                       (lw-complex-diskp (lw-complex-sub fine-unmodulated unmodulated) (/ error 2)))
                  (lw-complex-diskp coarse (+ cap (- (car unmodulated)) error)))
         :hints (("Goal"
                  :use ((:instance lw-complex-difference-symmetric (left fine) (right coarse) (radius (/ error 2)))
                        (:instance lw-dn-real-difference-bound (a fine-unmodulated) (b unmodulated) (radius (/ error 2)))
                        (:instance lw-complex-add-disk (left (lw-complex-sub coarse fine)) (radius (/ error 2))
                          (right fine) (other-radius (- cap (car fine-unmodulated))))
                        (:instance lw-complex-disk-enlarge (point coarse)
                          (radius (+ (/ error 2) (- cap (car fine-unmodulated)))) (cap (+ cap (- (car unmodulated)) error))))
                  :in-theory (enable lw-complexp)))
         :rule-classes nil))

(local (in-theory (disable lw-mellin-integral lw-mellin-integral-rational lw-mellin-integral-cutoff
                           lw-mellin-integral-cutoff-valid lw-mellin-bounded-integral-rational)))

(defthm lw-failed-search-improper-coefficient-normalized
  (implies (and (rationalp start) (< 1 start) (<= 64 (car (lw-log-bounds start 1/1000)))
                (natp index) (<= (* 6061/20 (cdr (lw-log-bounds start 1/1000))) index)
                (<= index (* 625/2 (car (lw-log-bounds start 1/1000))))
                (<= (lw-geometric-index 5000/4977 128) index)
                (rationalp height) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator)))
           (lw-complex-diskp (lw-mellin-integral 252 height index error) (+ (* (+ (* 8 ceiling) 10) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))) (- (car (lw-mellin-integral 252 0 index error))) error)))
  :hints (("Goal" :use ((:instance lw-mellin-integral-cutoff-valid (sigma 252))
                        (:instance lw-failed-search-refined-coefficient-normalized (cap (lw-mellin-integral-cutoff 252 index error)))
                        (:instance lw-mellin-coefficient-refinement-rational (cap (lw-mellin-integral-cutoff 252 index error)) (driver-height height) (height height))
                        (:instance lw-mellin-coefficient-refinement-rational (cap (lw-mellin-integral-cutoff 252 index error)) (driver-height height) (height 0))
                        (:instance lw-mellin-coefficient-refinement-comparison (cap (lw-mellin-integral-cutoff 252 index error)) (driver-height height) (height height))
                        (:instance lw-mellin-coefficient-refinement-comparison (cap (lw-mellin-integral-cutoff 252 index error)) (driver-height height) (height 0))
                        (:instance lw-mellin-integral-rational (sigma 252) (height height))
                        (:instance lw-mellin-integral-rational (sigma 252) (height 0))
                        (:instance lw-dn-coefficient-transport (coarse (lw-mellin-integral 252 height index error)) (fine (lw-mellin-coefficient-refined-sum (lw-mellin-integral-cutoff 252 index error) height height index error)) (unmodulated (lw-mellin-integral 252 0 index error)) (fine-unmodulated (lw-mellin-coefficient-refined-sum (lw-mellin-integral-cutoff 252 index error) height 0 index error)) (cap (* (+ (* 8 ceiling) 10) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))))))
                  :in-theory (enable lw-mellin-integral) :nonlinearp nil)))

(local (in-theory (disable lw-failed-search-improper-coefficient-normalized lw-kernel-window-threshold
                           (:executable-counterpart lw-kernel-window-threshold) lw-window-index lw-eventual-kernel-window-data)))

(defthm lw-eventual-failed-search-improper-coefficient-normalized
  (implies (and (rationalp start) (< 1 start) (<= (lw-kernel-window-threshold) start)
                (rationalp height) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator)))
           (let ((index (lw-window-index start)))
             (lw-complex-diskp (lw-mellin-integral 252 height index error) (+ (* (+ (* 8 ceiling) 10) (lw-rational-power (/ (- 252 (/ numerator denominator))) (+ 1 index))) (- (car (lw-mellin-integral 252 0 index error))) error))))
  :hints (("Goal" :use ((:instance lw-eventual-kernel-window-data (target (max 64 (lw-geometric-index 5000/4977 128))))
                        (:instance lw-failed-search-improper-coefficient-normalized (index (lw-window-index start))))
                  :in-theory (union-theories '(lw-kernel-window-threshold max natp lw-geometric-index-natural)
                                             (theory 'minimal-theory)))))
