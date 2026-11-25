(in-package "ACL2")

(include-book "mellin-integral")
(include-book "exp-addition")
(include-book "mellin-quadrature")

(local (in-theory
        (disable lw-log-signal-bounds lw-log-signal-point lw-log-signal-base lw-log-signal-margin
                 lw-log-signal-budget lw-log-signal-lipschitz lw-log-signal-cap
                 lw-log-signal-point-valid lw-log-signal-budget-valid lw-log-signal-margin-valid
                 lw-signal-bounds lw-signal-bounds-raw lw-signal-precision lw-signal-count
                 lw-signal-precision-positive lw-signal-precision-at-most-one
                 lw-gz-bounds-raw lw-gz-bounds-raw-valid lw-gz-lower-quadratic-growth
                 lw-rpow-bounds lw-rpow-bounds-sound lw-rational-power
                 lw-landau-window-search lw-failed-search-refined-gz-ceiling
                 lw-mellin-signal lw-mellin-weight lw-mellin-phase lw-mellin-sample
                 lw-mellin-signal-error lw-mellin-kernel-error lw-mellin-phase-error
                 lw-mellin-signal-cap lw-mellin-kernel-cap lw-mellin-component-error
                 lw-mellin-error-budgets lw-mellin-signal-bounded lw-mellin-weight-bounded
                 lw-mellin-phase-unit lw-mellin-phase-rational
                 lw-complexp lw-complex-diskp lw-complex-add lw-complex-sub lw-complex-scale
                 lw-complex-disk-enlarge lw-disk-enlarge
                 (:executable-counterpart lw-log-signal-bounds))))

(local (defthm lw-mw-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mw-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mw-negative-times
         (implies (and (rationalp a) (rationalp b))
                  (equal (* (- a) b) (- (* a b))))
         :hints (("Goal" :use ((:instance lw-mw-times-negative (a b) (b a)))
                         :in-theory (disable lw-mw-times-negative)))))
(local (defthm lw-mw-times-zero (equal (* 0 a) 0)))
(local (defthm lw-mw-times-minus-one
         (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-mw-double-negative
         (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-mw-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-mw-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(defun lw-log-signal-primitive-error (value error)
  (lw-signal-precision (lw-log-signal-point value error) 0 (/ (lw-log-signal-budget error) 2)))

(defthm lw-log-signal-primitive-error-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (and (rationalp (lw-log-signal-primitive-error value error))
                (< 0 (lw-log-signal-primitive-error value error))
                (<= (lw-log-signal-primitive-error value error) 1)))
  :hints (("Goal" :use (lw-log-signal-point-valid lw-log-signal-budget-valid
                        (:instance lw-signal-precision-positive (value (lw-log-signal-point value error))
                          (ceiling 0) (error (/ (lw-log-signal-budget error) 2)))
                        (:instance lw-signal-precision-at-most-one (value (lw-log-signal-point value error))
                          (ceiling 0) (error (/ (lw-log-signal-budget error) 2)))))))

(defthm lw-log-signal-base-lower-is-gz
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (equal (car (lw-log-signal-base value error))
                  (car (lw-gz-bounds-raw (lw-log-signal-point value error) (lw-signal-count (lw-log-signal-point value error))
                                         (lw-log-signal-primitive-error value error)))))
  :hints (("Goal" :use (lw-log-signal-point-valid lw-log-signal-primitive-error-valid
                        (:instance lw-gz-bounds-raw-valid (value (lw-log-signal-point value error))
                          (count (lw-signal-count (lw-log-signal-point value error)))
                          (epsilon (lw-log-signal-primitive-error value error))))
                  :in-theory (e/d (lw-log-signal-base lw-signal-bounds lw-signal-bounds-raw
                                    lw-interval-sub lw-interval-scale) (lw-log-signal-primitive-error-valid)))))

(defun lw-log-signal-window-cap (value error start ceiling numerator denominator)
  (let ((point (lw-log-signal-point value error)))
    (if (and (<= start point) (<= (* point point) (* start start start)))
        (* (+ ceiling 1) (car (lw-rpow-bounds point numerator denominator (lw-signal-precision point ceiling 1/4))))
      (* 4 point point))))

(defthm lw-log-signal-window-cap-valid
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error)
                (rationalp ceiling) (<= 0 ceiling) (natp numerator) (posp denominator) (<= numerator denominator))
           (and (rationalp (lw-log-signal-window-cap value error start ceiling numerator denominator))
                (<= 0 (lw-log-signal-window-cap value error start ceiling numerator denominator))))
  :hints (("Goal" :use (lw-log-signal-point-valid
                        (:instance lw-signal-precision-positive (value (lw-log-signal-point value error)) (error 1/4))
                        (:instance lw-rpow-bounds-sound (value (lw-log-signal-point value error))
                          (epsilon (lw-signal-precision (lw-log-signal-point value error) ceiling 1/4))))
                  :nonlinearp t)))

; The window test is an exact comparison at the constructed rational
; sample point. Its two branches use proved search failure or proved
; growth, never an assumed ceiling on a log-variable sample.
(defthm lw-failed-search-log-signal-ceiling
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (<= (car (lw-log-signal-bounds value error))
               (lw-log-signal-window-cap value error start ceiling numerator denominator)))
  :hints (("Goal" :use (lw-log-signal-point-valid lw-log-signal-primitive-error-valid lw-log-signal-margin-valid
                        lw-log-signal-base-lower-is-gz
                        (:instance lw-failed-search-refined-gz-ceiling (point (lw-log-signal-point value error))
                          (epsilon (lw-log-signal-primitive-error value error)))
                        (:instance lw-gz-lower-quadratic-growth (value (lw-log-signal-point value error))
                          (count (lw-signal-count (lw-log-signal-point value error)))
                          (epsilon (lw-log-signal-primitive-error value error))))
                  :in-theory (e/d (lw-log-signal-bounds) (lw-log-signal-primitive-error lw-log-signal-base-lower-is-gz
                                                        lw-log-signal-primitive-error-valid)))))

(defun lw-mellin-window-cap (value sigma index error start ceiling numerator denominator)
  (lw-log-signal-window-cap value (lw-mellin-signal-error value sigma index 1 error)
                            start ceiling numerator denominator))

; Weight is the interval length times the evaluator's unit-weight kernel.
; These are precisely the samples used by the dyadic integral constructor.
(defun lw-mellin-computed-window-row (value weight sigma height index error start ceiling numerator denominator)
  (let ((phase (lw-mellin-phase value sigma height index 1 error)))
    (list (lw-mellin-signal value sigma index 1 error)
          (* weight (lw-mellin-weight value sigma index 1 error)) (car phase) (cdr phase)
          (lw-mellin-window-cap value sigma index error start ceiling numerator denominator))))

(defthm lw-failed-search-computed-mellin-row-valid
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp value) (<= 0 value) (rationalp weight) (<= 0 weight)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (lw-mellin-rowp (lw-mellin-computed-window-row value weight sigma height index error start ceiling numerator denominator)))
  :hints (("Goal"
           :use ((:instance lw-mellin-error-budgets (step 1))
                 (:instance lw-failed-search-log-signal-ceiling (error (lw-mellin-signal-error value sigma index 1 error)))
                 (:instance lw-log-signal-window-cap-valid (error (lw-mellin-signal-error value sigma index 1 error)))
                 (:instance lw-mellin-signal-bounded (step 1)) (:instance lw-mellin-weight-bounded (step 1))
                 (:instance lw-mellin-phase-unit (step 1)) (:instance lw-mellin-phase-rational (step 1)))
           :in-theory (e/d (lw-mellin-signal lw-complexp lw-complex-diskp)
                           (lw-failed-search-log-signal-ceiling lw-log-signal-window-cap-valid))
           :nonlinearp t)))

(defthm lw-phase-value-zero
  (equal (lw-phase-value 0 error) (cons 1 0))
  :hints (("Goal" :in-theory (enable lw-phase-value lw-phase-grid lw-phase-steps lw-precision-fuel
                                    lw-phase-rotation lw-phase-denominator lw-complex-power lw-complex-mul lw-complex-scale))))

(defthm lw-mellin-phase-zero-height
  (equal (lw-mellin-phase value sigma 0 index step error) (cons 1 0))
  :hints (("Goal" :in-theory (enable lw-mellin-phase))))

(defthm lw-mellin-sample-zero-height
  (equal (cdr (lw-mellin-sample value sigma 0 index step error)) 0)
  :hints (("Goal" :in-theory (enable lw-mellin-sample lw-complex-scale))))

(defthm lw-mellin-computed-row-value
  (implies (and (rationalp value) (<= 0 value) (rationalp weight)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (let* ((row (lw-mellin-computed-window-row value weight sigma height index error start ceiling numerator denominator))
                  (point (lw-complex-scale weight (lw-mellin-sample value sigma height index 1 error))))
             (and (equal (* (nth 0 row) (nth 1 row) (nth 2 row)) (car point))
                  (equal (* (nth 0 row) (nth 1 row) (nth 3 row)) (cdr point)))))
  :hints (("Goal" :use ((:instance lw-mellin-signal-bounded (step 1)) (:instance lw-mellin-weight-bounded (step 1))
                        (:instance lw-mellin-phase-rational (step 1)))
                  :in-theory (enable lw-mellin-sample lw-complex-scale lw-complexp))))

(defthm lw-mellin-computed-row-plain
  (implies (and (rationalp value) (<= 0 value) (rationalp weight)
                (rationalp sigma) (<= 0 sigma) (rationalp error) (< 0 error))
           (let ((row (lw-mellin-computed-window-row value weight sigma height index error start ceiling numerator denominator)))
             (equal (* (nth 0 row) (nth 1 row))
                    (car (lw-complex-scale weight (lw-mellin-sample value sigma 0 index 1 error))))))
  :hints (("Goal" :use ((:instance lw-mellin-signal-bounded (step 1)) (:instance lw-mellin-weight-bounded (step 1)))
                  :in-theory (enable lw-mellin-sample lw-complex-scale))))

(defun lw-mellin-dyadic-window-rows (left right depth sigma height index error start ceiling numerator denominator)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (list (lw-mellin-computed-window-row left (- right left) sigma height index error start ceiling numerator denominator))
    (let ((middle (/ (+ left right) 2)))
      (append (lw-mellin-dyadic-window-rows left middle (- depth 1) sigma height index error start ceiling numerator denominator)
              (lw-mellin-dyadic-window-rows middle right (- depth 1) sigma height index error start ceiling numerator denominator)))))

(defthm lw-failed-search-dyadic-window-rows-valid
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp left) (<= 0 left) (rationalp right) (<= left right)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (lw-mellin-rowsp (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator)))
  :hints (("Goal" :induct (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator)
                  :in-theory (disable lw-mellin-computed-window-row lw-mellin-rowp))
          (and stable-under-simplificationp
               '(:use ((:instance lw-failed-search-computed-mellin-row-valid (value left) (weight (- right left))))
                 :in-theory (disable lw-mellin-computed-window-row lw-mellin-rowp lw-failed-search-computed-mellin-row-valid)))))

(defthm lw-mellin-dyadic-window-rows-value
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= left right)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (let* ((rows (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator))
                  (point (lw-mellin-dyadic-sum left right depth sigma height index error)))
             (and (equal (lw-mellin-real rows) (car point))
                  (equal (lw-mellin-imag rows) (cdr point)))))
  :hints (("Goal" :induct (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator)
                  :in-theory (e/d (lw-complex-add) (lw-mellin-computed-window-row)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-computed-row-value (value left) (weight (- right left))))
                 :in-theory (e/d (lw-complex-add)
                                 (lw-mellin-computed-window-row lw-mellin-computed-row-value))))))

(defthm lw-mellin-dyadic-window-rows-plain
  (implies (and (rationalp left) (<= 0 left) (rationalp right) (<= left right)
                (rationalp sigma) (<= 0 sigma) (rationalp error) (< 0 error))
           (equal (lw-mellin-plain (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator))
                  (car (lw-mellin-dyadic-sum left right depth sigma 0 index error))))
  :hints (("Goal" :induct (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator)
                  :in-theory (e/d (lw-complex-add) (lw-mellin-computed-window-row)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-computed-row-plain (value left) (weight (- right left))))
                 :in-theory (e/d (lw-complex-add)
                                 (lw-mellin-computed-window-row lw-mellin-computed-row-plain))))))

; The complex coefficient and its unmodulated companion are actual
; computed dyadic sums. The only ceiling premise is failed search.
(defthm lw-failed-search-dyadic-mellin-bound
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp left) (<= 0 left) (rationalp right) (<= left right)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-mellin-dyadic-sum left right depth sigma height index error)
            (- (* 2 (lw-mellin-budget
                      (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator)))
               (car (lw-mellin-dyadic-sum left right depth sigma 0 index error)))))
  :hints (("Goal" :use (lw-failed-search-dyadic-window-rows-valid lw-mellin-dyadic-window-rows-value lw-mellin-dyadic-window-rows-plain
                        (:instance lw-mellin-dyadic-rational (start left) (end right) (point-error error))
                        (:instance lw-mellin-one-sided-bound
                          (rows (lw-mellin-dyadic-window-rows left right depth sigma height index error start ceiling numerator denominator))))
                  :in-theory (e/d (lw-complex-diskp)
                                  (lw-diskp lw-mellin-rowsp lw-mellin-budget lw-mellin-real lw-mellin-imag lw-mellin-plain
                                   lw-mellin-dyadic-sum lw-mellin-dyadic-window-rows lw-mellin-dyadic-rational lw-mellin-one-sided-bound
                                   lw-failed-search-dyadic-window-rows-valid lw-mellin-dyadic-window-rows-value lw-mellin-dyadic-window-rows-plain)))))

(local (in-theory
        (disable lw-mellin-spatial-slope lw-mellin-spatial-error-factor
                 lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope
                 lw-kernel-spatial-cap lw-kernel-spatial-slope
                 lw-mellin-spatial-parameters lw-mellin-signal-spatial-parameters lw-kernel-spatial-parameters
                 lw-mellin-integral-depth lw-mellin-integral-precision lw-mellin-bounded-integral
                 lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid
                 lw-mellin-dyadic-cross-depth lw-mellin-dyadic-sum lw-mellin-dyadic-rational
                 lw-mellin-dyadic-window-rows lw-failed-search-dyadic-mellin-bound)))

(defthm lw-mellin-dyadic-zero-height
  (equal (cdr (lw-mellin-dyadic-sum left right depth sigma 0 index error)) 0)
  :hints (("Goal" :induct (lw-mellin-dyadic-sum left right depth sigma 0 index error)
                  :in-theory (enable lw-mellin-dyadic-sum lw-complex-add lw-complex-scale))))

(defthm lw-mellin-integral-zero-height
  (equal (cdr (lw-mellin-integral sigma 0 index error)) 0)
  :hints (("Goal" :in-theory (enable lw-mellin-integral lw-mellin-bounded-integral))))

(defthm lw-mellin-spatial-slope-height-dominates
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (rationalp step) (<= 0 step))
           (<= (lw-mellin-spatial-slope cap sigma 0 step)
               (lw-mellin-spatial-slope cap sigma height step)))
  :hints (("Goal" :use (lw-mellin-signal-spatial-parameters lw-kernel-spatial-parameters)
                  :in-theory (enable lw-mellin-spatial-slope) :nonlinearp t)))

(local (defthm lw-mw-mesh-nonnegative
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth)) (<= 0 (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))
         :rule-classes (:rewrite :type-prescription)))

; The height-zero companion in the one-sided inequality initially uses
; the complex sample's grid. Compare it with the evaluator's own grid.
(defthm lw-mellin-zero-grid-comparison
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (natp index) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-complex-sub
             (lw-mellin-dyadic-sum 0 cap (lw-mellin-integral-depth cap sigma height error)
                                   sigma 0 index (lw-mellin-integral-precision cap error))
             (lw-mellin-bounded-integral cap sigma 0 index error)) error))
  :hints (("Goal"
           :use ((:instance lw-mellin-spatial-parameters (step 1))
                 (:instance lw-mellin-spatial-parameters (step 1) (height 0))
                 (:instance lw-mellin-spatial-slope-height-dominates (step 1))
                 lw-mellin-integral-depth-adequate
                 (:instance lw-mellin-integral-depth-adequate (height 0))
                 lw-mellin-integral-precision-valid
                 (:instance lw-mw-mesh-nonnegative (width cap) (depth (lw-mellin-integral-depth cap sigma height error)))
                 (:instance lw-mw-mesh-nonnegative (width cap) (depth (lw-mellin-integral-depth cap sigma 0 error)))
                 (:instance lw-mellin-dyadic-cross-depth (height 0)
                   (left-depth (lw-mellin-integral-depth cap sigma height error))
                   (right-depth (lw-mellin-integral-depth cap sigma 0 error))
                   (left-error (lw-mellin-integral-precision cap error))
                   (right-error (lw-mellin-integral-precision cap error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                           (lw-mellin-dyadic-sum 0 cap (lw-mellin-integral-depth cap sigma height error)
                                                 sigma 0 index (lw-mellin-integral-precision cap error))
                           (lw-mellin-bounded-integral cap sigma 0 index error)))
                   (radius (* cap (+ (* (lw-mellin-spatial-slope cap sigma 0 1)
                                       (+ (lw-halved-width cap (lw-mellin-integral-depth cap sigma height error))
                                          (lw-halved-width cap (lw-mellin-integral-depth cap sigma 0 error))))
                                    (* (lw-mellin-spatial-error-factor cap 1)
                                       (+ (lw-mellin-integral-precision cap error) (lw-mellin-integral-precision cap error))))))
                   (cap error)))
           :in-theory (e/d (lw-mellin-bounded-integral) (lw-mellin-spatial-slope-height-dominates lw-mw-mesh-nonnegative))
           :nonlinearp t)))

(defthm lw-complex-disk-real-bound
  (implies (lw-complex-diskp point radius) (<= (abs (car point)) radius))
  :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp) :nonlinearp t)))

(defun lw-mellin-bounded-window-rows (cap sigma height index error start ceiling numerator denominator)
  (lw-mellin-dyadic-window-rows 0 cap (lw-mellin-integral-depth cap sigma height error)
                               sigma height index (lw-mellin-integral-precision cap error) start ceiling numerator denominator))

; Both complex and unmodulated values are now the default computed
; integrals, with no common-grid or coefficient approximation premise.
(defthm lw-failed-search-bounded-mellin-bound
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma)
                (rationalp height) (natp index) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-mellin-bounded-integral cap sigma height index error)
            (+ (* 2 (lw-mellin-budget (lw-mellin-bounded-window-rows cap sigma height index error start ceiling numerator denominator)))
               (- (car (lw-mellin-bounded-integral cap sigma 0 index error))) error)))
  :hints (("Goal"
           :use (lw-mellin-integral-precision-valid
                 lw-mellin-zero-grid-comparison
                 (:instance lw-mellin-bounded-integral-rational (height 0))
                 (:instance lw-mellin-dyadic-rational
                   (start 0) (end cap) (height 0) (depth (lw-mellin-integral-depth cap sigma height error))
                   (point-error (lw-mellin-integral-precision cap error)))
                 (:instance lw-failed-search-dyadic-window-rows-valid
                   (left 0) (right cap) (depth (lw-mellin-integral-depth cap sigma height error))
                   (error (lw-mellin-integral-precision cap error)))
                 (:instance lw-mellin-sums-rational
                   (rows (lw-mellin-bounded-window-rows cap sigma height index error start ceiling numerator denominator)))
                 (:instance lw-failed-search-dyadic-mellin-bound
                   (left 0) (right cap) (depth (lw-mellin-integral-depth cap sigma height error))
                   (error (lw-mellin-integral-precision cap error)))
                 (:instance lw-complex-disk-real-bound
                   (point (lw-complex-sub
                           (lw-mellin-dyadic-sum 0 cap (lw-mellin-integral-depth cap sigma height error)
                                                 sigma 0 index (lw-mellin-integral-precision cap error))
                           (lw-mellin-bounded-integral cap sigma 0 index error))) (radius error))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-bounded-integral cap sigma height index error))
                   (radius (- (* 2 (lw-mellin-budget (lw-mellin-bounded-window-rows cap sigma height index error start ceiling numerator denominator)))
                              (car (lw-mellin-dyadic-sum 0 cap (lw-mellin-integral-depth cap sigma height error)
                                                        sigma 0 index (lw-mellin-integral-precision cap error)))))
                   (cap (+ (* 2 (lw-mellin-budget (lw-mellin-bounded-window-rows cap sigma height index error start ceiling numerator denominator)))
                           (- (car (lw-mellin-bounded-integral cap sigma 0 index error))) error))))
           :in-theory (e/d (lw-mellin-bounded-integral lw-mellin-bounded-window-rows lw-complex-sub lw-complexp)
                           (lw-complex-disk-real-bound lw-mellin-zero-grid-comparison lw-mellin-budget
                            lw-mellin-real lw-mellin-imag lw-mellin-plain lw-mellin-mass lw-mellin-rowsp
                            lw-failed-search-dyadic-window-rows-valid lw-mellin-sums-rational lw-mellin-bounded-integral-rational)))))

(defun lw-mellin-window-budget (sigma height index error start ceiling numerator denominator)
  (lw-mellin-budget (lw-mellin-bounded-window-rows
                    (lw-mellin-integral-cutoff sigma index error) sigma height index (/ error 2) start ceiling numerator denominator)))

(defthm lw-failed-search-improper-mellin-bound
  (implies (and (rationalp start) (< 1 start) (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (not (lw-landau-window-search start ceiling numerator denominator))
                (rationalp sigma) (< 2 sigma) (rationalp height) (natp index) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-mellin-integral sigma height index error)
            (+ (* 2 (lw-mellin-window-budget sigma height index error start ceiling numerator denominator))
               (- (car (lw-mellin-integral sigma 0 index error))) (/ error 2))))
  :hints (("Goal" :use (lw-mellin-integral-cutoff-valid
                        (:instance lw-failed-search-bounded-mellin-bound
                          (cap (lw-mellin-integral-cutoff sigma index error)) (error (/ error 2))))
                  :in-theory (e/d (lw-mellin-integral lw-mellin-window-budget)
                                  (lw-mellin-integral-cutoff lw-mellin-integral-cutoff-valid lw-failed-search-bounded-mellin-bound
                                   lw-mellin-bounded-window-rows lw-mellin-budget)))))

(local (in-theory
        (disable lw-exp-bounds lw-exp-neg-bounds lw-exp-bounds-square-shift lw-exp-bounds-product-transport
                 lw-exp-bounds-valid lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-kernel-weight-scale-nonnegative lw-kernel-weight-bounds-valid
                 lw-log-signal-delta lw-log-signal-delta-valid)))

(local (defthm lw-mw-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-mw-division-product
         (implies (and (rationalp a) (<= 0 a) (rationalp scale) (<= 0 scale)
                       (rationalp lower) (< 0 lower) (rationalp upper) (< 0 upper) (<= (* a lower) upper))
                  (<= (/ (* a scale) upper) (/ scale lower)))
         :hints (("Goal" :use ((:instance inverse-of-* (x lower))
                              (:instance lw-mw-multiply-order (a (* a lower)) (b upper) (factor (/ scale lower)))
                              (:instance lw-positive-division-bound (numerator (* a scale)) (divisor upper) (bound (/ scale lower))))
                         :in-theory (disable inverse-of-*)
                         :nonlinearp t))
         :rule-classes nil))

; Multiplying by the lower exponential twice shifts the kernel's rate
; by two. All three evaluator precisions are independent.
(defthm lw-kernel-lower-quadratic-shift
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 2 sigma) (rationalp step) (<= 0 step))
           (<= (* (car (lw-exp-bounds value signal-error)) (car (lw-exp-bounds value signal-error))
                  (car (lw-kernel-weight-bounds value sigma index step kernel-error)))
               (cdr (lw-kernel-weight-bounds value (- sigma 2) index step shifted-error))))
  :hints (("Goal"
           :use ((:instance lw-exp-bounds-square-shift (rate (- sigma 2))
                   (rate-error (lw-kernel-weight-precision value index step shifted-error))
                   (total-error (lw-kernel-weight-precision value index step kernel-error)))
                 (:instance lw-exp-bounds-valid (epsilon signal-error))
                 (:instance lw-exp-bounds-valid (value (* (- sigma 2) value))
                   (epsilon (lw-kernel-weight-precision value index step shifted-error)))
                 (:instance lw-exp-bounds-valid (value (* sigma value))
                   (epsilon (lw-kernel-weight-precision value index step kernel-error)))
                 lw-kernel-weight-scale-nonnegative
                 (:instance lw-mw-division-product
                   (a (* (car (lw-exp-bounds value signal-error)) (car (lw-exp-bounds value signal-error))))
                   (scale (lw-kernel-weight-scale value index step))
                   (lower (car (lw-exp-bounds (* (- sigma 2) value) (lw-kernel-weight-precision value index step shifted-error))))
                   (upper (cdr (lw-exp-bounds (* sigma value) (lw-kernel-weight-precision value index step kernel-error))))))
           :in-theory (enable lw-kernel-weight-bounds lw-exp-neg-bounds)
           :nonlinearp t)))

(defthm lw-log-signal-point-exp-cap
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (<= (lw-log-signal-point value error) (* 2 (car (lw-exp-bounds value (lw-log-signal-delta value error))))))
  :hints (("Goal" :use (lw-log-signal-delta-valid (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value error))))
                  :in-theory (enable lw-log-signal-point))))

(defthm lw-log-signal-growth-kernel-bound
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 2 sigma)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (<= (* 4 (lw-log-signal-point value error) (lw-log-signal-point value error)
                  (car (lw-kernel-weight-bounds value sigma index step kernel-error)))
               (* 16 (cdr (lw-kernel-weight-bounds value (- sigma 2) index step shifted-error)))))
  :hints (("Goal" :use (lw-log-signal-point-valid lw-log-signal-point-exp-cap
                        (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value error)))
                        (:instance lw-kernel-weight-bounds-valid (error kernel-error))
                        (:instance lw-kernel-lower-quadratic-shift (signal-error (lw-log-signal-delta value error))))
                  :in-theory (disable lw-log-signal-point-exp-cap lw-kernel-lower-quadratic-shift)
                  :nonlinearp t)))

(defthm lw-log-signal-absolute-exp-growth
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (<= (abs (car (lw-log-signal-bounds value error)))
               (* 17 (car (lw-exp-bounds value (lw-log-signal-delta value error)))
                     (car (lw-exp-bounds value (lw-log-signal-delta value error))))))
  :hints (("Goal" :use (lw-log-signal-point-valid lw-log-signal-point-exp-cap lw-log-signal-primitive-error-valid
                        lw-log-signal-base-lower-is-gz lw-log-signal-margin-valid lw-log-signal-budget-valid lw-log-signal-delta-valid
                        (:instance lw-exp-bounds-valid (epsilon (lw-log-signal-delta value error)))
                        (:instance lw-gz-lower-quadratic-growth (value (lw-log-signal-point value error))
                          (count (lw-signal-count (lw-log-signal-point value error)))
                          (epsilon (lw-log-signal-primitive-error value error))))
                  :in-theory (e/d (lw-log-signal-bounds)
                                  (lw-log-signal-point-exp-cap lw-log-signal-primitive-error lw-log-signal-primitive-error-valid
                                   lw-log-signal-base-lower-is-gz))
                  :nonlinearp t)))

(local (defthm lw-mw-abs-times-nonnegative
         (implies (and (rationalp a) (rationalp b) (<= 0 b)) (equal (abs (* a b)) (* (abs a) b)))
         :hints (("Goal" :cases ((<= 0 a)) :nonlinearp t))))

(defthm lw-mellin-sample-growth-kernel-bound
  (implies (and (rationalp value) (<= 0 value) (rationalp sigma) (<= 2 sigma) (rationalp height)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (lw-complex-diskp (lw-mellin-sample value sigma height index step error)
                             (* 17 (cdr (lw-kernel-weight-bounds value (- sigma 2) index step shifted-error)))))
  :hints (("Goal"
           :use (lw-mellin-error-budgets lw-mellin-signal-bounded lw-mellin-weight-bounded lw-mellin-phase-unit
                 (:instance lw-log-signal-absolute-exp-growth (error (lw-mellin-signal-error value sigma index step error)))
                 (:instance lw-kernel-lower-quadratic-shift
                   (signal-error (lw-log-signal-delta value (lw-mellin-signal-error value sigma index step error)))
                   (kernel-error (lw-mellin-kernel-error value error)))
                 (:instance lw-kernel-weight-bounds-valid (sigma (- sigma 2)) (error shifted-error))
                 (:instance lw-complex-scale-disk (point (lw-mellin-phase value sigma height index step error))
                   (radius 1) (factor (* (lw-mellin-signal value sigma index step error) (lw-mellin-weight value sigma index step error))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-sample value sigma height index step error))
                   (radius (abs (* (lw-mellin-signal value sigma index step error) (lw-mellin-weight value sigma index step error))))
                   (cap (* 17 (cdr (lw-kernel-weight-bounds value (- sigma 2) index step shifted-error))))))
           :in-theory (e/d (lw-mellin-sample lw-mellin-signal lw-mellin-weight)
                           (lw-log-signal-absolute-exp-growth lw-kernel-lower-quadratic-shift lw-complex-scale-disk))
           :nonlinearp t)))

; Uniform tails of the existing weighted-grid constructor, rather than
; arbitrary data supplied with an assumed coefficient remainder.
(defun lw-mellin-tail-cells (start step count)
  (declare (xargs :measure (nfix count)))
  (if (zp count) nil
    (cons (cons start step) (lw-mellin-tail-cells (+ start step) step (- count 1)))))

(defthm lw-mellin-tail-cells-valid
  (implies (and (rationalp start) (<= 0 start) (rationalp step) (<= 0 step))
           (lw-mellin-cellsp (lw-mellin-tail-cells start step count)))
  :hints (("Goal" :induct (lw-mellin-tail-cells start step count))))

(local (defthm lw-mw-zero-disk
         (lw-complex-diskp (cons 0 0) 0)
         :hints (("Goal" :in-theory (enable lw-complex-diskp lw-complexp lw-diskp)))))

(local (in-theory
        (disable lw-mellin-sample-growth-kernel-bound lw-mellin-sum-raw lw-kernel-tail-rectangles
                 lw-kernel-tail-rectangles-at-cutoff lw-mellin-tail-cutoff lw-mellin-tail-cutoff-adequate)))

(defthm lw-mellin-tail-samples-kernel-bound
  (implies (and (rationalp start) (<= 0 start) (rationalp step) (<= 0 step)
                (rationalp sigma) (<= 2 sigma) (rationalp height) (rationalp error) (< 0 error))
           (lw-complex-diskp
            (lw-mellin-sum-raw (lw-mellin-tail-cells start step count) sigma height index error)
            (* 17 (lw-kernel-tail-rectangles start step count (- sigma 2) index shifted-error))))
  :hints (("Goal" :induct (lw-mellin-tail-cells start step count)
                  :in-theory (disable (:definition lw-mellin-tail-cells)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-sample-growth-kernel-bound (value start))
                       (:instance lw-complex-add-disk
                         (left (lw-mellin-sample start sigma height index step error))
                         (radius (* 17 (cdr (lw-kernel-weight-bounds start (- sigma 2) index step shifted-error))))
                         (right (lw-mellin-sum-raw (lw-mellin-tail-cells (+ start step) step (- count 1)) sigma height index error))
                         (other-radius (* 17 (lw-kernel-tail-rectangles (+ start step) step (- count 1) (- sigma 2) index shifted-error)))))
                 :expand ((lw-mellin-tail-cells start step count)
                          (lw-mellin-sum-raw (lw-mellin-tail-cells start step count) sigma height index error)
                          (lw-mellin-sum-raw (cons (cons start step) (lw-mellin-tail-cells (+ start step) step (- count 1)))
                                             sigma height index error)
                          (lw-mellin-sum-raw nil sigma height index error)
                          (lw-kernel-tail-rectangles start step count (- sigma 2) index shifted-error))
                 :in-theory (disable lw-complex-add-disk)))))

(defthm lw-mellin-tail-samples-at-cutoff
  (implies (and (rationalp sigma) (< 2 sigma) (rationalp height) (natp index) (natp count)
                (rationalp target-error) (< 0 target-error) (rationalp error) (< 0 error)
                (rationalp step) (< 0 step) (<= step (lw-mellin-tail-cutoff (- sigma 2) index 17 target-error)))
           (lw-complex-diskp
            (lw-mellin-sum-raw (lw-mellin-tail-cells (lw-mellin-tail-cutoff (- sigma 2) index 17 target-error) step count)
                               sigma height index error) target-error))
  :hints (("Goal"
           :use ((:instance lw-mellin-tail-cutoff-adequate (rate (- sigma 2)) (mass 17) (error target-error))
                 (:instance lw-mellin-tail-samples-kernel-bound
                   (start (lw-mellin-tail-cutoff (- sigma 2) index 17 target-error)) (shifted-error 1))
                 (:instance lw-kernel-tail-rectangles-at-cutoff (rate (- sigma 2)) (mass 17) (error 1))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-mellin-sum-raw
                           (lw-mellin-tail-cells (lw-mellin-tail-cutoff (- sigma 2) index 17 target-error) step count)
                           sigma height index error))
                   (radius (* 17 (lw-kernel-tail-rectangles
                                  (lw-mellin-tail-cutoff (- sigma 2) index 17 target-error) step count (- sigma 2) index 1)))
                   (cap target-error)))
           :in-theory (disable lw-mellin-tail-samples-kernel-bound lw-mellin-tail-cells))))
