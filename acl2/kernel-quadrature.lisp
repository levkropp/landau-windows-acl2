(in-package "ACL2")

(include-book "kernel-window-refinement")

; The tail evaluator puts the cell length inside the kernel constructor.
; Concentration uses external cell weights. Their primitive precisions
; differ, so relate their actual enclosures rather than identifying them.
(local (in-theory
        (disable lw-exp-term lw-exp-neg-bounds lw-exp-neg-bounds-valid lw-exp-neg-bounds-overlap
                 lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-kernel-weight-bounds-width lw-kernel-weight-bounds-valid lw-kernel-weight-bounds-overlap
                 lw-kernel-tail-rectangles lw-kernel-grid-upper-sum
                 lw-kernel-window-upper-sum lw-kernel-window-grid-length lw-kernel-window-upper-precision
                 lw-kernel-window-left-count lw-kernel-window-right-address
                 lw-kernel-window-upper-data-valid lw-kernel-window-upper-precision-budget
                 lw-kernel-window-upper-growth-budget lw-eventual-kernel-window-upper-budget
                 lw-kernel-window-threshold (:executable-counterpart lw-kernel-window-threshold)
                 lw-kernel-grid-step lw-kernel-grid-step-valid lw-window-index lw-log-bounds
                 (:executable-counterpart lw-log-bounds) lw-eventual-kernel-window-data
                 lw-rational-power lw-geometric-index (:executable-counterpart lw-geometric-index))))

(local (defthm lw-kq-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-kq-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kq-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-kq-zero-times (equal (* 0 a) 0)))
(local (defthm lw-kq-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-kq-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-kq-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-kq-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kq-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-kernel-weight-step-overlap
  (implies (and (rationalp value) (<= 0 value) (rationalp rate) (<= 0 rate)
                (rationalp step) (<= 0 step))
           (<= (car (lw-kernel-weight-bounds value rate index step error))
               (* step (cdr (lw-kernel-weight-bounds value rate index 1 unit-error)))))
  :hints (("Goal" :use ((:instance lw-exp-neg-bounds-overlap (value (* rate value))
                          (left-error (lw-kernel-weight-precision value index step error))
                          (right-error (lw-kernel-weight-precision value index 1 unit-error)))
                        (:instance lw-exp-neg-bounds-valid (value (* rate value))
                          (epsilon (lw-kernel-weight-precision value index step error)))
                        (:instance lw-exp-neg-bounds-valid (value (* rate value))
                          (epsilon (lw-kernel-weight-precision value index 1 unit-error)))
                        (:instance lw-kq-multiply-order
                          (a (car (lw-exp-neg-bounds (* rate value) (lw-kernel-weight-precision value index step error))))
                          (b (cdr (lw-exp-neg-bounds (* rate value) (lw-kernel-weight-precision value index 1 unit-error))))
                          (factor (* step (lw-exp-term value index)))))
                  :in-theory (enable lw-kernel-weight-bounds lw-kernel-weight-scale) :nonlinearp t)))

(local (in-theory (disable lw-kernel-weight-step-overlap)))

(defthm lw-kernel-upper-step-bound
  (implies (and (rationalp value) (<= 0 value) (rationalp rate) (<= 0 rate)
                (rationalp step) (<= 0 step) (rationalp error) (< 0 error))
           (<= (cdr (lw-kernel-weight-bounds value rate index step error))
               (+ (* step (cdr (lw-kernel-weight-bounds value rate index 1 unit-error))) error)))
  :hints (("Goal" :use (lw-kernel-weight-step-overlap (:instance lw-kernel-weight-bounds-width (sigma rate))))))

(local (in-theory (disable lw-kernel-upper-step-bound)))

(local (defthm lw-kq-rectangles-zero
         (implies (zp count) (equal (lw-kernel-tail-rectangles start step count rate index error) 0))
         :hints (("Goal" :in-theory (enable lw-kernel-tail-rectangles)))))
(local (defthm lw-kq-grid-zero
         (implies (zp count) (equal (lw-kernel-grid-upper-sum address count rate index step error) 0))
         :hints (("Goal" :in-theory (enable lw-kernel-grid-upper-sum)))))

(defthm lw-kernel-tail-rectangles-grid-bound
  (implies (and (natp address) (natp count) (rationalp rate) (<= 0 rate)
                (rationalp step) (< 0 step) (rationalp error) (< 0 error))
           (<= (lw-kernel-tail-rectangles (* address step) step count rate index error)
               (+ (lw-kernel-grid-upper-sum address count rate index step unit-error) (* count error))))
  :hints (("Goal" :induct (lw-kernel-grid-upper-sum address count rate index step unit-error)
                  :in-theory (enable (:induction lw-kernel-grid-upper-sum)))
          (and stable-under-simplificationp
               '(:use ((:instance lw-kernel-upper-step-bound (value (* address step))))
                 :expand ((lw-kernel-grid-upper-sum address count rate index step unit-error)
                          (lw-kernel-tail-rectangles (* address step) step count rate index error))
                 :do-not-induct t))))

(local (in-theory (disable lw-kernel-tail-rectangles-grid-bound)))

(defthm lw-kernel-tail-rectangles-valid
  (implies (and (rationalp start) (<= 0 start) (rationalp rate) (<= 0 rate) (rationalp step) (<= 0 step))
           (and (rationalp (lw-kernel-tail-rectangles start step count rate index error))
                (<= 0 (lw-kernel-tail-rectangles start step count rate index error))))
  :hints (("Goal" :induct (lw-kernel-tail-rectangles start step count rate index error)
                  :in-theory (enable lw-kernel-tail-rectangles))
          (and stable-under-simplificationp
               '(:use ((:instance lw-kernel-weight-bounds-valid (value start) (sigma rate)))
                 :do-not-induct t))))

(defun lw-kernel-window-cell-count (upper count step)
  (+ (lw-kernel-window-left-count upper step) (nfix count)))

(defthm lw-kernel-window-cell-count-natural
  (natp (lw-kernel-window-cell-count upper count step))
  :rule-classes (:rewrite :type-prescription))

(defun lw-kernel-window-rectangles (lower upper count index step error)
  (+ (lw-kernel-tail-rectangles 0 step (lw-kernel-window-left-count upper step) 250 index error)
     (lw-kernel-tail-rectangles (* step (lw-kernel-window-right-address lower step)) step count 250 index error)))

(defthm lw-kernel-window-rectangles-valid
  (implies (and (rationalp step) (< 0 step))
           (and (rationalp (lw-kernel-window-rectangles lower upper count index step error))
                (<= 0 (lw-kernel-window-rectangles lower upper count index step error))))
  :hints (("Goal" :use ((:instance lw-kernel-tail-rectangles-valid
                          (start 0) (count (lw-kernel-window-left-count upper step)) (rate 250))
                        (:instance lw-kernel-tail-rectangles-valid
                          (start (* step (lw-kernel-window-right-address lower step))) (rate 250)))
                  :in-theory (disable lw-kernel-tail-rectangles-valid))))

(defthm lw-kernel-window-rectangles-comparison
  (implies (and (natp count) (rationalp step) (< 0 step) (rationalp error) (< 0 error))
           (<= (lw-kernel-window-rectangles lower upper count index step error)
               (+ (lw-kernel-window-upper-sum lower upper count index step unit-error)
                  (* (lw-kernel-window-cell-count upper count step) error))))
  :hints (("Goal" :use ((:instance lw-kernel-tail-rectangles-grid-bound
                          (address 0) (count (lw-kernel-window-left-count upper step)) (rate 250))
                        (:instance lw-kernel-tail-rectangles-grid-bound
                          (address (lw-kernel-window-right-address lower step)) (rate 250)))
                  :in-theory (enable lw-kernel-window-upper-sum))))

(local (in-theory (disable lw-kernel-window-cell-count lw-kernel-window-rectangles lw-kernel-window-rectangles-comparison)))

(defun lw-kernel-window-cell-precision (upper count step target-error)
  (/ target-error (* 32 (+ 1 (lw-kernel-window-cell-count upper count step)))))

(defthm lw-kernel-window-cell-precision-budget
  (implies (and (rationalp target-error) (< 0 target-error))
           (and (rationalp (lw-kernel-window-cell-precision upper count step target-error))
                (< 0 (lw-kernel-window-cell-precision upper count step target-error))
                (<= (* 16 (lw-kernel-window-cell-count upper count step)
                       (lw-kernel-window-cell-precision upper count step target-error)) (/ target-error 2))))
  :hints (("Goal" :use ((:instance lw-positive-division-bound
                          (numerator (* 16 (lw-kernel-window-cell-count upper count step) target-error))
                          (divisor (* 32 (+ 1 (lw-kernel-window-cell-count upper count step)))) (bound (/ target-error 2))))
                  :nonlinearp t)))

(local (in-theory (disable lw-kernel-window-cell-precision lw-kernel-window-cell-precision-budget)))

(defthm lw-kernel-window-rectangles-budget
  (implies (and (rationalp lower) (<= 64 lower) (rationalp upper) (<= lower upper)
                (natp index) (<= (* 6061/20 upper) index) (<= index (* 625/2 lower))
                (<= (lw-geometric-index 5000/4977 128) index)
                (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (natp count) (rationalp target-error) (< 0 target-error))
           (<= (* 16 (lw-kernel-window-rectangles lower upper count index step
                       (lw-kernel-window-cell-precision upper count step target-error)))
               (+ (lw-rational-power 1/252 (+ 1 index)) target-error)))
  :hints (("Goal" :use (lw-kernel-window-cell-precision-budget lw-kernel-window-upper-precision-budget
                        (:instance lw-kernel-window-rectangles-comparison
                          (error (lw-kernel-window-cell-precision upper count step target-error))
                          (unit-error (lw-kernel-window-upper-precision upper count step target-error)))
                        (:instance lw-kernel-window-upper-growth-budget
                          (error (lw-kernel-window-upper-precision upper count step target-error)))))))

(local (in-theory (disable lw-kernel-window-rectangles-budget)))

(defthm lw-eventual-kernel-window-rectangles-budget
  (implies (and (rationalp start) (<= (lw-kernel-window-threshold) start)
                (rationalp cap) (< 0 cap) (rationalp mesh) (< 0 mesh)
                (natp count) (rationalp target-error) (< 0 target-error))
           (let* ((index (lw-window-index start)) (step (lw-kernel-grid-step cap 300 index mesh))
                  (lower (car (lw-log-bounds start 1/1000))) (upper (cdr (lw-log-bounds start 1/1000))))
             (<= (* 16 (lw-kernel-window-rectangles lower upper count index step
                         (lw-kernel-window-cell-precision upper count step target-error)))
                 (+ (lw-rational-power 1/252 (+ 1 index)) target-error))))
  :hints (("Goal" :use ((:instance lw-eventual-kernel-window-data (target (max 64 (lw-geometric-index 5000/4977 128))))
                        (:instance lw-kernel-grid-step-valid (rate 300) (index (lw-window-index start)))
                        (:instance lw-kernel-window-rectangles-budget
                          (lower (car (lw-log-bounds start 1/1000))) (upper (cdr (lw-log-bounds start 1/1000)))
                          (index (lw-window-index start)) (step (lw-kernel-grid-step cap 300 (lw-window-index start) mesh))))
                  :in-theory (union-theories '(lw-kernel-window-threshold max natp lw-geometric-index-natural)
                                             (theory 'minimal-theory)))))
