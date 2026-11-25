(in-package "ACL2")

(include-book "kernel-window")

; Transfer concentration from the actual sampler's lower weights to upper
; kernel enclosures, retaining only the requested primitive precision.
(local (in-theory
        (disable lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-kernel-weight-bounds-valid lw-kernel-weight-bounds-width lw-kernel-weight-bounds-overlap
                 lw-mellin-weight lw-mellin-kernel-error lw-mellin-component-error lw-mellin-signal-cap
                 lw-mellin-signal-cap-valid lw-log-signal-bounds (:executable-counterpart lw-log-signal-bounds)
                 lw-mellin-grid-weight-sum lw-kernel-window-radius lw-kernel-window-radius-valid
                 lw-kernel-window-left-count lw-kernel-window-right-address lw-mellin-kernel-window-concentration
                 lw-kernel-window-threshold (:executable-counterpart lw-kernel-window-threshold)
                 lw-kernel-grid-step lw-kernel-grid-step-valid lw-window-index lw-log-bounds
                 (:executable-counterpart lw-log-bounds) lw-eventual-kernel-window-data
                 lw-rational-power lw-geometric-index (:executable-counterpart lw-geometric-index)
                 lw-eventual-mellin-kernel-window-growth-budget)))

(local (defthm lw-kr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-kr-times-negative
         (implies (and (rationalp a) (rationalp b)) (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kr-negative-times
         (implies (and (rationalp a) (rationalp b)) (equal (* (- a) b) (- (* a b))))))
(local (defthm lw-kr-zero-times (equal (* 0 a) 0)))
(local (defthm lw-kr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-kr-double-negative (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-kr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-kr-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-kr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-kr-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defthm lw-mellin-kernel-error-at-most-request
  (implies (and (rationalp value) (<= 0 value) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-kernel-error value error))
                (< 0 (lw-mellin-kernel-error value error))
                (<= (lw-mellin-kernel-error value error) error)))
  :hints (("Goal" :use (lw-mellin-signal-cap-valid
                        (:instance lw-positive-division-bound (numerator error)
                          (divisor (* 3 (+ 1 (lw-mellin-signal-cap value)))) (bound error)))
                  :in-theory (enable lw-mellin-kernel-error lw-mellin-component-error) :nonlinearp t)))

(local (in-theory (disable lw-mellin-kernel-error-at-most-request)))

(defthm lw-kernel-upper-to-mellin-weight
  (implies (and (rationalp value) (<= 0 value) (rationalp rate) (<= 0 rate)
                (rationalp error) (< 0 error) (rationalp sample-error) (< 0 sample-error))
           (<= (cdr (lw-kernel-weight-bounds value rate index 1 error))
               (+ (lw-mellin-weight value rate index 1 sample-error) error sample-error)))
  :hints (("Goal" :use ((:instance lw-mellin-kernel-error-at-most-request (error sample-error))
                        (:instance lw-kernel-weight-bounds-width (sigma rate) (step 1))
                        (:instance lw-kernel-weight-bounds-width (sigma rate) (step 1) (error (lw-mellin-kernel-error value sample-error)))
                        (:instance lw-kernel-weight-bounds-overlap (sigma rate) (step 1)
                          (left-error error) (right-error (lw-mellin-kernel-error value sample-error))))
                  :in-theory (enable lw-mellin-weight))))

(defun lw-kernel-grid-upper-sum (address count rate index step error)
  (declare (xargs :measure (nfix count)))
  (if (zp count) 0
    (+ (* step (cdr (lw-kernel-weight-bounds (* address step) rate index 1 error)))
       (lw-kernel-grid-upper-sum (+ address 1) (- count 1) rate index step error))))

(defthm lw-kernel-grid-upper-sum-valid
  (implies (and (natp address) (rationalp rate) (<= 0 rate) (rationalp step) (<= 0 step))
           (and (rationalp (lw-kernel-grid-upper-sum address count rate index step error))
                (<= 0 (lw-kernel-grid-upper-sum address count rate index step error))))
  :hints (("Goal" :induct (lw-kernel-grid-upper-sum address count rate index step error))
          (and stable-under-simplificationp
               '(:use ((:instance lw-kernel-weight-bounds-valid (value (* address step)) (sigma rate) (step 1))
                       (:instance lw-kr-nonnegative-product (a step) (b (cdr (lw-kernel-weight-bounds (* address step) rate index 1 error)))))
                 :do-not-induct t))))

(local (in-theory (disable lw-kernel-upper-to-mellin-weight)))

(defthm lw-kernel-grid-upper-sum-comparison
  (implies (and (natp address) (natp count) (rationalp rate) (<= 0 rate) (rationalp step) (<= 0 step)
                (rationalp error) (< 0 error) (rationalp sample-error) (< 0 sample-error))
           (<= (lw-kernel-grid-upper-sum address count rate index step error)
               (+ (lw-mellin-grid-weight-sum address count rate index step sample-error)
                  (* count step (+ error sample-error)))))
  :hints (("Goal" :induct (lw-kernel-grid-upper-sum address count rate index step error))
          (and stable-under-simplificationp
               '(:use ((:instance lw-kernel-upper-to-mellin-weight (value (* address step)))
                       (:instance lw-kernel-weight-bounds-valid (value (* address step)) (sigma rate) (step 1))
                       (:instance lw-mellin-weight-bounded (value (* address step)) (sigma rate) (step 1) (error sample-error))
                       (:instance lw-kr-multiply-order
                         (a (cdr (lw-kernel-weight-bounds (* address step) rate index 1 error)))
                         (b (+ (lw-mellin-weight (* address step) rate index 1 sample-error) error sample-error))
                         (factor step)))
                 :expand ((lw-mellin-grid-weight-sum address count rate index step sample-error))
                 :do-not-induct t))))

(local (in-theory (disable lw-kernel-grid-upper-sum lw-kernel-grid-upper-sum-comparison)))

(defun lw-kernel-window-upper-sum (lower upper count index step error)
  (+ (lw-kernel-grid-upper-sum 0 (lw-kernel-window-left-count upper step) 250 index step error)
     (lw-kernel-grid-upper-sum (lw-kernel-window-right-address lower step) count 250 index step error)))

(defun lw-kernel-window-grid-length (upper count step)
  (* step (+ (lw-kernel-window-left-count upper step) (nfix count))))

(defthm lw-kernel-window-upper-data-valid
  (implies (and (natp count) (rationalp step) (< 0 step))
           (and (rationalp (lw-kernel-window-upper-sum lower upper count index step error))
                (<= 0 (lw-kernel-window-upper-sum lower upper count index step error))
                (rationalp (lw-kernel-window-grid-length upper count step))
                (<= 0 (lw-kernel-window-grid-length upper count step))))
  :hints (("Goal" :use ((:instance lw-kernel-grid-upper-sum-valid
                          (address 0) (count (lw-kernel-window-left-count upper step)) (rate 250))
                        (:instance lw-kernel-grid-upper-sum-valid
                          (address (lw-kernel-window-right-address lower step)) (rate 250)))
                  :in-theory (disable lw-kernel-grid-upper-sum-valid) :nonlinearp t)))

(local (in-theory (disable lw-kernel-window-grid-length)))

(defthm lw-kernel-window-upper-comparison
  (implies (and (rationalp lower) (<= 64 lower) (rationalp upper) (<= lower upper)
                (natp index) (<= (* 6061/20 upper) index) (<= index (* 625/2 lower))
                (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (natp count) (rationalp error) (< 0 error) (rationalp sample-error) (< 0 sample-error))
           (<= (lw-kernel-window-upper-sum lower upper count index step error)
               (+ (* 7 (lw-kernel-window-radius index)) (* (lw-kernel-window-grid-length upper count step) (+ error sample-error)))))
  :hints (("Goal" :use ((:instance lw-kernel-grid-upper-sum-comparison
                          (address 0) (count (lw-kernel-window-left-count upper step)) (rate 250))
                        (:instance lw-kernel-grid-upper-sum-comparison
                          (address (lw-kernel-window-right-address lower step)) (rate 250))
                        (:instance lw-mellin-kernel-window-concentration (error sample-error)))
                  :in-theory (enable lw-kernel-window-grid-length))))

(local (in-theory (disable lw-kernel-window-upper-sum lw-kernel-window-upper-comparison
                           lw-kernel-window-upper-data-valid)))

(local (defthm lw-kr-positive-refinement
         (implies (and (rationalp excess) (< 0 excess) (rationalp measure) (<= 0 measure))
                  (and (rationalp (/ excess (* 2 (+ 1 measure))))
                       (< 0 (/ excess (* 2 (+ 1 measure))))
                       (<= (* measure (/ excess (* 2 (+ 1 measure)))) (/ excess 2))))
         :hints (("Goal" :use ((:instance lw-positive-division-bound
                                (numerator (* measure excess)) (divisor (* 2 (+ 1 measure))) (bound (/ excess 2))))
                         :nonlinearp t))
         :rule-classes nil))

; Eliminate the auxiliary sampling precision by a computed rational excess.
; The primitive upper-kernel precision remains, multiplied by grid length.
(defthm lw-kernel-window-upper-concentration
  (implies (and (rationalp lower) (<= 64 lower) (rationalp upper) (<= lower upper)
                (natp index) (<= (* 6061/20 upper) index) (<= index (* 625/2 lower))
                (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (natp count) (rationalp error) (< 0 error))
           (<= (lw-kernel-window-upper-sum lower upper count index step error)
               (+ (* 7 (lw-kernel-window-radius index)) (* (lw-kernel-window-grid-length upper count step) error))))
  :hints (("Goal" :cases ((<= (lw-kernel-window-upper-sum lower upper count index step error)
                              (+ (* 7 (lw-kernel-window-radius index)) (* (lw-kernel-window-grid-length upper count step) error))))
                  :use (lw-kernel-window-upper-data-valid lw-kernel-window-radius-valid
                        (:instance lw-kr-positive-refinement (measure (lw-kernel-window-grid-length upper count step))
                          (excess (- (lw-kernel-window-upper-sum lower upper count index step error)
                                     (+ (* 7 (lw-kernel-window-radius index)) (* (lw-kernel-window-grid-length upper count step) error)))))
                        (:instance lw-kernel-window-upper-comparison
                          (sample-error (/ (- (lw-kernel-window-upper-sum lower upper count index step error)
                                               (+ (* 7 (lw-kernel-window-radius index)) (* (lw-kernel-window-grid-length upper count step) error)))
                                           (* 2 (+ 1 (lw-kernel-window-grid-length upper count step))))))))))

(local (in-theory (disable lw-kernel-window-upper-concentration lw-kernel-window-radius-normalization
                           lw-kernel-window-geometric-budget lw-rational-power-nonnegative)))

(defthm lw-kernel-window-upper-growth-budget
  (implies (and (rationalp lower) (<= 64 lower) (rationalp upper) (<= lower upper)
                (natp index) (<= (* 6061/20 upper) index) (<= index (* 625/2 lower))
                (<= (lw-geometric-index 5000/4977 128) index)
                (rationalp step) (< 0 step) (<= (* 600 step (+ 1 index)) 1)
                (natp count) (rationalp error) (< 0 error))
           (<= (* 16 (lw-kernel-window-upper-sum lower upper count index step error))
               (+ (lw-rational-power 1/252 (+ 1 index)) (* 16 (lw-kernel-window-grid-length upper count step) error))))
  :hints (("Goal" :use (lw-kernel-window-upper-concentration lw-kernel-window-radius-normalization
                        lw-kernel-window-geometric-budget
                        (:instance lw-rational-power-nonnegative (base 4977/5000) (exponent index))
                        (:instance lw-rational-power-nonnegative (base 1/252) (exponent (+ 1 index)))
                        (:instance lw-kr-multiply-order (a (* 128 (lw-rational-power 4977/5000 index))) (b 1)
                          (factor (lw-rational-power 1/252 (+ 1 index)))))
                  :nonlinearp t)))

(defun lw-kernel-window-upper-precision (upper count step target-error)
  (/ target-error (* 32 (+ 1 (lw-kernel-window-grid-length upper count step)))))

(defthm lw-kernel-window-upper-precision-budget
  (implies (and (natp count) (rationalp step) (< 0 step) (rationalp target-error) (< 0 target-error))
           (and (rationalp (lw-kernel-window-upper-precision upper count step target-error))
                (< 0 (lw-kernel-window-upper-precision upper count step target-error))
                (<= (* 16 (lw-kernel-window-grid-length upper count step)
                       (lw-kernel-window-upper-precision upper count step target-error)) (/ target-error 2))))
  :hints (("Goal" :use (lw-kernel-window-upper-data-valid
                        (:instance lw-positive-division-bound
                          (numerator (* 16 (lw-kernel-window-grid-length upper count step) target-error))
                          (divisor (* 32 (+ 1 (lw-kernel-window-grid-length upper count step)))) (bound (/ target-error 2))))
                  :nonlinearp t)))

(local (in-theory (disable lw-kernel-window-upper-growth-budget lw-kernel-window-upper-precision
                           lw-kernel-window-upper-precision-budget)))

(defthm lw-eventual-kernel-window-upper-budget
  (implies (and (rationalp start) (<= (lw-kernel-window-threshold) start)
                (rationalp cap) (< 0 cap) (rationalp mesh) (< 0 mesh)
                (natp count) (rationalp target-error) (< 0 target-error))
           (let* ((index (lw-window-index start)) (step (lw-kernel-grid-step cap 300 index mesh))
                  (lower (car (lw-log-bounds start 1/1000))) (upper (cdr (lw-log-bounds start 1/1000)))
                  (error (lw-kernel-window-upper-precision upper count step target-error)))
             (<= (* 16 (lw-kernel-window-upper-sum lower upper count index step error))
                 (+ (lw-rational-power 1/252 (+ 1 index)) (/ target-error 2)))))
  :hints (("Goal" :use ((:instance lw-eventual-kernel-window-data (target (max 64 (lw-geometric-index 5000/4977 128))))
                        (:instance lw-kernel-grid-step-valid (rate 300) (index (lw-window-index start)))
                        (:instance lw-kernel-window-upper-precision-budget
                          (upper (cdr (lw-log-bounds start 1/1000))) (step (lw-kernel-grid-step cap 300 (lw-window-index start) mesh)))
                        (:instance lw-kernel-window-upper-growth-budget
                          (lower (car (lw-log-bounds start 1/1000))) (upper (cdr (lw-log-bounds start 1/1000)))
                          (index (lw-window-index start)) (step (lw-kernel-grid-step cap 300 (lw-window-index start) mesh))
                          (error (lw-kernel-window-upper-precision (cdr (lw-log-bounds start 1/1000)) count
                                   (lw-kernel-grid-step cap 300 (lw-window-index start) mesh) target-error))))
                  :in-theory (union-theories '(lw-kernel-window-threshold max natp lw-geometric-index-natural)
                                             (theory 'minimal-theory)))))
