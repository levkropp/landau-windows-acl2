(in-package "ACL2")

(include-book "mellin-continuity")

; The quadrature step is outside the unit-weight sample.  Dyadic splitting
; therefore preserves the exact interval mass at every refinement depth.
(defun lw-mellin-dyadic-sum (start end depth sigma height index point-error)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (lw-complex-scale (- end start) (lw-mellin-sample start sigma height index 1 point-error))
    (let ((middle (/ (+ start end) 2)))
      (lw-complex-add (lw-mellin-dyadic-sum start middle (- depth 1) sigma height index point-error)
                      (lw-mellin-dyadic-sum middle end (- depth 1) sigma height index point-error)))))

(defun lw-mellin-dyadic-check (start end depth sigma index point-error)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (lw-mellin-sample-check start sigma index 1 point-error)
    (let ((middle (/ (+ start end) 2)))
      (and (lw-mellin-dyadic-check start middle (- depth 1) sigma index point-error)
           (lw-mellin-dyadic-check middle end (- depth 1) sigma index point-error)))))

(defthm lw-mellin-dyadic-check-valid
  (implies (and (rationalp start) (rationalp end) (<= 0 start) (<= start end)
                (rationalp sigma) (<= 0 sigma) (rationalp point-error) (< 0 point-error))
           (lw-mellin-dyadic-check start end depth sigma index point-error))
  :hints (("Goal" :induct (lw-mellin-dyadic-check start end depth sigma index point-error)
                  :in-theory (disable lw-mellin-sample-check))))

(local (in-theory
        (disable lw-mellin-sample lw-mellin-spatial-slope lw-mellin-spatial-error-factor
                 lw-mellin-signal-spatial-cap lw-mellin-signal-spatial-slope lw-log-signal-bounds
                 lw-mellin-spatial-parameters lw-mellin-sample-spatial-transport
                 lw-complexp lw-complex-add lw-complex-sub lw-complex-scale lw-complex-diskp
                 lw-complex-disk-enlarge lw-disk-enlarge
                 (:executable-counterpart lw-log-signal-bounds))))
(local (defthm lw-mp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mp-times-negative
         (implies (and (rationalp a) (rationalp b))
                  (equal (* a (- b)) (- (* a b))))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mp-negative-times
         (implies (and (rationalp a) (rationalp b))
                  (equal (* (- a) b) (- (* a b))))
         :hints (("Goal" :use ((:instance lw-mp-times-negative (a b) (b a)))
                         :in-theory (disable lw-mp-times-negative)))))
(local (defthm lw-mp-left-distribute
         (implies (and (rationalp a) (rationalp b) (rationalp c))
                  (equal (* (+ a b) c) (+ (* a c) (* b c))))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mp-times-zero (equal (* 0 a) 0)))
(local (defthm lw-mp-times-minus-one
         (implies (rationalp a) (equal (* -1 a) (- a)))))
(local (defthm lw-mp-double-negative
         (implies (rationalp a) (equal (- (- a)) a))))
(local (defthm lw-mp-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))
(local (defthm lw-mp-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp c) (<= 0 c))
                  (<= (* a c) (* b c)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-mp-scale-difference
   (implies (and (lw-complexp a) (lw-complexp b) (rationalp weight))
            (equal (lw-complex-sub (lw-complex-scale weight a) (lw-complex-scale weight b))
                   (lw-complex-scale weight (lw-complex-sub a b))))
   :hints (("Goal" :in-theory (enable lw-complexp lw-complex-sub lw-complex-scale)))
   :rule-classes nil))
(local
 (defthm lw-mp-add-difference
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d))
            (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
                   (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d))))
   :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub)))
   :rule-classes nil))
(local
 (defthm lw-mp-scale-join
   (implies (and (lw-complexp point) (rationalp a) (rationalp b))
            (equal (lw-complex-add (lw-complex-scale a point) (lw-complex-scale b point))
                   (lw-complex-scale (+ a b) point)))
   :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-scale)))
   :rule-classes nil))
(local
 (defthm lw-mp-add-difference-bound
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp c) (lw-complexp d)
                 (lw-complex-diskp (lw-complex-sub a c) radius)
                 (lw-complex-diskp (lw-complex-sub b d) other-radius))
            (lw-complex-diskp (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d)) (+ radius other-radius)))
   :hints (("Goal" :use (lw-mp-add-difference
                         (:instance lw-complex-add-disk (left (lw-complex-sub a c)) (right (lw-complex-sub b d))))
                   :in-theory (disable lw-complex-add-disk)))
   :rule-classes nil))
(local
 (defthm lw-mp-join-anchor-bound
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp point)
                 (rationalp wa) (rationalp wb) (rationalp radius)
                 (lw-complex-diskp (lw-complex-sub a (lw-complex-scale wa point)) (* wa radius))
                 (lw-complex-diskp (lw-complex-sub b (lw-complex-scale wb point)) (* wb radius)))
            (lw-complex-diskp (lw-complex-sub (lw-complex-add a b) (lw-complex-scale (+ wa wb) point))
                              (* (+ wa wb) radius)))
   :hints (("Goal" :use ((:instance lw-mp-scale-join (a wa) (b wb))
                         (:instance lw-mp-add-difference-bound
                           (c (lw-complex-scale wa point)) (d (lw-complex-scale wb point))
                           (radius (* wa radius)) (other-radius (* wb radius))))))
   :rule-classes nil))

(defthm lw-mellin-dyadic-rational
  (implies (and (rationalp start) (rationalp end) (<= 0 start) (<= start end)
                (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp point-error) (< 0 point-error))
           (lw-complexp (lw-mellin-dyadic-sum start end depth sigma height index point-error)))
  :hints (("Goal" :induct (lw-mellin-dyadic-sum start end depth sigma height index point-error)
                  :in-theory (enable lw-complexp lw-complex-add lw-complex-scale))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-sample-rational (value start) (step 1) (error point-error)))
                 :in-theory (e/d (lw-complexp lw-complex-add lw-complex-scale) (lw-mellin-sample-rational))))))

(local
 (defthm lw-mp-weighted-anchor-bound
   (implies (and (rationalp anchor) (rationalp start) (rationalp end) (rationalp range-end) (rationalp cap)
                 (<= 0 anchor) (<= anchor start) (<= start end) (<= end range-end) (<= range-end cap)
                 (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                 (rationalp coarse-error) (< 0 coarse-error) (rationalp fine-error) (< 0 fine-error))
            (lw-complex-diskp
             (lw-complex-sub (lw-complex-scale (- end start) (lw-mellin-sample start sigma height index 1 fine-error))
                             (lw-complex-scale (- end start) (lw-mellin-sample anchor sigma height index 1 coarse-error)))
             (* (- end start)
                (+ (* (lw-mellin-spatial-slope cap sigma height 1) (- range-end anchor))
                   (* (lw-mellin-spatial-error-factor cap 1) (+ coarse-error fine-error))))))
   :hints (("Goal"
            :use ((:instance lw-mellin-spatial-parameters (step 1))
                  (:instance lw-mellin-sample-rational (value start) (step 1) (error fine-error))
                  (:instance lw-mellin-sample-rational (value anchor) (step 1) (error coarse-error))
                  (:instance lw-mellin-sample-spatial-transport
                    (left start) (right anchor) (step 1) (left-error fine-error) (right-error coarse-error))
                  (:instance lw-mp-multiply-order
                    (a (- start anchor)) (b (- range-end anchor))
                    (c (* (- end start) (lw-mellin-spatial-slope cap sigma height 1))))
                  (:instance lw-mp-scale-difference
                    (a (lw-mellin-sample start sigma height index 1 fine-error))
                    (b (lw-mellin-sample anchor sigma height index 1 coarse-error)) (weight (- end start)))
                  (:instance lw-complex-scale-disk (factor (- end start))
                    (point (lw-complex-sub (lw-mellin-sample start sigma height index 1 fine-error)
                                           (lw-mellin-sample anchor sigma height index 1 coarse-error)))
                    (radius (+ (* (lw-mellin-spatial-slope cap sigma height 1) (abs (- start anchor)))
                               (* (lw-mellin-spatial-error-factor cap 1) (+ fine-error coarse-error)))))
                  (:instance lw-complex-disk-enlarge
                    (point (lw-complex-sub
                            (lw-complex-scale (- end start) (lw-mellin-sample start sigma height index 1 fine-error))
                            (lw-complex-scale (- end start) (lw-mellin-sample anchor sigma height index 1 coarse-error))))
                    (radius (* (- end start)
                               (+ (* (lw-mellin-spatial-slope cap sigma height 1) (abs (- start anchor)))
                                  (* (lw-mellin-spatial-error-factor cap 1) (+ fine-error coarse-error)))))
                    (cap (* (- end start)
                            (+ (* (lw-mellin-spatial-slope cap sigma height 1) (- range-end anchor))
                               (* (lw-mellin-spatial-error-factor cap 1) (+ coarse-error fine-error)))))))
            :in-theory (disable lw-mellin-sample-rational lw-complex-scale-disk)
            :nonlinearp t))
   :rule-classes nil))

(defthm lw-mellin-dyadic-anchor-bound
  (implies (and (rationalp anchor) (rationalp start) (rationalp end) (rationalp range-end) (rationalp cap)
                (<= 0 anchor) (<= anchor start) (<= start end) (<= end range-end) (<= range-end cap)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                (rationalp coarse-error) (< 0 coarse-error) (rationalp fine-error) (< 0 fine-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-dyadic-sum start end depth sigma height index fine-error)
                            (lw-complex-scale (- end start) (lw-mellin-sample anchor sigma height index 1 coarse-error)))
            (* (- end start)
               (+ (* (lw-mellin-spatial-slope cap sigma height 1) (- range-end anchor))
                  (* (lw-mellin-spatial-error-factor cap 1) (+ coarse-error fine-error))))))
  :hints (("Goal" :induct (lw-mellin-dyadic-sum start end depth sigma height index fine-error))
          (and stable-under-simplificationp
               '(:use (lw-mp-weighted-anchor-bound
                       (:instance lw-mellin-spatial-parameters (step 1))
                       (:instance lw-mellin-sample-rational (value anchor) (step 1) (error coarse-error))
                       (:instance lw-mellin-dyadic-rational (end (/ (+ start end) 2)) (depth (- depth 1)) (point-error fine-error))
                       (:instance lw-mellin-dyadic-rational (start (/ (+ start end) 2)) (depth (- depth 1)) (point-error fine-error))
                       (:instance lw-mp-join-anchor-bound
                         (a (lw-mellin-dyadic-sum start (/ (+ start end) 2) (- depth 1) sigma height index fine-error))
                         (b (lw-mellin-dyadic-sum (/ (+ start end) 2) end (- depth 1) sigma height index fine-error))
                         (point (lw-mellin-sample anchor sigma height index 1 coarse-error))
                         (wa (- (/ (+ start end) 2) start)) (wb (- end (/ (+ start end) 2)))
                         (radius (+ (* (lw-mellin-spatial-slope cap sigma height 1) (- range-end anchor))
                                    (* (lw-mellin-spatial-error-factor cap 1) (+ coarse-error fine-error))))))
                 :in-theory (disable lw-mellin-dyadic-sum lw-mellin-dyadic-rational lw-mellin-sample-rational)
                 :nonlinearp t))))

(local (in-theory (disable lw-halved-width)))
(local (defthm lw-mp-mesh-rational
         (implies (rationalp width) (rationalp (lw-halved-width width depth)))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))
         :rule-classes (:rewrite :type-prescription)))
(local
 (defthm lw-mp-zero-depth
   (implies (zp depth)
            (equal (lw-mellin-dyadic-sum start end depth sigma height index point-error)
                   (lw-complex-scale (- end start) (lw-mellin-sample start sigma height index 1 point-error))))))
(local
 (defthm lw-mp-zero-mesh
   (implies (zp depth) (equal (lw-halved-width width depth) width))
   :hints (("Goal" :in-theory (enable lw-halved-width)))))

(local (defthm lw-mp-left-span
         (implies (and (rationalp start) (rationalp end))
                  (equal (- (/ (+ start end) 2) start) (* 1/2 (- end start))))
         :hints (("Goal" :nonlinearp t))))
(local (defthm lw-mp-right-span
         (implies (and (rationalp start) (rationalp end))
                  (equal (- end (/ (+ start end) 2)) (* 1/2 (- end start))))
         :hints (("Goal" :nonlinearp t))))
(local (defthm lw-mp-two-half-radius
         (implies (and (rationalp width) (rationalp radius))
                  (equal (+ (* 1/2 width radius) (* 1/2 width radius)) (* width radius)))
         :hints (("Goal" :nonlinearp t))))

(defthm lw-mellin-dyadic-refinement
  (implies (and (rationalp start) (rationalp end) (rationalp cap)
                (<= 0 start) (<= start end) (<= end cap) (natp depth) (natp refinements)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                (rationalp coarse-error) (< 0 coarse-error) (rationalp fine-error) (< 0 fine-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-dyadic-sum start end (+ depth refinements) sigma height index fine-error)
                            (lw-mellin-dyadic-sum start end depth sigma height index coarse-error))
            (* (- end start)
               (+ (* (lw-mellin-spatial-slope cap sigma height 1) (lw-halved-width (- end start) depth))
                  (* (lw-mellin-spatial-error-factor cap 1) (+ coarse-error fine-error))))))
  :hints (("Goal" :induct (lw-mellin-dyadic-sum start end depth sigma height index coarse-error)
                  :do-not '(generalize eliminate-destructors)
                  :in-theory (disable (:definition lw-mellin-dyadic-sum) distributivity lw-mp-left-distribute))
          (and stable-under-simplificationp
               '(:use ((:instance lw-mellin-dyadic-anchor-bound (anchor start) (range-end end) (depth refinements))
                       lw-mp-left-span lw-mp-right-span
                       (:instance lw-halved-width-half (width (- end start)) (steps (- depth 1)))
                       (:instance lw-mp-two-half-radius
                         (width (- end start))
                         (radius (+ (* (lw-mellin-spatial-slope cap sigma height 1)
                                       (* 1/2 (lw-halved-width (- end start) (- depth 1))))
                                    (* (lw-mellin-spatial-error-factor cap 1) (+ coarse-error fine-error)))))
                       (:instance lw-mellin-spatial-parameters (step 1))
                       (:instance lw-mellin-dyadic-rational (end (/ (+ start end) 2))
                         (depth (+ -1 depth refinements)) (point-error fine-error))
                       (:instance lw-mellin-dyadic-rational (start (/ (+ start end) 2))
                         (depth (+ -1 depth refinements)) (point-error fine-error))
                       (:instance lw-mellin-dyadic-rational (end (/ (+ start end) 2))
                         (depth (- depth 1)) (point-error coarse-error))
                       (:instance lw-mellin-dyadic-rational (start (/ (+ start end) 2))
                         (depth (- depth 1)) (point-error coarse-error))
                       (:instance lw-mp-add-difference-bound
                         (a (lw-mellin-dyadic-sum start (/ (+ start end) 2) (+ -1 depth refinements) sigma height index fine-error))
                         (b (lw-mellin-dyadic-sum (/ (+ start end) 2) end (+ -1 depth refinements) sigma height index fine-error))
                         (c (lw-mellin-dyadic-sum start (/ (+ start end) 2) (- depth 1) sigma height index coarse-error))
                         (d (lw-mellin-dyadic-sum (/ (+ start end) 2) end (- depth 1) sigma height index coarse-error))
                         (radius (* (- (/ (+ start end) 2) start)
                                    (+ (* (lw-mellin-spatial-slope cap sigma height 1)
                                          (lw-halved-width (- (/ (+ start end) 2) start) (- depth 1)))
                                       (* (lw-mellin-spatial-error-factor cap 1) (+ coarse-error fine-error)))))
                         (other-radius (* (- end (/ (+ start end) 2))
                                          (+ (* (lw-mellin-spatial-slope cap sigma height 1)
                                                (lw-halved-width (- end (/ (+ start end) 2)) (- depth 1)))
                                             (* (lw-mellin-spatial-error-factor cap 1) (+ coarse-error fine-error)))))))
                 :expand ((lw-mellin-dyadic-sum start end depth sigma height index coarse-error)
                          (lw-mellin-dyadic-sum start end (+ depth refinements) sigma height index fine-error)
                          (lw-halved-width (- end start) depth))
                 :in-theory (disable lw-mellin-dyadic-sum lw-mellin-dyadic-rational lw-mellin-dyadic-anchor-bound
                                     distributivity lw-mp-left-distribute lw-mp-left-span lw-mp-right-span
                                     lw-halved-width-half lw-mp-two-half-radius)
                 :do-not-induct t
                 :nonlinearp t))))

(local (defthm lw-mp-mesh-nonnegative
         (implies (and (rationalp width) (<= 0 width)) (<= 0 (lw-halved-width width depth)))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))
         :rule-classes (:rewrite :linear)))
(local (defthm lw-mp-mesh-scale
         (implies (and (rationalp width) (rationalp factor))
                  (equal (lw-halved-width (* factor width) depth) (* factor (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth) :in-theory (enable lw-halved-width)))))

(defthm lw-mellin-dyadic-cross-depth
  (implies (and (rationalp cap) (<= 0 cap) (natp left-depth) (natp right-depth)
                (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-dyadic-sum 0 cap left-depth sigma height index left-error)
                            (lw-mellin-dyadic-sum 0 cap right-depth sigma height index right-error))
            (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1)
                         (+ (lw-halved-width cap left-depth) (lw-halved-width cap right-depth)))
                      (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error))))))
  :hints (("Goal" :cases ((<= left-depth right-depth))
                  :use ((:instance lw-mellin-spatial-parameters (step 1))
                        (:instance lw-mp-mesh-nonnegative (width cap) (depth left-depth))
                        (:instance lw-mp-mesh-nonnegative (width cap) (depth right-depth))
                        (:instance lw-mellin-dyadic-rational (start 0) (end cap) (depth left-depth) (point-error left-error))
                        (:instance lw-mellin-dyadic-rational (start 0) (end cap) (depth right-depth) (point-error right-error))
                        (:instance lw-mellin-dyadic-refinement (start 0) (end cap) (depth left-depth)
                          (refinements (- right-depth left-depth)) (coarse-error left-error) (fine-error right-error))
                        (:instance lw-mellin-dyadic-refinement (start 0) (end cap) (depth right-depth)
                          (refinements (- left-depth right-depth)) (coarse-error right-error) (fine-error left-error))
                        (:instance lw-complex-difference-symmetric
                          (left (lw-mellin-dyadic-sum 0 cap right-depth sigma height index right-error))
                          (right (lw-mellin-dyadic-sum 0 cap left-depth sigma height index left-error))
                          (radius (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1) (lw-halved-width cap left-depth))
                                            (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error))))))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-mellin-dyadic-sum 0 cap left-depth sigma height index left-error)
                                                (lw-mellin-dyadic-sum 0 cap right-depth sigma height index right-error)))
                          (radius (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1) (lw-halved-width cap left-depth))
                                            (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error)))))
                          (cap (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1)
                                            (+ (lw-halved-width cap left-depth) (lw-halved-width cap right-depth)))
                                         (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error))))))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub (lw-mellin-dyadic-sum 0 cap left-depth sigma height index left-error)
                                                (lw-mellin-dyadic-sum 0 cap right-depth sigma height index right-error)))
                          (radius (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1) (lw-halved-width cap right-depth))
                                            (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error)))))
                          (cap (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1)
                                            (+ (lw-halved-width cap left-depth) (lw-halved-width cap right-depth)))
                                         (* (lw-mellin-spatial-error-factor cap 1) (+ left-error right-error)))))))
                  :in-theory (disable lw-mellin-dyadic-sum lw-mellin-dyadic-rational lw-mellin-dyadic-refinement
                                      lw-mp-mesh-nonnegative)
                  :nonlinearp t)))

(defun lw-mellin-integral-width (cap sigma height)
  (* cap (lw-mellin-spatial-slope cap sigma height 1) cap))
(defun lw-mellin-integral-depth (cap sigma height error)
  (lw-halving-depth (lw-mellin-integral-width cap sigma height) (/ error 4)
                    (lw-precision-fuel (lw-mellin-integral-width cap sigma height) (/ error 4))))
(defun lw-mellin-integral-precision (cap error)
  (/ error (* 4 (+ 1 (* cap (lw-mellin-spatial-error-factor cap 1))))))
(defun lw-mellin-bounded-integral (cap sigma height index error)
  (lw-mellin-dyadic-sum 0 cap (lw-mellin-integral-depth cap sigma height error)
                        sigma height index (lw-mellin-integral-precision cap error)))

(defthm lw-mellin-integral-depth-adequate
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp error) (< 0 error))
           (and (natp (lw-mellin-integral-depth cap sigma height error))
                (<= (* cap (lw-mellin-spatial-slope cap sigma height 1)
                       (lw-halved-width cap (lw-mellin-integral-depth cap sigma height error))) (/ error 4))))
  :hints (("Goal"
           :use ((:instance lw-mellin-spatial-parameters (step 1))
                 (:instance lw-precision-fuel-adequate (width (lw-mellin-integral-width cap sigma height)) (epsilon (/ error 4)))
                 (:instance lw-halving-depth-adequate (width (lw-mellin-integral-width cap sigma height)) (epsilon (/ error 4))
                   (fuel (lw-precision-fuel (lw-mellin-integral-width cap sigma height) (/ error 4))))
                 (:instance lw-mp-mesh-scale (width cap) (factor (* cap (lw-mellin-spatial-slope cap sigma height 1)))
                   (depth (lw-mellin-integral-depth cap sigma height error))))
           :in-theory (disable lw-halving-depth lw-precision-fuel lw-precision-fuel-adequate lw-halving-depth-adequate lw-mp-mesh-scale)
           :nonlinearp t)))

(defthm lw-mellin-integral-precision-valid
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-integral-precision cap error))
                (< 0 (lw-mellin-integral-precision cap error))
                (<= (* cap (lw-mellin-spatial-error-factor cap 1) (lw-mellin-integral-precision cap error)) (/ error 4))))
  :hints (("Goal" :use ((:instance lw-mellin-spatial-parameters (step 1))
                        (:instance lw-positive-division-bound
                          (numerator (* cap (lw-mellin-spatial-error-factor cap 1) error))
                          (divisor (* 4 (+ 1 (* cap (lw-mellin-spatial-error-factor cap 1))))) (bound (/ error 4))))
                  :nonlinearp t)))

(defthm lw-mellin-bounded-integral-rational
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-mellin-bounded-integral cap sigma height index error)))
  :hints (("Goal" :use (lw-mellin-integral-precision-valid
                        (:instance lw-mellin-dyadic-rational (start 0) (end cap)
                          (depth (lw-mellin-integral-depth cap sigma height error))
                          (point-error (lw-mellin-integral-precision cap error))))
                  :in-theory (disable lw-mellin-dyadic-sum lw-mellin-integral-depth lw-mellin-integral-precision
                                      lw-mellin-integral-precision-valid lw-mellin-dyadic-rational))))

(defthm lw-mellin-bounded-integral-constructor-check
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height)
                (rationalp error) (< 0 error))
           (lw-mellin-dyadic-check 0 cap (lw-mellin-integral-depth cap sigma height error)
                                   sigma index (lw-mellin-integral-precision cap error)))
  :hints (("Goal" :use (lw-mellin-integral-precision-valid
                        (:instance lw-mellin-dyadic-check-valid (start 0) (end cap)
                          (depth (lw-mellin-integral-depth cap sigma height error))
                          (point-error (lw-mellin-integral-precision cap error))))
                  :in-theory (disable lw-mellin-dyadic-check lw-mellin-integral-depth lw-mellin-integral-precision
                                      lw-mellin-integral-precision-valid lw-mellin-dyadic-check-valid))))

; Both the mesh depth and point precision are computed from the requested
; error. This is Cauchy convergence under actual grid refinement, not just
; precision refinement on a fixed grid. The improper tail is still separate.
(defthm lw-mellin-bounded-integral-cauchy
  (implies (and (rationalp cap) (<= 0 cap) (rationalp sigma) (<= 0 sigma) (rationalp height) (natp index)
                (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
           (lw-complex-diskp
            (lw-complex-sub (lw-mellin-bounded-integral cap sigma height index left-error)
                            (lw-mellin-bounded-integral cap sigma height index right-error)) (+ left-error right-error)))
  :hints (("Goal"
           :use ((:instance lw-mellin-spatial-parameters (step 1))
                 (:instance lw-mellin-integral-depth-adequate (error left-error))
                 (:instance lw-mellin-integral-depth-adequate (error right-error))
                 (:instance lw-mellin-integral-precision-valid (error left-error))
                 (:instance lw-mellin-integral-precision-valid (error right-error))
                 (:instance lw-mellin-dyadic-cross-depth
                   (left-depth (lw-mellin-integral-depth cap sigma height left-error))
                   (right-depth (lw-mellin-integral-depth cap sigma height right-error))
                   (left-error (lw-mellin-integral-precision cap left-error))
                   (right-error (lw-mellin-integral-precision cap right-error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub (lw-mellin-bounded-integral cap sigma height index left-error)
                                          (lw-mellin-bounded-integral cap sigma height index right-error)))
                   (radius (* cap (+ (* (lw-mellin-spatial-slope cap sigma height 1)
                                        (+ (lw-halved-width cap (lw-mellin-integral-depth cap sigma height left-error))
                                           (lw-halved-width cap (lw-mellin-integral-depth cap sigma height right-error))))
                                     (* (lw-mellin-spatial-error-factor cap 1)
                                        (+ (lw-mellin-integral-precision cap left-error) (lw-mellin-integral-precision cap right-error))))))
                   (cap (+ left-error right-error))))
           :in-theory (disable lw-mellin-dyadic-sum lw-mellin-integral-depth lw-mellin-integral-precision
                               lw-mellin-integral-depth-adequate lw-mellin-integral-precision-valid lw-mellin-dyadic-cross-depth))))
