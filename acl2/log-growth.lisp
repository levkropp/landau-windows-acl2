(in-package "ACL2")

(include-book "window-index")

(local (defthm lw-growth-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-growth-zero-product (equal (* 0 value) 0)))

(local (defthm lw-growth-times-negation
         (implies (and (rationalp left) (rationalp right))
                  (equal (* left (- right)) (- (* left right))))
         :hints (("Goal" :use ((:instance distributivity
                                (x left) (y right) (z (- right))))
                         :in-theory (disable distributivity)))))

(local (defthm lw-growth-multiply-inequality
         (implies (and (rationalp left) (rationalp right) (<= left right)
                       (rationalp factor) (<= 0 factor))
                  (<= (* left factor) (* right factor)))
         :hints (("Goal" :nonlinearp t))
         :rule-classes nil))

; Concatenation and lower sums are exact rational identities. The proof of
; eventual log growth below groups uniform rectangles into doubling blocks;
; it never assumes a logarithm identity or a real analytic growth theorem.
(defthm lw-log-lower-concatenate
  (implies (and (rationalp start) (< 0 start)
                (rationalp step) (<= 0 step) (natp left) (natp right))
           (equal (car (lw-log-rectangles start step (+ left right)))
                  (+ (car (lw-log-rectangles start step left))
                     (car (lw-log-rectangles (+ start (* left step)) step right)))))
  :hints (("Goal" :induct (lw-log-rectangles start step left) :nonlinearp t)))

(defthm lw-log-lower-monotone-count
  (implies (and (rationalp start) (< 0 start)
                (rationalp step) (<= 0 step) (natp small) (natp large) (<= small large))
           (<= (car (lw-log-rectangles start step small))
               (car (lw-log-rectangles start step large))))
  :hints (("Goal" :use ((:instance lw-log-lower-concatenate (left small) (right (- large small)))
                        (:instance lw-log-rectangles-nonnegative
                          (start (+ start (* small step))) (count (- large small)))
                        (:instance lw-log-rectangles-interval (count small))
                        (:instance lw-log-rectangles-interval (count large)))
                  :in-theory (disable lw-log-rectangles lw-log-lower-concatenate
                                      lw-log-rectangles-nonnegative lw-log-rectangles-interval)
                  :nonlinearp t)))

(defthm lw-log-lower-constant-cap
  (implies (and (rationalp start) (< 0 start) (rationalp step) (<= 0 step)
                (natp count) (rationalp cap) (<= (+ start (* count step)) cap))
           (<= (/ (* count step) cap) (car (lw-log-rectangles start step count))))
  :hints (("Goal" :induct (lw-log-rectangles start step count) :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-reciprocal-antitone (left (+ start step)) (right cap))
                        (:instance lw-growth-multiply-inequality
                          (left (/ cap)) (right (/ (+ start step))) (factor step)))
                 :in-theory (disable lw-reciprocal-antitone lw-log-rectangles)
                 :nonlinearp t))))

(defthm lw-log-doubling-block-mass
  (implies (and (rationalp start) (< 0 start) (rationalp step) (< 0 step)
                (posp count) (<= start (* count step)))
           (<= 1/2 (car (lw-log-rectangles start step count))))
  :hints (("Goal" :use ((:instance lw-log-lower-constant-cap
                          (cap (+ start (* count step))))
                        (:instance lw-positive-division-lower-bound
                          (numerator (* count step)) (divisor (+ start (* count step))) (bound 1/2))
                        lw-log-rectangles-interval)
                  :in-theory (disable lw-log-rectangles lw-log-lower-constant-cap
                                      lw-log-rectangles-interval)
                  :nonlinearp t)))

(defun lw-dyadic-count (block steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps) 0
    (+ block (lw-dyadic-count (* 2 block) (- steps 1)))))

(defthm lw-dyadic-count-natural
  (implies (natp block) (natp (lw-dyadic-count block steps)))
  :rule-classes (:rewrite :type-prescription))

(local
 (defun lw-dyadic-mass-induction (start step block steps)
   (declare (xargs :measure (nfix steps)))
   (if (zp steps) (list start step block)
     (lw-dyadic-mass-induction (+ start (* block step)) step (* 2 block) (- steps 1)))))

(defthm lw-dyadic-count-mass
  (implies (and (rationalp start) (< 0 start) (rationalp step) (< 0 step)
                (posp block) (natp steps) (<= start (* block step)))
           (<= (/ steps 2)
               (car (lw-log-rectangles start step (lw-dyadic-count block steps)))))
  :hints (("Goal" :induct (lw-dyadic-mass-induction start step block steps)
                  :in-theory (disable lw-log-rectangles) :nonlinearp t)
          (and stable-under-simplificationp
               '(:use ((:instance lw-log-lower-concatenate
                          (left block) (right (lw-dyadic-count (* 2 block) (- steps 1))))
                        (:instance lw-log-doubling-block-mass (count block)))
                 :in-theory (disable lw-log-rectangles lw-log-lower-concatenate
                                     lw-log-doubling-block-mass lw-dyadic-count)
                 :nonlinearp t))))

(defthm lw-dyadic-count-closed
  (implies (and (rationalp block) (natp steps))
           (equal (lw-dyadic-count block steps)
                  (* block (- (lw-rational-power 2 steps) 1))))
  :hints (("Goal" :induct (lw-dyadic-count block steps))))

(defun lw-unit-block (step) (lw-ceiling-rational (/ step)))

(defthm lw-unit-block-natural
  (natp (lw-unit-block step))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-unit-block-width
  (implies (and (rationalp step) (< 0 step) (<= step 1))
           (and (posp (lw-unit-block step))
                (<= 1 (* (lw-unit-block step) step))
                (<= (* (lw-unit-block step) step) 2)))
  :hints (("Goal" :use ((:instance lw-ceiling-rational-bracket (value (/ step)))
                        (:instance inverse-of-* (x step))
                        (:instance lw-growth-multiply-inequality
                          (left (/ step)) (right (lw-unit-block step)) (factor step))
                        (:instance lw-growth-multiply-inequality
                          (left (lw-unit-block step)) (right (+ 1 (/ step))) (factor step)))
                  :in-theory (disable lw-ceiling-rational lw-ceiling-rational-bracket inverse-of-*)
                  :nonlinearp t)))

(defthm lw-dyadic-count-length-bound
  (implies (and (natp block) (natp steps) (rationalp step) (<= 0 step)
                (<= (* block step) 2))
           (<= (+ 1 (* (lw-dyadic-count block steps) step))
               (* 2 (lw-rational-power 2 steps))))
  :hints (("Goal" :use (lw-dyadic-count-closed
                        (:instance lw-rational-power-at-least-one (base 2) (exponent steps))
                        (:instance lw-growth-multiply-inequality
                          (left (* block step)) (right 2)
                          (factor (- (lw-rational-power 2 steps) 1))))
                  :in-theory (disable lw-dyadic-count lw-dyadic-count-closed lw-rational-power
                                      lw-rational-power-at-least-one)
                  :nonlinearp t)))

(defthm lw-log-lower-dyadic-growth
  (implies (and (rationalp step) (< 0 step) (<= step 1) (natp count) (natp steps)
                (<= (lw-rational-power 2 (+ steps 1)) (+ 1 (* count step))))
           (<= (/ steps 2) (car (lw-log-rectangles 1 step count))))
  :hints (("Goal" :use (lw-unit-block-width
                        (:instance lw-dyadic-count-length-bound (block (lw-unit-block step)))
                        (:instance lw-dyadic-count-mass (start 1) (block (lw-unit-block step)))
                        (:instance lw-log-lower-monotone-count
                          (start 1) (small (lw-dyadic-count (lw-unit-block step) steps)) (large count)))
                  :in-theory (disable lw-unit-block lw-unit-block-width lw-dyadic-count
                                      lw-dyadic-count-closed
                                      lw-dyadic-count-length-bound lw-dyadic-count-mass
                                      lw-log-rectangles lw-log-lower-monotone-count)
                  :nonlinearp t)))

(local
 (defthm lw-growth-positive-product
   (implies (and (rationalp left) (< 0 left) (rationalp right) (< 0 right))
            (< 0 (* left right)))
   :hints (("Goal" :nonlinearp t))
   :rule-classes nil))

(defthm lw-log-step-positive
  (implies (and (rationalp value) (< 1 value))
           (< 0 (/ (- value 1) (lw-log-count value epsilon))))
  :hints (("Goal" :use (lw-log-count-positive
                        (:instance lw-reciprocal-positive (value (lw-log-count value epsilon)))
                        (:instance lw-growth-positive-product
                          (left (- value 1)) (right (/ (lw-log-count value epsilon)))))
                  :in-theory (disable lw-log-count lw-log-count-positive lw-reciprocal-positive)
                  :nonlinearp t)))

(defthm lw-log-grid-endpoint
  (implies (rationalp value)
           (equal (+ 1 (* (lw-log-count value epsilon)
                           (/ (- value 1) (lw-log-count value epsilon)))) value))
  :hints (("Goal" :in-theory (disable lw-log-count))))

(defthm lw-log-bounds-dyadic-growth
  (implies (and (rationalp value) (rationalp epsilon) (< 0 epsilon) (<= epsilon 1)
                (natp steps) (<= (lw-rational-power 2 (+ steps 1)) value))
           (<= (/ steps 2) (car (lw-log-bounds value epsilon))))
  :hints (("Goal" :use ((:instance lw-log-lower-dyadic-growth
                          (step (/ (- value 1) (lw-log-count value epsilon)))
                          (count (lw-log-count value epsilon)))
                        (:instance lw-log-step-adequate)
                        (:instance lw-log-step-positive)
                        (:instance lw-log-grid-endpoint)
                        (:instance lw-rational-power-at-least-one (base 2) (exponent steps)))
                  :in-theory (disable lw-log-rectangles lw-log-count lw-log-lower-dyadic-growth
                                      lw-log-step-adequate lw-log-step-positive lw-log-grid-endpoint
                                      lw-rational-power-at-least-one)
                  :nonlinearp t)))

(defun lw-eventual-window-threshold (target)
  (lw-rational-power 2 (+ (* 2 (nfix target)) 9)))

(local (defthm lw-growth-power-two-natural
         (natp (lw-rational-power 2 exponent))
         :rule-classes (:rewrite :type-prescription)))

(defthm lw-eventual-window-threshold-natural
  (and (natp (lw-eventual-window-threshold target))
       (<= 1 (lw-eventual-window-threshold target)))
  :hints (("Goal" :use ((:instance lw-rational-power-at-least-one
                          (base 2) (exponent (+ (* 2 (nfix target)) 9))))
                  :in-theory (disable lw-rational-power lw-rational-power-at-least-one))))

(defthm lw-eventual-window-index
  (implies (and (natp target) (rationalp start)
                (<= (lw-eventual-window-threshold target) start))
           (and (lw-window-index-check start (lw-window-index start))
                (<= target (lw-window-index start))))
  :hints (("Goal" :use ((:instance lw-log-bounds-dyadic-growth
                          (value start) (epsilon 1/1000) (steps (+ (* 2 target) 8)))
                        (:instance lw-rational-power-at-least-one
                          (base 2) (exponent (+ (* 2 target) 9)))
                        (:instance lw-log-bounds-interval (value start) (epsilon 1/1000))
                        lw-window-index-check-computed
                        (:instance lw-window-index-threshold
                          (lower (car (lw-log-bounds start 1/1000))) (threshold target)))
                  :in-theory (disable lw-log-bounds lw-window-index-check lw-window-index-from-log
                                      lw-log-bounds-dyadic-growth lw-rational-power-at-least-one
                                      lw-log-bounds-interval lw-geometric-threshold
                                      lw-window-index-check-computed lw-window-index-threshold
                                      lw-rational-power)
                  :nonlinearp t)))

(defun lw-landau-window-threshold (growth pole-ratio tail-ratio
                                         pole-target tail-target ceiling-target)
  (lw-eventual-window-threshold
   (lw-landau-index growth pole-ratio tail-ratio pole-target tail-target ceiling-target)))

(defthm lw-eventual-window-geometric-bounds
  (implies (and (rationalp growth) (< 1 growth)
                (rationalp pole-ratio) (< 1 pole-ratio)
                (rationalp tail-ratio) (< 1 tail-ratio)
                (rationalp pole-target) (<= 0 pole-target)
                (rationalp tail-target) (<= 0 tail-target)
                (rationalp ceiling-target) (<= 0 ceiling-target)
                (rationalp start)
                (<= (lw-landau-window-threshold growth pole-ratio tail-ratio
                                                pole-target tail-target ceiling-target) start))
           (and (lw-window-index-check start (lw-window-index start))
                (<= ceiling-target (lw-rational-power growth (lw-window-index start)))
                (<= pole-target (lw-rational-power pole-ratio (lw-window-index start)))
                (<= tail-target (lw-rational-power tail-ratio (lw-window-index start)))))
  :hints (("Goal" :use ((:instance lw-eventual-window-index
                          (target (lw-landau-index growth pole-ratio tail-ratio
                                                   pole-target tail-target ceiling-target)))
                        (:instance lw-landau-index-sufficient (exponent (lw-window-index start))))
                  :in-theory (disable lw-eventual-window-threshold lw-eventual-window-index
                                      lw-landau-index lw-landau-index-sufficient lw-rational-power
                                      lw-window-index-from-log lw-log-bounds lw-window-index-check))))

(assert-event (let* ((steps 4) (step 1/10) (count (lw-dyadic-count (lw-unit-block step) steps)))
                (<= (/ steps 2) (car (lw-log-rectangles 1 step count)))))
