(in-package "ACL2")

(include-book "complex-exp-grid")
(include-book "rational-window")

; Exponential quadrature on the actual dyadic leaves, with a rational
; cutpoint inserted in each leaf. Endpoint increments telescope exactly.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-norm-square
                 lw-complex-reciprocal lw-complex-quotient
                 lw-complex-exp-value lw-complex-exp-primitive-value
                 lw-complex-exp-grid lw-complex-exp-grid-step-budget
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-exp-bounds
                 lw-complex-mul-commutative lw-complex-mul-left-commutes lw-complex-mul-subtract
                 lw-complex-disk-enlarge lw-disk-enlarge lw-halved-width)))

(local (defthm lw-ced-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-ced-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ced-zero-times (equal (* 0 a) 0)))
(local (defthm lw-ced-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-ced-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-ced-times-negative (a b) (b a)))
                         :in-theory (disable lw-ced-times-negative)))))
(local (defthm lw-ced-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-ced-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-dyadic-leaf-count (depth)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth) 1 (* 2 (lw-dyadic-leaf-count (- depth 1)))))

(defthm lw-dyadic-leaf-count-natural
  (posp (lw-dyadic-leaf-count depth))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-dyadic-leaf-count-mesh
  (implies (rationalp width)
           (equal (* (lw-dyadic-leaf-count depth) (lw-halved-width width depth)) width))
  :hints (("Goal" :induct (lw-dyadic-leaf-count depth)
                  :in-theory (enable lw-halved-width))))

(local (in-theory (disable lw-dyadic-leaf-count)))

(defun lw-complex-exp-clipped-dyadic (point start end depth cutpoint error)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (if (<= end cutpoint) (cons 0 0)
        (let ((node (max start cutpoint)))
          (lw-complex-scale (- end node)
                            (lw-complex-exp-value (lw-complex-scale node point) error))))
    (let ((middle (/ (+ start end) 2)))
      (lw-complex-add
       (lw-complex-exp-clipped-dyadic point start middle (- depth 1) cutpoint error)
       (lw-complex-exp-clipped-dyadic point middle end (- depth 1) cutpoint error)))))

(defun lw-complex-exp-clipped-increment (point start end cutpoint error)
  (lw-complex-sub
   (lw-complex-exp-value (lw-complex-scale (max end cutpoint) point) error)
   (lw-complex-exp-value (lw-complex-scale (max start cutpoint) point) error)))

(defthm lw-complex-exp-clipped-dyadic-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp end) (rationalp cutpoint)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)))
  :hints (("Goal" :induct (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)
                  :in-theory (enable lw-complexp lw-complex-add lw-complex-scale))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-exp-value-rational
                         (point (lw-complex-scale (max start cutpoint) point))))
                 :in-theory (e/d (lw-complexp lw-complex-add lw-complex-scale)
                                 (lw-complex-exp-value-rational)) :do-not-induct t))))

(defthm lw-complex-exp-clipped-increment-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp end) (rationalp cutpoint)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-clipped-increment point start end cutpoint error)))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-value-rational
                   (point (lw-complex-scale (max start cutpoint) point)))
                 (:instance lw-complex-exp-value-rational
                   (point (lw-complex-scale (max end cutpoint) point))))
           :in-theory (e/d (lw-complexp lw-complex-sub lw-complex-scale)
                           (lw-complex-exp-value-rational)) :do-not-induct t)))

(local (defthm lw-ced-sub-self
         (equal (lw-complex-sub a a) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-sub)))))
(local (defthm lw-ced-add-zero
         (implies (lw-complexp point) (equal (lw-complex-add (cons 0 0) point) point))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add)))))

(defthm lw-complex-exp-clipped-increment-add
  (equal (lw-complex-exp-clipped-increment point start end cutpoint error)
         (lw-complex-add
          (lw-complex-exp-clipped-increment point start middle cutpoint error)
          (lw-complex-exp-clipped-increment point middle end cutpoint error)))
  :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))
  :rule-classes nil)

(defthm lw-complex-exp-clipped-dyadic-before-cutpoint
  (implies (and (rationalp start) (rationalp end) (rationalp cutpoint)
                (<= start end) (<= end cutpoint))
           (equal (lw-complex-exp-clipped-dyadic point start end depth cutpoint error) (cons 0 0)))
  :hints (("Goal" :induct (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)
                  :in-theory (enable lw-complex-add))))

(local (in-theory (disable lw-complex-exp-clipped-dyadic lw-complex-exp-clipped-increment)))

(local (defthm lw-ced-midpoint-widths
         (implies (and (rationalp start) (rationalp end))
                  (and (equal (- (/ (+ start end) 2) start) (* 1/2 (- end start)))
                       (equal (- end (/ (+ start end) 2)) (* 1/2 (- end start)))))
         :rule-classes nil))

(local (defthm lw-ced-half-mesh
         (implies (and (rationalp start) (rationalp end) (not (zp depth)))
                  (and
                   (equal (lw-halved-width (- (/ (+ start end) 2) start) (- depth 1))
                          (lw-halved-width (- end start) depth))
                   (equal (lw-halved-width (- end (/ (+ start end) 2)) (- depth 1))
                          (lw-halved-width (- end start) depth))))
         :hints (("Goal"
                  :use (lw-ced-midpoint-widths
                        (:instance lw-halved-width-half (width (- end start)) (steps (- depth 1))))
                  :expand ((lw-halved-width (- end start) depth))
                  :in-theory (disable lw-halved-width-half)))
         :rule-classes nil))

(local (defthm lw-ced-mesh-data
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth))
                       (<= 0 (lw-halved-width width depth))
                       (<= (lw-halved-width width depth) width)))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))

(local (defthm lw-ced-budget-scalar
         (implies (and (rationalp cap) (<= 0 cap) (rationalp slope) (<= 0 slope)
                       (rationalp weight) (<= 0 weight) (rationalp error) (<= 0 error)
                       (rationalp small) (<= 0 small) (rationalp large) (<= small large))
                  (and (<= 0 (+ (* cap slope slope small small) (* weight error)))
                       (<= (+ (* cap slope slope small small) (* weight error))
                           (+ (* cap slope slope large large) (* weight error)))))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ced-step-budget-data
         (implies (and (lw-complexp point) (rationalp small) (<= 0 small)
                       (rationalp large) (<= small large)
                       (rationalp argument-cap) (<= 0 argument-cap) (rationalp error) (< 0 error))
                  (and (rationalp (lw-complex-exp-grid-step-budget point small argument-cap error))
                       (<= 0 (lw-complex-exp-grid-step-budget point small argument-cap error))
                       (<= (lw-complex-exp-grid-step-budget point small argument-cap error)
                           (lw-complex-exp-grid-step-budget point large argument-cap error))))
         :hints (("Goal"
                  :use (lw-complex-l1-bound lw-complex-exp-uniform-cap-data
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap 1))
                        (:instance lw-ced-budget-scalar
                          (cap (lw-complex-exp-uniform-cap argument-cap)) (slope (lw-complex-l1 point))
                          (weight (+ (lw-complex-exp-uniform-cap 1)
                                     (* 2 (lw-complex-exp-uniform-cap argument-cap)) 2))))
                  :in-theory (e/d (lw-complex-exp-grid-step-budget)
                                  (lw-complex-l1-bound lw-complex-exp-uniform-cap-data))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-ced-zero-disk
         (implies (and (rationalp radius) (<= 0 radius)) (lw-complex-diskp (cons 0 0) radius))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-diskp lw-diskp) :nonlinearp t))))
(local (defthm lw-ced-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-ced-mul-zero
         (equal (lw-complex-mul point (cons 0 0)) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-mul)))))
(local (defthm lw-ced-rectangle-shape
         (equal (lw-complex-sub (lw-complex-sub a b) (lw-complex-mul point cell))
                (lw-complex-sub a (lw-complex-add b (lw-complex-mul point cell))))
         :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))
(local (defthm lw-ced-endpoint-split
         (implies (and (rationalp node) (rationalp end)) (equal (+ node (- end node)) end))
         :rule-classes nil))

(local (defthm lw-ced-clipped-rectangle
         (implies
          (and (lw-complexp point) (rationalp start) (<= 0 start)
               (rationalp end) (<= start end) (rationalp bound) (<= end bound)
               (rationalp cutpoint) (<= 0 cutpoint)
               (rationalp mesh) (<= (- end start) mesh)
               (rationalp argument-cap) (<= 0 argument-cap)
               (<= (* (lw-complex-l1 point) bound) argument-cap)
               (<= (* (lw-complex-l1 point) mesh) 1) (rationalp error) (< 0 error))
          (lw-complex-diskp
           (lw-complex-sub
            (lw-complex-exp-clipped-increment point start end cutpoint error)
            (lw-complex-mul point (lw-complex-exp-clipped-dyadic point start end 0 cutpoint error)))
           (lw-complex-exp-grid-step-budget point mesh argument-cap error)))
         :hints
         (("Goal"
           :use (lw-complex-l1-bound
                 (:instance lw-ced-step-budget-data (small mesh) (large mesh))
                 (:instance lw-ced-step-budget-data (small (- end (max start cutpoint))) (large mesh))
                 (:instance lw-ced-multiply-order
                   (a (- end (max start cutpoint))) (b mesh) (factor (lw-complex-l1 point)))
                 (:instance lw-ced-endpoint-split (node (max start cutpoint)))
                 (:instance lw-complex-exp-rectangle-defect
                   (start (max start cutpoint)) (step (- end (max start cutpoint))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-clipped-increment point start end cutpoint error)
                     (lw-complex-mul point (lw-complex-exp-clipped-dyadic point start end 0 cutpoint error))))
                   (radius (lw-complex-exp-grid-step-budget point (- end (max start cutpoint)) argument-cap error))
                   (cap (lw-complex-exp-grid-step-budget point mesh argument-cap error))))
           :cases ((<= end cutpoint) (equal start end))
           :in-theory
           (e/d (lw-complex-exp-clipped-increment lw-complex-exp-clipped-dyadic)
                (lw-complex-l1-bound lw-complex-exp-rectangle-defect))
           :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-ced-residual-add
         (equal
          (lw-complex-sub (lw-complex-add a b) (lw-complex-mul point (lw-complex-add left right)))
          (lw-complex-add (lw-complex-sub a (lw-complex-mul point left))
                          (lw-complex-sub b (lw-complex-mul point right))))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub lw-complex-mul)))
         :rule-classes nil))

(local (defthm lw-ced-double
         (equal (+ a a) (* 2 a))
         :hints (("Goal" :cases ((acl2-numberp a))))))

(defthm lw-complex-exp-clipped-dyadic-telescope
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp end) (<= start end)
        (rationalp bound) (<= end bound) (natp depth) (rationalp cutpoint) (<= 0 cutpoint)
        (rationalp argument-cap) (<= 0 argument-cap)
        (<= (* (lw-complex-l1 point) bound) argument-cap)
        (<= (* (lw-complex-l1 point) (lw-halved-width (- end start) depth)) 1)
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-clipped-increment point start end cutpoint error)
     (lw-complex-mul point (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)))
    (* (lw-dyadic-leaf-count depth)
       (lw-complex-exp-grid-step-budget point (lw-halved-width (- end start) depth) argument-cap error))))
  :hints
  (("Goal"
    :induct (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)
    :in-theory (e/d ((:induction lw-complex-exp-clipped-dyadic)
                     (:definition lw-complex-exp-clipped-dyadic) lw-dyadic-leaf-count lw-halved-width)
                    (lw-complex-exp-clipped-dyadic-before-cutpoint)))
   (and stable-under-simplificationp
        '(:use
          (lw-ced-half-mesh
           (:instance lw-complex-exp-clipped-increment-add (middle (/ (+ start end) 2)))
           (:instance lw-ced-clipped-rectangle (mesh (- end start)))
           (:instance lw-ced-residual-add
             (a (lw-complex-exp-clipped-increment point start (/ (+ start end) 2) cutpoint error))
             (b (lw-complex-exp-clipped-increment point (/ (+ start end) 2) end cutpoint error))
             (left (lw-complex-exp-clipped-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint error))
             (right (lw-complex-exp-clipped-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint error)))
           (:instance lw-complex-add-disk
             (left (lw-complex-sub
               (lw-complex-exp-clipped-increment point start (/ (+ start end) 2) cutpoint error)
               (lw-complex-mul point
                 (lw-complex-exp-clipped-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint error))))
             (right (lw-complex-sub
               (lw-complex-exp-clipped-increment point (/ (+ start end) 2) end cutpoint error)
               (lw-complex-mul point
                 (lw-complex-exp-clipped-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint error))))
             (radius (* (lw-dyadic-leaf-count (- depth 1))
                        (lw-complex-exp-grid-step-budget
                         point (lw-halved-width (- (/ (+ start end) 2) start) (- depth 1)) argument-cap error)))
             (other-radius (* (lw-dyadic-leaf-count (- depth 1))
                              (lw-complex-exp-grid-step-budget
                               point (lw-halved-width (- end (/ (+ start end) 2)) (- depth 1)) argument-cap error)))))
          :expand
          ((lw-complex-exp-clipped-dyadic point start end 0 cutpoint error)
           (lw-halved-width (- end start) depth))
          :in-theory (disable lw-complex-exp-clipped-dyadic lw-dyadic-leaf-count lw-halved-width
                              lw-complex-exp-clipped-dyadic-before-cutpoint lw-complex-add-disk)
          :nonlinearp nil :do-not-induct t))))

(defun lw-complex-exp-clipped-primitive (point start end cutpoint error)
  (lw-complex-exp-primitive-value point (max start cutpoint) (max end cutpoint) error))

(defthm lw-complex-exp-clipped-primitive-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp end) (rationalp cutpoint)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-clipped-primitive point start end cutpoint error))))

(defthm lw-complex-exp-clipped-primitive-endpoint
  (implies (and (rationalp start) (rationalp end) (rationalp cutpoint) (<= start end))
           (equal (lw-complex-exp-clipped-primitive point start end cutpoint error)
                  (if (<= end cutpoint) (cons 0 0)
                    (lw-complex-exp-primitive-value point (max start cutpoint) end error))))
  :hints (("Goal" :in-theory (enable lw-complex-exp-primitive-value lw-complex-quotient lw-complex-mul))))

(local (in-theory (disable lw-complex-exp-clipped-primitive lw-complex-exp-clipped-primitive-endpoint)))

(local (defthm lw-ced-last-cancel
         (implies (and (lw-complexp a) (lw-complexp b) (not (equal a (cons 0 0))))
                  (equal (lw-complex-mul a
                           (lw-complex-mul b (lw-complex-reciprocal a))) b))
         :hints (("Goal" :use ((:instance lw-complex-mul-left-commutes
                                (c (lw-complex-reciprocal a))))
                         :in-theory (disable lw-complex-mul-commutative
                                             lw-complex-mul-left-commutes)))))

(local (defthm lw-ced-quotient-defect
         (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
                       (lw-complexp value) (lw-complexp total))
                  (equal
                   (lw-complex-quotient (lw-complex-sub value (lw-complex-mul point total)) point)
                   (lw-complex-sub (lw-complex-quotient value point) total)))
         :hints (("Goal" :in-theory (enable lw-complex-quotient lw-complex-mul-subtract
                                          lw-complex-mul-commutative lw-complex-mul-left-commutes)))))

(local (defthm lw-ced-quotient-disk
         (implies (and (lw-complex-diskp numerator radius) (lw-complexp denominator)
                       (rationalp clearance) (< 0 clearance)
                       (<= (* clearance clearance) (lw-complex-norm-square denominator)))
                  (lw-complex-diskp (lw-complex-quotient numerator denominator)
                                    (* radius (/ clearance))))
         :hints (("Goal"
                  :use ((:instance lw-complex-reciprocal-disk-bound
                          (point denominator) (lower clearance))
                        (:instance lw-complex-mul-disk
                          (left numerator) (right (lw-complex-reciprocal denominator))
                          (other-radius (/ clearance))))
                  :in-theory (e/d (lw-complex-quotient)
                                  (lw-complex-reciprocal-disk-bound lw-complex-mul-disk))))))


(local (defthm lw-ced-clipped-primitive-form
         (equal (lw-complex-exp-clipped-primitive point start end cutpoint error)
                (lw-complex-quotient (lw-complex-exp-clipped-increment point start end cutpoint error) point))
         :hints (("Goal" :in-theory (enable lw-complex-exp-clipped-primitive
                                            lw-complex-exp-primitive-value lw-complex-exp-clipped-increment)))
         :rule-classes nil))

(defthm lw-complex-exp-clipped-dyadic-primitive-error
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp end) (<= start end)
        (rationalp bound) (<= end bound) (natp depth) (rationalp cutpoint) (<= 0 cutpoint)
        (rationalp argument-cap) (<= 0 argument-cap)
        (<= (* (lw-complex-l1 point) bound) argument-cap)
        (<= (* (lw-complex-l1 point) (lw-halved-width (- end start) depth)) 1)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-clipped-primitive point start end cutpoint error)
     (lw-complex-exp-clipped-dyadic point start end depth cutpoint error))
    (* (lw-dyadic-leaf-count depth)
       (lw-complex-exp-grid-step-budget point (lw-halved-width (- end start) depth) argument-cap error)
       (/ clearance))))
  :hints (("Goal"
           :use (lw-complex-exp-clipped-dyadic-telescope
                 lw-ced-clipped-primitive-form
                 (:instance lw-complex-norm-lower-nonzero (lower clearance))
                 (:instance lw-ced-quotient-defect
                   (value (lw-complex-exp-clipped-increment point start end cutpoint error))
                   (total (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)))
                 (:instance lw-ced-quotient-disk
                   (denominator point)
                   (numerator (lw-complex-sub
                     (lw-complex-exp-clipped-increment point start end cutpoint error)
                     (lw-complex-mul point (lw-complex-exp-clipped-dyadic point start end depth cutpoint error))))
                   (radius (* (lw-dyadic-leaf-count depth)
                              (lw-complex-exp-grid-step-budget
                               point (lw-halved-width (- end start) depth) argument-cap error)))))
           :in-theory (disable lw-complex-exp-clipped-dyadic-telescope
                               lw-ced-quotient-defect lw-ced-quotient-disk
                               lw-complex-exp-clipped-dyadic-rational
                               lw-complex-exp-clipped-increment-rational)
           :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-clipped-primitive-cauchy
  (implies
   (and (lw-complexp point) (rationalp start) (rationalp end) (rationalp cutpoint)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-clipped-primitive point start end cutpoint left-error)
     (lw-complex-exp-clipped-primitive point start end cutpoint right-error))
    (* 2 (+ left-error right-error) (/ clearance))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-primitive-cauchy
                   (start (max start cutpoint)) (end (max end cutpoint))))
           :in-theory (e/d (lw-complex-exp-clipped-primitive) (lw-complex-exp-primitive-cauchy))
           :do-not-induct t)))

(local (defthm lw-ced-scale-rational
         (implies (and (lw-complexp point) (rationalp factor)) (lw-complexp (lw-complex-scale factor point)))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-scale)))))
(local (defthm lw-ced-scale-difference
         (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                (lw-complex-scale factor (lw-complex-sub a b)))
         :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))
(local (defthm lw-ced-add-differences
         (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
                (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d)))
         :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))
(local (defthm lw-ced-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ced-clipped-leaf-cauchy
         (implies
          (and (lw-complexp point) (rationalp start) (rationalp end) (<= start end) (rationalp cutpoint)
               (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
          (lw-complex-diskp
           (lw-complex-sub
            (lw-complex-exp-clipped-dyadic point start end 0 cutpoint left-error)
            (lw-complex-exp-clipped-dyadic point start end 0 cutpoint right-error))
           (* (- end start) (+ left-error right-error))))
         :hints (("Goal"
                  :use ((:instance lw-complex-exp-value-cauchy (point (lw-complex-scale (max start cutpoint) point)))
                        (:instance lw-ced-nonnegative-product (a (- end start)) (b (+ left-error right-error)))
                        (:instance lw-ced-multiply-order
                          (a (- end (max start cutpoint))) (b (- end start)) (factor (+ left-error right-error)))
                        (:instance lw-complex-scale-disk
                          (point (lw-complex-sub
                            (lw-complex-exp-value (lw-complex-scale (max start cutpoint) point) left-error)
                            (lw-complex-exp-value (lw-complex-scale (max start cutpoint) point) right-error)))
                          (factor (- end (max start cutpoint))) (radius (+ left-error right-error)))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                            (lw-complex-exp-clipped-dyadic point start end 0 cutpoint left-error)
                            (lw-complex-exp-clipped-dyadic point start end 0 cutpoint right-error)))
                          (radius (* (- end (max start cutpoint)) (+ left-error right-error)))
                          (cap (* (- end start) (+ left-error right-error)))))
                  :cases ((<= end cutpoint))
                  :in-theory (e/d (lw-complex-exp-clipped-dyadic)
                                  (lw-complex-exp-value-cauchy lw-complex-scale-disk))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-complex-exp-clipped-dyadic-cauchy
  (implies
   (and (lw-complexp point) (rationalp start) (rationalp end) (<= start end) (rationalp cutpoint)
        (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-clipped-dyadic point start end depth cutpoint left-error)
     (lw-complex-exp-clipped-dyadic point start end depth cutpoint right-error))
    (* (- end start) (+ left-error right-error))))
  :hints
  (("Goal"
    :induct (lw-complex-exp-clipped-dyadic point start end depth cutpoint left-error)
    :in-theory (e/d ((:induction lw-complex-exp-clipped-dyadic) (:definition lw-complex-exp-clipped-dyadic))
                    (lw-complex-exp-clipped-dyadic-before-cutpoint lw-complex-sub-add-first
                     lw-complex-add-commutative lw-complex-add-left-commutes)))
   (and stable-under-simplificationp
        '(:use
          (lw-ced-clipped-leaf-cauchy
           (:instance lw-complex-add-disk
             (left (lw-complex-sub
               (lw-complex-exp-clipped-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint left-error)
               (lw-complex-exp-clipped-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint right-error)))
             (right (lw-complex-sub
               (lw-complex-exp-clipped-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint left-error)
               (lw-complex-exp-clipped-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint right-error)))
             (radius (* (- (/ (+ start end) 2) start) (+ left-error right-error)))
             (other-radius (* (- end (/ (+ start end) 2)) (+ left-error right-error))))
           (:instance lw-complex-disk-enlarge
             (point (lw-complex-add
               (lw-complex-sub
                (lw-complex-exp-clipped-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint left-error)
                (lw-complex-exp-clipped-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint right-error))
               (lw-complex-sub
                (lw-complex-exp-clipped-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint left-error)
                (lw-complex-exp-clipped-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint right-error))))
             (radius (+ (* (- (/ (+ start end) 2) start) (+ left-error right-error))
                        (* (- end (/ (+ start end) 2)) (+ left-error right-error))))
             (cap (* (- end start) (+ left-error right-error)))))
          :expand
          ((lw-complex-exp-clipped-dyadic point start end 0 cutpoint left-error)
           (lw-complex-exp-clipped-dyadic point start end 0 cutpoint right-error))
          :in-theory (disable lw-complex-exp-clipped-dyadic lw-complex-add-disk
                              lw-complex-exp-clipped-dyadic-before-cutpoint lw-complex-sub-add-first
                              lw-complex-add-commutative lw-complex-add-left-commutes)
          :nonlinearp nil :do-not-induct t))))
