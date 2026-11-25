(in-package "ACL2")

(include-book "complex-exp-dyadic-grid")
(include-book "complex-exp-moment-grid")

; First-moment quadrature on clipped dyadic leaves. Finite integration
; by parts retains the zeroth exponential sum in the weighted residual.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-norm-square
                 lw-complex-reciprocal lw-complex-quotient
                 lw-complex-exp-value lw-complex-exp-primitive-value lw-complex-exp-moment-primitive
                 lw-complex-exp-grid lw-complex-exp-moment-grid
                 lw-complex-exp-grid-step-budget lw-complex-exp-moment-step-budget
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-exp-bounds
                 lw-complex-exp-clipped-dyadic lw-complex-exp-clipped-increment lw-complex-exp-clipped-primitive
                 lw-complex-exp-clipped-primitive-endpoint lw-dyadic-leaf-count lw-halved-width
                 lw-complex-exp-clipped-dyadic-before-cutpoint
                 lw-complex-mul-commutative lw-complex-mul-left-commutes lw-complex-mul-subtract
                 lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cmd-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cmd-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cmd-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cmd-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cmd-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-cmd-times-negative (a b) (b a)))
                         :in-theory (disable lw-cmd-times-negative)))))
(local (defthm lw-cmd-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-cmd-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-complex-exp-clipped-moment-dyadic (point start end depth cutpoint error)
  (declare (xargs :measure (nfix depth)))
  (if (zp depth)
      (if (<= end cutpoint) (cons 0 0)
        (let ((node (max start cutpoint)))
          (lw-complex-scale (* (- end node) node)
                            (lw-complex-exp-value (lw-complex-scale node point) error))))
    (let ((middle (/ (+ start end) 2)))
      (lw-complex-add
       (lw-complex-exp-clipped-moment-dyadic point start middle (- depth 1) cutpoint error)
       (lw-complex-exp-clipped-moment-dyadic point middle end (- depth 1) cutpoint error)))))

(defthm lw-complex-exp-clipped-moment-dyadic-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp end) (rationalp cutpoint)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint error)))
  :hints (("Goal" :induct (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint error)
                  :in-theory (enable lw-complexp lw-complex-add lw-complex-scale))
          (and stable-under-simplificationp
               '(:use ((:instance lw-complex-exp-value-rational
                         (point (lw-complex-scale (max start cutpoint) point))))
                 :in-theory (e/d (lw-complexp lw-complex-add lw-complex-scale)
                                 (lw-complex-exp-value-rational)) :do-not-induct t))))

(defthm lw-complex-exp-clipped-moment-dyadic-before-cutpoint
  (implies (and (rationalp start) (rationalp end) (rationalp cutpoint)
                (<= start end) (<= end cutpoint))
           (equal (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint error) (cons 0 0)))
  :hints (("Goal" :induct (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint error)
                  :in-theory (enable lw-complex-add))))

(defun lw-complex-exp-clipped-moment-increment (point start end cutpoint error)
  (lw-complex-sub
   (lw-complex-scale (max end cutpoint)
     (lw-complex-exp-value (lw-complex-scale (max end cutpoint) point) error))
   (lw-complex-scale (max start cutpoint)
     (lw-complex-exp-value (lw-complex-scale (max start cutpoint) point) error))))

(defthm lw-complex-exp-clipped-moment-increment-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp end) (rationalp cutpoint)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-clipped-moment-increment point start end cutpoint error)))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-value-rational
                   (point (lw-complex-scale (max start cutpoint) point)))
                 (:instance lw-complex-exp-value-rational
                   (point (lw-complex-scale (max end cutpoint) point))))
           :in-theory (e/d (lw-complexp lw-complex-sub lw-complex-scale)
                           (lw-complex-exp-value-rational)) :do-not-induct t)))

(defthm lw-complex-exp-clipped-moment-increment-add
  (equal
   (lw-complex-exp-clipped-moment-increment point start end cutpoint error)
   (lw-complex-add
    (lw-complex-exp-clipped-moment-increment point start middle cutpoint error)
    (lw-complex-exp-clipped-moment-increment point middle end cutpoint error)))
  :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))
  :rule-classes nil)

(local (in-theory (disable lw-complex-exp-clipped-moment-increment lw-complex-exp-clipped-moment-dyadic)))

(local (defthm lw-cmd-midpoint-widths
         (implies (and (rationalp start) (rationalp end))
                  (and (equal (- (/ (+ start end) 2) start) (* 1/2 (- end start)))
                       (equal (- end (/ (+ start end) 2)) (* 1/2 (- end start)))))
         :rule-classes nil))

(local (defthm lw-cmd-half-mesh
         (implies (and (rationalp start) (rationalp end) (not (zp depth)))
                  (and
                   (equal (lw-halved-width (- (/ (+ start end) 2) start) (- depth 1))
                          (lw-halved-width (- end start) depth))
                   (equal (lw-halved-width (- end (/ (+ start end) 2)) (- depth 1))
                          (lw-halved-width (- end start) depth))))
         :hints (("Goal"
                  :use (lw-cmd-midpoint-widths
                        (:instance lw-halved-width-half (width (- end start)) (steps (- depth 1))))
                  :expand ((lw-halved-width (- end start) depth))
                  :in-theory (disable lw-halved-width-half)))
         :rule-classes nil))

(local (defthm lw-cmd-mesh-data
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth))
                       (<= 0 (lw-halved-width width depth))
                       (<= (lw-halved-width width depth) width)))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))


(local (defthm lw-cmd-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cmd-coefficient-data
         (implies (and (rationalp bound) (<= 0 bound) (rationalp slope) (<= 0 slope)
                       (rationalp cap) (<= 0 cap) (rationalp weight) (<= 0 weight))
                  (and (<= 0 (* cap slope (+ 1 (* bound slope))))
                       (<= 0 (* bound weight))))
         :hints (("Goal"
                  :use ((:instance lw-cmd-nonnegative-product (a bound) (b slope))
                        (:instance lw-cmd-nonnegative-product (a cap) (b slope))
                        (:instance lw-cmd-nonnegative-product (a (* cap slope)) (b (+ 1 (* bound slope))))
                        (:instance lw-cmd-nonnegative-product (a bound) (b weight)))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmd-budget-scalar
         (implies (and (rationalp cap) (<= 0 cap) (rationalp weight) (<= 0 weight)
                       (rationalp error) (<= 0 error)
                       (rationalp small) (<= 0 small) (rationalp large) (<= small large))
                  (and (<= 0 (+ (* cap small small) (* weight error)))
                       (<= (+ (* cap small small) (* weight error))
                           (+ (* cap large large) (* weight error)))))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cmd-step-budget-data
         (implies
          (and (lw-complexp point) (rationalp bound) (<= 0 bound)
               (rationalp small) (<= 0 small) (rationalp large) (<= small large)
               (rationalp argument-cap) (<= 0 argument-cap) (rationalp error) (< 0 error))
          (and (rationalp (lw-complex-exp-moment-step-budget point small bound argument-cap error))
               (<= 0 (lw-complex-exp-moment-step-budget point small bound argument-cap error))
               (<= (lw-complex-exp-moment-step-budget point small bound argument-cap error)
                   (lw-complex-exp-moment-step-budget point large bound argument-cap error))))
         :hints (("Goal"
                  :use (lw-complex-l1-bound lw-complex-exp-uniform-cap-data
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap 1))
                        (:instance lw-cmd-coefficient-data
                          (slope (lw-complex-l1 point)) (cap (lw-complex-exp-uniform-cap argument-cap))
                          (weight (+ (lw-complex-exp-uniform-cap 1)
                                     (* 2 (lw-complex-exp-uniform-cap argument-cap)) 2)))
                        (:instance lw-cmd-budget-scalar
                          (cap (* (lw-complex-exp-uniform-cap argument-cap) (lw-complex-l1 point)
                                  (+ 1 (* bound (lw-complex-l1 point)))))
                          (weight (* bound (+ (lw-complex-exp-uniform-cap 1)
                                              (* 2 (lw-complex-exp-uniform-cap argument-cap)) 2)))))
                  :in-theory (e/d (lw-complex-exp-moment-step-budget lw-complex-exp-grid-step-budget)
                                  (lw-complex-l1-bound lw-complex-exp-uniform-cap-data))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmd-sub-self
         (equal (lw-complex-sub a a) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-sub)))))
(local (defthm lw-cmd-zero-disk
         (implies (and (rationalp radius) (<= 0 radius)) (lw-complex-diskp (cons 0 0) radius))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-diskp lw-diskp) :nonlinearp t))))
(local (defthm lw-cmd-scale-zero
         (equal (lw-complex-scale 0 point) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-scale)))))
(local (defthm lw-cmd-mul-zero
         (equal (lw-complex-mul point (cons 0 0)) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-mul)))))
(local (defthm lw-cmd-rectangle-shape
         (equal
          (lw-complex-sub (lw-complex-sub a b) (lw-complex-add base (lw-complex-mul point cell)))
          (lw-complex-sub a (lw-complex-add b (lw-complex-add base (lw-complex-mul point cell)))))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub)))))
(local (defthm lw-cmd-endpoint-split
         (implies (and (rationalp node) (rationalp end)) (equal (+ node (- end node)) end))
         :rule-classes nil))

(local (defthm lw-cmd-clipped-rectangle
         (implies
          (and (lw-complexp point) (rationalp start) (<= 0 start)
               (rationalp end) (<= start end) (rationalp bound) (<= end bound)
               (rationalp cutpoint) (<= 0 cutpoint) (rationalp mesh) (<= (- end start) mesh)
               (rationalp argument-cap) (<= 0 argument-cap)
               (<= (* (lw-complex-l1 point) bound) argument-cap)
               (<= (* (lw-complex-l1 point) mesh) 1) (rationalp error) (< 0 error))
          (lw-complex-diskp
           (lw-complex-sub
            (lw-complex-exp-clipped-moment-increment point start end cutpoint error)
            (lw-complex-add
             (lw-complex-exp-clipped-dyadic point start end 0 cutpoint error)
             (lw-complex-mul point (lw-complex-exp-clipped-moment-dyadic point start end 0 cutpoint error))))
           (lw-complex-exp-moment-step-budget point mesh bound argument-cap error)))
         :hints
         (("Goal"
           :use (lw-complex-l1-bound
                 (:instance lw-cmd-step-budget-data (small mesh) (large mesh))
                 (:instance lw-cmd-step-budget-data (small (- end (max start cutpoint))) (large mesh))
                 (:instance lw-cmd-multiply-order
                   (a (- end (max start cutpoint))) (b mesh) (factor (lw-complex-l1 point)))
                 (:instance lw-cmd-endpoint-split (node (max start cutpoint)))
                 (:instance lw-complex-exp-moment-rectangle-defect
                   (start (max start cutpoint)) (step (- end (max start cutpoint))))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-clipped-moment-increment point start end cutpoint error)
                     (lw-complex-add
                      (lw-complex-exp-clipped-dyadic point start end 0 cutpoint error)
                      (lw-complex-mul point (lw-complex-exp-clipped-moment-dyadic point start end 0 cutpoint error)))))
                   (radius (lw-complex-exp-moment-step-budget point (- end (max start cutpoint)) bound argument-cap error))
                   (cap (lw-complex-exp-moment-step-budget point mesh bound argument-cap error))))
           :cases ((<= end cutpoint) (equal start end))
           :in-theory
           (e/d (lw-complex-exp-clipped-moment-increment lw-complex-exp-clipped-moment-dyadic
                 lw-complex-exp-clipped-dyadic)
                (lw-complex-l1-bound lw-complex-exp-moment-rectangle-defect))
           :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cmd-residual-add
         (equal
          (lw-complex-sub
           (lw-complex-add a b)
           (lw-complex-add (lw-complex-add base-left base-right)
                           (lw-complex-mul point (lw-complex-add left right))))
          (lw-complex-add
           (lw-complex-sub a (lw-complex-add base-left (lw-complex-mul point left)))
           (lw-complex-sub b (lw-complex-add base-right (lw-complex-mul point right)))))
         :hints (("Goal" :in-theory (enable lw-complex-add lw-complex-sub lw-complex-mul)))
         :rule-classes nil))

(local (defthm lw-cmd-double
         (equal (+ a a) (* 2 a))
         :hints (("Goal" :cases ((acl2-numberp a))))))

(defthm lw-complex-exp-clipped-moment-dyadic-telescope
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp end) (<= start end)
        (rationalp bound) (<= end bound) (natp depth) (rationalp cutpoint) (<= 0 cutpoint)
        (rationalp argument-cap) (<= 0 argument-cap)
        (<= (* (lw-complex-l1 point) bound) argument-cap)
        (<= (* (lw-complex-l1 point) (lw-halved-width (- end start) depth)) 1)
        (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-clipped-moment-increment point start end cutpoint error)
     (lw-complex-add
      (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)
      (lw-complex-mul point (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint error))))
    (* (lw-dyadic-leaf-count depth)
       (lw-complex-exp-moment-step-budget point (lw-halved-width (- end start) depth) bound argument-cap error))))
  :hints
  (("Goal"
    :induct (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint error)
    :in-theory
    (e/d ((:induction lw-complex-exp-clipped-moment-dyadic)
          (:definition lw-complex-exp-clipped-moment-dyadic)
          lw-complex-exp-clipped-dyadic lw-dyadic-leaf-count lw-halved-width)
         (lw-complex-exp-clipped-moment-dyadic-before-cutpoint)))
   (and stable-under-simplificationp
        '(:use
          (lw-cmd-half-mesh
           (:instance lw-complex-exp-clipped-moment-increment-add (middle (/ (+ start end) 2)))
           (:instance lw-cmd-clipped-rectangle (mesh (- end start)))
           (:instance lw-cmd-residual-add
             (a (lw-complex-exp-clipped-moment-increment point start (/ (+ start end) 2) cutpoint error))
             (b (lw-complex-exp-clipped-moment-increment point (/ (+ start end) 2) end cutpoint error))
             (base-left (lw-complex-exp-clipped-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint error))
             (base-right (lw-complex-exp-clipped-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint error))
             (left (lw-complex-exp-clipped-moment-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint error))
             (right (lw-complex-exp-clipped-moment-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint error)))
           (:instance lw-complex-add-disk
             (left (lw-complex-sub
               (lw-complex-exp-clipped-moment-increment point start (/ (+ start end) 2) cutpoint error)
               (lw-complex-add
                (lw-complex-exp-clipped-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint error)
                (lw-complex-mul point
                  (lw-complex-exp-clipped-moment-dyadic point start (/ (+ start end) 2) (- depth 1) cutpoint error)))))
             (right (lw-complex-sub
               (lw-complex-exp-clipped-moment-increment point (/ (+ start end) 2) end cutpoint error)
               (lw-complex-add
                (lw-complex-exp-clipped-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint error)
                (lw-complex-mul point
                  (lw-complex-exp-clipped-moment-dyadic point (/ (+ start end) 2) end (- depth 1) cutpoint error)))))
             (radius (* (lw-dyadic-leaf-count (- depth 1))
                        (lw-complex-exp-moment-step-budget
                         point (lw-halved-width (- (/ (+ start end) 2) start) (- depth 1)) bound argument-cap error)))
             (other-radius (* (lw-dyadic-leaf-count (- depth 1))
                              (lw-complex-exp-moment-step-budget
                               point (lw-halved-width (- end (/ (+ start end) 2)) (- depth 1)) bound argument-cap error)))))
          :expand
          ((lw-complex-exp-clipped-moment-dyadic point start end 0 cutpoint error)
           (lw-complex-exp-clipped-dyadic point start end 0 cutpoint error)
           (lw-halved-width (- end start) depth))
          :in-theory
          (disable lw-complex-exp-clipped-moment-dyadic lw-complex-exp-clipped-dyadic
                   lw-dyadic-leaf-count lw-halved-width
                   lw-complex-exp-clipped-moment-dyadic-before-cutpoint lw-complex-add-disk)
          :nonlinearp nil :do-not-induct t))))

(defun lw-complex-exp-clipped-moment-primitive (point start end cutpoint error)
  (lw-complex-exp-moment-primitive point (max start cutpoint) (max end cutpoint) error))

(defthm lw-complex-exp-clipped-moment-primitive-rational
  (implies (and (lw-complexp point) (rationalp start) (rationalp end) (rationalp cutpoint)
                (rationalp error) (< 0 error))
           (lw-complexp (lw-complex-exp-clipped-moment-primitive point start end cutpoint error))))

(defthm lw-complex-exp-clipped-moment-primitive-endpoint
  (implies (and (rationalp start) (rationalp end) (rationalp cutpoint) (<= start end))
           (equal (lw-complex-exp-clipped-moment-primitive point start end cutpoint error)
                  (if (<= end cutpoint) (cons 0 0)
                    (lw-complex-exp-moment-primitive point (max start cutpoint) end error))))
  :hints (("Goal" :in-theory (enable lw-complex-exp-moment-primitive lw-complex-exp-primitive-value
                                    lw-complex-quotient lw-complex-mul))))

(local (in-theory (disable lw-complex-exp-clipped-moment-primitive
                           lw-complex-exp-clipped-moment-primitive-endpoint lw-complex-exp-moment-grid-budget)))

(local (defthm lw-cmd-last-cancel
         (implies (and (lw-complexp a) (lw-complexp b) (not (equal a (cons 0 0))))
                  (equal (lw-complex-mul a (lw-complex-mul b (lw-complex-reciprocal a))) b))
         :hints (("Goal" :use ((:instance lw-complex-mul-left-commutes
                                (c (lw-complex-reciprocal a))))
                         :in-theory (disable lw-complex-mul-commutative
                                             lw-complex-mul-left-commutes)))))

(local (defthm lw-cmd-quotient-defect
         (implies (and (lw-complexp point) (not (equal point (cons 0 0)))
                       (lw-complexp value) (lw-complexp total))
                  (equal
                   (lw-complex-quotient (lw-complex-sub value (lw-complex-mul point total)) point)
                   (lw-complex-sub (lw-complex-quotient value point) total)))
         :hints (("Goal" :in-theory (enable lw-complex-quotient lw-complex-mul-subtract
                                          lw-complex-mul-commutative lw-complex-mul-left-commutes)))))

(local (defthm lw-cmd-residual-combine
         (implies (and (lw-complexp weighted) (lw-complexp total0) (lw-complexp total1)
                       (lw-complexp primitive0) (lw-complexp point))
                  (equal
                   (lw-complex-add
                     (lw-complex-sub weighted (lw-complex-add total0 (lw-complex-mul point total1)))
                     (lw-complex-sub total0 primitive0))
                   (lw-complex-sub (lw-complex-sub weighted primitive0)
                                   (lw-complex-mul point total1))))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul)))))

(local (defthm lw-cmd-quotient-disk
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


(local (defthm lw-cmd-primitive-form
         (equal
          (lw-complex-exp-clipped-moment-primitive point start end cutpoint error)
          (lw-complex-quotient
           (lw-complex-sub
            (lw-complex-exp-clipped-moment-increment point start end cutpoint error)
            (lw-complex-exp-clipped-primitive point start end cutpoint error)) point))
         :hints (("Goal"
                  :in-theory (enable lw-complex-exp-clipped-moment-primitive lw-complex-exp-moment-primitive
                                     lw-complex-exp-clipped-moment-increment lw-complex-exp-clipped-primitive)))
         :rule-classes nil))

(defthm lw-complex-exp-clipped-moment-dyadic-primitive-error
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
     (lw-complex-exp-clipped-moment-primitive point start end cutpoint error)
     (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint error))
    (lw-complex-exp-moment-grid-budget point (lw-halved-width (- end start) depth)
                                      bound argument-cap (lw-dyadic-leaf-count depth) clearance error)))
  :hints (("Goal"
           :use (
            lw-complex-exp-clipped-moment-dyadic-telescope lw-complex-exp-clipped-dyadic-primitive-error
            lw-cmd-primitive-form
            (:instance lw-complex-norm-lower-nonzero (lower clearance))
            (:instance lw-complex-difference-symmetric
              (left (lw-complex-exp-clipped-primitive point start end cutpoint error))
              (right (lw-complex-exp-clipped-dyadic point start end depth cutpoint error))
              (radius (* (lw-dyadic-leaf-count depth)
                         (lw-complex-exp-grid-step-budget
                          point (lw-halved-width (- end start) depth) argument-cap error)
                         (/ clearance))))
            (:instance lw-complex-add-disk
              (left (lw-complex-sub
                (lw-complex-exp-clipped-moment-increment point start end cutpoint error)
                (lw-complex-add
                 (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)
                 (lw-complex-mul point (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint error)))))
              (radius (* (lw-dyadic-leaf-count depth)
                         (lw-complex-exp-moment-step-budget
                          point (lw-halved-width (- end start) depth) bound argument-cap error)))
              (right (lw-complex-sub
                (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)
                (lw-complex-exp-clipped-primitive point start end cutpoint error)))
              (other-radius (* (lw-dyadic-leaf-count depth)
                               (lw-complex-exp-grid-step-budget
                                point (lw-halved-width (- end start) depth) argument-cap error)
                               (/ clearance))))
            (:instance lw-cmd-quotient-disk
              (numerator (lw-complex-add
                (lw-complex-sub
                 (lw-complex-exp-clipped-moment-increment point start end cutpoint error)
                 (lw-complex-add
                  (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)
                  (lw-complex-mul point (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint error))))
                (lw-complex-sub
                 (lw-complex-exp-clipped-dyadic point start end depth cutpoint error)
                 (lw-complex-exp-clipped-primitive point start end cutpoint error))))
              (denominator point)
              (radius
               (+ (* (lw-dyadic-leaf-count depth)
                     (lw-complex-exp-moment-step-budget
                      point (lw-halved-width (- end start) depth) bound argument-cap error))
                  (* (lw-dyadic-leaf-count depth)
                     (lw-complex-exp-grid-step-budget
                      point (lw-halved-width (- end start) depth) argument-cap error)
                     (/ clearance))))))
           :in-theory
           (e/d (lw-complex-exp-moment-grid-budget)
                (lw-complex-exp-clipped-moment-dyadic-telescope lw-complex-exp-clipped-dyadic-primitive-error
                 lw-cmd-quotient-disk lw-complex-add-disk))
           :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-clipped-moment-primitive-cauchy
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp end) (<= start end)
        (rationalp bound) (<= end bound) (rationalp cutpoint) (<= 0 cutpoint)
        (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point))
        (rationalp left-error) (< 0 left-error) (rationalp right-error) (< 0 right-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-clipped-moment-primitive point start end cutpoint left-error)
     (lw-complex-exp-clipped-moment-primitive point start end cutpoint right-error))
    (* 2 (+ bound (/ clearance)) (+ left-error right-error) (/ clearance))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-moment-primitive-cauchy
                   (start (max start cutpoint)))
                 (:instance lw-cmd-nonnegative-product (a (+ bound (/ clearance))) (b (+ left-error right-error)))
                 (:instance lw-cmd-nonnegative-product
                   (a (* (+ bound (/ clearance)) (+ left-error right-error))) (b (* 2 (/ clearance)))))
           :cases ((<= end cutpoint))
           :in-theory (e/d (lw-complex-exp-clipped-moment-primitive-endpoint)
                           (lw-complex-exp-moment-primitive-cauchy))
           :nonlinearp nil :do-not-induct t)))
