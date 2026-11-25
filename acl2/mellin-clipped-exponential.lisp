(in-package "ACL2")

(include-book "complex-damped-product")
(include-book "complex-exp-dyadic-moment-grid")
(include-book "mellin-frozen-cutpoints")
(include-book "mellin-exponential-sample")

; Identify the three frozen correction components with complex
; exponential grids at their actual, independent primitive precisions.
; These are zeroth Mellin moments; the first-moment component is u*exp(u).

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-exp-value lw-complex-exp-cap lw-complex-l1
                 lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-exp-bounds lw-exp-neg-bounds
                 lw-damped-phase-sample lw-phase-value lw-exp-term
                 lw-mellin-weight lw-mellin-phase lw-mellin-kernel-error lw-mellin-phase-error
                 lw-mellin-signal-error lw-mellin-signal-cap lw-mellin-kernel-cap lw-mellin-component-error
                 lw-mellin-negative-error lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                 lw-mellin-frozen-basis-dyadic lw-mellin-clipped-basis-dyadic
                 lw-mellin-clipped-basis-before-cutpoint lw-mellin-clipped-ramp-linearization
                 lw-mellin-frozen-ramp-before-cutpoint lw-mellin-frozen-ramp-after-cutpoint
                 lw-complex-exp-clipped-dyadic lw-complex-exp-clipped-moment-dyadic
                 lw-complex-exp-clipped-dyadic-before-cutpoint lw-complex-exp-clipped-moment-dyadic-before-cutpoint
                 lw-complex-disk-enlarge lw-disk-enlarge
                 lw-complex-sub-add-first lw-complex-add-commutative lw-complex-add-left-commutes)))

(local (defthm lw-mce-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mce-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mce-times-negative
         (equal (* a (- b)) (- (* a b)))
         :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mce-negative-times
         (equal (* (- a) b) (- (* a b)))
         :hints (("Goal" :use ((:instance lw-mce-times-negative (a b) (b a)))
                         :in-theory (disable lw-mce-times-negative)))))
(local (defthm lw-mce-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mce-pair-complex
         (implies (and (rationalp a) (rationalp b)) (lw-complexp (cons a b)))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-mce-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-mce-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mce-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-mce-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(defun lw-mellin-zero-kernel (value sigma height sample-error)
  (lw-complex-scale (lw-mellin-weight value sigma 0 1 sample-error)
                    (lw-mellin-phase value sigma height 0 1 sample-error)))

(defun lw-mellin-exponential-component (kind value sigma height exp-error sample-error)
  (let ((kernel (lw-mellin-zero-kernel value sigma height sample-error)))
    (if (equal kind 3) kernel
      (lw-complex-scale
       (* (if (equal kind 1) value 1) (car (lw-exp-bounds value exp-error))) kernel))))

(defun lw-mellin-basis-exponential-point (kind sigma height)
  (cons (if (equal kind 3) (- sigma) (- 1 sigma)) (- height)))

(defun lw-mellin-exponential-model (kind value sigma height complex-error)
  (let ((point (lw-complex-exp-value
                (lw-complex-scale value (lw-mellin-basis-exponential-point kind sigma height)) complex-error)))
    (if (equal kind 1) (lw-complex-scale value point) point)))

(defun lw-mellin-exponential-moment-cap (kind cap) (if (equal kind 1) cap 1))

(defun lw-mellin-exponential-component-error (cap exp-error sample-error complex-error)
  (+ exp-error (* 2 (lw-complex-exp-uniform-cap cap) sample-error) complex-error))

(defthm lw-mellin-zero-kernel-form
  (equal
   (lw-mellin-zero-kernel value sigma height sample-error)
   (lw-damped-phase-sample (* sigma value) (- (* height value))
                           (lw-mellin-negative-error value 0 1 sample-error)
                           (lw-mellin-phase-error value sigma 0 1 sample-error)))
  :hints (("Goal"
           :in-theory (enable lw-mellin-zero-kernel lw-mellin-weight lw-mellin-phase
                              lw-kernel-weight-bounds lw-kernel-weight-scale lw-kernel-weight-precision
                              lw-mellin-negative-error lw-damped-phase-sample lw-exp-term lw-complex-scale)
           :do-not-induct t)))

(defthm lw-mellin-exponential-component-error-valid
  (implies (and (rationalp cap) (<= 0 cap) (rationalp exp-error) (< 0 exp-error)
                (rationalp sample-error) (< 0 sample-error) (rationalp complex-error) (< 0 complex-error))
           (and (rationalp (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))
                (< 0 (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))
                (rationalp (lw-mellin-exponential-moment-cap kind cap))
                (<= 0 (lw-mellin-exponential-moment-cap kind cap))))
  :hints (("Goal"
           :use ((:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
                 (:instance lw-mce-positive-product (a (lw-complex-exp-uniform-cap cap)) (b sample-error)))
           :in-theory (disable lw-complex-exp-uniform-cap-data) :nonlinearp nil :do-not-induct t)))

(defthm lw-mellin-zero-basis-leaf-form
  (implies (member-equal kind '(0 1 3))
           (equal
            (lw-mellin-frozen-basis-dyadic
             kind start end 0 sigma height 0 exp-error prime log-error sample-error)
            (lw-complex-scale (- end start)
              (lw-mellin-exponential-component kind start sigma height exp-error sample-error))))
  :hints (("Goal"
           :in-theory (e/d (lw-mellin-frozen-basis-dyadic lw-mellin-exponential-component
                             lw-mellin-zero-kernel lw-complex-scale)
                            (lw-mellin-zero-kernel-form))
           :do-not-induct t)))

(local (in-theory
        (disable lw-mellin-zero-kernel lw-mellin-exponential-component lw-mellin-basis-exponential-point
                 lw-mellin-exponential-model lw-mellin-exponential-moment-cap lw-mellin-exponential-component-error)))

(local (defthm lw-mce-real-cap
         (implies (and (rationalp value) (<= 0 value))
                  (and (equal (lw-complex-l1 (cons value 0)) value)
                       (equal (lw-complex-exp-cap (cons value 0)) (lw-exp-lipschitz-cap value))))
         :hints (("Goal" :in-theory (enable lw-complex-exp-cap lw-complex-l1 lw-exp-lipschitz-cap)))))

(local (defthm lw-mce-uniform-scalar
         (implies
          (and (rationalp slope) (<= 0 slope) (rationalp top) (<= 1 top) (<= slope top)
               (rationalp negative) (rationalp phase) (rationalp sample) (<= 0 sample)
               (<= negative sample) (<= phase sample)
               (rationalp exp-error) (<= 0 exp-error) (rationalp complex-error))
          (and (<= (+ negative phase complex-error) (+ exp-error (* 2 top sample) complex-error))
               (<= (+ exp-error (* slope (+ negative phase)) complex-error)
                   (+ exp-error (* 2 top sample) complex-error))))
         :hints (("Goal"
                  :use ((:instance lw-mce-multiply-order (a (+ negative phase)) (b (* 2 sample)) (factor slope))
                        (:instance lw-mce-multiply-order (a slope) (b top) (factor (* 2 sample)))
                        (:instance lw-mce-multiply-order (a 1) (b top) (factor (* 2 sample))))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mce-unweighted-comparison
         (implies
          (and (or (equal kind 0) (equal kind 3))
               (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
               (rationalp sigma) (<= 0 sigma) (rationalp height)
               (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
               (rationalp complex-error) (< 0 complex-error))
          (lw-complex-diskp
           (lw-complex-sub
            (lw-mellin-exponential-component kind value sigma height exp-error sample-error)
            (lw-mellin-exponential-model kind value sigma height complex-error))
           (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))
         :hints (("Goal"
                  :use (
                   (:instance lw-mellin-error-budgets (index 0) (step 1) (error sample-error))
                   (:instance lw-mellin-primitive-errors-at-most (index 0) (step 1) (error sample-error))
                   (:instance lw-mellin-negative-error-data (index 0) (step 1) (error sample-error))
                   (:instance lw-mce-nonnegative-product (a sigma) (b value))
                   (:instance lw-exp-lipschitz-cap-valid (cap value))
                   (:instance lw-complex-exp-uniform-cap-data (argument-cap cap))
                   (:instance lw-complex-exp-cap-uniform (point (cons value 0)) (argument-cap cap))
                   (:instance lw-complex-exp-kernel-agreement
                     (value (* sigma value)) (angle (- (* height value)))
                     (negative-error (lw-mellin-negative-error value 0 1 sample-error))
                     (phase-error (lw-mellin-phase-error value sigma 0 1 sample-error)))
                   (:instance lw-exp-times-damped-phase-agreement
                     (exponent value) (value (* sigma value)) (angle (- (* height value)))
                     (negative-error (lw-mellin-negative-error value 0 1 sample-error))
                     (phase-error (lw-mellin-phase-error value sigma 0 1 sample-error)))
                   (:instance lw-mce-uniform-scalar
                     (slope (lw-exp-lipschitz-cap value)) (top (lw-complex-exp-uniform-cap cap))
                     (negative (lw-mellin-negative-error value 0 1 sample-error))
                     (phase (lw-mellin-phase-error value sigma 0 1 sample-error)) (sample sample-error))
                   (:instance lw-complex-disk-enlarge
                     (point (lw-complex-sub
                       (lw-mellin-exponential-component kind value sigma height exp-error sample-error)
                       (lw-mellin-exponential-model kind value sigma height complex-error)))
                     (radius (if (equal kind 3)
                                 (+ (lw-mellin-negative-error value 0 1 sample-error)
                                    (lw-mellin-phase-error value sigma 0 1 sample-error) complex-error)
                               (+ exp-error
                                  (* (lw-exp-lipschitz-cap value)
                                     (+ (lw-mellin-negative-error value 0 1 sample-error)
                                        (lw-mellin-phase-error value sigma 0 1 sample-error))) complex-error)))
                     (cap (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))))
                  :cases ((equal kind 3))
                  :in-theory
                  (e/d (lw-mellin-exponential-component lw-mellin-exponential-model lw-mellin-basis-exponential-point
                        lw-mellin-exponential-component-error lw-complex-scale)
                       (lw-mellin-error-budgets lw-mellin-primitive-errors-at-most lw-mellin-negative-error-data
                        lw-exp-lipschitz-cap-valid lw-complex-exp-uniform-cap-data lw-complex-exp-cap-uniform
                        lw-complex-exp-kernel-agreement lw-exp-times-damped-phase-agreement))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-mce-component-moment
         (equal
          (lw-mellin-exponential-component 1 value sigma height exp-error sample-error)
          (lw-complex-scale value (lw-mellin-exponential-component 0 value sigma height exp-error sample-error)))
         :hints (("Goal" :in-theory (enable lw-mellin-exponential-component lw-complex-scale)))))
(local (defthm lw-mce-model-moment
         (equal (lw-mellin-exponential-model 1 value sigma height complex-error)
                (lw-complex-scale value (lw-mellin-exponential-model 0 value sigma height complex-error)))
         :hints (("Goal" :in-theory (enable lw-mellin-exponential-model lw-mellin-basis-exponential-point)))))
(local (defthm lw-mce-scale-difference
         (equal (lw-complex-sub (lw-complex-scale factor a) (lw-complex-scale factor b))
                (lw-complex-scale factor (lw-complex-sub a b)))
         :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-scale)))))
(local (defthm lw-mce-add-differences
         (equal (lw-complex-sub (lw-complex-add a b) (lw-complex-add c d))
                (lw-complex-add (lw-complex-sub a c) (lw-complex-sub b d)))
         :hints (("Goal" :in-theory (enable lw-complex-sub lw-complex-add)))))
(local (defthm lw-mce-sub-self
         (equal (lw-complex-sub a a) (cons 0 0))
         :hints (("Goal" :in-theory (enable lw-complex-sub)))))
(local (defthm lw-mce-zero-disk
         (implies (and (rationalp radius) (<= 0 radius)) (lw-complex-diskp (cons 0 0) radius))
         :hints (("Goal" :in-theory (enable lw-complexp lw-complex-diskp lw-diskp) :nonlinearp t))))

(defthm lw-mellin-exponential-component-comparison
  (implies
   (and (member-equal kind '(0 1 3))
        (rationalp cap) (<= 0 cap) (rationalp value) (<= 0 value) (<= value cap)
        (rationalp sigma) (<= 0 sigma) (rationalp height)
        (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
        (rationalp complex-error) (< 0 complex-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-exponential-component kind value sigma height exp-error sample-error)
     (lw-mellin-exponential-model kind value sigma height complex-error))
    (* (lw-mellin-exponential-moment-cap kind cap)
       (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))))
  :hints (("Goal"
           :use (lw-mce-unweighted-comparison
                 (:instance lw-mce-unweighted-comparison (kind 0))
                 lw-mellin-exponential-component-error-valid
                 (:instance lw-complex-scale-disk
                   (point (lw-complex-sub
                     (lw-mellin-exponential-component 0 value sigma height exp-error sample-error)
                     (lw-mellin-exponential-model 0 value sigma height complex-error)))
                   (factor value)
                   (radius (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))
                 (:instance lw-mce-multiply-order
                   (a value) (b cap) (factor (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-mellin-exponential-component 1 value sigma height exp-error sample-error)
                     (lw-mellin-exponential-model 1 value sigma height complex-error)))
                   (radius (* value (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))
                   (cap (* cap (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))))
           :cases ((equal kind 1))
           :in-theory (e/d (lw-mellin-exponential-moment-cap)
                           (lw-mellin-exponential-component-error-valid lw-complex-scale-disk))
           :nonlinearp nil :do-not-induct t)))

(defun lw-mellin-clipped-exponential-grid (kind start end depth cutpoint sigma height complex-error)
  (let ((point (lw-mellin-basis-exponential-point kind sigma height)))
    (if (equal kind 1)
        (lw-complex-exp-clipped-moment-dyadic point start end depth cutpoint complex-error)
      (lw-complex-exp-clipped-dyadic point start end depth cutpoint complex-error))))

(defthm lw-mellin-clipped-exponential-grid-rational
  (implies (and (rationalp start) (rationalp end) (rationalp cutpoint)
                (rationalp sigma) (rationalp height) (rationalp complex-error) (< 0 complex-error))
           (lw-complexp
            (lw-mellin-clipped-exponential-grid kind start end depth cutpoint sigma height complex-error)))
  :hints (("Goal" :in-theory (enable lw-mellin-basis-exponential-point) :do-not-induct t)))

(local (defthm lw-mce-grid-leaf
         (equal
          (lw-mellin-clipped-exponential-grid kind start end 0 cutpoint sigma height complex-error)
          (if (<= end cutpoint) (cons 0 0)
            (lw-complex-scale (- end (max start cutpoint))
              (lw-mellin-exponential-model kind (max start cutpoint) sigma height complex-error))))
         :hints (("Goal"
                  :in-theory (enable lw-mellin-clipped-exponential-grid lw-complex-exp-clipped-dyadic
                                     lw-complex-exp-clipped-moment-dyadic lw-mellin-exponential-model
                                     lw-mellin-basis-exponential-point lw-complex-scale)
                  :do-not-induct t))))

(local (defthm lw-mce-grid-refinement
         (implies (not (zp depth))
                  (equal
                   (lw-mellin-clipped-exponential-grid kind start end depth cutpoint sigma height complex-error)
                   (lw-complex-add
                    (lw-mellin-clipped-exponential-grid
                     kind start (/ (+ start end) 2) (- depth 1) cutpoint sigma height complex-error)
                    (lw-mellin-clipped-exponential-grid
                     kind (/ (+ start end) 2) end (- depth 1) cutpoint sigma height complex-error))))
         :hints (("Goal"
                  :in-theory (enable lw-mellin-clipped-exponential-grid
                                     lw-complex-exp-clipped-dyadic lw-complex-exp-clipped-moment-dyadic)
                  :do-not-induct t))))

(local (in-theory (disable lw-mellin-clipped-exponential-grid)))

(local (defthm lw-mce-clipped-leaf-comparison
         (implies
          (and (member-equal kind '(0 1 3))
               (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
               (rationalp end) (<= start end) (<= end cap) (rationalp cutpoint) (<= 0 cutpoint)
               (rationalp sigma) (<= 0 sigma) (rationalp height)
               (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
               (rationalp complex-error) (< 0 complex-error))
          (lw-complex-diskp
           (lw-complex-sub
            (lw-mellin-clipped-basis-dyadic
             kind start end 0 cutpoint sigma height 0 exp-error prime log-error sample-error)
            (lw-mellin-clipped-exponential-grid kind start end 0 cutpoint sigma height complex-error))
           (* (- end start) (lw-mellin-exponential-moment-cap kind cap)
              (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))))
         :hints (("Goal"
                  :use (lw-mellin-exponential-component-error-valid
                        (:instance lw-mellin-exponential-component-comparison (value (max start cutpoint)))
                        (:instance lw-complex-scale-disk
                          (point (lw-complex-sub
                            (lw-mellin-exponential-component kind (max start cutpoint) sigma height exp-error sample-error)
                            (lw-mellin-exponential-model kind (max start cutpoint) sigma height complex-error)))
                          (factor (- end (max start cutpoint)))
                          (radius (* (lw-mellin-exponential-moment-cap kind cap)
                                     (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))))
                        (:instance lw-mce-nonnegative-product
                          (a (lw-mellin-exponential-moment-cap kind cap))
                          (b (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))
                        (:instance lw-mce-nonnegative-product
                          (a (- end start))
                          (b (* (lw-mellin-exponential-moment-cap kind cap)
                                (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))))
                        (:instance lw-mce-multiply-order
                          (a (- end (max start cutpoint))) (b (- end start))
                          (factor (* (lw-mellin-exponential-moment-cap kind cap)
                                     (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))))
                        (:instance lw-complex-disk-enlarge
                          (point (lw-complex-sub
                            (lw-mellin-clipped-basis-dyadic
                             kind start end 0 cutpoint sigma height 0 exp-error prime log-error sample-error)
                            (lw-mellin-clipped-exponential-grid kind start end 0 cutpoint sigma height complex-error)))
                          (radius (* (- end (max start cutpoint)) (lw-mellin-exponential-moment-cap kind cap)
                                     (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))
                          (cap (* (- end start) (lw-mellin-exponential-moment-cap kind cap)
                                  (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))))
                  :cases ((<= end cutpoint))
                  :in-theory (e/d (lw-mellin-clipped-basis-dyadic)
                                  (lw-mellin-exponential-component-comparison
                                   lw-mellin-exponential-component-error-valid lw-complex-scale-disk))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-mellin-clipped-basis-exponential-comparison
  (implies
   (and (member-equal kind '(0 1 3))
        (rationalp cap) (<= 0 cap) (rationalp start) (<= 0 start)
        (rationalp end) (<= start end) (<= end cap) (natp depth)
        (rationalp cutpoint) (<= 0 cutpoint) (rationalp sigma) (<= 0 sigma) (rationalp height)
        (rationalp exp-error) (< 0 exp-error) (rationalp sample-error) (< 0 sample-error)
        (rationalp complex-error) (< 0 complex-error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-mellin-clipped-basis-dyadic
      kind start end depth cutpoint sigma height 0 exp-error prime log-error sample-error)
     (lw-mellin-clipped-exponential-grid kind start end depth cutpoint sigma height complex-error))
    (* (- end start) (lw-mellin-exponential-moment-cap kind cap)
       (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))))
  :hints
  (("Goal"
    :induct (lw-mellin-clipped-basis-dyadic
             kind start end depth cutpoint sigma height 0 exp-error prime log-error sample-error)
    :in-theory (e/d ((:induction lw-mellin-clipped-basis-dyadic) (:definition lw-mellin-clipped-basis-dyadic))
                    (member-equal)))
   (and stable-under-simplificationp
        '(:use
          (lw-mce-clipped-leaf-comparison lw-mellin-exponential-component-error-valid
           (:instance lw-complex-add-disk
             (left (lw-complex-sub
               (lw-mellin-clipped-basis-dyadic
                kind start (/ (+ start end) 2) (- depth 1) cutpoint sigma height 0 exp-error prime log-error sample-error)
               (lw-mellin-clipped-exponential-grid
                kind start (/ (+ start end) 2) (- depth 1) cutpoint sigma height complex-error)))
             (right (lw-complex-sub
               (lw-mellin-clipped-basis-dyadic
                kind (/ (+ start end) 2) end (- depth 1) cutpoint sigma height 0 exp-error prime log-error sample-error)
               (lw-mellin-clipped-exponential-grid
                kind (/ (+ start end) 2) end (- depth 1) cutpoint sigma height complex-error)))
             (radius (* (- (/ (+ start end) 2) start) (lw-mellin-exponential-moment-cap kind cap)
                        (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))
             (other-radius (* (- end (/ (+ start end) 2)) (lw-mellin-exponential-moment-cap kind cap)
                              (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))))
           (:instance lw-complex-disk-enlarge
             (point (lw-complex-add
               (lw-complex-sub
                (lw-mellin-clipped-basis-dyadic
                 kind start (/ (+ start end) 2) (- depth 1) cutpoint sigma height 0 exp-error prime log-error sample-error)
                (lw-mellin-clipped-exponential-grid
                 kind start (/ (+ start end) 2) (- depth 1) cutpoint sigma height complex-error))
               (lw-complex-sub
                (lw-mellin-clipped-basis-dyadic
                 kind (/ (+ start end) 2) end (- depth 1) cutpoint sigma height 0 exp-error prime log-error sample-error)
                (lw-mellin-clipped-exponential-grid
                 kind (/ (+ start end) 2) end (- depth 1) cutpoint sigma height complex-error))))
             (radius (+ (* (- (/ (+ start end) 2) start) (lw-mellin-exponential-moment-cap kind cap)
                           (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))
                        (* (- end (/ (+ start end) 2)) (lw-mellin-exponential-moment-cap kind cap)
                           (lw-mellin-exponential-component-error cap exp-error sample-error complex-error))))
             (cap (* (- end start) (lw-mellin-exponential-moment-cap kind cap)
                     (lw-mellin-exponential-component-error cap exp-error sample-error complex-error)))))
          :expand ((lw-mellin-clipped-basis-dyadic
                    kind start end 0 cutpoint sigma height 0 exp-error prime log-error sample-error))
          :in-theory (disable lw-mellin-clipped-basis-dyadic lw-mce-grid-refinement member-equal
                              lw-mellin-exponential-component-error-valid lw-complex-add-disk)
          :nonlinearp nil :do-not-induct t))))
