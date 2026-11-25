(in-package "ACL2")

(include-book "complex-exp-dyadic-grid")
(include-book "complex-exp-integral")

; Compute a dyadic depth and evaluation precision for the clipped
; exponential primitive. No mesh or point-budget premise is supplied.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-l1 lw-complex-norm-square
                 lw-complex-exp-value lw-complex-exp-primitive-value lw-complex-exp-grid
                 lw-complex-exp-clipped-dyadic lw-complex-exp-clipped-primitive
                 lw-complex-exp-clipped-primitive-endpoint lw-complex-exp-clipped-increment
                 lw-complex-exp-grid-step-budget lw-complex-exp-uniform-cap lw-exp-lipschitz-cap lw-exp-bounds
                 lw-complex-exp-integration-argument-cap lw-complex-exp-integration-weight
                 lw-dyadic-leaf-count lw-halved-width lw-halving-depth lw-precision-fuel
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-cei-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-cei-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-cei-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))
(local (defthm lw-cei-zero-times (equal (* 0 a) 0)))
(local (defthm lw-cei-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal" :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                              (:instance inverse-of-* (x divisor)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-cei-left-commutes)))))
(local (defthm lw-cei-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b) (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cei-nonnegative-product
         (implies (and (rationalp a) (<= 0 a) (rationalp b) (<= 0 b)) (<= 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))
(local (defthm lw-cei-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cei-mesh-scale
         (implies (and (rationalp width) (rationalp factor))
                  (equal (lw-halved-width (* factor width) depth) (* factor (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))
(local (defthm lw-cei-mesh-data
         (implies (and (rationalp width) (<= 0 width))
                  (and (rationalp (lw-halved-width width depth))
                       (<= 0 (lw-halved-width width depth))))
         :hints (("Goal" :induct (lw-halved-width width depth)
                         :in-theory (enable (:induction lw-halved-width) (:definition lw-halved-width))))
         :rule-classes nil))

(defun lw-complex-exp-dyadic-slope (point start length)
  (+ (lw-complex-l1 point)
     (* (lw-complex-exp-uniform-cap (lw-complex-exp-integration-argument-cap point start length))
        (lw-complex-l1 point) (lw-complex-l1 point) length)))

(defun lw-complex-exp-dyadic-target (clearance error)
  (min 1 (* 1/4 clearance error)))

(defun lw-complex-exp-dyadic-depth (point start length clearance error)
  (let ((width (* length (lw-complex-exp-dyadic-slope point start length)))
        (target (lw-complex-exp-dyadic-target clearance error)))
    (lw-halving-depth width target (lw-precision-fuel width target))))

(defun lw-complex-exp-dyadic-error (point start length clearance error)
  (/ (* clearance error)
     (* 16 (+ 1 (* (lw-dyadic-leaf-count (lw-complex-exp-dyadic-depth point start length clearance error))
                   (lw-complex-exp-integration-weight point start length))))))

(defun lw-complex-exp-dyadic-integral-grid (point start length cutpoint clearance error)
  (lw-complex-exp-clipped-dyadic
   point start (+ start length) (lw-complex-exp-dyadic-depth point start length clearance error) cutpoint
   (lw-complex-exp-dyadic-error point start length clearance error)))

(defun lw-complex-exp-dyadic-integral-value (point start length cutpoint clearance error)
  (lw-complex-exp-clipped-primitive point start (+ start length) cutpoint (* 1/16 clearance error)))

(local (defthm lw-cei-argument-data
         (implies (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length))
                  (and (rationalp (lw-complex-exp-integration-argument-cap point start length))
                       (<= 0 (lw-complex-exp-integration-argument-cap point start length))
                       (rationalp (lw-complex-exp-integration-weight point start length))
                       (<= 1 (lw-complex-exp-integration-weight point start length))))
         :hints (("Goal"
                  :use (lw-complex-l1-bound
                        (:instance lw-cei-nonnegative-product (a (lw-complex-l1 point)) (b (+ start length)))
                        (:instance lw-complex-exp-uniform-cap-data
                          (argument-cap (lw-complex-exp-integration-argument-cap point start length)))
                        (:instance lw-complex-exp-uniform-cap-data (argument-cap 1)))
                  :in-theory (e/d (lw-complex-exp-integration-argument-cap lw-complex-exp-integration-weight)
                                  (lw-complex-l1-bound lw-complex-exp-uniform-cap-data))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cei-slope-scalar
         (implies (and (rationalp slope) (<= 0 slope) (rationalp cap) (<= 0 cap)
                       (rationalp length) (<= 0 length))
                  (and (rationalp (+ slope (* cap slope slope length)))
                       (<= slope (+ slope (* cap slope slope length)))
                       (<= (* cap slope slope length) (+ slope (* cap slope slope length)))
                       (<= 0 (* cap slope slope length))))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cei-slope-data
         (implies (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length))
                  (and (rationalp (lw-complex-exp-dyadic-slope point start length))
                       (<= 0 (lw-complex-exp-dyadic-slope point start length))
                       (<= (lw-complex-l1 point) (lw-complex-exp-dyadic-slope point start length))
                       (<= (* (lw-complex-exp-uniform-cap (lw-complex-exp-integration-argument-cap point start length))
                              (lw-complex-l1 point) (lw-complex-l1 point) length)
                           (lw-complex-exp-dyadic-slope point start length))))
         :hints (("Goal"
                  :use (lw-cei-argument-data lw-complex-l1-bound
                        (:instance lw-complex-exp-uniform-cap-data
                          (argument-cap (lw-complex-exp-integration-argument-cap point start length)))
                        (:instance lw-cei-slope-scalar
                          (slope (lw-complex-l1 point))
                          (cap (lw-complex-exp-uniform-cap (lw-complex-exp-integration-argument-cap point start length)))))
                  :in-theory (e/d (lw-complex-exp-dyadic-slope)
                                  (lw-complex-l1-bound lw-complex-exp-uniform-cap-data))
                  :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(local (defthm lw-cei-target-data
         (implies (and (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
                  (and (rationalp (lw-complex-exp-dyadic-target clearance error))
                       (< 0 (lw-complex-exp-dyadic-target clearance error))
                       (<= (lw-complex-exp-dyadic-target clearance error) 1)
                       (<= (lw-complex-exp-dyadic-target clearance error) (* 1/4 clearance error))))
         :hints (("Goal" :use ((:instance lw-cei-positive-product (a clearance) (b error)))
                         :nonlinearp nil))
         :rule-classes nil))

(defthm lw-complex-exp-dyadic-depth-adequate
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (let* ((depth (lw-complex-exp-dyadic-depth point start length clearance error))
          (mesh (lw-halved-width length depth)))
     (and (natp depth)
          (<= (* (lw-complex-l1 point) mesh) 1)
          (<= (* (lw-complex-exp-uniform-cap (lw-complex-exp-integration-argument-cap point start length))
                 (lw-complex-l1 point) (lw-complex-l1 point) length mesh)
              (* 1/4 clearance error)))))
  :hints (("Goal"
           :use (lw-cei-slope-data lw-cei-target-data lw-complex-l1-bound lw-cei-argument-data
                 (:instance lw-complex-exp-uniform-cap-data
                   (argument-cap (lw-complex-exp-integration-argument-cap point start length)))
                 (:instance lw-cei-mesh-data
                   (width length) (depth (lw-complex-exp-dyadic-depth point start length clearance error)))
                 (:instance lw-cei-nonnegative-product
                   (a length) (b (lw-complex-exp-dyadic-slope point start length)))
                 (:instance lw-precision-fuel-adequate
                   (width (* length (lw-complex-exp-dyadic-slope point start length)))
                   (epsilon (lw-complex-exp-dyadic-target clearance error)))
                 (:instance lw-halving-depth-adequate
                   (width (* length (lw-complex-exp-dyadic-slope point start length)))
                   (epsilon (lw-complex-exp-dyadic-target clearance error))
                   (fuel (lw-precision-fuel (* length (lw-complex-exp-dyadic-slope point start length))
                                           (lw-complex-exp-dyadic-target clearance error))))
                 (:instance lw-cei-mesh-scale
                   (width length) (factor (lw-complex-exp-dyadic-slope point start length))
                   (depth (lw-complex-exp-dyadic-depth point start length clearance error)))
                 (:instance lw-cei-multiply-order
                   (a (lw-complex-l1 point)) (b (lw-complex-exp-dyadic-slope point start length))
                   (factor (lw-halved-width length (lw-complex-exp-dyadic-depth point start length clearance error))))
                 (:instance lw-cei-multiply-order
                   (a (* (lw-complex-exp-uniform-cap (lw-complex-exp-integration-argument-cap point start length))
                         (lw-complex-l1 point) (lw-complex-l1 point) length))
                   (b (lw-complex-exp-dyadic-slope point start length))
                   (factor (lw-halved-width length (lw-complex-exp-dyadic-depth point start length clearance error)))))
           :in-theory
           (e/d (lw-complex-exp-dyadic-depth)
                (lw-complex-exp-dyadic-slope lw-complex-exp-dyadic-target lw-complex-l1-bound
                 lw-complex-exp-uniform-cap-data
                 lw-precision-fuel-adequate lw-halving-depth-adequate))
           :nonlinearp nil :do-not-induct t)))

(local (in-theory
        (disable lw-complex-exp-dyadic-slope lw-complex-exp-dyadic-target lw-complex-exp-dyadic-depth
                 lw-complex-exp-dyadic-error lw-complex-exp-dyadic-integral-grid lw-complex-exp-dyadic-integral-value)))

(local (defthm lw-cei-precision-scalar
         (implies
          (and (rationalp numerator) (< 0 numerator) (rationalp count) (<= 1 count)
               (rationalp weight) (<= 1 weight))
          (let ((delta (/ numerator (* 16 (+ 1 (* count weight))))))
            (and (rationalp delta) (< 0 delta) (<= delta (* 1/16 numerator))
                 (<= (* count weight delta) (* 1/16 numerator)))))
         :hints (("Goal"
                  :use ((:instance lw-cei-positive-product (a count) (b weight))
                        (:instance lw-positive-division-bound
                          (numerator numerator) (divisor (* 16 (+ 1 (* count weight)))) (bound (* 1/16 numerator)))
                        (:instance lw-positive-division-bound
                          (numerator (* count weight numerator)) (divisor (* 16 (+ 1 (* count weight))))
                          (bound (* 1/16 numerator))))
                  :nonlinearp t :do-not-induct t))
         :rule-classes nil))

(defthm lw-complex-exp-dyadic-error-valid
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (let ((delta (lw-complex-exp-dyadic-error point start length clearance error)))
     (and (rationalp delta) (< 0 delta) (<= delta (* 1/16 clearance error))
          (<= (* (lw-dyadic-leaf-count (lw-complex-exp-dyadic-depth point start length clearance error))
                 (lw-complex-exp-integration-weight point start length) delta)
              (* 1/16 clearance error)))))
  :hints (("Goal"
           :use (lw-cei-argument-data
                 (:instance lw-cei-positive-product (a clearance) (b error))
                 (:instance lw-cei-precision-scalar
                   (numerator (* clearance error))
                   (count (lw-dyadic-leaf-count (lw-complex-exp-dyadic-depth point start length clearance error)))
                   (weight (lw-complex-exp-integration-weight point start length))))
           :in-theory (enable lw-complex-exp-dyadic-error) :nonlinearp nil :do-not-induct t)))

(local (defthm lw-cei-multiply-equality
         (implies (equal a b) (equal (* a factor) (* b factor)))
         :rule-classes nil))

(local (defthm lw-cei-total-budget
         (implies
          (and (rationalp count) (rationalp mesh) (rationalp length) (equal (* count mesh) length)
               (rationalp cap) (rationalp slope) (rationalp weight) (rationalp delta)
               (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error)
               (<= (* cap slope slope length mesh) (* 1/4 clearance error))
               (<= (* count weight delta) (* 1/16 clearance error)))
          (<= (* count (+ (* cap slope slope mesh mesh) (* weight delta)) (/ clearance)) (* 1/2 error)))
         :hints (("Goal"
                  :use ((:instance lw-cei-multiply-equality
                          (a (* count mesh)) (b length) (factor (* cap slope slope mesh)))
                        (:instance lw-cei-positive-product (a clearance) (b error))
                        (:instance inverse-of-* (x clearance))
                        (:instance lw-cei-multiply-order
                          (a (+ (* cap slope slope length mesh) (* count weight delta)))
                          (b (* 1/2 clearance error)) (factor (/ clearance))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-complex-exp-dyadic-total-budget
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (let* ((depth (lw-complex-exp-dyadic-depth point start length clearance error))
          (mesh (lw-halved-width length depth))
          (delta (lw-complex-exp-dyadic-error point start length clearance error)))
     (<= (* (lw-dyadic-leaf-count depth)
            (lw-complex-exp-grid-step-budget
             point mesh (lw-complex-exp-integration-argument-cap point start length) delta)
            (/ clearance))
         (* 1/2 error))))
  :hints (("Goal"
           :use (lw-complex-exp-dyadic-depth-adequate lw-complex-exp-dyadic-error-valid
                 lw-cei-argument-data lw-complex-l1-bound
                 (:instance lw-complex-exp-uniform-cap-data
                   (argument-cap (lw-complex-exp-integration-argument-cap point start length)))
                 (:instance lw-complex-exp-uniform-cap-data (argument-cap 1))
                 (:instance lw-cei-mesh-data
                   (width length) (depth (lw-complex-exp-dyadic-depth point start length clearance error)))
                 (:instance lw-dyadic-leaf-count-mesh
                   (width length) (depth (lw-complex-exp-dyadic-depth point start length clearance error)))
                 (:instance lw-cei-total-budget
                   (count (lw-dyadic-leaf-count (lw-complex-exp-dyadic-depth point start length clearance error)))
                   (mesh (lw-halved-width length (lw-complex-exp-dyadic-depth point start length clearance error)))
                   (cap (lw-complex-exp-uniform-cap (lw-complex-exp-integration-argument-cap point start length)))
                   (slope (lw-complex-l1 point)) (weight (lw-complex-exp-integration-weight point start length))
                   (delta (lw-complex-exp-dyadic-error point start length clearance error))))
           :in-theory
           (e/d (lw-complex-exp-grid-step-budget lw-complex-exp-integration-weight)
                (lw-complex-exp-dyadic-depth-adequate lw-complex-exp-dyadic-error-valid
                 lw-complex-l1-bound lw-complex-exp-uniform-cap-data lw-dyadic-leaf-count-mesh))
           :nonlinearp nil :do-not-induct t)))

(defthm lw-complex-exp-dyadic-integral-grid-rational
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp cutpoint) (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (lw-complexp (lw-complex-exp-dyadic-integral-grid point start length cutpoint clearance error)))
  :hints (("Goal"
           :use (lw-complex-exp-dyadic-error-valid)
           :in-theory (e/d (lw-complex-exp-dyadic-integral-grid) (lw-complex-exp-dyadic-error-valid))
           :do-not-induct t)))

(defthm lw-complex-exp-dyadic-integral-value-rational
  (implies
   (and (lw-complexp point) (rationalp start) (rationalp length) (rationalp cutpoint)
        (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error))
   (lw-complexp (lw-complex-exp-dyadic-integral-value point start length cutpoint clearance error)))
  :hints (("Goal"
           :use ((:instance lw-cei-positive-product (a clearance) (b error)))
           :in-theory (enable lw-complex-exp-dyadic-integral-value) :do-not-induct t)))

(defthm lw-complex-exp-clipped-computed-dyadic-quadrature
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp cutpoint) (<= 0 cutpoint) (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point)) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-clipped-primitive point start (+ start length) cutpoint
                                      (lw-complex-exp-dyadic-error point start length clearance error))
     (lw-complex-exp-dyadic-integral-grid point start length cutpoint clearance error))
    (* 1/2 error)))
  :hints (("Goal"
           :use (lw-complex-exp-dyadic-depth-adequate lw-complex-exp-dyadic-error-valid
                 lw-complex-exp-dyadic-total-budget lw-cei-argument-data
                 (:instance lw-complex-exp-clipped-dyadic-primitive-error
                   (end (+ start length)) (bound (+ start length))
                   (depth (lw-complex-exp-dyadic-depth point start length clearance error))
                   (argument-cap (lw-complex-exp-integration-argument-cap point start length))
                   (error (lw-complex-exp-dyadic-error point start length clearance error)))
                 (:instance lw-complex-disk-enlarge
                   (point (lw-complex-sub
                     (lw-complex-exp-clipped-primitive point start (+ start length) cutpoint
                                                      (lw-complex-exp-dyadic-error point start length clearance error))
                     (lw-complex-exp-dyadic-integral-grid point start length cutpoint clearance error)))
                   (radius
                    (* (lw-dyadic-leaf-count (lw-complex-exp-dyadic-depth point start length clearance error))
                       (lw-complex-exp-grid-step-budget
                        point (lw-halved-width length (lw-complex-exp-dyadic-depth point start length clearance error))
                        (lw-complex-exp-integration-argument-cap point start length)
                        (lw-complex-exp-dyadic-error point start length clearance error))
                       (/ clearance)))
                   (cap (* 1/2 error))))
           :in-theory
           (e/d (lw-complex-exp-dyadic-integral-grid lw-complex-exp-integration-argument-cap)
                (lw-complex-exp-dyadic-depth-adequate lw-complex-exp-dyadic-error-valid
                 lw-complex-exp-dyadic-total-budget lw-complex-exp-clipped-dyadic-primitive-error))
           :nonlinearp nil :do-not-induct t)))

(local (defthm lw-cei-endpoint-radius-budget
         (implies (and (rationalp clearance) (< 0 clearance) (rationalp error) (< 0 error)
                       (rationalp delta) (<= delta (* 1/16 clearance error)))
                  (<= (+ (* 2 (+ (* 1/16 clearance error) delta) (/ clearance)) (* 1/2 error)) error))
         :hints (("Goal"
                  :use ((:instance inverse-of-* (x clearance))
                        (:instance lw-cei-multiply-order
                          (a delta) (b (* 1/16 clearance error)) (factor (* 2 (/ clearance)))))
                  :in-theory (disable inverse-of-*) :nonlinearp nil :do-not-induct t))
         :rule-classes nil))

(defthm lw-complex-exp-clipped-computed-dyadic-endpoint
  (implies
   (and (lw-complexp point) (rationalp start) (<= 0 start) (rationalp length) (<= 0 length)
        (rationalp cutpoint) (<= 0 cutpoint) (rationalp clearance) (< 0 clearance)
        (<= (* clearance clearance) (lw-complex-norm-square point)) (rationalp error) (< 0 error))
   (lw-complex-diskp
    (lw-complex-sub
     (lw-complex-exp-dyadic-integral-value point start length cutpoint clearance error)
     (lw-complex-exp-dyadic-integral-grid point start length cutpoint clearance error))
    error))
  :hints (("Goal"
           :use
           (lw-complex-exp-clipped-computed-dyadic-quadrature
            lw-complex-exp-dyadic-error-valid
            lw-complex-exp-dyadic-integral-grid-rational lw-complex-exp-dyadic-integral-value-rational
            (:instance lw-cei-positive-product (a clearance) (b error))
            (:instance lw-complex-exp-clipped-primitive-rational
              (end (+ start length)) (error (lw-complex-exp-dyadic-error point start length clearance error)))
            (:instance lw-complex-exp-clipped-primitive-cauchy
              (end (+ start length)) (left-error (* 1/16 clearance error))
              (right-error (lw-complex-exp-dyadic-error point start length clearance error)))
            (:instance lw-cei-endpoint-radius-budget
              (delta (lw-complex-exp-dyadic-error point start length clearance error)))
            (:instance lw-complex-difference-triangle
              (left (lw-complex-exp-dyadic-integral-value point start length cutpoint clearance error))
              (middle (lw-complex-exp-clipped-primitive point start (+ start length) cutpoint
                                                       (lw-complex-exp-dyadic-error point start length clearance error)))
              (right (lw-complex-exp-dyadic-integral-grid point start length cutpoint clearance error))
              (radius (* 2 (+ (* 1/16 clearance error)
                              (lw-complex-exp-dyadic-error point start length clearance error)) (/ clearance)))
              (other-radius (* 1/2 error)))
            (:instance lw-complex-disk-enlarge
              (point (lw-complex-sub
                (lw-complex-exp-dyadic-integral-value point start length cutpoint clearance error)
                (lw-complex-exp-dyadic-integral-grid point start length cutpoint clearance error)))
              (radius (+ (* 2 (+ (* 1/16 clearance error)
                                 (lw-complex-exp-dyadic-error point start length clearance error)) (/ clearance))
                         (* 1/2 error)))
              (cap error)))
           :in-theory
           (e/d (lw-complex-exp-dyadic-integral-value)
                (lw-complex-exp-clipped-computed-dyadic-quadrature lw-complex-exp-dyadic-error-valid
                 lw-complex-exp-dyadic-integral-grid-rational lw-complex-exp-dyadic-integral-value-rational
                 lw-complex-exp-clipped-primitive-rational lw-complex-exp-clipped-primitive-cauchy
                 lw-complex-difference-triangle))
           :nonlinearp nil :do-not-induct t)))
