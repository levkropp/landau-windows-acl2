(in-package "ACL2")

(include-book "mellin-cutoff-order")
(include-book "mellin-uniform-mesh")
(include-book "mellin-shift-coefficients")

; A fixed cutoff, mesh and polynomial work across the entire shift disk
; inside the convergence half-plane. The same polynomial recovers the
; selected improper moment at its center.

(local (in-theory
        (disable lw-complexp lw-complex-add lw-complex-sub lw-complex-mul lw-complex-scale
                 lw-complex-diskp lw-diskp lw-complex-polynomial lw-halved-width
                 lw-mellin-integral lw-mellin-integral-cutoff lw-mellin-bounded-integral
                 lw-mellin-cutoff-prefix lw-mellin-cutoff-tail lw-mellin-cutoff-mesh lw-mellin-cutoff-precision
                 lw-mellin-shift-mesh-depth lw-mellin-uniform-depth lw-mellin-uniform-spatial-slope
                 lw-mellin-spatial-slope lw-mellin-spatial-error-factor lw-mellin-signal-spatial-slope
                 lw-mellin-signal-spatial-cap lw-kernel-spatial-cap lw-kernel-spatial-slope lw-exp-lipschitz-cap
                 lw-log-signal-bounds lw-mellin-sample lw-mellin-sample-kernel-form lw-mellin-cell-mass
                 lw-mellin-sum lw-mellin-sum-raw lw-mellin-sum-error lw-mellin-dyadic-cells
                 lw-mellin-shift-polynomial lw-mellin-shift-polynomial-degree lw-mellin-shift-polynomial-nodes
                 lw-exp-mixture-coefficients lw-exp-mixture-coefficient
                 lw-cauchy-boundary-check lw-cauchy-orbit-rotation lw-cauchy-coefficient-count
                 lw-complex-disk-enlarge lw-disk-enlarge)))

(local (defthm lw-mimp-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))
(local (defthm lw-mimp-left-distribute
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))
(local (defthm lw-mimp-zero-times (equal (* 0 a) 0)))
(local (defthm lw-mimp-components
         (implies (lw-complexp point) (and (rationalp (car point)) (rationalp (cdr point))))
         :hints (("Goal" :in-theory (enable lw-complexp)))))
(local (defthm lw-mimp-half-quarter
         (implies (rationalp value) (equal (* 1/2 1/4 value) (* 1/8 value)))
         :hints (("Goal" :use ((:instance associativity-of-* (x 1/2) (y 1/4) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mimp-left-commutes)))))
(local (defthm lw-mimp-quarter-eighth
         (implies (rationalp value) (equal (* 1/4 1/8 value) (* 1/32 value)))
         :hints (("Goal" :use ((:instance associativity-of-* (x 1/4) (y 1/8) (z value)))
                         :in-theory (disable associativity-of-* commutativity-of-* lw-mimp-left-commutes)))))

(defun lw-mellin-common-cutoff (sigma target radius error)
  (max (lw-mellin-integral-cutoff (- sigma radius) 0 (* 1/64 error))
       (lw-mellin-integral-cutoff (- sigma radius) target (* 1/64 error))))

(defthm lw-mellin-common-cutoff-data
  (implies (and (rationalp sigma) (rationalp radius) (<= 0 radius) (< 2 (- sigma radius))
                (natp target) (rationalp error) (< 0 error))
           (and (rationalp (lw-mellin-common-cutoff sigma target radius error)) (< 0 (lw-mellin-common-cutoff sigma target radius error))
                (<=
                  (lw-mellin-integral-cutoff (- sigma radius) 0 (* 1/64 error))
                  (lw-mellin-common-cutoff sigma target radius error))
                (<=
                  (lw-mellin-integral-cutoff (- sigma radius) target (* 1/64 error))
                  (lw-mellin-common-cutoff sigma target radius error))))
  :hints (("Goal" :use (
    (:instance lw-mellin-integral-cutoff-valid (sigma (- sigma radius)) (index 0) (error (* 1/64 error)))
    (:instance lw-mellin-integral-cutoff-valid (sigma (- sigma radius)) (index target) (error (* 1/64 error))))
    :in-theory (disable lw-mellin-integral-cutoff-valid))))

(local (in-theory (disable lw-mellin-common-cutoff)))

(defthm lw-mellin-common-cutoff-dominates
  (implies (and (rationalp sigma) (rationalp height) (natp target)
                (lw-complex-diskp shift radius) (< 2 (- sigma radius)) (rationalp error) (< 0 error))
           (and (rationalp (- sigma (car shift))) (< 2 (- sigma (car shift)))
                (rationalp (- height (cdr shift)))
                (<=
                  (lw-mellin-integral-cutoff (- sigma (car shift)) 0 (* 1/64 error))
                  (lw-mellin-common-cutoff sigma target radius error))
                (<=
                  (lw-mellin-integral-cutoff (- sigma (car shift)) target (* 1/64 error))
                  (lw-mellin-common-cutoff sigma target radius error))))
  :hints (("Goal" :use (lw-mellin-common-cutoff-data
    (:instance lw-complex-disk-coordinates (point shift))
    (:instance lw-mellin-integral-cutoff-antitone-abscissa
      (left (- sigma radius))
      (right (- sigma (car shift)))
      (index 0)
      (error (* 1/64 error)))
    (:instance lw-mellin-integral-cutoff-antitone-abscissa
      (left (- sigma radius))
      (right (- sigma (car shift)))
      (index target)
      (error (* 1/64 error))))
    :in-theory (disable lw-mellin-common-cutoff-data lw-complex-disk-coordinates
                        lw-mellin-integral-cutoff-antitone-abscissa)
    :cases ((<= 0 (car shift))))))

(defun lw-mellin-common-cells (sigma height target radius error)
  (let ((cutoff (lw-mellin-common-cutoff sigma target radius error)))
    (lw-mellin-dyadic-cells 0 cutoff (lw-mellin-shift-mesh-depth cutoff sigma height radius (* 1/4 error)))))

(defthm lw-mellin-common-cells-valid
  (implies (and (rationalp sigma) (rationalp height) (natp target)
                (rationalp radius) (<= 0 radius) (< 2 (- sigma radius)) (rationalp error) (< 0 error))
           (lw-mellin-cellsp (lw-mellin-common-cells sigma height target radius error)))
  :hints (("Goal" :use (lw-mellin-common-cutoff-data
    (:instance lw-mellin-shift-mesh-data
      (cap (lw-mellin-common-cutoff sigma target radius error))
      (shift (cons 0 0))
      (error (* 1/4 error)))
    (:instance lw-mellin-dyadic-cells-valid
      (start 0)
      (end (lw-mellin-common-cutoff sigma target radius error))
      (depth
        (lw-mellin-shift-mesh-depth
          (lw-mellin-common-cutoff sigma target radius error)
          sigma
          height
          radius
          (* 1/4 error)))))
    :in-theory (disable lw-mellin-common-cutoff-data lw-mellin-shift-mesh-data))))

(local (in-theory (disable lw-mellin-common-cells)))

(defun lw-mellin-improper-polynomial (sigma height target radius error)
  (lw-mellin-shift-polynomial (lw-mellin-common-cells sigma height target radius error)
                              sigma height target radius (* 1/4 error)))
(defun lw-mellin-improper-polynomial-degree (sigma height target radius error)
  (lw-mellin-shift-polynomial-degree (lw-mellin-common-cells sigma height target radius error)
                                     sigma height target radius (* 1/4 error)))

(defthm lw-mellin-improper-polynomial-valid
  (implies (and (rationalp sigma) (rationalp height) (natp target)
                (rationalp radius) (<= 0 radius) (< 2 (- sigma radius)) (rationalp error) (< 0 error))
           (and (lw-complex-coefficientsp (lw-mellin-improper-polynomial sigma height target radius error))
                (equal (len (lw-mellin-improper-polynomial sigma height target radius error))
                       (+ 1 (lw-mellin-improper-polynomial-degree sigma height target radius error)))
                (< target (len (lw-mellin-improper-polynomial sigma height target radius error)))
                (natp (lw-mellin-improper-polynomial-degree sigma height target radius error))
                (<= target (lw-mellin-improper-polynomial-degree sigma height target radius error))))
  :hints (("Goal" :use (
    (:instance lw-mellin-shift-polynomial-valid
      (cells (lw-mellin-common-cells sigma height target radius error))
      (error (* 1/4 error)))
    (:instance lw-mellin-shift-polynomial-degree-data
      (cells (lw-mellin-common-cells sigma height target radius error))
      (error (* 1/4 error)))
    (:instance lw-mellin-shift-polynomial-coefficient
      (cells (lw-mellin-common-cells sigma height target radius error))
      (error (* 1/4 error))))
    :in-theory (disable lw-mellin-shift-polynomial-valid lw-mellin-shift-polynomial-degree-data
                        lw-mellin-shift-polynomial-coefficient))))

(local (in-theory (disable lw-mellin-improper-polynomial lw-mellin-improper-polynomial-degree)))


(defthm lw-mellin-common-quadrature-comparison
  (implies (and (rationalp sigma) (rationalp height) (natp target)
                (lw-complex-diskp shift radius) (< 2 (- sigma radius))
                (or (equal index 0) (equal index target)) (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-sum
                 (lw-mellin-common-cells sigma height target radius error)
                 (- sigma (car shift))
                 (- height (cdr shift))
                 index
                 (* 1/32 error))
               (lw-mellin-integral (- sigma (car shift)) (- height (cdr shift)) index (* 1/64 error)))
             (* 17/64 error)))
  :hints (("Goal" :use (
    lw-mellin-common-cutoff-data lw-mellin-common-cutoff-dominates lw-mellin-common-cells-valid
    (:instance lw-mellin-shift-cell-bounded-comparison
      (cap (lw-mellin-common-cutoff sigma target radius error))
      (grid-error (* 1/32 error))
      (mesh-error (* 1/4 error))
      (bounded-error (* 1/64 error)))
    (:instance lw-mellin-bounded-above-cutoff-comparison
      (sigma (- sigma (car shift)))
      (height (- height (cdr shift)))
      (cap (lw-mellin-common-cutoff sigma target radius error))
      (integral-error (* 1/64 error))
      (bounded-error (* 1/64 error)))
    (:instance lw-complex-difference-triangle
      (left
        (lw-mellin-sum
          (lw-mellin-common-cells sigma height target radius error)
          (- sigma (car shift))
          (- height (cdr shift))
          index
          (* 1/32 error)))
      (middle
        (lw-mellin-bounded-integral
          (lw-mellin-common-cutoff sigma target radius error)
          (- sigma (car shift))
          (- height (cdr shift))
          index
          (* 1/64 error)))
      (right (lw-mellin-integral (- sigma (car shift)) (- height (cdr shift)) index (* 1/64 error)))
      (radius (+ (* 1/32 error) (* 1/4 (* 1/4 error)) (* 1/64 error)))
      (other-radius (* 5 (+ (* 1/64 error) (* 1/64 error)))))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-sum
            (lw-mellin-common-cells sigma height target radius error)
            (- sigma (car shift))
            (- height (cdr shift))
            index
            (* 1/32 error))
          (lw-mellin-integral (- sigma (car shift)) (- height (cdr shift)) index (* 1/64 error))))
      (radius
        (+ (+ (* 1/32 error) (* 1/4 (* 1/4 error)) (* 1/64 error)) (* 5 (+ (* 1/64 error) (* 1/64 error)))))
      (cap (* 17/64 error))))
    :in-theory (e/d (lw-mellin-common-cells)
                    (lw-mellin-common-cutoff-data lw-mellin-common-cutoff-dominates
                     lw-mellin-common-cells-valid lw-mellin-shift-cell-bounded-comparison
                     lw-mellin-bounded-above-cutoff-comparison lw-complex-difference-triangle))
    :cases ((equal index 0)))))

(defthm lw-mellin-computed-uniform-improper-polynomial
  (implies (and (rationalp sigma) (rationalp height) (natp target)
                (lw-complex-diskp shift radius) (< 2 (- sigma radius)) (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-complex-polynomial
                 (lw-mellin-improper-polynomial sigma height target radius error)
                 shift
                 0)
               (lw-mellin-integral (- sigma (car shift)) (- height (cdr shift)) 0 (* 1/64 error)))
             error))
  :hints (("Goal" :use (
    lw-mellin-improper-polynomial-valid lw-mellin-common-cutoff-dominates lw-mellin-common-cells-valid
    (:instance lw-mellin-computed-uniform-shift-polynomial
      (cells (lw-mellin-common-cells sigma height target radius error))
      (error (* 1/4 error)))
    (:instance lw-mellin-common-quadrature-comparison (index 0))
    (:instance lw-complex-difference-triangle
      (left (lw-complex-polynomial (lw-mellin-improper-polynomial sigma height target radius error) shift 0))
      (middle
        (lw-mellin-sum
          (lw-mellin-common-cells sigma height target radius error)
          (- sigma (car shift))
          (- height (cdr shift))
          0
          (* 1/32 error)))
      (right (lw-mellin-integral (- sigma (car shift)) (- height (cdr shift)) 0 (* 1/64 error)))
      (radius (* 1/4 error))
      (other-radius (* 17/64 error)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-complex-polynomial (lw-mellin-improper-polynomial sigma height target radius error) shift 0)
          (lw-mellin-integral (- sigma (car shift)) (- height (cdr shift)) 0 (* 1/64 error))))
      (radius (+ (* 1/4 error) (* 17/64 error)))
      (cap error)))
    :in-theory (e/d (lw-mellin-improper-polynomial)
                    (lw-mellin-improper-polynomial-valid lw-mellin-common-cutoff-dominates
                     lw-mellin-common-cells-valid lw-mellin-computed-uniform-shift-polynomial
                     lw-mellin-common-quadrature-comparison lw-complex-difference-triangle)))))

(defthm lw-mellin-improper-polynomial-moment-comparison
  (implies (and (rationalp sigma) (rationalp height) (natp target)
                (rationalp radius) (<= 0 radius) (< 2 (- sigma radius)) (rationalp error) (< 0 error))
           (lw-complex-diskp
             (lw-complex-sub
               (lw-mellin-integral sigma height target (* 1/64 error))
               (nth target (lw-mellin-improper-polynomial sigma height target radius error)))
             (* 1/2 error)))
  :hints (("Goal" :use (
    lw-mellin-common-cells-valid
    (:instance lw-mellin-common-quadrature-comparison (shift (cons 0 0)) (index target))
    (:instance lw-mellin-shift-polynomial-moment-comparison
      (cells (lw-mellin-common-cells sigma height target radius error))
      (error (* 1/4 error)))
    (:instance lw-complex-difference-symmetric
      (left
        (lw-mellin-sum
          (lw-mellin-common-cells sigma height target radius error)
          sigma
          height
          target
          (* 1/32 error)))
      (right (lw-mellin-integral sigma height target (* 1/64 error)))
      (radius (* 17/64 error)))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-integral sigma height target (* 1/64 error)))
      (middle
        (lw-mellin-sum
          (lw-mellin-common-cells sigma height target radius error)
          sigma
          height
          target
          (* 1/32 error)))
      (right (nth target (lw-mellin-improper-polynomial sigma height target radius error)))
      (radius (* 17/64 error))
      (other-radius (* 1/8 error)))
    (:instance lw-complex-disk-enlarge
      (point
        (lw-complex-sub
          (lw-mellin-integral sigma height target (* 1/64 error))
          (nth target (lw-mellin-improper-polynomial sigma height target radius error))))
      (radius (+ (* 17/64 error) (* 1/8 error)))
      (cap (* 1/2 error))))
    :in-theory (e/d (lw-mellin-improper-polynomial)
                    (lw-mellin-common-cells-valid lw-mellin-common-quadrature-comparison
                     lw-mellin-shift-polynomial-moment-comparison lw-complex-difference-triangle)))))

(defthm lw-mellin-improper-polynomial-cauchy-bound
  (implies (and (rationalp sigma) (rationalp height) (natp target)
                (rationalp radius) (<= 0 radius) (< 2 (- sigma radius))
                (rationalp error) (< 0 error) (rationalp cap) (<= 0 cap)
                (lw-cauchy-boundary-check (lw-mellin-improper-polynomial sigma height target radius error) (lw-cauchy-orbit-rotation (lw-mellin-improper-polynomial-degree sigma height target radius error)) 0
                  (lw-cauchy-coefficient-count (lw-mellin-improper-polynomial sigma height target radius error) (lw-mellin-improper-polynomial-degree sigma height target radius error) (* 1/2 error)) cap))
           (lw-complex-diskp (lw-mellin-integral sigma height target (* 1/64 error)) (+ cap error)))
  :hints (("Goal" :use (
    lw-mellin-improper-polynomial-valid lw-mellin-improper-polynomial-moment-comparison
    (:instance lw-cauchy-finite-coefficient-bound
      (coefficients (lw-mellin-improper-polynomial sigma height target radius error))
      (degree (lw-mellin-improper-polynomial-degree sigma height target radius error))
      (error (* 1/2 error)))
    (:instance lw-complex-difference-triangle
      (left (lw-mellin-integral sigma height target (* 1/64 error)))
      (middle (nth target (lw-mellin-improper-polynomial sigma height target radius error)))
      (right (cons 0 0))
      (radius (* 1/2 error))
      (other-radius (+ cap (* 1/2 error))))
    (:instance lw-complex-disk-enlarge
      (point (lw-mellin-integral sigma height target (* 1/64 error)))
      (radius (+ (* 1/2 error) cap (* 1/2 error)))
      (cap (+ cap error))))
    :in-theory (disable lw-mellin-improper-polynomial-valid lw-mellin-improper-polynomial-moment-comparison
                        lw-cauchy-finite-coefficient-bound lw-complex-difference-triangle))))

