(in-package "ACL2")

(include-book "euler-circle-pole-split")
(include-book "circle-exterior-coefficient-model")

; Use the same polynomial and factor roots as on the outer checked circle.
; The separate anchor, at the expansion center, provides an inner disk.
(defun lw-euler-circle-center-radius (center radius anchor-error)
  (min radius (lw-euler-neighborhood-radius (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error)))

(defun lw-euler-circle-center-margin-size (center anchor-error)
  (* 1/16 (lw-euler-value-clearance-size (car center) (cdr center) anchor-error)))

(defun lw-euler-circle-center-modelp (center radius plus-arcs minus-arcs target error epsilon anchor-error)
  (and (lw-euler-circle-coverp center radius plus-arcs minus-arcs)
       (lw-euler-value-clearance-check (car center) (cdr center) anchor-error)
       (natp target)
       (rationalp error) (< 0 error) (<= error 1)
       (<= (* (lw-euler-circle-outer-gap center radius) error) anchor-error)
       (rationalp epsilon) (< 0 epsilon)
       (<= epsilon (lw-euler-circle-center-margin-size center anchor-error))))

(local (in-theory
        (disable lw-euler-circle-center-modelp lw-euler-circle-center-radius
                 lw-euler-circle-center-margin-size)))

(local (defthm lw-eccc-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-eccc-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-eccc-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-eccc-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-eccc-times-negative (a b) (b a)))
                 :in-theory (disable lw-eccc-times-negative)))))

(local (defthm lw-eccc-zero-times (equal (* 0 a) 0)))

(local (defthm lw-eccc-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-eccc-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-eccc-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-eccc-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-eccc-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-eccc-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(defthm lw-euler-circle-center-model-data
  (implies (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error)
           (and (rationalp radius) (< 0 radius)
                (rationalp (lw-euler-circle-center-radius center radius anchor-error)) (< 0 (lw-euler-circle-center-radius center radius anchor-error))
                (<= (lw-euler-circle-center-radius center radius anchor-error) radius) (<= (lw-euler-circle-center-radius center radius anchor-error) (lw-euler-neighborhood-radius (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error))
                (rationalp (lw-euler-circle-outer-radius center radius)) (< (lw-euler-circle-center-radius center radius anchor-error) (lw-euler-circle-outer-radius center radius))
                (rationalp (lw-euler-circle-center-margin-size center anchor-error)) (< 0 (lw-euler-circle-center-margin-size center anchor-error))
                (lw-complex-coefficientsp (lw-euler-circle-global-polynomial center radius target error))
                (lw-ray-pointsp (lw-euler-circle-factor-roots center radius target error epsilon))))
  :hints (("Goal"
           :use (lw-euler-circle-outer-data lw-euler-circle-global-polynomials-valid
                 (:instance lw-euler-neighborhood-data (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                 (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-center-radius lw-euler-circle-center-margin-size lw-euler-circle-factor-roots min lw-eccc-left-commutes lw-eccc-left-distributes lw-eccc-fold-constants lw-eccc-times-negative lw-eccc-negative-times lw-eccc-zero-times lw-eccc-minus-one lw-eccc-double-negative lw-eccc-add-cancel lw-eccc-double lw-eccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(local
 (defthm lw-eccc-clearance-gap
   (implies (and (rationalp size) (< 0 size))
            (< (* 1/8 size 1/8 size) (* 1/16 size size)))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) consp lw-eccc-left-commutes lw-eccc-left-distributes lw-eccc-fold-constants lw-eccc-times-negative lw-eccc-negative-times lw-eccc-zero-times lw-eccc-minus-one lw-eccc-double-negative lw-eccc-add-cancel lw-eccc-double lw-eccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)) :nonlinearp t))
   :rule-classes nil))

(defthm lw-euler-circle-center-polynomial-margin
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (lw-complex-diskp point (lw-euler-circle-center-radius center radius anchor-error)))
           (not (lw-complex-diskp (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0) (* 2 (lw-euler-circle-center-margin-size center anchor-error)))))
  :hints (("Goal"
           :use (lw-euler-circle-center-model-data lw-euler-circle-outer-data
                 (:instance lw-euler-neighborhood-data (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                 (:instance lw-complex-disk-enlarge (radius (lw-euler-circle-center-radius center radius anchor-error)) (cap (lw-euler-neighborhood-radius (car center) (cdr center) (lw-euler-circle-outer-radius center radius) anchor-error)))
                 (:instance lw-complex-euler-neighborhood-polynomial-clearance
                   (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius)) (error (* (lw-euler-circle-outer-gap center radius) error)))
                 (:instance lw-eccc-clearance-gap (size (lw-euler-value-clearance-size (car center) (cdr center) anchor-error)))
                 (:instance lw-complex-disk-norm-square (point (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0)) (radius (* 2 (lw-euler-circle-center-margin-size center anchor-error)))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-global-polynomial lw-euler-circle-center-margin-size lw-eccc-left-commutes lw-eccc-left-distributes lw-eccc-fold-constants lw-eccc-times-negative lw-eccc-negative-times lw-eccc-zero-times lw-eccc-minus-one lw-eccc-double-negative lw-eccc-add-cancel lw-eccc-double lw-eccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :nonlinearp t :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-center-factor-margin
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (lw-complex-diskp point (lw-euler-circle-center-radius center radius anchor-error)))
           (and (lw-complexp (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-circle-global-polynomial center radius target error) (lw-euler-circle-outer-radius center radius) epsilon) point 0))
                (not (equal (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-circle-global-polynomial center radius target error) (lw-euler-circle-outer-radius center radius) epsilon) point 0) (cons 0 0)))
                (<= (* (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-center-margin-size center anchor-error)) (lw-complex-norm-square (lw-complex-polynomial (lw-polynomial-disk-factor-polynomial (lw-euler-circle-global-polynomial center radius target error) (lw-euler-circle-outer-radius center radius) epsilon) point 0)))))
  :hints (("Goal"
           :use (lw-euler-circle-center-model-data lw-euler-circle-center-polynomial-margin
                 (:instance lw-polynomial-disk-factor-margin (coefficients (lw-euler-circle-global-polynomial center radius target error))
                   (outer-radius (lw-euler-circle-outer-radius center radius)) (inner-radius (lw-euler-circle-center-radius center radius anchor-error)) (center point) (clearance (lw-euler-circle-center-margin-size center anchor-error))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-eccc-left-commutes lw-eccc-left-distributes lw-eccc-fold-constants lw-eccc-times-negative lw-eccc-negative-times lw-eccc-zero-times lw-eccc-minus-one lw-eccc-double-negative lw-eccc-add-cancel lw-eccc-double lw-eccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

; A finite witness selects any root in the closed inner disk.
(local
 (defun lw-eccc-root-in-disk (roots radius)
   (if (endp roots) nil
     (if (lw-complex-diskp (car roots) radius)
         (car roots)
       (lw-eccc-root-in-disk (cdr roots) radius)))))

(local
 (defthm lw-eccc-root-witness
   (implies (and (lw-ray-pointsp roots) (rationalp radius) (< 0 radius))
            (if (lw-eccc-root-in-disk roots radius)
                (and (member-equal (lw-eccc-root-in-disk roots radius) roots)
                     (lw-complex-diskp (lw-eccc-root-in-disk roots radius) radius))
              (lw-circle-exterior-rootsp roots radius)))
   :hints (("Goal" :induct (lw-eccc-root-in-disk roots radius)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-eccc-root-in-disk lw-circle-exterior-rootsp lw-ray-pointsp lw-complexp member-equal endp lw-eccc-left-commutes lw-eccc-left-distributes lw-eccc-fold-constants lw-eccc-times-negative lw-eccc-negative-times lw-eccc-zero-times lw-eccc-minus-one lw-eccc-double-negative lw-eccc-add-cancel lw-eccc-double lw-eccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-disk-norm-square (point (car roots))))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-euler-circle-center-roots-exterior
  (implies (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error)
           (lw-circle-exterior-rootsp (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error)))
  :hints (("Goal"
           :use (lw-euler-circle-center-model-data
                 (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius)))
                 (:instance lw-eccc-root-witness (roots (lw-euler-circle-factor-roots center radius target error epsilon)) (radius (lw-euler-circle-center-radius center radius anchor-error)))
                 (:instance lw-euler-circle-center-factor-margin (point (lw-eccc-root-in-disk (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error))))
                 (:instance lw-polynomial-disk-factor-evaluation
                   (coefficients (lw-euler-circle-global-polynomial center radius target error)) (outer-radius (lw-euler-circle-outer-radius center radius)) (point (lw-eccc-root-in-disk (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error))))
                 (:instance lw-complex-disk-data (point (lw-eccc-root-in-disk (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error))) (radius (lw-euler-circle-center-radius center radius anchor-error)))
                 (:instance lw-polynomial-factor-member-zero (roots (lw-euler-circle-factor-roots center radius target error epsilon))
                   (root (lw-eccc-root-in-disk (lw-euler-circle-factor-roots center radius target error epsilon) (lw-euler-circle-center-radius center radius anchor-error)))
                   (leading (lw-polynomial-leading (lw-polynomial-trim (lw-euler-circle-global-polynomial center radius target error))))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-factor-roots lw-eccc-left-commutes lw-eccc-left-distributes lw-eccc-fold-constants lw-eccc-times-negative lw-eccc-negative-times lw-eccc-zero-times lw-eccc-minus-one lw-eccc-double-negative lw-eccc-add-cancel lw-eccc-double lw-eccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defun lw-euler-circle-center-quotient (center radius point target error)
  (lw-complex-quotient (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial center radius target error) point) (lw-complex-polynomial (lw-euler-circle-global-polynomial center radius target error) point 0)))

(defthm lw-euler-circle-center-derivative-bound
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (lw-complex-diskp point (lw-euler-circle-center-radius center radius anchor-error)))
           (lw-complex-diskp (lw-complex-polynomial-derivative (lw-euler-circle-global-polynomial center radius target error) point) (lw-euler-circle-global-derivative-cap center radius)))
  :hints (("Goal"
           :use (lw-euler-circle-center-model-data lw-euler-circle-outer-data
                 lw-euler-circle-global-derivative-identity
                 (:instance lw-complex-disk-enlarge (radius (lw-euler-circle-center-radius center radius anchor-error)) (cap radius))
                 (:instance lw-complex-disk-data (radius (lw-euler-circle-center-radius center radius anchor-error)))
                 (:instance lw-polynomial-derivative-coefficients-evaluation (coefficients (lw-euler-circle-global-polynomial center radius target error)))
                 (:instance lw-complex-euler-uniform-derivative-polynomial-cap
                   (rate (car center)) (height (cdr center)) (outer-radius (lw-euler-circle-outer-radius center radius))
                   (inner-radius radius) (center point)))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-global-derivative lw-euler-circle-global-derivative-cap lw-eccc-left-commutes lw-eccc-left-distributes lw-eccc-fold-constants lw-eccc-times-negative lw-eccc-negative-times lw-eccc-zero-times lw-eccc-minus-one lw-eccc-double-negative lw-eccc-add-cancel lw-eccc-double lw-eccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)

(defthm lw-euler-circle-center-factor-quotient-error
  (implies (and (lw-euler-circle-center-modelp center radius plus-arcs minus-arcs target error epsilon anchor-error) (lw-complex-diskp point (lw-euler-circle-center-radius center radius anchor-error)))
           (lw-complex-diskp
            (lw-complex-sub (lw-polynomial-factor-log-sum (lw-euler-circle-factor-roots center radius target error epsilon) point) (lw-euler-circle-center-quotient center radius point target error))
            (* (lw-disk-factor-quotient-cost (- (lw-euler-circle-outer-radius center radius) (lw-euler-circle-center-radius center radius anchor-error)) (lw-euler-circle-center-margin-size center anchor-error) (lw-euler-circle-global-derivative-cap center radius)) epsilon)))
  :hints (("Goal"
           :use (lw-euler-circle-center-model-data lw-euler-circle-center-polynomial-margin
                 lw-euler-circle-center-derivative-bound lw-euler-circle-global-derivative-cap-data
                 (:instance lw-polynomial-disk-factor-sum-error (coefficients (lw-euler-circle-global-polynomial center radius target error))
                   (outer-radius (lw-euler-circle-outer-radius center radius)) (inner-radius (lw-euler-circle-center-radius center radius anchor-error)) (center point)
                   (clearance (lw-euler-circle-center-margin-size center anchor-error)) (numerator-cap (lw-euler-circle-global-derivative-cap center radius))))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-euler-circle-center-modelp lw-euler-circle-factor-roots lw-euler-circle-center-quotient lw-eccc-left-commutes lw-eccc-left-distributes lw-eccc-fold-constants lw-eccc-times-negative lw-eccc-negative-times lw-eccc-zero-times lw-eccc-minus-one lw-eccc-double-negative lw-eccc-add-cancel lw-eccc-double lw-eccc-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
