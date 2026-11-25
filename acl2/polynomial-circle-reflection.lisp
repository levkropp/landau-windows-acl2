(in-package "ACL2")

(include-book "polynomial-leading")
(include-book "polynomial-divided-difference")

; Pad and reverse the conjugated coefficients in degrees zero through degree.
; On the unit circle this is the ordinary polynomial w^degree * conjugate(P(w)).
(defun lw-polynomial-circle-reflection (coefficients degree)
  (cond ((endp coefficients)
         (lw-polynomial-monomial (cons 0 0) degree))
        ((zp degree)
         (list (lw-complex-conjugate (car coefficients))))
        (t
         (append (lw-polynomial-circle-reflection (cdr coefficients) (- degree 1))
                 (list (lw-complex-conjugate (car coefficients)))))))

(local (defthm lw-pcr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-pcr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-pcr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-pcr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-pcr-times-negative (a b) (b a)))
                 :in-theory (disable lw-pcr-times-negative)))))

(local (defthm lw-pcr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-pcr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-pcr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-pcr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-pcr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-pcr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-pcr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))


(local
 (defthm lw-pcr-length-natural
   (natp (len coefficients))
   :rule-classes (:rewrite :type-prescription)))

(local
 (defthm lw-pcr-append-valid
   (implies (and (lw-complex-coefficientsp left) (lw-complex-coefficientsp right))
            (and (lw-complex-coefficientsp (append left right))
                 (equal (len (append left right)) (+ (len left) (len right)))))
   :hints (("Goal" :induct (append left right)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-coefficientsp append len endp lw-pcr-length-natural lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(defthm lw-polynomial-circle-reflection-data
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree)))
           (and (lw-complex-coefficientsp (lw-polynomial-circle-reflection coefficients degree))
                (equal (len (lw-polynomial-circle-reflection coefficients degree)) (+ 1 degree))))
  :hints (("Goal" :induct (lw-polynomial-circle-reflection coefficients degree)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-circle-reflection lw-complex-coefficientsp lw-polynomial-monomial-valid lw-pcr-append-valid lw-complex-conjugate-rational len endp lw-pcr-length-natural lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

(local
 (defthm lw-pcr-empty
   (equal (lw-complex-polynomial nil point offset) (cons 0 0))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-polynomial endp lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-pcr-single
   (implies (and (lw-complexp coefficient) (lw-complexp point) (natp offset))
            (equal (lw-complex-polynomial (list coefficient) point offset)
                   (lw-complex-mul coefficient (lw-complex-power point offset))))
   :hints (("Goal" :expand ((lw-complex-polynomial (list coefficient) point offset))
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) endp lw-complex-add-zero lw-complex-power-rational lw-complex-ring-rational lw-pcr-empty lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-pcr-power-zero
   (equal (lw-complex-power point 0) (cons 1 0))
   :hints (("Goal" :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-complex-power lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-pcr-power-one
   (implies (lw-complexp point) (equal (lw-complex-power point 1) point))
   :hints (("Goal" :expand ((lw-complex-power point 1))
                   :in-theory (union-theories
 '(lw-pcr-power-zero lw-complex-mul-one lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))))))

(local
 (defthm lw-pcr-reflection-step
   (implies (and (lw-complexp a) (lw-complexp b) (lw-complexp point)
                 (equal (lw-complex-norm-square point) 1) (posp degree))
            (equal (lw-complex-mul (lw-complex-power point degree)
                                  (lw-complex-conjugate (lw-complex-add a (lw-complex-mul point b))))
                   (lw-complex-add
                    (lw-complex-mul (lw-complex-power point (- degree 1)) (lw-complex-conjugate b))
                    (lw-complex-mul (lw-complex-conjugate a) (lw-complex-power point degree)))))
   :hints (("Goal"
            :use ((:instance lw-complex-power-correlation-positive (offset (- degree 1)) (index 1))
                  (:instance lw-complex-mul-left-commutes (a (lw-complex-power point degree))
                    (b (lw-complex-conjugate b)) (c (lw-complex-conjugate point))))
            :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-pcr-power-one lw-complex-conjugate-product lw-complex-conjugate-add lw-complex-mul-distribute lw-complex-mul-associative lw-complex-mul-commutative lw-complex-add-commutative lw-complex-power-rational lw-complex-conjugate-rational lw-complex-ring-rational lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
            :do-not-induct t))))

(local
 (defthm lw-pcr-length-zero
   (equal (equal (len coefficients) 0)
          (not (consp coefficients)))))

(defthm lw-polynomial-circle-reflection-evaluation
  (implies (and (lw-complex-coefficientsp coefficients) (natp degree)
                (<= (len coefficients) (+ 1 degree))
                (lw-complexp point) (equal (lw-complex-norm-square point) 1))
           (equal (lw-complex-polynomial (lw-polynomial-circle-reflection coefficients degree) point 0)
                  (lw-complex-mul (lw-complex-power point degree) (lw-complex-conjugate (lw-complex-polynomial coefficients point 0)))))
  :hints (("Goal" :induct (lw-polynomial-circle-reflection coefficients degree)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-circle-reflection lw-polynomial-circle-reflection-data lw-complex-coefficientsp lw-polynomial-monomial-evaluation lw-complex-polynomial-append lw-complex-polynomial-horner lw-pcr-reflection-step lw-pcr-single lw-pcr-empty lw-pcr-power-zero lw-complex-mul-zero lw-complex-mul-one lw-complex-add-zero lw-complex-polynomial-rational lw-complex-power-rational lw-complex-conjugate-rational lw-complex-ring-rational (:executable-counterpart lw-complex-conjugate) endp len lw-pcr-length-natural lw-pcr-length-zero lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

; Prefix zeros to represent multiplication by the corresponding monomial.
(defun lw-polynomial-power-shift (coefficients shift)
  (if (zp shift) coefficients
    (cons (cons 0 0)
          (lw-polynomial-power-shift coefficients (- shift 1)))))

(defthm lw-polynomial-power-shift-valid
  (implies (and (lw-complex-coefficientsp coefficients) (natp shift))
           (lw-complex-coefficientsp (lw-polynomial-power-shift coefficients shift)))
  :hints (("Goal" :induct (lw-polynomial-power-shift coefficients shift)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-polynomial-power-shift lw-complex-coefficientsp lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory)))))

(local
 (defun lw-pcr-shift-induct (shift offset)
   (if (zp shift) offset
     (lw-pcr-shift-induct (- shift 1) (+ 1 offset)))))

(local
 (defthm lw-pcr-shift-evaluation-offset
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point)
                 (natp shift) (natp offset))
            (equal (lw-complex-polynomial (lw-polynomial-power-shift coefficients shift) point offset)
                   (lw-complex-polynomial coefficients point (+ shift offset))))
   :hints (("Goal" :induct (lw-pcr-shift-induct shift offset)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:induction lw-pcr-shift-induct) lw-polynomial-power-shift lw-complex-polynomial lw-complex-polynomial-rational lw-polynomial-power-shift-valid lw-complex-power-rational lw-complex-mul-zero lw-complex-add-zero endp lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))))

(defthm lw-polynomial-power-shift-coefficient
  (implies (and (lw-complex-coefficientsp coefficients) (natp shift)
                (natp target) (natp offset))
           (equal (lw-complex-coefficient-at (lw-polynomial-power-shift coefficients shift) target offset)
                  (lw-complex-coefficient-at coefficients target (+ shift offset))))
  :hints (("Goal" :induct (lw-pcr-shift-induct shift offset)
                  :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:induction lw-pcr-shift-induct) lw-polynomial-power-shift lw-complex-coefficient-at lw-complex-coefficient-at-rational lw-polynomial-power-shift-valid lw-complex-add-zero endp lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                  :do-not '(generalize fertilize))))

(local
 (defthm lw-pcr-offset-power
   (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point)
                 (natp shift))
            (equal (lw-complex-polynomial coefficients point shift)
                   (lw-complex-mul (lw-complex-power point shift)
                                   (lw-complex-polynomial coefficients point 0))))
   :hints (("Goal" :induct (lw-polynomial-power-shift coefficients shift)
                   :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) (:induction lw-polynomial-power-shift) lw-pcr-power-zero lw-complex-mul-one lw-complex-polynomial-rational lw-complex-power-rational lw-complex-ring-rational lw-complex-mul-associative lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-complex-polynomial-offset-step (offset (- shift 1))))
                  :expand ((lw-complex-power point shift))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-polynomial-power-shift-evaluation
  (implies (and (lw-complex-coefficientsp coefficients) (lw-complexp point) (natp shift))
           (equal (lw-complex-polynomial (lw-polynomial-power-shift coefficients shift) point 0)
                  (lw-complex-mul (lw-complex-power point shift)
                                  (lw-complex-polynomial coefficients point 0))))
  :hints (("Goal"
           :use (lw-pcr-offset-power (:instance lw-pcr-shift-evaluation-offset (offset 0)))
           :in-theory (union-theories
 '(fold-consts-in-+ (:executable-counterpart lw-complexp) lw-pcr-left-commutes lw-pcr-left-distributes lw-pcr-fold-constants lw-pcr-times-negative lw-pcr-negative-times lw-pcr-zero-times lw-pcr-minus-one lw-pcr-double-negative lw-pcr-add-cancel lw-pcr-double lw-pcr-add-double
 natp posp zp fix car-cons cdr-cons commutativity-of-* associativity-of-*
 commutativity-of-+ commutativity-2-of-+ associativity-of-+
 distributivity distributivity-of-minus-over-+ inverse-of-+ unicity-of-0 unicity-of-1)
 (theory 'minimal-theory))
           :do-not-induct t)))
