(in-package "ACL2")

(include-book "circle-pole-split")

(defun lw-circle-radius-branch (square lower upper)
  (let ((midpoint (* 1/2 (+ lower upper)))
        (quarter (* 1/4 (- upper lower))))
    (if (<= square (* midpoint midpoint))
        (cons (+ midpoint quarter) upper)
      (cons lower (- midpoint quarter)))))

(defun lw-circle-finite-radius-bracket (roots lower upper)
  (declare (xargs :measure (acl2-count roots)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp roots)
      (cons lower upper)
    (let ((next (lw-circle-radius-branch
                 (lw-complex-norm-square (car roots)) lower upper)))
      (lw-circle-finite-radius-bracket (cdr roots) (car next) (cdr next)))))

(defun lw-circle-finite-radius (bracket)
  (* 1/2 (+ (car bracket) (cdr bracket))))

(defun lw-circle-finite-radius-gap (bracket)
  (let ((width (- (cdr bracket) (car bracket))))
    (* width width)))

(defun lw-circle-radial-bracket-clear (roots lower upper gap)
  (declare (xargs :measure (acl2-count roots)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp roots) t
    (let ((square (lw-complex-norm-square (car roots))))
      (and (or (<= (+ square gap) (* lower lower))
               (<= (+ (* upper upper) gap) square))
           (lw-circle-radial-bracket-clear (cdr roots) lower upper gap)))))

(local (defthm lw-cfr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cfr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cfr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cfr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cfr-times-negative (a b) (b a)))
                 :in-theory (disable lw-cfr-times-negative)))))

(local (defthm lw-cfr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cfr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cfr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cfr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cfr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cfr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cfr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-cfr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cfr-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-cfr-left-commutes)))))

(local
 (defthm lw-cfr-square-order
   (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b))
            (<= (* a a) (* b b)))
   :hints (("Goal"
            :use ((:instance lw-cfr-multiply-order (factor a))
                  (:instance lw-cfr-multiply-order (factor b)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfr-left-commutes lw-cfr-left-distributes lw-cfr-fold-constants
              lw-cfr-times-negative lw-cfr-negative-times lw-cfr-zero-times
              lw-cfr-minus-one lw-cfr-double-negative lw-cfr-add-cancel lw-cfr-double lw-cfr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-cfr-square-gap
   (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b)
                 (rationalp width) (<= 0 width) (<= width (- b a)))
            (<= (+ (* a a) (* width width)) (* b b)))
   :hints (("Goal"
            :use ((:instance lw-cfr-square-order (a width) (b (- b a)))
                  (:instance lw-cfr-multiply-order (a 0) (b (- b a)) (factor a)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cfr-left-commutes lw-cfr-left-distributes lw-cfr-fold-constants
              lw-cfr-times-negative lw-cfr-negative-times lw-cfr-zero-times
              lw-cfr-minus-one lw-cfr-double-negative lw-cfr-add-cancel lw-cfr-double lw-cfr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-cfr-branch-data
   (implies (and (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper))
            (and (rationalp (car (lw-circle-radius-branch square lower upper))) (rationalp (cdr (lw-circle-radius-branch square lower upper)))
                 (<= lower (car (lw-circle-radius-branch square lower upper))) (< (car (lw-circle-radius-branch square lower upper)) (cdr (lw-circle-radius-branch square lower upper))) (<= (cdr (lw-circle-radius-branch square lower upper)) upper)
                 (equal (- (cdr (lw-circle-radius-branch square lower upper)) (car (lw-circle-radius-branch square lower upper))) (* 1/4 (- upper lower)))))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-radius-branch
              lw-cfr-left-commutes lw-cfr-left-distributes lw-cfr-fold-constants
              lw-cfr-times-negative lw-cfr-negative-times lw-cfr-zero-times
              lw-cfr-minus-one lw-cfr-double-negative lw-cfr-add-cancel lw-cfr-double lw-cfr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-cfr-surviving-gap
   (implies (and (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                 (rationalp square) (rationalp left) (rationalp right)
                 (<= (car (lw-circle-radius-branch square lower upper)) left) (<= left right) (<= right (cdr (lw-circle-radius-branch square lower upper))))
            (or (<= (+ square (* (- right left) (- right left))) (* left left))
                (<= (+ (* right right) (* (- right left) (- right left))) square)))
   :hints (("Goal"
            :use ((:instance lw-cfr-square-gap (a (* 1/2 (+ lower upper))) (b left) (width (- right left)))
                  (:instance lw-cfr-square-gap (a right) (b (* 1/2 (+ lower upper))) (width (- right left))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-radius-branch
              lw-cfr-left-commutes lw-cfr-left-distributes lw-cfr-fold-constants
              lw-cfr-times-negative lw-cfr-negative-times lw-cfr-zero-times
              lw-cfr-minus-one lw-cfr-double-negative lw-cfr-add-cancel lw-cfr-double lw-cfr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t))
   :rule-classes nil))

; Retain one quarter of the interval on the far side of each squared
; root distance. Every later retained interval preserves that clearance.
(defthm lw-circle-finite-radius-bracket-data
  (implies (and (lw-ray-pointsp roots) (rationalp lower) (<= 0 lower)
                (rationalp upper) (< lower upper))
           (let ((bracket (lw-circle-finite-radius-bracket roots lower upper)))
             (and (consp bracket) (rationalp (car bracket)) (rationalp (cdr bracket))
                  (<= lower (car bracket)) (< (car bracket) (cdr bracket))
                  (<= (cdr bracket) upper)
                  (lw-circle-radial-bracket-clear roots (car bracket) (cdr bracket)
                    (lw-circle-finite-radius-gap bracket)))))
  :hints (("Goal" :induct (lw-circle-finite-radius-bracket roots lower upper)
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-finite-radius-bracket lw-circle-finite-radius-gap
              lw-circle-radial-bracket-clear lw-ray-pointsp endp
              lw-cfr-left-commutes lw-cfr-left-distributes lw-cfr-fold-constants
              lw-cfr-times-negative lw-cfr-negative-times lw-cfr-zero-times
              lw-cfr-minus-one lw-cfr-double-negative lw-cfr-add-cancel lw-cfr-double lw-cfr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
          (and stable-under-simplificationp
               '(:use ((:instance lw-cfr-branch-data (square (lw-complex-norm-square (car roots))))
                       (:instance lw-complex-norm-square-valid (point (car roots)))
                       (:instance lw-cfr-surviving-gap (square (lw-complex-norm-square (car roots)))
                         (left (car (lw-circle-finite-radius-bracket (cdr roots) (car (lw-circle-radius-branch (lw-complex-norm-square (car roots)) lower upper)) (cdr (lw-circle-radius-branch (lw-complex-norm-square (car roots)) lower upper))))) (right (cdr (lw-circle-finite-radius-bracket (cdr roots) (car (lw-circle-radius-branch (lw-complex-norm-square (car roots)) lower upper)) (cdr (lw-circle-radius-branch (lw-complex-norm-square (car roots)) lower upper)))))))
                 :do-not-induct t)))
  :rule-classes nil)

(local
 (defthm lw-cfr-bracket-clear-at-radius
   (implies (and (rationalp lower) (<= 0 lower) (rationalp radius) (<= lower radius)
                 (rationalp upper) (<= radius upper)
                 (rationalp gap) (lw-circle-radial-bracket-clear roots lower upper gap))
            (lw-circle-radial-bracket-clear roots radius radius gap))
   :hints (("Goal" :induct (lw-circle-radial-bracket-clear roots lower upper gap)
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-radial-bracket-clear endp
              lw-cfr-left-commutes lw-cfr-left-distributes lw-cfr-fold-constants
              lw-cfr-times-negative lw-cfr-negative-times lw-cfr-zero-times
              lw-cfr-minus-one lw-cfr-double-negative lw-cfr-add-cancel lw-cfr-double lw-cfr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use ((:instance lw-cfr-square-order (a lower) (b radius))
                        (:instance lw-cfr-square-order (a radius) (b upper)))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-circle-finite-separated-radius
  (implies (and (lw-ray-pointsp roots) (rationalp lower) (<= 0 lower)
                (rationalp upper) (< lower upper))
           (let* ((bracket (lw-circle-finite-radius-bracket roots lower upper))
                  (radius (lw-circle-finite-radius bracket))
                  (gap (lw-circle-finite-radius-gap bracket)))
             (and (rationalp radius) (< lower radius) (< radius upper)
                  (rationalp gap) (< 0 gap)
                  (lw-circle-radial-bracket-clear roots radius radius gap))))
  :hints (("Goal"
           :use (lw-circle-finite-radius-bracket-data
                 (:instance lw-cfr-positive-product
                   (a (- (cdr (lw-circle-finite-radius-bracket roots lower upper)) (car (lw-circle-finite-radius-bracket roots lower upper)))) (b (- (cdr (lw-circle-finite-radius-bracket roots lower upper)) (car (lw-circle-finite-radius-bracket roots lower upper)))))
                 (:instance lw-cfr-bracket-clear-at-radius
                   (lower (car (lw-circle-finite-radius-bracket roots lower upper))) (upper (cdr (lw-circle-finite-radius-bracket roots lower upper))) (radius (lw-circle-finite-radius (lw-circle-finite-radius-bracket roots lower upper))) (gap (lw-circle-finite-radius-gap (lw-circle-finite-radius-bracket roots lower upper)))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-finite-radius lw-circle-finite-radius-gap
              lw-cfr-left-commutes lw-cfr-left-distributes lw-cfr-fold-constants
              lw-cfr-times-negative lw-cfr-negative-times lw-cfr-zero-times
              lw-cfr-minus-one lw-cfr-double-negative lw-cfr-add-cancel lw-cfr-double lw-cfr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
