(in-package "ACL2")

(include-book "circle-radial-clearance")
(include-book "pole-geometry")

; If the witness's horizontal projection is too wide for an empty real
; circle, modulate at the closest point to the real center instead.

(local (defthm lw-cpr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-cpr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-cpr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-cpr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-cpr-times-negative (a b) (b a)))
                 :in-theory (disable lw-cpr-times-negative)))))

(local (defthm lw-cpr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-cpr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-cpr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-cpr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-cpr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-cpr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-cpr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(defun lw-circle-pair-strip-pointsp (points)
  (declare (xargs :measure (acl2-count points)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (endp points)
      (null points)
    (let ((point (car points)))
      (and (lw-plane-pointp point)
           (< 0 (car point)) (<= (car point) 1) (not (equal (cdr point) 0))
           (lw-circle-pair-strip-pointsp (cdr points))))))

(defun lw-circle-pair-pole (points witness)
  (let* ((nearest (lw-nearest-point 252 0 points))
         (horizontal (- 252 (car witness))))
    (if (< (* horizontal horizontal) (lw-distance-squared 252 0 nearest))
        witness
      nearest)))

(defun lw-circle-pair-upper-radius (horizontal clearance-square limit)
  (min limit
       (+ horizontal
          (lw-circle-radial-clearance horizontal
            (- clearance-square (* horizontal horizontal))))))

(defun lw-circle-pair-radius-data (points witness limit)
  (let* ((pole (lw-circle-pair-pole points witness))
         (horizontal (- 252 (car pole)))
         (upper (lw-circle-pair-upper-radius horizontal (lw-distance-squared 252 0 (lw-nearest-point 252 0 points)) limit))
         (third (/ (- upper horizontal) 3)))
    (list pole (+ horizontal third) (+ horizontal (* 2 third)) (+ horizontal (* 5/2 third)))))

(local
 (defthm lw-cpr-strip-left
   (implies (lw-circle-pair-strip-pointsp points)
            (lw-points-left-of 252 points))
   :hints (("Goal" :induct (lw-circle-pair-strip-pointsp points)
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-pair-strip-pointsp lw-points-left-of lw-plane-pointp endp
              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))
   :rule-classes nil))

(local
 (defthm lw-cpr-strip-point
   (implies (and (lw-circle-pair-strip-pointsp points) (member-equal point points))
            (and (lw-plane-pointp point) (< 0 (car point)) (<= (car point) 1)
                 (not (equal (cdr point) 0))))
   :hints (("Goal" :induct (lw-circle-pair-strip-pointsp points)
                   :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-pair-strip-pointsp member-equal endp
              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
                   :do-not '(generalize fertilize)))
   :rule-classes nil))

(local
 (defthm lw-cpr-projection
   (implies (and (lw-plane-pointp point) (< 0 (car point)) (<= (car point) 1)
                 (not (equal (cdr point) 0)))
            (let ((horizontal (- 252 (car point))))
              (and (rationalp horizontal) (<= 251 horizontal)
                   (rationalp (cdr point))
                   (rationalp (lw-distance-squared 252 0 point))
                   (< (* horizontal horizontal) (lw-distance-squared 252 0 point))
                   (equal (lw-distance-squared 252 (cdr point) point)
                          (* horizontal horizontal)))))
   :hints (("Goal"
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-plane-pointp lw-distance-squared
              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-cpr-present
   (implies (member-equal point points) (consp points))
   :hints (("Goal" :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              member-equal
              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local (defthm lw-cpr-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-cpr-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local
 (defthm lw-cpr-square-order
   (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= a b))
            (<= (* a a) (* b b)))
   :hints (("Goal"
            :use ((:instance lw-cpr-multiply-order (factor a))
                  (:instance lw-cpr-multiply-order (factor b)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))
   :rule-classes nil))

(local
 (defthm lw-cpr-square-order-reflect
   (implies (and (rationalp a) (rationalp b) (<= 0 a) (<= 0 b)
                 (<= (* a a) (* b b)))
            (<= a b))
   :hints (("Goal"
            :use ((:instance lw-cpr-positive-product (a (- a b)) (b (+ a b))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-cpr-pole-data
   (implies (and (lw-circle-pair-strip-pointsp points)
                (member-equal witness points)
                (rationalp limit) (< (- 252 (car witness)) limit) (<= limit 252))
            (let ((pole (lw-circle-pair-pole points witness))
                  (horizontal (- 252 (car (lw-circle-pair-pole points witness)))))
              (and (member-equal pole points)
                   (rationalp horizontal) (<= 251 horizontal) (< horizontal limit)
                   (rationalp (cdr pole)) (rationalp (lw-distance-squared 252 0 (lw-nearest-point 252 0 points)))
                   (< (* horizontal horizontal) (lw-distance-squared 252 0 (lw-nearest-point 252 0 points)))
                   (equal (lw-distance-squared 252 (cdr pole) pole)
                          (* horizontal horizontal)))))
   :hints (("Goal"
            :use ((:instance lw-cpr-present (point witness))
                  (:instance lw-nearest-point-member (sigma 252) (height 0))
                  (:instance lw-cpr-strip-point (point witness))
                  (:instance lw-cpr-strip-point (point (lw-nearest-point 252 0 points)))
                  (:instance lw-cpr-projection (point witness))
                  (:instance lw-cpr-square-order-reflect
                    (a (- 252 (car (lw-nearest-point 252 0 points))))
                    (b (- 252 (car witness))))
                  (:instance lw-cpr-projection (point (lw-nearest-point 252 0 points))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-pair-pole
              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp t))
   :rule-classes nil))

(local
 (defthm lw-cpr-upper-data
   (implies (and (rationalp horizontal) (< 0 horizontal)
                 (rationalp clearance-square) (< (* horizontal horizontal) clearance-square)
                 (rationalp limit) (< horizontal limit))
            (let ((upper (lw-circle-pair-upper-radius horizontal clearance-square limit)))
              (and (rationalp upper) (< horizontal upper) (<= upper limit)
                   (< (* upper upper) clearance-square))))
   :hints (("Goal"
            :use ((:instance lw-circle-radial-clearance-budget
                     (radius horizontal) (gap (- clearance-square (* horizontal horizontal))))
                  (:instance lw-cpr-square-order (a limit)
                    (b (+ horizontal (lw-circle-radial-clearance horizontal
                          (- clearance-square (* horizontal horizontal)))))))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-pair-upper-radius min
              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(local
 (defthm lw-cpr-inner-radii
   (implies (and (rationalp horizontal) (<= 251 horizontal)
                 (rationalp upper) (< horizontal upper))
            (let* ((third (/ (- upper horizontal) 3))
                   (modulated (+ horizontal third))
                   (normalization (+ horizontal (* 2 third)))
                   (real-radius (+ horizontal (* 5/2 third))))
              (and (rationalp modulated) (< horizontal modulated)
                   (rationalp normalization) (< modulated normalization)
                   (rationalp real-radius) (< normalization real-radius) (< real-radius upper)
                   (< (* horizontal horizontal) (* modulated modulated))
                   (<= (* real-radius real-radius) (* upper upper)))))
   :hints (("Goal"
            :use ((:instance lw-cpr-positive-product
                     (a (- upper horizontal)) (b 1/3))
                  (:instance lw-cpr-square-order-reflect
                     (a (+ horizontal (/ (- upper horizontal) 3))) (b horizontal))
                  (:instance lw-cpr-square-order
                     (a (+ horizontal (* 5/2 (/ (- upper horizontal) 3)))) (b upper)))
            :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
            :do-not-induct t :nonlinearp nil))
   :rule-classes nil))

(defthm lw-circle-pair-radius-selection
  (implies (and (lw-circle-pair-strip-pointsp points)
                (member-equal witness points)
                (rationalp limit) (< (- 252 (car witness)) limit) (<= limit 252))
           (let* ((data (lw-circle-pair-radius-data points witness limit))
                  (pole (car data))
                  (modulated-upper (cadr data))
                  (normalization-radius (caddr data))
                  (real-radius (cadddr data))
                  (horizontal (- 252 (car pole))))
             (and (member-equal pole points) (rationalp (cdr pole))
                  (rationalp horizontal) (<= 251 horizontal)
                  (rationalp modulated-upper) (< horizontal modulated-upper)
                  (rationalp normalization-radius) (< modulated-upper normalization-radius)
                  (rationalp real-radius) (< normalization-radius real-radius)
                  (< real-radius limit)
                  (< (lw-distance-squared 252 (cdr pole) pole)
                     (* modulated-upper modulated-upper))
                  (< (* real-radius real-radius) (lw-distance-squared 252 0 (lw-nearest-point 252 0 points))))))
  :hints (("Goal"
           :use (lw-cpr-pole-data
                 (:instance lw-cpr-upper-data (horizontal (- 252 (car (lw-circle-pair-pole points witness)))) (clearance-square (lw-distance-squared 252 0 (lw-nearest-point 252 0 points))))
                 (:instance lw-cpr-inner-radii (horizontal (- 252 (car (lw-circle-pair-pole points witness)))) (upper (lw-circle-pair-upper-radius (- 252 (car (lw-circle-pair-pole points witness))) (lw-distance-squared 252 0 (lw-nearest-point 252 0 points)) limit))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-circle-pair-radius-data
              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t :nonlinearp nil))
  :rule-classes nil)

(defthm lw-circle-pair-real-radius-excludes-point
  (implies (and (lw-circle-pair-strip-pointsp points)
                (member-equal witness points)
                (rationalp limit) (< (- 252 (car witness)) limit) (<= limit 252)
                (member-equal point points))
           (let ((radius (cadddr (lw-circle-pair-radius-data points witness limit))))
             (< (* radius radius) (lw-distance-squared 252 0 point))))
  :hints (("Goal"
           :use (lw-cpr-strip-left lw-circle-pair-radius-selection
                 (:instance lw-nearest-point-minimizes (sigma 252) (height 0)))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)

              lw-cpr-left-commutes lw-cpr-left-distributes lw-cpr-fold-constants
              lw-cpr-times-negative lw-cpr-negative-times lw-cpr-zero-times
              lw-cpr-minus-one lw-cpr-double-negative lw-cpr-add-cancel lw-cpr-double lw-cpr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
