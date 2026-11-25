(in-package "ACL2")

(include-book "circle-bounded-radius-selection")
(include-book "euler-circle-inner-factor-count")
(include-book "euler-zeta-clearance")

; This computes a uniform radius clearance in the scaled disk.
; The selected radius can vary with the two approximation requests.

(local (defthm lw-ecbr-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ecbr-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ecbr-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ecbr-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ecbr-times-negative (a b) (b a)))
                 :in-theory (disable lw-ecbr-times-negative)))))

(local (defthm lw-ecbr-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ecbr-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ecbr-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ecbr-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ecbr-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ecbr-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ecbr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ecbr-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(defun lw-euler-circle-jensen-count-budget (rate height outer-radius cutoff-square)
  (let ((size (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))))
    (lw-circle-inner-factor-count-limit cutoff-square (* (* 1/8 size) (* 1/8 size)) (+ 1 (lw-euler-uniform-coefficient-cap rate height outer-radius)))))

(defun lw-euler-circle-bounded-radius (rate height outer-radius target error factor-error lower upper cutoff-square)
  (lw-circle-bounded-radius (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) lower upper cutoff-square (lw-euler-circle-jensen-count-budget rate height outer-radius cutoff-square)))

(defthm lw-euler-circle-bounded-radius-valid
  (implies (and (rationalp rate) (< 3 rate) (rationalp height)
                (rationalp outer-radius) (< 0 outer-radius) (< outer-radius rate)
                (natp target) (rationalp error) (< 0 error)
                (rationalp factor-error) (< 0 factor-error)
                (<= error 1) (<= factor-error 1)
                (<= error (* 1/64 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))))
                (<= factor-error (* 1/64 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))))
                (rationalp lower) (<= 0 lower) (rationalp upper) (< lower upper)
                (rationalp cutoff-square) (<= 0 cutoff-square)
                (< (* upper upper) cutoff-square) (< cutoff-square 1))
           (let* ((data (lw-euler-circle-bounded-radius rate height outer-radius target error factor-error lower upper cutoff-square))
                  (radius (car data))
                  (gap (cdr data)))
             (and (rationalp radius) (< lower radius) (< radius upper)
                  (equal gap (lw-circle-bounded-radius-gap lower upper cutoff-square (lw-euler-circle-jensen-count-budget rate height outer-radius cutoff-square)))
                  (rationalp gap) (< 0 gap)
                  (lw-circle-radial-bracket-clear (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error) radius radius gap))))
  :hints (("Goal"
           :use (lw-euler-zeta-clearance-check
                 (:instance lw-euler-circle-inner-factor-count (radius outer-radius) (anchor-error (lw-euler-zeta-clearance-request rate height)))
                 (:instance lw-euler-polynomial-coefficient-rational (radius outer-radius) (index 0))
                 (:instance lw-polynomial-disk-factor-data (coefficients (lw-euler-coefficient-polynomial rate height outer-radius target error)) (outer-radius 1) (epsilon factor-error))
                 (:instance lw-resolvent-truncation-count-natural
                   (radius cutoff-square) (error (/ (* (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height))) (* 1/8 (lw-euler-value-clearance-size rate height (lw-euler-zeta-clearance-request rate height)))) (* 2 (+ 2 (lw-euler-uniform-coefficient-cap rate height outer-radius)) (+ 2 (lw-euler-uniform-coefficient-cap rate height outer-radius))))))
                 (:instance lw-circle-bounded-radius-valid (roots (lw-polynomial-normalized-factor-roots (lw-euler-coefficient-polynomial rate height outer-radius target error) 1 factor-error)) (budget (lw-euler-circle-jensen-count-budget rate height outer-radius cutoff-square))))
           :in-theory (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-euler-circle-bounded-radius lw-euler-circle-jensen-count-budget
              lw-circle-inner-factor-count-limit lw-circle-bounded-radius
              lw-ecbr-left-commutes lw-ecbr-left-distributes lw-ecbr-fold-constants
              lw-ecbr-times-negative lw-ecbr-negative-times lw-ecbr-zero-times
              lw-ecbr-minus-one lw-ecbr-double-negative lw-ecbr-add-cancel lw-ecbr-double lw-ecbr-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))
           :do-not-induct t))
  :rule-classes nil)
