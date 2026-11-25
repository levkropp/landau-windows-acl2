(in-package "ACL2")

(include-book "euler-window-real-bands")

; Return the last empty band and, if encountered, its positive-count
; successor. The initial band is empty by the small-probe exclusions.

(local (defthm lw-ewrs-left-commutes
         (equal (* a (* b c)) (* b (* a c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c))
                              (:instance associativity-of-* (x b) (y a) (z c))
                              (:instance commutativity-of-* (x a) (y b)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(local (defthm lw-ewrs-left-distributes
         (equal (* (+ a b) c) (+ (* a c) (* b c)))
         :hints (("Goal" :use ((:instance distributivity (x c) (y a) (z b)))
                         :in-theory (disable distributivity)))))

(local (defthm lw-ewrs-times-negative
 (equal (* a (- b)) (- (* a b)))
 :hints (("Goal" :use ((:instance distributivity (x a) (y b) (z (- b))))
                 :in-theory (disable distributivity)))))

(local (defthm lw-ewrs-negative-times
 (equal (* (- a) b) (- (* a b)))
 :hints (("Goal" :use ((:instance lw-ewrs-times-negative (a b) (b a)))
                 :in-theory (disable lw-ewrs-times-negative)))))

(local (defthm lw-ewrs-zero-times (equal (* 0 a) 0)))

(local (defthm lw-ewrs-minus-one (implies (rationalp a) (equal (* -1 a) (- a)))))

(local (defthm lw-ewrs-double-negative (implies (rationalp a) (equal (- (- a)) a))))

(local (defthm lw-ewrs-add-cancel
         (implies (and (rationalp a) (rationalp b)) (equal (+ a (- a) b) b))))

(local (defthm lw-ewrs-double (implies (rationalp a) (equal (+ a a) (* 2 a)))))

(local (defthm lw-ewrs-add-double
         (implies (and (rationalp a) (rationalp b))
                  (equal (+ a (+ a b)) (+ (* 2 a) b)))))

(local (defthm lw-ewrs-fold-constants
         (implies (syntaxp (and (quotep a) (quotep b)))
                  (equal (* a (* b c)) (* (* a b) c)))
         :hints (("Goal" :use ((:instance associativity-of-* (x a) (y b) (z c)))
                         :in-theory (disable associativity-of-*)))))

(local (defthm lw-ewrs-positive-product
         (implies (and (rationalp a) (< 0 a) (rationalp b) (< 0 b)) (< 0 (* a b)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewrs-multiply-order
         (implies (and (rationalp a) (rationalp b) (<= a b)
                       (rationalp factor) (<= 0 factor))
                  (<= (* a factor) (* b factor)))
         :hints (("Goal" :nonlinearp t)) :rule-classes nil))

(local (defthm lw-ewrs-inverse-factor
         (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
                  (equal (* divisor (* (/ divisor) coefficient)) coefficient))
         :hints (("Goal"
                  :use ((:instance associativity-of-* (x divisor) (y (/ divisor)) (z coefficient))
                        (:instance inverse-of-* (x divisor)))
                  :in-theory (disable associativity-of-* commutativity-of-* lw-ewrs-left-commutes)))))

(local (deftheory lw-ewrs-arithmetic (union-theories
            '(fold-consts-in-+ (:executable-counterpart lw-complexp)
              lw-ewrs-left-commutes lw-ewrs-left-distributes lw-ewrs-fold-constants
              lw-ewrs-times-negative lw-ewrs-negative-times lw-ewrs-zero-times
              lw-ewrs-minus-one lw-ewrs-double-negative lw-ewrs-add-cancel lw-ewrs-double lw-ewrs-add-double
              natp posp zp fix car-cons cdr-cons
              commutativity-of-* associativity-of-*
              commutativity-of-+ commutativity-2-of-+ associativity-of-+
              distributivity distributivity-of-minus-over-+
              inverse-of-+ unicity-of-0 unicity-of-1)
            (theory 'minimal-theory))))

(defun lw-euler-window-scan-real-bands (cap step remaining current)
  (declare (xargs :measure (nfix remaining)
                  :hints (("Goal" :in-theory (theory 'ground-zero)))))
  (if (zp remaining) (list current nil)
    (let ((next (lw-euler-window-real-band cap step (- remaining 1))))
      (if (< 0 (lw-euler-circle-interior-count (cons 252 0) (car next) (cadr next) (caddr next)))
          (list current next)
        (lw-euler-window-scan-real-bands cap step (- remaining 1) next)))))

(defun lw-euler-window-real-covers (cap slack)
  (let* ((gap (lw-euler-window-real-gap cap slack))
         (step (lw-euler-window-real-band-step cap gap))
         (count (lw-euler-window-real-band-count cap gap)))
    (lw-euler-window-scan-real-bands cap step count
                                    (lw-euler-window-real-band cap step count))))

(local
 (defun lw-ewrs-current-check (current cap step remaining)
   (and (rationalp (car current))
        (< (- cap (* (+ 1 remaining) step)) (car current)) (< (car current) (- cap (* (+ 1/2 remaining) step)))
        (lw-euler-circle-coverp (cons 252 0) (car current) (cadr current) (caddr current)))))

(local
 (defun lw-ewrs-data-check (result base cap step)
   (let ((empty (car result))
         (positive (cadr result)))
     (and (rationalp (car empty)) (< base (car empty)) (< (car empty) cap)
          (lw-euler-circle-coverp (cons 252 0) (car empty) (cadr empty) (caddr empty)) (equal (lw-euler-circle-interior-count (cons 252 0) (car empty) (cadr empty) (caddr empty)) 0)
          (if positive
              (and (rationalp (car positive)) (< (car empty) (car positive)) (< (car positive) cap)
                   (< (car positive) (+ (car empty) (* 2 step)))
                   (lw-euler-circle-coverp (cons 252 0) (car positive) (cadr positive) (caddr positive)) (< 0 (lw-euler-circle-interior-count (cons 252 0) (car positive) (cadr positive) (caddr positive))))
            (< (- cap step) (car empty)))))))

(local
 (defthm lw-ewrs-next-band
   (implies (and (rationalp cap) (< cap 252) (rationalp step) (< 0 step)
                 (posp remaining) (<= 0 (- cap (* (+ 1 remaining) step))))
            (and (< (- cap (* (+ 1 remaining) step)) (- cap (* remaining step)))
                 (< (- cap (* (+ 1/2 remaining) step)) (- cap (* remaining step)))
                 (< (- cap (* (- remaining 1/2) step)) (+ (- cap (* (+ 1 remaining) step)) (* 2 step)))
                 (lw-ewrs-current-check (lw-euler-window-real-band cap step (- remaining 1)) cap step (- remaining 1))))
   :hints (("Goal"
            :use ((:instance lw-euler-window-real-band-valid (remaining (- remaining 1))))
            :in-theory (union-theories '(lw-ewrs-current-check) (theory 'lw-ewrs-arithmetic))
            :do-not-induct t))
   :rule-classes nil))

(local
 (defthm lw-ewrs-positive-car-nonempty
   (implies (and (rationalp (car data)) (< 0 (car data))) data)
   :hints (("Goal" :in-theory (theory 'minimal-theory)))
   :rule-classes nil))

(local
 (defthm lw-ewrs-scan-valid
   (implies (and (rationalp cap) (< cap 252) (rationalp step) (< 0 step) (natp remaining)
                 (rationalp base) (<= 0 base) (<= base (- cap (* (+ 1 remaining) step)))
                 (lw-ewrs-current-check current cap step remaining)
                 (equal (lw-euler-circle-interior-count (cons 252 0) (car current) (cadr current) (caddr current)) 0))
            (lw-ewrs-data-check (lw-euler-window-scan-real-bands cap step remaining current) base cap step))
   :hints (("Goal"
            :induct (lw-euler-window-scan-real-bands cap step remaining current)
            :in-theory (union-theories '(lw-euler-window-scan-real-bands)
                                      (theory 'lw-ewrs-arithmetic))
            :do-not '(generalize fertilize))
           (and stable-under-simplificationp
                '(:use (lw-ewrs-next-band
                        (:instance lw-euler-circle-interior-count-natural (center (cons 252 0))
                          (radius (car (lw-euler-window-real-band cap step (- remaining 1)))) (plus-arcs (cadr (lw-euler-window-real-band cap step (- remaining 1)))) (minus-arcs (caddr (lw-euler-window-real-band cap step (- remaining 1)))))
                        (:instance lw-ewrs-positive-car-nonempty (data (lw-euler-window-real-band cap step (- remaining 1))))
                        (:instance lw-ewrs-positive-product (a (+ 1/2 remaining)) (b step))
                        (:instance lw-ewrs-positive-product (a (- remaining 1/2)) (b step)))
                  :in-theory (union-theories '(lw-ewrs-current-check lw-ewrs-data-check)
                                            (theory 'lw-ewrs-arithmetic))
                  :do-not-induct t)))
   :rule-classes nil))

(defthm lw-euler-window-real-covers-valid
  (implies (and (rationalp cap) (< 251 cap) (< cap 252) (rationalp slack) (< 0 slack))
           (let* ((gap (lw-euler-window-real-gap cap slack))
                  (step (lw-euler-window-real-band-step cap gap))
                  (result (lw-euler-window-real-covers cap slack))
                  (empty (car result))
                  (positive (cadr result)))
             (and (rationalp (car empty)) (< (+ 251 (* 2 gap)) (car empty)) (< (car empty) cap)
                  (lw-euler-circle-coverp (cons 252 0) (car empty) (cadr empty) (caddr empty)) (equal (lw-euler-circle-interior-count (cons 252 0) (car empty) (cadr empty) (caddr empty)) 0)
                  (if positive
                      (and (rationalp (car positive)) (< (car empty) (car positive)) (< (car positive) cap)
                           (< (car positive) (+ (car empty) (* 2 step)))
                           (lw-euler-circle-coverp (cons 252 0) (car positive) (cadr positive) (caddr positive)) (< 0 (lw-euler-circle-interior-count (cons 252 0) (car positive) (cadr positive) (caddr positive))))
                    (< (- cap step) (car empty))))))
  :hints (("Goal"
           :use (lw-euler-window-real-gap-data
                 (:instance lw-euler-window-real-band-step-data (gap (lw-euler-window-real-gap cap slack)))
                 (:instance lw-euler-window-real-band-valid (step (lw-euler-window-real-band-step cap (lw-euler-window-real-gap cap slack)))
                   (remaining (lw-euler-window-real-band-count cap (lw-euler-window-real-gap cap slack))))
                 (:instance lw-euler-real-circle-initial-count-empty (gap (lw-euler-window-real-gap cap slack))
                   (outer-radius (lw-euler-window-real-outer cap))
                   (radius (car (lw-euler-window-real-band cap (lw-euler-window-real-band-step cap (lw-euler-window-real-gap cap slack)) (lw-euler-window-real-band-count cap (lw-euler-window-real-gap cap slack)))))
                   (plus-arcs (cadr (lw-euler-window-real-band cap (lw-euler-window-real-band-step cap (lw-euler-window-real-gap cap slack)) (lw-euler-window-real-band-count cap (lw-euler-window-real-gap cap slack)))))
                   (minus-arcs (caddr (lw-euler-window-real-band cap (lw-euler-window-real-band-step cap (lw-euler-window-real-gap cap slack)) (lw-euler-window-real-band-count cap (lw-euler-window-real-gap cap slack))))))
                 (:instance lw-ewrs-scan-valid
                   (base (+ 251 (* 2 (lw-euler-window-real-gap cap slack)))) (step (lw-euler-window-real-band-step cap (lw-euler-window-real-gap cap slack)))
                   (remaining (lw-euler-window-real-band-count cap (lw-euler-window-real-gap cap slack))) (current (lw-euler-window-real-band cap (lw-euler-window-real-band-step cap (lw-euler-window-real-gap cap slack)) (lw-euler-window-real-band-count cap (lw-euler-window-real-gap cap slack))))))
           :in-theory (union-theories '(lw-euler-window-real-covers lw-ewrs-current-check lw-ewrs-data-check
                                       (:type-prescription lw-ceiling-rational)
                                       lw-euler-window-real-band-count) (theory 'lw-ewrs-arithmetic))
           :do-not-induct t))
  :rule-classes nil)
