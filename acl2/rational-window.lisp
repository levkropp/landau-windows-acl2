(in-package "ACL2")

(include-book "grid-witness")

(local (defthm lw-multiply-left-commutes
         (equal (* left (* middle right)) (* middle (* left right)))
         :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                              (:instance associativity-of-* (x middle) (y left) (z right))
                              (:instance commutativity-of-* (x left) (y middle)))
                         :in-theory (disable associativity-of-* commutativity-of-*)))))

(defun lw-halved-width (width steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      width
    (/ (lw-halved-width width (- steps 1)) 2)))

(defthm lw-halved-width-half
  (implies (rationalp width)
           (equal (lw-halved-width (* 1/2 width) steps)
                  (/ (lw-halved-width width steps) 2))))

(local
 (defthm lw-halved-width-add
   (implies (and (rationalp left) (rationalp right))
            (equal (lw-halved-width (+ left right) steps)
                   (+ (lw-halved-width left steps) (lw-halved-width right steps))))))

(local
 (defthm lw-halved-width-negate
   (implies (rationalp width)
            (equal (lw-halved-width (- width) steps) (- (lw-halved-width width steps))))))

(defun lw-halving-depth (width epsilon fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (or (zp fuel) (<= width epsilon))
      0
    (+ 1 (lw-halving-depth width (* 2 epsilon) (- fuel 1)))))

(defthm lw-halving-depth-natural
  (natp (lw-halving-depth width epsilon fuel))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-positive-fuel-at-least-one
  (implies (not (zp fuel)) (<= 1 fuel))
  :rule-classes nil)

(defthm lw-doubling-budget
  (implies (and (rationalp width)
                (rationalp epsilon)
                (rationalp fuel)
                (<= 1 fuel)
                (< 0 epsilon)
                (<= width (* (+ 1 fuel) epsilon)))
           (<= width (* 2 fuel epsilon)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

(defthm lw-halving-depth-adequate
  (implies (and (rationalp width)
                (rationalp epsilon)
                (<= 0 width)
                (< 0 epsilon)
                (natp fuel)
                (<= width (* (+ 1 fuel) epsilon)))
           (<= (lw-halved-width width (lw-halving-depth width epsilon fuel)) epsilon))
  :hints (("Goal" :induct (lw-halving-depth width epsilon fuel)
                  :nonlinearp t)
          (and stable-under-simplificationp
               '(:use (lw-positive-fuel-at-least-one lw-doubling-budget)
                 :nonlinearp t))))

(defun lw-precision-fuel (width epsilon)
  (nfix (* (abs (numerator width)) (denominator epsilon))))

(local
 (defthm lw-inverse-factor
   (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
            (equal (* divisor (* (/ divisor) coefficient)) coefficient))
   :hints (("Goal" :use ((:instance associativity-of-* (x divisor)
                                    (y (/ divisor)) (z coefficient)))
                   :in-theory (disable associativity-of-* commutativity-of-*
                                       lw-multiply-left-commutes)))))

(defthm lw-rational-cross-multiply
  (implies (rationalp value)
           (equal (* (denominator value) value) (numerator value)))
  :instructions
  (:promote (:use (:instance rational-implies1 (x value))
                  (:instance rational-implies2 (x value))) :promote
   (:dive 1 2) (:equiv value (* (/ (denominator value)) (numerator value))) :top
   (:drop 2) (:in-theory (disable rational-implies2)) :bash))

(defthm lw-denominator-at-least-one
  (implies (rationalp value) (<= 1 (denominator value)))
  :hints (("Goal" :use ((:instance rational-implies1 (x value))
                        (:instance lw-positive-fuel-at-least-one (fuel (denominator value)))))))

(defthm lw-numerator-upper-bound
  (implies (and (rationalp width) (<= 0 width))
           (<= width (numerator width)))
  :hints (("Goal" :use ((:instance lw-rational-cross-multiply (value width))
                        (:instance lw-denominator-at-least-one (value width))
                        (:instance rational-implies1 (x width)))
                  :in-theory (disable lw-rational-cross-multiply lw-denominator-at-least-one)
                  :nonlinearp t)))

(defthm lw-positive-rational-numerator
  (implies (and (rationalp epsilon) (< 0 epsilon))
           (<= 1 (numerator epsilon)))
  :hints (("Goal" :use ((:instance rational-implies1 (x epsilon))
                        (:instance lw-rational-cross-multiply (value epsilon))
                        (:instance lw-positive-fuel-at-least-one (fuel (numerator epsilon))))
                  :in-theory (disable lw-rational-cross-multiply)
                  :nonlinearp t)))

(defthm lw-precision-fuel-adequate
  (implies (and (rationalp width)
                (rationalp epsilon)
                (<= 0 width)
                (< 0 epsilon))
           (<= width (* (+ 1 (lw-precision-fuel width epsilon)) epsilon)))
  :hints (("Goal" :use ((:instance lw-numerator-upper-bound)
                        (:instance lw-positive-rational-numerator)
                        (:instance lw-rational-cross-multiply (value epsilon))
                        (:instance rational-implies1 (x width))
                        (:instance rational-implies1 (x epsilon)))
                  :in-theory (disable lw-numerator-upper-bound lw-positive-rational-numerator
                                      lw-rational-cross-multiply)
                  :nonlinearp t)))

(defun lw-sqrt-bracket (target lower upper steps)
  (declare (xargs :measure (nfix steps)))
  (if (zp steps)
      (cons lower upper)
    (let ((midpoint (/ (+ lower upper) 2)))
      (if (<= (* midpoint midpoint) target)
          (lw-sqrt-bracket target midpoint upper (- steps 1))
        (lw-sqrt-bracket target lower midpoint (- steps 1))))))

(defun lw-square-bracketp (target bounds)
  (and (rationalp target)
       (lw-intervalp bounds)
       (<= 0 (car bounds))
       (<= (* (car bounds) (car bounds)) target)
       (<= target (* (cdr bounds) (cdr bounds)))))

(defthm lw-sqrt-bracket-refines
  (implies (and (rationalp lower)
                (rationalp upper)
                (<= lower upper))
           (and (lw-intervalp (lw-sqrt-bracket target lower upper steps))
                (<= lower (car (lw-sqrt-bracket target lower upper steps)))
                (<= (cdr (lw-sqrt-bracket target lower upper steps)) upper)))
  :hints (("Goal" :induct (lw-sqrt-bracket target lower upper steps))))

(defthm lw-sqrt-bracket-sound
  (implies (lw-square-bracketp target (cons lower upper))
           (lw-square-bracketp target (lw-sqrt-bracket target lower upper steps)))
  :hints (("Goal" :induct (lw-sqrt-bracket target lower upper steps))))

(defthm lw-sqrt-bracket-width
  (implies (and (rationalp lower) (rationalp upper))
           (equal (- (cdr (lw-sqrt-bracket target lower upper steps))
                     (car (lw-sqrt-bracket target lower upper steps)))
                  (lw-halved-width (- upper lower) steps)))
  :hints (("Goal" :induct (lw-sqrt-bracket target lower upper steps))))

(defun lw-window-bracket (start epsilon)
  (let* ((target (* start start start))
         (upper (* start start))
         (width (- upper start))
         (steps (lw-halving-depth width epsilon (lw-precision-fuel width epsilon))))
    (lw-sqrt-bracket target start upper steps)))

(defthm lw-window-initial-square-bracket
  (implies (and (rationalp start) (<= 1 start))
           (lw-square-bracketp (* start start start) (cons start (* start start))))
  :hints (("Goal" :nonlinearp t)))

(defthm lw-window-bracket-sound
  (implies (and (rationalp start) (<= 1 start))
           (lw-square-bracketp (* start start start) (lw-window-bracket start epsilon)))
  :hints (("Goal" :in-theory (disable lw-square-bracketp lw-sqrt-bracket))))

(defthm lw-window-bracket-contained
  (implies (and (rationalp start) (<= 1 start))
           (and (<= start (car (lw-window-bracket start epsilon)))
                (<= (cdr (lw-window-bracket start epsilon)) (* start start))))
  :hints (("Goal" :in-theory (disable lw-sqrt-bracket lw-halving-depth lw-precision-fuel)
                  :nonlinearp t)))

(defthm lw-window-bracket-width
  (implies (and (rationalp start)
                (<= 1 start)
                (rationalp epsilon)
                (< 0 epsilon))
           (<= (- (cdr (lw-window-bracket start epsilon))
                   (car (lw-window-bracket start epsilon))) epsilon))
  :hints (("Goal" :use ((:instance lw-halving-depth-adequate
                                  (width (- (* start start) start))
                                  (fuel (lw-precision-fuel (- (* start start) start) epsilon)))
                        (:instance lw-precision-fuel-adequate
                                   (width (- (* start start) start))))
                  :in-theory (disable lw-halving-depth lw-precision-fuel lw-halved-width
                                      lw-sqrt-bracket lw-precision-fuel-adequate)
                  :nonlinearp t)))

(defun lw-build-mesh (start endpoint step fuel)
  (declare (xargs :measure (nfix fuel)))
  (if (<= endpoint start)
      (list endpoint)
    (if (or (zp fuel) (<= endpoint (+ start step)))
        (list start endpoint)
      (cons start (lw-build-mesh (+ start step) endpoint step (- fuel 1))))))

(defthm lw-build-mesh-first
  (implies (and (rationalp start) (rationalp endpoint) (<= start endpoint))
           (equal (car (lw-build-mesh start endpoint step fuel)) start)))

(defthm lw-build-mesh-last
  (equal (lw-last-address (lw-build-mesh start endpoint step fuel)) endpoint))

(defthm lw-build-mesh-valid
  (implies (and (rationalp start)
                (rationalp endpoint)
                (rationalp step)
                (< 0 step)
                (<= start endpoint)
                (natp fuel)
                (<= (- endpoint start) (* (+ 1 fuel) step)))
           (lw-meshp (lw-build-mesh start endpoint step fuel) step))
  :hints (("Goal" :induct (lw-build-mesh start endpoint step fuel)
                  :nonlinearp t)))

(defun lw-addresses-between (lower upper addresses)
  (if (endp addresses)
      t
    (and (rationalp (car addresses))
         (<= lower (car addresses))
         (<= (car addresses) upper)
         (lw-addresses-between lower upper (cdr addresses)))))

(defthm lw-build-mesh-contained
  (implies (and (rationalp start)
                (rationalp endpoint)
                (rationalp step)
                (rationalp lower)
                (rationalp upper)
                (<= 0 step)
                (<= lower start)
                (<= start endpoint)
                (<= endpoint upper))
           (lw-addresses-between lower upper (lw-build-mesh start endpoint step fuel)))
  :hints (("Goal" :induct (lw-build-mesh start endpoint step fuel))))

(defun lw-window-mesh (start step)
  (let* ((endpoint (car (lw-window-bracket start step)))
         (width (- endpoint start)))
    (lw-build-mesh start endpoint step (lw-precision-fuel width step))))

(defthm lw-window-mesh-valid
  (implies (and (rationalp start) (<= 1 start) (rationalp step) (< 0 step))
           (lw-meshp (lw-window-mesh start step) step))
  :hints (("Goal" :use ((:instance lw-window-bracket-sound (epsilon step))
                        (:instance lw-window-bracket-contained (epsilon step))
                        (:instance lw-precision-fuel-adequate
                                   (width (- (car (lw-window-bracket start step)) start))
                                   (epsilon step)))
                  :in-theory (disable lw-window-bracket lw-window-bracket-sound
                                      lw-window-bracket-contained lw-build-mesh
                                      lw-precision-fuel lw-precision-fuel-adequate))))

(defthm lw-window-mesh-first
  (implies (and (rationalp start) (<= 1 start))
           (equal (car (lw-window-mesh start step)) start))
  :hints (("Goal" :use ((:instance lw-window-bracket-sound (epsilon step))
                        (:instance lw-window-bracket-contained (epsilon step)))
                  :in-theory (disable lw-window-bracket lw-build-mesh lw-precision-fuel
                                      lw-window-bracket-sound lw-window-bracket-contained))))

(defthm lw-window-mesh-last
  (equal (lw-last-address (lw-window-mesh start step))
         (car (lw-window-bracket start step)))
  :hints (("Goal" :in-theory (disable lw-build-mesh lw-window-bracket lw-precision-fuel))))

(defthm lw-window-mesh-contained
  (implies (and (rationalp start) (<= 1 start) (rationalp step) (< 0 step))
           (lw-addresses-between start (car (lw-window-bracket start step))
                                 (lw-window-mesh start step)))
  :hints (("Goal" :use ((:instance lw-window-bracket-sound (epsilon step))
                        (:instance lw-window-bracket-contained (epsilon step)))
                  :in-theory (disable lw-window-bracket lw-build-mesh lw-precision-fuel
                                      lw-window-bracket-sound lw-window-bracket-contained))))

(defthm lw-last-address-is-member
  (implies (consp addresses) (member-equal (lw-last-address addresses) addresses)))

(defthm lw-member-nearby
  (implies (and (member-equal address addresses)
                (<= (abs (- address point)) step))
           (lw-some-nearby point step addresses)))

(defthm lw-square-bracket-bounds-point
  (implies (and (lw-square-bracketp target bounds)
                (rationalp point)
                (<= 0 point)
                (<= (* point point) target))
           (<= point (cdr bounds)))
  :hints (("Goal" :nonlinearp t)))

(defthm lw-window-mesh-covers-point
  (implies (and (rationalp start)
                (<= 1 start)
                (rationalp step)
                (< 0 step)
                (rationalp point)
                (<= start point)
                (<= (* point point) (* start start start)))
           (lw-some-nearby point step (lw-window-mesh start step)))
  :hints (("Goal" :cases ((<= point (car (lw-window-bracket start step))))
                  :use ((:instance lw-window-mesh-valid)
                        (:instance lw-window-mesh-first)
                        (:instance lw-window-mesh-last)
                        (:instance lw-window-bracket-sound (epsilon step))
                        (:instance lw-window-bracket-contained (epsilon step))
                        (:instance lw-window-bracket-width (epsilon step))
                        (:instance lw-square-bracket-bounds-point
                                   (target (* start start start))
                                   (bounds (lw-window-bracket start step)))
                        (:instance lw-mesh-covers-point
                                   (addresses (lw-window-mesh start step)) (mesh step))
                        (:instance lw-last-address-is-member
                                   (addresses (lw-window-mesh start step)))
                        (:instance lw-member-nearby
                                   (address (car (lw-window-bracket start step)))
                                   (addresses (lw-window-mesh start step))))
                  :in-theory (disable lw-window-mesh lw-window-bracket lw-meshp
                                      lw-window-mesh-valid lw-window-bracket-width
                                      lw-window-bracket-sound lw-window-bracket-contained
                                      lw-square-bracketp lw-square-bracket-bounds-point
                                      lw-some-nearby))))

(defthm lw-window-grid-search-complete
  (implies (and (rationalp start)
                (<= 1 start)
                (rationalp step)
                (< 0 step)
                (rationalp point)
                (<= start point)
                (<= (* point point) (* start start start))
                (rationalp peak)
                (rationalp lipschitz)
                (<= 0 lipschitz)
                (rationalp threshold)
                (rationalp error)
                (< (+ threshold error (* lipschitz step)) peak)
                (lw-lower-lipschitz point peak lipschitz (lw-window-mesh start step) values)
                (lw-encloses-values samples values)
                (lw-widths-at-most error samples))
           (lw-first-above threshold samples))
  :hints (("Goal" :use (lw-window-mesh-covers-point
                        (:instance lw-nearby-forces-large-value
                                   (addresses (lw-window-mesh start step)) (mesh step))
                        lw-search-complete-of-margin)
                  :in-theory (disable lw-window-mesh lw-window-mesh-covers-point
                                      lw-lower-lipschitz lw-encloses-values lw-widths-at-most
                                      lw-some-value-above lw-first-above lw-some-nearby
                                      lw-first-above-complete))))

(assert-event
 (let ((bounds (lw-window-bracket 2 1/1000)))
   (and (lw-square-bracketp 8 bounds)
        (<= (- (cdr bounds) (car bounds)) 1/1000)
        (<= 2 (car bounds))
        (<= (cdr bounds) 4))))

(assert-event
 (let ((addresses (lw-window-mesh 2 1/10)))
   (and (lw-meshp addresses 1/10)
        (equal (car addresses) 2)
        (<= (* (lw-last-address addresses) (lw-last-address addresses)) 8)
        (lw-some-nearby 14/5 1/10 addresses))))
