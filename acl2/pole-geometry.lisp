(in-package "ACL2")

(include-book "rational-window")

(local
 (defthm lw-geometry-product-commutes
   (equal (* left (* middle right)) (* middle (* left right)))
   :hints (("Goal" :use ((:instance associativity-of-* (x left) (y middle) (z right))
                        (:instance associativity-of-* (x middle) (y left) (z right))
                        (:instance commutativity-of-* (x left) (y middle)))
                   :in-theory (disable associativity-of-* commutativity-of-*)))))

(local
 (defthm lw-inverse-pair
   (implies (and (rationalp divisor) (not (equal divisor 0)))
            (equal (* (/ divisor) divisor) 1))))

(local
 (defthm lw-quotient-cancels
   (implies (and (rationalp divisor) (not (equal divisor 0)) (rationalp coefficient))
            (equal (* (/ divisor) (* divisor coefficient)) coefficient))
   :hints (("Goal" :use ((:instance associativity-of-* (x (/ divisor))
                                    (y divisor) (z coefficient)))
                   :in-theory (disable associativity-of-* commutativity-of-*
                                       lw-geometry-product-commutes)))))

(local
 (defthm lw-negated-right-factor
   (implies (and (rationalp left) (rationalp right))
            (equal (* left (- right)) (- (* left right))))
   :hints (("Goal" :use ((:instance distributivity (x left) (y right) (z (- right))))
                   :in-theory (disable distributivity)))))

(local
 (defthm lw-negated-left-factor
   (implies (and (rationalp left) (rationalp right))
            (equal (* (- left) right) (- (* left right))))))

(local
 (defthm lw-square-nonnegative
   (implies (rationalp value) (<= 0 (* value value)))
   :hints (("Goal" :nonlinearp t))))

(defun lw-avoid-height-interval (lower upper forbidden)
  (declare (xargs :measure (acl2-count forbidden)))
  (if (endp forbidden)
      (cons lower upper)
    (let ((midpoint (/ (+ lower upper) 2)))
      (if (<= (car forbidden) midpoint)
          (lw-avoid-height-interval midpoint upper (cdr forbidden))
        (lw-avoid-height-interval lower midpoint (cdr forbidden))))))

(defun lw-outside-height-interval (bounds forbidden)
  (if (endp forbidden)
      t
    (and (or (<= (car forbidden) (car bounds))
             (<= (cdr bounds) (car forbidden)))
         (lw-outside-height-interval bounds (cdr forbidden)))))

(defthm lw-avoid-height-interval-refines
  (implies (and (rationalp lower) (rationalp upper) (< lower upper))
           (and (rationalp (car (lw-avoid-height-interval lower upper forbidden)))
                (rationalp (cdr (lw-avoid-height-interval lower upper forbidden)))
                (<= lower (car (lw-avoid-height-interval lower upper forbidden)))
                (< (car (lw-avoid-height-interval lower upper forbidden))
                   (cdr (lw-avoid-height-interval lower upper forbidden)))
                (<= (cdr (lw-avoid-height-interval lower upper forbidden)) upper)))
  :hints (("Goal" :induct (lw-avoid-height-interval lower upper forbidden))))

(defthm lw-outside-height-interval-refines
  (implies (and (lw-outside-height-interval outer forbidden)
                (<= (car outer) (car inner))
                (<= (cdr inner) (cdr outer)))
           (lw-outside-height-interval inner forbidden)))

(defthm lw-avoid-height-interval-excludes
  (implies (and (rationalp lower) (rationalp upper) (< lower upper))
           (lw-outside-height-interval
            (lw-avoid-height-interval lower upper forbidden) forbidden))
  :hints (("Goal" :induct (lw-avoid-height-interval lower upper forbidden))
          (and stable-under-simplificationp
               '(:use ((:instance lw-avoid-height-interval-refines
                                  (lower (/ (+ lower upper) 2))
                                  (forbidden (cdr forbidden)))
                       (:instance lw-avoid-height-interval-refines
                                  (upper (/ (+ lower upper) 2))
                                  (forbidden (cdr forbidden))))
                 :in-theory (disable lw-avoid-height-interval-refines)))))

(defun lw-chosen-height (lower upper forbidden)
  (let ((bounds (lw-avoid-height-interval lower upper forbidden)))
    (/ (+ (car bounds) (cdr bounds)) 2)))

(defthm lw-chosen-height-between
  (implies (and (rationalp lower) (rationalp upper) (< lower upper))
           (and (rationalp (lw-chosen-height lower upper forbidden))
                (< lower (lw-chosen-height lower upper forbidden))
                (< (lw-chosen-height lower upper forbidden) upper)))
  :hints (("Goal" :use (lw-avoid-height-interval-refines)
                  :in-theory (disable lw-avoid-height-interval
                                      lw-avoid-height-interval-refines))))

(defthm lw-outside-height-interval-not-member
  (implies (and (lw-outside-height-interval bounds forbidden)
                (rationalp height)
                (< (car bounds) height)
                (< height (cdr bounds)))
           (not (member-equal height forbidden))))

(defthm lw-chosen-height-avoids
  (implies (and (rationalp lower) (rationalp upper) (< lower upper))
           (not (member-equal (lw-chosen-height lower upper forbidden) forbidden)))
  :hints (("Goal" :use (lw-avoid-height-interval-refines
                        lw-avoid-height-interval-excludes
                        (:instance lw-outside-height-interval-not-member
                                   (bounds (lw-avoid-height-interval lower upper forbidden))
                                   (height (lw-chosen-height lower upper forbidden))))
                  :in-theory (disable lw-avoid-height-interval lw-avoid-height-interval-refines
                                      lw-avoid-height-interval-excludes
                                      lw-outside-height-interval))))

(defun lw-plane-pointp (point)
  (and (consp point) (rationalp (car point)) (rationalp (cdr point))))

(defun lw-distance-squared (sigma height point)
  (+ (* (- sigma (car point)) (- sigma (car point)))
     (* (- height (cdr point)) (- height (cdr point)))))

(defun lw-tie-numerator (sigma left right)
  (+ (- (* (- sigma (car left)) (- sigma (car left)))
         (* (- sigma (car right)) (- sigma (car right))))
     (- (* (cdr left) (cdr left)) (* (cdr right) (cdr right)))))

(defun lw-tie-denominator (left right)
  (* 2 (- (cdr left) (cdr right))))

(defun lw-tie-height (sigma left right)
  (let ((denominator (lw-tie-denominator left right)))
    (if (equal denominator 0)
        0
      (/ (lw-tie-numerator sigma left right) denominator))))

(defthm lw-tie-denominator-rational
  (implies (and (lw-plane-pointp left) (lw-plane-pointp right))
           (rationalp (lw-tie-denominator left right)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-tie-numerator-rational
  (implies (and (rationalp sigma) (lw-plane-pointp left) (lw-plane-pointp right))
           (rationalp (lw-tie-numerator sigma left right)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-tie-denominator-nonzero
  (implies (and (lw-plane-pointp left) (lw-plane-pointp right)
                (not (equal (cdr left) (cdr right))))
           (not (equal (lw-tie-denominator left right) 0))))

(defthm lw-equidistant-numerator
  (implies (and (rationalp sigma)
                (rationalp height)
                (lw-plane-pointp left)
                (lw-plane-pointp right)
                (equal (lw-distance-squared sigma height left)
                       (lw-distance-squared sigma height right)))
           (equal (lw-tie-numerator sigma left right)
                  (* (lw-tie-denominator left right) height)))
  :hints (("Goal" :nonlinearp t))
  :rule-classes nil)

(defthm lw-equidistant-tie-height
  (implies (and (rationalp sigma)
                (rationalp height)
                (lw-plane-pointp left)
                (lw-plane-pointp right)
                (not (equal (cdr left) (cdr right)))
                (equal (lw-distance-squared sigma height left)
                       (lw-distance-squared sigma height right)))
           (equal (lw-tie-height sigma left right) height))
  :hints (("Goal" :use (lw-equidistant-numerator
                        (:instance lw-quotient-cancels
                                   (divisor (lw-tie-denominator left right))
                                   (coefficient height)))
                  :in-theory (disable lw-tie-numerator lw-tie-denominator lw-distance-squared
                                      lw-quotient-cancels distributivity)))
  :rule-classes nil)

(defthm lw-equal-distances-force-same-point
  (implies (and (rationalp sigma)
                (rationalp height)
                (lw-plane-pointp left)
                (lw-plane-pointp right)
                (< (car left) sigma)
                (< (car right) sigma)
                (equal (lw-distance-squared sigma height left)
                       (lw-distance-squared sigma height right))
                (not (equal height (lw-tie-height sigma left right))))
           (equal left right))
  :hints (("Goal" :cases ((equal (cdr left) (cdr right)))
                  :use (lw-equidistant-tie-height)
                  :in-theory (disable lw-tie-height)
                  :nonlinearp t))
  :rule-classes nil)

(defun lw-tie-heights-with (sigma point points)
  (if (endp points)
      nil
    (cons (lw-tie-height sigma point (car points))
          (lw-tie-heights-with sigma point (cdr points)))))

(defun lw-all-tie-heights (sigma rows columns)
  (if (endp rows)
      nil
    (append (lw-tie-heights-with sigma (car rows) columns)
            (lw-all-tie-heights sigma (cdr rows) columns))))

(defthm lw-tie-heights-with-member
  (implies (member-equal other points)
           (member-equal (lw-tie-height sigma point other)
                         (lw-tie-heights-with sigma point points)))
  :hints (("Goal" :in-theory (disable lw-tie-height))))

(defthm lw-member-of-append-left
  (implies (member-equal value left) (member-equal value (append left right))))

(defthm lw-member-of-append-right
  (implies (member-equal value right) (member-equal value (append left right))))

(defthm lw-all-tie-heights-member
  (implies (and (member-equal left rows) (member-equal right columns))
           (member-equal (lw-tie-height sigma left right)
                         (lw-all-tie-heights sigma rows columns)))
  :hints (("Goal" :induct (lw-all-tie-heights sigma rows columns)
                  :in-theory (disable lw-tie-height))))

(defun lw-points-left-of (sigma points)
  (if (endp points)
      t
    (and (lw-plane-pointp (car points))
         (< (caar points) sigma)
         (lw-points-left-of sigma (cdr points)))))

(defthm lw-points-left-member
  (implies (and (lw-points-left-of sigma points) (member-equal point points))
           (and (lw-plane-pointp point) (< (car point) sigma))))

(defun lw-separating-height (sigma lower upper points)
  (lw-chosen-height lower upper (lw-all-tie-heights sigma points points)))

(defthm lw-separating-height-between
  (implies (and (rationalp lower) (rationalp upper) (< lower upper))
           (and (rationalp (lw-separating-height sigma lower upper points))
                (< lower (lw-separating-height sigma lower upper points))
                (< (lw-separating-height sigma lower upper points) upper)))
  :hints (("Goal" :in-theory (disable lw-chosen-height lw-all-tie-heights))))

(defthm lw-separating-height-injective
  (implies (and (rationalp sigma)
                (rationalp lower)
                (rationalp upper)
                (< lower upper)
                (lw-points-left-of sigma points)
                (member-equal left points)
                (member-equal right points)
                (equal (lw-distance-squared sigma (lw-separating-height sigma lower upper points) left)
                       (lw-distance-squared sigma (lw-separating-height sigma lower upper points) right)))
           (equal left right))
  :hints (("Goal" :use ((:instance lw-chosen-height-avoids
                                   (forbidden (lw-all-tie-heights sigma points points)))
                        (:instance lw-all-tie-heights-member (rows points) (columns points))
                        (:instance lw-points-left-member (point left))
                        (:instance lw-points-left-member (point right))
                        lw-separating-height-between
                        (:instance lw-equal-distances-force-same-point
                                   (height (lw-separating-height sigma lower upper points))))
                  :in-theory (disable lw-chosen-height lw-all-tie-heights
                                      lw-chosen-height-avoids lw-all-tie-heights-member
                                      lw-points-left-of lw-points-left-member lw-plane-pointp
                                      lw-distance-squared lw-tie-height
                                      lw-separating-height-between)))
  :rule-classes nil)

(defthm lw-distance-squared-rational
  (implies (and (rationalp sigma) (rationalp height) (lw-plane-pointp point))
           (rationalp (lw-distance-squared sigma height point)))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-distance-squared-nonnegative
  (implies (and (rationalp sigma) (rationalp height) (lw-plane-pointp point))
           (<= 0 (lw-distance-squared sigma height point)))
  :hints (("Goal" :use ((:instance lw-square-nonnegative (value (- sigma (car point))))
                        (:instance lw-square-nonnegative (value (- height (cdr point)))))
                  :in-theory (disable distributivity lw-square-nonnegative))))

(defun lw-nearest-point (sigma height points)
  (if (consp (cdr points))
      (let ((competitor (lw-nearest-point sigma height (cdr points))))
        (if (<= (lw-distance-squared sigma height (car points))
                (lw-distance-squared sigma height competitor))
            (car points)
          competitor))
    (car points)))

(defthm lw-nearest-point-member
  (implies (consp points) (member-equal (lw-nearest-point sigma height points) points)))

(defthm lw-nearest-point-minimizes
  (implies (and (rationalp sigma)
                (rationalp height)
                (lw-points-left-of sigma points)
                (member-equal point points))
           (<= (lw-distance-squared sigma height (lw-nearest-point sigma height points))
               (lw-distance-squared sigma height point)))
  :hints (("Goal" :induct (lw-nearest-point sigma height points)
                  :in-theory (disable lw-distance-squared))))

(defun lw-other-points (selected points)
  (if (endp points)
      nil
    (if (equal selected (car points))
        (lw-other-points selected (cdr points))
      (cons (car points) (lw-other-points selected (cdr points))))))

(defthm lw-other-points-member
  (iff (member-equal point (lw-other-points selected points))
       (and (member-equal point points) (not (equal point selected)))))

(defthm lw-other-points-preserve-left
  (implies (lw-points-left-of sigma points)
           (lw-points-left-of sigma (lw-other-points selected points))))

(defthm lw-separated-nearest-strict
  (implies (and (rationalp sigma)
                (rationalp lower)
                (rationalp upper)
                (< lower upper)
                (consp points)
                (lw-points-left-of sigma points)
                (member-equal point points)
                (not (equal point
                            (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points))))
           (< (lw-distance-squared sigma (lw-separating-height sigma lower upper points)
                                   (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points))
              (lw-distance-squared sigma (lw-separating-height sigma lower upper points) point)))
  :hints (("Goal" :use (lw-separating-height-between
                        (:instance lw-nearest-point-member
                                   (height (lw-separating-height sigma lower upper points)))
                        (:instance lw-nearest-point-minimizes
                                   (height (lw-separating-height sigma lower upper points)))
                        (:instance lw-points-left-member
                                   (point (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points)))
                        lw-points-left-member
                        (:instance lw-separating-height-injective
                                   (left (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points))
                                   (right point)))
                  :in-theory (disable lw-distance-squared lw-nearest-point lw-separating-height
                                      lw-points-left-of lw-points-left-member
                                      lw-separating-height-between lw-nearest-point-minimizes
                                      lw-nearest-point-member)))
  :rule-classes nil)

(defun lw-isolating-radius-squared (sigma height selected points cap)
  (let* ((others (lw-other-points selected points))
         (outer (if (consp others)
                    (min cap (lw-distance-squared sigma height
                                                 (lw-nearest-point sigma height others)))
                  cap)))
    (/ (+ (lw-distance-squared sigma height selected) outer) 2)))

(defthm lw-isolating-circle-correct
  (implies (and (rationalp sigma)
                (rationalp lower)
                (rationalp upper)
                (< lower upper)
                (rationalp cap)
                (consp points)
                (lw-points-left-of sigma points)
                (member-equal point points)
                (< (lw-distance-squared sigma (lw-separating-height sigma lower upper points)
                                        (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points))
                   cap))
           (let* ((height (lw-separating-height sigma lower upper points))
                  (selected (lw-nearest-point sigma height points))
                  (radius (lw-isolating-radius-squared sigma height selected points cap)))
             (and (< 0 radius)
                  (< (lw-distance-squared sigma height selected) radius)
                  (< radius cap)
                  (or (equal point selected)
                      (< radius (lw-distance-squared sigma height point))))))
  :hints (("Goal" :do-not-induct t
                  :use (lw-separating-height-between
                        (:instance lw-nearest-point-member
                                   (height (lw-separating-height sigma lower upper points)))
                        (:instance lw-nearest-point-member
                                   (height (lw-separating-height sigma lower upper points))
                                   (points (lw-other-points
                                            (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points)
                                            points)))
                        (:instance lw-separated-nearest-strict
                                   (point (lw-nearest-point
                                           sigma (lw-separating-height sigma lower upper points)
                                           (lw-other-points
                                            (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points)
                                            points))))
                        (:instance lw-nearest-point-minimizes
                                   (height (lw-separating-height sigma lower upper points))
                                   (points (lw-other-points
                                            (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points)
                                            points)))
                        (:instance lw-points-left-member
                                   (point (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points)))
                        (:instance lw-points-left-member
                                   (point (lw-nearest-point
                                           sigma (lw-separating-height sigma lower upper points)
                                           (lw-other-points
                                            (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points)
                                            points))))
                        (:instance lw-other-points-member
                                   (selected (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points)))
                        (:instance lw-other-points-member
                                   (selected (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points))
                                   (point (lw-nearest-point sigma (lw-separating-height sigma lower upper points)
                                                           (lw-other-points
                                                            (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points)
                                                            points))))
                        (:instance lw-other-points-preserve-left
                                   (selected (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points)))
                        (:instance lw-distance-squared-nonnegative
                                   (height (lw-separating-height sigma lower upper points))
                                   (point (lw-nearest-point sigma (lw-separating-height sigma lower upper points) points))))
                  :in-theory (disable lw-distance-squared lw-nearest-point lw-separating-height
                                      lw-other-points lw-points-left-of lw-points-left-member
                                      lw-separating-height-between lw-nearest-point-minimizes
                                      lw-nearest-point-member lw-distance-squared-nonnegative
                                      lw-other-points-member lw-other-points-preserve-left))))

(assert-event
 (let* ((forbidden '(1/2 3/4 7/8 15/16))
        (height (lw-chosen-height 0 1 forbidden)))
   (and (rationalp height) (< 0 height) (< height 1)
        (not (member-equal height forbidden)))))

(assert-event
 (let* ((points '((3/5 . 1) (3/5 . -1)))
        (height (lw-separating-height 2 -1 1 points))
        (selected (lw-nearest-point 2 height points))
        (radius (lw-isolating-radius-squared 2 height selected points 4)))
   (and (< -1 height) (< height 1)
        (not (equal (lw-distance-squared 2 height (car points))
                    (lw-distance-squared 2 height (cadr points))))
        (< (lw-distance-squared 2 height selected) radius)
        (< radius 4)
        (< radius (lw-distance-squared 2 height (car (lw-other-points selected points)))))))

(assert-event
 (let* ((points '((3/5 . 1) (3/5 . 1)))
        (height (lw-separating-height 2 0 2 points))
        (selected (lw-nearest-point 2 height points))
        (radius (lw-isolating-radius-squared 2 height selected points 4)))
   (and (not (lw-other-points selected points))
        (< (lw-distance-squared 2 height selected) radius)
        (< radius 4))))
