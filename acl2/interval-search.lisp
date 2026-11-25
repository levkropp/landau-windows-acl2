(in-package "ACL2")

(defun lw-intervalp (bounds)
  (and (consp bounds)
       (rationalp (car bounds))
       (rationalp (cdr bounds))
       (<= (car bounds) (cdr bounds))))

(defun lw-contains (bounds value)
  (and (lw-intervalp bounds)
       (rationalp value)
       (<= (car bounds) value)
       (<= value (cdr bounds))))

(defun lw-interval-add (left right)
  (cons (+ (car left) (car right))
        (+ (cdr left) (cdr right))))

(defun lw-interval-sub (left right)
  (cons (- (car left) (cdr right))
        (- (cdr left) (car right))))

(defun lw-interval-scale (coefficient bounds)
  (if (<= 0 coefficient)
      (cons (* coefficient (car bounds)) (* coefficient (cdr bounds)))
    (cons (* coefficient (cdr bounds)) (* coefficient (car bounds)))))

(defthm lw-contains-add
  (implies (and (lw-contains left left-value)
                (lw-contains right right-value))
           (lw-contains (lw-interval-add left right) (+ left-value right-value))))

(defthm lw-contains-sub
  (implies (and (lw-contains left left-value)
                (lw-contains right right-value))
           (lw-contains (lw-interval-sub left right) (- left-value right-value))))

(defthm lw-contains-scale
  (implies (and (rationalp coefficient) (lw-contains bounds value))
           (lw-contains (lw-interval-scale coefficient bounds) (* coefficient value)))
  :hints (("Goal" :nonlinearp t)))

(defthm lw-lower-gt-of-margin
  (implies (and (lw-contains bounds value)
                (rationalp threshold)
                (rationalp error)
                (<= (- (cdr bounds) (car bounds)) error)
                (< (+ threshold error) value))
           (< threshold (car bounds))))

(defun lw-first-above (threshold samples)
  (if (endp samples)
      nil
    (if (< threshold (caar samples))
        (cons 0 (car samples))
      (let ((found (lw-first-above threshold (cdr samples))))
        (if found (cons (+ 1 (car found)) (cdr found)) nil)))))

(defun lw-some-lower-above (threshold samples)
  (if (endp samples)
      nil
    (or (< threshold (caar samples))
        (lw-some-lower-above threshold (cdr samples)))))

(defthm lw-first-above-complete
  (iff (lw-first-above threshold samples)
       (lw-some-lower-above threshold samples)))

(defthm lw-first-above-lower-gt
  (implies (lw-first-above threshold samples)
           (< threshold (cadr (lw-first-above threshold samples)))))

(defthm lw-first-above-index-natural
  (implies (lw-first-above threshold samples)
           (natp (car (lw-first-above threshold samples))))
  :rule-classes (:rewrite :type-prescription))

(defthm lw-first-above-index-bound
  (implies (lw-first-above threshold samples)
           (< (car (lw-first-above threshold samples)) (len samples))))

(defthm lw-first-above-nth
  (implies (lw-first-above threshold samples)
           (equal (cdr (lw-first-above threshold samples))
                  (nth (car (lw-first-above threshold samples)) samples)))
  :hints (("Goal" :induct (lw-first-above threshold samples)
                  :in-theory (disable lw-first-above-complete))))

(defun lw-encloses-values (samples values)
  (if (endp samples)
      (endp values)
    (and (consp values)
         (lw-contains (car samples) (car values))
         (lw-encloses-values (cdr samples) (cdr values)))))

(defun lw-widths-at-most (error samples)
  (if (endp samples)
      t
    (and (<= (- (cdar samples) (caar samples)) error)
         (lw-widths-at-most error (cdr samples)))))

(defun lw-some-value-above (threshold values)
  (if (endp values)
      nil
    (or (< threshold (car values))
        (lw-some-value-above threshold (cdr values)))))

(defthm lw-first-above-value-gt
  (implies (and (rationalp threshold)
                (lw-encloses-values samples values)
                (lw-first-above threshold samples))
           (< threshold (nth (car (lw-first-above threshold samples)) values)))
  :hints (("Goal" :induct (lw-encloses-values samples values)
                  :in-theory (disable lw-first-above-complete))))

(defthm lw-search-complete-of-margin
  (implies (and (rationalp threshold)
                (rationalp error)
                (lw-encloses-values samples values)
                (lw-widths-at-most error samples)
                (lw-some-value-above (+ threshold error) values))
           (lw-first-above threshold samples)))

(assert-event (equal (lw-first-above 0 '((-1 . 0) (1/4 . 1/2)))
                     '(1 1/4 . 1/2)))

(assert-event (not (lw-first-above 0 '((-1 . 0) (-2 . -1)))))
