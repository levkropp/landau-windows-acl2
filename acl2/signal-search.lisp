(in-package "ACL2")

(include-book "signal-bounds")

(defun lw-signal-addressesp (addresses)
  (if (endp addresses) t
    (and (rationalp (car addresses)) (<= 1 (car addresses))
         (lw-signal-addressesp (cdr addresses)))))

(defun lw-signal-samples (addresses ceiling numerator denominator error)
  (if (endp addresses) nil
    (cons (lw-signal-bounds (car addresses) ceiling numerator denominator error)
          (lw-signal-samples (cdr addresses) ceiling numerator denominator error))))

(defun lw-intervalsp (samples)
  (if (endp samples) t
    (and (lw-intervalp (car samples)) (lw-intervalsp (cdr samples)))))

(defthm lw-signal-samples-length
  (equal (len (lw-signal-samples addresses ceiling numerator denominator error)) (len addresses)))

(defthm lw-signal-samples-valid
  (implies (and (lw-signal-addressesp addresses)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp error) (< 0 error))
           (lw-intervalsp (lw-signal-samples addresses ceiling numerator denominator error)))
  :hints (("Goal" :induct (lw-signal-samples addresses ceiling numerator denominator error)
                  :in-theory (disable lw-signal-bounds lw-intervalp))))

(defthm lw-signal-samples-widths
  (implies (and (lw-signal-addressesp addresses)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp error) (< 0 error))
           (lw-widths-at-most error (lw-signal-samples addresses ceiling numerator denominator error)))
  :hints (("Goal" :induct (lw-signal-samples addresses ceiling numerator denominator error)
                  :in-theory (disable lw-signal-bounds))
          (and stable-under-simplificationp
               '(:use ((:instance lw-signal-bounds-width (value (car addresses))))
                 :in-theory (e/d (lw-interval-width) (lw-signal-bounds lw-signal-bounds-width))))))

(defun lw-upper-values (samples)
  (if (endp samples) nil (cons (cdar samples) (lw-upper-values (cdr samples)))))

(defthm lw-encloses-upper-values
  (implies (lw-intervalsp samples) (lw-encloses-values samples (lw-upper-values samples))))

(defthm lw-signal-samples-nth
  (implies (and (natp index) (< index (len addresses)))
           (equal (nth index (lw-signal-samples addresses ceiling numerator denominator error))
                  (lw-signal-bounds (nth index addresses) ceiling numerator denominator error)))
  :hints (("Goal" :induct (nth index addresses)
                  :in-theory (disable lw-signal-bounds))))

(defthm lw-addresses-between-nth
  (implies (and (lw-addresses-between lower upper addresses)
                (natp index) (< index (len addresses)))
           (and (rationalp (nth index addresses))
                (<= lower (nth index addresses)) (<= (nth index addresses) upper)))
  :hints (("Goal" :induct (nth index addresses))))

(defthm lw-addresses-between-signal-addresses
  (implies (and (rationalp lower) (<= 1 lower)
                (lw-addresses-between lower upper addresses))
           (lw-signal-addressesp addresses)))

(defun lw-signal-search (addresses ceiling numerator denominator error)
  (lw-first-above 0 (lw-signal-samples addresses ceiling numerator denominator error)))

(defthm lw-signal-search-certificate
  (implies (lw-signal-search addresses ceiling numerator denominator error)
           (let ((found (lw-signal-search addresses ceiling numerator denominator error)))
             (and (natp (car found)) (< (car found) (len addresses))
                  (< 0 (cadr found))
                  (equal (cdr found)
                         (lw-signal-bounds (nth (car found) addresses)
                                            ceiling numerator denominator error)))))
  :hints (("Goal" :use ((:instance lw-first-above-index-natural
                          (threshold 0) (samples (lw-signal-samples addresses ceiling numerator denominator error)))
                        (:instance lw-first-above-index-bound
                          (threshold 0) (samples (lw-signal-samples addresses ceiling numerator denominator error)))
                        (:instance lw-first-above-lower-gt
                          (threshold 0) (samples (lw-signal-samples addresses ceiling numerator denominator error)))
                        (:instance lw-first-above-nth
                          (threshold 0) (samples (lw-signal-samples addresses ceiling numerator denominator error))))
                  :in-theory (disable lw-first-above lw-signal-samples lw-signal-bounds
                                      lw-first-above-nth lw-first-above-lower-gt
                                      lw-first-above-index-bound lw-first-above-index-natural))))

(defun lw-window-signal-search (start step ceiling numerator denominator error)
  (lw-signal-search (lw-window-mesh start step) ceiling numerator denominator error))

(defun lw-window-signal-address (start step found)
  (nth (car found) (lw-window-mesh start step)))

(defthm lw-window-signal-search-certificate
  (implies (and (rationalp start) (<= 1 start)
                (rationalp step) (< 0 step)
                (lw-window-signal-search start step ceiling numerator denominator error))
           (let* ((found (lw-window-signal-search start step ceiling numerator denominator error))
                  (address (lw-window-signal-address start step found)))
             (and (rationalp address) (<= start address)
                  (<= (* address address) (* start start start))
                  (< 0 (cadr found))
                  (equal (cdr found) (lw-signal-bounds address ceiling numerator denominator error)))))
  :hints (("Goal" :use ((:instance lw-signal-search-certificate
                          (addresses (lw-window-mesh start step)))
                        lw-window-mesh-contained
                        (:instance lw-window-bracket-sound (epsilon step))
                        (:instance lw-addresses-between-nth
                          (lower start) (upper (car (lw-window-bracket start step)))
                          (addresses (lw-window-mesh start step))
                          (index (car (lw-window-signal-search start step ceiling numerator denominator error)))))
                  :in-theory (disable lw-signal-search lw-signal-search-certificate
                                      lw-window-mesh lw-window-mesh-contained lw-window-bracket
                                      lw-window-bracket-sound lw-square-bracketp
                                      lw-addresses-between-nth lw-signal-bounds)
                  :nonlinearp t)
          (and stable-under-simplificationp
               '(:in-theory (enable lw-square-bracketp) :nonlinearp t))))

; Only the finite upper-transport/peak condition remains here. Sample
; construction, enclosure validity and precision are now discharged.
; The analytic Landau argument must still derive this condition.
(defthm lw-window-signal-search-complete
  (implies (and (rationalp start) (<= 1 start) (rationalp step) (< 0 step)
                (rationalp ceiling) (<= 0 ceiling)
                (natp numerator) (posp denominator) (<= numerator denominator)
                (rationalp error) (< 0 error)
                (rationalp point) (<= start point)
                (<= (* point point) (* start start start))
                (rationalp peak) (rationalp lipschitz) (<= 0 lipschitz)
                (< (+ error (* lipschitz step)) peak)
                (lw-lower-lipschitz
                 point peak lipschitz (lw-window-mesh start step)
                 (lw-upper-values (lw-signal-samples (lw-window-mesh start step)
                                                    ceiling numerator denominator error))))
           (lw-window-signal-search start step ceiling numerator denominator error))
  :hints (("Goal" :use ((:instance lw-window-grid-search-complete
                          (threshold 0)
                          (samples (lw-signal-samples (lw-window-mesh start step)
                                                      ceiling numerator denominator error))
                          (values (lw-upper-values
                                   (lw-signal-samples (lw-window-mesh start step)
                                                     ceiling numerator denominator error))))
                        (:instance lw-signal-samples-valid (addresses (lw-window-mesh start step)))
                        (:instance lw-signal-samples-widths (addresses (lw-window-mesh start step)))
                        (:instance lw-encloses-upper-values
                          (samples (lw-signal-samples (lw-window-mesh start step)
                                                      ceiling numerator denominator error)))
                        lw-window-mesh-contained
                        (:instance lw-addresses-between-signal-addresses
                          (lower start) (upper (car (lw-window-bracket start step)))
                          (addresses (lw-window-mesh start step))))
                  :in-theory (disable lw-first-above lw-window-mesh lw-window-bracket
                                      lw-signal-samples lw-upper-values lw-encloses-values
                                      lw-widths-at-most lw-lower-lipschitz lw-signal-addressesp
                                      lw-intervalsp lw-window-grid-search-complete
                                      lw-signal-samples-valid lw-signal-samples-widths
                                      lw-encloses-upper-values lw-window-mesh-contained
                                      lw-addresses-between-signal-addresses))))

(assert-event (let* ((found (lw-window-signal-search 1 1/2 1 1 2 1))
                     (address (lw-window-signal-address 1 1/2 found)))
                (and found (equal address 1) (< 0 (cadr found)))))
