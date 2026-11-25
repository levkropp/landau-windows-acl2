; Part One teaching examples only. No PA or ACL2 consistency theorem is asserted.
(in-package "ACL2")

(defthm video-natural-successor-nonzero
  (implies (natp n) (not (equal (+ 1 n) 0)))
  :rule-classes nil)

(defthm video-modus-ponens
  (implies (and p (implies p q)) q)
  :rule-classes nil)

(defthm video-explosion
  (implies (and p (not p)) q)
  :rule-classes nil)

(defun video-clock-next (n)
  (mod (+ 1 (nfix n)) 3))

(defthm video-clock-wraps
  (equal (video-clock-next 2) 0)
  :rule-classes nil)

(defun video-digit-listp (digits)
  (if (consp digits)
      (and (natp (car digits)) (< (car digits) 10)
           (video-digit-listp (cdr digits)))
    (equal digits nil)))

(defun video-encode-digits (digits code)
  (if (consp digits)
      (video-encode-digits (cdr digits)
                           (+ (* 10 code) (car digits)))
    code))

(defthm video-encoded-digits-natural
  (implies (and (video-digit-listp digits) (natp code))
           (natp (video-encode-digits digits code)))
  :hints (("Goal" :induct (video-encode-digits digits code)))
  :rule-classes nil)

(defthm video-encoding-example
  (equal (video-encode-digits '(2 0 3) 1) 1203)
  :rule-classes nil)

(assert-event (not (equal (video-clock-next 2) (+ 1 2))))
(assert-event (and (<= 1/2 2/3) (<= 2/3 3/4)))
