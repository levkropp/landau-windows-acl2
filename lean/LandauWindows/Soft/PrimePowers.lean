import LandauWindows.Soft.LogBounds

/-! The natural-number interpretation of `acl2/prime-powers.lisp`.
The bounded searches do not assume a primality or prime-power oracle. -/

namespace LandauWindows.CertificateGeometry

def noDivisor (value : ℕ) : ℕ → Bool
  | 0 => true
  | trial + 1 =>
      if trial + 1 < 2 then true
      else decide (value % (trial + 1) ≠ 0) && noDivisor value trial

theorem noDivisor_iff (value trial : ℕ) : noDivisor value trial = true ↔
    ∀ divisor : ℕ, 2 ≤ divisor → divisor ≤ trial → ¬divisor ∣ value := by
  induction trial with
  | zero => simp [noDivisor]; omega
  | succ trial ih =>
      by_cases hsmall : trial + 1 < 2
      · simp [noDivisor, hsmall]
        omega
      · simp only [noDivisor, hsmall, if_false, Bool.and_eq_true, decide_eq_true_eq, ih]
        constructor
        · rintro ⟨hcurrent, hprevious⟩ divisor hdiv hbound
          by_cases heq : divisor = trial + 1
          · subst divisor; simpa only [Nat.dvd_iff_mod_eq_zero] using hcurrent
          · exact hprevious divisor hdiv (by omega)
        · intro h
          exact ⟨by simpa only [Nat.dvd_iff_mod_eq_zero] using h (trial + 1) (by omega) le_rfl,
            fun divisor hdiv hbound => h divisor hdiv (by omega)⟩

def primeTest (value : ℕ) : Bool := decide (2 ≤ value) && noDivisor value (value - 1)

theorem primeTest_iff (value : ℕ) : primeTest value = true ↔ Nat.Prime value := by
  simp only [primeTest, Bool.and_eq_true, decide_eq_true_eq, noDivisor_iff, Nat.prime_def_lt']
  constructor
  · rintro ⟨hsize, hdiv⟩
    exact ⟨hsize, fun divisor hsmall hlarge => hdiv divisor hsmall (by omega)⟩
  · rintro ⟨hsize, hdiv⟩
    exact ⟨hsize, fun divisor hsmall hlarge => hdiv divisor hsmall (by omega)⟩

def powerExponent (value base : ℕ) : ℕ → Option ℕ
  | 0 => none
  | limit + 1 => if base ^ (limit + 1) = value then some (limit + 1)
      else powerExponent value base limit

theorem powerExponent_sound (value base limit exponent : ℕ)
    (hfound : powerExponent value base limit = some exponent) :
    0 < exponent ∧ exponent ≤ limit ∧ base ^ exponent = value := by
  induction limit with
  | zero => simp [powerExponent] at hfound
  | succ limit ih =>
      simp only [powerExponent] at hfound
      split_ifs at hfound with hpower
      · have heq : limit + 1 = exponent := Option.some.inj hfound
        subst exponent
        exact ⟨by omega, le_rfl, hpower⟩
      · rcases ih hfound with ⟨hpos, hbound, hpower⟩
        exact ⟨hpos, by omega, hpower⟩

theorem powerExponent_complete (value base limit exponent : ℕ)
    (hpos : 0 < exponent) (hbound : exponent ≤ limit) (hpower : base ^ exponent = value) :
    ∃ found, powerExponent value base limit = some found := by
  induction limit with
  | zero => omega
  | succ limit ih =>
      dsimp only [powerExponent]
      split_ifs with hcurrent
      · exact ⟨limit + 1, rfl⟩
      · apply ih
        by_contra h
        have heq : exponent = limit + 1 := by omega
        apply hcurrent
        simpa [heq] using hpower

def primePowerSearch (value : ℕ) : ℕ → Option (ℕ × ℕ)
  | 0 => none
  | candidate + 1 =>
      if candidate + 1 < 2 then none
      else if primeTest (candidate + 1) then
        match powerExponent value (candidate + 1) value with
        | some exponent => some (candidate + 1, exponent)
        | none => primePowerSearch value candidate
      else primePowerSearch value candidate

theorem primePowerSearch_sound (value candidate base exponent : ℕ)
    (hfound : primePowerSearch value candidate = some (base, exponent)) :
    Nat.Prime base ∧ base ≤ candidate ∧ 0 < exponent ∧ exponent ≤ value ∧ base ^ exponent = value := by
  induction candidate with
  | zero => simp [primePowerSearch] at hfound
  | succ candidate ih =>
      simp only [primePowerSearch] at hfound
      split_ifs at hfound with hsmall hprime
      · split at hfound
        next found hpower =>
          have heq : (candidate + 1, found) = (base, exponent) := Option.some.inj hfound
          have hb := congrArg Prod.fst heq
          have he := congrArg Prod.snd heq
          change candidate + 1 = base at hb
          change found = exponent at he
          rw [← hb, ← he]
          exact ⟨(primeTest_iff _).mp hprime, le_rfl,
            powerExponent_sound value (candidate + 1) value found hpower⟩
        next hnone =>
          rcases ih hfound with ⟨hp, hb, he⟩
          exact ⟨hp, by omega, he⟩
      · rcases ih hfound with ⟨hp, hb, he⟩
        exact ⟨hp, by omega, he⟩

theorem primePowerSearch_complete (value candidate base exponent : ℕ)
    (hprime : Nat.Prime base) (hbase : base ≤ candidate)
    (hpos : 0 < exponent) (hexponent : exponent ≤ value) (hpower : base ^ exponent = value) :
    ∃ found, primePowerSearch value candidate = some found := by
  induction candidate with
  | zero => have := hprime.two_le; omega
  | succ candidate ih =>
      by_cases hbelow : base ≤ candidate
      · obtain ⟨found, hfound⟩ := ih hbelow
        simp only [primePowerSearch]
        have hnotsmall : ¬candidate + 1 < 2 := by have := hprime.two_le; omega
        rw [if_neg hnotsmall]
        split_ifs
        · cases hpowerSearch : powerExponent value (candidate + 1) value with
          | none => exact ⟨found, hfound⟩
          | some foundExponent => exact ⟨(candidate + 1, foundExponent), rfl⟩
        · exact ⟨found, hfound⟩
      · have heq : candidate + 1 = base := by omega
        have hprimeTest := (primeTest_iff base).mpr hprime
        obtain ⟨found, hfound⟩ := powerExponent_complete value base value exponent hpos hexponent hpower
        simp only [primePowerSearch, heq, show ¬base < 2 by exact Nat.not_lt.mpr hprime.two_le,
          if_false, hprimeTest, if_true, hfound]
        exact ⟨(base, found), rfl⟩

def primePowerData (value : ℕ) : Option (ℕ × ℕ) := primePowerSearch value value

theorem primePowerData_iff (value : ℕ) :
    (∃ found, primePowerData value = some found) ↔ IsPrimePow value := by
  constructor
  · rintro ⟨⟨base, exponent⟩, hfound⟩
    rcases primePowerSearch_sound value value base exponent hfound with ⟨hp, _, he, _, hn⟩
    exact (isPrimePow_nat_iff value).mpr ⟨base, exponent, hp, he, hn⟩
  · intro h
    rcases (isPrimePow_nat_iff_bounded value).mp h with ⟨base, hb, exponent, he, hp, hpos, hn⟩
    exact primePowerSearch_complete value value base exponent hp hb hpos he hn

def mangoldtBounds (value : ℕ) (epsilon : ℚ) : Bounds :=
  match primePowerData value with
  | some (base, _) => computedLogBounds base epsilon
  | none => ⟨0, 0⟩

theorem mangoldtBounds_sound (value : ℕ) (epsilon : ℚ) :
    (mangoldtBounds value epsilon).Contains (ArithmeticFunction.vonMangoldt value) := by
  cases hdata : primePowerData value with
  | none =>
      have hnot : ¬IsPrimePow value := by
        intro h
        obtain ⟨found, hfound⟩ := (primePowerData_iff value).mpr h
        simp [hdata] at hfound
      simp [mangoldtBounds, hdata, ArithmeticFunction.vonMangoldt_apply, hnot, Bounds.Contains]
  | some found =>
      rcases found with ⟨base, exponent⟩
      rcases primePowerSearch_sound value value base exponent hdata with ⟨hp, _, he, _, hn⟩
      have hvalue : ArithmeticFunction.vonMangoldt value = Real.log (base : ℝ) := by
        rw [← hn, ArithmeticFunction.vonMangoldt_apply_pow (Nat.ne_of_gt he),
          ArithmeticFunction.vonMangoldt_apply_prime hp]
      simp only [mangoldtBounds, hdata, hvalue]
      exact computedLogBounds_sound base epsilon (by exact_mod_cast hp.one_le)

end LandauWindows.CertificateGeometry
