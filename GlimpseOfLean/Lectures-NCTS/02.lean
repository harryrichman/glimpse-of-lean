import GlimpseOfLean.Library.Short

/- Some basic propositions -/

example : ∀ (p : Prop), p → p := by
  intro p
  intro hp
  exact hp
  -- tauto

example : ∀ (p : Prop), p ↔ True → p := by
  intro p
  constructor
  · intro hp
    intro _
    exact hp
    -- exact (fun _ => hp)
  · intro htp
    apply htp
    tauto
    -- exact True.intro

example: 2 + 2 = 5 → False := by
  intro h
  contradiction
  -- norm_num

/- Example: infinitely many prime numbers -/

theorem exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  by_cases np : n.Prime
  · use n, np
  induction' n using Nat.strong_induction_on with n ih
  rw [Nat.prime_def_lt] at np
  push_neg at np
  rcases np h with ⟨m, mltn, mdvdn, mne1⟩
  have : m ≠ 0 := by
    intro mz
    rw [mz, zero_dvd_iff] at mdvdn
    linarith
  have mgt2 : 2 ≤ m := two_le this mne1
  by_cases mp : m.Prime
  · use m, mp
  · rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
    use p, pp
    apply pdvd.trans mdvdn


theorem primes_infinite' : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  intro s
  by_contra h
  push_neg at h
  set s' := s.filter Nat.Prime with s'_def
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h
  have : 2 ≤ (∏ i ∈ s', i) + 1 := by
    sorry
  rcases exists_prime_factor this with ⟨p, pp, pdvd⟩
  have : p ∣ ∏ i ∈ s', i := by
    sorry
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  show False
  sorry


/- Excercises: formalize the following statements in Lean -/

/- Every natural number n is the sum of four squares -/

/- Bertrand's postulate: For every natural number n > 1, there is a prime number p between n and 2n -/

/- Goldbach's conjecture: every even natural number greater than 2 is the sum of two primes. -/

/- (challenge) The prime number theorem -/

/- If p(x) is a polynomial with real coefficients, whose coefficients are all positive, and `a` is a
positive real number, then p(a) is nonzero. -/

/- If p(x) is a real-coeff. polynomial with degree d, then p(x) has at most d real roots. -/

/- If M is a real symmetric matrix, then the eigenvalues of M are real. -/
