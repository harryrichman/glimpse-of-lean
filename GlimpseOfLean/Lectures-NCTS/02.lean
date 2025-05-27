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

lemma two_le {m : ℕ} (h0 : m ≠ 0) (h1 : m ≠ 1) : 2 ≤ m := by
  sorry

lemma exists_prime_factor {n : Nat} (h : 2 ≤ n) : ∃ p : Nat, p.Prime ∧ p ∣ n := by
  -- either `n` is prime, or `n` is not prime
  by_cases np : n.Prime
  · -- if `n` is prime, ...
    -- then `n` is a prime divisor of `n`
    use n, np
  · -- otherwise, `n` is not prime.
    -- suppose by induction that the claim holds for all m < n.
    induction' n using Nat.strong_induction_on with n ih
    -- Since `n` is not prime, it has a factor `m` which satisfies 1 < m < n
    rw [Nat.prime_def_lt] at np
    push_neg at np
    rcases np h with ⟨m, mltn, mdvdn, mne1⟩
    have : m ≠ 0 := by
      intro mz
      rw [mz, zero_dvd_iff] at mdvdn
      linarith
    have mgt2 : 2 ≤ m := two_le this mne1
    -- either `m` is prime, or `m` is not prime
    by_cases mp : m.Prime
    · -- if `m` is prime, then `m` is a prime divisor of `n`
      use m, mp
    · -- if `m` is not prime, ...
      -- then by our inductive hypothesis, `m` has a prime divisor `p`
      rcases ih m mltn mgt2 mp with ⟨p, pp, pdvd⟩
      -- this `p` is also a prime divisor of `n`
      use p, pp
      apply Dvd.dvd.trans pdvd mdvdn


theorem primes_infinite : ∀ s : Finset Nat, ∃ p, Nat.Prime p ∧ p ∉ s := by
  -- consider a finite set `s`
  intro s
  -- suppose, for a contradiction, that the claim does not hold
  by_contra h
  have h_old := h
  push_neg at h
  -- Hypothesis: the finite set `s` contains all prime numbers
  -- s' = prime numbers inside s
  set s' := s.filter Nat.Prime with s'_def
  -- Claim: `n` is in `s'` if and only if `n` is prime
  have mem_s' : ∀ {n : ℕ}, n ∈ s' ↔ n.Prime := by
    intro n
    simp [s'_def]
    apply h n
  -- the product of numbers in `s'` is ≥ 1
  have hprod_ge_1 : 2 ≤ (∏ i ∈ s', i) + 1 := by
    sorry
  -- thus, (∏ i ∈ s', i) + 1 has at least one prime divisor `p`
  rcases exists_prime_factor hprod_ge_1 with ⟨p, pp, pdvd⟩
  -- but `p` is a divisor of (∏ i ∈ s', i)
  have : p ∣ ∏ i ∈ s', i := by -- Note: keyboard pipe: |, divisible: ∣
    sorry
  -- thus, `p` is a divisor of 1
  have : p ∣ 1 := by
    convert Nat.dvd_sub pdvd this
    simp
  -- but 1 does not have any prime factor
  simp only [Nat.dvd_one] at this
  apply Nat.prime_one_false
  rw [this] at pp
  exact pp


/- Excercises: formalize the following statements in Lean -/

/- Every natural number n is the sum of four squares -/

/- Bertrand's postulate: For every natural number n > 1, there is a prime number p between n and 2n -/

/- Goldbach's conjecture: every even natural number greater than 2 is the sum of two primes. -/

/- (challenge) The prime number theorem -/

/- If p(x) is a polynomial with real coefficients, whose coefficients are all positive, and `a` is a
positive real number, then p(a) is nonzero. -/

/- If p(x) is a real-coeff. polynomial with degree d, then p(x) has at most d real roots. -/

/- If M is a real symmetric matrix, then the eigenvalues of M are real. -/
