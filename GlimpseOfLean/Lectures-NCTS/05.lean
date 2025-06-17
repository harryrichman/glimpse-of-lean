import GlimpseOfLean.Library.Short

/- Excercises: formalize the following statements in Lean -/

/- Every natural number n is the sum of four squares -/

/- Bertrand's postulate: For every natural number n > 1, there is a prime number p between n and 2n -/

/- Goldbach's conjecture: every even natural number greater than 2 is the sum of two primes. -/

/- (challenge) The prime number theorem -/

/- If p(x) is a polynomial with real coefficients, whose coefficients are all positive, and `a` is a
positive real number, then p(a) is nonzero. -/

/- If p(x) is a real-coeff. polynomial with degree d, then p(x) has at most d real roots. -/

/- If M is a real symmetric matrix, then the eigenvalues of M are real. -/


example (n : ℕ) : ∃ a b c d : ℤ, n = a^2 + b^2 + c^2 + d^2 := by
  sorry

example (n : ℕ) (h : n > 1) : ∃ p q : ℕ, p.IsPrime, q.isPrime := by
  sorry
