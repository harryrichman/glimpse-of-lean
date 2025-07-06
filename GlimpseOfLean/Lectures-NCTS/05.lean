import GlimpseOfLean.Library.Short

-- variable (a : ℕ) (b : ℤ)
-- theorem my_thm_name (hypotheses) : statement := by sorry

theorem add_2_and_2 : 2 + 2 = 4 := by
  norm_num

example : 2 + 2 = 4 := by
  norm_num

def add_2_plus_2 := 2 + 2 = 4
#check add_2_plus_2

example : add_2_plus_2 := by
  unfold add_2_plus_2
  norm_num
/- Excercises: formalize the following statements in Lean -/


/- Every natural number n is the sum of four squares -/

theorem legendre : True := by sorry

theorem legendre_sum_of_four_squares (n : ℕ) : ∃ a b c d : ℕ, n = a^2 + b^2 + c^2 + d^2 := by
  sorry

theorem legendre_sum_of_four_squares' : ∀ n : ℕ,  ∃ a b c d : ℕ, n = a^2 + b^2 + c^2 + d^2 := by
  intro n₀
  sorry


/- Bertrand's postulate: For every natural number n > 1, there is a prime number p between n and 2n -/

theorem bertrand : True := by sorry

#eval Nat.Prime 10
#eval Nat.Prime 11
-- 10 : Nat, so 10.Prime is abbrev for Nat.Prime 10

theorem bertrand_prime (n : ℕ) (h : n > 1) : ∃ p, p.Prime ∧ (n < p) ∧ (p < 2*n) := by
  sorry

theorem bertrand_prime' : ∀ n > 1, ∃ p, p.Prime ∧ (n < p) ∧ (p < 2*n) := by
  intro n h_ge_1
  sorry


/- Goldbach's conjecture: every even natural number greater than 2 is the sum of two primes. -/

theorem goldbach : True := by sorry

theorem goldbach_sum : ∀ n > 2, (n % 2 = 0) → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ (p + q = n) := by
  sorry

#check 10.IsEven


/- (challenge) The prime number theorem -/

theorem pnt : True := by sorry

-- First, define the prime counting function π(x)
noncomputable def prime_counting_function (x : ℝ) : ℝ :=
  (Finset.filter Nat.Prime (Finset.range (Nat.floor x + 1))).card

def prime_counting_function' (x : ℕ) : ℕ :=
  (Finset.filter Nat.Prime (Finset.range (x + 1))).card

#eval prime_counting_function' 11

-- Notation for the prime counting function
notation "π" => prime_counting_function

theorem chebyshev_bounds : ∃ C₁ C₂ : NNReal, ∀ x, x / Real.log x < C₁ * π x ∧ π x < C₂ * x / Real.log x := by
  sorry

-- Classical Prime Number Theorem: π(x) ~ x / log(x)
-- Using asymptotic notation (∼ means f(x) / g(x) → 1 as x → ∞)
theorem prime_number_theorem_classical :
    π =ᶠ[Filter.atTop] fun x => x / Real.log x := by
  sorry

-- More explicit formulation: lim_{x→∞} π(x) / (x / log x) = 1
theorem prime_number_theorem_limit :
    Filter.Tendsto (fun x => (π x : ℝ) / (x / Real.log x)) Filter.atTop (𝓝 1) := by
  sorry


/- If p(x) is a polynomial with real coefficients, whose coefficients are all positive, and `a` is a
positive real number, then p(a) is nonzero. -/

/- If p(x) is a real-coeff. polynomial with degree d, then p(x) has at most d real roots. -/

/- If M is a real symmetric matrix, then the eigenvalues of M are real. -/

example {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) : True := by
  sorry



/- Example: Defining the Mobius function from number theory -/

def isDiv (d n : ℕ) : Bool := n % d == 0

def mobius (n : ℕ) : ℤ := match n with
  | 0 => 0
  | 1 => 1
  | n =>
    let strict_divisors := ((List.range n).filter (fun d => isDiv d n ∧ d > 0)).attach
    let mob_values := (strict_divisors).map (fun x => mobius x.1)
    let result := - mob_values.sum
    result
decreasing_by
  obtain ⟨x, hx⟩ := x
  simp only [List.mem_filter] at hx
  have hx2 := hx.left
  simp only [List.mem_range] at hx2
  apply hx2

#check List.attach

#check List.filter (fun d => isDiv d 100 ∧ d > 0) (List.range 100)
#eval (List.range 105).filter (fun d => isDiv d 105 ∧ d > 0)
#eval ((List.range 105).filter (fun d => isDiv d 105 ∧ d > 0)).attach

#check (List.range 5)[3]
#check (List.range 5).attach[3]

def strict_divisors (n : ℕ) :=
  let this := ((List.range n).filter (fun d => isDiv d n)).attach
  this

#check strict_divisors 21
#eval strict_divisors 21


#eval mobius 101
#eval (List.range 40).map (fun n => (n, mobius n))
