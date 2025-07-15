import GlimpseOfLean.Library.Short

def logConcaveCoeff (p : Polynomial ℝ) : Prop :=
  ∀ i : Fin (p.natDegree), (p.coeff i)^2 ≥ (p.coeff (i - 1)) * (p.coeff (i + 1))

def ultraLogConcaveCoeff (p : Polynomial ℝ) : Prop :=
  ∀ i : Fin (p.natDegree), (p.coeff i)^2 ≥ (p.coeff (i - 1)) * (p.coeff (i + 1)) * (1 + 1.0/i) * (1 + 1.0/(p.natDegree - i))

-- Newton's Theorem: If p(x) is a polynomial with real roots, then its coefficient sequence is
-- ultra-log-concave

theorem newton : ∀ p : Polynomial ℝ, (p.roots.card = p.natDegree) → ultraLogConcaveCoeff p := by
  sorry


-- Small case: degree 2 polynomial
theorem newton_2 (p : Polynomial ℝ) (hDeg : p.natDegree = 2) :
  (p.roots.card = 2) → (p.coeff 1)^2 ≥ 4*(p.coeff 0)*(p.coeff 2) := by
  sorry
