import GlimpseOfLean.Library.Short

open Polynomial

def logConcaveCoeff (p : Polynomial ℝ) : Prop :=
  ∀ i : Fin (p.natDegree), (p.coeff i)^2 ≥ (p.coeff (i - 1)) * (p.coeff (i + 1))

def ultraLogConcaveCoeff (p : Polynomial ℝ) : Prop :=
  ∀ i : Fin (p.natDegree),
  (p.coeff i)^2 ≥ (p.coeff (i - 1)) * (p.coeff (i + 1)) * (1 + 1.0/i) * (1 + 1.0/(p.natDegree - i))

noncomputable def binomCoeffToPoly (as : List ℝ) : Polynomial ℝ :=
  let n := as.length
  let monomials := List.map (fun (a, i) => C ((n.choose i) * a) * X^i) (List.zipIdx as)
  monomials.sum

#check List.zipIdx
#check List.zip

-- Newton's Theorem: If p(x) is a polynomial with real roots, then its coefficient sequence is
-- ultra-log-concave

theorem newton : ∀ p : Polynomial ℝ, (p.roots.card = p.natDegree) → ultraLogConcaveCoeff p := by
  intro p
  intro h
  have hMon : p.Monic := by sorry
  have hProd : _ := prod_multiset_X_sub_C_of_monic_of_roots_card_eq hMon h
  sorry
  -- Proof sketch:
  -- If p has all real roots, then the derivative p' also has all real roots
  -- By repeatedly taking derivatives, we get a quadratic polynomial, which has real roots
  -- By the quadratic formula, the ultra-log-concave relation holds for coeffs (n, n-1, n-2)
  -- If p has all real roots, then so does the "dual" polynomial with reversed coefficients,
  -- q(X) = X^n * p(1/X)
  -- By applying the same argument to q, we get the ultra-log-concave relation for coeffs (0, 1, 2)
  -- Finally,


-- Small case: degree 2 polynomial
theorem newton_2 (p : Polynomial ℝ) (hDeg : p.natDegree = 2) (hMon : p.Monic):
  (p.roots.card = 2) → (p.coeff 1)^2 ≥ 4*(p.coeff 0)*(p.coeff 2) := by
  intro h
  have hRoots : p.roots.card = p.natDegree := by
    simp_all only
  have h1 : ∃ a b k : ℝ, (p = (C k) * (X - C a) * (X - C b)) := by sorry
  rcases h1 with ⟨a, b, k,  hconst⟩
  have h2 : (p.coeff 2 = k) := by
    simp_all only
    sorry
  sorry
