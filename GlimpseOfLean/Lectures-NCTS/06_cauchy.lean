import GlimpseOfLean.Library.Short
import Mathlib.LinearAlgebra.Matrix.Spectrum

def topMinor {n : ℕ} {R : Type} [CommRing R] (A : Matrix (Fin (n+1)) (Fin (n+1)) R) : Matrix (Fin n) (Fin n) R :=
  A.submatrix Fin.castSucc Fin.castSucc

#eval topMinor !![(5 : ℤ), 4; 3, 2]

theorem minorOfHermitianHermitian {n : ℕ} (A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
  (A.IsHermitian) → ((topMinor A).IsHermitian) := by
  intro hA
  sorry


-- Cauchy's Interlacing Theorem: If A is a real, symmetric nxn matrix, then the eigenvalues of any
-- (n-1)x(n-1) minor interlace the eigenvalues of A

theorem cauchy {n : ℕ} : ∀ A : Matrix (Fin (n+1)) (Fin (n+1)) ℝ, (hA : A.IsHermitian) → ∀ i : Fin n,
  hA.eigenvalues i ≤ (minorOfHermitianHermitian A hA).eigenvalues i
  ∧ (minorOfHermitianHermitian A hA).eigenvalues i ≤ hA.eigenvalues (i+1) := by
  sorry
  -- Proof sketch:
  -- The i-th eigenvalue of A is the maximum Rayleigh quotient over a subspace of R^(n+1) of
  -- dimension i, when minimized over all possible subspaces of this dimension
  -- The i-th eigenvalue of A's top minor is this same quantity, except minimized over subspaces
  -- which are contained in the standard hyperplane R^n


-- Small example: 2x2 case

/- If A is a 2x2 symmetric real matrix, then the corner entry A_{0,0} lies between the eigenvalues
  of A -/
theorem cauchy_2_2 (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : A.IsHermitian) :
  (hA.eigenvalues 0 < A 0 0) ∧ (A 0 0 < hA.eigenvalues 1) := by
  sorry
