import GlimpseOfLean.Library.Short

/- Matrices -/

def M' :=
  !![1, 2, 3;
     4, 5, 6;
     7, 8, 9]
#check M'

def M : Matrix (Fin 3) (Fin 3) ℤ :=
  !![1, 2, 3;
     4, 5, 6;
     7, 8, 9]


#check M

-- access entries of M
#eval M 2 0
#eval M 2 1
#eval M 2 8

-- access rows of M
#eval M 2

-- matrix multiplication
#eval M * M


-- matrix from describing entries by a function

def abs_diff_matrix (n : ℕ) : Matrix (Fin n) (Fin n) ℚ :=
  Matrix.of (fun i j => |(i - j)|) -- `|i - j|`

-- example : i : ℚ

#eval abs_diff_matrix 5
#check abs_diff_matrix

/- Vectors -/

def v := !![10; 1; -1]
#check v
#check v.transpose

#eval M * v
#eval v.transpose * M

-- "vector type"
def v' : (Fin 3) → ℤ := ![10, 1, -1]
#check (v')

#eval M.mulVec v' -- shorthand for `Matrix.mulVec M v'
#eval Matrix.vecMul v' M
-- #eval M *ᵥ v

-- matrix as a bilinear form

#eval v.transpose * M * v


/- Eigenvalues and eigenvectors -/

def D := abs_diff_matrix 3
#eval D

-- check that v = (1, 0, -1) is an eigenvector
def v_neg2 : (Fin 3) → ℚ := ![1, 0, -1]

#eval D.mulVec v_neg2
#eval (-2) • v_neg2

theorem have_eigenvector : ∃ (μ : ℚ), D.mulVec v_neg2 = μ • v_neg2 := by
  use -2
  -- native_decide
  calc
    D.mulVec v_neg2 = ![-2, 0, 2] := by
      -- unfold D v_neg2
      -- unfold abs_diff_matrix
      native_decide
    _ = (-2 : ℚ) • v_neg2 := by native_decide
  done

example : ∃ μ : ℚ, D.mulVec ![1, 0, 1] = μ • ![1, 1, 1] := by
  use 2
  native_decide

def ones (n : ℕ) : (Fin n) → ℚ :=
  fun _ => 1

#eval ones 5

example (n : ℕ) : ∃ μ : ℚ, ∃ e_vec : (Fin n) → ℚ, (abs_diff_matrix n).mulVec e_vec = μ • (ones n) := by
  use n
  let v : (Fin n) → ℚ := (
    fun i => if i.val = 0 ∨ i.val = n - 1 then 1 else 0
  )
  use v
  calc
    (abs_diff_matrix n).mulVec v = (fun i => (n : ℚ)) := by
      unfold abs_diff_matrix
      unfold v
      funext i -- two functions are equal if their values on all inputs are equal

      -- native_decide+revert
      sorry
    _ = ↑n • v := by sorry
  sorry


/- Cauchy-Binet, https://en.wikipedia.org/wiki/Cauchy%E2%80%93Binet_formula -/

variable {R : Type* } { m n : ℕ } [CommRing R]
variable {M N : Type} [Fintype M] [Fintype N] [DecidableEq M] [DecidableEq N] [LinearOrder M] [LinearOrder N]

theorem Matrix.det_mul' (A : Matrix (Fin m) (Fin n) R) (B : Matrix (Fin n) (Fin m) R) :
  det (A * B) = ∑ f : (Fin m) ↪o (Fin n), det (A.submatrix id f) * det (B.submatrix f id) := by
  -- expand determinant in matrix entries as sum over permutations, on LHS
  rw [Matrix.det_apply (A * B)]
  -- simp_rw [Matrix.mul_apply, Finset.prod_sum, Finset.prod_mul_distrib]
  -- expand entries of matrix product A*B
  simp_rw [Matrix.mul_apply]
  -- interchange product (over Fin m) and sum (over Fin n)
  simp_rw [Finset.prod_sum]
  simp only [Finset.univ_pi_univ, Finset.prod_attach_univ]
  -- rewrite (prod_i a_i*b_i) as (prod_i a_i) * (prod_i b_i)
  simp_rw [Finset.prod_mul_distrib]
  -- simp_all only [Finset.univ_pi_univ, Finset.prod_attach_univ]
  -- expand determinats on RHS
  simp_rw [Matrix.det_apply]
  simp_all only [submatrix_apply, id_eq]
  -- exchange order of summation
  simp_rw [Finset.smul_sum]
  rw [Finset.sum_comm]

  -- calc
  --   ∑ x, Equiv.Perm.sign x • ∑ x_1, (∏ x_2, A (x x_2) (x_1 x_2 ⟨x_2, Finset.mem_univ x_2⟩.property)) * ∏ x, B (x_1 x ⟨x, Finset.mem_univ x⟩.property) x = ∑ x_1, ∑ σ, Equiv.Perm.sign σ • (∏ x_2, A (σ x_2) (x_1 x_2 ⟨x_2, Finset.mem_univ x_2⟩.property)) * ∏ x, B (x_1 x ⟨x, Finset.mem_univ x⟩.property) x := by rfl -- by simp?
  --   _ = 0 := by simp?
  --   _ = ∑ x, (∑ x_1, Equiv.Perm.sign x_1 • ∏ x_2, A (x_1 x_2) (x x_2)) * ∑ x_1, Equiv.Perm.sign x_1 • ∏ x_2, B (x (x_1 x_2)) x_2 := by rfl
  sorry
