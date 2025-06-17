import GlimpseOfLean.Library.Short


/- Matrices -/

def M : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 2;
     3, 4]

-- `Fin 2` is the standard type with 2 elements
--   its elements are `0` and `1`, but also `n` is interpreted mod 2.

-- matrix multipliation
#eval (M * M)


#eval (7 + 2 : Fin 2)


def M' := !![(1 : ℤ), 2; 3, 4]
#check M'
#eval (M' * M')

-- def N :=
--   !![1, 2;
--      3, 4]

-- def v : Vec (Fin 3) ℤ := ![4, 3, 2]


#eval M.det

#eval Matrix.det M

#eval M'.det

def N := !![1, 2; 3, -4]

#eval N.det

#check Matrix.charpoly
#check (Matrix.charpoly)
#check N.charpoly
-- #eval N.charpoly -- causes an error, because polynomials are noncomputable

/- type signature of a function -/
def my_sq (n : ℤ) : ℤ := n * n

#check my_sq -- type is `(n : ℤ) : ℤ`
#check (my_sq) -- type is `ℤ → ℤ`


/- Polynomials -/
noncomputable section -- everything in this section is marked `noncomputable`
open Polynomial
-- can use `X` instead of `Polynomial.X`

def p : Polynomial ℚ := C 4 + 3 * X
-- `C a` means the constant polynomial with value `a`
-- `X` is the polynomial variable



def q := p + 1

#check p
#check q
#check p * p

#check p.roots

#check p.degree
#check (natDegree X)
-- #eval (natDegree (5 : ℤ[X]))

example : p.degree = some 1 := by
  unfold p
  -- simp?
  sorry

example : roots (X + C 4) = {-4} := by
  exact roots_X_add_C 4

example : p.roots = {- 4/3} := by
  unfold p
  -- have : p = (3 : ℚ) * (X + (4/3 : ℚ)) := by
  --   simp?
  have : (C (1/3) * p).roots = p.roots := roots_C_mul p (by norm_num : (1/3 : ℚ) ≠ 0)
  rw [← this]
  rw [← roots_C_mul p (_ : 3 ≠ 0)]
  · -- goal one
    sorry
  · -- goal two
  exact roots_X_add_C (0 : ℤ)
  sorry

-- #eval (Polynomial.aeval (1 : ℤ)) p

end

/- Other -/

theorem fst_of_two_props : ∀ a b : Prop, a → b → a :=
  fun a b : Prop =>
  fun ha hb => ha

theorem fst_of_two_props' : ∀ a b : Prop, a → b → a := by
  intro a b
  intro ha
  intro _
  exact ha

def add1 (n : Nat) : Nat := n + 1

def add1' : Nat → Nat := fun n => n + 1

#check add1
#check (add1)

#check add1'
#check (add1')

#check (add1 20)

#eval (add1 20)
#eval (add1' 20)
