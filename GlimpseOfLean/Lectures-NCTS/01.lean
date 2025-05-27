import GlimpseOfLean.Library.Short

/- We can use Lean as a calculator using the `#eval` command -/

#eval 2 + 4

#eval 4^3

#eval 100 / 3 -- NOTE: rounds down
#eval 100.0 / 3
#eval (100 : ℚ) / 400
#eval (100 / 300 : ℚ)

/- We can check the type of an expression using the `#check` command -/

#check 100.0 / 3
#check (100 / 3 : ℚ)

#eval 3 - 10 -- NOTE: stops at zero :O
#eval (3 : ℤ) - 10

#check 3
#check (3 : ℤ) - 10
#check ℕ
#check Nat.add

#check (2 + 4 = 10)

/- We use `lemma` or `theorem` to declare a mathematical proposition, which we name for future use.
The programming language treats `lemma` and `theorem` in exactly the same way; the difference is
only for human readability. -/

lemma add_2_4 : 2 + 4 = 6 := by
  trivial
  -- norm_num -- decide -- tauto -- trivial -- linarith -- simp?

theorem add_2_4_wrong : 2 + 4 = 10 := by
  sorry

/- `example` is like `theorem`, except that we don't assign a name to the statement. This is
convenient if we don't plan to use it in the future. -/

example : 2 + 4 = 4 + 2 := by
  tauto -- trivial -- norm_num
