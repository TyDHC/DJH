import Mathlib.Tactic


set_option linter.style.commandStart false


example (a b : ℕ) (h1 : a = b) : b = a := by
  symm
  grind
