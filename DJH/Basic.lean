import Mathlib.Tactic
import DJH.temp

theorem test1 (a b : Nat) : a + b = b + a := by
  rw [Nat.add_comm]
