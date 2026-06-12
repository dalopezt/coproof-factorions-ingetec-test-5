import Mathlib

-- Generated from goal prompt
def digits10FactorialSum (n : ℕ) : ℕ :=
  (Nat.digits 10 n).map Nat.factorial |>.sum
