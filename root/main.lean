import «upper_bound».«main»
import «finite_verification».«main»
import Definitions
-- Sub-goal 1: Every factorion is at most 2,540,160



theorem root : {n : ℕ | digits10FactorialSum n = n} = {1, 2, 145, 40585} := by
  ext n
  constructor
  · intro hn
    have hle : n ≤ 2540160 := upper_bound n hn
    have hmem : n ∈ {n : ℕ | digits10FactorialSum n = n} ∩ {n | n ≤ 2540160} :=
      ⟨hn, hle⟩
    rw [finite_verification] at hmem
    exact hmem
  · intro hn
    have : {1, 2, 145, 40585} ⊆ {n : ℕ | digits10FactorialSum n = n} := by
      have := finite_verification
      intro x hx
      by_contra hne
      have : x ∈ {n : ℕ | digits10FactorialSum n = n} ∩ {n | n ≤ 2540160} := by
        rw [finite_verification]
        exact hx
      exact hne this.1
    exact this hn
