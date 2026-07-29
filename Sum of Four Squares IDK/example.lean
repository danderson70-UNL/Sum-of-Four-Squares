import Mathlib

example (m n a b c : ℕ) (m0 : m ≠ 0) (h : m * (1 + a) * (1 + b + c) = n) : a ≤ n := by
  obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := Nat.exists_eq_succ_of_ne_zero m0
  lia

example (m n a b c : ℕ) (m0 : m ≠ 0) (h : m * (1 + a) * (1 + b + c) = n) : a ≤ n := by
  -- obtain ⟨m', rfl⟩ : ∃ m' : ℕ, m = m' + 1 := Nat.exists_eq_succ_of_ne_zero m0
  nlinarith [m0.pos]

example (a b : ℕ) (b0 : b ≠ 0) : a ≤ b * a := by
  have := b0.pos
  -- lia
  exact Nat.le_mul_of_pos_left a this


example (q : ℂ) (qN1 : ‖q‖ < 1) : Summable (fun (p : ℤ × ℤ) ↦ (q^(p.1^2) * q^(p.2^2))) := by
  apply Summable.of_norm
  have : Summable (fun (z : ℤ) ↦ ‖q^(z^2)‖) := by sorry
  exact Summable.mul_norm (f := fun (z : ℤ) ↦ q^(z^2)) (g := fun (z : ℤ) ↦ q^(z^2)) this this
