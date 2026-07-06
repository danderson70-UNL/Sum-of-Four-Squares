import Mathlib


theorem pqrss [CommMonoidWithZero α] [NormalizedGCDMonoid α] (a b c : α) :
    normalize (gcd a b * gcd (lcm a b) c) = normalize (gcd b c * gcd a (lcm b c)) := by
  apply normalize_eq_normalize_iff_associated.mpr
  apply Associated.trans (gcd_mul_left' _ _ _).symm
  apply Associated.trans _ (gcd_mul_left' _ _ _)
  have rewriteLeft : gcd (gcd a b * lcm a b) (gcd a b * c)
      = gcd (a * b) (gcd (a * c) (b * c)) := by
    calc
    gcd (gcd a b * lcm a b) (gcd a b * c) = gcd (a * b) (gcd a b * c) := by
      apply Associated.gcd_eq_left (gcd_mul_lcm _ _)
    _ = gcd (a * b) (gcd (a * c) (b * c)) := by
      rw[Associated.gcd_eq_right (gcd_mul_right' _ _ _).symm]
  have rewriteRight : gcd (gcd b c * a) (gcd b c * lcm b c)
      = gcd (gcd (a * b) (a * c)) (b * c) := by
    calc
    gcd (gcd b c * a) (gcd b c * lcm b c) = gcd (gcd b c * a) (b * c) := by
      apply Associated.gcd_eq_right (gcd_mul_lcm _ _)
    _ = gcd (gcd (a * b) (a * c)) (b * c) := by
      rw[Associated.gcd_eq_left (gcd_mul_right' a b c).symm]
      repeat rw[mul_comm _ a]
  rw[rewriteLeft, rewriteRight]
  apply (gcd_assoc' _ _ _).symm

section

open Nat Finset Finsupp
variable {σ} [DecidableEq σ]
#check Finset.prod

def sgn_cmpre : ℕ × ℕ → ℤ := fun (i,j) ↦
  if i > j then -1
  else if i < j then 1
  else 0

def sgn : Finset ℕ × Finset ℕ → ℤ := fun (I,J) ↦
  ∏ i ∈ I, (∏ j ∈ J, sgn_cmpre (i,j))

def taylorMapExps {n : ℕ} (f : range n → σ →₀ ℕ) :
  Finset (range n) → σ →₀ ℕ :=
  fun I ↦ ⟨
    Finset.biUnion I (fun i ↦ (f i).support),
    fun (s : σ) ↦ ∑ i ∈ I, f i s,
    by
      intro s; rw[mem_biUnion]
      constructor
      · rintro ⟨a, ⟨aI, h⟩⟩ k; dsimp at k
        rw[mem_support_toFun] at h; replace h : f a s ≠ 0 := h
        rw[←insert_erase aI, sum_insert <| notMem_erase a I] at k
        exact h (Nat.eq_zero_of_add_eq_zero_right k)
      · rintro k; contrapose! k
        replace k : ∀ i ∈ I, f i s = 0 := by
          intro i iI
          apply notMem_support_iff.mp <| k i iI
        exact sum_eq_zero k
  ⟩

noncomputable def taylorMap {n : ℕ} {R} [CommRing R] (f : range n → σ →₀ ℕ) :
  Finset (range n) → MvPolynomial σ R :=
  fun I ↦ MvPolynomial.monomial (taylorMapExps f I) (1 : R)




end
