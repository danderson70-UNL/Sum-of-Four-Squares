import «Sum of Four Squares IDK».Common

def hello := "world"

example : 4 = 4 := rfl

example : 2 + 2 = 4 := by
  repeat apply Nat.succ_inj.mpr
  rfl

theorem thingy (a : ℂ) (b : ℂ) : a + b = b + a := by
  ring

section
open BigOperators

theorem sample (r : ℂ) : ‖r‖ < 1 → ∑i ∈ Finset.range 5, i = 10 := by
  intro h
  repeat rw[Finset.sum_range_succ]
  rw[Finset.sum_range_zero]

end

section
open Filter Topology

#check hasSum_geometric_of_lt_one
#check HasSum.hasSum_of_sum_eq
#eval ({1, 2} : Finset ℕ) ⊓ {1}

theorem geo_sum {r : ℝ} (h : 0 ≤ r ∧ r < 1) : HasSum (fun (n : ℕ) ↦ r^n) (1 - r)⁻¹ := by
  have w : r ≠ 1 := ne_of_lt h.2
  have : Tendsto (fun n ↦ (r ^ n - 1) * (r - 1)⁻¹) atTop (𝓝 ((0 - 1) * (r - 1)⁻¹)) := by
    apply ((tendsto_pow_atTop_nhds_zero_of_lt_one h.1 h.2).sub tendsto_const_nhds).mul
      tendsto_const_nhds
  apply (hasSum_iff_tendsto_nat_of_nonneg (pow_nonneg h.1) _).mpr
  simp only [geom_sum_eq w];
  simp[neg_inv] at this; simp[←div_eq_mul_inv _ (r-1)] at this
  assumption
end

section
open BigOperators

def doubleFinset (s : Finset ℕ) : Finset ℕ := s.biUnion (fun n ↦ {2*n, 2*n + 1})
#eval doubleFinset {3, 4, 10}

lemma doublePartOfProd (f : ℕ → ℂ) (g : ℕ → ℂ) {limit : ℂ} :
    HasProd (fun (n : ℕ) ↦ (f n) * (g n)) limit ↔
    HasProd (fun (n : ℕ) ↦ f n * g (2*n) * g (2*n + 1)) limit := by
  let P : ℕ ⊕ ℕ → ℂ
    | Sum.inl a => f a
    | Sum.inr b => g b
  let Q : ℕ ⊕ ℕ → ℂ
    | Sum.inl a => f a
    | Sum.inr b => g (2*b) * g (2*b + 1)
  calc
  _ ↔ HasProd P limit := by
    apply hasProd_iff_hasProd
    · sorry
    · sorry
  _ ↔ HasProd Q limit := sorry
  _ ↔ _ := sorry


noncomputable def F := fun (x y : ℂ) (n : ℕ) ↦
  (1 - x^(2*n + 2)) * (1 + x^(2*n + 1) * y) * (1 + x^(2*n + 1) * y⁻¹)
noncomputable def G := fun (x y : ℂ) (m : ℤ) ↦ x^(m^2) * y^m

theorem triple_product {x y : ℂ} (hx : ‖x‖ < 1) (hy : y ≠ 0) :
  ∃ limit : ℂ, HasProd (F x y) limit ∧ HasSum (G x y) limit := sorry

-- HasProd.hasProd_of_prod_eq seems useful for permuting the elements of a product
--  and rewriting products in a different order

lemma Aa {x : ℂ} (hx : ‖x‖ < 1) :
  ∃ limit : ℂ, HasProd (fun (n : ℕ) ↦ (1-x^(n+1)) / (1 + x^(n+1))) limit
    ∧ HasSum (fun (m : ℤ) ↦ x^(m^2)) limit := by
  obtain ⟨t, ⟨prodt, sumt⟩⟩ := triple_product hx (by norm_num : (-1 : ℂ) ≠ 0)
  use t; constructor
  · have : ∀ a : ℕ, (fun (n : ℕ) ↦ (1-x^(n+1)) / (1 + x^(n+1))) a = F x (-1) a := by
      sorry
    apply HasProd.congr_fun prodt this
  · have : ∀ b : ℤ, (fun (m : ℤ) ↦ x^(m^2)) b = G x (-1) b := by sorry
    apply HasSum.congr_fun sumt this
end
