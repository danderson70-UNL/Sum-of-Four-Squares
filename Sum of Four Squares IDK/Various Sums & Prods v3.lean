import Mathlib

section tools_and_lemmas
open Finset Polynomial

-- For rewriting a Finset.prod as two Finset.prod's multiplied together
macro "pUnion" : tactic => `(tactic| (
  convert (prod_union _)
  · ext n; rw[mem_union]; grind
  · apply disjoint_left.mpr; grind
  ))
lemma prod_range_split (w : ℂ) {q : ℂ} {x y : ℕ} : ∏ n ∈ range (x+y), (1 - w*q^n)
      = (∏ n ∈ range y, (1 - w*q^n)) * ∏ n ∈ Ico y (x+y), (1 - w*q^n) := by pUnion

-- For rewriting a Finset.prod by shifting the terms
macro "pBij" f:term " inv " g:term : tactic => `(tactic| (
  apply prod_bij $f (by grind) (by grind) (by intro z _; let := $g z; use this; grind) (by grind)
  ))

-- A special version of pBij specifically designed for expressions that go between
  -- a (1 - q*q^x) form and a (1 - q^(x+1)) form: See Section EQ1_lemmas
macro "pBij'" f:term " inv " g:term : tactic => `(tactic| (
  simp only [←pow_succ'];
  simp only [←zpow_natCast];
  pBij $f inv $g
  ))

-- Useful for rewriting terms in a product
macro "mul_rw" a:term "AND" b:term : tactic => `(tactic| (
  repeat rw[mul_right_comm _ $a];
  repeat rw[mul_right_comm _ $b];
  rw[mul_assoc]
))

-- For evaluating polynomials
macro "eval_poly" : tactic => `(tactic| (
  simp only [eval_finsetSum, eval_prod, eval_mul, eval_add, eval_sub, eval_X, eval_C, eval_one]
  ))

end tools_and_lemmas


section Tendsto_Lemmas
open Topology Filter

-- Lemmas: Tendsto Manipulations
lemma h_0 {f : ℕ → ℂ} : Tendsto f atTop (𝓝 1) →
    Tendsto (fun n ↦ ‖f n‖) atTop (𝓝 1) := by
  rw[←norm_one (α := ℝ)]; convert Tendsto.norm; rw[norm_one, norm_one]
lemma h_1 {f g : ℕ → ℂ} {c : ℂ} : Tendsto f atTop (𝓝 c) →
    Tendsto g atTop (𝓝 0) → Tendsto (fun n ↦ f n + g n) atTop (𝓝 c) := by
  nth_rw 2 [←add_zero c]; apply Tendsto.add
lemma h_2 {f g : ℕ → ℂ} {c : ℂ} : Tendsto f atTop (𝓝 c) →
    Tendsto g atTop (𝓝 0) → Tendsto (fun n ↦ f n - g n) atTop (𝓝 c) := by
  nth_rw 2 [←sub_zero c]; apply Tendsto.sub
lemma h_3 {f : ℕ → ℂ} {c : ℂ} : Tendsto f atTop (𝓝 0) →
    Tendsto (fun n ↦ c * f n) atTop (𝓝 0) := by
  nth_rw 2 [←mul_zero c]; apply Tendsto.const_mul
lemma h_4 {f : ℕ → ℂ} {c : ℂ} : Tendsto f atTop (𝓝 0) →
    Tendsto (fun n ↦ f n * c) atTop (𝓝 0) := by
  nth_rw 2 [←zero_mul c]; apply Tendsto.mul_const
lemma h_5 {f : ℕ → ℝ} : Tendsto f atTop (𝓝 1) →
    Tendsto (fun n ↦ (f n)⁻¹) atTop (𝓝 1) := by
    nth_rw 2 [one_eq_inv.mpr rfl]; exact fun h ↦ Tendsto.inv₀ h (one_ne_zero)
lemma h_6 {q : ℂ} (qN1 : ‖q‖ < 1) : Tendsto (fun n ↦ q^(n+1)) atTop (𝓝 0) := by
  rw[(by ext; ring : (fun n ↦ q^(n+1)) = fun n ↦ q * q^n)]
  apply h_3 (tendsto_pow_atTop_nhds_zero_of_norm_lt_one qN1)
lemma h_7 {q : ℂ} (qN1 : ‖q‖ < 1) : Tendsto (fun n ↦ q^(n+2)) atTop (𝓝 0) := by
  rw[(by ext; ring : (fun n ↦ q^(n+2)) = fun n ↦ q^2 * q^n)]
  apply h_3 (tendsto_pow_atTop_nhds_zero_of_norm_lt_one qN1)
lemma h_8 {q : ℂ} (qN1 : ‖q‖ < 1) : Tendsto (fun n ↦ q^(2*n+2)) atTop (𝓝 0) := by
  rw[(by ext; ring : (fun n ↦ q^(2*n+2)) = fun n ↦ q^(n+1) * q^(n+1)), ←zero_mul 0]
  apply Tendsto.mul <;> exact h_6 qN1
lemma h_9 {q : ℂ} (qN1 : ‖q‖ < 1) : Tendsto (fun n ↦ q^(2*n+4)) atTop (𝓝 0) := by
  rw[(by ext; ring : (fun n ↦ q^(2*n+4)) = fun n ↦ q^(n+2) * q^(n+2)), ←zero_mul 0]
  apply Tendsto.mul <;> exact h_7 qN1
lemma EQ2_1 {x y : ℂ} {f : ℕ → ℂ} (x0 : x ≠ 0) : Tendsto (fun n ↦ x⁻¹ * f n) atTop (𝓝 y) ↔
    Tendsto f atTop (𝓝 (x*y)) := by
  nth_rw 1 [←inv_mul_cancel_left₀ x0 y]
  have : (fun n ↦ x⁻¹ * f n) = (fun n ↦ x⁻¹ • f n) := by ext; rw[smul_eq_mul]
  rw[this, ←smul_eq_mul x⁻¹]
  rw[tendsto_const_smul_iff₀ (inv_ne_zero x0)]

end Tendsto_Lemmas


section W_Lemmas
open Finset Topology Filter Polynomial

-- The (a; q)_n notation
def W (a q : ℂ) (n : ℕ) := ∏ i ∈ range n, (1 - a * q^i)

-- Showing that W and its terms are nonzero
lemma W0_terms {a q : ℂ} (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1) (x : ℕ) : 1 - a*q^x ≠ 0 := by
  have hqx := pow_le_pow_left₀ (norm_nonneg q) qN1.le x; rw[one_pow] at hqx
  intro eq
  apply eq_of_sub_eq_zero at eq
  apply_fun fun X ↦ ‖X‖ at eq
  rw[norm_one, norm_mul, norm_pow] at eq
  have := mul_lt_mul' hqx aN1 (norm_nonneg a) one_pos
  rw[one_mul] at this
  linarith
lemma W0_terms' {q : ℂ} {x : ℕ} (qN1 : ‖q‖ < 1) (x0 : x ≠ 0) : 1 - q^x ≠ 0 := by
  intro eq
  apply eq_of_sub_eq_zero at eq
  have := pow_lt_pow_left₀ qN1 (norm_nonneg q) x0
  rw[←norm_pow q, ←eq, norm_one, one_pow] at this
  linarith
lemma W0 {a q : ℂ} (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1) (n : ℕ) : W a q n ≠ 0 := by
  rw[W, prod_ne_zero_iff]
  intro i _ eq
  apply eq_of_sub_eq_zero at eq
  apply_fun Norm.norm at eq
  rw[norm_mul, norm_pow, norm_one] at eq
  rw[eq] at aN1
  have := pow_le_pow_left₀ (norm_nonneg q) qN1.le i
  rw[one_pow] at this
  have := mul_le_mul_of_nonneg_left this (norm_nonneg a)
  linarith

-- Limit of the factors of W
lemma W_terms_tendsto_1 {a q : ℂ} (qN1 : ‖q‖ < 1) (x : ℕ) :
    Tendsto (fun n ↦ 1 - a*q^(n+x)) atTop (𝓝 1) := by
  apply h_2 tendsto_const_nhds; apply h_3
  apply Tendsto.comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one qN1) (tendsto_add_atTop_nat (x))

-- A formula for the quotient of two W terms
lemma WW_quotA {a q : ℂ} (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1) {x y : ℕ}
    : W a q (x+y) * (W a q x)⁻¹ = ∏ i ∈ range y, (1-a*q^(x+i)) := by
  rw[W, W, add_comm, prod_range_split]
  have : (∏ n ∈ range x, (1 - a * q ^ n)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    exact fun n _ ↦ W0_terms aN1 qN1 n
  field_simp
  pBij (fun n _ ↦ n-x) inv (fun m ↦ m+x)

lemma WW_quotA' {a q : ℂ} (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1) {x y : ℕ}
  : W a q x * (W a q (x+y))⁻¹ = ∏ i ∈ range y, (1-a*q^(x+i))⁻¹ := by
  rw[W, W, add_comm, prod_range_split, prod_inv_distrib]
  have : (∏ n ∈ range x, (1 - a * q ^ n)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    exact fun n _ ↦ W0_terms aN1 qN1 n
  rw[mul_inv, ←mul_assoc, mul_inv_cancel₀ this, one_mul]
  apply congrArg (fun X ↦ X⁻¹)
  pBij (fun n _ ↦ n-x) inv (fun m ↦ m+x)

-- The quotient of two W terms approaches 1 if they always remain |x-y| away from each other.
lemma WW_tendsto_1 {a q : ℂ} (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1) (x y : ℕ) :
    Tendsto (fun N ↦ W a q (N+x) * (W a q (N+y))⁻¹) atTop (𝓝 1) := by
  wlog _ : x ≥ y generalizing x y with H
  · have : (fun N ↦ W a q (N + x) * (W a q (N + y))⁻¹)
        = (fun N ↦ (W a q (N + y) * (W a q (N + x))⁻¹)⁻¹) := by
      ext N
      have : (W a q (N + x)) ≠ 0 := W0 aN1 qN1 _
      field
    rw[this, ←inv_one]
    apply Tendsto.inv₀ _ one_ne_zero
    exact H y x (by linarith)
  simp only [W]
  suffices : Tendsto (fun N ↦ ∏ n ∈ Ico (N+y) (N+x), (1-a*q^n)) atTop (𝓝 1)
  · apply Tendsto.congr _ this; intro N
    have : (x-y) + (N+y) = N + x := by omega
    nth_rw 2 [←this]
    rw[prod_range_split, this]
    have : (∏ n ∈ range (N + y), (1 - a * q ^ n)) ≠ 0 := by
      rw[prod_ne_zero_iff]; rintro n -
      exact W0_terms aN1 qN1 n
    rw[mul_right_comm, mul_inv_cancel₀ this, one_mul]
  apply Tendsto.congr (f₁ := (fun N ↦ ∏ n ∈ range (x-y), (1 - a * q ^ (N+y+n))))
  · intro N
    pBij (fun n _ ↦ N + y + n) inv (fun m ↦ m - N - y)
  have : 1 = ∏ n ∈ range (x - y), 1 := Eq.symm prod_const_one
  nth_rw 2 [←prod_const_one (s := range (x-y))]
  apply tendsto_finsetProd
  simp only [add_assoc]
  exact fun n _ ↦ W_terms_tendsto_1 qN1 _

lemma WW_tendsto_1' {a q : ℂ} (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1) (x y : ℕ) :
    Tendsto (fun N ↦ W a q (N-x) * (W a q (N-y))⁻¹) atTop (𝓝 1) := by
  have : Tendsto (fun N ↦ W a q (N+y) * (W a q (N+x))⁻¹) atTop (𝓝 1) := WW_tendsto_1 aN1 qN1 y x
  have := Tendsto.comp (WW_tendsto_1 aN1 qN1 y x) (tendsto_sub_atTop_nat (x+y))
  apply Filter.Tendsto.congr' _ this
  apply sets_of_superset (x := Set.Ici (x+y))
  · simp only [Filter.mem_sets, mem_atTop_sets, Set.mem_Ici]; use (x+y); tauto
  intro i ni; rw[Set.mem_Ici] at ni
  dsimp
  rw[(by omega : i - (x+y) + y = i - x), (by omega : i - (x+y) + x = i - y)]

end W_Lemmas


section EQ1_lemmas
open Finset BigOperators Polynomial

-- Lemmas: polyConditionA Unions
lemma pCA2 {q : ℂ} {N m : ℕ} (mR : m < N + 1) : ∏ n ∈ (range (N+1)).erase m, (1 - q ^ ((n:ℤ)-m))
      = (∏ n ∈ range m, (1 - q^((n:ℤ)-m))) * ∏ n ∈ Ioc m N, (1 - q^((n:ℤ)-m)) := by pUnion
lemma pCA3 {a q : ℂ} {N m : ℕ} (mR : m < N + 1) : ∏ n ∈ (range (N+1)).erase 0, (1 - a*q^((n:ℤ)-m-1))
      = (∏ n ∈ Icc 1 m, (1 - a*q^((n:ℤ)-m-1))) * ∏ n ∈ Ioc m N, (1 - a*q^((n:ℤ)-m-1)) := by pUnion

-- Lemmas: polyConditionA Bound Changes
lemma pCA4 {q : ℂ} {N m : ℕ} : ∏ n ∈ Ioc m N, (1 - q^((n:ℤ)-m))
  = ∏ n ∈ range (N-m), (1 - q*q^n) := by pBij' (fun x _ ↦ x - m - 1) inv (fun z ↦ z + m + 1)
lemma pCA5 {a q : ℂ} {N m : ℕ} : ∏ n ∈ Ioc m N, (1 - a*q^((n:ℤ)-m-1))
  = ∏ n ∈ range (N-m), (1 - a*q^n) := by
  simp only [←zpow_natCast]; pBij (fun x _ ↦ x - m - 1) inv (fun z ↦ z + m + 1)
lemma pCA6 {q : ℂ} {m : ℕ} : ∏ n ∈ range m, (1 - q^((m:ℤ)-n)) = ∏ n ∈ range m, (1 - q*q^n) := by
  pBij' (fun x _ ↦ m - x - 1) inv (fun z ↦ m - z - 1)
lemma pCA7 {a q : ℂ} {N m : ℕ} : ∏ n ∈ (range (N+1)).erase 0, (1 - a*q^((n:ℤ)+m-1))
  = ∏ n ∈ Ico m (N+m), (1 - a*q^n) := by
  simp only [←zpow_natCast]; pBij (fun x _ ↦ x + m - 1) inv (fun z ↦ z + 1 - m)
lemma pCA8 {q : ℂ} {m : ℕ} : ∏ n ∈ Icc 1 m, (-q^((n:ℤ)-m-1)) = ∏ n ∈ range m, (-q^((n:ℤ)-m)) := by
  apply prod_bij (fun n _ ↦ n - 1) (by grind) (by grind) (by intro z _; use z + 1; grind)
  grind
lemma pCA9 {a q : ℂ} {m : ℕ} : ∏ n ∈ Icc 1 m, (1 - a⁻¹*q^((m:ℤ)+1-n))
    = ∏ n ∈ range m, (1 - a⁻¹*q*q^n) := by
  simp only [mul_assoc]
  pBij' (fun n _ ↦ m - n) inv (fun z ↦ m - z)

-- Lemmas: polyConditionA Other
lemma pCA10 {q : ℂ} {N m : ℕ} (mR : m < N + 1) : (∏ n ∈ (range (N+1)).erase m, (1 - q^(n+m)))
    * (if m = 0 then 1 else (1 + q^m)) = ∏ n ∈ Ico m (N+m), (1 - q*q^n) := by
  have : ∀ n : ℕ, q*q^n = q^(n+1) := by simp only [pow_succ']; tauto
  by_cases m0 : m = 0
  · rw[if_pos m0, mul_one, m0]
    pBij (fun x _ ↦ x - 1) inv (fun z ↦ z + 1)
  · rw[if_neg m0, ←prod_erase_mul _ _ (a := 0) (by grind), mul_assoc, zero_add]
    rw[(by ring : (1 - q^m) * (1 + q^m) = (1 - q^(m + m))), erase_right_comm]
    rw[prod_erase_mul _ _ (by grind)]
    pBij (fun x _ ↦ x + m - 1) inv (fun z ↦ z + 1 - m)

end EQ1_lemmas


noncomputable section EQ1
variable (a q : ℂ)
open Finset BigOperators Polynomial

-- The A_n
-- Note A_0 simplifies to (W a q N)^2 / (W q q N)^2
def A (N n : ℕ) := a^n * (W (a⁻¹ * q) q n) * (W a q n)⁻¹
  * ((W a q (N+n)) * (W a q (N-n)) * ((W q q (N+n))⁻¹ * (W q q (N-n))⁻¹))
  * if n = 0 then 1 else (1+q^n)

-- The numerator and denominator of the left side of (1)
-- Note Dw q 0 simplifies to 2 - X
def Up (n : ℕ) : ℂ[X] := if n = 0 then 1 else 1 - C (a*q^(n-1)) * X + C (a^2*q^(2*n-2))
def Dw (n : ℕ) : ℂ[X] := 1 - C (q^n) * X + C (q^(2*n))

-- The roots for each denominator
-- Note rt q 0 = 2
def rt (n : ℕ) : ℂ := (1 + q^(2*n)) / q^n

-- A lemma that relies on the definition of Up
lemma pCA11 {a q : ℂ} {N m : ℕ} (q0 : q ≠ 0) : ∏ n ∈ range (N + 1), eval (rt q m) (Up a q n)
    = ∏ n ∈ (range (N + 1)).erase 0, ((1 - a*q^((n:ℤ)-m-1)) * (1 - a*q^((n:ℤ)+m-1))) := by
  rw[←prod_erase (range (N+1)) (by simp only [Up, if_pos, eval_one]) (a := 0)]
  apply prod_congr rfl
  intro n nE; apply mem_erase.mp at nE
  simp only [rt, Up, if_neg nE.1]; eval_poly
  field_simp; ring_nf
  rw[mul_comm (q^m) (a^2), mul_assoc (a^2), mul_assoc (a^2)]
  simp only [mul_comm _ a, mul_assoc a, ←zpow_natCast, ←zpow_add₀ q0]
  grind

-- Proving and Applying Equation 1
lemma polyConditionA (a q : ℂ) (N : ℕ) (q0 : q ≠ 0) (a0 : a ≠ 0) (qN1 : ‖q‖ < 1)
    (h₁ : ∀ n : ℕ, 1-a*q^n ≠ 0) :
    ∀ m ∈ range (N+1), eval (rt q m) (∑ t ∈ range (N+1), (C (A a q N t)
    * ∏ n ∈ (range (N + 1)).erase t, (Dw q n)) - ∏ n ∈ range (N+1), (Up a q n)) = 0 := by
  -- Remove the summands that equal 0
  intro m mR
  eval_poly
  have : ∑ t ∈ range (N + 1), (A a q N t * ∏ n ∈ (range (N + 1)).erase t, eval (rt q m) (Dw q n))
      = A a q N m * ∏ n ∈ (range (N + 1)).erase m, eval (rt q m) (Dw q n) := by
    apply sum_eq_single
    · intro t tR tm
      apply mul_eq_zero_of_right
      apply prod_eq_zero (mem_erase.mpr ⟨tm.symm, mR⟩)
      rw[Dw, rt]; eval_poly
      field
    · exact fun h ↦ False.elim (h mR)
  rw[this]; clear this
  simp only [A, W, Dw]
  apply mem_range.mp at mR
  -- Rewriting the A term and the right side of the Dw term
  have : (fun (n:ℕ) ↦ eval (rt q m) (1 - C (q^n) * X + C (q^(2*n))))
      = (fun (n:ℕ) ↦ ((1 - q^((n:ℤ)-m)) * (1 - q^(n+m)))) := by
    ext n; simp [rt]
    field_simp; ring_nf
    simp only [←zpow_natCast, ←zpow_add₀ q0, add_sub_cancel]
    rw[(by omega : (↑(m * 2) + ↑n + (↑n - ↑m)) = (m:ℤ) + ↑(n*2))]
    ring
  rw[prod_range_split a, prod_range_split q, this, prod_mul_distrib]; clear this -- have := pCA10 mR
  -- Rewriting the left side of the Dw term
  rw[pCA2 mR, pCA4]
  have : (fun (n:ℕ) ↦ 1 - q^((n:ℤ)-m))
      = (fun (n:ℕ) ↦ (-q^((n:ℤ)-m)) * (1 - q^((m:ℤ)-n))) := by
    ext n
    rw[mul_sub, mul_one, neg_mul, sub_neg_eq_add, ←zpow_add' (Or.inl q0)]
    ring_nf; rw[zpow_zero]; ring
  rw[this, prod_mul_distrib]; clear this
  rw[pCA6]
  -- Rewriting the Up term
  rw[pCA11 q0, prod_mul_distrib, pCA7, pCA3 mR, pCA5]
  have : (fun (n:ℕ) ↦ (1 - a*q^((n:ℤ)-m-1)))
    = (fun (n:ℕ) ↦ a * (-q^((n:ℤ)-m-1)) * (1 - a⁻¹*q^((m:ℤ)+1-n))) := by
    ext n
    rw[mul_assoc, mul_sub, mul_one, neg_mul, mul_comm a⁻¹, ←mul_assoc, ←zpow_add' (Or.inl q0)]
    rw[(by omega : ((n:ℤ) - ↑m - 1 + (↑m + 1 - ↑n)) = ↑0)]
    field
  rw[this, prod_mul_distrib, ←pow_card_mul_prod, pCA9, pCA8, (by simp : #(Icc 1 m) = m)]
  have : (∏ n ∈ range m, (1 - a*q^n)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro _ _
    exact h₁ _
  have (s : Finset ℕ) : (∏ n ∈ s, (1 - q*q^n)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro n _
    rw[mul_comm, ←pow_succ]
    exact W0_terms' qN1 (Nat.succ_ne_zero n)
  field_simp [fun s ↦ this s]
  rw[mul_comm (if m = 0 then 1 else 1 + q ^ m), pCA10 mR]
  ring

lemma eq_1 (a q : ℂ) (N : ℕ) (q0 : q ≠ 0) (a0 : a ≠ 0)
    (qN1 : ‖q‖ < 1) (h₁ : ∀ n : ℕ, 1-a*q^n ≠ 0) :
    ∑ m ∈ range (N+1), (C (A a q N m) * ∏ n ∈ (range (N + 1)).erase m, (Dw q n))
    = ∏ n ∈ range (N+1), (Up a q n) := by
  let f := ∑ m ∈ range (N+1), (C (A a q N m) * ∏ n ∈ (range (N + 1)).erase m, (Dw q n))
      - ∏ n ∈ range (N+1), (Up a q n)
  have : f.degree ≤ N := by
    apply (degree_sub_le _ _).trans
    have : degree (∑ m ∈ range (N + 1), C (A a q N m) * ∏ n ∈ (range (N + 1)).erase m, Dw q n)
        ≤ ↑N := by
      apply (degree_sum_le _ _).trans
      apply Finset.sup_le
      intro m mR; apply mem_range.mp at mR
      compute_degree
      rw[degree_prod]
      have : ∀ i ∈ (range (N + 1)).erase m, (Dw q i).degree = 1 := by
        rintro n -
        rw[Dw]
        compute_degree!
        exact fun h ↦ False.elim (q0 h)
      rw[sum_congr rfl this]
      simp only [sum_const, nsmul_eq_mul, mul_one, Nat.cast_le, ge_iff_le]
      rw[card_erase_of_mem (by simp; omega), card_range]
      norm_num
    apply max_le this
    rw[degree_prod]
    have : ∑ n ∈ range (N + 1), (Up a q n).degree ≤
        ∑ n ∈ range (N + 1), (if n = 0 then 0 else 1) := by
      apply sum_le_sum
      rintro n nN; apply mem_range.mp at nN
      by_cases n0 : (n = 0)
      · rw[n0, Up, if_pos rfl, if_pos rfl]
        compute_degree
      · rw[Up, if_neg n0, if_neg n0]
        compute_degree!
    apply this.trans
    rw[←sum_erase_add _ _ (by simp : 0 ∈ range (N+1)), if_pos rfl, add_zero]
    have : ∀ x ∈ (range (N + 1)).erase 0, (if x = 0 then 0 else 1) = (1 : WithBot ℕ) := by
      intro x xS; apply ne_of_mem_erase at xS
      rw[if_neg xS]
    rw[sum_congr rfl this]; simp
  apply eq_of_sub_eq_zero
  change f = 0
  by_contra! f0
  let H := card_roots f0
  apply this.trans' at H
  have : ↑((List.range (N+1)).map (fun n ↦ rt q n)) ≤ f.roots := by
    refine (Multiset.le_iff_subset ?_).mpr ?_
    · refine Multiset.coe_nodup.mpr ?_
      refine List.Nodup.map_on ?_ List.nodup_range
      intro m mR n nR eq
      rw[rt, rt] at eq
      wlog mnle : m ≤ n generalizing m n
      · exact (this n nR m mR (eq.symm) (Nat.le_of_not_le mnle)).symm
      · obtain ⟨k, rfl⟩ := (Nat.le.dest mnle)
        apply_fun (fun T ↦ T * q^(m+k)) at eq
        rw[pow_add] at eq
        field_simp at eq;
        symm at eq
        apply sub_eq_zero_of_eq at eq
        rw[add_mul, sub_add_eq_sub_sub] at eq
        rw[(by ring : 1 + q ^ (2 * (m + k)) - 1 * q ^ k - q ^ (2 * m) * q ^ k
            = (1 - q^(2*m+k)) * (1 - q^k))] at eq
        apply NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero at eq
        by_cases k0 : k = 0
        · rw[k0, add_zero]
        · rcases eq with T | T
          · have := W0_terms' qN1 (by omega : 2*m + k ≠ 0)
            contradiction
          · have : k = 0 := by by_contra; exact W0_terms' qN1 this T
            rw[this, add_zero]
    · intro _ rL
      obtain ⟨m, mR, rfl⟩ := List.mem_map.mp rL
      refine mem_roots'.mpr ⟨f0, ?_⟩
      apply IsRoot.def.mpr
      apply polyConditionA <;> assumption
  apply Multiset.card_le_card at this
  simp only [Multiset.coe_card, List.length_map, List.length_range, Order.add_one_le_iff] at this
  have _ : (N : WithBot ℕ) < ↑f.roots.card := by exact Nat.cast_lt.mpr this
  order

lemma eq_1_eval (a q x : ℂ) (N : ℕ) (q0 : q ≠ 0) (a0 : a ≠ 0)
    (qN1 : ‖q‖ < 1) (h₁ : ∀ n : ℕ, 1-a*q^n ≠ 0) :
    ∑ m ∈ range (N+1), ((A a q N m) * ∏ n ∈ (range (N + 1)).erase m, eval x (Dw q n))
    = ∏ n ∈ range (N+1), eval x (Up a q n) := by
  have eq := eq_1 a q N q0 a0 qN1 h₁
  apply_fun fun X ↦ eval x X at eq
  simp only [eval_finsetSum, eval_prod, eval_mul, eval_C] at eq
  exact eq

end EQ1


noncomputable section S_lemmas
open Finset Filter

-- The summands in the Summation of Equation 2
  -- Note it is shifted to be n ≥ 0 instead of n ≥ 1
def S (a q x : ℂ) (n : ℕ) := a^(n+1) * (W (a⁻¹*q) q (n+1)) * (1 + q^(n+1))
  * (W a q (n+1))⁻¹ * (1 - q^(n+1)*x + q^(2*n+2))⁻¹

-- S is nonzero for large enough N
lemma S0_eventually {a q x : ℂ} (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1)
    (h' : ∀ N : ℕ, 1 - a⁻¹*q*q^N ≠ 0) (h₂ : ∀ n : ℕ, 1-q^n*x+q^(2*n) ≠ 0) :
    ∀ᶠ (n : ℕ) in atTop, S a q x n ≠ 0 := by
  have : ‖a‖ > 0 := lt_of_le_of_ne (norm_nonneg a) (norm_ne_zero_iff.mpr a0).symm
  obtain ⟨N, h⟩ : ∃ N : ℕ, ‖q‖^N < ‖a‖ := exists_pow_lt_of_lt_one this qN1
  rw[Filter.eventually_atTop]; use N; intro n nN
  rw[S]; repeat apply mul_ne_zero
  · exact pow_ne_zero n a0
  · exact a0
  · rw[W, prod_ne_zero_iff]
    exact fun i _ eq ↦ h' i eq
  · intro eq; apply_fun fun X ↦ ‖X - q^(n+1)‖ at eq
    simp at eq
    have := pow_lt_pow_left₀ qN1 (norm_nonneg q) (by omega : n+1 ≠ 0)
    rw[one_pow] at this
    linarith
  · exact inv_ne_zero (W0 aN1 qN1 (n+1))
  · exact inv_ne_zero (h₂ _)

-- S is summable and bounded
lemma S_Summable {a q x : ℂ} (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1)
    (h₁ : ∀ n : ℕ, 1-a*q^n ≠ 0) (h₂ : ∀ n : ℕ, 1-q^n*x+q^(2*n) ≠ 0) : Summable (S a q x) := by
  by_cases! h' : ∃ N : ℕ, 1 - a⁻¹*q*q^N = 0
  · obtain ⟨N, h'⟩ := h'
    apply summable_of_hasFiniteSupport
    have : Function.support (S a q x) ⊆ ↑(range N) := by
      intro n (eq : S a q x n ≠ 0)
      apply mem_range.mpr; contrapose! eq
      have : W (a⁻¹ * q) q (n + 1) = 0 := by
        rw[W]; apply prod_eq_zero (mem_range.mpr <| Order.lt_add_one_iff.mpr eq)
        exact h'
      rw[S, this]
      ring
    apply Set.Finite.subset (finite_toSet (range N)) this
  apply summable_of_ratio_test_tendsto_lt_one aN1 (S0_eventually a0 aN1 qN1 h' h₂)
  have : ‖a‖ = ‖a‖ * 1 * 1 * 1 * 1 * 1 * 1 := by repeat rw[mul_one]
  rw[this]
  have : (fun n ↦ ‖S a q x (n + 1)‖ / ‖S a q x n‖) = (fun n ↦ ‖a‖ * ‖1-a⁻¹*q^(n+2)‖
      * ‖1+q^(n+2)‖ * ‖1-q^(n+1)*x+q^(2*n+2)‖ * ‖1-a*q^(n+1)‖⁻¹ * ‖1+q^(n+1)‖⁻¹
      * ‖1-q^(n+2)*x+q^(2*n+4)‖⁻¹) := by
    ext n; rw[S, S]
    repeat rw[norm_mul]
    rw[norm_pow, norm_pow, norm_inv, norm_inv, norm_inv, norm_inv]
    rw[div_eq_inv_mul]; repeat rw[mul_inv]
    rw[inv_inv, inv_inv, (by omega : n+1+1 = n+2), (by omega : 2*(n+1)+2 = 2*n+4)]
    repeat rw[←mul_assoc]
    have : ‖W (a⁻¹ * q) q (n + 2)‖ * ‖W (a⁻¹ * q) q (n + 1)‖⁻¹ = ‖1-a⁻¹*q^(n+2)‖ := by
      rw[W, W, ←prod_erase_mul _ _ (by simp : n+1 ∈ range (n+2)), norm_mul]
      rw[(by grind : (range (n+2)).erase (n+1) = range (n+1))]
      have : ‖∏ x ∈ range (n + 1), (1 - a⁻¹*q*q^x)‖ ≠ 0 := by
        rw[norm_ne_zero_iff, prod_ne_zero_iff]
        exact fun i _ eq ↦ h' i eq
      rw[mul_right_comm, mul_inv_cancel₀ this, one_mul, mul_assoc, ←pow_succ']
    mul_rw ‖W (a⁻¹ * q) q (n + 2)‖ AND ‖W (a⁻¹ * q) q (n + 1)‖⁻¹; rw[this]
    have : ‖W a q (n + 2)‖⁻¹ * ‖W a q (n + 1)‖ = ‖1-a*q^(n+1)‖⁻¹ := by
      rw[W, W, ←prod_erase_mul _ _ (by simp : n+1 ∈ range (n+2)), norm_mul, mul_inv]
      rw[(by grind : (range (n+2)).erase (n+1) = range (n+1))]
      have : ‖∏ x ∈ range (n + 1), (1 - a * q ^ x)‖ ≠ 0 := by
        rw[norm_ne_zero_iff, prod_ne_zero_iff]
        rintro i -
        exact h₁ i
      field
    mul_rw ‖W a q (n + 2)‖⁻¹ AND ‖W a q (n + 1)‖; rw[this]
    have aN0 := norm_ne_zero_iff.mpr a0
    field
  rw[this]
  repeat apply Filter.Tendsto.mul
  · exact tendsto_const_nhds
  · apply h_0; apply h_2 tendsto_const_nhds; apply h_3 (h_7 qN1)
  · apply h_0; apply h_1 tendsto_const_nhds (h_7 qN1)
  · apply h_0; apply h_1 _ (h_8 qN1)
    apply h_2 tendsto_const_nhds
    apply h_4; apply h_6 qN1
  · apply h_5; apply h_0; apply h_2 tendsto_const_nhds
    apply h_3 (h_6 qN1)
  · apply h_5; apply h_0; apply h_1 tendsto_const_nhds (h_6 qN1)
  · apply h_5; apply h_0; apply h_1
    · apply h_2 tendsto_const_nhds; apply h_4 (h_7 qN1)
    · apply h_9 qN1

end S_lemmas


noncomputable section B_lemmas

-- The bounds used within the EQ_2 proof
def B (a q x : ℂ) (n : ℕ) := ‖S a q x n‖
    * Real.exp (2 * ((1-‖a‖)⁻¹ + (1-‖q‖)⁻¹) * (1-‖q‖)⁻¹)

-- The series B converges
lemma B_Summable {a q x : ℂ} (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1)
    (h₁ : ∀ n : ℕ, 1-a*q^n ≠ 0) (h₂ : ∀ n : ℕ, 1-q^n*x+q^(2*n) ≠ 0) : Summable (B a q x) := by
  apply Summable.mul_right
  exact Summable.norm (S_Summable a0 aN1 qN1 h₁ h₂)

end B_lemmas


noncomputable section SS_lemmas
open Finset Filter Topology Real

-- Some summands for a "helper" Summation in the proof
  -- Note it is shifted to be n ≥ 0 instead of n ≥ 1
def SS (a q x : ℂ) (n N : ℕ) := if N ≤ n then 0 else (S a q x n)
  * ((W a q (N+n+1)) * (W a q (N-n-1)) * ((W q q (N+n+1))⁻¹ * (W q q (N-n-1))⁻¹))
  * ((W q q N)^2 * (W a q N)⁻¹^2)

lemma SS_alt {a q x : ℂ} (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1) (n N : ℕ)
    : SS a q x n N = if N ≤ n then 0 else (S a q x n)
    * ∏ i ∈ range (n+1), ((1 + a*q^(N-n-1+i) * (1-q^(n+1)) * (1-a*q^(N-n-1+i))⁻¹)
    * (1 + q*q^(N-n-1+i) * (q^(n+1)-1) * (1-q*q^(N+i))⁻¹)) := by
  rw[SS]
  by_cases Nnle : N ≤ n
  · rw[if_pos Nnle, if_pos Nnle]
  rw[if_neg Nnle, if_neg Nnle, mul_assoc]
  apply congrArg (fun X ↦ (S a q x n) * X)
  have : ((W a q (N+n+1)) * (W a q (N-n-1)) * ((W q q (N+n+1))⁻¹ * (W q q (N-n-1))⁻¹))
    * ((W q q N)^2 * (W a q N)⁻¹^2)
    = (W a q (N+n+1) * (W a q N)⁻¹) * (W a q (N-n-1) * (W a q N)⁻¹)
    * ((W q q N * (W q q (N+n+1))⁻¹) * (W q q N * (W q q (N-n-1))⁻¹)) := by ring
  rw[this]; clear this
  nth_rw 4 7 [(by omega : N = (N-n-1) + (n+1))]
  rw[add_assoc, WW_quotA aN1 qN1, WW_quotA' aN1 qN1, WW_quotA' qN1 qN1, WW_quotA qN1 qN1]
  rw[prod_mul_distrib, ←prod_mul_distrib, ←prod_mul_distrib]
  congr
  · ext i
    nth_rw 3 [←mul_inv_cancel₀ (W0_terms aN1 qN1 _)]
    rw[←add_mul]
    apply congrArg (fun X ↦ X*_)
    ring_nf
    nth_rw 3 [←pow_one q]
    repeat rw[mul_assoc]
    repeat rw[←pow_add]
    rw[(by omega : 1+(i+(N-n-1+n)) = N + i)]
  · ext i
    nth_rw 3 [←mul_inv_cancel₀ (W0_terms qN1 qN1 _)]
    rw[mul_comm, ←add_mul]
    apply congrArg (fun X ↦ X*_)
    ring_nf
    nth_rw 7 [←pow_one q]
    repeat rw[mul_assoc]
    repeat rw[←pow_add]
    rw[(by omega : 2+(N-n-1+(i+n)) = 1+(i+N))]
    ring

lemma SS_Bounded_Eventually {a q x : ℂ} (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1) :
    ∀ᶠ (N : ℕ) in atTop, ∀ (n : ℕ), ‖SS a q x n N‖ ≤ B a q x n := by
  apply Eventually.of_forall
  intro N n
  rw[B]
  by_cases Nnle : N ≤ n
  · rw[SS, if_pos Nnle, norm_zero]
    apply mul_nonneg (norm_nonneg _) (exp_nonneg _)
  rw[SS_alt aN1 qN1, if_neg Nnle, norm_mul]
  apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
  have hqN (w : ℕ) : ‖q‖^w ≤ 1 := by rw[←one_pow w]; gcongr
  have H (i : ℕ) : (1 + a * q^(N-n-1+i) * (1-q^(n+1)) * (1-a*q^(N-n-1+i))⁻¹ ≠ 0)
      ∧ (1 + q * q^(N-n-1+i) * (q^(n+1)-1) * (1-q*q^(N+i))⁻¹ ≠ 0) := by
    constructor <;> (
      rw[mul_sub, mul_one, mul_assoc, ←pow_add, (by omega : (N-n-1+i) + (n+1) = N+i)]
      intro eq
      apply neg_eq_of_add_eq_zero_right at eq
      symm at eq
      apply eq_mul_of_mul_inv_eq₀ (by grind) at eq
      rw[neg_one_mul, neg_sub, sub_right_inj] at eq
      have : (1:ℝ) < 1 := by
        calc
          _ = ‖(1:ℂ)‖ := norm_one.symm
          _ = ‖_*q^_‖ := by rw[←eq]
          _ = ‖_‖ * ‖q‖^_ := by nth_rw 1 [norm_mul, norm_pow]
          _ < 1 * 1 := mul_lt_mul_of_nonneg_of_pos (by assumption) (hqN _) (norm_nonneg _)
              one_pos
          _ = 1 := one_mul 1
      linarith
    )
  have : 0 < ‖∏ i ∈ range (n + 1), (1 + a*q^(N-n-1+i) * (1-q^(n+1)) * (1-a*q^(N-n-1+i))⁻¹)
      * (1+q*q^(N-n-1+i) * (q^(n+1)-1) * (1-q*q^(N+i))⁻¹)‖ := by
    rw[norm_pos_iff, prod_ne_zero_iff]
    rintro n -; apply mul_ne_zero_iff.mpr
    exact H n
  rw[←exp_log this]; clear this
  apply exp_le_exp_of_le
  rw[norm_prod, log_prod]; swap
  · rintro i -
    rw[norm_mul]; apply mul_ne_zero <;> rw[norm_ne_zero_iff]
    · exact (H i).1
    · exact (H i).2
  calc
    _ ≤ ∑ i ∈ range (n+1), 2 * ((1-‖a‖)⁻¹ + (1-‖q‖)⁻¹) * ‖q‖^i := by
      apply sum_le_sum; rintro i -
      obtain ⟨ha0, hq0⟩ := H i
      rw[norm_mul, log_mul _ _]
      rotate_left
      · rw[norm_ne_zero_iff]; assumption
      · rw[norm_ne_zero_iff]; assumption
      have log_norm_one_plus {w : ℂ} (h : w ≠ -1) : log ‖1+w‖ ≤ ‖w‖ := by
        calc
          _ ≤ log (1 + ‖w‖) := by
            gcongr
            · rw[norm_pos_iff]
              contrapose! h
              grind only
            rw[←norm_one (α := ℂ)]
            exact norm_add_le 1 w
          _ ≤ _ := by
            nth_rw 2 [(by ring : ‖w‖ = 1 + ‖w‖ - 1)]
            apply log_le_sub_one_of_pos
            linarith [norm_nonneg w]
      calc
        _ ≤ ‖a * q^(N-n-1+i) * (1-q^(n+1)) * (1-a*q^(N-n-1+i))⁻¹‖
            + ‖q * q^(N-n-1+i) * (q^(n+1)-1) * (1-q*q^(N+i))⁻¹‖ := by
          apply add_le_add <;> (apply log_norm_one_plus; grind only)
        _ = ‖q‖^(N-n-1) * ‖1-q^(n+1)‖
            * (‖a‖*‖1-a*q^(N-n-1+i)‖⁻¹ + ‖q‖*‖1-q*q^(N+i)‖⁻¹) * ‖q‖^i := by
          rw[mul_add, add_mul]
          nth_rw 2 [←norm_neg (1-q^(n+1))]
          simp only [←norm_pow, ←norm_inv, ←norm_mul]
          grind
        _ ≤ _ := by
          rw[←one_mul 2]
          have (w : ℕ) : ‖q‖^w ≤ 1 := by rw[←one_pow w]; gcongr
          gcongr
          · exact this _
          · calc
              ‖1-q^(n+1)‖ ≤ ‖(1:ℂ)‖ + ‖q^(n+1)‖ := norm_sub_le _ _
              _ = 1 + ‖q‖^(n+1) := by rw[norm_one, norm_pow]
              _ ≤ 1 + 1 := by gcongr; exact this _
              _ = 2 := one_add_one_eq_two
          · rw[←one_mul (1-‖a‖)⁻¹]; gcongr
            calc
              _ ≤ 1 - ‖a‖*‖q‖^(N-n-1+i) := by nth_rw 1 [←mul_one ‖a‖]; gcongr; exact this _
              _ = 1 - ‖a*q^(N-n-1+i)‖ := by rw[norm_mul, norm_pow]
              _ ≤ _ := by rw[←norm_one (α := ℂ)]; apply norm_sub_norm_le
          · rw[←one_mul (1-‖q‖)⁻¹]; gcongr
            calc
              _ ≤ 1 - ‖q‖*‖q‖^(N+i) := by nth_rw 1 [←mul_one ‖q‖]; gcongr; exact this _
              _ = 1 - ‖q*q^(N+i)‖ := by rw[norm_mul, norm_pow]
              _ ≤ _ := by rw[←norm_one (α := ℂ)]; apply norm_sub_norm_le
    _ = 2 * ((1-‖a‖)⁻¹ + (1-‖q‖)⁻¹) * ∑ i ∈ range (n+1), ‖q‖^i := by rw[mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _
      · apply mul_nonneg zero_le_two
        apply add_nonneg <;> (rw[inv_nonneg]; linarith)
      apply le_of_mul_le_mul_left _ (by linarith : 0 < 1 - ‖q‖)
      rw[mul_inv_cancel₀ (by linarith), mul_comm]
      rw[geom_sum_mul_of_le_one qN1.le]
      linarith [pow_nonneg (norm_nonneg q) (n+1)]

-- SS converges to S as N → ∞
lemma SS_Tendsto_S {a q x : ℂ} (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1) (n : ℕ) :
    Tendsto (fun N ↦ SS a q x n N) atTop (𝓝 (S a q x n)) := by
  simp only [SS]
  suffices H : Tendsto (fun N ↦ S a q x n * (W a q (N+n+1) * (W a q N)⁻¹)
      * (W a q (N-n-1) * (W a q N)⁻¹) * (W q q N * (W q q (N+n+1))⁻¹)
      * (W q q N * (W q q (N-n-1))⁻¹)) atTop (𝓝 (S a q x n * 1 * 1 * 1 * 1))
  · repeat rw[mul_one] at H
    apply Filter.Tendsto.congr' _ H
    apply sets_of_superset (x := Set.Ici (n+1))
    · simp only [Filter.mem_sets, mem_atTop_sets, Set.mem_Ici]; use (n+1); tauto
    intro i ni; rw[Set.mem_Ici] at ni
    dsimp; rw[if_neg (Nat.not_le_of_lt ni)]
    ring
  apply Tendsto.mul _
  · simp only [Nat.sub_sub]
    exact WW_tendsto_1' qN1 qN1 0 (n+1)
  apply Tendsto.mul _
  · exact WW_tendsto_1 qN1 qN1 0 (n+1)
  apply Tendsto.mul _
  · simp only [Nat.sub_sub]
    exact WW_tendsto_1' aN1 qN1 (n+1) 0
  apply Tendsto.mul _
  · exact WW_tendsto_1 aN1 qN1 (n+1) 0
  · exact tendsto_const_nhds

end SS_lemmas


noncomputable section EQ2_lemmas
open Finset
variable (a q x : ℂ)

-- The factors in the Product of Equation 2
  -- Note it is shifted to be n ≥ 0 instead of n ≥ 1
def P (n : ℕ) := (1 - a*q^n*x + a^2*q^(2*n)) * (1 - q^(n+1)*x + q^(2*n+2))⁻¹
  * ((1 - q^(n+1))^2 * (1 - a*q^n)⁻¹^2)

-- Lemmas: Other
lemma pEQ2_1 {a q x : ℂ} : (fun n ↦ P a q x n) = (fun n ↦ Polynomial.eval x (Up a q (n+1))
    * (Polynomial.eval x (Dw q (n+1)))⁻¹ * ((1 - q^(n+1))^2 * (1 - a*q^n)⁻¹^2)) := by
  ext n
  rw[P, Up, Dw, if_neg (Nat.succ_ne_zero n)]
  eval_poly
  rw[Nat.add_sub_self_right, (by omega : (2*(n+1) - 2) = 2*n), mul_add, mul_one]

lemma pEQ2_2 {a q x : ℂ} {N : ℕ} (h₂ : ∀ n : ℕ, 1-q^n*x+q^(2*n) ≠ 0) :
    (∑ i ∈ range (N + 1), (∏ x_1 ∈ range (N + 1), Polynomial.eval x (Dw q x_1))⁻¹ *
    (A a q N i * ∏ n ∈ (range (N + 1)).erase i, Polynomial.eval x (Dw q n)))
    = (∑ i ∈ range (N + 1), (A a q N i * (Polynomial.eval x (Dw q i))⁻¹)) := by
  apply sum_congr rfl
  intro n nR
  nth_rw 2 [mul_comm]; rw[←mul_assoc]
  rw[←prod_erase_mul _ _ nR]
  have : (∏ m ∈ (range (N+1)).erase n, Polynomial.eval x (Dw q m)) ≠ 0 := by
    rw[prod_ne_zero_iff]
    intro n _
    rw[Dw]; eval_poly
    exact h₂ n
  field

lemma EQ2_3 (a q x : ℂ) (N : ℕ) (qN1 : ‖q‖ < 1) (h₁ : ∀ n : ℕ, 1-a*q^n ≠ 0) :
    (2-x)⁻¹ = A a q N 0 * (Polynomial.eval x (Dw q 0))⁻¹ * (W q q N ^ 2 * (W a q N)⁻¹^2) := by
  rw[A, Dw]; eval_poly; rw[if_true]
  simp only [W, range_zero, prod_empty]
  have : (∏ i ∈ range N, (1 - q * q ^ i)) ≠ 0 := by
    rw[prod_ne_zero_iff]
    intro n _
    rw[←pow_succ']
    apply W0_terms' qN1 (Nat.succ_ne_zero n)
  have : (∏ i ∈ range N, (1 - a * q ^ i)) ≠ 0 := by
    rw[prod_ne_zero_iff]
    intro n _
    exact h₁ n
  grind

lemma pEQ2_4 {a q x : ℂ} {N : ℕ} (qN1 : ‖q‖ < 1)
    (h₁ : ∀ n : ℕ, 1-a*q^n ≠ 0) : (2 - x)⁻¹ + ∑ n ∈ range N, SS a q x n N
    = (∑ n ∈ range (N + 1), A a q N n * (Polynomial.eval x (Dw q n))⁻¹)
    * (W q q N ^ 2 * (W a q N)⁻¹^2) := by
  have : ∑ n ∈ range N, SS a q x n N = ∑ n ∈ (range (N+1)).erase 0, SS a q x (n-1) N := by
    apply sum_bij (fun n _ ↦ n + 1) (by grind) (by grind)
      (by intro z _; use z - 1; grind) (by grind)
  rw[this]; clear this
  rw[←sum_erase_add _ _ (by simp : 0 ∈ range (N+1)), add_mul]
  rw[EQ2_3 a q x N qN1 h₁, add_comm]
  apply congrArg (fun X ↦ X + _)
  rw[sum_mul]
  apply sum_congr rfl
  intro n nE
  rw[SS, S, A, Dw]; eval_poly
  rw[mem_erase, mem_range] at nE
  rw[if_neg nE.1, if_neg (by omega)]
  rw[(by omega : n - 1 + 1 = n), (by omega : (2 * (n - 1) + 2) = 2*n)]
  rw[(by omega : (N + (n - 1) + 1) = N + n), (by omega : (N - (n - 1) - 1) = N - n)]
  repeat rw[mul_right_comm _ (1 + q^n)]
  repeat rw[mul_right_comm _ (1 - q^n*x + q^(2*n))⁻¹]

lemma pEQ2_5 {a q x : ℂ} (q0 : q ≠ 0) (a0 : a ≠ 0) (qN1 : ‖q‖ < 1)
    (h₁ : ∀ n : ℕ, 1-a*q^n ≠ 0) (h₂ : ∀ n : ℕ, 1-q^n*x+q^(2*n) ≠ 0) :
    (fun N ↦ (2-x)⁻¹ * ∏ n ∈ range N, P a q x n) = (fun N ↦ (2-x)⁻¹ + ∑' n : ℕ, SS a q x n N) := by
  ext N
  rw[tsum_eq_sum (s := range N)]; swap
  · intro n nR
    by_cases! Nnle : N ≤ n
    · rw[SS, if_pos Nnle]
    · rw[mem_range] at nR
      linarith
  rw[pEQ2_1, prod_mul_distrib, prod_mul_distrib]
  have : (∏ n ∈ range N, Polynomial.eval x (Up a q (n+1)))
      = ∏ n ∈ range (N+1), Polynomial.eval x (Up a q n) := by
    have : Polynomial.eval x (Up a q 0) = 1 := by rw[Up, if_pos, Polynomial.eval_one]; rfl
    have : ∏ n ∈ range (N+1), Polynomial.eval x (Up a q n)
        = ∏ n ∈ (range (N+1)).erase 0, Polynomial.eval x (Up a q n) := by
      rw[prod_erase _ (f := fun n ↦ Polynomial.eval x (Up a q n)) this]
    rw[this]
    pBij (fun n _ ↦ n + 1)  inv (fun z ↦ z - 1)
  rw[this, prod_inv_distrib]; clear this
  nth_rw 3 [mul_comm]; repeat rw[←mul_assoc]
  have : (∏ n ∈ range N, Polynomial.eval x (Dw q (n+1)))
      = ∏ n ∈ (range (N+1)).erase 0, Polynomial.eval x (Dw q n) := by
    pBij (fun n _ ↦ n + 1)  inv (fun z ↦ z - 1)
  rw[this]; clear this
  rw[←eq_1_eval a q x N q0 a0 qN1 h₁]
  have : (2 - x)⁻¹ = (Polynomial.eval x (Dw q 0))⁻¹ := by rw[Dw, inv_inj]; eval_poly; ring
  nth_rw 1 [mul_comm (2-x)⁻¹, this, ←mul_inv,
    prod_erase_mul _ (by simp : 0 ∈ range (N+1)) (f := fun n ↦ Polynomial.eval x (Dw q n))]
  rw[mul_sum, pEQ2_2 h₂]
  rw[prod_mul_distrib, prod_pow, (by ext; ring : (fun n ↦ 1 - q^(n+1)) = fun n ↦ 1 - q*q^n), ←W]
  rw[prod_pow, prod_inv_distrib, ←W]
  rw[pEQ2_4 qN1 h₁]

end EQ2_lemmas


section EQ2
open Finset Filter Topology

theorem eq_2 (a q x : ℂ) (q0 : q ≠ 0) (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1)
    (h₁ : ∀ n : ℕ, 1-a*q^n ≠ 0) (h₂ : ∀ n : ℕ, 1-q^n*x+q^(2*n) ≠ 0) :
    ∃ limitP : ℂ, ∃ limitS : ℂ, Tendsto (fun N ↦ ∏ n ∈ range N, P a q x n) atTop (𝓝 limitP)
    ∧ HasSum (S a q x) limitS ∧ (2-x)⁻¹ * limitP = (2-x)⁻¹ + limitS := by
  suffices H : Tendsto (fun N ↦ (2-x)⁻¹ * ∏ n ∈ range N, P a q x n)
      atTop (𝓝 ((2-x)⁻¹ + ∑' n : ℕ, S a q x n))
  · have x2 : (2 - x) ≠ 0 := by have := h₂ 0; simp at this; ring_nf at this; tauto
    rw[EQ2_1 x2] at H
    use ((2-x) * ((2-x)⁻¹ + ∑' (n : ℕ), S a q x n)), ∑' n : ℕ, S a q x n
    exact ⟨H, Summable.hasSum (S_Summable a0 aN1 qN1 h₁ h₂), (by grind only [h₂ 0])⟩
  rw[pEQ2_5 q0 a0 qN1 h₁ h₂, tendsto_const_add_iff]
  apply tendsto_tsum_of_dominated_convergence (B_Summable a0 aN1 qN1 h₁ h₂) (SS_Tendsto_S aN1 qN1)
      (SS_Bounded_Eventually aN1 qN1)

end EQ2
