import Mathlib

noncomputable section
variable (a q : ℂ)
open BigOperators Polynomial Finset Nat

-- The (a; q)_n notation
def W (n : ℕ) := ∏ i ∈ range n, (1 - a * q^i)

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

-- Lemmas: General
lemma succ_pow {q : ℂ} {x : ℕ} : q * q^x = q^(x+1) := by
  rw[mul_comm, pow_succ]
lemma pow_ne_one {q : ℂ} {x : ℕ} (h : ‖q‖ < 1) (x0 : x ≠ 0) : 1 - q^x ≠ 0 := by
  intro eq
  apply eq_of_sub_eq_zero at eq
  have := pow_lt_pow_left₀ h (norm_nonneg q) x0
  rw[←norm_pow q, ←eq, norm_one, one_pow] at this
  linarith
macro "eval_poly" : tactic => `(tactic| (
  simp only [eval_finset_sum, eval_prod, eval_mul, eval_add, eval_sub, eval_X, eval_C, eval_one]
  ))

-- Lemmas : polyConditionA Unions
macro "pUnion" : tactic => `(tactic| (
  convert (prod_union _)
  · ext n; rw[mem_union]; grind
  · apply disjoint_left.mpr; grind
  ))
lemma pCA1 (w : ℂ) {q : ℂ} {N m : ℕ} : ∏ n ∈ range (N+m), (1 - w*q^n)
      = (∏ n ∈ range m, (1 - w*q^n)) * ∏ n ∈ Ico m (N+m), (1 - w*q^n) := by pUnion
lemma pCA2 {q : ℂ} {N m : ℕ} {h : m < N + 1} : ∏ n ∈ (range (N+1)).erase m, (1 - q ^ ((n:ℤ)-m))
      = (∏ n ∈ range m, (1 - q^((n:ℤ)-m))) * ∏ n ∈ Ioc m N, (1 - q^((n:ℤ)-m)) := by pUnion
lemma pCA3 {a q : ℂ} {N m : ℕ} {h : m < N + 1} : ∏ n ∈ (range (N+1)).erase 0, (1 - a*q^((n:ℤ)-m-1))
      = (∏ n ∈ Icc 1 m, (1 - a*q^((n:ℤ)-m-1))) * ∏ n ∈ Ioc m N, (1 - a*q^((n:ℤ)-m-1)) := by pUnion

-- Lemmas : polyConditionA Bound Changes
macro "pBij" f:term " inv " g:term : tactic => `(tactic|
    apply prod_bij $f (by grind) (by grind) (by intro z _; let := $g z; use this; grind)
    (by intros; simp only[succ_pow]; simp only [←zpow_natCast]; grind))
lemma pCA4 {q : ℂ} {N m : ℕ} : ∏ n ∈ Ioc m N, (1 - q^((n:ℤ)-m))
  = ∏ n ∈ range (N-m), (1 - q*q^n) := by pBij (fun x _ ↦ x - m - 1) inv (fun z ↦ z + m + 1)
lemma pCA5 {a q : ℂ} {N m : ℕ} : ∏ n ∈ Ioc m N, (1 - a*q^((n:ℤ)-m-1))
  = ∏ n ∈ range (N-m), (1 - a*q^n) := by pBij (fun x _ ↦ x - m - 1) inv (fun z ↦ z + m + 1)
lemma pCA6 {q : ℂ} {m : ℕ} : ∏ n ∈ range m, (1 - q^((m:ℤ)-n)) = ∏ n ∈ range m, (1 - q*q^n) := by
  pBij (fun x _ ↦ m - x - 1) inv (fun z ↦ m - z - 1)
lemma pCA7 {a q : ℂ} {N m : ℕ} : ∏ n ∈ (range (N+1)).erase 0, (1 - a*q^((n:ℤ)+m-1))
  = ∏ n ∈ Ico m (N+m), (1 - a*q^n) := by pBij (fun x _ ↦ x + m - 1) inv (fun z ↦ z + 1 - m)
lemma pCA8 {q : ℂ} {m : ℕ} : ∏ n ∈ Icc 1 m, (-q^((n:ℤ)-m-1)) = ∏ n ∈ range m, (-q^((n:ℤ)-m)) := by
  apply prod_bij (fun n _ ↦ n - 1) (by grind) (by grind) (by intro z _; use z + 1; grind)
  grind
lemma pCA9 {a q : ℂ} {m : ℕ} : ∏ n ∈ Icc 1 m, (1 - a⁻¹*q^((m:ℤ)+1-n))
    = ∏ n ∈ range m, (1 - a⁻¹*q*q^n) := by
  apply prod_bij (fun n _ ↦ m - n) (by grind) (by grind) (by intro z _; use m - z; grind)
  intros; rw[mul_assoc, succ_pow, ←zpow_natCast]; grind

-- Lemmas : polyConditionA Other
lemma pCA10 {a q : ℂ} {N m : ℕ} {q0 : q ≠ 0} : ∏ n ∈ range (N + 1), eval (rt q m) (Up a q n)
      = ∏ n ∈ (range (N + 1)).erase 0, ((1 - a*q^((n:ℤ)-m-1)) * (1 - a*q^((n:ℤ)+m-1))) := by
  rw[←prod_erase (range (N+1)) (a := 0)]; swap
  · simp only [Up, if_pos, eval_one]
  · apply prod_congr rfl
    intro n nE; apply mem_erase.mp at nE
    simp only [rt, Up, if_neg nE.1, eval_mul, eval_add, eval_sub, eval_X, eval_C, eval_one]
    field_simp; ring_nf
    rw[mul_comm (q^m) (a^2), mul_assoc (a^2), mul_assoc (a^2)]
    simp only [mul_comm _ a, mul_assoc a, ←zpow_natCast, ←zpow_add₀ q0]
    grind
lemma pCA11 {q : ℂ} {N m : ℕ} {h : m < N + 1} : (∏ n ∈ (range (N+1)).erase m, (1 - q^(n+m)))
    * (if m = 0 then 1 else (1 + q^m)) = ∏ n ∈ Ico m (N+m), (1 - q*q^n) := by
  by_cases m0 : m = 0
  · rw[if_pos m0, mul_one]
    pBij (fun x _ ↦ x - 1) inv (fun z ↦ z + 1)
  · rw[if_neg m0, ←prod_erase_mul _ _ (a := 0) (by grind), mul_assoc, zero_add]
    rw[(by ring : (1 - q^m) * (1 + q^m) = (1 - q^(m + m))), erase_right_comm]
    rw[prod_erase_mul _ _ (by grind)]
    pBij (fun x _ ↦ x + m - 1) inv (fun z ↦ z + 1 - m)

-- The actual ponlymonial condition needed for Equation (1)
lemma polyConditionA (a q : ℂ) (N : ℕ) (q0 : q ≠ 0) (a0 : a ≠ 0)
    (h₁ : ‖q‖ < 1) (h₂ : ∀ n : ℕ, 1 - a*q^n ≠ 0) :
    ∀ m ∈ range (N+1), eval (rt q m) (∑ t ∈ range (N+1), (C (A a q N t)
    * ∏ n ∈ (range (N + 1)).erase t, (Dw q n)) - ∏ n ∈ range (N+1), (Up a q n)) = 0 := by
  -- Remove the summands that equal 0
  intro m mR
  rw[eval_sub, eval_finset_sum, eval_prod]
  have : ∑ t ∈ range (N + 1), eval (rt q m) (C (A a q N t) * ∏ n ∈ (range (N + 1)).erase t, Dw q n)
      = eval (rt q m) (C (A a q N m) * ∏ n ∈ (range (N + 1)).erase m, Dw q n) := by
    apply sum_eq_single
    · intro t tR tm
      rw[eval_mul, eval_prod]
      apply mul_eq_zero_of_right
      apply prod_eq_zero (mem_erase.mpr ⟨tm.symm, mR⟩)
      simp only [Dw, rt, eval_mul, eval_add, eval_sub, eval_one, eval_C, eval_X]
      field
    · exact fun h ↦ (by exfalso; exact h mR)
  rw[this, eval_mul, eval_prod, eval_C]; clear this
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
  rw[pCA1 a, pCA1 q, this, prod_mul_distrib]; clear this -- have := pCA11
  -- Rewriting the left side of the Dw term
  rw[pCA2 (h := mR), pCA4]
  have : (fun (n:ℕ) ↦ 1 - q^((n:ℤ)-m))
      = (fun (n:ℕ) ↦ (-q^((n:ℤ)-m)) * (1 - q^((m:ℤ)-n))) := by
    ext n
    rw[mul_sub, mul_one, neg_mul, sub_neg_eq_add, ←zpow_add' (Or.inl q0)]
    ring_nf; rw[zpow_zero]; ring
  rw[this, prod_mul_distrib]; clear this
  rw[pCA6]
  -- Rewriting the Up term
  rw[pCA10 (q0 := q0), prod_mul_distrib, pCA7, pCA3 (h := mR), pCA5]
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
    exact h₂ _
  have (s : Finset ℕ) : (∏ n ∈ s, (1 - q*q^n)) ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro n _
    rw[mul_comm, ←pow_succ]
    have := succ_ne_zero n
    exact pow_ne_one h₁ this
  field_simp [fun s ↦ this s]
  rw[mul_comm (if m = 0 then 1 else 1 + q ^ m), pCA11 (h := mR)]
  ring

-- Equation 1, with the denominator canceled out
lemma eq_1 (a q : ℂ) (N : ℕ) (q0 : q ≠ 0) (a0 : a ≠ 0)
    (h₁ : ‖q‖ < 1) (h₂ : ∀ n : ℕ, 1-a*q^n ≠ 0) :
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
      simp only [sum_const, nsmul_eq_mul, mul_one, cast_le, ge_iff_le]
      rw[card_erase_of_mem (by simp; omega), card_range]
      norm_num
    apply max_le this
    rw[degree_prod]
    have : ∑ n ∈ range (N + 1), (Up a q n).degree ≤
        ∑ n ∈ range (N + 1), (if n = 0 then 0 else 1) := by
      apply sum_le_sum
      rintro n nN; apply mem_range.mp at nN
      by_cases h : (n = 0)
      · rw[h, Up, if_pos rfl, if_pos rfl]
        compute_degree
      · rw[Up, if_neg h, if_neg h]
        compute_degree!
    apply this.trans
    rw[←sum_erase_add _ _ (by simp : 0 ∈ range (N+1)), if_pos rfl, add_zero]
    have : ∀ x ∈ (range (N + 1)).erase 0, (if x = 0 then 0 else 1) = (1 : WithBot ℕ) := by
      intro x xS; apply ne_of_mem_erase at xS
      rw[if_neg xS]
    rw[sum_congr rfl this]; simp
  apply eq_of_sub_eq_zero
  change f = 0
  by_contra h
  let H := card_roots h
  apply this.trans' at H
  have : ↑((List.range (N+1)).map (fun n ↦ rt q n)) ≤ f.roots := by
    refine (Multiset.le_iff_subset ?_).mpr ?_
    · refine Multiset.coe_nodup.mpr ?_
      refine List.Nodup.map_on ?_ List.nodup_range
      · intro m mR n nR eq
        rw[rt, rt] at eq
        wlog h : m ≤ n generalizing m n
        · exact (this n nR m mR (eq.symm) (Nat.le_of_not_le h)).symm
        · obtain ⟨k, rfl⟩ := (Nat.le.dest h)
          apply_fun (fun T ↦ T * q^(m+k)) at eq
          rw[pow_add] at eq
          field_simp at eq;
          symm at eq
          apply sub_eq_zero_of_eq at eq
          rw[add_mul, sub_add_eq_sub_sub] at eq
          rw[(by ring : 1 + q ^ (2 * (m + k)) - 1 * q ^ k - q ^ (2 * m) * q ^ k
              = (1 - q^(2*m+k)) * (1 - q^k))] at eq
          apply NoZeroDivisors.eq_zero_or_eq_zero_of_mul_eq_zero at eq
          by_cases h : k = 0
          · rw[h, add_zero]
          · rcases eq with T | T
            · have := pow_ne_one h₁ (by omega : 2*m + k ≠ 0)
              contradiction
            · have : k = 0 := by by_contra; exact pow_ne_one h₁ this T
              rw[this, add_zero]
    · intro _ rL
      obtain ⟨m, mR, rfl⟩ := List.mem_map.mp rL
      refine mem_roots'.mpr ⟨h, ?_⟩
      apply IsRoot.def.mpr
      apply polyConditionA <;> assumption
  apply Multiset.card_le_card at this
  simp only [Multiset.coe_card, List.length_map, List.length_range, Order.add_one_le_iff] at this
  have k : (N : WithBot ℕ) < ↑f.roots.card := by exact cast_lt.mpr this
  order

lemma eq_1_eval (a q x : ℂ) (N : ℕ) (q0 : q ≠ 0) (a0 : a ≠ 0)
    (h₁ : ‖q‖ < 1) (h₂ : ∀ n : ℕ, 1-a*q^n ≠ 0) :
    ∑ m ∈ range (N+1), ((A a q N m) * ∏ n ∈ (range (N + 1)).erase m, eval x (Dw q n))
    = ∏ n ∈ range (N+1), eval x (Up a q n) := by
  have eq := eq_1 a q N q0 a0 h₁ h₂
  apply_fun fun X ↦ eval x X at eq
  simp only [eval_finset_sum, eval_prod, eval_mul, eval_C] at eq
  exact eq

end

-- Section for eq_2
noncomputable section
variable (a q x : ℂ) (r : ℝ)
open Finset Filter Topology
-- The factors in the Product of Equation 2
  -- Note it is shifted to be n ≥ 0 instead of n ≥ 1

def P (n : ℕ) := (1 - a*q^n*x + a^2*q^(2*n)) * (1 - q^(n+1)*x + q^(2*n+2))⁻¹
  * ((1 - q^(n+1))^2 * (1 - a*q^n)⁻¹^2)
-- The summands in the Summation of Equation 2
  -- and some summands for a "helper" Summation in the proof
  -- Note it is shifted to be n ≥ 0 instead of n ≥ 1
def S (n : ℕ) := a^(n+1) * (W (a⁻¹*q) q (n+1)) * (1 + q^(n+1))
  * (W a q (n+1))⁻¹ * (1 - q^(n+1)*x + q^(2*n+2))⁻¹

def SS (n N : ℕ) := if N ≤ n then 0 else (S a q x n)
  * ((W a q (N+n+1)) * (W a q (N-n-1)) * ((W q q (N+n+1))⁻¹ * (W q q (N-n-1))⁻¹))
  * ((W q q N)^2 * (W a q N)⁻¹^2)

-- Bounds result
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

lemma Seq0 {a q x : ℂ} {N : ℕ} (h : a = 0 ∨ a = q * q ^ N) : ∀ n ≥ N, S a q x n = 0 := by
  by_cases a0 : a = 0
  · intros; rw[a0, S]; ring
  have := Or.resolve_left h a0
  intro n nN
  have : W (a⁻¹*q) q (n+1) = 0 := by
    rw[W]; apply prod_eq_zero (mem_range.mpr (by omega : N < n+1))
    rw[mul_assoc, ←this]
    field
  rw[S, this]
  ring

lemma S0_eventually {a q x : ℂ} (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1)
    (h' : ∀ N : ℕ, a ≠ q*q^N) (h₃ : ∀ n : ℕ, 1 - q^n*x + q^(2*n) ≠ 0) :
    ∀ᶠ (n : ℕ) in atTop, S a q x n ≠ 0 := by
  have : ‖a‖ > 0 := lt_of_le_of_ne (norm_nonneg a) (norm_ne_zero_iff.mpr a0).symm
  obtain ⟨N, h⟩ : ∃ N : ℕ, ‖q‖^N < ‖a‖ := exists_pow_lt_of_lt_one this qN1
  rw[Filter.eventually_atTop]; use N; intro n nN
  rw[S]; repeat apply mul_ne_zero
  · exact pow_ne_zero n a0
  · exact a0
  · rw[W, prod_ne_zero_iff]
    rintro i - eq
    apply_fun fun X ↦ a * (X + a⁻¹*q*q^i) at eq
    rw[sub_add_cancel, zero_add, mul_one, ←mul_assoc, ←mul_assoc, mul_inv_cancel₀ a0, one_mul] at eq
    exact h' i eq
  · intro eq; apply_fun fun X ↦ ‖X - q^(n+1)‖ at eq
    simp at eq
    have := pow_lt_pow_left₀ qN1 (norm_nonneg q) (by omega : n+1 ≠ 0)
    rw[one_pow] at this
    linarith
  · exact inv_ne_zero (W0 aN1 qN1 (n+1))
  · exact inv_ne_zero (h₃ _)



-- S is summable and bounded
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
    have : 1 = (1:ℝ)⁻¹ := by exact one_eq_inv.mpr rfl
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

macro "mul_rw" a:term "AND" b:term : tactic => `(tactic| (
  repeat rw[mul_right_comm _ $a];
  repeat rw[mul_right_comm _ $b];
  rw[mul_assoc]
))

lemma S_Summable {a q x : ℂ} (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1)
    (h₂ : ∀ n : ℕ, 1-a*q^n ≠ 0) (h₃ : ∀ n : ℕ, 1 - q^n*x + q^(2*n) ≠ 0) : Summable (S a q x) := by
  by_cases h' : ∃ N : ℕ, a = q*q^N
  · obtain ⟨N, h'⟩ := h'
    apply summable_of_hasFiniteSupport
    have : Function.support (S a q x) ⊆ ↑(range N) := by
      intro n (eq : S a q x n ≠ 0)
      apply mem_range.mpr; contrapose! eq
      have : W (a⁻¹ * q) q (n + 1) = 0 := by
        rw[W]; apply prod_eq_zero (mem_range.mpr <| Order.lt_add_one_iff.mpr eq)
        rw[mul_assoc, ←h']
        field
      rw[S, this]
      ring
    apply Set.Finite.subset (finite_toSet (range N)) this
  simp only [not_exists, ←ne_eq] at h'
  apply summable_of_ratio_test_tendsto_lt_one aN1 (S0_eventually a0 aN1 qN1 h' h₃)
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
        rintro i - eq
        apply_fun fun X ↦ a * (X + a⁻¹*q*q^i) at eq
        rw[sub_add_cancel, mul_one, zero_add, ←mul_assoc, ←mul_assoc] at eq
        rw[mul_inv_cancel₀ a0, one_mul] at eq
        exact h' i eq
      rw[mul_right_comm, mul_inv_cancel₀ this, one_mul, mul_assoc, succ_pow]
    mul_rw ‖W (a⁻¹ * q) q (n + 2)‖ AND ‖W (a⁻¹ * q) q (n + 1)‖⁻¹; rw[this]
    have : ‖W a q (n + 2)‖⁻¹ * ‖W a q (n + 1)‖ = ‖1-a*q^(n+1)‖⁻¹ := by
      rw[W, W, ←prod_erase_mul _ _ (by simp : n+1 ∈ range (n+2)), norm_mul, mul_inv]
      rw[(by grind : (range (n+2)).erase (n+1) = range (n+1))]
      have : ‖∏ x ∈ range (n + 1), (1 - a * q ^ x)‖ ≠ 0 := by
        rw[norm_ne_zero_iff, prod_ne_zero_iff]
        rintro i -
        exact h₂ i
      field
    mul_rw ‖W a q (n + 2)‖⁻¹ AND ‖W a q (n + 1)‖; rw[this]
    have aN0 := norm_ne_zero_iff.mpr a0
    field
  rw[this]
  repeat apply Filter.Tendsto.mul
  · exact tendsto_const_nhds_iff.mpr rfl
  · apply h_0; apply h_2 (tendsto_const_nhds_iff.mpr rfl); apply h_3 (h_7 qN1)
  · apply h_0; apply h_1 (tendsto_const_nhds_iff.mpr rfl) (h_7 qN1)
  · apply h_0; apply h_1 _ (h_8 qN1)
    apply h_2 (tendsto_const_nhds_iff.mpr rfl)
    apply h_4; apply h_6 qN1
  · apply h_5; apply h_0; apply h_2 (tendsto_const_nhds_iff.mpr rfl)
    apply h_3 (h_6 qN1)
  · apply h_5; apply h_0; apply h_1 (tendsto_const_nhds_iff.mpr rfl) (h_6 qN1)
  · apply h_5; apply h_0; apply h_1
    · apply h_2 (tendsto_const_nhds_iff.mpr rfl); apply h_4 (h_7 qN1)
    · apply h_9 qN1

lemma S_bounded {a q x : ℂ} (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1)
    (h₂ : ∀ n : ℕ, 1-a*q^n ≠ 0) (h₃ : ∀ n : ℕ, 1 - q^n*x + q^(2*n) ≠ 0) :
    ∃ B : ℝ, ∀ n : ℕ, ‖S a q x n‖ ≤ B := by
  have T := (S_Summable a0 aN1 qN1 h₂ h₃).tendsto_atTop_zero
  obtain ⟨B, T⟩ := Bornology.IsBounded.exists_norm_le (Metric.isBounded_range_of_tendsto _ T)
  use B; intro n
  exact norm_norm (S a q x n) ▸ T (S a q x n) (Set.mem_range.mpr ⟨n, rfl⟩)

-- Bounds result
lemma W_bounded (a : ℂ) {q : ℂ} (qN1 : ‖q‖ < 1) : ∃ B : ℝ, ∀ n : ℕ, ‖W a q n‖ ≤ B := by
  -- #check Multipliable.tendsto_prod_tprod_nat
  suffices W_conv : ∃ l, Tendsto (fun n ↦ ‖W a q n‖) atTop (𝓝 l)
  · rcases W_conv with ⟨l, h⟩
    obtain ⟨B, h⟩ := Bornology.IsBounded.exists_norm_le (Metric.isBounded_range_of_tendsto _ h)
    use B; intro n
    exact norm_norm (W a q n) ▸ h ‖W a q n‖ (Set.mem_range.mpr ⟨n, rfl⟩)
  use ∏' n : ℕ, ‖1 - a*q^n‖
  have : (fun n ↦ ‖W a q n‖) = fun n ↦ ∏ i ∈ range n, ‖1 - a*q^i‖ := by
    ext n
    rw[W, norm_prod]
  rw[this]; apply Multipliable.tendsto_prod_tprod_nat
  rw[(by ext; ring_nf : (fun i ↦ ‖1 - a*q^i‖) = fun i ↦ ‖1 + -a*q^i‖)]
  apply multipliable_norm_one_add_of_summable_norm
  rw[(by ext; simp : (fun n ↦ ‖-a*q^n‖) = fun n ↦ ‖a‖*‖q‖^n)]
  apply Summable.mul_left
  refine summable_geometric_of_lt_one (norm_nonneg q) qN1

lemma Winv_bounded (a q : ℂ) : ∀ᶠ n : ℕ in atTop, ‖W a q n‖⁻¹ < 2 := by
  sorry




-- The bounds used within the proof below
def B (n : ℕ) := ‖S a q x n‖ * 2

-- Lemmas about B
-- lemma EQ2_2 {a : ℂ} (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) : ∃ r : ℝ, (r > 1) ∧ (‖a * r‖ < 1) := by
--   have aN0 := norm_ne_zero_iff.mpr a0
--   have aNpos := norm_pos_iff.mpr a0
--   have : ‖a‖⁻¹ > 1 := (one_lt_inv₀ aNpos).mpr aN1
--   obtain ⟨r, r1, hr⟩ : ∃ r : ℝ, 1 < r ∧ r < ‖a‖⁻¹ := exists_between this
--   have rNormEq : ‖(r:ℂ)‖ = r := by refine Complex.norm_of_nonneg (by linarith)
--   use r, r1
--   rw[norm_mul, ←mul_inv_cancel₀ aN0]
--   apply mul_lt_mul' (le_refl _) (rNormEq ▸ hr : ) (norm_nonneg _) (norm_pos_iff.mpr a0)

-- lemma EQ2_3 {a : ℂ} {r : ℝ} {arN1 : ‖a * r‖ < 1} : Summable (fun n ↦ ‖SS a q x n N‖) := by
--   apply (summable_nat_add_iff 1).mpr
--   apply summable_geometric_of_abs_lt_one
--   rwa[←Real.norm_eq_abs, norm_norm]

-- lemma B_Summable {a q x : ℂ} : Summable (B a q x) := by sorry

-- lemma EQ2_5_1 { a q x : ℂ} : ∀ᶠ (N : ℕ) in atTop, ∀ (n : ℕ), ‖S a q x ‖

-- lemma EQ2_5 {a q x : ℂ} (r : ℝ) {r1 : r > 1} {arN1 : (‖a * r‖ < 1)} :
--     ∀ᶠ (N : ℕ) in atTop, ∀ (n : ℕ), ‖SS a q x n N‖ ≤ B a r x n := by
--   apply Eventually.of_forall
--   intro N n
--   by_cases Nn : N ≤ n
--   · rw[SS, if_pos Nn, norm_zero, B]
--     apply pow_nonneg (norm_nonneg (a*↑r))
--   rw[SS, if_neg Nn, S, B]; repeat rw[norm_mul]
--   rw[norm_pow, norm_pow, norm_inv, norm_inv, norm_inv]


--   sorry





lemma EQ2_1 {x y : ℂ} {f : ℕ → ℂ} (x0 : x ≠ 0) : Tendsto (fun n ↦ x⁻¹ * f n) atTop (𝓝 y) ↔
    Tendsto f atTop (𝓝 (x*y)) := by
  nth_rw 1 [←inv_mul_cancel_left₀ x0 y]
  have : x * y = x • y := by exact Eq.symm (smul_eq_mul x y)
  have : (fun n ↦ x⁻¹ * f n) = (fun n ↦ x⁻¹ • f n) := by ext; rw[smul_eq_mul]
  rw[this, ←smul_eq_mul x⁻¹]
  rw[tendsto_const_smul_iff₀ (inv_ne_zero x0)]
#check tendsto_const_add_iff
#check tendsto_const_smul_iff₀

lemma EQ2_4 {a q x : ℂ} (n : ℕ) : Tendsto (fun N ↦ SS a q x n N) atTop (𝓝 (S a q x n)) := by
  simp only [SS]
  -- have : ∀ᶠ N in atTop, SS a q x n N = S a q x n * (W a q (N + n + 1) * W a q (N - n - 1)
  --   * ((W q q (N + n + 1))⁻¹ * (W q q (N - n - 1))⁻¹)) := by sorry
  suffices h : Tendsto (fun N ↦ S a q x n * (W a q (N + n + 1) * W a q (N - n - 1)
      * ((W q q (N + n + 1))⁻¹ * (W q q (N - n - 1))⁻¹)) * (W q q N ^ 2 * W a q N ^ (-2:ℤ)))
      atTop (𝓝 (S a q x n))
  · sorry
  nth_rw 2 [←mul_one (S a q x n)]; rw[←smul_eq_mul]
  repeat rw[mul_assoc]
  simp only [mul_assoc]
  simp only [←smul_eq_mul (S a q x n)]
  -- apply tendsto_const_smul_iff₀ (c := S a q x n) _
  sorry

lemma EQ2_6 {a q x : ℂ} : Multipliable fun n ↦ P a q x n := by
  -- Real.multipliable_of_summable_log
  -- Real.log_le_sub_one_of_pos
  sorry

lemma EQ2_8 {a q x : ℂ} : (fun n ↦ P a q x n) = (fun n ↦ Polynomial.eval x (Up a q (n+1))
    * (Polynomial.eval x (Dw q (n+1)))⁻¹ * ((1 - q^(n+1))^2 * (1 - a*q^n)^(-2:ℤ))) := by
  ext n
  rw[P, Up, Dw, if_neg (Nat.succ_ne_zero n)]
  eval_poly
  rw[Nat.add_sub_self_right, (by omega : (2*(n+1) - 2) = 2*n), mul_add, mul_one]
  sorry

lemma EQ2_9 {a q x : ℂ} {N : ℕ} (h₃ : ∀ n : ℕ, 1 - q^n*x + q^(2*n) ≠ 0) :
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
    exact h₃ n
  field

lemma EQ2_11 (a q x : ℂ) (N : ℕ) (qN1 : ‖q‖ < 1) (h₂ : ∀ n : ℕ, 1-a*q^n ≠ 0) :
    (2-x)⁻¹ = A a q N 0 * (Polynomial.eval x (Dw q 0))⁻¹ * (W q q N ^ 2 * (W a q N ^ 2)⁻¹) := by
  rw[A, Dw]; eval_poly; rw[if_true]
  simp only [W, range_zero, prod_empty]
  have : (∏ i ∈ range N, (1 - q * q ^ i)) ≠ 0 := by
    rw[prod_ne_zero_iff]
    intro n _
    rw[succ_pow]
    apply pow_ne_one qN1 (Nat.succ_ne_zero n)
  have : (∏ i ∈ range N, (1 - a * q ^ i)) ≠ 0 := by
    rw[prod_ne_zero_iff]
    intro n _
    exact h₂ n
  grind

lemma EQ2_12 (x y z : ℂ) : x = y → x + z = y + z := by
  intro rfl; rfl

lemma EQ2_14 (x y z : ℂ) : x = y → z * x = z * y := by
  intro rfl; rfl

lemma EQ2_10 {a q x : ℂ} {N : ℕ} (qN1 : ‖q‖ < 1)
    (h₂ : ∀ n : ℕ, 1-a*q^n ≠ 0) : (2 - x)⁻¹ + ∑ n ∈ range N, SS a q x n N
    = (∑ n ∈ range (N + 1), A a q N n * (Polynomial.eval x (Dw q n))⁻¹)
    * (W q q N ^ 2 * (W a q N ^ 2)⁻¹) := by
  have : ∑ n ∈ range N, SS a q x n N = ∑ n ∈ (range (N+1)).erase 0, SS a q x (n-1) N := by
    apply sum_bij (fun n _ ↦ n + 1) (by grind) (by grind)
      (by intro z _; use z - 1; grind) (by grind)
  rw[this]; clear this
  rw[←sum_erase_add _ _ (by simp : 0 ∈ range (N+1)), add_mul]
  rw[EQ2_11 a q x N qN1 h₂, add_comm]
  apply EQ2_12
  rw[sum_mul]
  apply sum_congr rfl
  intro n nE
  rw[SS, S, A, Dw]; eval_poly
  rw[mem_erase, mem_range] at nE
  rw[if_neg nE.1, if_neg (by omega)]
  have J1 : n - 1 + 1 = n := by omega
  have J2 : (2 * (n - 1) + 2) = 2*n := by omega
  have J3 : (N + (n - 1) + 1) = N + n := by omega
  have J4 : (N - (n - 1) - 1) = N - n := by omega
  rw[J1, J2, J3, J4]
  repeat rw[mul_right_comm _ (1 + q^n)]
  repeat rw[mul_right_comm _ (1 - q^n*x + q^(2*n))⁻¹]
  rw[inv_pow _ 2]

lemma EQ2_7 {a q x : ℂ} (q0 : q ≠ 0) (a0 : a ≠ 0) (qN1 : ‖q‖ < 1)
    (h₂ : ∀ n : ℕ, 1-a*q^n ≠ 0) (h₃ : ∀ n : ℕ, 1 - q^n*x + q^(2*n) ≠ 0) :
    (fun N ↦ (2-x)⁻¹ * ∏ n ∈ range N, P a q x n) = (fun N ↦ (2-x)⁻¹ + ∑' n : ℕ, SS a q x n N) := by
  ext N
  rw[tsum_eq_sum (s := range N)]; swap
  · intro n nR
    by_cases! h : N ≤ n
    · rw[SS, if_pos h]
    · rw[mem_range] at nR
      linarith
  rw[EQ2_8, prod_mul_distrib, prod_mul_distrib]
  have : (∏ n ∈ range N, Polynomial.eval x (Up a q (n+1)))
      = ∏ n ∈ range (N+1), Polynomial.eval x (Up a q n) := by
    have : Polynomial.eval x (Up a q 0) = 1 := by rw[Up, if_pos, Polynomial.eval_one]; rfl
    have : ∏ n ∈ range (N+1), Polynomial.eval x (Up a q n)
        = ∏ n ∈ (range (N+1)).erase 0, Polynomial.eval x (Up a q n) := by
      rw[prod_erase _ (f := fun n ↦ Polynomial.eval x (Up a q n)) this]
    rw[this]
    apply prod_bij (fun n _ ↦ n + 1) (by grind) (by grind) (by intro z _; use z - 1; grind)
      (by grind)
  rw[this, prod_inv_distrib]; clear this
  nth_rw 3 [mul_comm]; repeat rw[←mul_assoc]
  have : (∏ n ∈ range N, Polynomial.eval x (Dw q (n+1)))
      = ∏ n ∈ (range (N+1)).erase 0, Polynomial.eval x (Dw q n) := by
    apply prod_bij (fun n _ ↦ n + 1) (by grind) (by grind) (by intro z _; use z - 1; grind)
      (by grind)
  rw[this]; clear this
  rw[←eq_1_eval a q x N q0 a0 qN1 h₂]
  have : (2 - x)⁻¹ = (Polynomial.eval x (Dw q 0))⁻¹ := by rw[Dw, inv_inj]; eval_poly; ring
  nth_rw 1 [mul_comm (2-x)⁻¹, this, ←mul_inv,
    prod_erase_mul _ (by simp : 0 ∈ range (N+1)) (f := fun n ↦ Polynomial.eval x (Dw q n))]
  rw[mul_sum, EQ2_9 h₃]
  rw[prod_mul_distrib, prod_pow, (by ext; ring : (fun n ↦ 1 - q^(n+1)) = fun n ↦ 1 - q*q^n), ←W]
  rw[prod_zpow, ←W, zpow_neg]
  rw[EQ2_10 qN1 h₂]
  rfl




-- -- theorem eq_2
-- theorem eq_2 (a q x : ℂ) (q0 : q ≠ 0) (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1)
--     (h₂ : ∀ n : ℕ, 1-a*q^n ≠ 0) (h₃ : ∀ n : ℕ, 1 - q^n*x + q^(2*n) ≠ 0) :
--     (2-x)⁻¹ * ∏' n : ℕ, P a q x n = (2-x)⁻¹ + ∑' n : ℕ, S a q x n := by
--   suffices h : Tendsto (fun N ↦ (2-x)⁻¹ * ∏ n ∈ range N, P a q x n)
--       atTop (𝓝 ((2-x)⁻¹ + ∑' n : ℕ, S a q x n))
--   · have x2 : (2 - x) ≠ 0 := by have := h₃ 0; simp at this; ring_nf at this; tauto
--     rw[EQ2_1 x2] at h
--     have : a⁻¹ * q = x ↔ q = a * x := by exact inv_mul_eq_iff_eq_mul₀ a0
--     rw[inv_mul_eq_iff_eq_mul₀ x2]
--     apply HasProd.tprod_eq
--     exact (Multipliable.hasProd_iff_tendsto_nat EQ2_6).mpr h
--   rw[EQ2_7 q0 a0 qN1 h₂ h₃, tendsto_const_add_iff]
--   obtain ⟨r, r1, arN1⟩ := EQ2_2 a0 aN1
--   apply tendsto_tsum_of_dominated_convergence (EQ2_3) EQ2_4 (EQ2_5 r)
--     <;> assumption


theorem eq_2' (a q x : ℂ) (q0 : q ≠ 0) (a0 : a ≠ 0) (aN1 : ‖a‖ < 1) (qN1 : ‖q‖ < 1)
    (h₂ : ∀ n : ℕ, 1-a*q^n ≠ 0) (h₃ : ∀ n : ℕ, 1 - q^n*x + q^(2*n) ≠ 0) :
    ∃ limitP : ℂ, ∃ limitS : ℂ, HasProd (P a q x) limitP ∧ HasSum (S a q x) limitS
    ∧ (2-x)⁻¹ * limitP = (2-x)⁻¹ + limitS := by
  suffices h : Tendsto (fun N ↦ (2-x)⁻¹ * ∏ n ∈ range N, P a q x n)
      atTop (𝓝 ((2-x)⁻¹ + ∑' n : ℕ, S a q x n))
  · have x2 : (2 - x) ≠ 0 := by have := h₃ 0; simp at this; ring_nf at this; tauto
    rw[EQ2_1 x2] at h
    apply (Multipliable.hasProd_iff_tendsto_nat EQ2_6).mpr at h
    apply HasProd.tprod_eq at h
    use ∏' n : ℕ, P a q x n, ∑' n : ℕ, S a q x n
    refine ⟨Multipliable.hasProd EQ2_6, Summable.hasSum sorry, ?_⟩
    rw[h]; field
  rw[EQ2_7 q0 a0 qN1 h₂ h₃, tendsto_const_add_iff]
  -- obtain ⟨r, r1, arN1⟩ := EQ2_2 a0 aN1
  apply tendsto_tsum_of_dominated_convergence (EQ2_3 r) EQ2_4 (EQ2_5 r)
    <;> assumption

end
