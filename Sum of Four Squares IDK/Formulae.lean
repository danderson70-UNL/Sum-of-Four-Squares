import Mathlib
import «Sum of Four Squares IDK».«Various Sums & Prods v3»
import «Sum of Four Squares IDK».«Power & Multilinear Series»
set_option linter.style.whitespace false

section prod_props
open Finset

-- Some general theorems
theorem HasProd.in_pairs {f : ℕ → ℂ} {a : ℂ} (h : HasProd f a) :
    HasProd (fun n ↦ f (2*n) * f (2*n+1)) a := by
  apply HasProd.hasProd_of_prod_eq _ h
  intro u
  let v := u.biUnion (fun n ↦ {n/2})
  use v; intro v' vv'
  use v'.biUnion (fun n ↦ {2*n, 2*n+1})
  constructor
  · intro n nu
    have : n = 2*(n/2) ∨ n = 2*(n/2)+1 := by omega
    rw[Finset.mem_biUnion]; use n/2
    refine ⟨vv' (mem_biUnion.mpr ⟨n, nu, by simp⟩), by simpa⟩
  · rw[prod_biUnion]
    · simp
    intro m mv n nv mn
    simp; omega

example (f g : ℂ → ℂ) (a b : ℂ) (hf : HasProd f a) (hg : HasProd g b) :
  HasProd (fun n ↦ f n * g n) (a*b) := HasProd.mul hf hg

theorem HasProd.inv₀ {α β : Type*} {L : SummationFilter β} [CommGroupWithZero α]
    [TopologicalSpace α] [ContinuousInv₀ α] [IsTopologicalGroup αˣ]
    {f : β → α} {a : α} (h : HasProd f a L) (a0 : a ≠ 0) :
    HasProd (fun n ↦ (f n)⁻¹) a⁻¹ L := by
  have : (fun (s : Finset β) ↦ ∏ n ∈ s, (f n)⁻¹)
      = (fun (s : Finset β) ↦ (∏ n ∈ s, f n)⁻¹) :=
    by ext s; apply prod_inv_distrib
  rw[HasProd, this]
  apply Filter.Tendsto.inv₀ h a0

example {f : ℕ → ℂ} {a : ℂ} (h : HasProd f a) (a0 : a ≠ 0) :
    HasProd (fun n ↦ (f n)⁻¹) a⁻¹ := by
  apply HasProd.inv₀ h a0

-- Some theorems that are more specific
lemma L_1 {q : ℂ} (qN1 : ‖q‖ < 1) : ∃ b : ℂ, b ≠ 0 ∧ HasProd (fun n ↦ 1 - q^(n+1)) b := by
  obtain ⟨b, hb⟩ := ModularForm.multipliable_one_sub_pow qN1
  use b; refine ⟨?_, hb⟩
  intro rfl
  simp only [sub_eq_add_neg] at hb
  apply (tprod_one_add_ne_zero_of_summable _ _) (HasProd.tprod_eq hb)
  · exact fun n ↦ W0_terms' qN1 (Nat.succ_ne_zero n)
  · simp only [norm_neg, norm_pow]; simp only [pow_succ]
    apply Summable.mul_right
    exact summable_geometric_of_lt_one (norm_nonneg q) qN1

lemma L_3 {q l : ℂ} (qN1 : ‖q‖ < 1) (h : HasProd (fun n ↦ (1-q^(2*n+1))^2 * (1-q^(2*n+2))) l) :
    HasProd (fun n ↦ (1-q^(n+1)) * (1+q^(n+1))⁻¹) l := by
  have : (fun n ↦ (1-q^(n+1)) * (1+q^(n+1))⁻¹)
      = (fun n ↦ (1-q^(n+1))^2 * (1-q^(2*(n+1)))⁻¹) := by
    ext n
    rw[(by ring : 1-q^(2*(n+1)) = (1-q^(n+1))*(1+q^(n+1))), mul_inv]
    have : 1-q^(n+1) ≠ 0 := by apply W0_terms' qN1 (Nat.succ_ne_zero _)
    grobner
  rw[this]; clear this
  have : (fun n ↦ (1-q^(2*n+1))^2 * (1-q^(2*n+2)))
      = (fun n ↦ (1-q^(2*n+1))^2 * (1-q^(2*n+2))^2 * (1-q^(2*(n+1)))⁻¹) := by
    ext n
    have : 1-q^(2*n+2) ≠ 0 := by apply W0_terms' qN1 (Nat.succ_ne_zero _)
    grobner
  rw[this] at h; clear this
  obtain ⟨b, b0, hb⟩ := L_1 qN1
  have ha_split := HasProd.in_pairs hb
  have h := HasProd.mul ((ha_split.inv₀ b0).pow 2) h
  rw[(by field : l = b^2 * (b⁻¹^2 * l))]
  apply HasProd.mul (hb.pow 2)
  have : (fun n ↦ ((1-q^(2*n+1)) * (1-q^(2*n+1+1)))⁻¹^2 * ((1-q^(2*n+1))^2 * (1-q^(2*n+2))^2
      * (1-q^(2*(n+1)))⁻¹)) = (fun n ↦ (1-q^(2*(n+1)))⁻¹) := by
    ext n
    field [W0_terms' qN1]
  rwa[this] at h

end prod_props


section JacobiTripleProduct_lemmas
open Topology

lemma L_2 [Field α] (z : ℤ) {n : ℕ} (n0 : n ≠ 0) : (-1:α)^(z^n) = (-1:α)^z := by
  by_cases h : Even z
  · rw[Even.neg_one_zpow h, Even.neg_one_zpow (h.pow_of_ne_zero n0)]
  · have h := by exact Int.not_even_iff_odd.mp h
    rw[Odd.neg_one_zpow h, Odd.neg_one_zpow h.pow]


-- Results about the Jacobi Triple Product
theorem jacobiTripleProduct {a q : ℂ} (a0 : a ≠ 0) (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasProd (fun n ↦ (1+a*q^(2*n+1)) * (1+a⁻¹*q^(2*n+1)) * (1-q^(2*n+2))) limit
    ∧ HasSum (fun z : ℤ ↦ a^z * q^(z^2)) limit := by sorry

-- def statementOf_jacobiTripleProduct {a q : ℂ} (a0 : a ≠ 0) (qN1 : ‖q‖ < 1) : Prop :=
--     ∃ limit : ℂ, HasProd (fun n ↦ (1+a*q^(2*n+1)) * (1+a⁻¹*q^(2*n+1)) * (1-q^(2*n+2))) limit
--     ∧ HasSum (fun z : ℤ ↦ a^z * q^(z^2)) limit
-- variable (jtp : Π {a q : ℂ} (a0 : a ≠ 0) (qN1 : ‖q‖ < 1), statementOf_jacobiTripleProduct a0 qN1)
-- include jtp

lemma JTP_1 {q : ℂ} (qB : q ∈ Metric.ball 0 1) :
    ∃ limit : ℂ, HasSum (fun z : ℤ ↦ (-1)^z * q^(z^2)) limit
    ∧ HasProd (fun n ↦ (1 - q^(n+1)) * (1 + q^(n+1))⁻¹) limit := by
  -- obtain ⟨l, prod, sum⟩ := jtp (by grobner : (-1:ℂ) ≠ 0) qN1
  have qN1 := mem_ball_zero_iff.mp qB
  obtain ⟨l, prod, sum⟩ := jacobiTripleProduct (by grobner : (-1:ℂ) ≠ 0) qN1
  use l; refine ⟨sum, ?_⟩; clear sum
  simp only [neg_one_mul, (by ring : (-1:ℂ)⁻¹ = -1), ←sub_eq_add_neg, ←pow_two] at prod
  apply L_3 qN1 prod

lemma JTP_2 {q : ℂ} (qB : q ∈ Metric.ball 0 1) :
    ∃ limit : ℂ, HasSum (fun z : ℤ ↦ (-1)^z * q^(z^2)) limit
    ∧ HasProd (fun n ↦ ((1-q^(2*n+1)) * (1-q^(2*n+2)))
      * ((1+q^(2*n+2))⁻¹ * (1+q^(2*n+1))⁻¹)) limit := by
  -- obtain ⟨l, sum, prod⟩ := JTP_1 jtp qN1
  obtain ⟨l, sum, prod⟩ := JTP_1 qB
  use l; refine ⟨sum, ?_⟩
  have : (fun n ↦ (1-q^(2*n+1)) * (1-q^(2*n+2)) * ((1+q^(2*n+2))⁻¹ * (1+q^(2*n+1))⁻¹))
      = (fun n ↦ (1-q^(2*n+1)) * (1+q^(2*n+1))⁻¹ * ((1-q^(2*n+2)) * (1+q^(2*n+2))⁻¹)) := by
    ext n; ring
  rw[this]
  apply HasProd.in_pairs prod

lemma JTP_3 {q : ℂ} (qB : q ∈ Metric.ball 0 1) :
    ∃ limit : ℂ, HasProd (fun n ↦
      ((1+q^(4*n+2)) * (1-q^(2*n+2))) * ((1+q^(4*n+4))⁻¹ * (1+q^(2*n+1))⁻¹)
      * ((1+q^(2*n+2)) * (1-q^(2*n+1))⁻¹)) limit
    ∧ HasSum (fun z : ℤ ↦ q^(2*z^2)) limit := by
  have qN1 := mem_ball_zero_iff.mp qB
  have : -q^2 ∈ Metric.ball 0 1 := by
    rw[mem_ball_zero_iff]
    rw[Complex.norm_neg', norm_pow, ←one_pow 2]
    exact zpow_lt_zpow_left₀ two_pos (norm_nonneg q) qN1
  -- obtain ⟨l, sum, prod⟩ := JTP_2 jtp this
  obtain ⟨l, sum, prod⟩ := JTP_2 this
  use l; constructor
  · have : (fun n ↦
          (1-(-q^2)^(2*n+1)) * (1-(-q^2)^(2*n+2)) * ((1+(-q^2)^(2*n+2))⁻¹ * (1+(-q^2)^(2*n+1))⁻¹))
        = (fun n ↦ (1+q^(4*n+2)) * (1-q^(2*n+2)) * ((1+q^(4*n+4))⁻¹ * (1+q^(2*n+1))⁻¹)
          * ((1+q^(2*n+2)) * (1-q^(2*n+1))⁻¹)) := by
      ext n
      repeat rw[neg_eq_neg_one_mul (q^2), mul_pow, mul_pow, ←pow_mul, ←pow_mul]
      have : q - -l = q + l := by exact sub_neg_eq_add q l
      rw[Odd.neg_one_pow (odd_two_mul_add_one n), neg_one_mul, sub_neg_eq_add, ←sub_eq_add_neg]
      rw[(by omega : 2*n+2 = 2*(n+1)), Even.neg_one_pow (even_two_mul (n+1)), one_mul]
      rw[(by omega : 2*(2*(n+1)) = 4*n+4), (by omega : 2*(2*n+1) = 4*n+2)]
      rw[(by field : (1 - q ^ (4 * n + 2))⁻¹ = (1 + q ^ (2 * n + 1))⁻¹ * (1 - q ^ (2 * n + 1))⁻¹)]
      ring
    simpa [this] using prod
  · have : (fun z:ℤ ↦ (-1)^z * (-q^2)^(z^2)) = (fun z ↦ q^(2*z^2)) := by
      ext z
      rw[neg_eq_neg_one_mul (q^2), mul_zpow, L_2 z two_ne_zero, ←mul_assoc]
      rw[←zpow_two, ←zpow_mul, mul_comm z, Even.neg_one_zpow (even_two_mul z), one_mul, zpow_mul]
      rfl
    simpa [this] using sum

end JacobiTripleProduct_lemmas


section d_lemmas
open Finset

def nrange (n : ℕ) := Finset.range (n+1)
#eval nrange 4

variable (r m n : ℕ)
def d := #{x ∈ nrange n | (x ∣ n) ∧ (x % m = r)}
#eval {x ∈ nrange 15 | (x ∣ 15) ∧ (x % 4 = 1)}
#eval {p ∈ (nrange 5).product (nrange 5) | p.1 + p.2 = 6}
#eval d 1 4 15

--Nat.lt_add_of_pos_right
theorem Nat.lt_add_of_nonzero_right (a : ℕ) {b : ℕ} (b0 : b ≠ 0) : a < a + b := by
  apply Nat.lt_add_of_pos_right (zero_lt_of_ne_zero b0)
theorem Nat.le_mul_of_nonzero_left (b : ℕ) {a : ℕ} (a0 : a ≠ 0)  : b ≤ a * b := by
  apply Nat.le_mul_of_pos_left _ (zero_lt_of_ne_zero a0)
theorem Nat.le_mul_of_nonzero_right (a : ℕ) {b : ℕ} (b0 : b ≠ 0) : a ≤ a * b := by
  apply Nat.le_mul_of_pos_right _ (zero_lt_of_ne_zero b0)

lemma d_geom_sum {q : ℂ} (qB : q ∈ Metric.ball 0 1) {r m : ℕ} (r0 : r ≠ 0) (m0 : m ≠ 0) :
    ∃ limit : ℂ, HasSum (fun n ↦ q^(r*n) / (1 - q^(m*n))) limit
    ∧ HasSum (fun n ↦ d r m (n+1) * q^(n+1)) limit := by
  obtain ⟨l, h⟩ : Summable (fun n ↦ q^(r*n) / (1 - q^(m*n))) := by sorry
  refine ⟨l, h, ?_⟩
  suffices : HasSum (fun p : ℕ × ℕ ↦ q^((p.1+1)*(m*p.2+r))) l
  · apply HasSum.hasSum_of_sum_eq _ this
    intro u; use u.image (fun p ↦ (p.1+1)*(m*p.2+r))
    intro v' vv'
    let u' := v'.biUnion (fun n ↦ {p ∈ (nrange n).product (nrange n) | (p.1+1)*(m*p.2+r) = n})
    use u'
    constructor
    · intro p pu
      rw[mem_biUnion]; use (p.1+1)*(m*p.2+r)
      constructor
      · exact vv' (Finset.mem_image.mpr ⟨p, pu, rfl⟩)
      · simp only [product_eq_sprod, mem_filter, mem_product, and_true]
        rw[nrange, mem_range, mem_range]
        have : (m * p.2 + r) ≠ 0 := by omega
        constructor
        · calc
          _ < p.1 + 1 := lt_add_one p.1
          _ ≤ (p.1 + 1) * (m*p.2 + r) := Nat.le_mul_of_nonzero_right (p.1 + 1) this
          _ < _ := lt_add_one _
        · calc
          _ ≤ m*p.2 := Nat.le_mul_of_nonzero_left _ m0
          _ < m*p.2 + r := by refine Nat.lt_add_of_nonzero_right _ r0
          _ ≤ _ := by lia
    · rw[Finset.sum_biUnion]
      · apply Finset.sum_congr rfl
        intro n nv'
        calc
          _ = ∑ p ∈ (nrange n).product (nrange n) with (p.1+1)*(m*p.2+r) = n, q^(n+1) := by
            sorry
          _ = #{p ∈ (nrange n).product (nrange n) | (p.1+1)*(m*p.2+r) = n} * q^(n+1) := by
            sorry
          _ = _ := by
            apply congr_arg (fun (X:ℕ) ↦ X * q^(n+1))
            sorry
      · sorry
  simp [mul_add, pow_add]
  -- #check HasSum.prod_mk
  sorry

example (a b : ℕ) (h : a ≠ 0) : b ≤ a*b := by apply?

end d_lemmas

section sum_of_squares_formulae
open Finset

def zrange (n : ℕ) := (range (2*n+1)).image (fun (x:ℕ) ↦ (x:ℤ) - n)
#eval zrange 4

def sum_sq_sq (n : ℕ) := #{(⟨x,_⟩, ⟨y,_⟩) : (zrange n) × (zrange n) | x^2 + y^2 = n}
def sum_sq_2sq (n : ℕ) := #{(⟨x,_⟩, ⟨y,_⟩) : (zrange n) × (zrange n) | x^2 + 2 * y^2 = n}
def sum_sq_3sq (n : ℕ) := #{(⟨x,_⟩, ⟨y,_⟩) : (zrange n) × (zrange n) | x^2 + 3 * y^2 = n}
def sum_sq_sq_sq_sq (n : ℕ) := #{(⟨w,_⟩, ⟨x,_⟩, ⟨y,_⟩, ⟨z,_⟩) : (zrange n) × (zrange n)
    × (zrange n) × (zrange n) | w^2 + x^2 + y^2 + z^2 = n}
#eval sum_sq_sq_sq_sq 5

lemma L_4 (q : ℂ) : ∀ limit : ℂ, HasSum (fun z : ℤ ↦ q^(z^2)) limit
    → HasSum (term sum_sq_sq q) (limit^2) := by sorry

end sum_of_squares_formulae

section
open Filter Finset Topology

lemma h₁_qB {q : ℂ} (qB : q ∈ Metric.ball 0 1) : ∀ n : ℕ, 1 + q^n ≠ 0 := by
  apply mem_ball_zero_iff.mp at qB
  intro n eq
  apply eq_neg_of_add_eq_zero_left at eq
  by_cases n0 : n = 0
  · rw[n0] at eq
    grobner
  have := pow_lt_pow_left₀ qB (norm_nonneg q) n0
  rw[←norm_pow q, ←norm_neg, ←eq, norm_one, one_pow] at this
  linarith

theorem eq_2aq {q x : ℂ} (qB : q ∈ Metric.ball 0 1) (h₂ : ∀ n : ℕ, 1-q^n*x+q^(2*n) ≠ 0) :
    ∃ limitP : ℂ, ∃ limitS : ℂ,
    Tendsto (fun N ↦ ∏ n ∈ range N,
      ((1+q^(n+1)*x+q^(2*n+2)) / (1-q^(n+1)*x+q^(2*n+2))) * (((1-q^(n+1))^2) / (1+q^(n+1))^2))
      atTop (𝓝 limitP)
    ∧ HasSum (fun n ↦ (-q)^(n+1) / (1-q^(n+1)*x+q^(2*n+2))) limitS
    ∧ (2-x)⁻¹ * limitP = (2-x)⁻¹ + 2 * limitS := by
  have qN1 := mem_ball_zero_iff.mp qB
  by_cases q0 : q = 0
  · use 1, 0
    simp [q0]
  have h₁ : ∀ n : ℕ, 1 - (-q)*q^n ≠ 0 := by
    simp only[neg_mul, sub_neg_eq_add, ←pow_succ']
    exact fun n ↦ h₁_qB qB n.succ
  obtain ⟨lP, lS, prod, sum, eq⟩ :=
    eq_2 (by grobner : -q ≠ 0) q0 (by rwa[←norm_neg] at qN1) qN1 h₁ h₂
  use lP, lS/2
  refine ⟨?_, ?_, ?_⟩
  · convert prod
    rw[P]
    field
  · suffices : HasSum (fun n ↦ (-q)^(n+1) / (1-q^(n+1)*x+q^(2*n+2))*2) (lS)
    · have := (HasSum.div_const this 2)
      simpa [mul_div_cancel₀]
    convert sum with n
    have : W ((-q)⁻¹*q) q (n+1) * (1+q^(n+1)) * (W (-q) q (n+1))⁻¹ = 2 := by
      simp only [W, inv_neg, neg_mul, inv_mul_cancel₀ q0, sub_neg_eq_add, ←pow_succ', one_mul]
      rw[←prod_erase_mul _ _ (by simp : 0 ∈ range (n+1))]
      rw[←prod_erase_mul _ _ (by simp : n ∈ range (n+1))]
      have : (∏ x ∈ (range (n + 1)).erase 0, (1 + q ^ x))
          = (∏ x ∈ (range (n + 1)).erase n, (1 + q ^ (x + 1))) := by
        pBij (fun n _ ↦ n - 1) inv (fun m ↦ m + 1)
      rw[this]
      simp only [neg_mul, sub_neg_eq_add, ←pow_succ'] at h₁
      have : (∏ x ∈ (range (n + 1)).erase n, (1 + q ^ (x + 1))) ≠ 0 := by
        rw[prod_ne_zero_iff]; rintro m -; exact h₁ m
      have := h₁ n
      field
    rw[S, mul_assoc ((-q)^(n+1)), mul_assoc ((-q)^(n+1)), this]
    ring
  · rw[eq]; field

lemma eq_C' {q : ℂ} (qB : q ∈ Metric.ball 0 1) : ∃ limitL : ℂ, ∃ limitR,
    HasSum (fun z : ℤ ↦ (-1)^z * q^(z^2)) limitL
    ∧ HasSum (fun n ↦ (-q)^(n+1) / (1+(-q)^(2*n+2))) limitR
    ∧ limitL^2 = 1 + 4 * limitR := by
  have qN1 := mem_ball_zero_iff.mp qB
  have h₂ : ∀ n : ℕ, 1 - q^n*0 + q^(2*n) ≠ 0 := by
    intro n; rw[mul_zero, sub_zero]
    exact h₁_qB qB _
  obtain ⟨lP, lS, prod, sum, eq⟩ := eq_2aq qB h₂
  obtain ⟨lJ, Jsum, Jprod⟩ := JTP_1 qB
  simp only [mul_zero, add_zero, sub_zero, fun n ↦ div_self (h₁_qB qB (2*n+2)),
    one_mul, div_eq_mul_inv, ←inv_pow, ←mul_pow] at prod
  simp only [mul_zero, sub_zero] at sum
  use lJ, lS
  refine ⟨Jsum, ?_, ?_⟩
  · simp only [fun n ↦ (by omega : 2*n+2 = 2*(n+1)), fun n ↦ Even.neg_pow (even_two_mul (n+1)) q]
    simp only [fun n ↦ (by omega : 2*(n+1) = 2*n+2)]
    exact sum
  · have : lJ^2 = lP := by
      have := HasProd.tendsto_prod_nat (HasProd.pow Jprod 2)
      apply tendsto_nhds_unique this prod
    rw[this]
    grobner

example : sum_sq_sq = fun n ↦ if n = 0 then 1 else 4*(d 1 4 n - d 3 4 n) := by
  apply eq_PS_on_disk
  intro q qB
  have : -q ∈ Metric.ball 0 1 := by sorry
  obtain ⟨lL, lR, sumL, sumR, eq⟩ := eq_C' this
  use lL^2
  constructor
  · have : (fun (z:ℤ) ↦ (-1) ^ z * (-q) ^ z ^ 2) = (fun z ↦ q^(z^2)) := by
      ext z
      have : (-1:ℂ)^z * (-1)^(z^2) = 1 := by
        simp[L_2 z two_ne_zero, ←zpow_add₀, ←two_mul, Even.neg_one_zpow]
      rw[neg_eq_neg_one_mul q, mul_zpow, ←mul_assoc, this, one_mul]
    rw[this] at sumL
    exact L_4 q lL sumL
  · have : (fun n ↦ (- -q)^(n+1) / (1 + (- -q)^(2*n+2)))
        = (fun n ↦ q^(n+1) / (1-q^(4*n+4)) - q^)





end
