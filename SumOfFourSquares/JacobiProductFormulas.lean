import Mathlib
import RogersRamanujan
import SumOfFourSquares.VariousSumsAndProducts
-- import SumOfFourSquares.VariousSumsAndProducts
set_option linter.style.whitespace false

section prod_props
open Finset

-- Some general theorems
lemma HasProd.in_pairs {f : ℕ → ℂ} {a : ℂ} (h : HasProd f a) :
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

lemma HasProd.inv₀ {α β : Type*} {L : SummationFilter β} [CommGroupWithZero α]
    [TopologicalSpace α] [ContinuousInv₀ α] [IsTopologicalGroup αˣ]
    {f : β → α} {a : α} (h : HasProd f a L) (a0 : a ≠ 0) :
    HasProd (fun n ↦ (f n)⁻¹) a⁻¹ L := by
  have : (fun (s : Finset β) ↦ ∏ n ∈ s, (f n)⁻¹)
      = (fun (s : Finset β) ↦ (∏ n ∈ s, f n)⁻¹) :=
    by ext s; apply prod_inv_distrib
  rw[HasProd, this]
  apply Filter.Tendsto.inv₀ h a0

-- Some lemmas that are more specific to certain situations
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

variable {a q : ℂ} (a0 : a ≠ 0) (qN1 : ‖q‖ < 1)

lemma L_2 {α : Type*} [Field α] (z : ℤ) {n : ℕ} (n0 : n ≠ 0) : (-1:α)^(z^n) = (-1:α)^z := by
  by_cases h : Even z
  · rw[Even.neg_one_zpow h, Even.neg_one_zpow (h.pow_of_ne_zero n0)]
  · have h := by exact Int.not_even_iff_odd.mp h
    rw[Odd.neg_one_zpow h, Odd.neg_one_zpow h.pow]

lemma multipliable_b (b : ℂ) (qN1 : ‖q‖ < 1): Multipliable (fun n ↦ (1+b*q^(2*n+1))) := by
  apply Complex.multipliable_one_add_of_summable
  apply Summable.mul_left
  apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg q) qN1)
  intro n
  rw[norm_pow]; apply pow_le_pow_of_le_one (norm_nonneg q) qN1.le (by omega)

open QTheory
theorem jacobiTripleProduct {a q : ℂ} (a0 : a ≠ 0) (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasProd (fun n ↦ (1+a*q^(2*n+1)) * (1+a⁻¹*q^(2*n+1)) * (1-q^(2*n+2))) limit
    ∧ HasSum (fun z : ℤ ↦ a^z * q^(z^2)) limit := by
  have : ‖q^2‖ < 1 := by
    rw[norm_pow, pow_two, ←one_mul 1]
    apply mul_lt_mul'' qN1 qN1 (norm_nonneg q) (norm_nonneg q)
  have := jacobi_triple_product_hasSum_complex this (by field : (a*q) * (a⁻¹*q) = q^2)
  refine ⟨(q^2; q^2)_∞ * (-(a*q); q^2)_∞ * (-(a⁻¹*q); q^2)_∞, ?_, ?_⟩
  · have multipliable_a : Multipliable (fun n ↦ (1+a*q^(2*n+1))) := multipliable_b a qN1
    have multipliable_a_inv : Multipliable (fun n ↦ (1+a⁻¹*q^(2*n+1))) := multipliable_b a⁻¹ qN1
    have multipliable_q : Multipliable (fun n ↦ (1-q^(2*n+2))) := by
      simp_rw[(by intros; field : ∀ n : ℕ, 1-q^(2*n+2) = 1+(-q)*q^(2*n+1))]
      exact multipliable_b (-q) qN1
    rw [multipliable_a.mul multipliable_a_inv|>.mul multipliable_q |>.hasProd_iff]
    rw [mul_comm (q^2;_)_∞, mul_right_comm]; simp only [qPochhammerInf]
    have (b : ℂ) (n : ℕ) : b * q * (q^2)^n = b * q^(2*n+1) := by field
    simp only [neg_mul, this a, sub_neg_eq_add, this a⁻¹,
      (by intros; field : ∀ n : ℕ, q ^ 2 * (q ^ 2) ^ n = q ^ (2 * n + 2))]
    simp_rw [tprod_eq_of_multipliable_unconditional multipliable_a]
    simp_rw [tprod_eq_of_multipliable_unconditional multipliable_a_inv]
    simp_rw [tprod_eq_of_multipliable_unconditional multipliable_q]
    rw[multipliable_a.mul multipliable_a_inv |>.tprod_mul multipliable_q]
    rw[multipliable_a.tprod_mul multipliable_a_inv]
  · convert this using 1
    ext z; simp only [abPow]
    cases z with
    | ofNat n =>
      simp only [Int.ofNat_eq_natCast, zpow_natCast, Int.natAbs_natCast, ← pow_mul,
        n.two_mul_choose_two_right]
      by_cases! n0 : n = 0
      · simp[n0]
      rw[(by rfl : q^(n:ℤ)^2 = q^n^2), mul_pow, mul_assoc, ←pow_add, ←mul_one_add]
      rw[add_comm, Nat.sub_add_cancel (n.one_le_iff_ne_zero.mpr n0), pow_two]
    | negSucc n =>
      have : (Int.negSucc n)^2 = (n+1)^2 := Int.natAbs_eq_iff_sq_eq.mp rfl
      simp only [zpow_negSucc, this, Int.natAbs_negSucc, Nat.succ_eq_add_one, ← pow_mul,
        (n + 1).two_mul_choose_two_right, add_tsub_cancel_right]
      by_cases! n0 : n = 0
      · simp[n0]
      have : a⁻¹^n = (a^n)⁻¹ := by exact inv_pow a n
      rw[(by rfl : q^((n:ℤ)+1)^2 = q^(n+1)^2), mul_pow, inv_pow, mul_assoc, ←pow_add, ←mul_one_add]
      rw[add_comm 1, pow_two]

lemma JTP_1 {q : ℂ} (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasSum (fun z : ℤ ↦ (-1)^z * q^(z^2)) limit
    ∧ HasProd (fun n ↦ (1 - q^(n+1)) * (1 + q^(n+1))⁻¹) limit := by
  obtain ⟨l, prod, sum⟩ := jacobiTripleProduct (by grobner : (-1:ℂ) ≠ 0) qN1
  use l; refine ⟨sum, ?_⟩; clear sum
  simp only [neg_one_mul, (by ring : (-1:ℂ)⁻¹ = -1), ←sub_eq_add_neg, ←pow_two] at prod
  apply L_3 qN1 prod

lemma JTP_2 {q : ℂ} (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasSum (fun z : ℤ ↦ (-1)^z * q^(z^2)) limit
    ∧ HasProd (fun n ↦ ((1-q^(2*n+1)) * (1-q^(2*n+2)))
      * ((1+q^(2*n+2))⁻¹ * (1+q^(2*n+1))⁻¹)) limit := by
  obtain ⟨l, sum, prod⟩ := JTP_1 qN1
  use l; refine ⟨sum, ?_⟩
  have : (fun n ↦ (1-q^(2*n+1)) * (1-q^(2*n+2)) * ((1+q^(2*n+2))⁻¹ * (1+q^(2*n+1))⁻¹))
      = (fun n ↦ (1-q^(2*n+1)) * (1+q^(2*n+1))⁻¹ * ((1-q^(2*n+2)) * (1+q^(2*n+2))⁻¹)) := by
    ext n; ring
  rw[this]
  apply HasProd.in_pairs prod

lemma JTP_3 {q : ℂ} (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasProd (fun n ↦
      ((1+q^(4*n+2)) * (1-q^(2*n+2))) * ((1+q^(4*n+4))⁻¹ * (1+q^(2*n+1))⁻¹)
      * ((1+q^(2*n+2)) * (1-q^(2*n+1))⁻¹)) limit
    ∧ HasSum (fun z : ℤ ↦ q^(2*z^2)) limit := by
  have : ‖-q^2‖ < 1 := by
    rw[Complex.norm_neg', norm_pow, ←one_pow 2]
    exact zpow_lt_zpow_left₀ two_pos (norm_nonneg q) qN1
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
