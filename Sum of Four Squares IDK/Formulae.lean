import Mathlib
import «Sum of Four Squares IDK».«Various Sums & Prods v3»

set_option linter.style.whitespace false

noncomputable section prod_props
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


noncomputable section d_lemmas
open Finset

variable (r m n : ℕ)
def d := #{x ∈ range (n+1) | (x ∣ n) ∧ (x % m = r)}
#eval {x ∈ range (9+1) | (x ∣ 9) ∧ (x % 4 = 1)}
#eval d 1 4 9
def U x := {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1 ∧ ∀ n : ℕ, 1 - q^n*x + q^(2*n) ≠ 0}

end d_lemmas



noncomputable section
open Topology

lemma L_2 [Field α] (z : ℤ) {n : ℕ} (n0 : n ≠ 0) : (-1:α)^(z^n) = (-1:α)^z := by
  by_cases h : Even z
  · rw[Even.neg_one_zpow h, Even.neg_one_zpow (h.pow_of_ne_zero n0)]
  · have h := by exact Int.not_even_iff_odd.mp h
    rw[Odd.neg_one_zpow h, Odd.neg_one_zpow h.pow]

example (f g : ℂ → ℂ) : f = g := by
  have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
      (sorry : AnalyticOnNhd ℂ f Set.univ) (sorry : AnalyticOnNhd ℂ g Set.univ)
      (isPreconnected_univ) (Set.mem_univ 0 : 0 ∈ Set.univ) (sorry) (z₀ := 0)
  exact (Set.eqOn_univ f g).mp this



-- lemma
#check geom_series_eq_inverse
lemma h (q : ℂ) (k : ‖q‖ < 1) : HasSum (fun n ↦ q^n) (1-q)⁻¹ := by
  exact hasSum_geometric_of_norm_lt_one k



-- Results about the Jacobi Triple Product
def statementOf_jacobiTripleProduct {a q : ℂ} (a0 : a ≠ 0) (qN1 : ‖q‖ < 1) : Prop :=
    ∃ limit : ℂ, HasProd (fun n ↦ (1+a*q^(2*n+1)) * (1+a⁻¹*q^(2*n+1)) * (1-q^(2*n+2))) limit
    ∧ HasSum (fun z : ℤ ↦ a^z * q^(z^2)) limit
-- axiom jacobiTripleProduct {a q : ℂ} (a0 : a ≠ 0) (qN1 : ‖q‖ < 1) :
--   statementOf_jacobiTripleProduct a0 qN1
-- variable (a q : ℂ) (a0 : a ≠ 0) (qN1 : ‖q‖ < 1)
variable (jtp : Π {a q : ℂ} (a0 : a ≠ 0) (qN1 : ‖q‖ < 1), statementOf_jacobiTripleProduct a0 qN1)
include jtp

lemma JTP_1 {q : ℂ} (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasSum (fun z : ℤ ↦ (-1)^z * q^(z^2)) limit
    ∧ HasProd (fun n ↦ (1 - q^(n+1)) * (1 + q^(n+1))⁻¹) limit := by
  obtain ⟨l, prod, sum⟩ := jtp (by grobner : (-1:ℂ) ≠ 0) qN1
  use l; refine ⟨sum, ?_⟩; clear sum
  simp only [neg_one_mul, (by ring : (-1:ℂ)⁻¹ = -1), ←sub_eq_add_neg, ←pow_two] at prod
  apply L_3 qN1 prod

lemma JTP_2 {q : ℂ} (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasSum (fun z : ℤ ↦ (-1)^z * q^(z^2)) limit
    ∧ HasProd (fun n ↦ ((1-q^(2*n+1)) * (1-q^(2*n+2)))
      * ((1+q^(2*n+2))⁻¹ * (1+q^(2*n+1))⁻¹)) limit := by
  obtain ⟨l, sum, prod⟩ := JTP_1 jtp qN1
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
  obtain ⟨l, sum, prod⟩ := JTP_2 jtp this
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


lemma eq_2_aq {q x : ℂ} (qU : q ∈ Metric.ball 0 1) :
    (2-x)⁻¹ * ∏' n : ℕ, (1 + q^(n+1)*x + q^(2*n+2))
      * (1 - q^(n+1)*x + q^(2*n+2))⁻¹ * ((1 - q^(n+1))^2 * (1 + q^(n+1))⁻¹^2)
    = (2-x)⁻¹ + 2 * ∑' n : ℕ, (-1)^(n+1) * q^(n+1) * (1 - q^n*x + q^(2*n)) := by
  sorry

-- lemma eqC_1 {L R : ℕ → ℂ} {U : Set ℂ} (limU : 0 ∈ closure U) (U0 : 0 ∉ U)
--     (H : ∀ q ∈ U, ∃ limit, HasSum (fun n ↦ (L n) * q ^ n) limit
--     ∧ HasSum (fun n ↦ (R n) * q ^ n) limit) : ∀ n : ℕ, L n = R n := by
--   let M (n : ℕ) := L n - R n
--   intro _; apply Nat.strong_induction_on (p := fun n ↦ L n = R n)
--   intro N hN
--   by_contra!
--   have MN0 : M N ≠ 0 := sub_ne_zero_of_ne this
--   have HS0 : ∀ q ∈ U, HasSum (fun n ↦ M (N+n) / M N * q^n) 0 := by
--     intro q qU; obtain ⟨limit, Ll, Rl⟩ := H q qU
--     have eq := (sub_self limit) ▸ HasSum.sub Ll Rl
--     have : (fun n ↦ (L n) * q^n - (R n) * q^n) = (fun n ↦ q^n • (M n)) := by
--       ext; simp only [M, smul_eq_mul]; ring
--     rw[this] at eq
--     have : ∀ n < N, M n = 0 := by intro n nN; simp only [hN n nN, sub_self, M]
--     obtain ⟨t, ht, A⟩ := HasSum.exists_hasSum_smul_of_apply_eq_zero eq this
--     have : q^N ≠ 0 := by apply pow_ne_zero; rintro rfl; exact U0 qU
--     have : t = 0 := by simpa [smul_eq_mul, this] using ht
--     rw[this] at A
--     have : (fun n ↦ q^n • M (n+N)) = (fun n ↦ M N * (M (N + n) / M N * q ^ n)) := by
--       ext n; rw[smul_eq_mul, add_comm]; field_simp
--     rw[this] at A
--     apply HasSum.mul_left (M N)⁻¹ at A
--     simpa [←mul_assoc, inv_mul_cancel₀ MN0] using A
--   have HSlimit : TendsTo


--   simp at this
--   -- grind
--   sorry

lemma eq_C (N : ℕ) (N1 : N ≥ 1) : Nat.card {p : ℤ × ℤ // p.1^2 + p.2^2 = N}
    = 4 * (d 1 4 N - d 3 4 N) := by
  have N0 : N ≠ 0 := Nat.ne_zero_of_lt N1
  let L := fun (n:ℕ) ↦ Nat.card {p : ℤ × ℤ // p.1^2 + p.2^2 = n}
  let R := fun n ↦ if n = 0 then 1 else 4 * (d 1 4 N - d 3 4 N)
  have hL : absConvDisk1 (fun n ↦ L n) := by sorry
  have hR : absConvDisk1 (fun n ↦ R n) := by sorry
  have : ∀ q ∈ Metric.ball 0 1, (evalPowerSeries hL q) = (evalPowerSeries hR q) := by
    -- Apply eq_2_aq somewhere in here
    sorry
  apply powSeriesUniqueRadius1 hL hR at this
  apply_fun (fun X ↦ X N) at this
  dsimp at this
  simp only [L, R, if_neg N0] at this
  exact_mod_cast this

end
