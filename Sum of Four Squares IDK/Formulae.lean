import Mathlib
import «Sum of Four Squares IDK».«Various Sums & Prods v3»
import «Sum of Four Squares IDK».«Power & Multilinear Series v2»
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
open Finset Nat

def nrange (n : ℕ) := range (n+1)
#eval nrange 4

variable (r m n : ℕ)
def d := #{x ∈ nrange n | (x ∣ n) ∧ (x % m = r)}
-- Examples
#eval {x ∈ nrange 15 | (x ∣ 15) ∧ (x % 4 = 1)}
#eval d 1 4 15

lemma d_geom_sum {q : ℂ} (qB : q ∈ Metric.ball 0 1) {r m : ℕ} (r0 : r ≠ 0) (m0 : m ≠ 0)
    (rm : r < m) : ∃ limit : ℂ, HasSum (fun n ↦ q^(r*(n+1)) / (1 - q^(m*(n+1)))) limit
    ∧ HasSum (fun n ↦ d r m (n+1) * q^(n+1)) limit := by
  rw[mem_ball_zero_iff] at qB
  obtain ⟨limit, sumH⟩ : Summable (fun n ↦ q^(r*(n+1)) / (1-q^(m*(n+1)))) := by
    apply Summable.of_norm_bounded (g := fun n ↦ ‖q‖^n/(1-‖q‖))
    · apply Summable.div_const
      apply summable_geometric_of_lt_one (norm_nonneg q) qB
    · intro n
      rw[norm_div]
      apply div_le_div₀ (pow_nonneg (norm_nonneg q) n) _ (by linarith) _
      · rw[norm_pow]
        apply pow_le_pow_of_le_one (norm_nonneg q) qB.le
        trans n+1
        · linarith
        · apply Nat.le_mul_of_pos_left _ r0.pos
      · calc
          _ ≤ 1 - ‖q‖^(m*(n+1)) := by
            have : ‖q‖^(m*(n+1)) ≤ ‖q‖ := pow_le_of_le_one (norm_nonneg q) qB.le (by lia)
            grind
          _ ≤ _ := by
            rw[←norm_one (α := ℂ), ←norm_pow]
            apply norm_sub_norm_le
  refine ⟨limit, sumH, ?_⟩
  suffices : HasSum (fun p : ℕ × ℕ ↦ q^((p.1+1)*(m*p.2+r))) limit
  · let g := fun p : ℕ × ℕ ↦ (p.1+1)*(m*p.2+r) - 1
    have : (fun n ↦ (d r m (n+1)) * q^(n+1))
        = (fun n ↦ ∑' p : g⁻¹' {n}, q^(((p.1.1)+1)*(m*(p.1.2)+r))) := by
      ext n
      let f := fun x : ℕ ↦ (⟨(n+1)/x - 1, (x-r)/m⟩ : ℕ × ℕ)
      have : g⁻¹' {n} ⊆ {x ∈ nrange (n+1) | (x ∣ n+1) ∧ (x % m = r)}.image f := by
        intro p ph
        simp only [Set.mem_preimage, Set.mem_singleton_iff, g] at ph
        simp only [coe_image, coe_filter, Set.mem_image, Set.mem_setOf_eq]
        refine ⟨m*p.2 + r, ?_, ?_⟩
        · simp only [mul_add_mod_self_left, nrange, mem_range]
          refine ⟨by lia, ⟨p.1+1, by lia⟩, mod_eq_of_lt rm⟩
        · simp only [add_tsub_cancel_right, ← Nat.eq_div_of_mul_eq_right m0 rfl, Prod.ext_iff,
          and_true, f]
          rw[←ph, (by lia : (p.1+1) * (m*p.2+r) - 1 + 1 = (p.1+1) * (m*p.2+r))]
          rw[←Nat.eq_div_of_mul_eq_left (by omega) rfl]
          omega
      have : (g⁻¹' {n}).Finite := Set.Finite.subset (finite_toSet _) this
      calc
        _ = ∑ p ∈ this.toFinset, q^(n+1) := by
          rw[Finset.sum_const, nsmul_eq_mul]
          congr; symm
          apply Finset.card_bij (fun p _ ↦ m*p.2 + r)
          · intro p ph
            simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, g] at ph
            simp only [mem_filter, mul_add_mod_self_left, nrange, mem_range]
            refine ⟨by lia, ⟨p.1+1, by lia⟩, mod_eq_of_lt rm⟩
          · rintro p ph q qh eq
            simp only [Set.Finite.mem_toFinset, Set.mem_preimage, Set.mem_singleton_iff, g] at *
            rw[←qh, ←eq] at ph
            have : m * p.2 + r > 0 := by omega
            have ph := sub_one_cancel (mul_pos (by omega) this) (mul_pos (by omega) this) ph
            simp only [mul_eq_mul_right_iff, add_right_cancel_iff, Nat.add_eq_zero_iff,
              Nat.mul_eq_zero, r0, and_false, or_false] at ph
            refine Prod.ext_iff.mpr ⟨ph, ?_⟩
            exact (Nat.mul_right_inj m0).mp (add_right_cancel eq)
          · rintro x xh
            obtain ⟨xR, xn1, xmr⟩ := mem_filter.mp xh
            use ⟨(n+1)/x - 1, (x-r)/m⟩
            have h : m ∣ (x-r) := by
              apply dvd_of_mod_eq_zero (sub_mod_eq_zero_of_mod_eq _)
              rw[xmr]
              exact (mod_eq_of_lt rm).symm
            have : r ≤ x := by
              rw[←mod_add_div x m, xmr]
              omega
            simp only [Nat.mul_div_cancel' h, Nat.sub_add_cancel this, Set.Finite.mem_toFinset,
              Set.mem_preimage, Set.mem_singleton_iff, exists_prop, and_true, g]
            obtain ⟨y, xyn⟩ := xn1
            have x0 : x ≠ 0 := by omega
            have y0 : y ≠ 0 := by rintro rfl; omega
            rw[xyn, ←Nat.eq_div_of_mul_eq_right x0 rfl, sub_one_add_one y0]
            lia
        _ = ∑' p : g⁻¹' {n}, q^(n+1) := by
          convert (Finset.tsum_subtype' _ _).symm
          apply this.coe_toFinset.symm
        _ = _ := by
          congr
          ext ⟨p, ph⟩
          simp only [Set.mem_preimage, Set.mem_singleton_iff, g] at ph
          congr
          lia
    rw[this]; clear this
    exact HasSum.tsum_fiberwise this g
  show HasSum (fun (p : ℕ × ℕ) ↦ q^((p.1+1)*(m*p.2+r))) limit
  have p_fun_summable : Summable (fun p : ℕ × ℕ ↦ q^((p.1+1)*(m*p.2+r))) := by
    have : ∀ p : ℕ × ℕ, ‖q^((p.1+1) * (m*p.2+r))‖ ≤ ‖q^(p.1)*q^(p.2)‖ := by
      rintro ⟨a, b⟩
      simp only [norm_pow, ←pow_add]
      apply pow_le_pow_of_le_one (norm_nonneg q) qB.le
      rw[add_mul]
      apply Nat.add_le_add
      · exact Nat.le_mul_of_pos_right a (by omega)
      · rw[one_mul]
        exact le_add_right_of_le (Nat.le_mul_of_pos_left b m0.pos)
    apply Summable.of_norm_bounded _ this
    apply Summable.mul_norm
      <;> (simp only [norm_pow]; exact summable_geometric_of_lt_one (norm_nonneg q) qB)
  apply (Summable.hasSum_iff p_fun_summable).mpr
  · rw[Summable.tsum_prod p_fun_summable]
    have : (fun a ↦ ∑' b : ℕ, q^((a+1) * (m*b+r)))
        = (fun a ↦ q^(r*(a+1)) * (1 - q^(m*(a+1)))⁻¹) := by
      ext a
      rw[←tsum_geometric_of_norm_lt_one]; rotate_left
      · rw[norm_pow]
        exact pow_lt_one₀ (norm_nonneg q) (by simpa [mem_ball_zero_iff] using qB) (by lia)
      rw[←smul_eq_mul, ←tsum_const_smul'']
      congr
      ext b
      rw[smul_eq_mul, ←pow_mul, ←pow_add]
      grind
    simp only [this, ← div_eq_mul_inv]
    exact sumH.tsum_eq

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

lemma Int.neg_self_le_self_sq (a : ℤ) : -a ≤ a^2 := by
  exact sq_abs a ▸ (neg_le_abs a).trans (Int.le_self_sq |a|)

lemma L_4 {q : ℂ} (qN1 : ‖q‖ < 1) : ∀ limit : ℂ, HasSum (fun z : ℤ ↦ q^(z^2)) limit
    → HasSum (term (fun n ↦ sum_sq_sq n) q) (limit^2) := by
  intro limit sumH
  suffices h : HasSum (fun (p : ℤ × ℤ) ↦ q^(p.1^2) * q^(p.2^2)) (limit^2)
  · let g := fun (p : ℤ × ℤ) ↦ (p.1^2 + p.2^2).toNat
    have : (term (fun n  ↦ ↑(sum_sq_sq n)) q)
        = (fun (n : ℕ) ↦ ∑' p : g ⁻¹' {n}, q^(p.1.1^2) * q^(p.1.2^2)) := by
      ext n
      have : g⁻¹' {n} ⊆ (Finset.product (zrange n) (zrange n)) := by
        intro p pR
        simp only [product_eq_sprod, coe_product, Set.mem_prod, SetLike.mem_coe]
        have : 0 ≤ p.1^2 + p.2^2 := by linarith [sq_nonneg p.1, sq_nonneg p.2]
        simp [g] at pR
        have eq : p.1^2 + p.2^2 = n := by omega
        have {a b : ℤ} (h : a^2 + b^2 = n) : (a ∈ zrange n) := by
          simp only [zrange, mem_image, mem_range, Order.lt_add_one_iff]
          use (a + n).toNat
          have : a + n ≥ 0 := by linarith [Int.neg_self_le_self_sq a, sq_nonneg b]
          simp [max_eq_left this, two_mul]
          linarith [Int.le_self_sq a, sq_nonneg b]
        exact ⟨this eq, this (add_comm (p.1^2) _ ▸ eq)⟩
      have g_finite : (g⁻¹' {n}).Finite := Set.Finite.subset (finite_toSet _) this
      calc
        _ = ∑ p ∈ g_finite.toFinset, q^n := by
          simp only [term, sum_sq_sq, Int.cast_natCast, sum_const, nsmul_eq_mul,
            mul_eq_mul_right_iff, Nat.cast_inj, pow_eq_zero_iff', ne_eq]
          left
          apply Finset.card_bij (fun p _ ↦ ⟨p.1.1, p.2.1⟩)
          · simp [g]
            grind
          · grind
          · intro p pR
            have : 0 ≤ p.1^2 + p.2^2 := by linarith [sq_nonneg p.1, sq_nonneg p.2]
            simp [g] at pR
            have eq : p.1^2 + p.2^2 = n := by omega
            have {a b : ℤ} (h : a^2 + b^2 = n) : (a ∈ zrange n) := by
              simp only [zrange, mem_image, mem_range, Order.lt_add_one_iff]
              use (a + n).toNat
              have : a + n ≥ 0 := by linarith [Int.neg_self_le_self_sq a, sq_nonneg b]
              simp [max_eq_left this, two_mul]
              linarith [Int.le_self_sq a, sq_nonneg b]
            use ⟨⟨p.1, this eq⟩, ⟨p.2, this (add_comm (p.1^2) _ ▸ eq)⟩⟩
            simpa
        _ = ∑' p : g⁻¹' {n}, q^n := by
          convert (Finset.tsum_subtype' _ _).symm
          apply g_finite.coe_toFinset.symm
        _ = _ := by
          congr
          ext ⟨p, pR⟩
          have : 0 ≤ p.1^2 + p.2^2 := by linarith [sq_nonneg p.1, sq_nonneg p.2]
          simp [g] at pR
          rw[←zpow_natCast]
          have : ↑n = p.1^2 + p.2^2 := by omega
          by_cases q0 : q = 0
          · by_cases h : p.1 = 0
            · rw[this]; simp [h]
            simp only [q0, this, zero_zpow _ (pow_ne_zero 2 h), zero_mul]
            apply zero_zpow
            apply Int.ne_of_gt
            have := lt_of_le_of_ne (sq_nonneg p.1) (pow_ne_zero 2 h).symm
            linarith [sq_nonneg p.2]
          simp [this, zpow_add₀ q0]
    rw[this]
    exact HasSum.tsum_fiberwise h g
  show HasSum (fun (p : ℤ × ℤ) ↦ q^(p.1^2) * q^(p.2^2)) (limit^2)
  have prod_summable : Summable (fun (p : ℤ × ℤ) ↦ q^(p.1^2) * q^(p.2^2)) := by
    apply Summable.of_norm
    have : Summable (fun (z : ℤ) ↦ ‖q^(z^2)‖) := by
      have : (fun (z : ℤ) ↦ ‖q^(z^2)‖) = Int.rec (fun n ↦ ‖q^(n^2)‖) (fun n ↦ ‖q^((n+1)^2)‖) := by
        ext z
        cases z with
        | ofNat n =>
            simp only [Int.ofNat_eq_natCast, norm_zpow, norm_pow]
            rw[←zpow_natCast, Int.natCast_pow]
        | negSucc n =>
            simp only [norm_zpow, norm_pow]
            rw[(Int.natAbs_eq_iff_sq_eq.mp rfl : (Int.negSucc n)^2 = (n+1)^2)]
            exact_mod_cast rfl
      rw[this]
      apply Summable.int_rec <;> (
          apply Summable.of_norm_bounded (summable_geometric_of_lt_one (norm_nonneg q) qN1);
          intro i; rw[norm_norm, norm_pow];
          apply pow_le_pow_of_le_one (norm_nonneg q) qN1.le;)
      · exact Nat.le_self_pow two_ne_zero i
      · have := Nat.le_self_pow two_ne_zero (i+1)
        linarith
    -- have h := Summable.mul_norm this this
    -- exact h
    -- rw[(rfl : NonUnitalSeminormedRing.toSeminormedAddCommGroup.toNorm
    --     = instCommCStarAlgebraComplex.toCStarAlgebra.toNorm)]
    -- exact Summable.mul_norm this this
    exact (Summable.mul_norm this this : _)
  rw[prod_summable.hasSum_iff, Summable.tsum_prod prod_summable]
  calc
    _ = ∑' (w : ℤ), (q^(w^2) * ∑' (z : ℤ), q^(z^2)) := by
      refine tsum_congr ?_
      intro b
      simp [tsum_mul_left]
    _ = _ := by rw[sumH.tsum_eq, tsum_mul_right, sumH.tsum_eq, pow_two]

end sum_of_squares_formulae


section sum_sq_sq_formula
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
#eval sum_sq_sq 0

theorem Jacobi_sum_of_two_squares : sum_sq_sq
    = fun n ↦ if n = 0 then 1 else 4*(d 1 4 n - d 3 4 n) := by
  suffices h : (fun n ↦ (sum_sq_sq n : ℤ))
      = (fun n ↦ if n = 0 then 1 else 4*((d 1 4 n : ℤ) - (d 3 4 n)))
  · ext n
    have eq := congrFun h n
    grind
  apply eq_PS_on_disk
  intro q qB
  have : -q ∈ Metric.ball 0 1 := by
    apply mem_ball_zero_iff.mpr
    rw[norm_neg]
    exact mem_ball_zero_iff.mp qB
  obtain ⟨lL, lR, sumL, sumR, eq⟩ := eq_C' this
  use lL^2
  constructor
  · have : (fun (z:ℤ) ↦ (-1) ^ z * (-q) ^ z ^ 2) = (fun z ↦ q^(z^2)) := by
      ext z
      have : (-1:ℂ)^z * (-1)^(z^2) = 1 := by
        simp[L_2 z two_ne_zero, ←zpow_add₀, ←two_mul, Even.neg_one_zpow]
      rw[neg_eq_neg_one_mul q, mul_zpow, ←mul_assoc, this, one_mul]
    rw[this] at sumL
    exact L_4 (mem_ball_zero_iff.mp qB) lL sumL
  · rw[eq]
    suffices h : HasSum (fun n ↦ (d 1 4 (n+1))*q^(n+1) - (d 3 4 (n+1))*q^(n+1)) lR
    · have : 1 = ∑ i ∈ range 1, (term (fun n ↦ if n = 0 then 1
          else 4 * (d 1 4 n - d 3 4 n)) q) i := by simp[term]
      rw[add_comm, this, ←hasSum_nat_add_iff]; clear this
      simp only [term, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceIte, Int.cast_mul,
        Int.cast_ofNat, mul_assoc]
      apply HasSum.mul_left 4
      have : (fun n ↦ ↑((d 1 4 (n+1) : ℤ) - (d 3 4 (n+1))) * q^(n+1))
          = (fun n ↦ (d 1 4 (n+1))*q^(n+1) - (d 3 4 (n+1))*q^(n+1)) := by
        ext n
        rw[←sub_mul]
        congr
        simp
      rwa[this]
    have : (fun n ↦ (- -q)^(n+1) / (1 + (- -q)^(2*n+2)))
        = (fun n ↦ q^(1*(n+1)) / (1-q^(4*(n+1))) - q^(3*(n+1)) / (1-q^(4*(n+1)))) := by
      ext n
      calc
        _ = q^(n+1) * (1-q^(2*n+2)) / ((1+q^(2*n+2)) * (1-q^(2*n+2))) := by
          have : 1-q^(2*n+2) ≠ 0 := by apply W0_terms' (mem_ball_zero_iff.mp qB) (by omega)
          field
        _ = _ := by ring
    rw[this] at sumR; clear this
    obtain ⟨l1, ⟨h1_quot, h1_d⟩⟩ := d_geom_sum qB one_ne_zero four_ne_zero (by omega)
    obtain ⟨l3, ⟨h3_quot, h3_d⟩⟩ := d_geom_sum qB three_ne_zero four_ne_zero (by omega)
    rw[HasSum.unique sumR (HasSum.sub h1_quot h3_quot)]
    apply HasSum.sub h1_d h3_d

end sum_sq_sq_formula
