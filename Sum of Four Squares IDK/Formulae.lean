import Mathlib
import «Sum of Four Squares IDK».«Power & Multilinear Series»

noncomputable section
open Set Finset Topology

variable (r m n : ℕ)
def d := #{x ∈ range (n+1) | (x ∣ n) ∧ (x % m = r)}
#eval {x ∈ range (9+1) | (x ∣ 9) ∧ (x % 4 = 1)}
#eval d 1 4 9
def U x := {q : ℂ | q ≠ 0 ∧ ‖q‖ < 1 ∧ ∀ n : ℕ, 1 - q^n*x + q^(2*n) ≠ 0}


-- lemma
#check geom_series_eq_inverse
lemma h (q : ℂ) (k : ‖q‖ < 1) : HasSum (fun n ↦ q^n) (1-q)⁻¹ := by
  exact hasSum_geometric_of_norm_lt_one k

lemma negOnePow_mul_self (z : ℤ) : (-1:ℂ)^(z^2) = (-1:ℂ)^z := by
  sorry

lemma negOneZpow_even (z : ℤ) : (-1:ℂ)^(2*z) = 1 := by sorry

lemma negOnePow_odd (n : ℕ) : (-1:ℂ)^(2*n+1) = -1 := by
  rw[neg_one_pow_eq_pow_mod_two]
  simp only [Nat.mul_add_mod_self_left, Nat.mod_succ, pow_one]

lemma negOnePow_even (n : ℕ) : (-1:ℂ)^(2*n+2) = 1 := by
  rw[neg_one_pow_eq_pow_mod_two]
  simp only [Nat.add_mod_right, Nat.mul_mod_right, pow_zero]





-- Results about the Jacobi Triple Product
axiom jacobiTripleProduct {a q : ℂ} (a0 : a ≠ 0) (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasProd (fun n ↦ (1+a*q^(2*n+1)) * (1+a⁻¹*q^(2*n+1)) * (1-q^(2*n+2))) limit
    ∧ HasSum (fun z : ℤ ↦ a^z * q^(z^2)) limit

lemma JTP_1 {q : ℂ} (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasProd (fun n ↦ (1 - q^(n+1)) * (1 + q^(n+1))⁻¹) limit
    ∧ HasSum (fun z : ℤ ↦ (-1)^z * q^(z^2)) limit := by
  obtain ⟨l, prod, sum⟩ := jacobiTripleProduct (a := -1) (by grind only) qN1
  use l; refine ⟨?_, sum⟩
  sorry

lemma JTP_2 {q : ℂ} (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasProd (fun n ↦
      ((1-q^(2*n+1)) * (1-q^(2*n+2))) * ((1+q^(2*n+2))⁻¹ * (1+q^(2*n+1))⁻¹)) limit
    ∧ HasSum (fun z : ℤ ↦ (-1)^z * q^(z^2)) limit := by
  sorry

lemma JTP_3 {q : ℂ} (qN1 : ‖q‖ < 1) :
    ∃ limit : ℂ, HasProd (fun n ↦
      ((1+q^(4*n+2)) * (1-q^(2*n+2))) * ((1+q^(4*n+4))⁻¹ * (1+q^(2*n+1))⁻¹)
      * ((1+q^(2*n+2)) * (1-q^(2*n+1))⁻¹)) limit
    ∧ HasSum (fun z : ℤ ↦ q^(2*z^2)) limit := by
  have : ‖-q^2‖ < 1 := by
    rw[Complex.norm_neg', norm_pow, ←one_pow 2]
    exact zpow_lt_zpow_left₀ two_pos (norm_nonneg q) qN1
  obtain ⟨l, prod, sum⟩ := JTP_2 this
  use l; constructor
  · have : (fun n ↦
          (1-(-q^2)^(2*n+1)) * (1-(-q^2)^(2*n+2)) * ((1+(-q^2)^(2*n+2))⁻¹ * (1+(-q^2)^(2*n+1))⁻¹))
        = (fun n ↦ (1+q^(4*n+2)) * (1-q^(2*n+2)) * ((1+q^(4*n+4))⁻¹ * (1+q^(2*n+1))⁻¹)
          * ((1+q^(2*n+2)) * (1-q^(2*n+1))⁻¹)) := by
      ext n
      repeat rw[neg_eq_neg_one_mul (q^2), mul_pow, mul_pow, ←pow_mul, ←pow_mul]
      repeat rw[negOnePow_odd, negOnePow_even, one_mul]
      rw[(by omega : 2*(2*n+2) = 4*n+4), (by omega : 2*(2*n+1) = 4*n+2)]
      rw[(by ring : 1 - (-1) * (q^(4*n+2)) = 1 + (q^(4*n+2)))]
      rw[(by ring : 1 + (-1) * (q^(4*n+2)) = 1 - (q^(4*n+2)))]
      rw[(by field : (1 - q ^ (4 * n + 2))⁻¹ = (1 + q ^ (2 * n + 1))⁻¹ * (1 - q ^ (2 * n + 1))⁻¹)]
      ring
    simpa [this] using prod
  · have : (fun z:ℤ ↦ (-1)^z * (-q^2)^(z^2)) = (fun z ↦ q^(2*z^2)) := by
      ext z
      rw[neg_eq_neg_one_mul (q^2), mul_zpow, negOnePow_mul_self, ←mul_assoc]
      rw[←zpow_two, ←zpow_mul, mul_comm z, negOneZpow_even z, one_mul, zpow_mul]
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
