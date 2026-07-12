import Mathlib

noncomputable section
open Set Finset Topology FormalMultilinearSeries

-- "p" is a FormalMultilinearSeries
def coeffs_to_p (f : ℕ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (f n)
def term (f : ℕ → ℂ) (q : ℂ) := fun n ↦ f n * q^n
def convDisk1 (f : ℕ → ℂ) := ∀ q ∈ Metric.ball 0 1, Summable (term f q)
def evalPS {f : ℕ → ℂ} (_ : convDisk1 f) := fun q ↦ ∑' n, term f q n

lemma ball_eq_eball (a : ℂ) (r : ℝ) : Metric.ball a r = Metric.eball a r.toNNReal := by
    ext x
    rw[Metric.mem_ball, Complex.dist_eq, Metric.mem_eball]
    rw[←Real.toNNReal_lt_toNNReal_iff_of_nonneg (norm_nonneg (x-a))]
    convert ENNReal.coe_lt_coe.symm
    rw[edist_eq_enorm_sub, norm_toNNReal]
    exact enorm_eq_nnnorm (x-a)

lemma PSAt_of_pos_convDisk1 {f : ℕ → ℂ} (fconv : convDisk1 f)
    (fpos : ∀ n : ℕ, ‖f n‖ = f n) :
    HasFPowerSeriesAt (evalPS fconv) (coeffs_to_p f) 0 := by
  use (1 : NNReal)
  refine ⟨?_, one_pos, ?_⟩
  · rw[ENNReal.coe_one]
    by_contra!
    obtain ⟨r, rh, r1⟩ := exists_between this
    obtain ⟨s, rfl⟩ : ∃ s : NNReal, r = ↑s := by
      apply ENNReal.exists_ne_top.mp
      use r; refine ⟨?_, rfl⟩
      have := le_top (a := (1:ENNReal))
      grind_order
    rw[(by rw[Complex.nnnorm_real, NNReal.nnnorm_eq] : s = ‖(s:ℂ)‖₊)] at rh
    have := not_summable_norm_of_radius_lt_nnnorm (coeffs_to_p f) rh
    simp only [coeffs_to_p, ContinuousMultilinearMap.norm_mkPiRing, Complex.norm_real,
      Real.norm_eq_abs, NNReal.abs_eq] at this
    contrapose! this; clear this
    apply (RCLike.summable_ofReal ℂ).mp
    simp only [Complex.coe_algebraMap, Complex.ofReal_mul, fpos, Complex.ofReal_pow]
    refine fconv s ?_
    apply mem_ball_zero_iff.mpr
    rw[Complex.norm_of_nonneg NNReal.zero_le_coe]
    simp only [ENNReal.coe_lt_one_iff, NNReal.coe_lt_one] at *
    assumption
  · intro q qB
    rw[←Real.toNNReal_one, ←ball_eq_eball] at qB
    simp only [coeffs_to_p, ContinuousMultilinearMap.mkPiRing_apply, prod_const, card_univ,
      Fintype.card_fin, smul_eq_mul, evalPS, zero_add, mul_comm (q^_)]
    apply (fconv q qB).hasSum


example (f g : ℕ → ℂ) (fconv : convDisk1 f) (gconv : convDisk1 g)
    (fpos : ∀ n : ℕ, ‖f n‖ = f n) (gpos : ∀ n : ℕ, ‖g n‖ = g n) : f = g := by
  have : (evalPS fconv) = (evalPS gconv) := by sorry
  have := HasFPowerSeriesAt.eq_formalMultilinearSeries
      (PSAt_of_pos_convDisk1 fconv fpos) (this ▸ PSAt_of_pos_convDisk1 gconv gpos)
  ext n
  have : coeffs_to_p f n = coeffs_to_p g n := by sorry
  apply ContinuousMultilinearMap.mkPiRing_eq_iff.mp this

  -- have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
  --     (hxxx fconv fpos) (hxxx gconv gpos)
  --     (Metric.isPreconnected_ball) (Metric.mem_ball_self one_pos) (sorry)

  -- exact (Set.eqOn_univ (evalPS fconv) (evalPS gconv)).mp this

-- example (f g : ℂ → ℂ) (fpos : ∀ n : ℕ, ‖f n‖ = f n) (fpos : ∀ n : ℕ, ‖f n‖ = f n): f = g := by
--   have := AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq
--       (sorry : AnalyticOnNhd ℂ f Set.univ) (sorry : AnalyticOnNhd ℂ g Set.univ)
--       (isPreconnected_univ) (Set.mem_univ 0 : 0 ∈ Set.univ) (sorry) (z₀ := 0)
--   exact (Set.eqOn_univ f g).mp this



-- lemma hxxx {f : ℕ → ℂ} (fconv : convDisk1 f) (fpos : ∀ n : ℕ, ‖f n‖ = f n) :
--     AnalyticOnNhd ℂ (evalPS fconv) (Metric.ball 0 1) := by
--   rw[ball_eq_eball]
--   apply HasFPowerSeriesOnBall.analyticOnNhd (p := coeffs_to_p f)
--   refine ⟨?_, Real.toNNReal_one ▸ one_pos, ?_⟩
--   · rw[Real.toNNReal_one, ENNReal.coe_one]
--     by_contra!
--     obtain ⟨r, rh, r1⟩ := exists_between this
--     obtain ⟨s, rfl⟩ : ∃ s : NNReal, r = ↑s := by
--       apply ENNReal.exists_ne_top.mp
--       use r; refine ⟨?_, rfl⟩
--       have := le_top (a := (1:ENNReal))
--       grind_order
--     rw[(by rw[Complex.nnnorm_real, NNReal.nnnorm_eq] : s = ‖(s:ℂ)‖₊)] at rh
--     have := not_summable_norm_of_radius_lt_nnnorm (coeffs_to_p f) rh
--     simp only [coeffs_to_p, ContinuousMultilinearMap.norm_mkPiRing, Complex.norm_real,
--       Real.norm_eq_abs, NNReal.abs_eq] at this
--     contrapose! this; clear this
--     apply (RCLike.summable_ofReal ℂ).mp
--     simp only [Complex.coe_algebraMap, Complex.ofReal_mul, fpos, Complex.ofReal_pow]
--     refine fconv s ?_
--     apply mem_ball_zero_iff.mpr
--     rw[Complex.norm_of_nonneg NNReal.zero_le_coe]
--     simp only [ENNReal.coe_lt_one_iff, NNReal.coe_lt_one] at *
--     assumption
--   · intro q qB
--     rw[←ball_eq_eball] at qB
--     simp only [coeffs_to_p, ContinuousMultilinearMap.mkPiRing_apply, prod_const, card_univ,
--       Fintype.card_fin, smul_eq_mul, evalPS, zero_add, mul_comm (q^_)]
--     apply (fconv q qB).hasSum

-- HasFPowerSeriesAt.eq_formalMultilinearSeries
-- HasFPowerSeriesOnBall f p&q 0 1 → HasFPowerSeriesAt
-- Look at context after Line 24












-- def absConvDisk1 (f : ℕ → ℂ) := ∀ q ∈ Metric.ball 0 1, Summable (fPowS (fun n ↦ ‖f n‖) q)

-- theorem conv_of_absConv {f : ℕ → ℂ} (h : absConvDisk1 f) : convDisk1 f := by sorry
-- -- summable_of_absolute_convergence_real

-- theorem pRadius_le_1 {f : ℕ → ℂ} (h : absConvDisk1 f) : 1 ≤ (coeffs_to_p f).radius := by
--   let p := coeffs_to_p f
--   have (n : ℕ) : ‖p n‖ = ‖f n‖ := by
--     simp only [coeffs_to_p, ContinuousMultilinearMap.norm_mkPiRing, p]
--   sorry
--   -- apply FormalMultilinearSeries.le_radius_of_bound _ ()
--   -- intro n




-- instance powSeriesCoincidesMultilinMap {f : ℕ → ℂ} (h : absConvDisk1 f) :
--     HasFPowerSeriesOnBall (evalPowerSeries h) (coeffs_to_p f) 0 1 where
--   r_le := pRadius_le_1 h
--   r_pos := one_pos
--   hasSum := by
--     sorry

-- theorem powSeriesUniqueRadius1 {f g : ℕ → ℂ} (hf : absConvDisk1 f) (hg : absConvDisk1 g)
--     (h : ∀ q ∈ Metric.ball 0 1, (evalPowerSeries hf q) = (evalPowerSeries hg q)) : f = g := by

--   sorry

end
