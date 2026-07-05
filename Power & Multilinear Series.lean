import Mathlib

noncomputable section
open Set Finset Topology

-- "p" is a FormalMultilinearSeries
def coeffs_to_p (f : ℕ → ℂ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (f n)
def fPowS (f : ℕ → ℂ) (q : ℂ) := fun n ↦ f n * q^n
def convDisk1 (f : ℕ → ℂ) := ∀ q ∈ Metric.ball 0 1, Summable (fPowS f q)
def absConvDisk1 (f : ℕ → ℂ) := ∀ q ∈ Metric.ball 0 1, Summable (fPowS (fun n ↦ ‖f n‖) q)
def evalPowerSeries {f : ℕ → ℂ} (_ : convDisk1 f) := fun q ↦ ∑' n, fPowS f q n

theorem conv_of_absConv {f : ℕ → ℂ} (h : absConvDisk1 f) : convDisk1 f := by sorry
-- summable_of_absolute_convergence_real

theorem pRadius_le_1 {f : ℕ → ℂ} (h : absConvDisk1 f) : 1 ≤ (coeffs_to_p f).radius := by
  let p := coeffs_to_p f
  have (n : ℕ) : ‖p n‖ = ‖f n‖ := by
    simp only [coeffs_to_p, ContinuousMultilinearMap.norm_mkPiRing, p]
  sorry
  -- apply FormalMultilinearSeries.le_radius_of_bound _ ()
  -- intro n




instance powSeriesCoincidesMultilinMap {f : ℕ → ℂ} (h : absConvDisk1 f) :
    HasFPowerSeriesOnBall (evalPowerSeries h) (coeffs_to_p f) 0 1 where
  r_le := pRadius_le_1 h
  r_pos := one_pos
  hasSum := by
    sorry

theorem powSeriesUniqueRadius1 {f g : ℕ → ℂ} (hf : absConvDisk1 f) (hg : absConvDisk1 g)
    (h : ∀ q ∈ Metric.ball 0 1, (evalPowerSeries hf q) = (evalPowerSeries hg q)) : f = g := by

  sorry

end
