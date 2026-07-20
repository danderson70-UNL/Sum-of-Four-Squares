import Mathlib

noncomputable section
open Set Finset Topology FormalMultilinearSeries Complex

-- "p" is a FormalMultilinearSeries
def coeffs_to_p (f : ℕ → ℤ) : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun n ↦ ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (f n)
def term (f : ℕ → ℤ) (q : ℂ) := fun n ↦ ↑(f n) * q^n
def convDisk1 (f : ℕ → ℤ) := ∀ q ∈ Metric.ball 0 1, Summable (term f q)
def evalPS (f : ℕ → ℤ) := fun q ↦ ∑' n, term f q n
#check FormalMultilinearSeries.summable

lemma PS_at_of_pos_convDisk1 {f : ℕ → ℤ} (fconv : convDisk1 f) :
    HasFPowerSeriesAt (evalPS f) (coeffs_to_p f) 0 := by
  rw[hasFPowerSeriesAt_iff']
  apply Filter.eventually_iff_exists_mem.mpr ⟨Metric.ball 0 1,
      by apply Metric.ball_mem_nhds 0 one_pos, ?_⟩
  intro q qB
  simp only [sub_zero, coeff, coeffs_to_p, ContinuousMultilinearMap.mkPiRing_apply, Pi.one_apply,
    prod_const_one, smul_eq_mul, one_mul, mul_comm (q ^ _), evalPS]
  rw[(by grind[term] : (fun n ↦ (f n : ℂ) * q^n) = term f q)]
  have := (fconv q qB).hasSum
  grind [term]

theorem eq_PS_on_disk (f g : ℕ → ℤ) (H : ∀ q ∈ Metric.ball (0 : ℂ) 1, ∃ limit : ℂ,
    (HasSum (term f q) limit ∧ HasSum (term g q) limit)) : f = g := by
  have PS_at_f := PS_at_of_pos_convDisk1 (fun q qB ↦ (H q qB).choose_spec.1.summable)
  have PS_at_g : HasFPowerSeriesAt (evalPS f) (coeffs_to_p g) 0 := by
    apply HasFPowerSeriesAt.congr
      (PS_at_of_pos_convDisk1 (fun q qB ↦ (H q qB).choose_spec.2.summable))
    apply Set.EqOn.eventuallyEq_of_mem _ (Metric.ball_mem_nhds 0 (one_pos))
    intro q qB
    obtain ⟨l, f_sum, g_sum⟩ := H q qB
    rw[evalPS, evalPS, f_sum.tsum_eq, g_sum.tsum_eq]
  have := HasFPowerSeriesAt.eq_formalMultilinearSeries PS_at_f PS_at_g
  ext n
  apply_mod_cast ContinuousMultilinearMap.mkPiRing_eq_iff.mp (congrFun this n)

end
