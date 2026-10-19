module
public import FRSB.ParisiControlCovariance
public import FRSB.MomentKernelClamp
public import FRSB.CDFMeasureExt

@[expose] public section

/-! The strictness assembly with its remaining actual second-moment analytic
input named explicitly. The unconditional theorem will instantiate this input
with the genuine Gamma evolution, rather than assuming measure strictness. -/
noncomputable section
open Set MeasureTheory Filter
open scoped Topology NNReal
namespace FRSB
open Paper

/-- Equality in a measure mixture determines the measure once the optimal
second moment's nondegenerate actual derivative is supplied. -/
theorem measure_eq_of_mix_equality_of_momentDerivative
    (β h : ℝ) (hβ : β ≠ 0) (μ ν : ParisiMeasure) (t : ℝ)
    (ht : t ∈ Ioo (0 : ℝ) 1) (d : ℝ → ℝ)
    (hd : ∀ s ∈ Ioo (0 : ℝ) 1,
      HasDerivAt (selectedParisiSecondMoment β h hβ (parisiMix μ ν t)) (d s) s)
    (hbound : ∀ s ∈ Ioo (0 : ℝ) 1, ‖d s‖ ≤ β ^ 2)
    (hpos : ∀ s ∈ Ioo (0 : ℝ) 1, d s ≠ 0)
    (he : parisiPDEFunctional β h (parisiMix μ ν t) =
      (1-t) * parisiPDEFunctional β h μ + t * parisiPDEFunctional β h ν) : μ = ν := by
  have hDrift := parisiPDEFunctional_mix_eq_imp_drift_ae_eq β h hβ μ ν t ht he
  rw [selectedParisiControl_eq_feedback] at hDrift
  have hkernel := selectedParisi_cdfKernel_zero_of_drift_ae_eq β h hβ (parisiMix μ ν t) μ ν hDrift
  apply eq_of_parisiCDF_tail_integrals_eq_zero μ ν
  apply tailIntegral_eq_zero_of_unitMomentKernel_zero
    (fun s => parisiCDF μ s - parisiCDF ν s)
    (selectedParisiSecondMoment β h hβ (parisiMix μ ν t)) d
    ((parisiCDF_measurable μ).sub (parisiCDF_measurable ν))
    (norm_parisiCDF_sub_le_one μ ν) (β ^ 2).toNNReal
    (continuousOn_selectedParisiSecondMoment β h hβ (parisiMix μ ν t)) hd
  · intro s hs
    simpa only [Real.coe_toNNReal _ (sq_nonneg β)] using hbound s hs
  · exact hpos
  · intro s hs
    exact hkernel s ⟨hs.1.le, hs.2.le⟩

end FRSB
