module
public import Paper.JTFubini
public import FRSB.ParisiMeasureTopology

@[expose] public section

/-! Weak continuity and exact affinity of genuinely weighted CDF corrections. -/
noncomputable section
open Set MeasureTheory
open scoped Topology
namespace FourPapersCommon

def weightedCDFIntegral (w : ℝ → ℝ) (μ : Paper.ParisiMeasure) : ℝ :=
  ∫ s in (0 : ℝ)..1, w s * Paper.parisiCDF μ s

def weightedTail (w : ℝ → ℝ) (q : Paper.Overlap) : ℝ := ∫ s in (q : ℝ)..1, w s

theorem continuous_weightedTail (w : ℝ → ℝ) (hw : ContinuousOn w (Icc (0 : ℝ) 1)) :
    Continuous (weightedTail w) := by
  have hi : IntegrableOn w (uIcc (0 : ℝ) 1) volume := by
    rw [uIcc_of_le zero_le_one]
    exact hw.integrableOn_compact isCompact_Icc
  have hc : ContinuousOn (fun q : ℝ => ∫ s in q..1, w s) (Icc (0 : ℝ) 1) := by
    simpa only [uIcc_of_le zero_le_one] using
      intervalIntegral.continuousOn_primitive_interval_left hi
  exact hc.comp_continuous continuous_subtype_val (fun q => q.property)

theorem weightedCDFIntegral_eq_measure_integral (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) 1)) (μ : Paper.ParisiMeasure) :
    weightedCDFIntegral w μ = ∫ q, weightedTail w q ∂(μ : Measure Paper.Overlap) := by
  exact (Paper.parisiCDF_tail_pairing μ w
    ((hw.integrableOn_compact isCompact_Icc).mono_set Ioc_subset_Icc_self)).symm

theorem continuous_weightedCDFIntegral (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) 1)) : Continuous (weightedCDFIntegral w) := by
  have he : weightedCDFIntegral w = fun μ : Paper.ParisiMeasure =>
      ∫ q, weightedTail w q ∂(μ : Measure Paper.Overlap) :=
    funext (weightedCDFIntegral_eq_measure_integral w hw)
  rw [he]
  exact ProbabilityMeasure.continuous_integral_continuousMap
    (⟨weightedTail w,continuous_weightedTail w hw⟩ : C(Paper.Overlap,ℝ))

theorem weightedCDFIntegral_mix (w : ℝ → ℝ)
    (hw : ContinuousOn w (Icc (0 : ℝ) 1)) (μ ν : Paper.ParisiMeasure)
    (t : ℝ) (ht : t ∈ Icc (0 : ℝ) 1) :
    weightedCDFIntegral w (Paper.parisiMix μ ν t) =
      (1-t)*weightedCDFIntegral w μ+t*weightedCDFIntegral w ν := by
  simp only [weightedCDFIntegral_eq_measure_integral w hw]
  exact Paper.integral_parisiMix (continuous_weightedTail w hw) μ ν t ht

end FourPapersCommon
