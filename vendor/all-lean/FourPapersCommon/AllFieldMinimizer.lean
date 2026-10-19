module
public import FourPapersCommon.AllFieldMoments
public import FRSB.ParisiStrictnessBridge
public import FRSB.ParisiMinimizerGeometry

@[expose] public section

/-! Strict convexity and uniqueness for the actual Parisi minimizer at every
deterministic initial field. All second-moment inputs are proved for that field. -/
noncomputable section
open Set MeasureTheory Paper
namespace FourPapersCommon

theorem measure_eq_of_mix_equality_allFields (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : Paper.ParisiMeasure) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (he : parisiPDEFunctional β h (parisiMix μ ν t) =
      (1-t)*parisiPDEFunctional β h μ+t*parisiPDEFunctional β h ν) : μ = ν := by
  let ρ := parisiMix μ ν t
  apply FRSB.measure_eq_of_mix_equality_of_momentDerivative β h hβ μ ν t ht
    (fun s => β^2*fieldCurvatureMoment2 β h hβ ρ s)
  · intro s hs
    exact hasDerivAt_Gamma β h hβ ρ hs
  · intro s hs
    have hp := fieldCurvatureMoment2_pos β h hβ ρ ⟨hs.1.le,hs.2.le⟩
    rw [norm_mul,Real.norm_of_nonneg (sq_nonneg β),Real.norm_of_nonneg hp.le]
    exact (mul_le_mul_of_nonneg_left (fieldCurvatureMoment2_le_one β h hβ ρ s)
      (sq_nonneg β)).trans_eq (mul_one _)
  · intro s hs
    exact (mul_pos (sq_pos_of_ne_zero hβ)
      (fieldCurvatureMoment2_pos β h hβ ρ ⟨hs.1.le,hs.2.le⟩)).ne'
  · exact he

theorem parisiFunctional_mix_lt_allFields (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : Paper.ParisiMeasure) (hne : μ ≠ ν) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    parisiPDEFunctional β h (parisiMix μ ν t) <
      (1-t)*parisiPDEFunctional β h μ+t*parisiPDEFunctional β h ν := by
  have hle := parisiPDEFunctional_mix_le β h μ ν t ⟨ht.1.le,ht.2.le⟩
  by_contra hnot
  exact hne (measure_eq_of_mix_equality_allFields β h hβ μ ν t ht
    (le_antisymm hle (not_lt.mp hnot)))

theorem parisiPotential_initial_mix_lt_allFields (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : Paper.ParisiMeasure) (hne : μ ≠ ν) (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) :
    parisiPotential β (parisiMix μ ν t) (0,h) <
      (1-t)*parisiPotential β μ (0,h)+t*parisiPotential β ν (0,h) := by
  have hh := parisiFunctional_mix_lt_allFields β h hβ μ ν hne t ht
  unfold parisiPDEFunctional parisiFunctional at hh
  rw [parisiCorrection_integral_mix μ ν t ⟨ht.1.le,ht.2.le⟩] at hh
  nlinarith

theorem minimizer_eq_allFields (β h : ℝ) (hβ : β ≠ 0)
    (μ ν : Paper.ParisiMeasure) (hμ : FRSB.IsParisiMinimizer β h μ)
    (hν : FRSB.IsParisiMinimizer β h ν) : μ = ν := by
  by_contra hne
  have hs := parisiFunctional_mix_lt_allFields β h hβ μ ν hne (1/2) (by norm_num)
  rw [FRSB.IsParisiMinimizer.mix_value hμ hν (1/2) (by norm_num)] at hs
  exact (lt_irrefl _) hs

theorem parisiMinimizer_unique_allFields (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (hμ : FRSB.IsParisiMinimizer β h μ) :
    μ = FRSB.parisiMinimizer β h :=
  minimizer_eq_allFields β h hβ μ _ hμ (FRSB.isParisiMinimizer_selected β h)

theorem existsUnique_parisi_minimizer_allFields (β h : ℝ) (hβ : β ≠ 0) :
    ∃! μ : Paper.ParisiMeasure, FRSB.IsParisiMinimizer β h μ := by
  exact ⟨FRSB.parisiMinimizer β h,FRSB.isParisiMinimizer_selected β h,
    fun μ hμ => parisiMinimizer_unique_allFields β h hβ μ hμ⟩

end FourPapersCommon
