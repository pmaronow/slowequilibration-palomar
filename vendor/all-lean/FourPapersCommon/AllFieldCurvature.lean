module
public import FRSB.OptimalCurvatureMoment

@[expose] public section

/-! Genuine curvature moments along the optimal diffusion at every field. -/
noncomputable section
open Set MeasureTheory ProbabilityTheory Paper
namespace FourPapersCommon
open FRSB

def fieldCurvatureMoment2 (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure) (s : ℝ) : ℝ :=
  ∫ ω, parisiHessian β μ (s, selectedParisiItoState β h hβ μ s.toNNReal ω)^2
    ∂canonicalBrownianMeasure

theorem integrable_fieldCurvature_square (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (s : ℝ) :
    Integrable (fun ω => parisiHessian β μ
      (s, selectedParisiItoState β h hβ μ s.toNNReal ω)^2) canonicalBrownianMeasure := by
  have hX : Measurable (selectedParisiItoState β h hβ μ s.toNNReal) :=
    ((boundedDriftItoCharacteristics_selectedParisiState β h hβ μ).adapted_state s.toNNReal).measurable
      |>.mono (canonicalBrownianFiltration.le s.toNNReal) le_rfl
  apply (integrable_const (1 : ℝ)).mono'
    (((continuous_parisiHessian_all β μ).measurable.comp
      (measurable_const.prodMk hX)).pow_const 2).aestronglyMeasurable
  exact .of_forall fun ω => by
    rw [norm_pow]
    exact pow_le_one₀ (norm_nonneg _) (norm_parisiHessian_le_one_all β μ _)

theorem fieldCurvatureMoment2_pos (β h : ℝ) (hβ : β ≠ 0) (μ : Paper.ParisiMeasure)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) : 0 < fieldCurvatureMoment2 β h hβ μ s := by
  unfold fieldCurvatureMoment2
  apply (integral_pos_iff_support_of_nonneg (fun _ => sq_nonneg _)
    (integrable_fieldCurvature_square β h hβ μ s)).mpr
  have he : Function.support (fun ω => parisiHessian β μ
      (s, selectedParisiItoState β h hβ μ s.toNNReal ω)^2) = univ := by
    ext ω
    simp only [Function.mem_support, mem_univ, iff_true]
    exact (sq_pos_of_pos (parisiHessian_pos_all β μ s _ hs)).ne'
  rw [he]
  simp

theorem fieldCurvatureMoment2_le_one (β h : ℝ) (hβ : β ≠ 0)
    (μ : Paper.ParisiMeasure) (s : ℝ) : fieldCurvatureMoment2 β h hβ μ s ≤ 1 := by
  have hh := integral_mono (integrable_fieldCurvature_square β h hβ μ s)
    (integrable_const (1 : ℝ)) (fun ω => by
      have hh := norm_parisiHessian_le_one_all β μ
        (s, selectedParisiItoState β h hβ μ s.toNNReal ω)
      rw [Real.norm_eq_abs, abs_le] at hh
      nlinarith [hh.1, hh.2])
  simpa only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one,
    one_smul, fieldCurvatureMoment2] using hh

end FourPapersCommon
