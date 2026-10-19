module
public import FRSB.GlobalMeasureStability
public import FRSB.ParameterJets
public import FRSB.OperatorMeasureContinuity
public import Paper.ParisiTimeRegularity

@[expose] public section

/-! Measure-uniform bounds and weak-measure continuity of every genuine spatial jet. -/
noncomputable section
open Set Filter MeasureTheory ProbabilityTheory Paper
open scoped Topology BoundedContinuousFunction ContDiff
namespace FRSB

theorem continuous_spatialDerivativeBCF (β : ℝ) (n : ℕ) :
    Continuous (fun μ : ParisiMeasure => bcfSpatialDerivative (parisiGradientBCF β μ) n) := by
  let B := fun μ : ParisiMeasure => parisiSlabBilinearOperator β μ (by norm_num : (0 : ℝ) ≤ 1)
  let H := parisiSlabTerminalHeatOperator β (by norm_num : (0 : ℝ) ≤ 1) parisiLineTanhBCF
  let g := fun t : ℝ => bcfTranslate t H
  let v := fun p : ParisiMeasure × ℝ => bcfTranslate p.2 (parisiGradientBCF β p.1)
  have hB := continuous_parisiSlabBilinearOperator β (by norm_num : (0 : ℝ) ≤ 1)
    (le_refl 0) (le_refl 1)
  have hfix (μ : ParisiMeasure) (t : ℝ) : v (μ, t) = g t + B μ (v (μ, t)) (v (μ, t)) := by
    have h := congrArg (bcfTranslate t) (parisiGradientBCF_quadratic_fixedPoint β μ)
    have hadd : bcfTranslate t (H + B μ (parisiGradientBCF β μ) (parisiGradientBCF β μ)) =
        bcfTranslate t H + bcfTranslate t (B μ (parisiGradientBCF β μ) (parisiGradientBCF β μ)) := by
      ext p
      rfl
    change bcfTranslate t (parisiGradientBCF β μ) = bcfTranslate t
      (H + B μ (parisiGradientBCF β μ) (parisiGradientBCF β μ)) at h
    rw [hadd, parisiSlabBilinearOperator_translate_diagonal] at h
    exact h
  have hinv (μ : ParisiMeasure) : quadraticLinearizationIsInvertible (B μ) (v (μ, 0)) := by
    simpa only [v, bcfTranslate_zero] using
      parisiSlabBilinearOperator_global_residual_isInvertible β μ (parisiGradientBCF β μ)
        (norm_parisiGradientBCF_le_one β μ)
  exact continuous_parameter_line_jets B g v hB (continuous_translated_gradientBCF β)
    (contDiff_bcfTranslate_parisiSlabTerminalTanh β _) hfix hinv n

theorem exists_uniform_spatialDerivativeBCF_bound (β : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ μ : ParisiMeasure,
      ‖bcfSpatialDerivative (parisiGradientBCF β μ) n‖ ≤ K := by
  obtain ⟨K, hK⟩ := (isCompact_univ : IsCompact (univ : Set ParisiMeasure)).exists_bound_of_continuousOn
    (continuous_spatialDerivativeBCF β n).continuousOn
  refine ⟨max K 0 + 1, by positivity, fun μ => ?_⟩
  exact (hK μ (mem_univ μ)).trans (by linarith [le_max_left K 0])

def uniformSpatialConstant (β : ℝ) (n : ℕ) : ℝ :=
  (exists_uniform_spatialDerivativeBCF_bound β n).choose

theorem uniformSpatialConstant_pos (β : ℝ) (n : ℕ) :
    0 < uniformSpatialConstant β n :=
  (exists_uniform_spatialDerivativeBCF_bound β n).choose_spec.1

theorem norm_spatialDerivativeBCF_le_uniform (β : ℝ) (μ : ParisiMeasure) (n : ℕ) :
    ‖bcfSpatialDerivative (parisiGradientBCF β μ) n‖ ≤ uniformSpatialConstant β n :=
  (exists_uniform_spatialDerivativeBCF_bound β n).choose_spec.2 μ

theorem parisiSpatialField_uniform_bound (β : ℝ) (n : ℕ) (μ : ParisiMeasure) (p : ℝ × ℝ) :
    ‖parisiSpatialField β μ (n + 1) p‖ ≤ uniformSpatialConstant β n :=
  (norm_parisiSlabExtend_le (by norm_num : (0 : ℝ) ≤ 1)
    (bcfSpatialDerivative (parisiGradientBCF β μ) n) p).trans
      (norm_spatialDerivativeBCF_le_uniform β μ n)

/-- The paper's positive-order bounds are uniform over every probability measure. -/
theorem positive_order_spatial_derivatives_uniform (β : ℝ) (n : ℕ) :
    ∃ K : ℝ, 0 < K ∧ ∀ (μ : ParisiMeasure) (t : Icc (0 : ℝ) 1) (x : ℝ),
      ‖iteratedDeriv (n + 1) (fun y => parisiPotential β μ (t, y)) x‖ ≤ K := by
  refine ⟨uniformSpatialConstant β n, uniformSpatialConstant_pos β n, fun μ t x => ?_⟩
  rw [← parisiSpatialField_eq_iteratedDeriv β μ (n + 1) t x t.property]
  exact parisiSpatialField_uniform_bound β n μ (t, x)

theorem tendsto_spatialDerivativeBCF_of_weak {A : Type*} {l : Filter A}
    (β : ℝ) (n : ℕ) (μ : ParisiMeasure) (ν : A → ParisiMeasure)
    (hν : Tendsto ν l (𝓝 μ)) :
    Tendsto (fun a => bcfSpatialDerivative (parisiGradientBCF β (ν a)) n) l
      (𝓝 (bcfSpatialDerivative (parisiGradientBCF β μ) n)) :=
  ((continuous_spatialDerivativeBCF β n).continuousAt).tendsto.comp hν

end FRSB
