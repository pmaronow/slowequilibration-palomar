-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledOriginalEndpoint

@[expose] public section

/-! True disorder-averaged original spin/REM endpoint. All Gaussian
marginals and products are the actual iid coordinate laws, and their
integrability is proved before the expectation identities. -/

namespace SlowEquilibration.SphericalParisiLabeledOriginalPressure
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledRealization
open SphericalParisiLabeledThreeBlock SphericalParisiLabeledUnheldComparison
open SphericalParisiLabeledOriginalEndpoint SphericalParisiGaussianREM
open GaussianCompactFeatureComparison GaussianSpinInterpolation
open scoped BigOperators RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

def originalLabeledLinear {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 : ℝ)
    (z : UnitSphere N × Fin k) : EuclideanSpace ℝ (OriginalCoordinate N k d) →L[ℝ] ℝ :=
  innerSL ℝ (β • originalFeature d c (theta d c q1-theta d c q0) z)

def originalLabeledPressure {N k : ℕ} [NeZero k] (μ : Measure (UnitSphere N))
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 : ℝ) : ℝ :=
  ∫ G,logPartition (μ.prod (labelLaw k)) (originalLabeledLinear d c β q0 q1) G
    ∂SYK.standardGaussianMeasureOnEuclidean (OriginalCoordinate N k d)

omit [DecidableEq σ] in
theorem actual_original_labeled_log_integrable {N k : ℕ} [NeZero k]
    (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ]
    (d : σ → ℕ) (c : σ → ℝ) {β : ℝ} (hβ : 0 ≤ β) (q0 q1 : ℝ) :
    Integrable (logPartition (μ.prod (labelLaw k)) (originalLabeledLinear d c β q0 q1))
      (SYK.standardGaussianMeasureOnEuclidean (OriginalCoordinate N k d)) := by
  classical
  let γ := SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)
  let δ := SYK.standardGaussianMeasureOnEuclidean (Fin k)
  let F := fun p : EuclideanSpace ℝ (Coordinate N d) × EuclideanSpace ℝ (Fin k) =>
    logPartition μ (spinLinear d c β) p.1+
      remLogAverage N k (β*Real.sqrt (theta d c q1-theta d c q0)) p.2
  have hiF : Integrable F (γ.prod δ) :=
    ((originalSpinLogPartition_integrable μ d c β).comp_fst δ).add
      ((remLogAverage_integrable N k (NeZero.pos k) (mul_nonneg hβ (Real.sqrt_nonneg _))).comp_snd γ)
  have hLaw : HasLaw (sumSplit (ι := Coordinate N d) (κ := Fin k)) (γ.prod δ)
      (SYK.standardGaussianMeasureOnEuclidean (OriginalCoordinate N k d)) :=
    ⟨sumSplit.continuous.measurable.aemeasurable,sumSplit_gaussian_map⟩
  apply (hLaw.integrable_comp hiF).congr
  exact .of_forall fun G => by
    have h := actual_original_log_partition_factorization μ d c β q0 q1 (sumSplit G).1 (sumSplit G).2
    rw [sumJoin_sumSplit] at h
    exact h.symm

omit [DecidableEq σ] in
/-- Actual original expectation equals the real spin pressure plus the
independent true iid Gaussian REM log-average. -/
theorem actual_original_pressure_eq_spin_add_rem {N k : ℕ} [NeZero k]
    (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ]
    (d : σ → ℕ) (c : σ → ℝ) {β : ℝ} (hβ : 0 ≤ β) (q0 q1 : ℝ) :
    originalLabeledPressure (k := k) μ d c β q0 q1=originalSpinPressure μ d c β+
      (∫ y,remLogAverage N k (β*Real.sqrt (theta d c q1-theta d c q0)) y
        ∂SYK.standardGaussianMeasureOnEuclidean (Fin k)) := by
  classical
  let γ := SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)
  let δ := SYK.standardGaussianMeasureOnEuclidean (Fin k)
  let F := fun p : EuclideanSpace ℝ (Coordinate N d) × EuclideanSpace ℝ (Fin k) =>
    logPartition μ (spinLinear d c β) p.1+
      remLogAverage N k (β*Real.sqrt (theta d c q1-theta d c q0)) p.2
  have hs := originalSpinLogPartition_integrable μ d c β
  have hr := remLogAverage_integrable N k (NeZero.pos k)
    (β := β*Real.sqrt (theta d c q1-theta d c q0)) (mul_nonneg hβ (Real.sqrt_nonneg _))
  have hiF : Integrable F (γ.prod δ) := (hs.comp_fst δ).add (hr.comp_snd γ)
  have hLaw : HasLaw (sumSplit (ι := Coordinate N d) (κ := Fin k)) (γ.prod δ)
      (SYK.standardGaussianMeasureOnEuclidean (OriginalCoordinate N k d)) :=
    ⟨sumSplit.continuous.measurable.aemeasurable,sumSplit_gaussian_map⟩
  have H := hLaw.integral_comp hiF.aestronglyMeasurable
  have hEach (G : EuclideanSpace ℝ (OriginalCoordinate N k d)) :
      F (sumSplit G)=logPartition (μ.prod (labelLaw k)) (originalLabeledLinear d c β q0 q1) G := by
    have h := actual_original_log_partition_factorization μ d c β q0 q1 (sumSplit G).1 (sumSplit G).2
    rw [sumJoin_sumSplit] at h
    exact h.symm
  change (∫ G,logPartition (μ.prod (labelLaw k)) (originalLabeledLinear d c β q0 q1) G
    ∂SYK.standardGaussianMeasureOnEuclidean (OriginalCoordinate N k d))=_
  rw [← integral_congr_ae (.of_forall hEach)]
  rw [show (fun G => F (sumSplit G))=F ∘ sumSplit by rfl,H]
  unfold F
  rw [integral_add (hs.comp_fst δ) (hr.comp_snd γ),integral_fun_fst,integral_fun_snd]
  simp only [probReal_univ,one_smul,originalSpinPressure]
  rfl

private theorem join_inner {ι κ : Type*} [Fintype ι] [Fintype κ]
    (u u' : EuclideanSpace ℝ ι) (w w' : EuclideanSpace ℝ κ) :
    inner ℝ (sumJoin (u,w)) (sumJoin (u',w'))=inner ℝ u u'+inner ℝ w w' := by
  simp only [PiLp.inner_apply,Fintype.sum_sum_type]
  rfl

omit [DecidableEq σ] in
theorem actual_base_original_field {N k : ℕ} (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 : ℝ)
    (z : UnitSphere N × Fin k) (D : EuclideanSpace ℝ (BaseCoordinate N k d)) :
    baseLinear d c β q0 q1 0 z D=
      originalLabeledLinear d c β q0 q1 z (projectGaussian Sum.inl D) := by
  unfold baseLinear baseFeature originalLabeledLinear
  simp only [Real.cos_zero,Real.sin_zero,mul_one,mul_zero,zero_smul]
  rw [innerSL_apply_apply,innerSL_apply_apply,← sumJoin_sumSplit D,join_inner,inner_zero_left,add_zero]
  rfl

omit [DecidableEq σ] in
/-- Exact identification of the unheld zero-rotation endpoint with the
original tensor-plus-scalar-label Gaussian bank. -/
theorem actual_unheld_original_pressure {N k : ℕ} [NeZero k]
    (μ : Measure (UnitSphere N)) [IsProbabilityMeasure μ]
    (d : σ → ℕ) (c : σ → ℝ) {β : ℝ} (hβ : 0 ≤ β) (q0 q1 : ℝ) :
    unheldPressure (μ.prod (labelLaw k)) d c β q0 q1 0=originalLabeledPressure (k := k) μ d c β q0 q1 := by
  have hi := actual_original_labeled_log_integrable (k := k) μ d c hβ q0 q1
  have H := (projectGaussian_hasLaw
    (Sum.inl : OriginalCoordinate N k d → BaseCoordinate N k d) Sum.inl_injective).integral_comp hi.aestronglyMeasurable
  have he (D : EuclideanSpace ℝ (BaseCoordinate N k d)) :
      logPartition (μ.prod (labelLaw k)) (baseLinear d c β q0 q1 0) D=
        logPartition (μ.prod (labelLaw k)) (originalLabeledLinear d c β q0 q1) (projectGaussian Sum.inl D) := by
    unfold logPartition
    apply congrArg Real.log
    unfold GaussianSpinInterpolation.moment weight
    apply integral_congr_ae
    exact .of_forall fun z => by
      dsimp only
      rw [actual_base_original_field]
  unfold unheldPressure originalLabeledPressure
  rw [integral_congr_ae (.of_forall he)]
  exact H

end
end SlowEquilibration.SphericalParisiLabeledOriginalPressure
