-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianDensityDilationPointwise
public import SlowEquilibration.PairValuePhysicalDensity
public import SlowEquilibration.PairScorePhysicalDensity
public import SlowEquilibration.SphericalScoreDensity

/-! Pointwise identification of physical one-point factors in pair-density
ratios with the manuscript's existing actual H/N and (H/N,K/N) densities. -/
@[expose] public section
namespace SlowEquilibration.NormalizedPairObservations
noncomputable section
open Function MeasureTheory GaussianRegression SphericalModel SphericalGaussianJet
open WholeFieldRegression NormalizedObservationCoercivity SphericalSequentialRegression
open scoped ENNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 500000

lemma double_sqrt_normalized_value {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    (Real.sqrt (N:ℝ))⁻¹ • normalizedValue c x=(N:ℝ)⁻¹ • valueCLM c x := by
  rw [normalizedValue,smul_smul,← pow_two,inv_pow,Real.sq_sqrt (Nat.cast_nonneg N)]

lemma double_sqrt_normalized_score {N P : ℕ} (c : Degree P → ℝ) (x : Vector N) :
    (Real.sqrt (N:ℝ))⁻¹ • normalizedScore c x=(N:ℝ)⁻¹ • scoreCLM c x := by
  rw [normalizedScore,smul_smul,← pow_two,inv_pow,Real.sq_sqrt (Nat.cast_nonneg N)]

/-- The energy factor used in the proper pair ratio is the literal existing
one-point H/N density at every height, with its genuine sqrt N Jacobian. -/
theorem physicalValueDensity_eq_normalizedValuePdf {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (x : Vector N)
    (hx : ‖x‖^2=(N:ℝ)) (h : ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    physicalValueDensity N (normalizedValue c x) h=(normalizedValuePdf c x h).toReal := by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hRef : Surjective (referenceValue μ Q) :=
    center_value_surjective μ hQ referencePoint (by simpa using referencePoint_norm_sq)
  have hGram : gram (normalizedValue c x)=gram (referenceValue μ Q) :=
    normalizedValue_gram_eq_reference hN μ hQ.le x hx
  have hA : Surjective (normalizedValue c x) :=
    surjective_of_gram_det_ne_zero _ (by rw [hGram];exact (gram_det_pos _ hRef).ne')
  have hPos : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hPhys : Surjective ((N:ℝ)⁻¹ • valueCLM c x) := by
    rw [← double_sqrt_normalized_value]
    exact div_smul_observation_surjective _ hA hPos
  have hDensity:=realObservationDensity_div_smul (normalizedValue c x) hA hPos h
  rw [double_sqrt_normalized_value,Module.finrank_self,pow_one,smul_eq_mul] at hDensity
  rw [normalizedValuePdf,← realObservationDensity_eq_toReal _ hPhys]
  exact hDensity.symm

lemma physicalScoreTarget_eq_smul (N : ℕ) (h k : ℝ) :
    physicalScoreTarget N h k=Real.sqrt (N:ℝ) • (WithLp.toLp 2 ![h,k] : EuclideanSpace ℝ (Fin 2)) := by
  apply PiLp.ext
  intro i
  fin_cases i <;> rfl

/-- The mixed score factor used in the pair ratio is exactly the existing
actual (H/N,K/N) density, pointwise and with its N Jacobian. -/
theorem physicalScoreDensity_eq_normalizedScorePdf {N : ℕ} (hN : 0 < N)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ)) (h k : ℝ) :
    let c:=centerCoefficients (mixtureCoefficients μ) Q
    physicalScoreDensity N (normalizedScore c x) h k=
      (normalizedScorePdf c x (WithLp.toLp 2 ![h,k])).toReal := by
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hRef : Surjective (referenceScore μ Q) :=
    center_score_surjective (by norm_num) μ hQ hnp referencePoint
      (by simpa using referencePoint_norm_sq)
  have hGram : gram (normalizedScore c x)=gram (referenceScore μ Q) :=
    sqrtNormalized_score_gram_eq_reference hN μ hQ.le x hx
  have hA : Surjective (normalizedScore c x) :=
    surjective_of_gram_det_ne_zero _ (by rw [hGram];exact (gram_det_pos _ hRef).ne')
  have hPos : 0 < Real.sqrt (N:ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hPhys : Surjective ((N:ℝ)⁻¹ • scoreCLM c x) := by
    rw [← double_sqrt_normalized_score]
    exact div_smul_observation_surjective _ hA hPos
  have hdim : Module.finrank ℝ (EuclideanSpace ℝ (Fin 2))=2 := by
    norm_num [finrank_euclideanSpace]
  have hDensity:=realObservationDensity_div_smul (normalizedScore c x) hA hPos
    (WithLp.toLp 2 ![h,k])
  rw [double_sqrt_normalized_score,hdim,Real.sq_sqrt (Nat.cast_nonneg N)] at hDensity
  rw [normalizedScorePdf,← realObservationDensity_eq_toReal _ hPhys]
  unfold physicalScoreDensity
  rw [physicalScoreTarget_eq_smul]
  exact hDensity.symm

end
end SlowEquilibration.NormalizedPairObservations
