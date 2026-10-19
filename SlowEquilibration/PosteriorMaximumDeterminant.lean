-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalNegativeHessianMark
public import SlowEquilibration.SphericalCountIntensity

/-! Exact negative-Hessian determinant means under the genuine whole-field
posteriors, obtained from the complete conditioned matrix law. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalForm SphereHessian
open SphericalPosteriorMaps NegativeDefiniteOperators GOEMaximumDeterminant
open WholeFieldRegression IntrinsicHessianLaw ConditionedIntrinsicHessian PureConditionedHessian
open ConditionedDeterminantMoments UnrestrictedConditionedDeterminants
open SphericalSequentialRegression GOERawMoments GOEAsymptotics OAI.CriticalSK
open scoped ENNReal
noncomputable section
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma goe_symmetric_ae (m N : ℕ) (b : ℝ) :
    ∀ᵐ W ∂goeLaw m N b, ∀ i j, W i j = W j i := by
  have hm : MeasurableSet {W : Matrix (Fin m) (Fin m) ℝ | ∀ i j, W i j = W j i} := by
    simp only [ofPred_forall]
    apply MeasurableSet.iInter
    intro i
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_eq_fun ((measurable_pi_apply j).comp (measurable_pi_apply i))
      ((measurable_pi_apply i).comp (measurable_pi_apply j))
  apply (ae_map_iff (symmetricMatrix_measurable m).aemeasurable hm).mpr
  apply Filter.Eventually.of_forall
  intro a i j
  by_cases hij : i ≤ j
  · by_cases hji : j ≤ i
    · have : i = j := le_antisymm hij hji
      subst j
      rfl
    · simp [symmetricMatrix, hij, hji]
  · have hji : j ≤ i := le_of_lt (lt_of_not_ge hij)
    simp [symmetricMatrix, hij, hji]

def negativeMatrixWeight (m : ℕ) (W : Matrix (Fin m) (Fin m) ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal |W.det| * if NegativeDefinite (gaussianMatrixCLM (matrixToGaussian W)) then 1 else 0

lemma negativeMatrixWeight_measurable (m : ℕ) : Measurable (negativeMatrixWeight m) := by
  exact (continuous_id.matrix_det.abs.measurable.ennreal_ofReal).mul
    (Measurable.ite ((isOpen_negativeDefinite (E := EuclideanSpace ℝ (Fin m))).measurableSet.preimage
      (matrixOperator_measurable m)) measurable_const measurable_const)

lemma negative_matrix_mean_of_law {Ω : Type*} [MeasurableSpace Ω] {ν : Measure Ω}
    (n : ℕ) (b k : ℝ) (H : Ω → Matrix (Fin (n+1)) (Fin (n+1)) ℝ)
    (hH : HasLaw H ((goeLaw (n+1) (n+2) b).map (fun W => W-k • 1)) ν) :
    (∫⁻ ω, negativeMatrixWeight (n+1) (H ω) ∂ν) =
      ENNReal.ofReal (maximumMean n (n+2) b k) := by
  have hs : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ => W-k • 1) := by fun_prop
  rw [hH.lintegral_comp (negativeMatrixWeight_measurable (n+1)).aemeasurable,
    lintegral_map (negativeMatrixWeight_measurable (n+1)) hs]
  have he : (fun W => negativeMatrixWeight (n+1) (W-k • 1)) =ᵐ[goeLaw (n+1) (n+2) b]
      ((maximumEvent n k).indicator (fun W => ENNReal.ofReal (matrixAbsoluteDet n k W))) := by
    filter_upwards [goe_symmetric_ae (n+1) (n+2) b] with W hW
    simp only [negativeMatrixWeight, shifted_abs_det,
      negativeDefinite_shifted_matrix_iff W hW k]
    by_cases hk : W ∈ maximumEvent n k <;> simp [hk]
  rw [lintegral_congr_ae he, lintegral_indicator (maximumEvent_measurable n k)]
  have hi : Integrable (matrixAbsoluteDet n k) (goeLaw (n+1) (n+2) b) := by
    simpa only [shifted_abs_det] using (fixed_shifted_determinant_integrable (n+1) (n+2) b k).abs
  exact (ofReal_integral_eq_lintegral_ofReal hi.integrableOn
    (Filter.Eventually.of_forall (fun W => abs_nonneg ((k • 1-W).det)))).symm

lemma intrinsic_negative_weight_eq {n P : ℕ} (c : Degree P → ℝ)
    (x : Vector (n+1)) (hx : ‖x‖^2=(n+1 : ℕ)) (J : Disorder (n+1) P)
    (hc : surfaceGradient (field c J) x = 0) :
    ENNReal.ofReal |(intrinsicHessian (field c J) x).det| * negativeHessianMark n c J x =
      negativeMatrixWeight n (intrinsicMatrix c x hx J) := by
  rw [negativeHessianMark_eq n c J x hx hc]
  simp only [negativeMatrixWeight, intrinsicMatrix, LinearMap.det_toMatrix,
    negativeDefinite_toMatrix_iff]

lemma mixed_posterior_negative_det_mean (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (x : Vector (n+2)) (hx : ‖x‖^2=(n+2 : ℕ)) (z : EuclideanSpace ℝ (Fin 2)) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| *
      negativeHessianMark (n+1) c J x ∂mixedConditionedLaw c x hx z) =
      ENNReal.ofReal (maximumMean n (n+2) (Q^2 * μ.xi2 Q) (z 1)) := by
  dsimp only
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hk : jointScoreTarget (n+1) (((n+2 : ℕ):ℝ) • z) (Sum.inl 1) / (n+2 : ℕ) = z 1 := by
    change (((n+2 : ℕ):ℝ) * z 1) / (n+2 : ℕ) = _
    field_simp
  have hH := conditioned_intrinsicMatrix_hasLaw μ hQ hnp x hx
    (jointScoreTarget (n+1) (((n+2 : ℕ):ℝ) • z))
  simp only [hk] at hH
  rw [← negative_matrix_mean_of_law n _ _ _ hH]
  apply lintegral_congr_ae
  filter_upwards [conditioned_critical_ae μ hQ hnp x hx
    (jointScoreTarget (n+1) (((n+2 : ℕ):ℝ) • z)) (fun _ => rfl)] with J hJ
  exact intrinsic_negative_weight_eq c x hx J hJ

lemma pure_posterior_negative_det_mean (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (x : Vector (n+2)) (hx : ‖x‖^2=(n+2 : ℕ)) (h : ℝ) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, ENNReal.ofReal |(intrinsicHessian (field c J) x).det| *
      negativeHessianMark (n+1) c J x ∂valueConditionedLaw c x hx h) =
      ENNReal.ofReal (maximumMean n (n+2) (Q^2 * μ.xi2 Q) ((p:ℝ)*h)) := by
  dsimp only
  let μ := FiniteMixture.pure p hp alpha halpha
  let c := centerCoefficients (mixtureCoefficients μ) Q
  rw [← negative_matrix_mean_of_law n _ _ _ (pure_hessian_at_normalized_value p hp alpha halpha hQ x hx h)]
  apply lintegral_congr_ae
  filter_upwards [valueTangent_conditioned_critical_ae μ hQ x hx h] with J hJ
  exact intrinsic_negative_weight_eq c x hx J hJ

end
end SlowEquilibration.SphericalMarkedWindows
