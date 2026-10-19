-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalCountIntensity

/-! Rectangular value/radial windows and the source's iterated count intensity. -/
@[expose] public section
namespace SlowEquilibration.SphericalMarkedWindows
open MeasureTheory ProbabilityTheory Set Function
open SphericalModel SphericalGaussianJet SphericalSequentialRegression
open GOEPhysicalPotential GOERawMoments
open scoped ENNReal
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000

lemma physicalMean_measurable (n N : ℕ) (b : ℝ) : Measurable (physicalMean n N b) := by
  have h : Continuous (fun p : ℝ × Matrix (Fin (n+1)) (Fin (n+1)) ℝ =>
      matrixAbsoluteDet n p.1 p.2) :=
    ((continuous_fst.smul continuous_const).sub continuous_snd).matrix_det.abs
  exact h.measurable.stronglyMeasurable.integral_prod_right'.measurable

lemma mixedCriticalIntensity_measurable (n : ℕ) (μ : FiniteMixture) (Q : ℝ) :
    Measurable (mixedCriticalIntensity n μ Q) := by
  exact (measurable_const.mul (physicalScorePdf_measurable (n+2) μ Q)).mul
    (((physicalMean_measurable n (n+2) (Q^2 * μ.xi2 Q)).comp
      ((EuclideanSpace.proj (1 : Fin 2)).continuous.measurable)).ennreal_ofReal)

def scorePairEquiv : (ℝ × ℝ) ≃ᵐ EuclideanSpace ℝ (Fin 2) :=
  (MeasurableEquiv.finTwoArrow (α := ℝ)).symm.trans (MeasurableEquiv.toLp 2 (Fin 2 → ℝ))

lemma scorePairEquiv_apply (h k : ℝ) : scorePairEquiv (h,k) = WithLp.toLp 2 ![h,k] := rfl

lemma scorePairEquiv_measurePreserving : MeasurePreserving scorePairEquiv :=
  (PiLp.volume_preserving_toLp (Fin 2)).comp (volume_preserving_piFinTwo (fun _ : Fin 2 => ℝ)).symm

def rectangularScoreWindow (I U : Set ℝ) : Set (EuclideanSpace ℝ (Fin 2)) :=
  {b | b 0 ∈ I ∧ b 1 ∈ U}

lemma rectangularScoreWindow_measurable (I U : Set ℝ) (hI : MeasurableSet I) (hU : MeasurableSet U) :
    MeasurableSet (rectangularScoreWindow I U) :=
  (hI.preimage (EuclideanSpace.proj (0 : Fin 2)).continuous.measurable).inter
    (hU.preimage (EuclideanSpace.proj (1 : Fin 2)).continuous.measurable)

lemma lintegral_rectangularScoreWindow (I U : Set ℝ)
    (f : EuclideanSpace ℝ (Fin 2) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ b in rectangularScoreWindow I U, f b) =
      ∫⁻ h in I, ∫⁻ k in U, f (WithLp.toLp 2 ![h,k]) := by
  rw [← scorePairEquiv_measurePreserving.setLIntegral_comp_preimage_emb
    scorePairEquiv.measurableEmbedding f]
  have he : scorePairEquiv ⁻¹' rectangularScoreWindow I U = I ×ˢ U := by
    ext p
    rfl
  rw [he]
  exact setLIntegral_prod _ (hf.comp scorePairEquiv.measurable).aemeasurable

/-- The actual expected mixed critical count in separate value and radial
windows equals the literal two scalar Lebesgue integrals of the physical intensity. -/
theorem actual_mixed_rectangular_count (n : ℕ) (μ : FiniteMixture) {Q : ℝ}
    (hQ : 0 < Q) (hnp : μ.minDegree < μ.maxDegree)
    (I U : Set ℝ) (hI : MeasurableSet I) (hU : MeasurableSet U) :
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (n+1) c (rectangularScoreWindow I U) (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ h in I, ∫⁻ k in U, mixedCriticalIntensity n μ Q (WithLp.toLp 2 ![h,k]) := by
  dsimp only
  rw [actual_mixed_count_intensity n μ hQ hnp _ (rectangularScoreWindow_measurable I U hI hU)]
  exact lintegral_rectangularScoreWindow I U _ (mixedCriticalIntensity_measurable n μ Q)

/-- The pure value/radial rectangle reduces exactly to `h∈I` and `p*h∈U`. -/
lemma pure_rectangularScoreWindow (p : ℕ) (I U : Set ℝ) :
    pureScoreWindow p (rectangularScoreWindow I U) = {h | h ∈ I ∧ (p:ℝ)*h ∈ U} := rfl

theorem actual_pure_rectangular_count (n : ℕ) (p : ℕ) (hp : 2 ≤ p)
    (alpha : ℝ) (halpha : 0 < alpha) {Q : ℝ} (hQ : 0 < Q)
    (I U : Set ℝ) (hI : MeasurableSet I) (hU : MeasurableSet U) :
    let μ := FiniteMixture.pure p hp alpha halpha
    let c := centerCoefficients (mixtureCoefficients μ) Q
    (∫⁻ J, actualScoreWindowCount (n+1) c (rectangularScoreWindow I U) (fun _ _ => 1) J
      ∂disorderLaw (n+2) μ.maxDegree) =
      ∫⁻ h in {h | h ∈ I ∧ (p:ℝ)*h ∈ U}, pureCriticalIntensity n p hp alpha halpha Q h := by
  exact actual_pure_count_intensity n p hp alpha halpha hQ _
    (rectangularScoreWindow_measurable I U hI hU)

end
end SlowEquilibration.SphericalMarkedWindows
