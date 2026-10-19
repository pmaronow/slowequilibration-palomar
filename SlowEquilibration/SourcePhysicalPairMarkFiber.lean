-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourcePhysicalPairDensityIdentity
public import SlowEquilibration.SphericalPureMarkedWindows

/-! Literal physical score and value marks on the actual full-disorder
pair posterior. This retains the field-dependent window predicates used
by ordered critical-pair counts. -/
@[expose] public section
namespace SlowEquilibration.PairConditionalDeterminantMoments
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalGaussianJet WholeFieldRegression NormalizedPairObservations
open GaussianRegression GaussianObservationCoercivity IntrinsicHessianLaw PairObservationTargets
open SphericalPairMarkedWindows SphericalMarkedWindows PairObservationSmallOverlap
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000

lemma actualScore_eq_sqrtNormalized {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) (x:Vector N) :
    actualScore c J x=(Real.sqrt (N:ℝ))⁻¹ • normalizedScore c x (euclideanDisorder J):=by
  unfold actualScore normalizedScore
  rw [smul_apply,smul_smul,←mul_inv,←pow_two,Real.sq_sqrt (Nat.cast_nonneg N)]

lemma actualValue_eq_sqrtNormalized {N P:ℕ} (c:Degree P→ℝ) (J:Disorder N P) (x:Vector N) :
    actualValue c J x=(Real.sqrt (N:ℝ))⁻¹*normalizedValue c x (euclideanDisorder J):=by
  unfold actualValue normalizedValue
  rw [smul_apply,smul_eq_mul,←mul_assoc,←mul_inv,←pow_two,Real.sq_sqrt (Nat.cast_nonneg N)]
  simp only [SphericalSequentialRegression.valueCLM,flatJetCLM_apply,unpack_euclideanDisorder,jet,iteratedFDeriv_zero_apply,div_eq_mul_inv,mul_comm]

theorem source_mixed_physical_pair_marks_ae (μ:FiniteMixture) {Q:ℝ}
    (hQ:0<Q) (hnp:μ.minDegree<μ.maxDegree) (hd:4 ≤ μ.minDegree) :
    ∃ η:ℝ,0<η ∧ ∀ n:ℕ,∀ (x y:Vector (n+3))
      (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)), |overlap x y| ≤ η →
      ∀ b:ScorePairSpace,
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      ∀ᵐ J ∂pairMixedConditionedLaw c x y hx hy b,
        actualScore c J x=b.fst ∧ actualScore c J y=b.snd:=by
  obtain ⟨η,hη,hall⟩:=uniform_intrinsic_physical_mixed_disintegration μ hQ hnp hd
  refine ⟨η,hη,?_⟩
  intro n x y hx hy hr b
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hA:Surjective (groupedMixedPair c x y (tangentFrame x hx) (tangentFrame y hy)):=
    (hall (n+2) x y hx hy hr).1
  have hf:=coefficientKernel_observation_ae _ hA (WithLp.toLp 2 (Real.sqrt (n+3:ℕ) • b,0))
  change ∀ᵐ J ∂coefficientKernel (groupedMixedPair c x y (tangentFrame x hx) (tangentFrame y hy))
    (WithLp.toLp 2 (Real.sqrt (n+3:ℕ) • b,0)), _
  filter_upwards [hf] with J hJ
  have hxscore:normalizedScore c x (euclideanDisorder J)=Real.sqrt (n+3:ℕ) • b.fst:=
    congrArg (fun w:GroupedMixedPairSpace (n+2)=>w.fst.fst) hJ
  have hyscore:normalizedScore c y (euclideanDisorder J)=Real.sqrt (n+3:ℕ) • b.snd:=
    congrArg (fun w:GroupedMixedPairSpace (n+2)=>w.fst.snd) hJ
  constructor
  · rw [actualScore_eq_sqrtNormalized,hxscore,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]
  · rw [actualScore_eq_sqrtNormalized,hyscore,smul_smul,inv_mul_cancel₀ (by positivity),one_smul]

theorem source_value_physical_pair_marks_ae (μ:FiniteMixture) {Q:ℝ}
    (hQ:0<Q) (hd:4 ≤ μ.minDegree) :
    ∃ η:ℝ,0<η ∧ ∀ n:ℕ,∀ (x y:Vector (n+3))
      (hx:‖x‖^2=(n+3:ℕ)) (hy:‖y‖^2=(n+3:ℕ)), |overlap x y| ≤ η →
      ∀ b:ValuePairSpace,
      let c:=centerCoefficients (mixtureCoefficients μ) Q
      ∀ᵐ J ∂pairValueConditionedLaw c x y hx hy b,
        actualValue c J x=b.fst ∧ actualValue c J y=b.snd:=by
  obtain ⟨η,hη,hall⟩:=uniform_intrinsic_physical_value_disintegration μ hQ hd
  refine ⟨η,hη,?_⟩
  intro n x y hx hy hr b
  dsimp only
  let c:=centerCoefficients (mixtureCoefficients μ) Q
  have hA:Surjective (groupedValuePair c x y (tangentFrame x hx) (tangentFrame y hy)):=
    (hall (n+2) x y hx hy hr).1
  have hf:=coefficientKernel_observation_ae _ hA (WithLp.toLp 2 (Real.sqrt (n+3:ℕ) • b,0))
  change ∀ᵐ J ∂coefficientKernel (groupedValuePair c x y (tangentFrame x hx) (tangentFrame y hy))
    (WithLp.toLp 2 (Real.sqrt (n+3:ℕ) • b,0)), _
  filter_upwards [hf] with J hJ
  have hxvalue:normalizedValue c x (euclideanDisorder J)=Real.sqrt (n+3:ℕ)*b.fst:=
    congrArg (fun w:GroupedValuePairSpace (n+2)=>w.fst.fst) hJ
  have hyvalue:normalizedValue c y (euclideanDisorder J)=Real.sqrt (n+3:ℕ)*b.snd:=
    congrArg (fun w:GroupedValuePairSpace (n+2)=>w.fst.snd) hJ
  constructor
  · rw [actualValue_eq_sqrtNormalized,hxvalue,←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]
  · rw [actualValue_eq_sqrtNormalized,hyvalue,←mul_assoc,inv_mul_cancel₀ (by positivity),one_mul]

end
end SlowEquilibration.PairConditionalDeterminantMoments
