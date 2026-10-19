-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalWeightedReplicaMeasurability
public import SlowEquilibration.SphericalLikelihoodContiguity
public import SlowEquilibration.SphericalGoodReference
public import SlowEquilibration.VaryingProbability

@[expose] public section

/-! # Literal source plateau-norm transfer

The genuine planted norm-error expectation and normalized-partition lower
-tail tightness imply source prop:pl-norm under the actual disorder. Both
remaining thermodynamic obligations are explicit primitive inputs.
-/
namespace SlowEquilibration.SphericalWeightedReplicaPlateau
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalBarycenter VaryingProbability
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {N : ℕ}

def sourceNormError (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (z : Disorder N μ.maxDegree × Vector N) : ℝ :=
  (‖sourceObservable β (fieldOfMixture μ z.1) J δ q₁ q₂ z.2‖^2-q)^2

theorem sourceNormError_measurable (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ) :
    Measurable (sourceNormError (N := N) μ β J δ q₁ q₂ q) :=
  (((sourceObservable_joint_measurable μ β J δ q₁ q₂).norm.pow_const 2).sub_const q).pow_const 2

theorem sourceNormError_nonnegative (μ : FiniteMixture) (β J δ q₁ q₂ q : ℝ)
    (z : Disorder N μ.maxDegree × Vector N) : 0 ≤ sourceNormError μ β J δ q₁ q₂ q z :=
  sq_nonneg _

theorem sourceNormError_le_one (hN : 1 ≤ N) (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ)
    {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) (z : Disorder N μ.maxDegree × Vector N) :
    sourceNormError μ β J δ q₁ q₂ q z ≤ 1 := by
  have hB := sourceObservable_norm_le_one hN β (fieldOfMixture_contDiff μ z.1).continuous
    J δ q₁ q₂ z.2
  have hs : ‖sourceObservable β (fieldOfMixture μ z.1) J δ q₁ q₂ z.2‖^2 ≤ 1 := by
    nlinarith [norm_nonneg (sourceObservable β (fieldOfMixture μ z.1) J δ q₁ q₂ z.2)]
  have hdiff : |‖sourceObservable β (fieldOfMixture μ z.1) J δ q₁ q₂ z.2‖^2-q| ≤ 1 := by
    exact abs_le.mpr ⟨by linarith [hq.2,sq_nonneg ‖sourceObservable β (fieldOfMixture μ z.1) J δ q₁ q₂ z.2‖],by linarith [hq.1]⟩
  have hsq := (sq_le_sq₀ (abs_nonneg _) zero_le_one).mpr hdiff
  rw [sq_abs,one_pow] at hsq
  exact hsq

/-- The actual source integrated norm error is bounded by a tolerance plus
the genuine quenched Gibbs bad-reference mass. -/
theorem sourceNormFluctuation_le_badMass (hN : 1 ≤ N) (μ : FiniteMixture)
    (β J δ q₁ q₂ : ℝ) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1) {ε : ℝ} (hε : 0 < ε)
    (D : Disorder N μ.maxDegree) :
    sourceNormFluctuation μ β J δ q₁ q₂ q D ≤ ε+
      referenceBadMass (mixtureCoefficients μ) β
        {z | ε ≤ sourceNormError μ β J δ q₁ q₂ q z} D := by
  let π := mixtureGibbsLaw μ β D
  let _ : IsProbabilityMeasure π := by
    change IsProbabilityMeasure (gibbsLaw N β (fieldOfMixture μ D))
    exact gibbsLaw_probability hN β (fieldOfMixture_contDiff μ D).continuous
  let E : Set (Vector N) := {x | ε ≤ sourceNormError μ β J δ q₁ q₂ q (D,x)}
  have hE : MeasurableSet E := measurableSet_le measurable_const
    ((sourceNormError_measurable μ β J δ q₁ q₂ q).comp (measurable_const.prodMk measurable_id))
  have hφ : Integrable (fun x => sourceNormError μ β J δ q₁ q₂ q (D,x)) π :=
    Integrable.of_bound ((sourceNormError_measurable μ β J δ q₁ q₂ q).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable 1 (.of_forall fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sourceNormError_nonnegative _ _ _ _ _ _ _ _)]
        exact sourceNormError_le_one hN μ β J δ q₁ q₂ hq (D,x))
  have hI : Integrable (E.indicator (fun _ => (1:ℝ))) π := (integrable_const 1).indicator hE
  have hb := integral_mono_ae hφ ((integrable_const ε).add hI) (.of_forall fun x => by
    change sourceNormError μ β J δ q₁ q₂ q (D,x) ≤ ε+E.indicator (fun _ => (1:ℝ)) x
    by_cases hx : x ∈ E
    · rw [Set.indicator_of_mem hx]
      exact (sourceNormError_le_one hN μ β J δ q₁ q₂ hq (D,x)).trans (by linarith)
    · rw [Set.indicator_of_notMem hx,add_zero]
      exact (not_le.mp hx).le)
  simp only [Pi.add_apply] at hb
  rw [integral_add (integrable_const ε) hI,integral_const,probReal_univ,one_smul,
    integral_indicator hE,setIntegral_const,smul_eq_mul,mul_one] at hb
  exact hb

/-- Complete actual source prop:pl-norm transfer from its two primitive
stochastic inputs. The planted transverse-moment proof and the HMP
lower-tail theorem are not replaced by conclusions about the slow spin. -/
theorem sourceNormFluctuation_inProbability_of_planted
    (μ : FiniteMixture) (β J δ q₁ q₂ : ℝ) {q : ℝ} (hq : q ∈ Icc (0:ℝ) 1)
    (hTight : LikelihoodLowerTailTight μ β)
    (hPlanted : Tendsto (fun N => ∫ z : Disorder N μ.maxDegree × Vector N,
      sourceNormError μ β J δ q₁ q₂ q z ∂plantedLaw (mixtureCoefficients μ) β)
      atTop (𝓝 (0:ℝ))) :
    InProbability (fun N => disorderLaw N μ.maxDegree)
      (fun N => sourceNormFluctuation (N := N) μ β J δ q₁ q₂ q) 0 := by
  intro θ hθ
  let E := fun N => {z : Disorder N μ.maxDegree × Vector N |
    θ/2 ≤ sourceNormError μ β J δ q₁ q₂ q z}
  have hE : ∀ N, MeasurableSet (E N) := fun N =>
    measurableSet_le measurable_const (sourceNormError_measurable μ β J δ q₁ q₂ q)
  have hP : Tendsto (fun N => (plantedLaw (mixtureCoefficients μ) β).real (E N))
      atTop (𝓝 (0:ℝ)) := by
    have hBound : ∀ᶠ N : ℕ in atTop,
        (plantedLaw (mixtureCoefficients μ) β).real (E N) ≤
          (∫ z : Disorder N μ.maxDegree × Vector N, sourceNormError μ β J δ q₁ q₂ q z
            ∂plantedLaw (mixtureCoefficients μ) β)/(θ/2) := by
      filter_upwards [eventually_ge_atTop 1] with N hN
      let _ := plantedLaw_probability hN (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ) β
      have hi : Integrable (sourceNormError (N := N) μ β J δ q₁ q₂ q)
          (plantedLaw (mixtureCoefficients μ) β) :=
        Integrable.of_bound (sourceNormError_measurable μ β J δ q₁ q₂ q).aestronglyMeasurable 1
          (.of_forall fun z => by
            rw [Real.norm_eq_abs,abs_of_nonneg (sourceNormError_nonnegative _ _ _ _ _ _ _ _)]
            exact sourceNormError_le_one hN μ β J δ q₁ q₂ hq z)
      have hb := mul_meas_ge_le_integral_of_nonneg (μ := plantedLaw (mixtureCoefficients μ) β)
        (.of_forall (sourceNormError_nonnegative μ β J δ q₁ q₂ q)) hi (θ/2)
      change θ/2*(plantedLaw (mixtureCoefficients μ) β).real (E N) ≤ _ at hb
      exact (le_div_iff₀' (half_pos hθ)).mpr hb
    exact squeeze_zero' (.of_forall fun _ => measureReal_nonneg) hBound
      (by simpa only [zero_div] using hPlanted.div_const (θ/2))
  have hQ := gibbsReference_event_tendsto_of_planted μ β E hE hTight hP
  have hBound : ∀ᶠ N : ℕ in atTop,
      (disorderLaw N μ.maxDegree).real {D | θ ≤ ‖sourceNormFluctuation μ β J δ q₁ q₂ q D-0‖} ≤
        (gibbsReferenceLaw (mixtureCoefficients μ) β).real (E N)/(θ/2) := by
    filter_upwards [eventually_ge_atTop 1] with N hN
    have hi := referenceBadMass_integrable hN (mixtureCoefficients μ) β (hE N)
    have hm := mul_meas_ge_le_integral_of_nonneg (μ := disorderLaw N μ.maxDegree)
      (.of_forall fun _ => measureReal_nonneg) hi (θ/2)
    change θ/2*(disorderLaw N μ.maxDegree).real
      {D | θ/2 ≤ referenceBadMass (mixtureCoefficients μ) β (E N) D} ≤
      ∫ D, referenceBadMass (mixtureCoefficients μ) β (E N) D ∂disorderLaw N μ.maxDegree at hm
    have hsub : {D | θ ≤ ‖sourceNormFluctuation μ β J δ q₁ q₂ q D-0‖} ⊆
        {D | θ/2 ≤ referenceBadMass (mixtureCoefficients μ) β (E N) D} := by
      intro D hD
      have hV : 0 ≤ sourceNormFluctuation μ β J δ q₁ q₂ q D := integral_nonneg fun x => sq_nonneg _
      change θ ≤ ‖sourceNormFluctuation μ β J δ q₁ q₂ q D-0‖ at hD
      rw [sub_zero,Real.norm_eq_abs,abs_of_nonneg hV] at hD
      have hb := sourceNormFluctuation_le_badMass hN μ β J δ q₁ q₂ hq (half_pos hθ) D
      change θ/2 ≤ _
      change sourceNormFluctuation μ β J δ q₁ q₂ q D ≤ θ/2+
        referenceBadMass (mixtureCoefficients μ) β (E N) D at hb
      linarith
    have hb := measureReal_mono (μ := disorderLaw N μ.maxDegree) hsub
    rw [← gibbsReference_real_eq_integral_badMass hN (mixtureCoefficients μ) β (hE N)] at hm
    exact hb.trans ((le_div_iff₀' (half_pos hθ)).mpr hm)
  exact squeeze_zero' (.of_forall fun _ => measureReal_nonneg) hBound
    (by simpa only [zero_div] using hQ.div_const (θ/2))

end
end SlowEquilibration.SphericalWeightedReplicaPlateau
