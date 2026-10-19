-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledPhysical

/-! The original physical killed kernel acts as a genuine semigroup on
actual Gibbs L² classes, with its actual path-integral representative. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal InnerProductSpace
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalDynamics.FixedCoefficients SphericalReversibility
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

theorem sourceKilledKernel_integral_actual (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (t : ℝ≥0) (f : Vector N → ℝ) (hf : StronglyMeasurable f) (x : Vector N) :
    (∫ y, f y ∂sourceKilledKernel μ J β κ hκ t x) =
      sourceKilledExpectation μ J β κ t f x := by
  rw [sourceKilledExpectation_eq_actual]
  rw [sourceKilledKernel,killedKernel_integral]
  · let X := flow
      (cutoffDrift_lipschitz β (mixedGradient μ J) (mixedGradient_contDiff μ J)
        (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
      (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec x
    have he : ∀ᵐ ω ∂VectorBrownian.law N, ∀ r, X r ω = mixedProcess μ J β x r ω :=
      jointProcess_ae (canonicalDriver N) _ _ x
    apply integral_congr_ae
    filter_upwards [he] with ω hω
    have ho : occupation κ X t ω = occupation κ (mixedProcess μ J β x) t ω := by
      apply intervalIntegral.integral_congr
      intro r _
      exact congrArg κ (hω r.toNNReal)
    change survival κ X t ω * f (X t ω) = _
    simp only [survival,ho,hω t]
  · exact hf

theorem sourceKilledOperator_ae_expectation (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (t : ℝ≥0)
    (U : Lp ℝ 2 (mixtureGibbsLaw μ β J)) (f : Vector N → ℝ) (hf : StronglyMeasurable f)
    (hUf : U =ᵐ[mixtureGibbsLaw μ β J] f) :
    sourceKilledOperator hN μ J β κ hκ hκ0 t U =ᵐ[mixtureGibbsLaw μ β J]
      fun x => sourceKilledExpectation μ J β κ t f x := by
  let := mixtureGibbsLaw_probability hN μ β J
  let := sourceKilledKernel_finite μ J β κ hκ hκ0 t
  have ha := KilledL2.ae_average_congr (mixtureGibbsLaw μ β J) (sourceKilledKernel μ J β κ hκ t)
    (sourceKilledKernel_gibbs_subinvariant hN μ J β κ hκ hκ0 t) hUf
  filter_upwards [sourceKilledOperator_ae hN μ J β κ hκ hκ0 t U,ha] with x hx ha
  exact hx.trans (ha.trans (sourceKilledKernel_integral_actual μ J β κ hκ t f hf x))

theorem sourceKilledOperator_add (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (s t : ℝ≥0) :
    sourceKilledOperator hN μ J β κ hκ hκ0 (s+t) =
      (sourceKilledOperator hN μ J β κ hκ hκ0 s).comp
        (sourceKilledOperator hN μ J β κ hκ hκ0 t) := by
  let π := mixtureGibbsLaw μ β J
  let K := sourceKilledKernel μ J β κ hκ
  let Q := sourceKilledOperator hN μ J β κ hκ hκ0
  let := mixtureGibbsLaw_probability hN μ β J
  let := sourceKilledKernel_finite μ J β κ hκ hκ0 s
  let := sourceKilledKernel_finite μ J β κ hκ hκ0 t
  let := sourceKilledKernel_finite μ J β κ hκ hκ0 (s+t)
  apply ContinuousLinearMap.ext
  intro U
  have hrep := Measure.ae_ae_of_ae_comp
    ((ae_mono (sourceKilledKernel_gibbs_subinvariant hN μ J β κ hκ hκ0 s))
      (sourceKilledOperator_ae hN μ J β κ hκ hκ0 t U))
  have hi : Integrable (U : Vector N → ℝ) (K (s+t) ∘ₘ π) :=
    ((Lp.memLp U).integrable (by norm_num)).mono_measure
      (sourceKilledKernel_gibbs_subinvariant hN μ J β κ hκ hκ0 (s+t))
  have hslice := (Measure.integrable_comp_iff hi.aestronglyMeasurable).mp hi
  apply Lp.ext
  filter_upwards [sourceKilledOperator_ae hN μ J β κ hκ hκ0 (s+t) U,
    sourceKilledOperator_ae hN μ J β κ hκ hκ0 s (Q t U),hrep,hslice.1]
    with x hst hs hr hi
  change Q (s+t) U x = Q s (Q t U) x
  rw [hst,hs]
  calc
    _ = ∫ z, ∫ y, U y ∂K t z ∂K s x := by
      have hc := sourceKilledKernel_add μ J β κ hκ hκ0 s t x
      rw [hc] at hi ⊢
      exact Kernel.integral_comp hi
    _ = _ := by
      have hrf : (Q t U : Vector N → ℝ) =ᵐ[K s x] fun z => ∫ y, U y ∂K t z := hr
      exact integral_congr_ae (EventuallyEq.symm hrf)

end SlowEquilibration.ConditionedEntrance.FeynmanKac
