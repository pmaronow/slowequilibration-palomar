-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledL2

/-! The original finite mixed field's bounded-killing transition kernel
and actual Gibbs L² contraction. Kernel subinvariance follows from the
literal survival weight and the proved stationarity of the physical SDE. -/
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

def sourceKilledKernel (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (κ : Vector N → ℝ) (hκ : Continuous κ) (t : ℝ≥0) : Kernel (Vector N) (Vector N) :=
  killedKernel
    (cutoffDrift_lipschitz β (mixedGradient μ J) (mixedGradient_contDiff μ J)
      (cutoffRadius N) (cutoffRadius_pos N)).choose_spec
    (CutoffSDE.cutoffNoise_lipschitz N (cutoffRadius N) (cutoffRadius_pos N)).choose_spec κ hκ t

theorem sourceKilledKernel_finite (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (t : ℝ≥0) :
    IsFiniteKernel (sourceKilledKernel μ J β κ hκ t) :=
  killedKernel_finite _ _ κ hκ hκ0 t

theorem sourceKilledKernel_le_original (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (t : ℝ≥0) (x : Vector N) : sourceKilledKernel μ J β κ hκ t x ≤ mixedTransitionKernel μ J β t x :=
  killedLaw_le_original _ _ κ hκ hκ0 t x

theorem sourceKilledKernel_mass_le (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (t : ℝ≥0) (x : Vector N) : sourceKilledKernel μ J β κ hκ t x univ ≤ 1 :=
  (sourceKilledKernel_le_original μ J β κ hκ hκ0 t x univ).trans_eq (by simp)

theorem sourceKilledKernel_add (μ : FiniteMixture) (J : Disorder N μ.maxDegree) (β : ℝ)
    (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (s t : ℝ≥0) (x : Vector N) :
    sourceKilledKernel μ J β κ hκ (s+t) x =
      (sourceKilledKernel μ J β κ hκ t ∘ₖ sourceKilledKernel μ J β κ hκ s) x :=
  killedKernel_add _ _ (mixedCoefficientBounds μ J β) κ hκ hκ0 s t x

/-- True Gibbs subinvariance is derived from physical survival domination
and actual SDE stationarity; it is not an additional killed-law premise. -/
theorem sourceKilledKernel_gibbs_subinvariant (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (t : ℝ≥0) :
    sourceKilledKernel μ J β κ hκ t ∘ₘ mixtureGibbsLaw μ β J ≤ mixtureGibbsLaw μ β J := by
  have he : sourceKilledKernel μ J β κ hκ t ∘ₘ mixtureGibbsLaw μ β J ≤
      mixedTransitionKernel μ J β t ∘ₘ mixtureGibbsLaw μ β J := by
    apply Measure.le_iff.mpr
    intro A hA
    rw [Measure.bind_apply hA (Kernel.aemeasurable _),Measure.bind_apply hA (Kernel.aemeasurable _)]
    exact lintegral_mono (fun x => sourceKilledKernel_le_original μ J β κ hκ hκ0 t x A)
  exact he.trans_eq (mixedTransitionKernel_gibbs_invariant hN μ J β t)

/-- The genuine Hilbert operator of the original physically killed
process. Every norm and quotient-class condition is derived. -/
def sourceKilledOperator (hN : 1 ≤ N) (μ : FiniteMixture) (J : Disorder N μ.maxDegree)
    (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (t : ℝ≥0) : Lp ℝ 2 (mixtureGibbsLaw μ β J) →L[ℝ] Lp ℝ 2 (mixtureGibbsLaw μ β J) := by
  let := mixtureGibbsLaw_probability hN μ β J
  let := sourceKilledKernel_finite μ J β κ hκ hκ0 t
  exact KilledL2.operator (mixtureGibbsLaw μ β J) (sourceKilledKernel μ J β κ hκ t)
    (sourceKilledKernel_mass_le μ J β κ hκ hκ0 t)
    (sourceKilledKernel_gibbs_subinvariant hN μ J β κ hκ hκ0 t)

theorem sourceKilledOperator_norm_le (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (t : ℝ≥0) :
    ‖sourceKilledOperator hN μ J β κ hκ hκ0 t‖ ≤ 1 := by
  let := mixtureGibbsLaw_probability hN μ β J
  let := sourceKilledKernel_finite μ J β κ hκ hκ0 t
  exact KilledL2.operator_norm_le _ _ _ _

theorem sourceKilledOperator_ae (hN : 1 ≤ N) (μ : FiniteMixture)
    (J : Disorder N μ.maxDegree) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (t : ℝ≥0)
    (U : Lp ℝ 2 (mixtureGibbsLaw μ β J)) :
    sourceKilledOperator hN μ J β κ hκ hκ0 t U =ᵐ[mixtureGibbsLaw μ β J]
      fun x => ∫ y, U y ∂sourceKilledKernel μ J β κ hκ t x := by
  let := mixtureGibbsLaw_probability hN μ β J
  let := sourceKilledKernel_finite μ J β κ hκ hκ0 t
  exact KilledL2.operator_ae _ _ _ _ U

end SlowEquilibration.ConditionedEntrance.FeynmanKac
