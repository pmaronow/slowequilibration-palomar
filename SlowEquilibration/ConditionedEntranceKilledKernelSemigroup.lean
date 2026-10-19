-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceKilledKernel

/-! The genuine physical killed kernels satisfy Chapman--Kolmogorov.
This is transferred from the proved literal weighted path expectation,
not assumed as a probabilistic interface. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology StochasticCalculus
open scoped NNReal ENNReal
namespace SlowEquilibration.ConditionedEntrance.FeynmanKac
open SphericalAging HardSphereDynamics SphericalDynamics.FixedCoefficients
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ} {Kb Ks : ℝ≥0}
  {b : Fin N → State N → ℝ} {σ : Fin N → Fin N → State N → ℝ}
  (hb : ∀ i, LipschitzWith Kb (b i)) (hσ : ∀ i j, LipschitzWith Ks (σ i j))

theorem killedKernel_add (B : CoefficientBounds b σ)
    (κ : State N → ℝ) (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x)
    (s t : ℝ≥0) (x : State N) :
    killedKernel hb hσ κ hκ (s+t) x =
      (killedKernel hb hσ κ hκ t ∘ₖ killedKernel hb hσ κ hκ s) x := by
  let := killedKernel_finite hb hσ κ hκ hκ0 s
  let := killedKernel_finite hb hσ κ hκ hκ0 t
  let := killedKernel_finite hb hσ κ hκ hκ0 (s+t)
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  have hfi : Integrable (fun y => f y)
      ((killedKernel hb hσ κ hκ t ∘ₖ killedKernel hb hσ κ hκ s) x) :=
    Integrable.of_bound f.continuous.stronglyMeasurable.aestronglyMeasurable ‖f‖
      (.of_forall (fun y => f.norm_coe_le_norm y))
  calc
    _ = killedTransition hb hσ κ (s+t) f x :=
      killedKernel_integral hb hσ κ hκ (s+t) f f.continuous.stronglyMeasurable x
    _ = killedTransition hb hσ κ s (killedTransition hb hσ κ t f) x :=
      killedTransition_add hb hσ B κ hκ hκ0 s t f f.continuous.stronglyMeasurable
        ‖f‖ (norm_nonneg _) (fun y => f.norm_coe_le_norm y) x
    _ = ∫ z, killedTransition hb hσ κ t f z ∂killedKernel hb hσ κ hκ s x :=
      (killedKernel_integral hb hσ κ hκ s (killedTransition hb hσ κ t f)
        (killedTransition_stronglyMeasurable hb hσ κ hκ t f f.continuous.stronglyMeasurable) x).symm
    _ = ∫ z, ∫ y, f y ∂killedKernel hb hσ κ hκ t z ∂killedKernel hb hσ κ hκ s x := by
      apply integral_congr_ae
      exact .of_forall (fun z => (killedKernel_integral hb hσ κ hκ t f
        f.continuous.stronglyMeasurable z).symm)
    _ = _ := (Kernel.integral_comp hfi).symm

end SlowEquilibration.ConditionedEntrance.FeynmanKac
