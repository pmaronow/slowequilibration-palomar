-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceSmoothKilledCoreBounds
public import SlowEquilibration.SphericalC2EssentialSelfAdjoint

/-! The actual smooth source killed Gibbs L² semigroup differentiates on its
true C² core. All pointwise derivatives and dominating slope bounds are
derived from the original diffusion and the literal occupation weight. -/
@[expose] public section
noncomputable section
open Set MeasureTheory ProbabilityTheory Filter Topology
open scoped NNReal ENNReal InnerProductSpace ContDiff
namespace SlowEquilibration.ConditionedEntrance.SmoothKilled
open SphericalAging HardSphereDynamics SphericalModel SphericalDynamics
open SphericalForm SphericalReversibility SphericalReversibility.Ito
open SphericalSmoothTensorStationarity FeynmanKac
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {N : ℕ}

def generatorVector (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ) (hκ : Continuous κ)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) : Lp ℝ 2 (gibbsLaw N β D.hamiltonian) :=
  gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous
    (fun x => coefficientGenerator β (smoothGradient D.hamiltonian D.hamiltonian_contDiff) f x-κ x*f x)
    ((SphericalC1Dynamics.Ito.generator_continuous β _
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) hf).sub (hκ.mul hf.continuous))

/-- The source generator conclusion has no derivative, semigroup,
resolvent, or killing estimate among its hypotheses. -/
theorem operator_C2_hasDerivWithinAt_zero (D : SourceData N) (β : ℝ) (κ : Vector N → ℝ)
    (hκ : Continuous κ) (hκ0 : ∀ x, 0 ≤ κ x) (K : ℝ) (hK0 : 0 ≤ K) (hK : ∀ x, ‖κ x‖ ≤ K)
    (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) :
    HasDerivWithinAt
      (fun r : ℝ => operator D β κ hκ hκ0 r.toNNReal
        (gibbsToL2 D.dimension_ge_one β D.hamiltonian D.hamiltonian_contDiff.continuous f hf.continuous))
      (generatorVector D β κ hκ f hf) (Ici 0) 0 := by
  let := gibbsLaw_probability D.dimension_ge_one β D.hamiltonian_contDiff.continuous
  let H := D.hamiltonian
  let hH := D.hamiltonian_contDiff.continuous
  let L : Vector N → ℝ := fun x => coefficientGenerator β (smoothGradient D.hamiltonian D.hamiltonian_contDiff) f x-κ x*f x
  have hL : Continuous L := (SphericalC1Dynamics.Ito.generator_continuous β _
    (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) hf).sub (hκ.mul hf.continuous)
  obtain ⟨C0,hC0⟩ := (physicalSphere_compact N).exists_bound_of_continuousOn hf.continuous.continuousOn
  obtain ⟨M0,hM0⟩ := (physicalSphere_compact N).exists_bound_of_continuousOn
    (SphericalC1Dynamics.Ito.generator_continuous β _
      (smoothGradient_contDiff D.hamiltonian D.hamiltonian_contDiff) hf).continuousOn
  let C : ℝ := max C0 0
  let M : ℝ := max M0 0
  have hC : ∀ y, OnSphere y → ‖f y‖ ≤ C := fun y hy => (hC0 y hy).trans (le_max_left _ _)
  have hM : ∀ y, OnSphere y → ‖coefficientGenerator β (smoothGradient D.hamiltonian D.hamiltonian_contDiff) f y‖ ≤ M :=
    fun y hy => (hM0 y hy).trans (le_max_left _ _)
  have hLf : ∀ y, OnSphere y → ‖L y‖ ≤ M+K*C := by
    intro y hy
    exact (norm_sub_le _ _).trans (add_le_add (hM y hy)
      ((norm_mul _ _).trans_le (mul_le_mul (hK y) (hC y hy) (norm_nonneg _) hK0)))
  apply lp_derivative_lift _ _ (fun r => expectation D β κ r.toNNReal f) L
    (fun r => (expectation_stronglyMeasurable D β κ hκ hκ0 r.toNNReal f
      hf.continuous.stronglyMeasurable).aestronglyMeasurable) hL.aestronglyMeasurable
    (fun r => operator_ae_expectation D β κ hκ hκ0 r.toNNReal
      (gibbsToL2 D.dimension_ge_one β H hH f hf.continuous) f hf.continuous.stronglyMeasurable
      (gibbsToL2_coe D.dimension_ge_one β H hH f hf.continuous))
    (gibbsToL2_coe D.dimension_ge_one β H hH L hL) (M+K*C) (by dsimp [M,C]; positivity)
  · intro r hr
    filter_upwards [gibbsLaw_support D.dimension_ge_one β H] with x hx
    have hxs : OnSphere x := (onSphere_iff_norm_sq x).mpr hx
    exact ⟨expectation_slope_norm_le D β κ hκ hκ0 K hK0 hK
      f hf C M hC hM x hxs r hr,hLf x hxs⟩
  · filter_upwards [gibbsLaw_support D.dimension_ge_one β H] with x hx
    exact expectation_generator_zero D β x
      ((onSphere_iff_norm_sq x).mpr hx) κ hκ hκ0 K hK0 hK f hf

end SlowEquilibration.ConditionedEntrance.SmoothKilled
