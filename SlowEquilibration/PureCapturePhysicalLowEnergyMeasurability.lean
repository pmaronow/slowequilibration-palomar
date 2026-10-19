-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalFiniteMeasurability

/-! Measurability and integrability of the literal finite-replica bad
energy alternative in source Proposition 9.16. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalLowEnergyMeasurability

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm SphericalGaussianJet
open PureCapturePhysicalCoarseTransfer
open PureCapturePhysicalFiniteEnsembleTransfer
open PureCapturePhysicalFiniteMeasurability
open scoped Topology BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def jointSuccessfulLowEnergy {n k T : ℕ} (μ : FiniteMixture)
    (Q θ e τ₁ : ℝ) :
    Set (Disorder (n+2) μ.maxDegree × PhysicalEnsemble (n+2) k T) :=
  {p | p.2 ∈ someSuccessfulBlockLowEnergy μ p.1 Q θ e τ₁}

theorem jointSuccessfulLowEnergy_measurable {n k T : ℕ}
    (μ : FiniteMixture) (Q θ e τ₁ : ℝ) :
    MeasurableSet (jointSuccessfulLowEnergy (n := n) (k := k) (T := T)
      μ Q θ e τ₁) := by
  have hb (b : Fin T) : MeasurableSet
      {p : Disorder (n+2) μ.maxDegree × PhysicalEnsemble (n+2) k T |
        goodCompanionBlock Q θ p.2.1 (p.2.2 b) ∧
        field (mixtureCoefficients μ) p.1 (physicalTrainingCenter (p.2.2 b)) <
          (n+2 : ℝ)*(e-τ₁)} := by
    have hblock : Measurable (fun p : Disorder (n+2) μ.maxDegree ×
        PhysicalEnsemble (n+2) k T => (p.2.1,p.2.2 b)) :=
      (measurable_fst.comp measurable_snd).prodMk
        ((measurable_pi_apply b).comp (measurable_snd.comp measurable_snd))
    have hG : MeasurableSet {q : Vector (n+2) × (Fin k → Vector (n+2)) |
        goodCompanionBlock Q θ q.1 q.2} :=
      (goodCompanionBlock_open (N := n+2) (k := k) Q θ).measurableSet
    have hgood : MeasurableSet {p : Disorder (n+2) μ.maxDegree ×
        PhysicalEnsemble (n+2) k T |
        goodCompanionBlock Q θ p.2.1 (p.2.2 b)} := by
      change MeasurableSet ((fun p : Disorder (n+2) μ.maxDegree ×
        PhysicalEnsemble (n+2) k T => (p.2.1,p.2.2 b)) ⁻¹'
          {q : Vector (n+2) × (Fin k → Vector (n+2)) |
            goodCompanionBlock Q θ q.1 q.2})
      exact hG.preimage hblock
    have hcenter : Measurable (fun p : Disorder (n+2) μ.maxDegree ×
        PhysicalEnsemble (n+2) k T => physicalTrainingCenter (p.2.2 b)) :=
      physicalTrainingCenter_measurable.comp
        ((measurable_pi_apply b).comp (measurable_snd.comp measurable_snd))
    have hfield : Measurable (fun p : Disorder (n+2) μ.maxDegree ×
        PhysicalEnsemble (n+2) k T =>
        field (mixtureCoefficients μ) p.1 (physicalTrainingCenter (p.2.2 b))) :=
      (field_jointContinuous (mixtureCoefficients μ)).measurable.comp
        (measurable_fst.prodMk hcenter)
    exact hgood.inter (measurableSet_lt hfield measurable_const)
  have hUnion : MeasurableSet
      (⋃ b : Fin T, {p : Disorder (n+2) μ.maxDegree × PhysicalEnsemble (n+2) k T |
        goodCompanionBlock Q θ p.2.1 (p.2.2 b) ∧
        field (mixtureCoefficients μ) p.1 (physicalTrainingCenter (p.2.2 b)) <
          (n+2 : ℝ)*(e-τ₁)}) :=
    MeasurableSet.iUnion hb
  convert hUnion using 1
  ext p
  simp [jointSuccessfulLowEnergy,someSuccessfulBlockLowEnergy]

/-- The source low-energy alternative has an original-disorder
measurable Gibbs-product probability. -/
theorem finiteLowEnergyProbability_measurable {n k T : ℕ}
    (μ : FiniteMixture) (β Q θ e τ₁ : ℝ) :
    Measurable (fun J : Disorder (n+2) μ.maxDegree =>
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real
        (someSuccessfulBlockLowEnergy μ J Q θ e τ₁)) := by
  have h := (Kernel.measurable_kernel_prodMk_left
    (κ := physicalEnsembleKernel (n := n) (k := k) (T := T) μ β)
    (jointSuccessfulLowEnergy_measurable μ Q θ e τ₁)).ennreal_toReal
  convert h using 1
  funext J
  change (physicalEnsembleLaw (k := k) (T := T) μ β J).real
      (someSuccessfulBlockLowEnergy μ J Q θ e τ₁) =
    (physicalEnsembleKernel (n := n) (k := k) (T := T) μ β J).real
      {p | (J,p) ∈ jointSuccessfulLowEnergy μ Q θ e τ₁}
  rw [physicalEnsembleKernel_apply]
  rfl

theorem finiteFailureProbability_integrable {n k T : ℕ}
    (μ : FiniteMixture) (β Q θ : ℝ) :
    Integrable (fun J : Disorder (n+2) μ.maxDegree =>
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real
        (allBlocksFail Q θ)) (disorderLaw (n+2) μ.maxDegree) := by
  apply Integrable.of_bound
    (finiteFailureProbability_measurable μ β Q θ).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro J
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

theorem finiteLowEnergyProbability_integrable {n k T : ℕ}
    (μ : FiniteMixture) (β Q θ e τ₁ : ℝ) :
    Integrable (fun J : Disorder (n+2) μ.maxDegree =>
      (physicalEnsembleLaw (k := k) (T := T) μ β J).real
        (someSuccessfulBlockLowEnergy μ J Q θ e τ₁))
        (disorderLaw (n+2) μ.maxDegree) := by
  apply Integrable.of_bound
    (finiteLowEnergyProbability_measurable μ β Q θ e τ₁).aestronglyMeasurable 1
  apply Filter.Eventually.of_forall
  intro J
  rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

end SlowEquilibration.PureCapturePhysicalLowEnergyMeasurability
