-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiLabeledRealization
public import SlowEquilibration.GaussianThreeBlockReplicaError

@[expose] public section

/-! Actual uniform positive-overlap control for the original finite tensor
field, shared/fresh linear trial, finite labels and held perturbation at
every interpolation angle. The real Gaussian realization and the true
Gibbs normalization/Fubini are used; no positivity limit is a hypothesis. -/

namespace SlowEquilibration.SphericalParisiLabeledPhysicalPositivity
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalModel FiniteTensorMixtureMaximum PureTensorJetBounds
open SphericalParisiLabeledCovariance SphericalParisiLabeledThreeBlock
open SphericalParisiLabeledTrace SphericalParisiLabeledBankPositivity
open SphericalParisiLabeledRealization
open SphericalPositivePerturbation GaussianCompactFeatureComparison GaussianSpinInterpolation
open scoped RealInnerProductSpace
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
variable {σ : Type*} [Fintype σ] [DecidableEq σ]

omit [DecidableEq σ] in
theorem actual_negative_pair_mass_realization {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) (d : σ → ℕ) (c : σ → ℝ)
    (β q0 q1 v θ ε : ℝ) (x : Fin K → ℝ)
    (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
    actualNegativePairMass ν d c β q0 q1 v x θ D ε=
      realizedPairMass ν (threeLinear d c β q0 q1 v (fun _ => 1))
        (realizedDisorder N k K d θ) (negativePairSet N k ε) (x,D) := by
  unfold actualNegativePairMass realizedPairMass
  dsimp only
  rw [actual_three_gibbs_realization]

/-- All true finite Gaussian and coefficient averages of the literal
negative-overlap event are small, uniformly in every original mixture,
label count, reference law, inverse temperature and rotation parameter. -/
theorem exists_uniform_actual_three_bank_pair_positivity {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ K : ℕ,∃ V : ℝ,0 < K ∧ 1 ≤ V ∧
      ∀ (N k : ℕ) (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
        (σ : Type*) [Fintype σ] [DecidableEq σ]
        (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v : ℝ),V ≤ v → ∀ θ : ℝ,
      (∫ x,∫ D,actualNegativePairMass ν d c β q0 q1 v x θ D ε
        ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate N k K d)
        ∂positiveCubeLaw K) ≤ η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_actual_labeled_bank_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro N k ν _ σ _ _ d c β q0 q1 v hv θ
  let L := baseLinear (N := N) (k := k) d c β q0 q1 θ
  have hL : Measurable L := (baseLinear_continuous d c β q0 q1 θ).measurable
  obtain ⟨B,hB⟩ := isCompact_univ.exists_bound_of_continuousOn
    (baseLinear_continuous (N := N) (k := k) d c β q0 q1 θ).continuousOn
  have hb : ∀ᵐ z ∂ν,‖L z‖ ≤ B := .of_forall fun z => hB z (mem_univ z)
  let T := threeLinear (N := N) (k := k) d c β q0 q1 v (fun _ : Fin K => 1)
  have hT : Measurable T := (actual_threeLinear_continuous d c β q0 q1 v _).measurable
  obtain ⟨C,hC,hbound⟩ := actual_threeLinear_bounded (N := N) (k := k) d c β q0 q1 v (fun _ : Fin K => 1)
  have hbT : ∀ᵐ z ∂ν,‖T z‖ ≤ C := .of_forall hbound
  have hsplit (x : Fin K → ℝ) (D : EuclideanSpace ℝ (ThreeCoordinate N k K d)) :
      ∀ᵐ z ∂ν,T z (realizedDisorder N k K d θ (x,D))=
        L z (sumSplit D).1+
          SphericalParisiUnitSpherePositivity.unitSphereLinear (coefficients v x) z.1 (sumSplit D).2 := by
    exact .of_forall fun z => by
      change threeLinear d c β q0 q1 v (fun _ => 1) z
        (GaussianThreeBlockComparison.rotation threeLabel θ (parameterDisorder x D))=_
      rw [parameterDisorder_rotation,← actual_threeLinear_parameter_realization,
        actual_threeLinear_rotation_split]
  have H := hPos (Fin k) ν (BaseCoordinate N k d) L hL hb v hv T hT hC hbT
    (realizedDisorder N k K d θ) (realizedDisorder_continuous N k K d θ).measurable hsplit
  apply le_trans _ H
  apply le_of_eq
  apply integral_congr_ae
  exact .of_forall fun x => integral_congr_ae (.of_forall fun D =>
    actual_negative_pair_mass_realization ν d c β q0 q1 v θ ε x D)

omit [DecidableEq σ] in
/-- Joint coefficient/Gaussian integrability of the actual negative pair
mass follows from the genuine Markov Gibbs law and its true [0,1] bound. -/
theorem actual_negative_pair_mass_joint_integrable {N k K : ℕ}
    (ν : Measure (UnitSphere N × Fin k)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (β q0 q1 v θ ε : ℝ) :
    Integrable (fun p : (Fin K → ℝ) × EuclideanSpace ℝ (ThreeCoordinate N k K d) =>
      actualNegativePairMass ν d c β q0 q1 v p.1 θ p.2 ε)
      ((positiveCubeLaw K).prod (SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate N k K d))) := by
  let T := threeLinear (N := N) (k := k) d c β q0 q1 v (fun _ : Fin K => 1)
  obtain ⟨C,hC,hbound⟩ := actual_threeLinear_bounded (N := N) (k := k) d c β q0 q1 v (fun _ : Fin K => 1)
  have hT : Measurable T := (actual_threeLinear_continuous d c β q0 q1 v _).measurable
  have hb : ∀ᵐ z ∂ν,‖T z‖ ≤ C := .of_forall hbound
  let F := realizedPairMass ν T (realizedDisorder N k K d θ) (negativePairSet N k ε)
  have hF : Measurable F := realizedPairMass_measurable ν T hT hC hb _
    (realizedDisorder_continuous N k K d θ).measurable _ (negativePairSet_measurable N k ε)
  have hi : Integrable F ((positiveCubeLaw K).prod
      (SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate N k K d))) :=
    Integrable.of_bound hF.aestronglyMeasurable 1 (.of_forall fun p =>
      realizedPairMass_norm_le_one ν T hT hb _ _ p)
  apply hi.congr
  exact .of_forall fun p => (actual_negative_pair_mass_realization ν d c β q0 q1 v θ ε p.1 p.2).symm

end
end SlowEquilibration.SphericalParisiLabeledPhysicalPositivity
