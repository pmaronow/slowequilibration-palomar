-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiUnitSpherePositivity
public import SlowEquilibration.GaussianIndependentBankPositivity

@[expose] public section

/-! Genuine independent-bank positivity on the metric sphere with arbitrary
labels. The true Gibbs normalization, Gaussian block laws and parameter
Fubini are used internally. Inputs describe actual finite linear fields and
their ordinary exponent split, not a desired positivity/pressure limit. -/

namespace SlowEquilibration.SphericalParisiLabeledBankPositivity
noncomputable section
open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation GaussianCompactFeatureComparison
open SphericalParisiUnitSpherePositivity SphericalPositivePerturbation
open SphericalAging.FiniteModel PureTensorJetBounds
open scoped RealInnerProductSpace
set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

/-- True joined-Gaussian and external-parameter average of metric-sphere
spin-label Gibbs pairs. All constants are uniform in every base law, label
space, Gaussian coordinate bank and literal bounded base feature. -/
theorem exists_uniform_actual_labeled_bank_positivity {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ K : ℕ,∃ V : ℝ,0 < K ∧ 1 ≤ V ∧
      ∀ {N : ℕ} (A : Type*) [MeasurableSpace A]
        (ν : Measure (UnitSphere N × A)) [IsProbabilityMeasure ν]
        (ι : Type*) [Fintype ι] [DecidableEq ι]
        (L : UnitSphere N × A → EuclideanSpace ℝ ι →L[ℝ] ℝ),Measurable L →
        ∀ {B : ℝ},(∀ᵐ z ∂ν,‖L z‖ ≤ B) →
        ∀ (v : ℝ),V ≤ v →
        ∀ (T : UnitSphere N × A → EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K) →L[ℝ] ℝ),
          Measurable T → ∀ {C : ℝ},0 ≤ C → (∀ᵐ z ∂ν,‖T z‖ ≤ C) →
        ∀ (Φ : (Fin K → ℝ) × EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K) →
          EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K)),Measurable Φ →
        (∀ (x : Fin K → ℝ) (D : EuclideanSpace ℝ (ι ⊕ TensorCoordinate N K)),
          ∀ᵐ z ∂ν,T z (Φ (x,D))=L z (sumSplit D).1+
            unitSphereLinear (coefficients v x) z.1 (sumSplit D).2) →
        (∫ x,∫ D,realizedPairMass ν T Φ
          {z : (UnitSphere N × A) × (UnitSphere N × A) |
            inner ℝ z.1.1.val z.2.1.val ≤ -ε} (x,D)
          ∂SYK.standardGaussianMeasureOnEuclidean (ι ⊕ TensorCoordinate N K)
          ∂positiveCubeLaw K) ≤ η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_metric_sphere_labeled_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro N A _ ν _ ι _ _ L hL B hb v hv T hT C hC hbT Φ hΦ hsplit
  let E : Set ((UnitSphere N × A) × (UnitSphere N × A)) :=
    {z | inner ℝ z.1.1.val z.2.1.val ≤ -ε}
  have hE : MeasurableSet E := measurableSet_le (by fun_prop) measurable_const
  let F := realizedPairMass ν T Φ E
  have hF : Measurable F := realizedPairMass_measurable ν T hT hC hbT Φ hΦ E hE
  have hFb : ∀ p,‖F p‖ ≤ 1 := realizedPairMass_norm_le_one ν T hT hbT Φ E
  have hNode (u : EuclideanSpace ℝ ι) :
      (∫ x,∫ w,F (x,sumJoin (u,w))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K) ≤ η := by
    have : IsProbabilityMeasure (gibbsMeasure ν L u) := gibbsMeasure_probability ν L hL hb u
    have H := hPos A (gibbsMeasure ν L u) v hv
    have he : (∫ x,∫ w,F (x,sumJoin (u,w))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K)=
      (∫ x,∫ w,
        ((gibbsMeasure (gibbsMeasure ν L u) (unitSphereLinear (coefficients v x) ∘ Prod.fst) w).prod
          (gibbsMeasure (gibbsMeasure ν L u) (unitSphereLinear (coefficients v x) ∘ Prod.fst) w)).real E
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K) := by
      apply integral_congr_ae
      exact .of_forall fun x => integral_congr_ae (.of_forall fun w => by
        have hs : ∀ᵐ z ∂ν,T z (Φ (x,sumJoin (u,w)))=
            L z u+unitSphereLinear (coefficients v x) z.1 w := by
          simpa only [sumSplit_sumJoin] using hsplit x (sumJoin (u,w))
        have hg := gibbsMeasure_associate ν L hL hb u
          (unitSphereLinear (coefficients v x) ∘ Prod.fst)
          ((unitSphereLinear_measurable _).comp measurable_fst) w T hT hbT
          (Φ (x,sumJoin (u,w))) hs
        change ((gibbsMeasure ν T (Φ (x,sumJoin (u,w)))).prod
          (gibbsMeasure ν T (Φ (x,sumJoin (u,w))))).real E=_
        rw [← hg])
    exact he.trans_le H
  have hSwap := external_parameter_joined_gaussian_swap (positiveCubeLaw K) F hF hFb
  change (∫ x,∫ D,F (x,D) ∂SYK.standardGaussianMeasureOnEuclidean (ι ⊕ TensorCoordinate N K)
    ∂positiveCubeLaw K) ≤ η
  rw [hSwap]
  have hn : ∀ᵐ u ∂SYK.standardGaussianMeasureOnEuclidean ι,
      0 ≤ (∫ x,∫ w,F (x,sumJoin (u,w))
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K) :=
    .of_forall fun u => integral_nonneg fun x => integral_nonneg fun w => measureReal_nonneg
  have H := integral_mono_of_nonneg hn (integrable_const η) (.of_forall hNode)
  simpa only [integral_const,probReal_univ,one_smul] using H

end
end SlowEquilibration.SphericalParisiLabeledBankPositivity
