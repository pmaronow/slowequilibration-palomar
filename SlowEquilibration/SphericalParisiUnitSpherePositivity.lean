-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalParisiGibbsProjection
public import SlowEquilibration.PureTensorJetBounds

@[expose] public section

/-! Uniform true Gibbs positivity on the literal metric unit sphere used by
the original spherical field. The normalization-one spin subtype is related
by the actual identity on underlying physical vectors and measurable Gibbs
pushforward. Arbitrary extra labels and singular base measures are retained. -/

namespace SlowEquilibration.SphericalParisiUnitSpherePositivity
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalAging.FiniteModel PureTensorJetBounds
open SphericalPositivePerturbation GaussianSpinInterpolation
open SphericalParisiGibbsProjection
open scoped RealInnerProductSpace
set_option maxHeartbeats 1000000

def sphereToSpin (N : ℕ) (z : UnitSphere N) : UnitSpin N := ⟨z.val,unit_norm z⟩

theorem sphereToSpin_measurable (N : ℕ) : Measurable (sphereToSpin N) := by
  unfold sphereToSpin
  fun_prop

def unitSphereLinear {N K : ℕ} (a : Fin K → ℝ) :
    UnitSphere N → PerturbationDisorder N K →L[ℝ] ℝ := fun z => linear a z.val

theorem unitSphereLinear_measurable {N K : ℕ} (a : Fin K → ℝ) :
    Measurable (unitSphereLinear (N := N) a) :=
  (linear_measurable a).comp measurable_subtype_coe

/-- The actual sphere-label Gibbs pushforward preserves the literal
negative-overlap product probability. -/
theorem actual_metric_sphere_gibbs_pair_mass {N K : ℕ}
    (A : Type*) [MeasurableSpace A] (ν : Measure (UnitSphere N × A)) [SFinite ν]
    (a : Fin K → ℝ) (w : PerturbationDisorder N K) (ε : ℝ) :
    ((gibbsMeasure ν (unitSphereLinear a ∘ Prod.fst) w).prod
      (gibbsMeasure ν (unitSphereLinear a ∘ Prod.fst) w)).real
      {z : (UnitSphere N × A) × (UnitSphere N × A) |
        inner ℝ z.1.1.val z.2.1.val ≤ -ε} =
    ((gibbsMeasure (ν.map (Prod.map (sphereToSpin N) id))
      (unitLinear a ∘ Prod.fst) w).prod
      (gibbsMeasure (ν.map (Prod.map (sphereToSpin N) id))
      (unitLinear a ∘ Prod.fst) w)).real
      {z : (UnitSpin N × A) × (UnitSpin N × A) |
        inner ℝ z.1.1.val z.2.1.val ≤ -ε} := by
  let s := Prod.map (sphereToSpin N) (id : A → A)
  have hs : Measurable s := (sphereToSpin_measurable N).prodMap measurable_id
  have hg := gibbsMeasure_pushforward ν s hs (unitLinear a ∘ Prod.fst)
    ((unitLinear_measurable a).comp measurable_fst) w
  have hcomp : (unitLinear a ∘ Prod.fst) ∘ s=unitSphereLinear a ∘ Prod.fst := rfl
  rw [hcomp] at hg
  let : SFinite (gibbsMeasure ν (unitSphereLinear a ∘ Prod.fst) w) := by
    unfold gibbsMeasure
    infer_instance
  rw [← hg,Measure.map_prod_map _ _ hs hs,
    map_measureReal_apply (hs.prodMap hs)
      (measurableSet_le (by fun_prop) measurable_const)]
  rfl

/-- Actual uniform positivity with metric-sphere spins and arbitrary labels.
The perturbation cutoff and strength are chosen before every dimension,
all labels and all joint probability measures. -/
theorem exists_uniform_metric_sphere_labeled_positivity {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ K : ℕ,∃ V : ℝ,0 < K ∧ 1 ≤ V ∧
      ∀ {N : ℕ} (A : Type*) [MeasurableSpace A]
        (ν : Measure (UnitSphere N × A)) [IsProbabilityMeasure ν]
        (v : ℝ),V ≤ v →
        (∫ x,∫ w,
          ((gibbsMeasure ν (unitSphereLinear (coefficients v x) ∘ Prod.fst) w).prod
            (gibbsMeasure ν (unitSphereLinear (coefficients v x) ∘ Prod.fst) w)).real
          {z : (UnitSphere N × A) × (UnitSphere N × A) |
            inner ℝ z.1.1.val z.2.1.val ≤ -ε}
          ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
          ∂positiveCubeLaw K) ≤ η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_labeled_gibbs_pair_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro N A _ ν _ v hv
  have hs : Measurable (Prod.map (sphereToSpin N) (id : A → A)) :=
    (sphereToSpin_measurable N).prodMap measurable_id
  have : IsProbabilityMeasure (ν.map (Prod.map (sphereToSpin N) id)) :=
    (Measure.isProbabilityMeasure_map_iff hs.aemeasurable).mpr inferInstance
  have H := hPos A (ν.map (Prod.map (sphereToSpin N) id)) v hv
  apply le_trans _ H
  apply le_of_eq
  apply integral_congr_ae
  exact .of_forall fun x => integral_congr_ae (.of_forall fun w =>
    actual_metric_sphere_gibbs_pair_mass A ν (coefficients v x) w ε)

end
end SlowEquilibration.SphericalParisiUnitSpherePositivity
