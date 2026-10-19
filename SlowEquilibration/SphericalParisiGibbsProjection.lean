-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianSpinKernels
public import SlowEquilibration.SphericalPerturbationPairMass

@[expose] public section

/-! Exact Gibbs projection and true uniform spherical overlap positivity
with arbitrary extra labels. This is the ordinary joint spin-label Gibbs
measure needed for a finite-label Ruelle interpolation. The label law may
be singular; its true marginal is obtained by pushforward, with both Gibbs
normalization and product-replica transport proved internally. -/

namespace SlowEquilibration.SphericalParisiGibbsProjection

noncomputable section
open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation SphericalPositivePerturbation
open SphericalAging.FiniteModel
open scoped Topology RealInnerProductSpace ENNReal
set_option maxHeartbeats 1000000

theorem map_withDensity_composition {V W : Type*} [MeasurableSpace V] [MeasurableSpace W]
    (ν : Measure V) (s : V → W) (hs : Measurable s) (d : W → ℝ≥0∞) (hd : Measurable d) :
    (ν.withDensity (d ∘ s)).map s=(ν.map s).withDensity d := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf hs]
  change (∫⁻ v,(f ∘ s) v ∂ν.withDensity (d ∘ s))=_
  rw [lintegral_withDensity_eq_lintegral_mul ν (hd.comp hs) (hf.comp hs),
    lintegral_withDensity_eq_lintegral_mul (ν.map s) hd hf]
  have hmul : Measurable (fun w => d w*f w) := hd.mul hf
  simpa only [Pi.mul_apply,Function.comp_apply] using (lintegral_map hmul hs).symm

/-- An actual ordinary Gibbs tilt which depends only on a measurable
spin projection pushes forward to the Gibbs tilt of the true spin law. -/
theorem gibbsMeasure_pushforward {V W H : Type*}
    [MeasurableSpace V] [MeasurableSpace W]
    [NormedAddCommGroup H] [NormedSpace ℝ H]
    (ν : Measure V) (s : V → W) (hs : Measurable s)
    (L : W → H →L[ℝ] ℝ) (hL : Measurable L) (w : H) :
    (gibbsMeasure ν (L ∘ s) w).map s=gibbsMeasure (ν.map s) L w := by
  have hZ : GaussianSpinInterpolation.moment (ν.map s) (fun _ => 1) L w=
      GaussianSpinInterpolation.moment ν (fun _ => 1) (L ∘ s) w := by
    unfold GaussianSpinInterpolation.moment weight
    simp only [one_mul]
    have he : Measurable (fun v : W => Real.exp (L v w)) :=
      ((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL).exp
    exact integral_map hs.aemeasurable he.aestronglyMeasurable
  unfold gibbsMeasure
  rw [hZ]
  exact map_withDensity_composition ν s hs _
    ((((ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL).exp.div_const _).ennreal_ofReal)

/-- Uniform genuine negative-overlap control survives arbitrary extra
labels in the original Gibbs space. Its cutoff and strength are selected
before all dimensions, all label spaces, and all joint probability laws. -/
theorem exists_uniform_labeled_gibbs_pair_positivity {ε η : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1) (hη : 0 < η) :
    ∃ K : ℕ,∃ V : ℝ,0 < K ∧ 1 ≤ V ∧
      ∀ {N : ℕ} (A : Type*) [MeasurableSpace A]
        (ν : Measure (UnitSpin N × A)) [IsProbabilityMeasure ν]
        (v : ℝ),V ≤ v →
        (∫ x,∫ w,
          ((gibbsMeasure ν (unitLinear (coefficients v x) ∘ Prod.fst) w).prod
            (gibbsMeasure ν (unitLinear (coefficients v x) ∘ Prod.fst) w)).real
          {z : (UnitSpin N × A) × (UnitSpin N × A) |
            inner ℝ z.1.1.val z.2.1.val ≤ -ε}
          ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)
          ∂positiveCubeLaw K) ≤ η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_gibbs_pair_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro N A _ ν _ v hv
  have hp := hPos (ν.map Prod.fst) v hv
  have hpair (x : Fin K → ℝ) (w : PerturbationDisorder N K) :
      ((gibbsMeasure ν (unitLinear (coefficients v x) ∘ Prod.fst) w).prod
        (gibbsMeasure ν (unitLinear (coefficients v x) ∘ Prod.fst) w)).real
        {z : (UnitSpin N × A) × (UnitSpin N × A) |
          inner ℝ z.1.1.val z.2.1.val ≤ -ε} =
      ((gibbsMeasure (ν.map Prod.fst) (unitLinear (coefficients v x)) w).prod
        (gibbsMeasure (ν.map Prod.fst) (unitLinear (coefficients v x)) w)).real
        {z : UnitSpin N × UnitSpin N | inner ℝ z.1.val z.2.val ≤ -ε} := by
    have hg := gibbsMeasure_pushforward ν Prod.fst measurable_fst
      (unitLinear (coefficients v x)) (unitLinear_measurable _) w
    let : SFinite (gibbsMeasure ν (unitLinear (coefficients v x) ∘ Prod.fst) w) := by
      unfold gibbsMeasure
      infer_instance
    rw [← hg,Measure.map_prod_map _ _ measurable_fst measurable_fst,
      map_measureReal_apply (measurable_fst.prodMap measurable_fst)
        (measurableSet_le (by fun_prop) measurable_const)]
    rfl
  have he : (∫ x,∫ w,
      ((gibbsMeasure ν (unitLinear (coefficients v x) ∘ Prod.fst) w).prod
        (gibbsMeasure ν (unitLinear (coefficients v x) ∘ Prod.fst) w)).real
        {z : (UnitSpin N × A) × (UnitSpin N × A) |
          inner ℝ z.1.1.val z.2.1.val ≤ -ε}
      ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K) =
      (∫ x,∫ w,
        ((gibbsMeasure (ν.map Prod.fst) (unitLinear (coefficients v x)) w).prod
          (gibbsMeasure (ν.map Prod.fst) (unitLinear (coefficients v x)) w)).real
          {z : UnitSpin N × UnitSpin N | inner ℝ z.1.val z.2.val ≤ -ε}
        ∂SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K) ∂positiveCubeLaw K) := by
    apply integral_congr_ae
    exact .of_forall fun x => integral_congr_ae (.of_forall (hpair x))
  exact he.trans_le hp

end
end SlowEquilibration.SphericalParisiGibbsProjection
