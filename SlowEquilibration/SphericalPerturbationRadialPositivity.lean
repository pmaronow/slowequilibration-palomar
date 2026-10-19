-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalPerturbationConditioning

/-! Genuine uniform positivity after conditioning arbitrary bounded
Gaussian base fields on the actual positive-radius sphere. The final
probability is the literal ambient two-replica Gibbs probability. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalPositivePerturbation

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation
open SphericalAging.FiniteModel
open scoped ProbabilityTheory Topology RealInnerProductSpace

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

def radiusOverlap {N : ℕ} (r : ℝ) (x y : Vector N) : ℝ := inner ℝ x y/r^2

theorem radiusOverlap_fromUnit {N : ℕ} {r : ℝ} (hr : r≠0) (x y : UnitSpin N) :
    radiusOverlap r (fromUnit r x) (fromUnit r y)=inner ℝ x.val y.val := by
  simp only [radiusOverlap,fromUnit,real_inner_smul_left,real_inner_smul_right]
  field_simp [hr]

theorem radiusOverlap_measurable (N : ℕ) (r : ℝ) :
    Measurable (fun z : Vector N × Vector N => radiusOverlap r z.1 z.2) := by
  unfold radiusOverlap
  fun_prop

/-- Exact two-replica event transport under the actual sphere embedding. -/
theorem fromUnit_pair_mass {N : ℕ} (G : Measure (UnitSpin N)) [SFinite G]
    {r : ℝ} (hr : 0<r) (A : Set ℝ) (hA : MeasurableSet A) :
    ((G.map (fromUnit r)).prod (G.map (fromUnit r))).real
      {z : Vector N × Vector N | radiusOverlap r z.1 z.2∈A}=
    (G.prod G).real {z : UnitSpin N × UnitSpin N | inner ℝ z.1.val z.2.val∈A} := by
  have hs := fromUnit_measurable N r
  have hF := hs.prodMap hs
  have hE : MeasurableSet {z : Vector N × Vector N | radiusOverlap r z.1 z.2∈A} := by
    simpa only [preimage,mem_ofPred_eq] using hA.preimage (radiusOverlap_measurable N r)
  rw [Measure.map_prod_map _ _ hs hs,map_measureReal_apply hF hE]
  congr 1
  ext z
  change radiusOverlap r (fromUnit r z.1) (fromUnit r z.2)∈A ↔ inner ℝ z.1.val z.2.val∈A
  rw [radiusOverlap_fromUnit hr.ne']

/-- Exact radial tensor tilt of the true ambient spherical law. -/
theorem radial_gibbsMeasure_map {N K : ℕ} (μ : Measure (Vector N))
    {r : ℝ} (hr : 0<r) (hμ : ∀ᵐ x ∂μ,‖x‖=r) (a : Fin K → ℝ)
    (w : PerturbationDisorder N K) :
    gibbsMeasure μ (radialPerturbation a r) w=
      (gibbsMeasure (unitLaw μ r) (unitLinear a) w).map (fromUnit r) := by
  calc
    _=(gibbsMeasure (unitLaw μ r) (fun z => radialPerturbation a r (fromUnit r z)) w).map (fromUnit r) :=
      (unitLaw_gibbs_map μ hr hμ _ (radialPerturbation_measurable a r) w).symm
    _=_ := by
      congr 1
      apply gibbsMeasure_congr_field
      exact .of_forall fun z => congrArg (fun f => f w) (radialPerturbation_fromUnit a hr.ne' z)

/-- Uniform positivity under arbitrary actual bounded Gaussian base-field
conditioning. K and V precede the sphere dimension, radius, spin law,
coefficient space, base field and its realized Gaussian coordinates. -/
theorem exists_uniform_conditioned_radial_positivity {ε η : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hη : 0<η) :
    ∃ K : ℕ, ∃ V : ℝ, 0<K ∧ 1≤V ∧
      ∀ {N : ℕ} (μ : Measure (Vector N)) [IsProbabilityMeasure μ]
      {r : ℝ}, 0<r → (∀ᵐ x ∂μ,‖x‖=r) →
      ∀ (H : Type*) [NormedAddCommGroup H] [NormedSpace ℝ H]
        [CompleteSpace H] [FiniteDimensional ℝ H],
      ∀ (L : Vector N → H →L[ℝ] ℝ), Measurable L →
      ∀ {B : ℝ}, (∀ᵐ x ∂μ,‖L x‖≤B) → ∀ (u : H) (v : ℝ), V≤v →
        (∫x,∫w,
          ((gibbsMeasure (gibbsMeasure μ L u) (radialPerturbation (coefficients v x) r) w).prod
            (gibbsMeasure (gibbsMeasure μ L u) (radialPerturbation (coefficients v x) r) w)).real
            {z : Vector N × Vector N | radiusOverlap r z.1 z.2≤-ε}
          ∂(SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ∂positiveCubeLaw K)≤η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_gibbs_pair_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro N μ _ r hr hμ H _ _ _ _ L hL B hb u v hv
  have hvnon : 0≤v := le_trans (by norm_num : (0:ℝ)≤1) (hV.trans hv)
  let μb := gibbsMeasure μ L u
  have hμb : ∀ᵐ x ∂μb,‖x‖=r := (gibbsMeasure_absolutelyContinuous μ L u).ae_le hμ
  let ν := unitLaw μb r
  let _ : IsProbabilityMeasure ν := conditioned_unitLaw_probability μ hr hμ L hL hb u
  have hbound := hPos ν v hv
  have heq : (∫x,∫w,
      ((gibbsMeasure μb (radialPerturbation (coefficients v x) r) w).prod
        (gibbsMeasure μb (radialPerturbation (coefficients v x) r) w)).real
        {z : Vector N × Vector N | radiusOverlap r z.1 z.2≤-ε}
      ∂(SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ∂positiveCubeLaw K)=
      ∫x,∫w,((gibbsMeasure ν (unitLinear (coefficients v x)) w).prod
        (gibbsMeasure ν (unitLinear (coefficients v x)) w)).real
        {z : UnitSpin N × UnitSpin N | inner ℝ z.1.val z.2.val≤-ε}
      ∂(SYK.standardGaussianMeasureOnEuclidean (TensorCoordinate N K)) ∂positiveCubeLaw K := by
    apply integral_congr_ae
    exact .of_forall fun x => by
      apply integral_congr_ae
      exact .of_forall fun w => by
        let _ := parameterizedGibbsKernel_markov (K := K) ν hvnon
        let _ : IsProbabilityMeasure (gibbsMeasure ν (unitLinear (coefficients v x)) w) := by
          rw [← parameterizedGibbsKernel_apply ν hvnon x w]
          infer_instance
        change ((gibbsMeasure μb (radialPerturbation (coefficients v x) r) w).prod
          (gibbsMeasure μb (radialPerturbation (coefficients v x) r) w)).real _=_
        rw [radial_gibbsMeasure_map μb hr hμb]
        exact fromUnit_pair_mass _ hr (Iic (-ε)) measurableSet_Iic
  exact heq.trans_le hbound

end SlowEquilibration.SphericalPositivePerturbation
