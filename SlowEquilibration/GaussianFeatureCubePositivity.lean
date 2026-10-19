-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianFeatureCubeStatistics
public import SlowEquilibration.GaussianThreeBlockReplicaError

/-! Genuine uniform negative-overlap control for arbitrary continuous
spherical feature fields with an independent trial and held tensor bank. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianFeatureDirac

open MeasureTheory ProbabilityTheory Set
open GaussianSpinInterpolation SphericalPositivePerturbation
open SphericalAging.FiniteModel SphericalAging.SphereInitialLaw
open scoped Topology RealInnerProductSpace

set_option maxHeartbeats 1800000
set_option linter.unusedSectionVars false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n K : ℕ}

theorem cube_pairMass_realization (A : Vector n → EuclideanSpace ℝ ι) (β k v θ : ℝ)
    (cube : Fin K → ℝ) (D : EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K)))
    (E : Set (Vector n × Vector n)) :
    GaussianThreeBlockComparison.pairEventMass (sphereLaw n) (cubeLinear A β k v cube) threeLabel θ E D=
      realizedPairMass (sphereLaw n) (cubeLinear A β k v (fun _ => 1)) (cubeRealization n K θ) E (cube,D) := by
  unfold GaussianThreeBlockComparison.pairEventMass realizedPairMass
  rw [cube_gibbs_realization]

theorem cube_meanEventMass_integrable (hn : 1≤n) (A : Vector n → EuclideanSpace ℝ ι)
    (hA : Continuous A) (β k v θ : ℝ) (E : Set (Vector n × Vector n)) (hE : MeasurableSet E) :
    Integrable (fun cube : Fin K → ℝ => ∫D,
      GaussianThreeBlockComparison.pairEventMass (sphereLaw n) (cubeLinear A β k v cube) threeLabel θ E D
      ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K))) (positiveCubeLaw K) := by
  let T := cubeLinear (K := K) A β k v (fun _ => 1)
  obtain ⟨B,hB,hTb⟩ := exists_cube_bound hn A hA β k v (fun _ => 1)
  have hT : Measurable T := (cubeLinear_continuous A hA β k v _).measurable
  let F := realizedPairMass (sphereLaw n) T (cubeRealization (ι := ι) n K θ) E
  have hF : Measurable F := realizedPairMass_measurable (sphereLaw n) T hT hB hTb _
    (cubeRealization_continuous n K θ).measurable E hE
  have hm := hF.stronglyMeasurable.integral_prod_right'
    (ν := SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K))) |>.measurable
  have hbound (cube : Fin K → ℝ) :
      ‖∫D,F (cube,D) ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K))‖≤1 := by
    simpa only [probReal_univ,mul_one] using norm_integral_le_of_norm_le_const
      (μ := SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K)))
      (.of_forall fun D => realizedPairMass_norm_le_one (sphereLaw n) T hT hTb _ E (cube,D))
  have hi : Integrable (fun cube => ∫D,F (cube,D)
      ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K)))
      (positiveCubeLaw K) := Integrable.of_bound hm.aestronglyMeasurable 1 (.of_forall hbound)
  convert hi using 1
  funext cube
  apply integral_congr_ae
  exact .of_forall fun D => cube_pairMass_realization A β k v θ cube D E

/-- All perturbation constants are selected before dimension, coefficient
space, every original feature realization, trial and interpolation angle. -/
theorem exists_uniform_cube_pair_positivity {ε η : ℝ}
    (hε : 0<ε) (hε1 : ε≤1) (hη : 0<η) :
    ∃ K : ℕ,∃ V : ℝ,0<K ∧ 1≤V ∧
      ∀ (n : ℕ),1≤n → ∀ (ι : Type*) [Fintype ι] [DecidableEq ι],
      ∀ (A : Vector n → EuclideanSpace ℝ ι),Continuous A →
      ∀ (β k v : ℝ),V≤v → ∀θ : ℝ,
      (∫cube,∫D,GaussianThreeBlockComparison.pairEventMass (sphereLaw n)
        (cubeLinear A β k v cube) threeLabel θ
        {z : Vector n × Vector n | SphericalModel.overlap z.1 z.2≤-ε} D
        ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K)) ∂positiveCubeLaw K)≤η := by
  obtain ⟨K,V,hK,hV,hPos⟩ := exists_uniform_sphere_bank_positivity hε hε1 hη
  refine ⟨K,V,hK,hV,?_⟩
  intro n hn ι _ _ A hA β k v hv θ
  let L := GaussianSpinComparison.rotatedLinear (twoLinear A β k) twoLabel θ
  obtain ⟨B₂,hB₂,hOld⟩ := exists_twoLinear_sphere_bound A hA β k
  have hL : Measurable L := GaussianSpinComparison.rotatedLinear_measurable _
    (twoLinear_continuous A hA β k).measurable twoLabel θ
  have hOldb : ∀ᵐ x ∂sphereLaw n,‖twoLinear A β k x‖≤B₂ :=
    (sphereLaw_support hn).mono fun x hx => hOld x hx
  have hLb := GaussianSpinComparison.rotatedLinear_bound (sphereLaw n) _ hB₂ hOldb twoLabel θ
  let T := cubeLinear (K := K) A β k v (fun _ => 1)
  obtain ⟨B,hB,hTb⟩ := exists_cube_bound hn A hA β k v (fun _ => 1)
  have hT : Measurable T := (cubeLinear_continuous A hA β k v _).measurable
  have hsplit (cube : Fin K → ℝ) (D : EuclideanSpace ℝ (ThreeCoordinate n ι (TensorCoordinate n K))) :
      ∀ᵐ x ∂sphereLaw n,T x (cubeRealization n K θ (cube,D))=
        L x (GaussianCompactFeatureComparison.sumSplit D).1+
          radialPerturbation (coefficients v cube) (Real.sqrt n) x (GaussianCompactFeatureComparison.sumSplit D).2 := by
    exact .of_forall fun x => by
      change cubeLinear A β k v (fun _ => 1) x
        (GaussianThreeBlockComparison.rotation threeLabel θ (cubeOperator cube D))=_
      rw [cubeOperator_rotation,← cubeLinear_realization,cubeLinear,threeLinear_rotation]
      rfl
  have ht := hPos hn (TwoCoordinate n ι) L hL hLb v hv T hT hB hTb
    (cubeRealization (ι := ι) n K θ) (cubeRealization_continuous n K θ).measurable hsplit
  have heq : (∫cube,∫D,GaussianThreeBlockComparison.pairEventMass (sphereLaw n)
      (cubeLinear A β k v cube) threeLabel θ
      {z : Vector n × Vector n | SphericalModel.overlap z.1 z.2≤-ε} D
      ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K)) ∂positiveCubeLaw K)=
      ∫cube,∫D,realizedPairMass (sphereLaw n) T (cubeRealization (ι := ι) n K θ)
        {z : Vector n × Vector n | SphericalModel.overlap z.1 z.2≤-ε} (cube,D)
      ∂SYK.standardGaussianMeasureOnEuclidean (ThreeCoordinate n ι (TensorCoordinate n K)) ∂positiveCubeLaw K := by
    apply integral_congr_ae
    exact .of_forall fun cube => integral_congr_ae (.of_forall fun D => cube_pairMass_realization A β k v θ cube D _)
  exact heq.trans_le ht

end SlowEquilibration.GaussianFeatureDirac
