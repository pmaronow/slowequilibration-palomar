-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPosteriorIndependence
public import SlowEquilibration.CommonHessianBulkBorderCovariance
public import SlowEquilibration.SphericalPosteriorCommonGOE

/-! Actual posterior independence of the entire common Hessian bulk pair
from both border rows and corners. No independence assumption is supplied. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity GaussianRegressionCovariance SphericalConditionalMatrices
open NormalizedPairObservations SphericalTwoPointCovariance CanonicalGOERealization
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

section SinglePair
variable {E F G H : Type*}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
omit [FiniteDimensional ℝ F] in
lemma single_pair_cross_zero (B : E →L[ℝ] F) (A : E →L[ℝ] G) (C : E →L[ℝ] H)
    (hBA : B.comp A.adjoint=0) (hBC : B.comp C.adjoint=0) :
    B.comp (pairHilbert A C).adjoint=0 := by
  apply ContinuousLinearMap.ext
  intro w
  change B ((pairHilbert A C).adjoint w)=0
  rw [pairHilbert_adjoint,map_add]
  have h1:=congrArg (fun T:G→L[ℝ]F=>T w.fst) hBA
  have h2:=congrArg (fun T:H→L[ℝ]F=>T w.snd) hBC
  change B (A.adjoint w.fst)=0 at h1
  change B (C.adjoint w.snd)=0 at h2
  rw [h1,h2,zero_add]
end SinglePair

def borderCLM {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N) (e : Fin m → Vector N)
    (v : Vector N) : EuclideanDisorder N P →L[ℝ] WithLp 2 (EuclideanSpace ℝ (Fin m)×ℝ) :=
  pairHilbert (commonRowCLM c x e v) (flatJetCLM c 2 x ![v,v])

def borderPairCLM {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e : Fin m → Vector N) (v w : Vector N) : EuclideanDisorder N P →L[ℝ]
      WithLp 2 (WithLp 2 (EuclideanSpace ℝ (Fin m)×ℝ)×WithLp 2 (EuclideanSpace ℝ (Fin m)×ℝ)) :=
  pairHilbert (borderCLM c x e v) (borderCLM c y e w)

lemma common_bulk_border_cross_zero {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y v : Vector N) (e : Fin m → Vector N)
    (htany : ∀ i,inner ℝ (e i) y=0) (hplane : ∀ i,inner ℝ (e i) v=0) :
    (flatHessianCLM c x e).comp (borderCLM c y e v).adjoint=0 :=
  single_pair_cross_zero _ _ _ (common_bulk_row_cross_zero hN c hc x y v e htany hplane)
    (common_bulk_corner_cross_zero hN c hc x y v e htany hplane)

lemma common_bulk_pair_border_pair_cross_zero {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y v w : Vector N) (e : Fin m → Vector N)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hv : ∀ i,inner ℝ (e i) v=0) (hw : ∀ i,inner ℝ (e i) w=0) :
    (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)).comp (borderPairCLM c x y e v w).adjoint=0 :=
  paired_observations_cross_zero _ _ _ _
    (common_bulk_border_cross_zero hN c hc x x v e htanx hv)
    (common_bulk_border_cross_zero hN c hc x y w e htany hw)
    (common_bulk_border_cross_zero hN c hc y x v e htanx hv)
    (common_bulk_border_cross_zero hN c hc y y w e htany hw)


/-- Full actual common bulk pair is independent of both complete border
rows and corners under every specified mixed posterior target. -/
theorem common_bulk_border_mixed_independent {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y v v' : Vector N) (e : Fin m → Vector N)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hv : ∀ i,inner ℝ (e i) v=0) (hv' : ∀ i,inner ℝ (e i) v'=0)
    (f g : Fin k → Vector N) (w : WithLp 2 (MixedObservationSpace k×MixedObservationSpace k))
    (hA : Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))) :
    IndepFun (actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)))
      (actualObservation (borderPairCLM c x y e v v'))
      (coefficientKernel (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)) w) := by
  apply coefficientKernel_independent_of_cross_zero _ hA
  · exact paired_observations_cross_zero _ _ _ _
      (common_flat_hessian_mixed_cross_zero hN c hc hdeg x x e htanx f)
      (common_flat_hessian_mixed_cross_zero hN c hc hdeg x y e htany g)
      (common_flat_hessian_mixed_cross_zero hN c hc hdeg y x e htanx f)
      (common_flat_hessian_mixed_cross_zero hN c hc hdeg y y e htany g)
  · exact common_bulk_pair_border_pair_cross_zero hN c hc x y v v' e htanx htany hv hv'

/-- Full actual common bulk pair is independent of both complete border
rows and corners under every specified proper value-only posterior target. -/
theorem common_bulk_border_value_independent {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y v v' : Vector N) (e : Fin m → Vector N)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (hv : ∀ i,inner ℝ (e i) v=0) (hv' : ∀ i,inner ℝ (e i) v'=0)
    (f g : Fin k → Vector N) (w : WithLp 2 (ValueObservationSpace k×ValueObservationSpace k))
    (hA : Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g))) :
    IndepFun (actualObservation (pairHilbert (flatHessianCLM c x e) (flatHessianCLM c y e)))
      (actualObservation (borderPairCLM c x y e v v'))
      (coefficientKernel (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)) w) := by
  apply coefficientKernel_independent_of_cross_zero _ hA
  · exact paired_observations_cross_zero _ _ _ _
      (common_flat_hessian_value_cross_zero hN c hc hdeg x x e htanx f)
      (common_flat_hessian_value_cross_zero hN c hc hdeg x y e htany g)
      (common_flat_hessian_value_cross_zero hN c hc hdeg y x e htanx f)
      (common_flat_hessian_value_cross_zero hN c hc hdeg y y e htany g)
  · exact common_bulk_pair_border_pair_cross_zero hN c hc x y v v' e htanx htany hv hv'

end
end SlowEquilibration.SphericalCommonHessianRegression
