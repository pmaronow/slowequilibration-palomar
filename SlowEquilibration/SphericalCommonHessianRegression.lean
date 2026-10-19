-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianUnaffectedRegression
public import SlowEquilibration.GaussianObservationCoercivity
public import SlowEquilibration.HessianObservationCovariance

/-! Complete actual common-complement Hessian pair law is unaffected by
mixed or proper pure pair conditioning, at every specified score target. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity GaussianRegressionCovariance
open NormalizedPairObservations HessianObservationCovariance SphericalHessianTraceCovariance
open SphericalConditionalMatrices GOEAsymptotics
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

lemma hessianGaussianCLM_eq_flatJet {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (g : EuclideanDisorder N P) (i j : Fin m) :
    hessianGaussianCLM c x e g i j=flatJetCLM c 2 x ![e i,e j] g := by
  simp only [hessianGaussianCLM_apply,hessianEntry,flatJetCLM_apply]

lemma common_hessian_mixed_cross_zero {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (e : Fin m → Vector N) (htany : ∀ i,inner ℝ (e i) y=0)
    (f : Fin k → Vector N) :
    (hessianGaussianCLM c x e).comp (singleMixedObservation c y f).adjoint=0 := by
  ext w i j
  change hessianGaussianCLM c x e ((singleMixedObservation c y f).adjoint w) i j=0
  rw [hessianGaussianCLM_eq_flatJet,hessian_mixed_coupling hN c hc hdeg x y]
  simp only [htany,mul_zero,zero_mul,add_zero]

lemma common_hessian_value_cross_zero {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (e : Fin m → Vector N) (htany : ∀ i,inner ℝ (e i) y=0)
    (f : Fin k → Vector N) :
    (hessianGaussianCLM c x e).comp (singleValueObservation c y f).adjoint=0 := by
  ext w i j
  change hessianGaussianCLM c x e ((singleValueObservation c y f).adjoint w) i j=0
  rw [hessianGaussianCLM_eq_flatJet,hessian_value_coupling hN c hc hdeg x y]
  simp only [htany,mul_zero,zero_mul,add_zero]

def commonHessianPair {N P m : ℕ} (c : Degree P → ℝ) (x y : Vector N)
    (e : Fin m → Vector N) : EuclideanDisorder N P →L[ℝ]
      WithLp 2 (GaussianMatrix m×GaussianMatrix m) :=
  pairHilbert (hessianGaussianCLM c x e) (hessianGaussianCLM c y e)

lemma paired_observations_cross_zero {E F G H : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G] [FiniteDimensional ℝ G]
    [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (B1 B2 : E →L[ℝ] F) (A1 : E →L[ℝ] G) (A2 : E →L[ℝ] H)
    (h11 : B1.comp A1.adjoint=0) (h12 : B1.comp A2.adjoint=0)
    (h21 : B2.comp A1.adjoint=0) (h22 : B2.comp A2.adjoint=0) :
    (pairHilbert B1 B2).comp (pairHilbert A1 A2).adjoint=0 := by
  apply ContinuousLinearMap.ext
  intro w
  apply WithLp.ofLp_injective 2
  apply Prod.ext
  · change B1 ((pairHilbert A1 A2).adjoint w)=0
    rw [pairHilbert_adjoint,map_add]
    have h1:=congrArg (fun T : G →L[ℝ] F => T w.fst) h11
    have h2:=congrArg (fun T : H →L[ℝ] F => T w.snd) h12
    change B1 (A1.adjoint w.fst)=0 at h1
    change B1 (A2.adjoint w.snd)=0 at h2
    rw [h1,h2,zero_add]
  · change B2 ((pairHilbert A1 A2).adjoint w)=0
    rw [pairHilbert_adjoint,map_add]
    have h1:=congrArg (fun T : G →L[ℝ] F => T w.fst) h21
    have h2:=congrArg (fun T : H →L[ℝ] F => T w.snd) h22
    change B2 (A1.adjoint w.fst)=0 at h1
    change B2 (A2.adjoint w.snd)=0 at h2
    rw [h1,h2,zero_add]

/-- The entire two ambient-Hessian bulk matrices retain their original
joint Gaussian law under the canonical mixed full-disorder posterior. -/
theorem common_hessian_pair_mixed_hasLaw {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (e : Fin m → Vector N)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (f g : Fin k → Vector N) (w : WithLp 2 (MixedObservationSpace k×MixedObservationSpace k))
    (_hA : Surjective (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g))) :
    HasLaw (actualObservation (commonHessianPair c x y e))
      ((stdGaussian (EuclideanDisorder N P)).map (commonHessianPair c x y e))
      (coefficientKernel (pairHilbert (singleMixedObservation c x f) (singleMixedObservation c y g)) w) := by
  apply unaffected_actualObservation_hasLaw
  exact paired_observations_cross_zero _ _ _ _
    (common_hessian_mixed_cross_zero hN c hc hdeg x x e htanx f)
    (common_hessian_mixed_cross_zero hN c hc hdeg x y e htany g)
    (common_hessian_mixed_cross_zero hN c hc hdeg y x e htanx f)
    (common_hessian_mixed_cross_zero hN c hc hdeg y y e htany g)

/-- Proper pure/value posterior, without conditioning on a redundant radial
coordinate; the complete original common-Hessian pair law remains unchanged. -/
theorem common_hessian_pair_value_hasLaw {N P m k : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (hdeg : ∀ p,c p≠0 → 3 ≤ p.val.val)
    (x y : Vector N) (e : Fin m → Vector N)
    (htanx : ∀ i,inner ℝ (e i) x=0) (htany : ∀ i,inner ℝ (e i) y=0)
    (f g : Fin k → Vector N) (w : WithLp 2 (ValueObservationSpace k×ValueObservationSpace k))
    (_hA : Surjective (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g))) :
    HasLaw (actualObservation (commonHessianPair c x y e))
      ((stdGaussian (EuclideanDisorder N P)).map (commonHessianPair c x y e))
      (coefficientKernel (pairHilbert (singleValueObservation c x f) (singleValueObservation c y g)) w) := by
  apply unaffected_actualObservation_hasLaw
  exact paired_observations_cross_zero _ _ _ _
    (common_hessian_value_cross_zero hN c hc hdeg x x e htanx f)
    (common_hessian_value_cross_zero hN c hc hdeg x y e htany g)
    (common_hessian_value_cross_zero hN c hc hdeg y x e htanx f)
    (common_hessian_value_cross_zero hN c hc hdeg y y e htany g)

end
end SlowEquilibration.SphericalCommonHessianRegression
