-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianBorderCovariance
public import SlowEquilibration.SphericalCommonHessianGram

/-! Genuine tensor covariance orthogonality of the complete common Hessian
bulk and both border components, before Gaussian posterior independence. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianObservationCoercivity SphericalTwoPointCovariance ScalarCoefficientCovariance
open SphericalPairRegression HessianObservationCovariance CanonicalGOERealization
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

lemma common_bulk_row_cross_zero {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y v : Vector N) (e : Fin m → Vector N)
    (htany : ∀ i,inner ℝ (e i) y=0) (hplane : ∀ i,inner ℝ (e i) v=0) :
    (flatHessianCLM c x e).comp (commonRowCLM c y e v).adjoint=0 := by
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  have h:=cross_covariance_entry (flatHessianCLM c x e) (commonRowCLM c y e v) i j
  simp only [actualObservation,flatHessianCLM_apply,commonRowCLM_apply,
    flatJetCLM_apply,unpack_euclideanDisorder] at h
  rw [common_hessian_covariance hN c hc x y _ _ _ _ (htany i.1) (htany i.2)] at h
  simp only [hplane,mul_zero,zero_mul,add_zero] at h
  change flatHessianCLM c x e ((commonRowCLM c y e v).adjoint (EuclideanSpace.basisFun (Fin m) ℝ j)) i=0
  simpa only [flatHessianCLM_apply] using h.symm

lemma common_bulk_corner_cross_zero {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x y v : Vector N) (e : Fin m → Vector N)
    (htany : ∀ i,inner ℝ (e i) y=0) (hplane : ∀ i,inner ℝ (e i) v=0) :
    (flatHessianCLM c x e).comp (flatJetCLM c 2 y ![v,v]).adjoint=0 := by
  apply ContinuousLinearMap.ext
  intro t
  apply PiLp.ext
  intro i
  have hcross : scalarCross (flatJetCLM c 2 x ![e i.1,e i.2]) (flatJetCLM c 2 y ![v,v])=0 := by
    rw [scalarCross_flatJet,common_hessian_covariance hN c hc x y _ _ _ _ (htany i.1) (htany i.2)]
    simp only [hplane,mul_zero,add_zero]
  change flatHessianCLM c x e ((flatJetCLM c 2 y ![v,v]).adjoint t) i=0
  rw [flatHessianCLM_apply,← flatJetCLM_apply]
  change (flatJetCLM c 2 x ![e i.1,e i.2]) ((flatJetCLM c 2 y ![v,v]).adjoint t)=0
  have h1 : (flatJetCLM c 2 x ![e i.1,e i.2]) ((flatJetCLM c 2 y ![v,v]).adjoint 1)=0 := hcross
  calc
    _=t • (flatJetCLM c 2 x ![e i.1,e i.2]) ((flatJetCLM c 2 y ![v,v]).adjoint 1) := by
      rw [← map_smul,← map_smul,smul_eq_mul,mul_one]
    _=0 := by rw [h1,smul_zero]

end
end SlowEquilibration.SphericalCommonHessianRegression
