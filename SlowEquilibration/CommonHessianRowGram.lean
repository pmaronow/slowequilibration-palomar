-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianBorderCovariance
public import SlowEquilibration.SphericalPairBorderedFrame

/-! Actual common Hessian border-row covariance is b/N times identity;
Gaussian regression decreases its true covariance on the row's own space. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance SphericalPairCommonFrame
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

/-- True row covariance in an arbitrary orthonormal tangent common frame
with a unit orthogonal border direction; no GOE row-law input. -/
theorem commonRowCLM_gram {N P m : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (e : Fin m → Vector N) (he : Orthonormal ℝ e) (htan : ∀ i,inner ℝ (e i) x=0)
    (v : Vector N) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) (hve : ∀ i,inner ℝ (e i) v=0) :
    GaussianRegression.gram (commonRowCLM c x e v)=(secondCovariance c 1/(N:ℝ)) •
      ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)) := by
  let fullFrame : Fin (m+1) → Vector N := Fin.cons v e
  have hfull : Orthonormal ℝ fullFrame:=orthonormal_fin_cons e he v hv hve
  have hfulltan : ∀ i : Fin (m+1),inner ℝ (fullFrame i) x=0 := by
    intro i
    refine Fin.cases hvtan (fun i=>htan i) i
  apply ContinuousLinearMap.coe_injective
  apply (EuclideanSpace.basisFun (Fin m) ℝ).toBasis.ext
  intro j
  apply PiLp.ext
  intro i
  have h:=actual_covariance_gram (commonRowCLM c x e v) i j
  simp only [actualObservation,commonRowCLM_apply,flatJetCLM_apply,unpack_euclideanDisorder] at h
  change cov[hessianEntry c x fullFrame i.succ 0,
    hessianEntry c x fullFrame j.succ 0;disorderLaw N P]=_ at h
  rw [hessianEntry_covariance (r:=1) hN c hc x (by simpa using hx) _ hfull hfulltan] at h
  change GaussianRegression.gram (commonRowCLM c x e v) (EuclideanSpace.basisFun (Fin m) ℝ j) i=
    ((secondCovariance c 1/(N:ℝ)) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin m)))
      (EuclideanSpace.basisFun (Fin m) ℝ j) i
  rw [← h]
  simp [EuclideanSpace.basisFun_apply,eq_comm]

end
end SlowEquilibration.SphericalCommonHessianRegression
