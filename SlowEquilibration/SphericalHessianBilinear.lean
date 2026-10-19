-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedPairObservations
public import SlowEquilibration.SphericalHessianTraceCovariance

@[expose] public section

/-! Actual matrix Hessian pairing equals the true reconstructed directional jet. -/
namespace SlowEquilibration.SphericalHessianTraceCovariance
noncomputable section
open SphericalModel SphericalGaussianJet NormalizedPairObservations WholeFieldRegression
open GOEAsymptotics OAI.CriticalSK
open scoped BigOperators RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

theorem hessianGaussianCLM_bilinear {N P m : ℕ} (c : Degree P → ℝ) (x : Vector N)
    (e : Fin m → Vector N) (g : EuclideanDisorder N P)
    (p q : EuclideanSpace ℝ (Fin m)) :
    inner ℝ p (gaussianMatrixCLM (hessianGaussianCLM c x e g) q)=
      flatJetCLM c 2 x ![frameSum e p,frameSum e q] g := by
  simp only [PiLp.inner_apply,RCLike.inner_apply,conj_trivial]
  change (∑ i,(∑ j,hessianGaussianCLM c x e g i j*q j)*p i)=_
  simp only [flatJetCLM_apply,jet,iteratedFDeriv_two_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one,frameSum,map_sum,map_smul,
    sum_apply,smul_apply,smul_eq_mul,hessianGaussianCLM_apply,hessianEntry_eq_fderiv,
    Finset.mul_sum,Finset.sum_mul]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

end
end SlowEquilibration.SphericalHessianTraceCovariance
