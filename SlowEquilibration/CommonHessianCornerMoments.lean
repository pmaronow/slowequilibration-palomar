-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianRowMoments
public import SlowEquilibration.SphericalCommonHessianCovariance

/-! Actual Gaussian Hessian corner covariance 2b/N and uniform ordinary
posterior centered corner norm moments, with no moment premises. -/
@[expose] public section
namespace SlowEquilibration.SphericalCommonHessianRegression
noncomputable section
open Function MeasureTheory ProbabilityTheory SphericalModel SphericalGaussianJet WholeFieldRegression
open GaussianRegression GaussianRegressionCovariance GaussianVectorPolynomialMoments SphericalTwoPointCovariance
open ScalarCoefficientCovariance
open scoped RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000
variable {F : Type*}
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

def cornerCLM {N P : ℕ} (c : Degree P → ℝ) (x v : Vector N) : EuclideanDisorder N P →L[ℝ] ℝ :=
  flatJetCLM c 2 x ![v,v]

/-- Literal corner covariance, including the factor two on the GOE diagonal. -/
theorem cornerCLM_gram {N P : ℕ} (hN : 0 < N) (c : Degree P → ℝ)
    (hc : ∀ p,0 ≤ c p) (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (v : Vector N) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0) :
    gram (cornerCLM c x v)=(2*secondCovariance c 1/(N:ℝ)) • ContinuousLinearMap.id ℝ ℝ := by
  have hr : overlap x x=1 := by
    unfold overlap
    rw [real_inner_self_eq_norm_sq,hx,div_self (by exact_mod_cast hN.ne')]
  have hcov : scalarCross (cornerCLM c x v) (cornerCLM c x v)=2*secondCovariance c 1/(N:ℝ) := by
    rw [cornerCLM,scalarCross_flatJet,common_hessian_covariance hN c hc x x v v v v hvtan hvtan,
      hr,real_inner_self_eq_norm_sq,hv]
    norm_num
    ring
  apply ContinuousLinearMap.ext
  intro t
  change cornerCLM c x v ((cornerCLM c x v).adjoint t)=(2*secondCovariance c 1/(N:ℝ))*t
  calc
    _=t • cornerCLM c x v ((cornerCLM c x v).adjoint 1) := by
      rw [← map_smul,← map_smul,smul_eq_mul,mul_one]
    _=t*(2*secondCovariance c 1/(N:ℝ)) := by rw [show cornerCLM c x v ((cornerCLM c x v).adjoint 1)=_ from hcov];rfl
    _=_ := by ring

/-- Genuine posterior centered corner norm moments are bounded uniformly
in every sphere dimension and every observation target. -/
theorem conditional_corner_norm_moments {N P : ℕ} (hN : 0 < N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (hb : 0 < secondCovariance c 1)
    (x : Vector N) (hx : ‖x‖^2=(N:ℝ))
    (v : Vector N) (hv : ‖v‖=1) (hvtan : inner ℝ v x=0)
    (A : EuclideanDisorder N P →L[ℝ] F) (hA : Surjective A) :
    ∀ r:ℕ,Integrable (fun u:ℝ=>‖u‖^r) (centeredLaw A (cornerCLM c x v)) ∧
      (∫ u,‖u‖^r ∂centeredLaw A (cornerCLM c x v)) ≤
        (r.factorial:ℝ)*Real.exp (Real.sqrt (2*secondCovariance c 1)+secondCovariance c 1) := by
  let τ:=2*secondCovariance c 1/(N:ℝ)
  have hτ : 0 < τ:=div_pos (mul_pos (by norm_num) hb) (Nat.cast_pos.mpr hN)
  have hcov (u:ℝ) : covarianceBilin (centeredLaw A (cornerCLM c x v)) u u ≤ (Real.sqrt τ)^2*‖u‖^2 := by
    have hh:=centeredLaw_covariance_le_gram A hA (cornerCLM c x v) u
    rw [cornerCLM_gram hN c hc x hx v hv hvtan] at hh
    simpa only [smul_apply,ContinuousLinearMap.id_apply,real_inner_smul_right,
      real_inner_self_eq_norm_sq,Real.sq_sqrt hτ.le] using hh
  have hτbound : τ ≤ 2*secondCovariance c 1:=div_le_self (by positivity) (by exact_mod_cast hN)
  have hscale : Real.sqrt τ*Real.sqrt (Module.finrank ℝ ℝ:ℝ) ≤ Real.sqrt (2*secondCovariance c 1) := by
    simp only [Module.finrank_self,Nat.cast_one,Real.sqrt_one,mul_one]
    exact Real.sqrt_le_sqrt hτbound
  intro r
  have hh:=centered_gaussian_norm_moments (centeredLaw A (cornerCLM c x v)) (centeredLaw_mean A _)
    (Real.sqrt_pos.mpr hτ) hcov hscale r
  refine ⟨hh.1,hh.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  apply Real.exp_le_exp.mpr
  rw [Real.sq_sqrt hτ.le]
  linarith

end
end SlowEquilibration.SphericalCommonHessianRegression
