module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalBarycenterLaw

@[expose] public section

/-! # Actual derivatives of the overlap weight and its tangent score -/
namespace SlowEquilibration.SphericalBarycenter
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 900000
open Set MeasureTheory Filter Metric
open SphericalModel SphericalForm SphericalAging.HardSphereDynamics
open scoped Topology ContDiff InnerProductSpace BigOperators
variable {N : ℕ}

/-- The literal logarithm of the positive overlap weight. -/
def logPsi (h : ℝ → ℝ) (x u : Vector N) : ℝ := -(N:ℝ)*h (overlap x u)

lemma logPsi_eq_log (h : ℝ → ℝ) (x u : Vector N) :
    logPsi h x u = Real.log (psi h x u) := by rw [psi, Real.log_exp]; rfl

lemma logPsi_joint_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) :
    ContDiff ℝ ∞ (fun z : Vector N × Vector N => logPsi h z.2 z.1) := by
  exact contDiff_const.mul (hh.comp ((contDiff_snd.inner ℝ contDiff_fst).div_const _))

lemma logPsi_contDiff {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (u : Vector N) :
    ContDiff ℝ ∞ (fun x => logPsi h x u) :=
  logPsi_joint_contDiff hh |>.comp (contDiff_const.prodMk contDiff_id)

lemma psiSq_hasFDerivAt {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x u : Vector N) :
    HasFDerivAt (fun y => (psi h y u)^2)
      ((2*(psi h x u)^2) • fderiv ℝ (fun y => logPsi h y u) x) x := by
  have hd := (((logPsi_contDiff hh u).differentiable (by simp)) x).hasFDerivAt.exp.pow 2
  convert hd using 1
  · rfl
  · simp only [psi, logPsi, two_smul, smul_smul]
    congr 1
    ring

lemma logPsi_hasGradientAt (hN : 1 ≤ N) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (x u : Vector N) : HasGradientAt (fun y => logPsi h y u)
      (-(deriv h (overlap x u)) • u) x := by
  have hNr : (N:ℝ) ≠ 0 := by exact_mod_cast (show N≠0 by omega)
  have hR : HasFDerivAt (fun y : Vector N => overlap y u)
      ((N:ℝ)⁻¹ • innerSL ℝ u) x := by
    have hd := ((innerSL ℝ u).hasFDerivAt (x := x)).const_mul (N:ℝ)⁻¹
    convert hd using 1
    · funext y
      simp only [overlap, div_eq_inv_mul]
      rw [real_inner_comm]
      rfl
  have hd := (((hh.differentiable (by simp)) (overlap x u)).hasDerivAt.comp_hasFDerivAt x hR).const_mul (-(N:ℝ))
  apply hd.congr_fderiv
  ext v
  simp only [_root_.smul_apply, smul_eq_mul,
    InnerProductSpace.toDual_apply_apply, real_inner_smul_left, innerSL_apply_apply]
  field_simp

lemma logPsi_gradient (hN : 1 ≤ N) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x u : Vector N) :
    gradient (fun y => logPsi h y u) x = -(deriv h (overlap x u)) • u :=
  (logPsi_hasGradientAt hN hh x u).gradient

/-- The actual intrinsic logarithmic score ∇_S log ψ. -/
def score (h : ℝ → ℝ) (x u : Vector N) : Vector N :=
  surfaceGradient (fun y => logPsi h y u) x

lemma score_eq (hN : 1 ≤ N) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x u : Vector N) :
    score h x u = -(deriv h (overlap x u)) • tangentProjection x u := by
  rw [score, surfaceGradient, logPsi_gradient hN hh, map_smul]

lemma score_continuous (hN : 1 ≤ N) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h) (x : Vector N) :
    Continuous (score h x) := by
  have hd : Continuous (deriv h) := hh.continuous_deriv (by simp)
  have hc : Continuous (fun u : Vector N => -(deriv h (overlap x u)) • tangentProjection x u) :=
    (hd.comp ((continuous_const.inner continuous_id).div_const _)).neg.smul (tangentProjection x).continuous
  have he : score h x = (fun u => -(deriv h (overlap x u)) • tangentProjection x u) :=
    funext (score_eq hN hh x)
  rw [he]
  exact hc

lemma psi_surfaceGradient (hN : 1 ≤ N) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (x u : Vector N) : surfaceGradient (fun y => psi h y u) x = psi h x u • score h x u := by
  have hd := (((logPsi_contDiff hh u).differentiable (by simp)) x).hasFDerivAt.exp
  apply (InnerProductSpace.toDual ℝ (Vector N)).injective
  rw [dual_surfaceGradient, map_smul, score, dual_surfaceGradient]
  rw [show fderiv ℝ (fun y => psi h y u) x = psi h x u •
      fderiv ℝ (fun y => logPsi h y u) x from hd.fderiv]
  rfl

/-- The genuine logarithmic score bound uses the actual orthogonal tangent
projection and the actual radius √N. -/
theorem score_norm_sq_le (hN : 1 ≤ N) {h : ℝ → ℝ} (hh : ContDiff ℝ ∞ h)
    (M : ℝ) (hM : 0 ≤ M) (hd : ∀ r ∈ Icc (-1:ℝ) 1, |deriv h r| ≤ M)
    (x u : Vector N) (hx : OnSphere x) (hu : OnSphere u) :
    ‖score h x u‖^2 ≤ (N:ℝ)*M^2 := by
  have hR := overlap_mem_Icc_of_norm_sq hN x u ((onSphere_iff_norm_sq x).mp hx)
    ((onSphere_iff_norm_sq u).mp hu)
  have hp : ‖tangentProjection x u‖ ≤ ‖u‖ := by
    exact ((tangentProjection x).le_opNorm u).trans
      (by simpa using mul_le_mul_of_nonneg_right (tangentProjection_norm_le (by omega) x hx) (norm_nonneg u))
  have hs : ‖score h x u‖ ≤ M*‖u‖ := by
    rw [score_eq hN hh, norm_smul, Real.norm_eq_abs, abs_neg]
    exact mul_le_mul (hd _ hR) hp (norm_nonneg _) hM
  have hn := pow_le_pow_left₀ (norm_nonneg _) hs 2
  rw [mul_pow, (onSphere_iff_norm_sq u).mp hu] at hn
  simpa only [mul_comm] using hn

end
end SlowEquilibration.SphericalBarycenter
