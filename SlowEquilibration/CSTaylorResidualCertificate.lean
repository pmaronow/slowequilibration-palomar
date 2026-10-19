-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSDiracResidual
public import SlowEquilibration.CSAuxiliaryDiracCertificate
public import SlowEquilibration.FiniteMixtureTaylorResidual

@[expose] public section

/-!
# Actual static certificate for the canonical plateau Taylor residual

The genuine auxiliary Dirac minimizer is recentered through its actual first
variation. The resulting covariance is precisely the binomial finite mixture
ξ(q+(1-q)t)-ξ(q)-(1-q)ξ'(q)t. No residual RS hypothesis is used.
-/

namespace SlowEquilibration
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory CrisantiSommers

namespace FiniteMixture

theorem auxiliary_recenteredResidual_eq_taylorResidual (μ : FiniteMixture)
    {q : ℝ} (hq : q ∈ Ioo (0 : ℝ) 1) :
    (μ.taylorResidual hq.1 (sub_pos.mpr hq.2)).xi =
      recenteredResidual (μ.auxiliaryCovariance q) (latitudeDiracLocation q) := by
  funext t
  have hscale : (1-latitudeDiracLocation q)*(1-q^2) = 1-q := by
    rw [CSAuxiliaryDiracCertificate.latitudeDirac_one_sub hq.1.le]
    field_simp [show 1+q ≠ 0 by linarith [hq.1]]
    ring
  have hpoint : q^2+(1-q^2)*(latitudeDiracLocation q+(1-latitudeDiracLocation q)*t) =
      q+(1-q)*t := by
    calc
      _ = (q^2+(1-q^2)*latitudeDiracLocation q)+
          ((1-latitudeDiracLocation q)*(1-q^2))*t := by ring
      _ = _ := by rw [CSAuxiliaryDiracCertificate.latitudeDirac_affine hq.1.le,hscale]
  have hterm : (1-latitudeDiracLocation q)*((1-q^2)*μ.xi1 q)*t = (1-q)*μ.xi1 q*t := by
    calc
      _ = ((1-latitudeDiracLocation q)*(1-q^2))*μ.xi1 q*t := by ring
      _ = _ := by rw [hscale]
  rw [μ.taylorResidual_xi hq.1 (sub_pos.mpr hq.2), recenteredResidual,
    (μ.auxiliaryCovariance_hasDerivAt q (latitudeDiracLocation q)).deriv]
  simp only [FiniteMixture.auxiliaryCovariance]
  rw [hpoint,CSAuxiliaryDiracCertificate.latitudeDirac_affine hq.1.le,hterm]
  ring

end FiniteMixture

namespace CSTaylorResidualCertificate

/-- Any genuine auxiliary one-atom minimizer implies the actual static
threshold condition for its finite recentered Taylor covariance. -/
theorem taylorResidual_static_of_auxiliary_dirac_minimizer (μ : FiniteMixture)
    {β q : ℝ} (hβ : 0 ≤ β) (hq : q ∈ Ioo (0 : ℝ) 1)
    (hmin : (latitudeDiracCandidate q ⟨hq.1.le,hq.2⟩).IsMinimizer β (μ.auxiliaryCovariance q)) :
    β ≤ Thresholds.staticThreshold (μ.taylorResidual hq.1 (sub_pos.mpr hq.2)).xi := by
  have ha : latitudeDiracLocation q ∈ Ioo (0 : ℝ) 1 := by
    constructor
    · unfold latitudeDiracLocation
      exact div_pos hq.1 (by linarith [hq.1])
    · exact (latitudeDiracLocation_mem ⟨hq.1.le,hq.2⟩).2
  apply le_staticThreshold_of_recentered_dirac_minimizer
    (latitudeDiracCandidate q ⟨hq.1.le,hq.2⟩) hβ (μ.auxiliaryCovariance q)
    (fun t _ => (μ.auxiliaryCovariance_hasDerivAt q t).differentiableAt) ha rfl hmin
  exact μ.auxiliary_recenteredResidual_eq_taylorResidual hq

/-- The canonical plateau residual is at or below its own actual static
threshold for every canonical finite mixture, including all odd degrees. -/
theorem qStar_taylorResidual_le_staticThreshold (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    β ≤ Thresholds.staticThreshold
      (μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
        (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)).xi := by
  have hβ0 : 0 ≤ β := (μ.dynamicalThreshold_pos.trans hβ).le
  have hq := (μ.qStar_solves_plateau hβ).1
  exact taylorResidual_static_of_auxiliary_dirac_minimizer μ hβ0 hq
    (CSAuxiliaryDiracCertificate.latitudeDiracCandidate_isMinimizer μ hβ)

/-- Actual ordinary CS Dirac-zero minimality for the canonical finite
Taylor residual, derived from the genuine auxiliary minimizer. -/
theorem qStar_taylorResidual_diracZeroMinimal (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    CSReplicaSymmetric.DiracZeroMinimal
      (μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
        (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)) β := by
  exact CSReplicaSymmetric.diracZeroMinimal_of_le_staticThreshold _
    (μ.dynamicalThreshold_pos.trans hβ).le (qStar_taylorResidual_le_staticThreshold μ hβ)

/-- The physical auxiliary bottom certificate is genuinely non-strict.
Higher-order endpoint crossings are retained rather than excluded. -/
theorem qStar_auxiliary_bottom_weak (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    let q := Thresholds.qStar μ.xi β
    q^2*(1-q)^2*μ.xi2 q ≤ q*(1-q)*μ.xi1 q := by
  let q := Thresholds.qStar μ.xi β
  have hq : q ∈ Ioo (0 : ℝ) 1 := (μ.qStar_solves_plateau hβ).1
  have h := μ.elasticity_qStar_le hβ
  change q*μ.xi2 q/μ.xi1 q ≤ 1/(1-q) at h
  have hh := (div_le_div_iff₀ (μ.xi1_pos hq.1) (sub_pos.mpr hq.2)).mp h
  have hmul := mul_le_mul_of_nonneg_left hh
    (mul_nonneg hq.1.le (sub_pos.mpr hq.2).le)
  change q^2*(1-q)^2*μ.xi2 q ≤ q*(1-q)*μ.xi1 q
  convert hmul using 1 <;> ring

end CSTaylorResidualCertificate
end
end SlowEquilibration
