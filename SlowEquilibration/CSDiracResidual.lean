-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CSFirstVariation
public import SlowEquilibration.CSLatitudeEntropyCalculus
public import SlowEquilibration.CSReplicaSymmetric
public import Mathlib.Analysis.Calculus.LocalExtr.Basic

@[expose] public section

/-!
# Actual Dirac minimality implies replica symmetry of the Taylor residual

Recentering the genuine first variation at its positive Dirac maximum gives
the literal replica-symmetric potential of the constant-and-linear Taylor
residual. Stationarity and the maximum are derived from actual CS minimality.
-/

namespace SlowEquilibration.CrisantiSommers

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
open Set MeasureTheory Filter
open scoped Topology

def recenteredResidual (η : ℝ → ℝ) (a t : ℝ) : ℝ :=
  η (a+(1-a)*t)-η a-(1-a)*deriv η a*t

theorem recenteredResidual_hasDerivAt {η : ℝ → ℝ} {a t : ℝ}
    (hη : DifferentiableAt ℝ η (a+(1-a)*t)) :
    HasDerivAt (recenteredResidual η a)
      ((1-a)*(deriv η (a+(1-a)*t)-deriv η a)) t := by
  have hlin := ((hasDerivAt_id t).const_mul (1-a)).const_add a
  convert ((hη.hasDerivAt.comp t hlin).sub_const (η a)).sub
    ((hasDerivAt_id t).const_mul ((1-a)*deriv η a)) using 1
  · funext u; rfl
  · simp only [mul_one]
    ring

theorem firstVariation_dirac_recentered_identity (β : ℝ) (η : ℝ → ℝ)
    (hη : ∀ t < 1, DifferentiableAt ℝ η t) {a r : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hstationary : β^2*deriv η a = a/(1-a)^2) (hr : r ∈ Ioo (0 : ℝ) 1) :
    firstVariation β η (Measure.dirac a) (a+(1-a)*r)-
      firstVariation β η (Measure.dirac a) a =
        Thresholds.Phi (recenteredResidual η a) β r := by
  have ha0 : 0 < a := ha.1
  have ha1 : a < 1 := ha.2
  let F : ℝ → ℝ := fun t =>
    firstVariation β η (Measure.dirac a) (a+(1-a)*t)-
      firstVariation β η (Measure.dirac a) a-Thresholds.Phi (recenteredResidual η a) β t
  have hder : ∀ t ∈ uIcc (0 : ℝ) r, HasDerivAt F 0 t := by
    intro t ht
    have ht' : t ∈ Icc (0 : ℝ) r := by simpa only [uIcc_of_le hr.1.le] using ht
    have ht1 : t < 1 := ht'.2.trans_lt hr.2
    have hsa : a ≤ a+(1-a)*t := by
      nlinarith [mul_nonneg (sub_pos.mpr ha1).le ht'.1]
    have hs0 : 0 ≤ a+(1-a)*t := ha.1.le.trans hsa
    have hs1 : a+(1-a)*t < 1 := by
      nlinarith [mul_pos (sub_pos.mpr ha1) (sub_pos.mpr ht1)]
    have hlin := ((hasDerivAt_id t).const_mul (1-a)).const_add a
    have hphi := (firstVariation_dirac_hasDerivAt_of_ge β η
      ⟨ha.1.le,ha.2⟩ ⟨hs0,hs1⟩ hsa (hη _ hs1).hasDerivAt).comp t hlin
    have hR := recenteredResidual_hasDerivAt (hη _ hs1)
    have hPhi := Thresholds.hasDerivAt_Phi (β := β) hR.differentiableAt ht1
    rw [hR.deriv] at hPhi
    convert (hphi.sub_const (firstVariation β η (Measure.dirac a) a)).sub hPhi using 1
    · rfl
    · simp only [mul_one]
      have hfactor : 1-(a+(1-a)*t) = (1-a)*(1-t) := by ring
      calc
        0 = (1-a)*(β^2*deriv η a-a/(1-a)^2) := by rw [hstationary]; ring
        _ = _ := by
          rw [hfactor]
          field_simp [show 1-a ≠ 0 by linarith, show 1-t ≠ 0 by linarith]
          ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hder
    (continuous_const.intervalIntegrable (0 : ℝ) r)
  have hzero : F 0 = 0 := by simp [F,recenteredResidual,Thresholds.Phi]
  have hfinal : F r = 0 := by simpa only [intervalIntegral.integral_zero,hzero,sub_zero] using hFTC.symm
  dsimp [F] at hfinal
  linarith

theorem firstVariation_dirac_maximum_of_minimizer (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ)
    (hη : ∀ t < 1, DifferentiableAt ℝ η t) {a : ℝ} (_ha : a ∈ Ioo (0 : ℝ) 1)
    (hlaw : ζ.law = Measure.dirac a) (hmin : ζ.IsMinimizer β η) :
    ∀ t ∈ Ico (0 : ℝ) 1, firstVariation β η (Measure.dirac a) t ≤
      firstVariation β η (Measure.dirac a) a := by
  have hc : ContinuousOn η (Ico (0 : ℝ) 1) := by
    intro t ht
    exact (hη t ht.2).continuousAt.continuousWithinAt
  obtain ⟨m,hmax,hsupport⟩ := (ζ.minimizer_iff_support_on_maximum β η hc).mp hmin
  rw [hlaw] at hmax hsupport
  have hm : firstVariation β η (Measure.dirac a) a = m := by simpa using hsupport
  intro t ht
  rw [hm]
  exact hmax t ht

theorem dirac_stationary_of_minimizer (ζ : Admissible) (β : ℝ) (η : ℝ → ℝ)
    (hη : ∀ t < 1, DifferentiableAt ℝ η t) {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1)
    (hlaw : ζ.law = Measure.dirac a) (hmin : ζ.IsMinimizer β η) :
    β^2*deriv η a = a/(1-a)^2 := by
  have hmax := firstVariation_dirac_maximum_of_minimizer ζ β η hη ha hlaw hmin
  have hlocal : IsLocalMax (firstVariation β η (Measure.dirac a)) a := by
    change ∀ᶠ t in 𝓝 a, firstVariation β η (Measure.dirac a) t ≤ firstVariation β η (Measure.dirac a) a
    filter_upwards [Ioo_mem_nhds ha.1 ha.2] with t ht
    exact hmax t ⟨ht.1.le,ht.2⟩
  have hd := firstVariation_dirac_hasDerivAt_of_ge β η ⟨ha.1.le,ha.2⟩
    ⟨ha.1.le,ha.2⟩ le_rfl (hη a ha.2).hasDerivAt
  have hz := hlocal.hasDerivAt_eq_zero hd
  linarith

/-- The residual replica-symmetric potential is derived from the actual
minimizer, rather than included in its hypotheses. -/
theorem recenteredResidual_Phi_nonpos_of_dirac_minimizer (ζ : Admissible)
    (β : ℝ) (η : ℝ → ℝ) (hη : ∀ t < 1, DifferentiableAt ℝ η t)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hlaw : ζ.law = Measure.dirac a)
    (hmin : ζ.IsMinimizer β η) :
    ∀ r ∈ Ioo (0 : ℝ) 1, Thresholds.Phi (recenteredResidual η a) β r ≤ 0 := by
  have hstationary := dirac_stationary_of_minimizer ζ β η hη ha hlaw hmin
  have hmax := firstVariation_dirac_maximum_of_minimizer ζ β η hη ha hlaw hmin
  intro r hr
  rw [← firstVariation_dirac_recentered_identity β η hη ha hstationary hr]
  have hs0 : 0 ≤ a+(1-a)*r := by
    have hm := mul_nonneg (sub_pos.mpr ha.2).le hr.1.le
    linarith [ha.1]
  have hs1 : a+(1-a)*r < 1 := by
    have hm := mul_pos (sub_pos.mpr ha.2) (sub_pos.mpr hr.2)
    nlinarith
  exact sub_nonpos.mpr (hmax _ ⟨hs0,hs1⟩)

/-- Any actual finite residual representing the recentered covariance is
at or below its own static threshold. -/
theorem le_staticThreshold_of_recentered_dirac_minimizer (ζ : Admissible)
    {β : ℝ} (hβ : 0 ≤ β) (η : ℝ → ℝ) (hη : ∀ t < 1, DifferentiableAt ℝ η t)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hlaw : ζ.law = Measure.dirac a)
    (hmin : ζ.IsMinimizer β η) (ν : FiniteMixture)
    (hν : ν.xi = recenteredResidual η a) : β ≤ Thresholds.staticThreshold ν.xi := by
  apply (ν.Phi_nonpos_iff_le_staticThreshold hβ).mp
  rw [hν]
  exact recenteredResidual_Phi_nonpos_of_dirac_minimizer ζ β η hη ha hlaw hmin

theorem diracZeroMinimal_of_recentered_dirac_minimizer (ζ : Admissible)
    {β : ℝ} (hβ : 0 ≤ β) (η : ℝ → ℝ) (hη : ∀ t < 1, DifferentiableAt ℝ η t)
    {a : ℝ} (ha : a ∈ Ioo (0 : ℝ) 1) (hlaw : ζ.law = Measure.dirac a)
    (hmin : ζ.IsMinimizer β η) (ν : FiniteMixture)
    (hν : ν.xi = recenteredResidual η a) : CSReplicaSymmetric.DiracZeroMinimal ν β :=
  CSReplicaSymmetric.diracZeroMinimal_of_le_staticThreshold ν hβ
    (le_staticThreshold_of_recentered_dirac_minimizer ζ hβ η hη ha hlaw hmin ν hν)

end
end SlowEquilibration.CrisantiSommers
