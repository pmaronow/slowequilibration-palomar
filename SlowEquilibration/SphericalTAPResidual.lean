-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPCertificate
public import SlowEquilibration.CSLatitudeEntropyCalculus
public import SlowEquilibration.FiniteMixtureTaylorResidual
public import SlowEquilibration.SphericalParisiReplicaSymmetric

@[expose] public section

/-!
# The actual residual spherical model at a certified one-step contact

The residual is constructed as a literal finite nonnegative covariance.
Its RS potential is the negative of the original contact potential after
the source affine change of variables. Thus the actual physical residual
pressure is identified by the proved all-finite RS lower bound, without the
missing all-temperature physical Parisi formula.
-/

namespace SlowEquilibration.SphericalTAPResidual

noncomputable section
open MeasureTheory Set Filter CrisantiSommers CSParisiMeasure TwoAtomStationarity
open SphericalTAPCertificate SphericalModel
open scoped Topology

set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem inverseSquare_intervalIntegrable {x Q a b : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (ha : a < 1) (hb : b < 1) :
    IntervalIntegrable (fun t => 1 / (xHat (twoAtom x Q) t) ^ 2) volume a b := by
  let : IsProbabilityMeasure (twoAtom x Q) :=
    twoAtom_probability ⟨hx.1.le, hx.2.le⟩
  have hcut := twoAtom_hasCutoff (x := x) ⟨hQ.1.le, hQ.2⟩
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_const.div ((xHat_continuous (twoAtom x Q) hcut).continuousOn.pow 2)
  intro t ht
  have ht1 : t < 1 := ht.2.trans_lt (max_lt ha hb)
  exact pow_ne_zero 2 (xHat_pos (twoAtom x Q) hcut ht1).ne'

private theorem integral_inverseSquare_of_ge {x Q r : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1) (hQ : Q ∈ Ioo (0 : ℝ) 1)
    (hr : r < 1) (hQr : Q ≤ r) :
    (∫ t in (0 : ℝ)..r, 1 / (xHat (twoAtom x Q) t) ^ 2) =
      Q / (profileConstant x Q * (1-Q)) + (1-r)⁻¹ - (1-Q)⁻¹ := by
  have htail : (∫ t in Q..r, 1 / (xHat (twoAtom x Q) t) ^ 2) =
      (1-r)⁻¹ - (1-Q)⁻¹ := by
    rw [← integral_one_sub_inverseSquare hQ.2 hr hQr]
    apply intervalIntegral.integral_congr
    intro t ht
    have ht' : t ∈ Icc Q r := by simpa only [uIcc_of_le hQr] using ht
    change 1 / (xHat (twoAtom x Q) t) ^ 2 = 1 / (1-t) ^ 2
    rw [xHat_twoAtom ⟨hx.1.le, hx.2.le⟩ (hQ.1.le.trans ht'.1)]
    split_ifs with htQ
    · have htEq : t = Q := le_antisymm htQ ht'.1
      subst t
      congr 1
      ring
    · rfl
  rw [← intervalIntegral.integral_add_adjacent_intervals
    (inverseSquare_intervalIntegrable hx hQ (by norm_num) hQ.2)
    (inverseSquare_intervalIntegrable hx hQ hQ.2 hr),
    TwoAtomStationarity.integral_inverseSquare hx hQ, htail]
  ring

private theorem residual_hasDerivAt (μ : FiniteMixture) {Q : ℝ}
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    HasDerivAt (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi
      ((1-Q) * (μ.xi1 (Q+(1-Q)*t) - μ.xi1 Q)) t := by
  have hlin := ((hasDerivAt_id t).const_mul (1-Q)).const_add Q
  have hd := ((μ.hasDerivAt_xi (Q+(1-Q)*t)).comp t hlin).sub_const (μ.xi Q)
  have hd' := hd.sub ((hasDerivAt_id t).const_mul ((1-Q)*μ.xi1 Q))
  have heq : (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi =
      (fun u => μ.xi (Q+(1-Q)*u)-μ.xi Q-(1-Q)*μ.xi1 Q*u) := by
    ext u
    exact μ.taylorResidual_xi hQ.1 (sub_pos.mpr hQ.2) u
  rw [heq]
  convert hd' using 1
  · rfl
  · simp only [mul_one]
    ring

private theorem residual_xi1 (μ : FiniteMixture) {Q : ℝ}
    (hQ : Q ∈ Ioo (0 : ℝ) 1) (t : ℝ) :
    (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi1 t =
      (1-Q) * (μ.xi1 (Q+(1-Q)*t) - μ.xi1 Q) :=
  HasDerivAt.unique ((μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).hasDerivAt_xi t)
    (residual_hasDerivAt μ hQ t)

/-- The literal residual's Hessian coefficient is the source rescaled
second derivative, with no covariance-identification premise. -/
theorem residual_xi2_zero (μ : FiniteMixture) {Q : ℝ}
    (hQ : Q ∈ Ioo (0 : ℝ) 1) :
    (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi2 0 = (1-Q) ^ 2 * μ.xi2 Q := by
  have hlin := ((hasDerivAt_id (0 : ℝ)).const_mul (1-Q)).const_add Q
  have houter : HasDerivAt μ.xi1 (μ.xi2 Q) (Q+(1-Q)*(0 : ℝ)) := by
    simpa using μ.hasDerivAt_xi1 Q
  have hd := ((houter.comp (0 : ℝ) hlin).sub_const
    (μ.xi1 Q)).const_mul (1-Q)
  have heq : (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi1 =
      (fun t => (1-Q) * (μ.xi1 (Q+(1-Q)*t) - μ.xi1 Q)) :=
    funext (residual_xi1 μ hQ)
  have hmodel : HasDerivAt (μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).xi1
      ((1-Q) ^ 2 * μ.xi2 Q) 0 := by
    rw [heq]
    convert hd using 1
    · rfl
    · simp only [mul_one]
      ring
  exact HasDerivAt.unique
    ((μ.taylorResidual hQ.1 (sub_pos.mpr hQ.2)).hasDerivAt_xi1 0) hmodel

/-- Source Proposition 5.11(2), its exact residual/contact identity,
proved for the ordinary integral certificate and actual finite residual. -/
theorem residual_Phi_eq_neg_potential {μ : FiniteMixture}
    {β x Q t : ℝ} (h : Certificate μ β x Q) (ht : t ∈ Ioo (0 : ℝ) 1) :
    Thresholds.Phi (μ.taylorResidual h.overlap_range.1
      (sub_pos.mpr h.overlap_range.2)).xi β t =
      -CSStructure.potential μ β (twoAtom x Q) (Q+(1-Q)*t) := by
  let ν := μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)
  let F : ℝ → ℝ := fun u => firstVariation β μ.xi (twoAtom x Q) (Q+(1-Q)*u) -
    firstVariation β μ.xi (twoAtom x Q) Q - Thresholds.Phi ν.xi β u
  let : IsProbabilityMeasure (twoAtom x Q) :=
    twoAtom_probability ⟨h.weight_range.1.le, h.weight_range.2.le⟩
  have hcut := twoAtom_hasCutoff (x := x) ⟨h.overlap_range.1.le, h.overlap_range.2⟩
  have hs : 0 < 1-Q := sub_pos.mpr h.overlap_range.2
  have hd : ∀ u ∈ uIcc (0 : ℝ) t, HasDerivAt F 0 u := by
    intro u hu
    have hu' : u ∈ Icc (0 : ℝ) t := by simpa only [uIcc_of_le ht.1.le] using hu
    have hu1 : u < 1 := hu'.2.trans_lt ht.2
    have hQr : Q ≤ Q+(1-Q)*u := by nlinarith [mul_nonneg hs.le hu'.1]
    have hr1 : Q+(1-Q)*u < 1 := by nlinarith [mul_pos hs (sub_pos.mpr hu1)]
    have hlin := ((hasDerivAt_id u).const_mul (1-Q)).const_add Q
    have hφ := (firstVariation_hasDerivAt β μ.xi (twoAtom x Q) hcut hr1
      (μ.hasDerivAt_xi (Q+(1-Q)*u))).comp u hlin
    rw [integral_inverseSquare_of_ge h.weight_range h.overlap_range hr1 hQr] at hφ
    have hR := residual_hasDerivAt μ h.overlap_range u
    have hPhi := Thresholds.hasDerivAt_Phi (β := β) hR.differentiableAt hu1
    rw [hR.deriv] at hPhi
    have hstation := (TwoAtomStationarity.contact_equations μ β h.weight_range
      h.overlap_range h.contact_value h.contact_derivative).1
    convert (hφ.sub_const (firstVariation β μ.xi (twoAtom x Q) Q)).sub hPhi using 1
    · rfl
    · simp only [mul_one]
      have hfactor : 1-(Q+(1-Q)*u) = (1-Q)*(1-u) := by ring
      rw [hfactor]
      field_simp [hs.ne', show 1-u ≠ 0 by linarith,
        (profileConstant_pos h.weight_range h.overlap_range).ne'] at hstation ⊢
      nlinarith [hstation]
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hd
    (continuous_const.intervalIntegrable (0 : ℝ) t)
  have hF0 : F 0 = 0 := by simp [F, Thresholds.Phi, ν.xi_zero]
  have hFt : F t = 0 := by
    simpa only [intervalIntegral.integral_zero, hF0, sub_zero] using hFTC.symm
  have hzero : firstVariation β μ.xi (twoAtom x Q) Q = 0 := neg_eq_zero.mp h.contact_value
  dsimp [F] at hFt
  rw [hzero] at hFt
  unfold CSStructure.potential
  dsimp [ν] at hFt
  linarith

/-- The source certificate implies strict replica symmetry of its literal
finite residual throughout the whole overlap interval. -/
theorem residual_Phi_neg {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    ∀ t ∈ Ioo (0 : ℝ) 1,
      Thresholds.Phi (μ.taylorResidual h.overlap_range.1
        (sub_pos.mpr h.overlap_range.2)).xi β t < 0 := by
  intro t ht
  rw [residual_Phi_eq_neg_potential h ht]
  have hs : 0 < 1-Q := sub_pos.mpr h.overlap_range.2
  have hrt : Q < Q+(1-Q)*t := by nlinarith [mul_pos hs ht.1]
  have hr1 : Q+(1-Q)*t < 1 := by nlinarith [mul_pos hs (sub_pos.mpr ht.2)]
  exact neg_neg_of_pos (h.positive_off_contact _
    ⟨h.overlap_range.1.trans hrt, hr1⟩ (ne_of_gt hrt))

/-- The residual's own static threshold is derived from the strict
source certificate, with no residual RS or pressure premise. -/
theorem residual_le_staticThreshold {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    β ≤ Thresholds.staticThreshold
      (μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)).xi :=
  ((μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)).Phi_nonpos_iff_le_staticThreshold
    h.beta_pos.le).mp (fun t ht => (residual_Phi_neg h t ht).le)

/-- The canonical residual law is the actual zero atom. -/
theorem residual_canonical_law {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    (canonicalMinimizer
      (μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)) β).law =
      Measure.dirac (0 : ℝ) :=
  (canonicalMinimizer_law_eq_diracZero_iff _ h.beta_pos.le).mpr (residual_le_staticThreshold h)

/-- The strict source replicon inequality for the actual residual follows
from the nondegenerate original contact, including its quadratic term. -/
theorem residual_replicon_lt_one {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    β ^ 2 * (μ.taylorResidual h.overlap_range.1
      (sub_pos.mpr h.overlap_range.2)).xi2 0 < 1 := by
  rw [residual_xi2_zero μ h.overlap_range]
  have hfrac := h.edge_margin.1
  rw [markB_div_markY_sq μ h.beta_pos h.overlap_range] at hfrac
  simpa only [mul_assoc] using hfrac

/-- Source Proposition 5.11(2), its actual physical residual pressure
clause, for all source finite-mixture certificates, including odd degrees. -/
theorem residual_physical_pressure {μ : FiniteMixture} {β x Q : ℝ}
    (h : Certificate μ β x Q) :
    Tendsto (fun N : ℕ => quenchedPressure N
      (μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2)) β) atTop
      (𝓝 (β ^ 2 * (μ.xi 1 - μ.xi Q - (1-Q) * μ.xi1 Q) / 2)) := by
  have ht := general_quenchedPressure_tendsto_annealed_le_static
    (μ.taylorResidual h.overlap_range.1 (sub_pos.mpr h.overlap_range.2))
    h.beta_pos.le (residual_le_staticThreshold h)
  rw [μ.taylorResidual_xi h.overlap_range.1 (sub_pos.mpr h.overlap_range.2) 1] at ht
  simpa only [mul_one, add_sub_cancel] using ht

end
end SlowEquilibration.SphericalTAPResidual
