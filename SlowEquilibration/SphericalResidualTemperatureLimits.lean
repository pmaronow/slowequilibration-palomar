-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTemperatureStability
public import SlowEquilibration.CSTaylorResidualCertificate
public import SlowEquilibration.MixturePlateauLocation

@[expose] public section

/-! # Genuine residual RS limits with the physical covariance correction

The static condition is imposed only at the fixed limiting temperature. The
literal dimension-corrected temperatures can lie above that static endpoint.
For the canonical plateau residual the condition is derived from actual
auxiliary Dirac minimality, rather than supplied as a residual RS assumption.
-/

namespace SlowEquilibration
noncomputable section
open Set Filter
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000

namespace SphericalModel

/-- Actual covariance-convex RS pressure at an arbitrary convergent sequence
of nonnegative temperatures, including a limiting static endpoint. -/
theorem convex_quenchedPressure_tendsto_annealed_varying_temperature
    (μ : FiniteMixture) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi)
    {β : ℝ} (hβ : 0 ≤ β) (hstatic : β ≤ Thresholds.staticThreshold μ.xi)
    (b : ℕ → ℝ) (hb0 : ∀ᶠ N in atTop, 0 ≤ b N) (hb : Tendsto b atTop (𝓝 β)) :
    Tendsto (fun N : ℕ => quenchedPressure N μ (b N)) atTop
      (𝓝 (β^2*μ.xi 1/2)) :=
  quenchedPressure_tendsto_varying_temperature μ id b hβ (eventually_ge_atTop 1)
    hb0 hb (convex_quenchedPressure_tendsto_annealed_le_static μ hconv hβ hstatic)

/-- The physical N+j covariance normalization requires no static-threshold
bound on its corrected finite-dimensional temperatures. -/
theorem convex_quenchedPressure_tendsto_annealed_dimensionCorrected
    (μ : FiniteMixture) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi)
    {β : ℝ} (hβ : 0 ≤ β) (hstatic : β ≤ Thresholds.staticThreshold μ.xi) (j : ℕ) :
    Tendsto (fun N : ℕ => quenchedPressure N μ (dimensionCorrectedTemperature β j N))
      atTop (𝓝 (β^2*μ.xi 1/2)) :=
  quenchedPressure_tendsto_dimensionCorrectedTemperature μ hβ j
    (convex_quenchedPressure_tendsto_annealed_le_static μ hconv hβ hstatic)

/-- Converting pressure per transverse dimension to pressure per ambient
dimension preserves its genuine limit. -/
theorem quenchedPressure_tendsto_dimensionCorrected_per_ambient
    (μ : FiniteMixture) {β F : ℝ} (hβ : 0 ≤ β) (j : ℕ)
    (hfixed : Tendsto (fun N : ℕ => quenchedPressure N μ β) atTop (𝓝 F)) :
    Tendsto (fun N : ℕ => ((N : ℝ)/((N+j : ℕ) : ℝ))*
      quenchedPressure N μ (dimensionCorrectedTemperature β j N)) atTop (𝓝 F) := by
  have hratio : Tendsto (fun N : ℕ => (N : ℝ)/((N+j : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add] using tendsto_natCast_div_add_atTop (j : ℝ)
  simpa only [one_mul] using hratio.mul
    (quenchedPressure_tendsto_dimensionCorrectedTemperature μ hβ j hfixed)

end SphericalModel

namespace FiniteMixture
open SphericalModel

/-- The actual finite Taylor residual has the physical varying-temperature
RS limit whenever the original covariance is convex on signed overlaps. -/
theorem taylorResidual_quenchedPressure_tendsto_dimensionCorrected
    (μ : FiniteMixture) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hright : r+s ≤ 1)
    (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β : ℝ} (hβ : 0 ≤ β)
    (hstatic : β ≤ Thresholds.staticThreshold (μ.taylorResidual hr hs).xi) (j : ℕ) :
    Tendsto (fun N : ℕ => quenchedPressure N (μ.taylorResidual hr hs)
      (dimensionCorrectedTemperature β j N)) atTop
      (𝓝 (β^2*(μ.taylorResidual hr hs).xi 1/2)) :=
  quenchedPressure_tendsto_dimensionCorrectedTemperature _ hβ j
    (μ.taylorResidual_quenchedPressure_tendsto_annealed hr hs hright hconv hβ hstatic)

/-- Nonnegative affine covariance range supplies residual convexity for
arbitrary original degree parity. -/
theorem taylorResidual_quenchedPressure_tendsto_dimensionCorrected_of_nonnegative_range
    (μ : FiniteMixture) {r s : ℝ} (hr : 0 < r) (hs : 0 < s) (hsr : s ≤ r)
    {β : ℝ} (hβ : 0 ≤ β)
    (hstatic : β ≤ Thresholds.staticThreshold (μ.taylorResidual hr hs).xi) (j : ℕ) :
    Tendsto (fun N : ℕ => quenchedPressure N (μ.taylorResidual hr hs)
      (dimensionCorrectedTemperature β j N)) atTop
      (𝓝 (β^2*(μ.taylorResidual hr hs).xi 1/2)) :=
  quenchedPressure_tendsto_dimensionCorrectedTemperature _ hβ j
    (μ.taylorResidual_quenchedPressure_tendsto_of_nonnegative_range hr hs hsr hβ hstatic)

/-- The canonical qStar residual has its actual static certificate derived
from auxiliary Dirac minimality; no residual optimality premise is imposed. -/
theorem qStar_taylorResidual_quenchedPressure_tendsto_dimensionCorrected
    (μ : FiniteMixture) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) :
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    Tendsto (fun N : ℕ => quenchedPressure N ν (dimensionCorrectedTemperature β j N))
      atTop (𝓝 (β^2*ν.xi 1/2)) := by
  exact μ.taylorResidual_quenchedPressure_tendsto_dimensionCorrected _ _
    (by linarith) hconv (μ.dynamicalThreshold_pos.trans hβ).le
    (CSTaylorResidualCertificate.qStar_taylorResidual_le_staticThreshold μ hβ) j

/-- Minimum supported degree at least three gives the genuine nonnegative
affine residual range, with arbitrary parity and no original RS premise. -/
theorem qStar_taylorResidual_quenchedPressure_tendsto_dimensionCorrected_of_minDegree
    (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) :
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    Tendsto (fun N : ℕ => quenchedPressure N ν (dimensionCorrectedTemperature β j N))
      atTop (𝓝 (β^2*ν.xi 1/2)) := by
  exact μ.taylorResidual_quenchedPressure_tendsto_dimensionCorrected_of_nonnegative_range _ _
    (by linarith [μ.half_lt_qStar hd hβ]) (μ.dynamicalThreshold_pos.trans hβ).le
    (CSTaylorResidualCertificate.qStar_taylorResidual_le_staticThreshold μ hβ) j

/-- The canonical residual annealed value, expressed in the manuscript's
literal original covariance and the genuine plateau equation. -/
theorem qStar_taylorResidual_annealed_value (μ : FiniteMixture) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) :
    let q := Thresholds.qStar μ.xi β
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    β^2*ν.xi 1/2 = (β^2*(μ.xi 1-μ.xi q)-q)/2 := by
  dsimp only
  have hq := (μ.qStar_solves_plateau hβ).1
  have hplateau := (μ.qStar_solves_plateau hβ).2
  rw [(μ.hasDerivAt_xi _).deriv] at hplateau
  have hstationary : β^2*(1-Thresholds.qStar μ.xi β)*μ.xi1
      (Thresholds.qStar μ.xi β) = Thresholds.qStar μ.xi β := by
    apply (eq_div_iff (sub_pos.mpr hq.2).ne').mp at hplateau
    nlinarith [hplateau]
  rw [μ.taylorResidual_xi,show Thresholds.qStar μ.xi β+
      (1-Thresholds.qStar μ.xi β)*(1 : ℝ) = 1 by ring]
  nlinarith [hstationary]

/-- The corrected physical residual pressure converges to the literal
plateau expression, also when β is the residual's own static endpoint. -/
theorem qStar_taylorResidual_quenchedPressure_tendsto_dimensionCorrected_value
    (μ : FiniteMixture) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) :
    let q := Thresholds.qStar μ.xi β
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    Tendsto (fun N : ℕ => quenchedPressure N ν (dimensionCorrectedTemperature β j N))
      atTop (𝓝 ((β^2*(μ.xi 1-μ.xi q)-q)/2)) := by
  have h := μ.qStar_taylorResidual_quenchedPressure_tendsto_dimensionCorrected hconv hβ j
  dsimp only at h ⊢
  rw [μ.qStar_taylorResidual_annealed_value hβ] at h
  exact h

/-- The same literal endpoint limit for arbitrary parity with minimum
supported degree at least three. -/
theorem qStar_taylorResidual_quenchedPressure_tendsto_dimensionCorrected_value_of_minDegree
    (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) :
    let q := Thresholds.qStar μ.xi β
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    Tendsto (fun N : ℕ => quenchedPressure N ν (dimensionCorrectedTemperature β j N))
      atTop (𝓝 ((β^2*(μ.xi 1-μ.xi q)-q)/2)) := by
  have h := μ.qStar_taylorResidual_quenchedPressure_tendsto_dimensionCorrected_of_minDegree hd hβ j
  dsimp only at h ⊢
  rw [μ.qStar_taylorResidual_annealed_value hβ] at h
  exact h

/-- The literal per-ambient-dimension canonical residual limit required
when the transverse sphere has ambient dimension N and physical scale N+j. -/
theorem qStar_taylorResidual_pressure_per_ambient_tendsto
    (μ : FiniteMixture) (hconv : ConvexOn ℝ (Icc (-1 : ℝ) 1) μ.xi) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) :
    let q := Thresholds.qStar μ.xi β
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    Tendsto (fun N : ℕ => ((N : ℝ)/((N+j : ℕ) : ℝ))*
      quenchedPressure N ν (dimensionCorrectedTemperature β j N)) atTop
      (𝓝 ((β^2*(μ.xi 1-μ.xi q)-q)/2)) := by
  have hratio : Tendsto (fun N : ℕ => (N : ℝ)/((N+j : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add] using tendsto_natCast_div_add_atTop (j : ℝ)
  simpa only [one_mul] using hratio.mul
    (μ.qStar_taylorResidual_quenchedPressure_tendsto_dimensionCorrected_value hconv hβ j)

/-- Arbitrary original parity has the same actual per-ambient limit once
minimum degree three proves the residual's nonnegative affine range. -/
theorem qStar_taylorResidual_pressure_per_ambient_tendsto_of_minDegree
    (μ : FiniteMixture) (hd : 3 ≤ μ.minDegree) {β : ℝ}
    (hβ : Thresholds.dynamicalThreshold μ.xi < β) (j : ℕ) :
    let q := Thresholds.qStar μ.xi β
    let ν := μ.taylorResidual (μ.qStar_solves_plateau hβ).1.1
      (sub_pos.mpr (μ.qStar_solves_plateau hβ).1.2)
    Tendsto (fun N : ℕ => ((N : ℝ)/((N+j : ℕ) : ℝ))*
      quenchedPressure N ν (dimensionCorrectedTemperature β j N)) atTop
      (𝓝 ((β^2*(μ.xi 1-μ.xi q)-q)/2)) := by
  have hratio : Tendsto (fun N : ℕ => (N : ℝ)/((N+j : ℕ) : ℝ)) atTop (𝓝 1) := by
    simpa only [Nat.cast_add] using tendsto_natCast_div_add_atTop (j : ℝ)
  simpa only [one_mul] using hratio.mul
    (μ.qStar_taylorResidual_quenchedPressure_tendsto_dimensionCorrected_value_of_minDegree hd hβ j)

end FiniteMixture
end
end SlowEquilibration
