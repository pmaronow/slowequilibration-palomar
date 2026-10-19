-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.CSPureModels
public import SlowEquilibration.SphericalTAPCertificate

/-! The source strict one-step certificate for every proper pure model above
its actual static threshold, obtained from its canonical minimizer. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalTAPCertificate
open Set CrisantiSommers CSParisiMeasure
set_option autoImplicit false

theorem pure_certificate_above_static (p : ℕ) (hp : 4 ≤ p)
    {β : ℝ} (hβ : Thresholds.staticThreshold (fun r : ℝ => r^p) < β) :
    ∃ x Q : ℝ, Certificate
      (FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity)) β x Q := by
  let μ := FiniteMixture.pure p (by omega : 2 ≤ p) 1 (by positivity : (0 : ℝ) < 1)
  have hξ : μ.xi = (fun r : ℝ => r^p) := by
    funext r
    simp only [μ, FiniteMixture.pure_xi, one_mul]
  have hgt : Thresholds.staticThreshold μ.xi < β := by rwa [hξ]
  obtain ⟨x,hx,Q,hQ,hlaw,hvalue,hderiv,hcurv,hpositive⟩ :=
    CSPureModels.pure_canonicalMinimizer_strict_oneStep p (by omega)
      1 (by positivity) hgt
  refine ⟨x,Q,?_⟩
  refine {
    min_degree := ?_
    beta_pos := μ.staticThreshold_pos.trans hgt
    weight_range := hx
    overlap_range := hQ
    contact_value := ?_
    contact_derivative := ?_
    positive_off_contact := ?_
    contact_curvature := ?_ }
  · rw [(CSPureModels.pure_degrees p (by omega) 1 (by positivity)).1]
    exact hp
  · rwa [← hlaw]
  · rwa [← hlaw]
  · intro r hr hrQ
    rw [← hlaw]
    exact hpositive r hr hrQ
  · rwa [← hlaw]

end SlowEquilibration.SphericalTAPCertificate
