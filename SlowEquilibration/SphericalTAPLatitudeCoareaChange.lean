-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPhysicalLatitudeSlice

@[expose] public section

/-! The exact scalar change of variables between the Lambert radial chart
and physical spherical latitude. The Jacobian is `r = |d(1-r²/2)/dr|`.
This is the missing calculus step between the existing genuine radial
coarea formula and manuscript Lemma 12.19's symmetric latitude integral. -/

namespace SlowEquilibration.SphericalTAPLatitudeCoareaChange
noncomputable section
open MeasureTheory Set
open SlowEquilibration.SphericalModel
set_option autoImplicit false

theorem radialLatitude_hasDerivAt (r : ℝ) :
    HasDerivAt radialLatitude (-r) r := by
  unfold radialLatitude
  convert (hasDerivAt_const r (1:ℝ)).sub
    (((hasDerivAt_id r).pow 2).div_const 2) using 1
  · funext x
    simp
  · simp

/-- Exact ordinary-integral substitution `q=1-r²/2`, with orientation
reversed because latitude decreases with positive chart radius. -/
theorem radialLatitude_interval_change (F : ℝ → ℝ) (hF : Continuous F)
    (a b : ℝ) :
    (∫ r in a..b, r*F (radialLatitude r)) =
      ∫ q in (radialLatitude b)..(radialLatitude a), F q := by
  have hsubst := intervalIntegral.integral_comp_mul_deriv
    (a := a) (b := b) (f := radialLatitude) (f' := fun r => -r) (g := F)
    (fun r _ => radialLatitude_hasDerivAt r)
    (continuous_neg.comp continuous_id).continuousOn hF
  have hneg :
      (∫ r in a..b, (F ∘ radialLatitude) r*(-r)) =
      -(∫ r in a..b, r*F (radialLatitude r)) := by
    simp_rw [show ∀ r : ℝ, (F ∘ radialLatitude) r*(-r) =
      -(r*F (radialLatitude r)) from fun r => by dsimp; ring]
    exact intervalIntegral.integral_neg
  rw [hneg] at hsubst
  have hreverse : (∫ q in (radialLatitude b)..(radialLatitude a), F q) =
      -(∫ q in (radialLatitude a)..(radialLatitude b), F q) :=
    intervalIntegral.integral_symm _ _
  rw [hreverse]
  linarith

end
end SlowEquilibration.SphericalTAPLatitudeCoareaChange
