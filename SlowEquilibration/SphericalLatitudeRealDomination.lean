-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLatitudeAverageDomination
public import SlowEquilibration.SphereSupportedIntegrals

/-! Real integral form of the true arbitrary-axis latitude disintegration.
Continuous observables are genuinely integrable on the actual sphere. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set
open SphericalForm
set_option autoImplicit false
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- A genuine latitude estimate transports to the actual sphere integral,
with actual compact-support integrability on both sides. -/
theorem latitude_integral_domination {n : ℕ} (hn : 2≤n)
    (x : Vector (n+1)) (hx : ‖x‖^2=((n+1 : ℕ) : ℝ))
    (F : Vector (n+1)→ℝ) (hF : Continuous F) (hF0 : ∀ u,0≤F u)
    (G : ℝ→ℝ) (hG : Continuous G) (hG0 : ∀ r,0≤G r)
    (hLat : ∀ r∈Ioo (-1 : ℝ) 1,
      Integrable F (latitudeLaw x (latitudeFrameAt x) r) ∧
      (∫ u,F u ∂latitudeLaw x (latitudeFrameAt x) r)≤G r) :
    Integrable F (sphereLaw (n+1)) ∧
    (∫ u,F u ∂sphereLaw (n+1))≤∫ u,G (overlap x u) ∂sphereLaw (n+1) := by
  have hiF := integrable_sphereSupported_continuous (sphereLaw (n+1))
    (sphereLaw_support (by omega)) hF
  have hGG : Continuous (fun u : Vector (n+1) => G (overlap x u)) :=
    hG.comp ((continuous_const.inner continuous_id).div_const _)
  have hiG := integrable_sphereSupported_continuous (sphereLaw (n+1))
    (sphereLaw_support (by omega)) hGG
  refine ⟨hiF,?_⟩
  have h := latitude_average_domination hn x hx (fun u => ENNReal.ofReal (F u))
    (ENNReal.measurable_ofReal.comp hF.measurable) (fun r => ENNReal.ofReal (G r))
    (ENNReal.measurable_ofReal.comp hG.measurable) ?_
  · rw [←ofReal_integral_eq_lintegral_ofReal hiF (Filter.Eventually.of_forall hF0),
      ←ofReal_integral_eq_lintegral_ofReal hiG (Filter.Eventually.of_forall (fun u => hG0 _))] at h
    exact (ENNReal.ofReal_le_ofReal_iff (integral_nonneg (fun u => hG0 _))).mp h
  · intro r hr
    rw [←ofReal_integral_eq_lintegral_ofReal (hLat r hr).1 (Filter.Eventually.of_forall hF0)]
    exact ENNReal.ofReal_le_ofReal (hLat r hr).2

end
end SlowEquilibration.SphericalModel
