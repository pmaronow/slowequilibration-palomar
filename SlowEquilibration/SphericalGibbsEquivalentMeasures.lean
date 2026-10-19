-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalSobolevGibbsTransport

/-! Positive continuous spherical Gibbs densities have the original
uniform null sets; completed graph equality is fixed by its actual value. -/
@[expose] public section
noncomputable section
open MeasureTheory Filter
namespace SlowEquilibration.SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
variable {N : ℕ}

theorem sphereLaw_absolutelyContinuous_gibbsLaw (hN : 1≤N) (β : ℝ)
    (H : Vector N→ℝ) (hH : Continuous H) : sphereLaw N ≪ gibbsLaw N β H := by
  apply withDensity_absolutelyContinuous'
  · exact (gibbsDensity_continuous β hH).measurable.ennreal_ofReal.aemeasurable
  · exact .of_forall (fun x => ne_of_gt (ENNReal.ofReal_pos.mpr (gibbsDensity_pos hN β hH x)))

theorem gibbsLaw_absolutelyContinuous_gibbsLaw (hN : 1≤N) (β₀ β₁ : ℝ)
    (H₀ H₁ : Vector N→ℝ) (hH₀ : Continuous H₀) :
    gibbsLaw N β₁ H₁ ≪ gibbsLaw N β₀ H₀ :=
  (gibbsLaw_absolutelyContinuous β₁ H₁).trans (sphereLaw_absolutelyContinuous_gibbsLaw hN β₀ H₀ hH₀)

end SlowEquilibration.SphericalModel

namespace SlowEquilibration.SphericalForm
open SphericalModel
set_option maxHeartbeats 300000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

theorem sphericalSobolevGraph_eq_of_value_ae {N : ℕ} (hN : 1≤N) (β : ℝ)
    (H : Vector N→ℝ) (hH : ContDiff ℝ 1 H)
    (u v : sphericalSobolevGraph hN β H hH.continuous)
    (huv : u.val.fst=ᵐ[gibbsLaw N β H] v.val.fst) : u=v := by
  apply sphericalEnergyL2Map_injective hN β H hH
  exact Lp.ext huv

end SlowEquilibration.SphericalForm
