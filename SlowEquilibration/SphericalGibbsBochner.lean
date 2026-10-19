-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalGibbs

@[expose] public section

/-! # Genuine vector-valued integral against the actual spherical Gibbs law -/
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal physical Gibbs integral for any real normed observable. -/
theorem integral_gibbsLaw_bochner {N : ℕ} {G : Type*}
    [NormedAddCommGroup G] [NormedSpace ℝ G]
    (hN : 1≤N) (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) (f : Vector N → G) :
    (∫ u,f u ∂gibbsLaw N β H)=
      (partition N β H)⁻¹ • (∫ u,Real.exp (β*H u) • f u ∂sphereLaw N) := by
  rw [gibbsLaw,integral_withDensity_eq_integral_toReal_smul
    (gibbsDensity_continuous β hH).measurable.ennreal_ofReal
    (.of_forall fun _ => ENNReal.ofReal_lt_top)]
  simp_rw [ENNReal.toReal_ofReal (gibbsDensity_pos hN β hH _).le]
  have he : (fun u => gibbsDensity N β H u • f u)=
      fun u => (partition N β H)⁻¹ • (Real.exp (β*H u) • f u) := by
    funext u
    rw [gibbsDensity,div_eq_inv_mul,mul_smul]
  rw [he,integral_smul]

end
end SlowEquilibration.SphericalModel
