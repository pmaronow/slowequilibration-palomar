-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.NormalizedRadialMeasure

@[expose] public section

/-! Integrability under a normalized radial law is equivalent to weighted
Lebesgue integrability on its source interval. -/

namespace SlowEquilibration.NormalizedRadialMeasureIntegrableTransfer
noncomputable section
open MeasureTheory Set NormalizedRadialMeasure
open scoped ENNReal
set_option autoImplicit false

theorem integrable_weighted_of_law
    {f g : ℝ → ℝ} {U : Set ℝ}
    (hf : Measurable f) (hf0 : ∀ k, 0 ≤ f k)
    (hZ : 0 < ∫ k in U, f k)
    (hg : Integrable g (law f U)) :
    IntegrableOn (fun k => g k * f k) U := by
  let Z := ∫ k in U, f k
  have hfd : Measurable (fun k : ℝ => ENNReal.ofReal (f k / Z)) :=
    (hf.div_const Z).ennreal_ofReal
  have htop : ∀ᵐ k ∂volume.restrict U,
      ENNReal.ofReal (f k / Z) < ⊤ := by simp
  have hWeighted : Integrable (fun k => (f k/Z) * g k)
      (volume.restrict U) := by
    have hh := (integrable_withDensity_iff_integrable_smul' hfd htop).mp hg
    convert hh using 1
    funext k
    rw [ENNReal.toReal_ofReal (div_nonneg (hf0 k) hZ.le)]
    simp only [smul_eq_mul,Z]
  have hScale : Integrable (fun k => Z * ((f k/Z)*g k))
      (volume.restrict U) := hWeighted.const_mul Z
  apply hScale.congr
  filter_upwards with k
  have hEq : Z * ((f k/Z)*g k) = g k * f k := by
    have hZn : Z ≠ 0 := hZ.ne'
    field_simp [hZn]
  exact hEq

end
end SlowEquilibration.NormalizedRadialMeasureIntegrableTransfer
