-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ExpectedCompactNormalizedLimits

/-! Converting centered upper-tail limits of an integrable intensity into
fixed-window intensity masses, without continuity at the mark cutoff. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.ExpectedTailCentering
open Set MeasureTheory Filter
open scoped Topology

theorem compact_centered_window_integral_limit
    {f : ℕ → ℝ → ℝ} (m : ℕ → ℝ) {c₀ : ℝ}
    (hi : ∀ᶠ n : ℕ in atTop, Integrable (f n))
    (htail : ∀ t : ℝ, Tendsto (fun n : ℕ => tail (f n) (m n+t))
      atTop (𝓝 (Real.exp (-c₀*t))))
    {a b : ℝ} (hab : a ≤ b) :
    Tendsto (fun n : ℕ => ∫ H in Icc (m n+a) (m n+b), f n H)
      atTop (𝓝 (Real.exp (-c₀*a)-Real.exp (-c₀*b))) := by
  have hlim := (htail a).sub (htail b)
  have he : (fun n : ℕ => tail (f n) (m n+a)-tail (f n) (m n+b)) =ᶠ[atTop]
      (fun n : ℕ => ∫ H in Icc (m n+a) (m n+b), f n H) := by
    filter_upwards [hi] with n hn
    have hDiff := intervalIntegral.integral_Ici_sub_Ici'
      (hn.integrableOn (s := Ici (m n+a)))
      (hn.integrableOn (s := Ici (m n+b)))
    change tail (f n) (m n+a)-tail (f n) (m n+b)=
      ∫ H in (m n+a)..(m n+b), f n H at hDiff
    rw [intervalIntegral.integral_of_le (by linarith : m n+a ≤ m n+b),
      ←integral_Icc_eq_integral_Ioc] at hDiff
    exact hDiff
  exact hlim.congr' he

end SlowEquilibration.ExpectedTailCentering
