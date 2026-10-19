-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLogPolynomialLaplace
public import SlowEquilibration.SourceGaussianLaplacePhysical

/-! Exact physical-coordinate interpretation of the centered logarithmic
polynomial Gaussian kernel. -/
@[expose] public section
namespace SlowEquilibration.SourcePureLogPolynomialPhysical
noncomputable section
open Set MeasureTheory SourcePureLogPolynomialLaplace
  SourcePureLogPolynomialAmplitude SourceGaussianLaplaceScaled

/-- The centered amplitude as a function of physical latitude. -/
def physicalCenteredAmplitude (a : ℝ → ℝ) (p : ℕ)
    (β cp m l r t : ℝ) (n : ℕ) (z : ℝ) : ℝ :=
  if z ∈ Icc l r then
    a z * Real.exp (β*t*m^p + β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-m^p))
  else 0

/-- The scaled and physical versions of the centered kernel agree exactly. -/
theorem centeredKernel_eq_scaledKernel (φ a : ℝ → ℝ) (p : ℕ)
    (β cp m l r t : ℝ) (n : ℕ) :
    centeredKernel φ a p β cp m l r t n =
      scaledKernel φ (physicalCenteredAmplitude a p β cp m l r t n) m l r n := by
  funext u
  rfl

/-- Exact change of variables for the log-centered local latitude integral. -/
theorem centeredIntegral_univ_eq_physical (φ a : ℝ → ℝ) (p : ℕ)
    (β cp m l r t : ℝ) (hlr : l ≤ r) (n : ℕ) :
    centeredIntegral φ a p β cp m l r Set.univ n t =
      Real.sqrt (n+2 : ℕ) *
        (∫ z in l..r, a z * Real.exp
          ((n+2 : ℕ)*(φ z-φ m) + β*t*m^p +
            β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-m^p))) := by
  rw [centeredIntegral, setIntegral_univ,
    centeredKernel_eq_scaledKernel,
    SourceGaussianLaplacePhysical.scaledKernel_integral_eq_physical
      φ (physicalCenteredAmplitude a p β cp m l r t n) m l r hlr n]
  congr 1
  apply intervalIntegral.integral_congr
  intro z hz
  have hz' : z ∈ Icc l r := by simpa only [uIcc_of_le hlr] using hz
  simp only [physicalCenteredAmplitude, hz', ↓reduceIte]
  rw [mul_assoc, ← Real.exp_add]
  congr 1
  ring

end
end SlowEquilibration.SourcePureLogPolynomialPhysical
