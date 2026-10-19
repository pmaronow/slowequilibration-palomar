-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplacePrefactor

/-! Ratios of microscopic and total latitude integrals converge to Gaussian mass ratios. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianLaplaceRatio
noncomputable section
open Filter Set MeasureTheory
open scoped Topology

/-- Gaussian mass fraction of a symmetric microscopic interval. -/
def gaussianWindowFraction (κ w : ℝ) : ℝ :=
  (∫ u in Icc (-w) w, Real.exp (-κ*u^2/2)) /
    Real.sqrt (Real.pi/(κ/2))

/-- The ratio of the physical microscopic band mass to the total local
latitude mass tends to its Gaussian probability. -/
theorem physical_window_ratio_gaussian {φ a : ℝ → ℝ}
    {m l r κ c M w : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r)) (hφmeas : Measurable φ)
    (ha : ContinuousOn a (Icc l r)) (hameas : Measurable a)
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = -κ)
    (hl : l < m) (hr : m < r) (hw : 0 ≤ w)
    (hc : 0 < c) (hκ : 0 < κ) (hM : 0 ≤ M) (ham : 0 < a m)
    (hamp : ∀ t ∈ Icc l r, |a t| ≤ M)
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2) :
    Tendsto (fun n : ℕ =>
      (∫ t in m-w/Real.sqrt (n+2 : ℕ)..m+w/Real.sqrt (n+2 : ℕ),
          a t*Real.exp ((n+2 : ℕ)*(φ t-φ m))) /
        (∫ t in l..r, a t*Real.exp ((n+2 : ℕ)*(φ t-φ m))))
      atTop (𝓝 (gaussianWindowFraction κ w)) := by
  let W : ℕ → ℝ := fun n =>
    ∫ t in m-w/Real.sqrt (n+2 : ℕ)..m+w/Real.sqrt (n+2 : ℕ),
      a t*Real.exp ((n+2 : ℕ)*(φ t-φ m))
  let T : ℕ → ℝ := fun n =>
    ∫ t in l..r, a t*Real.exp ((n+2 : ℕ)*(φ t-φ m))
  have hW := SourceGaussianLaplacePhysicalWindow.physical_local_gaussian_symmetric_window
    hφ hφmeas ha hameas hstat hcurv hl hr hw hc hM hamp henv
  have hT := SourceGaussianLaplacePhysical.physical_local_gaussian
    hφ hφmeas ha hameas hstat hcurv hl hr hc hM hamp henv
  have hG : 0 < Real.sqrt (Real.pi/(κ/2)) := by positivity
  have hdiv := hW.div hT (by positivity : a m*Real.sqrt (Real.pi/(κ/2)) ≠ 0)
  have hEq (n : ℕ) :
      (Real.sqrt (n+2 : ℕ)*W n)/(Real.sqrt (n+2 : ℕ)*T n) = W n/T n := by
    have hs : Real.sqrt (n+2 : ℕ) ≠ 0 := by positivity
    field_simp
  have hLim :
      (a m*(∫ u in Icc (-w) w, Real.exp (-κ*u^2/2))) /
          (a m*Real.sqrt (Real.pi/(κ/2))) = gaussianWindowFraction κ w := by
    unfold gaussianWindowFraction
    have ha0 : a m ≠ 0 := ham.ne'
    field_simp
  have hdiv' := hdiv.congr' (.of_forall fun n => hEq n)
  simpa only [W, T, hLim] using hdiv'

end
end SlowEquilibration.SourceGaussianLaplaceRatio
