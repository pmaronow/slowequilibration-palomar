-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLogPolynomialAmplitude
public import SlowEquilibration.SourceGaussianLaplacePerturbedIntegrable
public import SlowEquilibration.SourceUniformMonotoneParameter

/-! Gaussian Laplace limits with the manuscript's exact `log N` polynomial
centering, including uniformity in the bounded energy shift. -/
@[expose] public section
namespace SlowEquilibration.SourcePureLogPolynomialLaplace
noncomputable section
open Set Filter MeasureTheory SourcePureLogPolynomialAmplitude
  SourceGaussianLaplacePerturbed
open scoped Topology

/-- The microscopic kernel after factoring its value at the pure-model
contact latitude. -/
def centeredKernel (φ a : ℝ → ℝ) (p : ℕ)
    (β cp m l r t : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  perturbedKernel φ (centeredAmplitude a p β cp m l r t) m l r n u

/-- Its integral on any fixed microscopic set. -/
def centeredIntegral (φ a : ℝ → ℝ) (p : ℕ)
    (β cp m l r : ℝ) (S : Set ℝ) (n : ℕ) (t : ℝ) : ℝ :=
  ∫ u in S, centeredKernel φ a p β cp m l r t n u

/-- Each finite-dimensional centered kernel is integrable. -/
theorem integrable_centeredKernel {φ a : ℝ → ℝ} {m l r c M : ℝ}
    (hφmeas : Measurable φ) (hameas : Measurable a)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ z ∈ Icc l r, |a z| ≤ M)
    (hm : |m| ≤ 1) (hband : Icc l r ⊆ Icc (-1:ℝ) 1)
    (henv : ∀ z ∈ Icc l r, φ z ≤ φ m-c*(z-m)^2)
    (p : ℕ) (β cp t : ℝ) (hcp : 0 < cp) (n : ℕ) :
    Integrable (centeredKernel φ a p β cp m l r t n) := by
  have hδ : 0 < c/2 := by linarith
  obtain ⟨B,hB,hbound⟩ := exists_gaussian_bound hM hamp hm hband
    p β cp t (c/2) hcp hδ
  exact SourceGaussianLaplacePerturbedIntegrable.integrable_perturbedKernel
    hφmeas (measurable_centeredAmplitude hameas p β cp m l r t)
    (by linarith : c/2 < c) hB hbound henv n

/-- The exact log-centered integral tends pointwise to Gaussian mass times
the energy-dependent contact amplitude. -/
theorem centeredIntegral_tendsto {φ a : ℝ → ℝ} {m l r q c M : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r)) (hφmeas : Measurable φ)
    (ha : ContinuousOn a (Icc l r)) (hameas : Measurable a)
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = q)
    (hl : l < m) (hr : m < r) (hm : m ∈ Ioo (-1:ℝ) 1)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ z ∈ Icc l r, |a z| ≤ M)
    (hband : Icc l r ⊆ Icc (-1:ℝ) 1)
    (henv : ∀ z ∈ Icc l r, φ z ≤ φ m-c*(z-m)^2)
    (p : ℕ) (β cp t : ℝ) (hcp : 0 < cp) (S : Set ℝ) :
    Tendsto (fun n : ℕ => centeredIntegral φ a p β cp m l r S n t) atTop
      (𝓝 ((a m*Real.exp (β*t*m^p))*
        ∫ u in S, Real.exp (q*u^2/2))) := by
  have hδ : 0 < c/2 := by linarith
  obtain ⟨B,hB,hbound⟩ := exists_gaussian_bound hM hamp
    ((abs_lt.mpr hm).le) hband p β cp t (c/2) hcp hδ
  have hlim := integral_perturbedKernel_tendsto hφ hφmeas hstat hcurv
    hl hr hc (by linarith : c/2 < c) hB
    (measurable_centeredAmplitude hameas p β cp m l r t)
    (centeredAmplitude_tendsto ha hl hr hm p β cp t)
    hbound henv S
  simpa only [centeredIntegral, centeredKernel, integral_const_mul] using hlim

/-- Increasing energy shifts increase the clipped source amplitude on a
positive latitude band. -/
theorem centeredAmplitude_monotone {a : ℝ → ℝ} {m l r β cp : ℝ}
    (ha : ∀ z ∈ Icc l r, 0 ≤ a z)
    (hzpos : ∀ z ∈ Icc l r, 0 ≤ z)
    (hβ : 0 ≤ β) (p n : ℕ) (u : ℝ) :
    Monotone (fun t => centeredAmplitude a p β cp m l r t n u) := by
  intro t₁ t₂ h12
  let z : ℝ := m+u/Real.sqrt (n+2 : ℕ)
  let shift : ℝ := Real.log (n+2 : ℕ)/(2*cp)
  by_cases hz : z ∈ Icc l r
  · have hpow : 0 ≤ z^p := pow_nonneg (hzpos z hz) p
    have hslope : 0 ≤ β*z^p := mul_nonneg hβ hpow
    have he : β*t₁*m^p + β*(t₁-shift)*(z^p-m^p) ≤
        β*t₂*m^p + β*(t₂-shift)*(z^p-m^p) := by
      have hid : (β*t₂*m^p + β*(t₂-shift)*(z^p-m^p))-
          (β*t₁*m^p + β*(t₁-shift)*(z^p-m^p)) =
          (β*z^p)*(t₂-t₁) := by ring
      exact sub_nonneg.mp (by rw [hid]; exact mul_nonneg hslope (sub_nonneg.mpr h12))
    simp only [centeredAmplitude,
      show m+u/Real.sqrt (n+2 : ℕ) ∈ Icc l r from hz, ↓reduceIte]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) (ha z hz)
  · simp only [centeredAmplitude,
      show m+u/Real.sqrt (n+2 : ℕ) ∉ Icc l r from hz, ↓reduceIte]
    exact le_refl _

/-- The full centered kernel is increasing in the energy shift. -/
theorem centeredKernel_monotone {φ a : ℝ → ℝ} {m l r β cp : ℝ}
    (ha : ∀ z ∈ Icc l r, 0 ≤ a z)
    (hzpos : ∀ z ∈ Icc l r, 0 ≤ z)
    (hβ : 0 ≤ β) (p n : ℕ) (u : ℝ) :
    Monotone (fun t => centeredKernel φ a p β cp m l r t n u) := by
  intro t₁ t₂ h12
  by_cases hu : u ∈ Icc (Real.sqrt (n+2 : ℕ)*(l-m))
      (Real.sqrt (n+2 : ℕ)*(r-m))
  · simp only [centeredKernel, perturbedKernel, hu, ↓reduceIte]
    exact mul_le_mul_of_nonneg_right
      ((centeredAmplitude_monotone ha hzpos hβ p n u) h12)
      (Real.exp_pos _).le
  · simp only [centeredKernel, perturbedKernel, hu, ↓reduceIte]
    exact le_refl _

/-- Latitude positivity makes the finite-dimensional local integral
monotone in the energy shift. -/
theorem centeredIntegral_monotone {φ a : ℝ → ℝ} {m l r c M β cp : ℝ}
    (hφmeas : Measurable φ) (hameas : Measurable a)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ z ∈ Icc l r, |a z| ≤ M)
    (hm : |m| ≤ 1) (hband : Icc l r ⊆ Icc (-1:ℝ) 1)
    (henv : ∀ z ∈ Icc l r, φ z ≤ φ m-c*(z-m)^2)
    (ha : ∀ z ∈ Icc l r, 0 ≤ a z)
    (hzpos : ∀ z ∈ Icc l r, 0 ≤ z)
    (hβ : 0 ≤ β) (hcp : 0 < cp)
    (p n : ℕ) (S : Set ℝ) :
    Monotone (centeredIntegral φ a p β cp m l r S n) := by
  intro t₁ t₂ h12
  apply integral_mono
    ((integrable_centeredKernel hφmeas hameas hc hM hamp hm hband
      henv p β cp t₁ hcp n).integrableOn)
    ((integrable_centeredKernel hφmeas hameas hc hM hamp hm hband
      henv p β cp t₂ hcp n).integrableOn)
  intro u
  exact (centeredKernel_monotone ha hzpos hβ p n u) h12

/-- Pointwise Gaussian limits become uniform over every compact energy
interval, using positivity and monotonicity of the exact source tilt. -/
theorem centeredIntegral_uniformOn {φ a : ℝ → ℝ} {m l r q c M β cp : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r)) (hφmeas : Measurable φ)
    (haCont : ContinuousOn a (Icc l r)) (hameas : Measurable a)
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = q)
    (hl : l < m) (hr : m < r) (hm : m ∈ Ioo (-1:ℝ) 1)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ z ∈ Icc l r, |a z| ≤ M)
    (hband : Icc l r ⊆ Icc (-1:ℝ) 1)
    (henv : ∀ z ∈ Icc l r, φ z ≤ φ m-c*(z-m)^2)
    (ha : ∀ z ∈ Icc l r, 0 ≤ a z)
    (hzpos : ∀ z ∈ Icc l r, 0 ≤ z)
    (hβ : 0 ≤ β) (hcp : 0 < cp)
    (p : ℕ) (S U : Set ℝ) (hU : IsCompact U) :
    TendstoUniformlyOn
      (fun n t => centeredIntegral φ a p β cp m l r S n t)
      (fun t => (a m*Real.exp (β*t*m^p))*
        ∫ u in S, Real.exp (q*u^2/2)) atTop U := by
  apply SourceUniformMonotoneParameter.uniform_on_compact_of_monotone
  · intro n
    exact centeredIntegral_monotone hφmeas hameas hc hM hamp
      ((abs_lt.mpr hm).le) hband henv ha hzpos hβ hcp p n S
  · fun_prop
  · intro t
    exact centeredIntegral_tendsto hφ hφmeas haCont hameas hstat hcurv
      hl hr hm hc hM hamp hband henv p β cp t hcp S
  · exact hU

end
end SlowEquilibration.SourcePureLogPolynomialLaplace
