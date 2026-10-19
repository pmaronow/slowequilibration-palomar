-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourcePureLogPolynomialPhysicalWindow
public import SlowEquilibration.SourceGaussianLaplacePhysicalWindow

/-! Exact physical-coordinate identity for the logarithmically centered
microscopic latitude window. -/
@[expose] public section
namespace SlowEquilibration.SourcePureLogPolynomialPhysicalWindowUniform
noncomputable section
open Filter Set MeasureTheory SourcePureLogPolynomialLaplace
  SourcePureLogPolynomialAmplitude
open scoped Topology

/-- Once the fixed microscopic interval lies in the localization band, the
centered integral is exactly the source's physical latitude integral. -/
theorem centeredIntegral_window_eq_physical_eventually_uniform (φ a : ℝ → ℝ) (p : ℕ)
    (β cp : ℝ) {l m r α γ : ℝ}
    (hl : l < m) (hr : m < r) (hαγ : α ≤ γ) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      centeredIntegral φ a p β cp m l r (Icc α γ) n t =
        Real.sqrt (n+2 : ℕ) *
          (∫ z in m+α/Real.sqrt (n+2 : ℕ)..m+γ/Real.sqrt (n+2 : ℕ),
            a z * Real.exp ((n+2 : ℕ)*(φ z-φ m) + β*t*m^p +
              β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-m^p))) := by
  have hα := SourceGaussianLaplaceTaylor.scaled_tendsto m α
  have hγ := SourceGaussianLaplaceTaylor.scaled_tendsto m γ
  filter_upwards [hα.eventually (Ioo_mem_nhds hl hr),
    hγ.eventually (Ioo_mem_nhds hl hr)] with n hαn hγn
  intro t
  let s : ℝ := Real.sqrt (n+2 : ℕ)
  let L : ℝ := s*(l-m)
  let R : ℝ := s*(r-m)
  let f : ℝ → ℝ := fun z => a z * Real.exp ((n+2 : ℕ)*(φ z-φ m) +
    β*t*m^p + β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-m^p))
  have hs : 0 < s := by dsimp [s]; positivity
  have hs0 : s ≠ 0 := hs.ne'
  have hαmem : α ∈ Icc L R := by
    have hla : l-m ≤ α/s := by dsimp [s] at *; linarith [hαn.1]
    have hra : α/s ≤ r-m := by dsimp [s] at *; linarith [hαn.2]
    have hla' := (le_div_iff₀ hs).mp hla
    have hra' := (div_le_iff₀ hs).mp hra
    exact ⟨by dsimp [L]; nlinarith [hla'],
      by dsimp [R]; nlinarith [hra']⟩
  have hγmem : γ ∈ Icc L R := by
    have hlγ : l-m ≤ γ/s := by dsimp [s] at *; linarith [hγn.1]
    have hrγ : γ/s ≤ r-m := by dsimp [s] at *; linarith [hγn.2]
    have hla' := (le_div_iff₀ hs).mp hlγ
    have hra' := (div_le_iff₀ hs).mp hrγ
    exact ⟨by dsimp [L]; nlinarith [hla'],
      by dsimp [R]; nlinarith [hra']⟩
  have hsub : Icc α γ ⊆ Icc L R := by
    intro u hu
    exact ⟨hαmem.1.trans hu.1,hu.2.trans hγmem.2⟩
  have hpoint : ∀ u ∈ Icc α γ,
      centeredKernel φ a p β cp m l r t n u = f (m+u/s) := by
    intro u hu
    have hmem := hsub hu
    have hzphys : m+u/s ∈ Icc l r := by
      have hlo : α/s ≤ u/s := div_le_div_of_nonneg_right hu.1 hs.le
      have hhi : u/s ≤ γ/s := div_le_div_of_nonneg_right hu.2 hs.le
      exact ⟨by linarith [hαn.1,hlo],by linarith [hγn.2,hhi]⟩
    dsimp [L,R,s] at hmem hzphys
    simp only [centeredKernel, SourceGaussianLaplacePerturbed.perturbedKernel,
      centeredAmplitude, hmem, hzphys, ↓reduceIte]
    dsimp [f]
    rw [mul_assoc, ← Real.exp_add]
    congr 1
    dsimp [s]
    ring
  have hchange :
      (∫ u in α..γ, f (m+u/s)) =
        s*(∫ z in m+α/s..m+γ/s, f z) := by
    rw [intervalIntegral.integral_comp_add_div (f:=f) hs0 m]
    simp only [smul_eq_mul]
  calc
    centeredIntegral φ a p β cp m l r (Icc α γ) n t
      = ∫ u in Icc α γ, f (m+u/s) :=
        setIntegral_congr_fun measurableSet_Icc hpoint
    _ = ∫ u in α..γ, f (m+u/s) := by
      rw [intervalIntegral.integral_of_le hαγ, ← integral_Icc_eq_integral_Ioc]
    _ = s*(∫ z in m+α/s..m+γ/s, f z) := hchange
    _ = _ := rfl

/-- Symmetric physical windows agree with the microscopic integrals for
all energy shifts simultaneously after one geometry-dependent threshold. -/
theorem centeredIntegral_symmetric_window_eq_physical_eventually_uniform
    (φ a : ℝ → ℝ) (p : ℕ) (β cp : ℝ)
    {l m r w : ℝ} (hl : l < m) (hr : m < r) (hw : 0 ≤ w) :
    ∀ᶠ n : ℕ in atTop, ∀ t : ℝ,
      centeredIntegral φ a p β cp m l r (Icc (-w) w) n t =
        Real.sqrt (n+2 : ℕ) *
          (∫ z in m-w/Real.sqrt (n+2 : ℕ)..m+w/Real.sqrt (n+2 : ℕ),
            a z * Real.exp ((n+2 : ℕ)*(φ z-φ m) + β*t*m^p +
              β*(t-Real.log (n+2 : ℕ)/(2*cp))*(z^p-m^p))) := by
  filter_upwards [centeredIntegral_window_eq_physical_eventually_uniform
    φ a p β cp hl hr (by linarith : -w ≤ w)] with n hn
  intro t
  simpa only [neg_div,sub_eq_add_neg] using hn t

end
end SlowEquilibration.SourcePureLogPolynomialPhysicalWindowUniform
