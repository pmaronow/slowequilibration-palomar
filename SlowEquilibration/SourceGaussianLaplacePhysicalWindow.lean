-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SourceGaussianLaplacePhysical

/-! A fixed microscopic interval corresponds to a shrinking physical interval. -/
@[expose] public section
namespace SlowEquilibration.SourceGaussianLaplacePhysicalWindow
noncomputable section
open Filter Set MeasureTheory SourceGaussianLaplaceScaled
open scoped Topology

/-- Once the physical localization contains a fixed microscopic window,
its integral is exactly the change-of-variables image of that window. -/
theorem scaledKernel_window_eq_physical_eventually (φ a : ℝ → ℝ)
    {l m r α β : ℝ} (hl : l < m) (hr : m < r) (hαβ : α ≤ β) :
    ∀ᶠ n : ℕ in atTop,
      (∫ u in Icc α β, scaledKernel φ a m l r n u) =
        Real.sqrt (n+2 : ℕ) *
          (∫ t in m+α/Real.sqrt (n+2 : ℕ)..m+β/Real.sqrt (n+2 : ℕ),
            a t*Real.exp ((n+2 : ℕ)*(φ t-φ m))) := by
  have hα := SourceGaussianLaplaceTaylor.scaled_tendsto m α
  have hβ := SourceGaussianLaplaceTaylor.scaled_tendsto m β
  filter_upwards [hα.eventually (Ioo_mem_nhds hl hr),
    hβ.eventually (Ioo_mem_nhds hl hr)] with n hαn hβn
  let s : ℝ := Real.sqrt (n+2 : ℕ)
  let L : ℝ := s*(l-m)
  let R : ℝ := s*(r-m)
  let f : ℝ → ℝ := fun t => a t*Real.exp ((n+2 : ℕ)*(φ t-φ m))
  have hs : 0 < s := by dsimp [s]; positivity
  have hs0 : s ≠ 0 := hs.ne'
  have hαmem : α ∈ Icc L R := by
    have hla : l-m ≤ α/s := by dsimp [s] at *; linarith [hαn.1]
    have hra : α/s ≤ r-m := by dsimp [s] at *; linarith [hαn.2]
    have hla' := (le_div_iff₀ hs).mp hla
    have hra' := (div_le_iff₀ hs).mp hra
    exact ⟨by dsimp [L]; nlinarith [hla'],
      by dsimp [R]; nlinarith [hra']⟩
  have hβmem : β ∈ Icc L R := by
    have hlb : l-m ≤ β/s := by dsimp [s] at *; linarith [hβn.1]
    have hrb : β/s ≤ r-m := by dsimp [s] at *; linarith [hβn.2]
    have hlb' := (le_div_iff₀ hs).mp hlb
    have hrb' := (div_le_iff₀ hs).mp hrb
    exact ⟨by dsimp [L]; nlinarith [hlb'],
      by dsimp [R]; nlinarith [hrb']⟩
  have hsub : Icc α β ⊆ Icc L R := by
    intro u hu
    exact ⟨hαmem.1.trans hu.1,hu.2.trans hβmem.2⟩
  have hpoint : ∀ u ∈ Icc α β, scaledKernel φ a m l r n u = f (m+u/s) := by
    intro u hu
    have hmem := hsub hu
    dsimp [L,R,s] at hmem
    simp only [scaledKernel, hmem, ↓reduceIte]
    rfl
  have hchange :
      (∫ u in α..β, f (m+u/s)) = s*(∫ t in m+α/s..m+β/s, f t) := by
    rw [intervalIntegral.integral_comp_add_div (f:=f) hs0 m]
    simp only [smul_eq_mul]
  calc
    (∫ u in Icc α β, scaledKernel φ a m l r n u)
      = ∫ u in Icc α β, f (m+u/s) :=
        setIntegral_congr_fun measurableSet_Icc hpoint
    _ = ∫ u in α..β, f (m+u/s) := by
      rw [intervalIntegral.integral_of_le hαβ, ← integral_Icc_eq_integral_Ioc]
    _ = s*(∫ t in m+α/s..m+β/s, f t) := hchange
    _ = _ := rfl

/-- The centered physical window has its exact Gaussian limiting mass. -/
theorem physical_local_gaussian_window {φ a : ℝ → ℝ}
    {m l r κ c M α β : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r)) (hφmeas : Measurable φ)
    (ha : ContinuousOn a (Icc l r)) (hameas : Measurable a)
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = -κ)
    (hl : l < m) (hr : m < r) (hαβ : α ≤ β)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ t ∈ Icc l r, |a t| ≤ M)
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2) :
    Tendsto (fun n : ℕ => Real.sqrt (n+2 : ℕ) *
      (∫ t in m+α/Real.sqrt (n+2 : ℕ)..m+β/Real.sqrt (n+2 : ℕ),
        a t*Real.exp ((n+2 : ℕ)*(φ t-φ m)))) atTop
      (𝓝 (a m * ∫ u in Icc α β, Real.exp (-κ*u^2/2))) := by
  have h := SourceGaussianLaplaceLocal.integral_scaledKernel_window_local
    (α:=α) (β:=β)
    hφ hφmeas ha hameas hstat hcurv hl hr hc hM hamp henv
  exact h.congr' (scaledKernel_window_eq_physical_eventually φ a hl hr hαβ)

/-- The symmetric physical window used for the pure-model band calculation. -/
theorem physical_local_gaussian_symmetric_window {φ a : ℝ → ℝ}
    {m l r κ c M w : ℝ}
    (hφ : ContDiffOn ℝ 2 φ (Ioo l r)) (hφmeas : Measurable φ)
    (ha : ContinuousOn a (Icc l r)) (hameas : Measurable a)
    (hstat : derivWithin φ (Ioo l r) m = 0)
    (hcurv : iteratedDerivWithin 2 φ (Ioo l r) m = -κ)
    (hl : l < m) (hr : m < r) (hw : 0 ≤ w)
    (hc : 0 < c) (hM : 0 ≤ M)
    (hamp : ∀ t ∈ Icc l r, |a t| ≤ M)
    (henv : ∀ t ∈ Icc l r, φ t ≤ φ m-c*(t-m)^2) :
    Tendsto (fun n : ℕ => Real.sqrt (n+2 : ℕ) *
      (∫ t in m-w/Real.sqrt (n+2 : ℕ)..m+w/Real.sqrt (n+2 : ℕ),
        a t*Real.exp ((n+2 : ℕ)*(φ t-φ m)))) atTop
      (𝓝 (a m * ∫ u in Icc (-w) w, Real.exp (-κ*u^2/2))) := by
  simpa only [neg_div, sub_eq_add_neg] using
    (physical_local_gaussian_window (α:=-w) (β:=w)
      hφ hφmeas ha hameas hstat hcurv hl hr (by linarith)
      hc hM hamp henv)

end
end SlowEquilibration.SourceGaussianLaplacePhysicalWindow
