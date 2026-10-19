-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GaussianRadialEnergyTilt
public import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Genuine integral regularity of the exact radial energy reweighting.
Only the original nonnegative radial density and a bounded radial interval
are used, rather than an assumed normalized tail or count limit. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 300000

def energyDensity (w : ℝ → ℝ) (U : Set ℝ) (N A B c₀ m σ : ℝ) : ℝ :=
  ∫ k in U,tiltedDensity w N A B c₀ m σ k

theorem scalar_tilt_upper {A N M : ℝ} (hA : 0 ≤ A) (hN : 0<N)
    {B c₀ m σ k : ℝ} (hk : |k-m| ≤ M) :
    -c₀*σ-B*(k-m)*σ-A*σ^2/(2*N) ≤ (|c₀|+|B| * M)*|σ| := by
  have h1 : -c₀*σ ≤ |c₀| * |σ| := by simpa only [abs_mul,neg_mul] using neg_le_abs (c₀*σ)
  have h2 : -B*(k-m)*σ ≤ |B| * M*|σ| := by
    have hh := neg_le_abs (B*(k-m)*σ)
    rw [abs_mul,abs_mul] at hh
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (abs_nonneg B))
      (abs_nonneg σ)
    nlinarith
  have hq : 0 ≤ A*σ^2/(2*N) := by positivity
  nlinarith

/-- The exact reweighted density is integrable on any bounded radial
region, for every physical energy increment. -/
theorem tiltedDensity_integrableOn {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hw : IntegrableOn w U) (h0 : ∀ k∈U,0 ≤ w k)
    {N A B c₀ m M : ℝ} (hA : 0 ≤ A) (hN : 0<N) (hRadius : ∀ k∈U,|k-m| ≤ M)
    (σ : ℝ) : IntegrableOn (tiltedDensity w N A B c₀ m σ) U := by
  have hi := hw.const_mul (Real.exp ((|c₀|+|B| * M)*|σ|))
  apply hi.mono'
  · exact hw.aestronglyMeasurable.mul
      (by fun_prop : Continuous (fun k : ℝ =>
        Real.exp (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N)))).aestronglyMeasurable
  · filter_upwards [ae_restrict_mem hU] with k hk
    have hh := Real.exp_le_exp.mpr (scalar_tilt_upper (B := B) (c₀ := c₀) (σ := σ) hA hN (hRadius k hk))
    rw [Real.norm_of_nonneg (show 0 ≤ tiltedDensity w N A B c₀ m σ k from
      mul_nonneg (h0 k hk) (Real.exp_pos _).le)]
    exact (mul_le_mul_of_nonneg_left hh (h0 k hk)).trans_eq (by ring)

/-- Continuous dependence on unnormalized physical energy follows by
actual dominated convergence against the original radial density. -/
theorem energyDensity_continuous {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hw : IntegrableOn w U) (h0 : ∀ k∈U,0 ≤ w k)
    {N A B c₀ m M : ℝ} (hA : 0 ≤ A) (hN : 0<N) (hM : 0 ≤ M)
    (hRadius : ∀ k∈U,|k-m| ≤ M) : Continuous (energyDensity w U N A B c₀ m) := by
  apply continuous_iff_continuousAt.mpr
  intro σ₀
  let C := Real.exp ((|c₀|+|B| * M)*(|σ₀|+1))
  have hCoef : 0 ≤ |c₀|+|B| * M := by positivity
  have hNear : ∀ᶠ σ : ℝ in 𝓝 σ₀,|σ| < |σ₀|+1 :=
    continuous_abs.continuousAt.eventually (gt_mem_nhds (by linarith : |σ₀| < |σ₀|+1))
  have hBound : ∀ᶠ σ : ℝ in 𝓝 σ₀,∀ᵐ k ∂volume.restrict U,
      ‖tiltedDensity w N A B c₀ m σ k‖ ≤ C*w k := by
    filter_upwards [hNear] with σ hσ
    filter_upwards [ae_restrict_mem hU] with k hk
    rw [Real.norm_of_nonneg (show 0 ≤ tiltedDensity w N A B c₀ m σ k from
      mul_nonneg (h0 k hk) (Real.exp_pos _).le)]
    have he := (Real.exp_le_exp.mpr (scalar_tilt_upper (B := B) (c₀ := c₀) (σ := σ) hA hN (hRadius k hk))).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.le hCoef))
    exact (mul_le_mul_of_nonneg_left he (h0 k hk)).trans_eq (by dsimp [C];ring)
  exact tendsto_integral_filter_of_dominated_convergence (fun k => C*w k)
    (Eventually.of_forall fun σ => (tiltedDensity_integrableOn hU hw h0 hA hN hRadius σ).aestronglyMeasurable)
    hBound (hw.const_mul C) (ae_of_all _ (fun k => by
      exact (by unfold tiltedDensity;fun_prop : Continuous (fun σ : ℝ =>
        tiltedDensity w N A B c₀ m σ k)).continuousAt.tendsto))
end SlowEquilibration.GaussianRadialEnergyTilt
