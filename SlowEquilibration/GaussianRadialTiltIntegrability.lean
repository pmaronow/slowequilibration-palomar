-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GaussianRadialTiltAnalysis

/-! Positivity and global energy integrability of an actual Gaussian
radial tilt, obtained from its original radial mass. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 300000

theorem scalar_tilt_lower {M : ℝ} {B c₀ m σ k A N : ℝ} (hk : |k-m| ≤ M) :
    -(|c₀|+|B| * M)*|σ|-A*σ^2/(2*N) ≤
      -c₀*σ-B*(k-m)*σ-A*σ^2/(2*N) := by
  have h1 : -(|c₀| * |σ|) ≤ -c₀*σ := by
    simpa only [abs_mul,neg_mul] using neg_le_neg (le_abs_self (c₀*σ))
  have h2 : -(|B| * M*|σ|) ≤ -B*(k-m)*σ := by
    have hh := le_abs_self (B*(k-m)*σ)
    rw [abs_mul,abs_mul] at hh
    have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hk (abs_nonneg B))
      (abs_nonneg σ)
    nlinarith
  nlinarith

theorem energyDensity_lower {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hw : IntegrableOn w U) (h0 : ∀ k∈U,0 ≤ w k)
    {N A B c₀ m M : ℝ} (hA : 0 ≤ A) (hN : 0 < N) (hRadius : ∀ k∈U,|k-m| ≤ M)
    (σ : ℝ) :
    Real.exp (- (|c₀|+|B| * M)*|σ|-A*σ^2/(2*N))*(∫ k in U,w k) ≤
      energyDensity w U N A B c₀ m σ := by
  have hl := hw.const_mul (Real.exp (- (|c₀|+|B| * M)*|σ|-A*σ^2/(2*N)))
  have hi := tiltedDensity_integrableOn (B := B) (c₀ := c₀) hU hw h0 hA hN hRadius σ
  rw [energyDensity,←integral_const_mul]
  apply integral_mono_ae hl hi
  filter_upwards [ae_restrict_mem hU] with k hk
  have he := Real.exp_le_exp.mpr
    (scalar_tilt_lower (B := B) (c₀ := c₀) (A := A) (N := N) (σ := σ) (hRadius k hk))
  change Real.exp (- (|c₀|+|B| * M)*|σ|-A*σ^2/(2*N))*w k ≤
    w k*Real.exp (-c₀*σ-B*(k-m)*σ-A*σ^2/(2*N))
  rw [mul_comm _ (w k)]
  exact mul_le_mul_of_nonneg_left he (h0 k hk)

theorem energyDensity_pos {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hw : IntegrableOn w U) (h0 : ∀ k∈U,0 ≤ w k) (hmass : 0 < ∫ k in U,w k)
    {N A B c₀ m M : ℝ} (hA : 0 ≤ A) (hN : 0 < N) (hRadius : ∀ k∈U,|k-m| ≤ M)
    (σ : ℝ) : 0 < energyDensity w U N A B c₀ m σ :=
  (mul_pos (Real.exp_pos _) hmass).trans_le (energyDensity_lower hU hw h0 hA hN hRadius σ)

/-- Completing a scalar quadratic supplies a global integrable energy
envelope without any hypothesis on the normalized upper tail. -/
theorem scalar_quadratic_envelope {A N : ℝ} (hA : 0 < A) (hN : 0 < N) (L σ : ℝ) :
    L*|σ|-A*σ^2/(2*N) ≤ N*L^2/A-A*σ^2/(4*N) := by
  have he : N*L^2/A-A*σ^2/(4*N)-(L*|σ|-A*σ^2/(2*N))=
      (A*|σ|-2*N*L)^2/(4*N*A) := by
    field_simp
    ring_nf
    simp only [sq_abs]
  rw [←sub_nonneg,he]
  positivity

theorem energyDensity_gaussian_upper {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hw : IntegrableOn w U) (h0 : ∀ k∈U,0 ≤ w k)
    {N A B c₀ m M : ℝ} (hA : 0 < A) (hN : 0 < N) (hRadius : ∀ k∈U,|k-m| ≤ M)
    (σ : ℝ) :
    energyDensity w U N A B c₀ m σ ≤
      (∫ k in U,w k)*Real.exp (N*(|c₀|+|B| * M)^2/A)*
        RadialGaussianBounds.gaussian (A/(4*N)) 0 σ := by
  have ht := tiltedDensity_integrableOn (B := B) (c₀ := c₀) hU hw h0 hA.le hN hRadius σ
  have hc := hw.const_mul (Real.exp (N*(|c₀|+|B| * M)^2/A-A*σ^2/(4*N)))
  have hh : energyDensity w U N A B c₀ m σ ≤
      ∫ k in U,Real.exp (N*(|c₀|+|B| * M)^2/A-A*σ^2/(4*N))*w k := by
    apply integral_mono_ae ht hc
    filter_upwards [ae_restrict_mem hU] with k hk
    have hq : -c₀*σ-B*(k-m)*σ-A*σ^2/(2*N) ≤
        (|c₀|+|B| * M)*|σ|-A*σ^2/(2*N) := by
      have hlin := scalar_tilt_upper (A := 0) (B := B) (c₀ := c₀) (σ := σ)
        (by rfl) hN (hRadius k hk)
      simpa only [zero_mul,zero_div,sub_zero] using sub_le_sub_right hlin (A*σ^2/(2*N))
    have he := Real.exp_le_exp.mpr (hq.trans (scalar_quadratic_envelope hA hN _ σ))
    exact (mul_le_mul_of_nonneg_left he (h0 k hk)).trans_eq (by ring)
  refine hh.trans_eq ?_
  rw [integral_const_mul,Real.exp_sub]
  unfold RadialGaussianBounds.gaussian
  rw [sub_zero]
  have he : Real.exp (-(A/(4*N))*σ^2)=Real.exp (-A*σ^2/(4*N)) := by congr 1;ring
  have hneg : -A*σ^2/(4*N)=-(A*σ^2/(4*N)) := by ring
  rw [he,hneg,Real.exp_neg]
  ring

theorem energyDensity_integrable {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hw : IntegrableOn w U) (h0 : ∀ k∈U,0 ≤ w k)
    {N A B c₀ m M : ℝ} (hA : 0 < A) (hN : 0 < N) (hM : 0 ≤ M)
    (hRadius : ∀ k∈U,|k-m| ≤ M) : Integrable (energyDensity w U N A B c₀ m) := by
  have hg := (RadialGaussianBounds.gaussian_integrable (by positivity : 0 < A/(4*N)) 0).const_mul
    ((∫ k in U,w k)*Real.exp (N*(|c₀|+|B| * M)^2/A))
  apply hg.mono'
  · exact (energyDensity_continuous hU hw h0 hA.le hN hM hRadius).aestronglyMeasurable
  · apply ae_of_all
    intro σ
    have hnonneg : 0 ≤ energyDensity w U N A B c₀ m σ := by
      apply integral_nonneg_of_ae
      filter_upwards [ae_restrict_mem hU] with k hk
      exact mul_nonneg (h0 k hk) (Real.exp_pos _).le
    rw [Real.norm_of_nonneg hnonneg]
    exact energyDensity_gaussian_upper hU hw h0 hA hN hRadius σ

end SlowEquilibration.GaussianRadialEnergyTilt
