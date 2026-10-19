-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.GaussianRadialTiltAnalysis
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-! Exact physical-energy differentiation under the true radial integral.
A bounded radial interval and its original integrable density supply the
local derivative majorant, rather than an assumed differentiability premise. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.GaussianRadialEnergyTilt
open Set MeasureTheory Filter
open scoped Topology
set_option maxHeartbeats 400000

def energyScore (N A B c₀ m σ k : ℝ) : ℝ := c₀+B*(k-m)+A*σ/N

theorem tiltedDensity_hasDerivAt (w : ℝ → ℝ) {N : ℝ} (hN : N ≠ 0)
    (A B c₀ m σ k : ℝ) :
    HasDerivAt (fun v => tiltedDensity w N A B c₀ m v k)
      (-energyScore N A B c₀ m σ k*tiltedDensity w N A B c₀ m σ k) σ := by
  have hPoly : HasDerivAt (fun v : ℝ => -c₀*v-B*(k-m)*v-A*v^2/(2*N))
      (-energyScore N A B c₀ m σ k) σ := by
    convert (((hasDerivAt_id σ).const_mul (-c₀)).sub
      ((hasDerivAt_id σ).const_mul (B*(k-m)))).sub
      ((((hasDerivAt_id σ).pow 2).const_mul A).div_const (2*N)) using 1
    · funext v
      simp only [Pi.sub_apply,Pi.pow_apply,id_eq]
    · unfold energyScore
      field_simp [hN]
      norm_num [id_eq]
      ring
  convert hPoly.exp.const_mul (w k) using 1
  · rfl
  · unfold tiltedDensity
    ring

theorem energyScore_abs_bound {N A B c₀ m M σ k r : ℝ} (hN : 0 < N)
    (_hM : 0 ≤ M) (hk : |k-m| ≤ M) (hσ : |σ| ≤ r) :
    |energyScore N A B c₀ m σ k| ≤ |c₀|+|B| *M+|A| *r/N := by
  have h1 := abs_add_le c₀ (B*(k-m))
  have h2 := abs_add_le (c₀+B*(k-m)) (A*σ/N)
  have hB := mul_le_mul_of_nonneg_left hk (abs_nonneg B)
  have hA := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hσ (abs_nonneg A)) hN.le
  simp only [abs_mul,abs_div,abs_of_pos hN] at h1 h2
  unfold energyScore
  linarith

/-- Genuine derivative under the integral at every physical energy. -/
theorem energyDensity_hasDerivAt {w : ℝ → ℝ} {U : Set ℝ} (hU : MeasurableSet U)
    (hw : IntegrableOn w U) (h0 : ∀ k ∈ U,0 ≤ w k)
    {N A B c₀ m M : ℝ} (hA : 0 ≤ A) (hN : 0 < N) (hM : 0 ≤ M)
    (hRadius : ∀ k ∈ U,|k-m| ≤ M) (σ₀ : ℝ) :
    IntegrableOn (fun k => -energyScore N A B c₀ m σ₀ k*tiltedDensity w N A B c₀ m σ₀ k) U ∧
    HasDerivAt (energyDensity w U N A B c₀ m)
      (∫ k in U,-energyScore N A B c₀ m σ₀ k*tiltedDensity w N A B c₀ m σ₀ k) σ₀ := by
  let r := |σ₀|+1
  let C := Real.exp ((|c₀|+|B| *M)*r)
  let D := |c₀|+|B| *M+|A| *r/N
  let s : Set ℝ := {σ | |σ| < r}
  have hCoef : 0 ≤ |c₀|+|B| *M := by positivity
  have hD : 0 ≤ D := by dsimp [D,r];positivity
  have hs : s ∈ 𝓝 σ₀ := by
    exact continuous_abs.continuousAt.preimage_mem_nhds
      (Iio_mem_nhds (by dsimp [r];linarith : |σ₀| < r))
  have hF (σ : ℝ) := tiltedDensity_integrableOn (B := B) (c₀ := c₀) hU hw h0 hA hN hRadius σ
  have hMeas : AEStronglyMeasurable
      (fun k => -energyScore N A B c₀ m σ₀ k*tiltedDensity w N A B c₀ m σ₀ k) (volume.restrict U) :=
    (by unfold energyScore;fun_prop : Continuous (fun k : ℝ => -energyScore N A B c₀ m σ₀ k)).aestronglyMeasurable.mul
      (hF σ₀).aestronglyMeasurable
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le hs
    (Eventually.of_forall fun σ => (hF σ).aestronglyMeasurable) (hF σ₀) hMeas
    (by
      filter_upwards [ae_restrict_mem hU] with k hk
      intro σ hσ
      have hscore : |energyScore N A B c₀ m σ k| ≤ D :=
        energyScore_abs_bound (A := A) (B := B) (c₀ := c₀) hN hM (hRadius k hk) (le_of_lt hσ)
      have hTilt : |tiltedDensity w N A B c₀ m σ k| ≤ C*w k := by
        rw [abs_of_nonneg (show 0 ≤ tiltedDensity w N A B c₀ m σ k from
          mul_nonneg (h0 k hk) (Real.exp_pos _).le)]
        have hExp := (Real.exp_le_exp.mpr (scalar_tilt_upper (B := B) (c₀ := c₀) (σ := σ) hA hN
          (hRadius k hk))).trans (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hσ.le hCoef))
        exact (mul_le_mul_of_nonneg_left hExp (h0 k hk)).trans_eq (by dsimp [C];ring)
      rw [Real.norm_eq_abs,abs_mul,abs_neg]
      exact (mul_le_mul hscore hTilt (abs_nonneg _) hD).trans_eq (by ring))
    (hw.const_mul (D*C))
    (ae_of_all _ (fun k σ _ => tiltedDensity_hasDerivAt w hN.ne' A B c₀ m σ k))
end SlowEquilibration.GaussianRadialEnergyTilt
