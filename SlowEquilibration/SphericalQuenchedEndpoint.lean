-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalLinearEndpoint
public import Mathlib.Analysis.Calculus.Deriv.Slope

@[expose] public section

/-! Actual quenched linear spherical endpoints, including the varying variance
normalization required by a latitude of an (n+1)-dimensional sphere. -/

namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

theorem linearSphereQuenchedPressure_le_fractional {N : ℕ} (hN : 1 ≤ N)
    {κ a : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) :
    linearSphereQuenchedPressure N κ ≤ linearSphereOneStepPressure N κ a := by
  have hi : Integrable (linearSphereLogPartition N κ)
      (SYK.standardGaussianMeasureOnEuclidean (Fin N)) :=
    linearSphereLogPartition_integrable hN hκ
  have hl : Integrable (fun g => Real.log (Real.exp (a*linearSphereLogPartition N κ g)))
      (SYK.standardGaussianMeasureOnEuclidean (Fin N)) := by
    simpa only [Real.log_exp] using hi.const_mul a
  have hj := integral_log_le_log_integral _
    (exp_linearSphereLogPartition_integrable hN κ a) hl
    (.of_forall fun _ => Real.exp_pos _)
  simp only [Real.log_exp, integral_const_mul] at hj
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold linearSphereQuenchedPressure linearSphereOneStepPressure
  rw [ite_eq_right_iff.mpr (fun h => (ha.ne' h).elim)]
  apply div_le_div_of_nonneg_right _ hN0.le
  apply (le_div_iff₀ ha).mpr
  simpa only [linearSphereLogPartition, mul_comm] using hj

def quenchedLinearTrial (κ z : ℝ) : ℝ := ((z-1)-Real.log z+κ/z)/2

theorem linearEndpointTrial_tendsto_zero (κ z : ℝ) :
    Tendsto (fun a : ℝ => linearEndpointTrial κ a z 1 1)
      (𝓝[>] 0) (𝓝 (quenchedLinearTrial κ z)) := by
  have hd : HasDerivAt (fun a : ℝ => Real.log (1-a*κ/z)) (-κ/z) 0 := by
    convert (((hasDerivAt_id (0 : ℝ)).mul_const κ).div_const z).const_sub 1 |>.log (by norm_num) using 1 <;>
      simp [neg_div]
  have hs := hd.tendsto_slope_zero_right
  have hh : Tendsto (fun a : ℝ => Real.log (1-a*κ/z)/a) (𝓝[>] 0) (𝓝 (-κ/z)) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm] using hs
  have ht : Tendsto (fun a : ℝ => ((z-1)-Real.log z-Real.log (1-a*κ/z)/a)/2)
      (𝓝[>] 0) (𝓝 (((z-1)-Real.log z-(-κ/z))/2)) :=
    (tendsto_const_nhds.sub hh).div_const 2
  simpa only [linearEndpointTrial, quenchedLinearTrial, one_pow, mul_one,
    neg_div, sub_neg_eq_add] using ht

/-- A genuine thermodynamic upper endpoint for the ordinary quenched linear
spherical pressure, proved by Jensen and the fractional Gaussian-shell bound. -/
theorem linearSphereQuenchedPressure_eventually_upper {κ z : ℝ}
    (hκ : 0 ≤ κ) (hz : 1 ≤ z) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      linearSphereQuenchedPressure N κ ≤ quenchedLinearTrial κ z + ε := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have ht := (linearEndpointTrial_tendsto_zero κ z).eventually
    (gt_mem_nhds (lt_add_of_pos_right _ (half_pos hε)))
  have hc : Tendsto (fun a : ℝ => a*κ) (𝓝[>] 0) (𝓝 0) := by
    have hid : Tendsto (fun a : ℝ => a) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    simpa only [zero_mul] using hid.mul_const κ
  have hac := hc.eventually (gt_mem_nhds hz0)
  have hpos : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a := self_mem_nhdsWithin
  obtain ⟨a, ⟨ha, hcompat⟩, htrial⟩ := ((hpos.and hac).and ht).exists
  have hmain := linearSphereOneStepPressure_eventually_upper hκ ha hz hcompat (half_pos hε)
  filter_upwards [hmain, eventually_ge_atTop 1] with N hmain hN
  have hj := linearSphereQuenchedPressure_le_fractional hN hκ ha
  linarith

theorem linearSphere_partition_eq_radius {N : ℕ} (hN : 1 ≤ N) (κ : ℝ) (g : Vector N) :
    partition N 1 (fun x => Real.sqrt κ*inner ℝ g x) =
      SphereLinear.partition g (Real.sqrt κ*Real.sqrt (N : ℝ)) := by
  let : NeZero N := ⟨by omega⟩
  rw [linearSphere_partition_eq_angular hN κ zero_lt_one g]
  unfold SphereLinear.partition
  apply integral_congr_ae
  exact .of_forall fun x => by
    simp only [div_one, one_mul, real_inner_smul_left]
    congr 1
    ring

theorem linearSphereQuenchedPressure_mono {N : ℕ} (hN : 1 ≤ N)
    {κ K : ℝ} (hκ : 0 ≤ κ) (hK : κ ≤ K) :
    linearSphereQuenchedPressure N κ ≤ linearSphereQuenchedPressure N K := by
  let : NeZero N := ⟨by omega⟩
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  unfold linearSphereQuenchedPressure
  apply div_le_div_of_nonneg_right _ hN0.le
  apply integral_mono (linearSphereLogPartition_integrable hN hκ)
    (linearSphereLogPartition_integrable hN (hκ.trans hK))
  intro g
  change Real.log (partition N 1 (fun x => Real.sqrt κ*inner ℝ g x)) ≤
    Real.log (partition N 1 (fun x => Real.sqrt K*inner ℝ g x))
  rw [linearSphere_partition_eq_radius hN κ g, linearSphere_partition_eq_radius hN K g]
  apply Real.log_le_log (SphereLinear.partition_pos _ _)
  exact SphereLinear.partition_mono_radius g
    (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
    (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hK) (Real.sqrt_nonneg _))

/-- The same actual endpoint allows a convergent physical variance sequence;
only the ordinary scalar coupling converges, with no pressure-limit premise. -/
theorem linearSphereQuenchedPressure_eventually_upper_of_variance_tendsto
    (κN : ℕ → ℝ) {κ z : ℝ} (hκ : 0 ≤ κ) (hz : 1 ≤ z)
    (hκN : ∀ᶠ N : ℕ in atTop, 0 ≤ κN N) (hlim : Tendsto κN atTop (𝓝 κ))
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      linearSphereQuenchedPressure N (κN N) ≤ quenchedLinearTrial κ z + ε := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hδ : 0 < ε*z := mul_pos hε hz0
  have hupper := hlim.eventually (gt_mem_nhds (lt_add_of_pos_right κ hδ))
  have hmain := linearSphereQuenchedPressure_eventually_upper
    (show 0 ≤ κ+ε*z by linarith) hz (half_pos hε)
  have heval : quenchedLinearTrial (κ+ε*z) z = quenchedLinearTrial κ z + ε/2 := by
    unfold quenchedLinearTrial
    field_simp
    ring
  filter_upwards [hupper, hmain, hκN, eventually_ge_atTop 1] with N hupper hmain hκN hN
  have hm := linearSphereQuenchedPressure_mono hN hκN hupper.le
  rw [heval] at hmain
  linarith

end
end SlowEquilibration.SphericalModel
