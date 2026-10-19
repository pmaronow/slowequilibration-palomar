-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphereShellPressure
public import SlowEquilibration.SphericalFractionalPressure
public import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual normalized spherical one-step linear endpoint. Gaussian shell
mass is proved from the exact Gaussian law, rather than supplied as an
asymptotic pressure hypothesis. -/

@[expose] public section
namespace SlowEquilibration.SphericalModel
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped RealInnerProductSpace Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

theorem linearSphere_partition_eq_angular {N : ℕ} (hN : 1 ≤ N) (κ : ℝ)
    {t : ℝ} (ht : 0 < t) (g : Vector N) :
    partition N 1 (fun x => Real.sqrt κ * inner ℝ g x) =
      SphereLinear.partition ((Real.sqrt κ / t) • g) (t * Real.sqrt (N : ℝ)) := by
  let : NeZero N := ⟨by omega⟩
  rw [partition, sphereLaw, SphereVolume.sphereLaw_eq_normalized_angular N hN,
    integral_map (by fun_prop) (by fun_prop), SphereLinear.partition_eq_angular]
  apply integral_congr_ae
  exact .of_forall fun u => by
    simp only [one_mul, real_inner_smul_right, real_inner_smul_left]
    congr 1
    field_simp

theorem radial_shell_mass_eq {N : ℕ} (hN : 1 ≤ N) {t u : ℝ} (ht : 0 ≤ t) (hu : 0 ≤ u) :
    (SphereVolume.gaussianRadius (Vector N)).real
      {r : Ioi (0 : ℝ) | t * Real.sqrt (N : ℝ) ≤ (r : ℝ) ∧
        (r : ℝ) ≤ u * Real.sqrt (N : ℝ)} =
      (stdGaussian (Vector N)).real {x | t ^ 2 * N ≤ ‖x‖ ^ 2 ∧ ‖x‖ ^ 2 ≤ u ^ 2 * N} := by
  let : NeZero N := ⟨by omega⟩
  have hm := congrArg (fun ν : Measure ℝ => ν (Icc (t * Real.sqrt (N : ℝ))
    (u * Real.sqrt (N : ℝ)))) (SphereVolume.gaussianRadius_map (E := Vector N))
  rw [Measure.map_apply measurable_subtype_coe measurableSet_Icc,
    Measure.map_apply measurable_norm measurableSet_Icc] at hm
  change (SphereVolume.gaussianRadius (Vector N))
    {r : Ioi (0 : ℝ) | t * Real.sqrt (N : ℝ) ≤ (r : ℝ) ∧
      (r : ℝ) ≤ u * Real.sqrt (N : ℝ)} =
    (stdGaussian (Vector N)) {x | t * Real.sqrt (N : ℝ) ≤ ‖x‖ ∧
      ‖x‖ ≤ u * Real.sqrt (N : ℝ)} at hm
  unfold Measure.real
  rw [hm]
  congr 2
  ext x
  simp only [mem_ofPred_eq]
  have hR : 0 ≤ t * Real.sqrt (N : ℝ) := mul_nonneg ht (Real.sqrt_nonneg _)
  have hU : 0 ≤ u * Real.sqrt (N : ℝ) := mul_nonneg hu (Real.sqrt_nonneg _)
  rw [← sq_le_sq₀ hR (norm_nonneg x), ← sq_le_sq₀ (norm_nonneg x) hU,
    mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg N)]

theorem radial_shell_mass_eventually {t u : ℝ} (ht : 0 < t) (ht1 : t < 1) (hu : 1 < u) :
    ∀ᶠ N : ℕ in atTop, (1 / 2 : ℝ) ≤
      (SphereVolume.gaussianRadius (Vector N)).real
        {r : Ioi (0 : ℝ) | t * Real.sqrt (N : ℝ) ≤ (r : ℝ) ∧
          (r : ℝ) ≤ u * Real.sqrt (N : ℝ)} := by
  have h := GaussianShell.shell_mass_eventually (sq_pos_of_pos ht)
    (show t ^ 2 < 1 by nlinarith) (show 1 < u ^ 2 by nlinarith)
  filter_upwards [h, eventually_ge_atTop 1] with N h hN
  rw [radial_shell_mass_eq hN ht.le (by linarith)]
  exact h

/-- The explicit Gaussian-shell trial value, prior to sending both radii to
one. -/
def linearEndpointTrial (κ a z t u : ℝ) : ℝ :=
  ((z - 1) * u ^ 2 - Real.log z - Real.log (1 - a * κ / (z * t ^ 2)) / a) / 2

theorem linearSphereOneStepPressure_shell_upper {N : ℕ} (hN : 1 ≤ N)
    {κ a z t u : ℝ} (hκ : 0 ≤ κ) (ha : 0 < a) (hz : 1 ≤ z) (ht : 0 < t)
    (htu : t ≤ u) (hac : a * κ < z * t ^ 2)
    (hmass : (1 / 2 : ℝ) ≤ (SphereVolume.gaussianRadius (Vector N)).real
      {r : Ioi (0 : ℝ) | t * Real.sqrt (N : ℝ) ≤ (r : ℝ) ∧
        (r : ℝ) ≤ u * Real.sqrt (N : ℝ)}) :
    linearSphereOneStepPressure N κ a ≤ Real.log 2 / N + linearEndpointTrial κ a z t u := by
  let : NeZero N := ⟨by omega⟩
  have hN0 : 0 < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have hcsq : (Real.sqrt κ / t) ^ 2 = κ / t ^ 2 := by rw [div_pow, Real.sq_sqrt hκ]
  have hsc : a * (Real.sqrt κ / t) ^ 2 < z := by
    rw [hcsq, ← mul_div_assoc]
    exact (div_lt_iff₀ (sq_pos_of_pos ht)).mpr hac
  have H := SphereLinear.fractional_moment_shell_upper hz
    (mul_nonneg ht.le (Real.sqrt_nonneg (N : ℝ)))
    (mul_le_mul_of_nonneg_right htu (Real.sqrt_nonneg (N : ℝ))) ha.le hsc hmass
  have he (g : Vector N) :
      Real.log (SphereLinear.partition ((Real.sqrt κ / t) • g) (t * Real.sqrt (N : ℝ))) =
        linearSphereLogPartition N κ g := by
    unfold linearSphereLogPartition
    rw [linearSphere_partition_eq_angular hN κ ht g]
  simp only [he, finrank_euclideanSpace, Fintype.card_fin, mul_pow,
    Real.sq_sqrt (Nat.cast_nonneg N), hcsq] at H
  have hearg : 1 - a * (κ / t ^ 2) / z = 1 - a * κ / (z * t ^ 2) := by ring
  rw [hearg] at H
  have hμ : SYK.standardGaussianMeasureOnEuclidean (Fin N) = stdGaussian (Vector N) :=
    map_pi_eq_stdGaussian
  have hpos := exp_linearSphereLogPartition_integral_pos hN κ a
  rw [hμ] at hpos
  have hlog := Real.log_le_log hpos H
  rw [Real.log_exp] at hlog
  unfold linearSphereOneStepPressure
  rw [ite_eq_right_iff.mpr (fun h => (ha.ne' h).elim), hμ]
  have hdiv := div_le_div_of_nonneg_right (div_le_div_of_nonneg_right hlog ha.le) hN0.le
  convert hdiv using 1
  unfold linearEndpointTrial
  field_simp
  ring

theorem linearSphereOneStepPressure_shell_eventually {κ a z t u : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hz : 1 ≤ z) (ht : 0 < t) (ht1 : t < 1)
    (hu : 1 < u) (hac : a * κ < z * t ^ 2) :
    ∀ᶠ N : ℕ in atTop,
      linearSphereOneStepPressure N κ a ≤ Real.log 2 / N + linearEndpointTrial κ a z t u := by
  filter_upwards [radial_shell_mass_eventually ht ht1 hu, eventually_ge_atTop 1] with N hm hN
  exact linearSphereOneStepPressure_shell_upper hN hκ ha hz ht (by linarith) hac hm

/-- The true thermodynamic upper bound for the fractional Gaussian linear
spherical endpoint. The only parameters are the physical κ, fractional mass a
and Gaussian quadratic multiplier z. -/
theorem linearSphereOneStepPressure_eventually_upper {κ a z : ℝ}
    (hκ : 0 ≤ κ) (ha : 0 < a) (hz : 1 ≤ z) (hac : a * κ < z)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N : ℕ in atTop,
      linearSphereOneStepPressure N κ a ≤ linearEndpointTrial κ a z 1 1 + ε := by
  have hz0 : 0 < z := lt_of_lt_of_le zero_lt_one hz
  have harg : 1 - a * κ / z ≠ 0 := ne_of_gt (sub_pos.mpr ((div_lt_one hz0).mpr hac))
  have hc : ContinuousAt (fun p : ℝ × ℝ => linearEndpointTrial κ a z p.1 p.2) (1, 1) := by
    have hden : ContinuousAt (fun p : ℝ × ℝ => z * p.1 ^ 2) (1, 1) :=
      (continuousAt_fst.pow 2).const_mul z
    have hrec : ContinuousAt (fun p : ℝ × ℝ => a * κ / (z * p.1 ^ 2)) (1, 1) :=
      continuousAt_const.div hden (by simpa using hz0.ne')
    have hlog : ContinuousAt (fun p : ℝ × ℝ => Real.log (1 - a * κ / (z * p.1 ^ 2))) (1, 1) :=
      (continuousAt_const.sub hrec).log (by simpa using harg)
    exact ((((continuousAt_snd.pow 2).const_mul (z - 1)).sub continuousAt_const).sub
      (hlog.div_const a)).div_const 2
  let d : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hd : Tendsto d atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  have ht : Tendsto (fun n => 1 - d n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.sub hd
  have hu : Tendsto (fun n => 1 + d n) atTop (𝓝 (1 : ℝ)) := by
    simpa using tendsto_const_nhds.add hd
  have hp : Tendsto (fun n : ℕ => (1 - d n, 1 + d n)) atTop (𝓝 ((1 : ℝ), (1 : ℝ))) :=
    ht.prodMk_nhds hu
  have htrial : Tendsto (fun n : ℕ => linearEndpointTrial κ a z (1 - d n) (1 + d n))
      atTop (𝓝 (linearEndpointTrial κ a z 1 1)) := by
    exact Filter.Tendsto.comp
      (f := fun n : ℕ => ((1 - d n : ℝ), (1 + d n : ℝ)))
      (g := fun p : ℝ × ℝ => linearEndpointTrial κ a z p.1 p.2) hc hp
  have hcompat : Tendsto (fun n => z * (1 - d n) ^ 2) atTop (𝓝 z) := by
    simpa using tendsto_const_nhds.mul (ht.pow 2)
  have hevent := ((ht.eventually (lt_mem_nhds zero_lt_one)).and
    (hcompat.eventually (lt_mem_nhds hac))).and
      (htrial.eventually (gt_mem_nhds (lt_add_of_pos_right _ (half_pos hε))))
  obtain ⟨n, ⟨hn, hncompat⟩, hntrial⟩ := hevent.exists
  have hdpos : 0 < d n := by dsimp [d]; positivity
  have hmain := linearSphereOneStepPressure_shell_eventually hκ ha hz hn
    (by linarith : 1 - d n < 1) (by linarith : 1 < 1 + d n) hncompat
  have hsmall := (tendsto_const_div_atTop_nhds_zero_nat (Real.log 2)).eventually
    (gt_mem_nhds (half_pos hε))
  filter_upwards [hmain, hsmall] with N hmain hsmall
  linarith

end
end SlowEquilibration.SphericalModel
