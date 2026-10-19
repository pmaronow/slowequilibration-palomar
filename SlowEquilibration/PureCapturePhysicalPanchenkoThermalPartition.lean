-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.PureCapturePhysicalPanchenkoThermalMGF
public import SlowEquilibration.SphericalParisiGibbsTilt

/-! The exact Gibbs moment-generating functions of a bounded scalar
observable are ratios of the original physical partition functions. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoThermalPartition
open MeasureTheory ProbabilityTheory SphericalParisiGibbsTilt
open scoped ENNReal Topology
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option linter.style.haveILetI false

variable {V : Type*} [MeasurableSpace V]

theorem scalarPartition_add_constant (ν : Measure V) (f : V → ℝ) (c : ℝ) :
    scalarPartition ν (fun z => f z+c) =
      scalarPartition ν f * Real.exp c := by
  unfold scalarPartition
  simp_rw [Real.exp_add]
  rw [integral_mul_const]

theorem scalarGibbs_scalar_mgf_ratio
    (ν : Measure V) [IsProbabilityMeasure ν]
    (H : V → ℝ) (hH : Measurable H) {K : ℝ}
    (hb : ∀ᵐ z ∂ν, |H z| ≤ K)
    (β t : ℝ) :
    scalarPartition (scalarGibbs ν (fun z => β*H z)) (fun z => t*H z) =
      scalarPartition ν (fun z => (β+t)*H z) /
        scalarPartition ν (fun z => β*H z) := by
  have hf : Measurable (fun z => β*H z) := measurable_const.mul hH
  have hfb : ∀ᵐ z ∂ν, |β*H z| ≤ |β| * K := hb.mono fun z hz => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  rw [scalarPartition_after_tilt ν (fun z => β*H z) (fun z => t*H z) hf hfb]
  have heq : (fun z => β*H z+t*H z) = (fun z => (β+t)*H z) := by
    funext z
    ring
  rw [heq]

theorem scalarGibbs_centered_scalar_mgf_ratio
    (ν : Measure V) [IsProbabilityMeasure ν]
    (H : V → ℝ) (hH : Measurable H) {K : ℝ}
    (hb : ∀ᵐ z ∂ν, |H z| ≤ K)
    (β t m : ℝ) :
    scalarPartition (scalarGibbs ν (fun z => β*H z))
      (fun z => t*(H z-m)) =
      scalarPartition ν (fun z => (β+t)*H z) * Real.exp (-t*m) /
        scalarPartition ν (fun z => β*H z) := by
  have hf : Measurable (fun z => β*H z) := measurable_const.mul hH
  have hfb : ∀ᵐ z ∂ν, |β*H z| ≤ |β| * K := hb.mono fun z hz => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg _)
  rw [scalarPartition_after_tilt ν (fun z => β*H z)
    (fun z => t*(H z-m)) hf hfb]
  have heq : (fun z => β*H z+t*(H z-m)) =
      (fun z => (β+t)*H z+(-t*m)) := by
    funext z
    ring
  rw [heq,scalarPartition_add_constant]

theorem scalarPartition_scaled_pos
    (ν : Measure V) [IsProbabilityMeasure ν]
    (H : V → ℝ) (hH : Measurable H) {K : ℝ}
    (hb : ∀ᵐ z ∂ν, |H z| ≤ K) (t : ℝ) :
    0 < scalarPartition ν (fun z => t*H z) := by
  apply scalarPartition_pos ν (fun z => t*H z) (measurable_const.mul hH)
  exact hb.mono fun z hz => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left hz (abs_nonneg t)

/-- The centered thermal MGF has no linear term after summing its two
signs; the result is the exact log-partition second difference. -/
theorem scalarGibbs_centered_log_mgfs_eq_second_difference
    (ν : Measure V) [IsProbabilityMeasure ν]
    (H : V → ℝ) (hH : Measurable H) {K : ℝ}
    (hb : ∀ᵐ z ∂ν, |H z| ≤ K)
    (β δ m : ℝ) :
    let P := scalarGibbs ν (fun z => β*H z)
    Real.log (scalarPartition P (fun z => δ*(H z-m))) +
      Real.log (scalarPartition P (fun z => -δ*(H z-m))) =
      Real.log (scalarPartition ν (fun z => (β+δ)*H z)) +
        Real.log (scalarPartition ν (fun z => (β-δ)*H z)) -
        2*Real.log (scalarPartition ν (fun z => β*H z)) := by
  dsimp only
  have hbase := scalarPartition_scaled_pos ν H hH hb β
  have hplus := scalarPartition_scaled_pos ν H hH hb (β+δ)
  have hminus := scalarPartition_scaled_pos ν H hH hb (β-δ)
  rw [scalarGibbs_centered_scalar_mgf_ratio ν H hH hb β δ m]
  rw [scalarGibbs_centered_scalar_mgf_ratio ν H hH hb β (-δ) m]
  rw [show β + -δ = β-δ from by ring]
  simp only [neg_neg]
  rw [Real.log_div (mul_ne_zero hplus.ne' (Real.exp_pos _).ne') hbase.ne',
    Real.log_div (mul_ne_zero hminus.ne' (Real.exp_pos _).ne') hbase.ne',
    Real.log_mul hplus.ne' (Real.exp_pos _).ne',
    Real.log_mul hminus.ne' (Real.exp_pos _).ne',
    Real.log_exp,Real.log_exp]
  ring

/-- Finite-volume thermal concentration around the true Gibbs mean,
bounded by the exact symmetric log-partition difference. -/
theorem scalarGibbs_centered_absolute_le_second_difference
    (ν : Measure V) [IsProbabilityMeasure ν]
    (H : V → ℝ) (hH : Measurable H) {K : ℝ}
    (hb : ∀ᵐ z ∂ν, |H z| ≤ K)
    (β δ : ℝ) :
    let P := scalarGibbs ν (fun z => β*H z)
    let m := ∫ z, H z ∂P
    δ * (∫ z, |H z-m| ∂P) ≤
      Real.log 2 +
        Real.log (scalarPartition ν (fun z => (β+δ)*H z)) +
        Real.log (scalarPartition ν (fun z => (β-δ)*H z)) -
        2*Real.log (scalarPartition ν (fun z => β*H z)) := by
  dsimp only
  let P := scalarGibbs ν (fun z => β*H z)
  letI : IsProbabilityMeasure P := scalarGibbs_probability ν
    (fun z => β*H z) (measurable_const.mul hH)
    (hb.mono fun z hz => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hz (abs_nonneg β))
  let m := ∫ z, H z ∂P
  have hHae : ∀ᵐ z ∂P, |H z| ≤ K :=
    (scalarGibbs_absolutelyContinuous ν (fun z => β*H z)).ae_le hb
  have hHint : Integrable H P := by
    apply Integrable.of_bound hH.aestronglyMeasurable K
    exact hHae.mono fun z hz => by simpa only [Real.norm_eq_abs] using hz
  have hcenter : ∀ᵐ z ∂P, |H z-m| ≤ K+|m| :=
    hHae.mono fun z hz => (abs_sub _ _).trans (add_le_add hz le_rfl)
  have hfi : Integrable (fun z => H z-m) P := hHint.sub (integrable_const _)
  have hf : Measurable (fun z => H z-m) := hH.sub measurable_const
  have hplus : Integrable (fun z => Real.exp (δ*(H z-m))) P := by
    apply scalar_exp_integrable P (fun z => δ*(H z-m)) (measurable_const.mul hf)
    exact hcenter.mono fun z hz => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hz (abs_nonneg δ)
  have hminus : Integrable (fun z => Real.exp (-δ*(H z-m))) P := by
    apply scalar_exp_integrable P (fun z => -δ*(H z-m)) (measurable_const.mul hf)
    exact hcenter.mono fun z hz => by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hz (abs_nonneg (-δ))
  have hzero : (∫ z, H z-m ∂P) = 0 := by
    rw [integral_sub hHint (integrable_const m),integral_const,probReal_univ,one_smul]
    dsimp [m]
    ring
  have hmgf := PureCapturePhysicalPanchenkoThermalMGF.centered_absolute_integral_le_log_mgfs
    P (fun z => H z-m) hf hfi δ hplus hminus hzero
  have hlog := scalarGibbs_centered_log_mgfs_eq_second_difference
    ν H hH hb β δ m
  change δ * (∫ z, |H z-m| ∂P) ≤
    Real.log 2 + Real.log (scalarPartition P (fun z => δ*(H z-m))) +
      Real.log (scalarPartition P (fun z => -δ*(H z-m))) at hmgf
  dsimp only at hlog
  rw [add_assoc, hlog] at hmgf
  convert hmgf using 1; ring

end SlowEquilibration.PureCapturePhysicalPanchenkoThermalPartition
