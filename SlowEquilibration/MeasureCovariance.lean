module
-- SPDX-License-Identifier: Apache-2.0

public import Mathlib.MeasureTheory.Integral.MeanInequalities
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.InnerProductSpace.LinearMap
public import Mathlib.Tactic

@[expose] public section

/-! # Actual covariance estimates for probability integrals -/

namespace SlowEquilibration.MeasureCovariance
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000
open MeasureTheory Set Filter
open scoped InnerProductSpace ENNReal NNReal

variable {X G : Type*} [MeasurableSpace X]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G] [CompleteSpace G]

/-- Vector-valued Cauchy--Schwarz for the actual scalar-vector integral. -/
theorem norm_integral_smul_sq_le (μ : Measure X) (f : X → ℝ) (g : X → G)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖∫ x, f x • g x ∂μ‖^2 ≤ (∫ x, (f x)^2 ∂μ)*(∫ x, ‖g x‖^2 ∂μ) := by
  have hH := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2:ℝ).HolderConjugate 2 from by rw [Real.holderConjugate_iff]; norm_num)
    (ae_of_all μ (fun x => norm_nonneg (f x)))
    (ae_of_all μ (fun x => norm_nonneg (g x)))
    (show MemLp (fun x => ‖f x‖) (ENNReal.ofReal 2) μ from by simpa using hf.norm)
    (show MemLp (fun x => ‖g x‖) (ENNReal.ofReal 2) μ from by simpa using hg.norm)
  have hn : ‖∫ x, f x • g x ∂μ‖ ≤ ∫ x, ‖f x‖*‖g x‖ ∂μ := by
    simpa only [norm_smul] using norm_integral_le_integral_norm (fun x => f x • g x)
  have hh : ‖∫ x, f x • g x ∂μ‖ ≤
      Real.sqrt (∫ x, (f x)^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ) := by
    refine hn.trans ?_
    simpa only [Real.sqrt_eq_rpow, Real.rpow_two, Real.norm_eq_abs, sq_abs] using hH
  have ha : 0 ≤ ∫ x, (f x)^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  have hb : 0 ≤ ∫ x, ‖g x‖^2 ∂μ := integral_nonneg (fun _ => sq_nonneg _)
  calc
    _ ≤ (Real.sqrt (∫ x, (f x)^2 ∂μ)*Real.sqrt (∫ x, ‖g x‖^2 ∂μ))^2 :=
      pow_le_pow_left₀ (norm_nonneg _) hh 2
    _ = _ := by rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- The actual centered vector variance identity. -/
theorem integral_norm_sub_mean_sq (μ : Measure X) [IsProbabilityMeasure μ]
    (U : X → G) (hU : MemLp U 2 μ) :
    (∫ x, ‖U x-(∫ y, U y ∂μ)‖^2 ∂μ) =
      (∫ x, ‖U x‖^2 ∂μ)-‖∫ y, U y ∂μ‖^2 := by
  let m := ∫ y, U y ∂μ
  have hiU : Integrable U μ := hU.integrable (by norm_num)
  have hiN : Integrable (fun x => ‖U x‖^2) μ := hU.integrable_norm_pow'
  have hiI : Integrable (fun x => inner ℝ (U x) m) μ := by
    apply ((innerSL ℝ m).integrable_comp hiU).congr
    exact ae_of_all μ (fun x => real_inner_comm (U x) m)
  have hI : (∫ x, inner ℝ (U x) m ∂μ) = ‖m‖^2 := by
    have hh := (innerSL ℝ m).integral_comp_comm hiU
    change (∫ x, inner ℝ m (U x) ∂μ) = inner ℝ m m at hh
    have he : (fun x => inner ℝ (U x) m) = fun x => inner ℝ m (U x) := by
      funext x; exact real_inner_comm _ _
    rw [he]
    change (∫ x, inner ℝ m (U x) ∂μ) = ‖m‖^2
    rw [hh]
    exact real_inner_self_eq_norm_sq m
  have he : (fun x => ‖U x-m‖^2) =
      (fun x => ‖U x‖^2-2*inner ℝ (U x) m+‖m‖^2) := by
    funext x
    exact norm_sub_sq_real _ _
  rw [he]
  rw [integral_add (f := fun x => ‖U x‖^2-2*inner ℝ (U x) m)
    (g := fun _ => ‖m‖^2) (hiN.sub (hiI.const_mul 2)) (integrable_const _),
    integral_sub hiN (hiI.const_mul 2), integral_const_mul, hI]
  simp only [integral_const, probReal_univ, smul_eq_mul, one_mul]
  ring

end
end SlowEquilibration.MeasureCovariance
