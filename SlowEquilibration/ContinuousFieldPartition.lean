-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.ContinuousFieldLaw
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.SpecialFunctions.Log.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

@[expose] public section

/-! # Literal compact-field partition as a Borel Lipschitz observable -/
namespace SlowEquilibration.ContinuousFieldPartition
noncomputable section
open MeasureTheory
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {K : Type*} [TopologicalSpace K] [CompactSpace K]
  [MeasurableSpace K] [BorelSpace K]

def partition (ν : Measure K) (β : ℝ) (f : C(K,ℝ)) : ℝ := ∫ x,Real.exp (β*f x) ∂ν

def logPartition (ν : Measure K) (β : ℝ) (f : C(K,ℝ)) : ℝ := Real.log (partition ν β f)

lemma exponential_integrable (ν : Measure K) [IsProbabilityMeasure ν] (β : ℝ) (f : C(K,ℝ)) :
    Integrable (fun x => Real.exp (β*f x)) ν :=
  (Real.continuous_exp.comp (f.continuous.const_mul β)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

lemma partition_pos (ν : Measure K) [IsProbabilityMeasure ν] (β : ℝ) (f : C(K,ℝ)) :
    0 < partition ν β f := integral_exp_pos (exponential_integrable ν β f)

lemma partition_compare (ν : Measure K) [IsProbabilityMeasure ν] (β : ℝ) (f g : C(K,ℝ)) :
    partition ν β f ≤ Real.exp (|β| *‖f-g‖)*partition ν β g := by
  unfold partition
  rw [← integral_const_mul]
  apply integral_mono (exponential_integrable ν β f)
    ((exponential_integrable ν β g).const_mul _)
  intro x
  have hn : |f x-g x| ≤ ‖f-g‖ := by
    simpa only [ContinuousMap.sub_apply,Real.norm_eq_abs] using
      (f-g).norm_coe_le_norm x
  have hb : β*(f x-g x) ≤ |β| *‖f-g‖ := by
    calc
      _ ≤ |β*(f x-g x)| := le_abs_self _
      _ = |β| *|f x-g x| := abs_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hn (abs_nonneg _)
  change Real.exp (β*f x) ≤ Real.exp (|β| * ‖f-g‖)*Real.exp (β*g x)
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith

lemma logPartition_compare (ν : Measure K) [IsProbabilityMeasure ν] (β : ℝ) (f g : C(K,ℝ)) :
    logPartition ν β f ≤ |β| *‖f-g‖+logPartition ν β g := by
  have hh := Real.log_le_log (partition_pos ν β f) (partition_compare ν β f g)
  rw [Real.log_mul (Real.exp_ne_zero _) (partition_pos ν β g).ne',Real.log_exp] at hh
  exact hh

theorem logPartition_lipschitz (ν : Measure K) [IsProbabilityMeasure ν] (β : ℝ) :
    LipschitzWith ⟨|β|,abs_nonneg β⟩ (logPartition ν β) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro f g
  rw [Real.norm_eq_abs,abs_le]
  change -(|β| * ‖f-g‖) ≤ logPartition ν β f-logPartition ν β g ∧
    logPartition ν β f-logPartition ν β g ≤ |β| * ‖f-g‖
  have hfg := logPartition_compare ν β f g
  have hgf := logPartition_compare ν β g f
  rw [norm_sub_rev] at hgf
  constructor <;> linarith

theorem logPartition_measurable (ν : Measure K) [IsProbabilityMeasure ν] (β : ℝ) :
    Measurable (logPartition ν β) := (logPartition_lipschitz ν β).continuous.measurable

end
end SlowEquilibration.ContinuousFieldPartition
