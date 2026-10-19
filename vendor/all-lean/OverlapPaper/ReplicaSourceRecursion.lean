module
public import OverlapPaper.ReplicaSourceHoeffding
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.Analysis.Convex.SpecificFunctions.Pow
public import Mathlib.MeasureTheory.Measure.Tilted

@[expose] public section

/-! The normalized source recursion is dominated by the genuine Markov
expectation of its exponential. Zero recursion mass is included. -/
noncomputable section
open MeasureTheory ProbabilityTheory Set Real
namespace OverlapPaper

def sourceLogAverage {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (a : ℝ) (w : Ω → ℝ) : ℝ :=
  if a = 0 then ∫ x, w x ∂μ else (Real.log (∫ x, Real.exp (a * w x) ∂μ)) / a

theorem sourceLogAverage_le_log_exp {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) (ha : a ∈ Icc 0 1)
    (w : Ω → ℝ) (hi : Integrable w μ)
    (he : Integrable (fun x => Real.exp (w x)) μ)
    (hea : Integrable (fun x => Real.exp (a * w x)) μ) :
    sourceLogAverage μ a w ≤ Real.log (∫ x, Real.exp (w x) ∂μ) := by
  have hp : 0 < ∫ x, Real.exp (w x) ∂μ := by
    simpa only [mgf, one_mul] using mgf_pos (t := 1) (by simpa only [one_mul] using he)
  by_cases ha0 : a = 0
  · simp only [sourceLogAverage, ha0, ite_true]
    have H := convexOn_exp.map_integral_le continuous_exp.continuousOn isClosed_univ
      (Filter.Eventually.of_forall (fun x => mem_univ (w x))) hi he
    have Hlog := Real.log_le_log (Real.exp_pos _) H
    simpa only [Real.log_exp] using Hlog
  · have hap : 0 < a := lt_of_le_of_ne ha.1 (Ne.symm ha0)
    have hr : Integrable (fun x => (Real.exp (w x)) ^ a) μ := by
      simpa only [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm] using hea
    have H := (Real.concaveOn_rpow ha.1 ha.2).le_map_integral
      (Real.continuous_rpow_const ha.1).continuousOn isClosed_Ici
      (Filter.Eventually.of_forall (fun x => (Real.exp_pos (w x)).le)) he hr
    have Hlog := Real.log_le_log (by
      simpa only [mgf] using mgf_pos hea) (show (∫ x, Real.exp (a * w x) ∂μ) ≤ (∫ x, Real.exp (w x) ∂μ) ^ a by
      simpa only [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp, mul_comm] using H)
    rw [Real.log_rpow hp] at Hlog
    simpa only [sourceLogAverage, ha0, ite_false, div_le_iff₀ hap, mul_comm] using Hlog

theorem exp_sourceLogAverage_le {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) (ha : a ∈ Icc 0 1)
    (w : Ω → ℝ) (hi : Integrable w μ)
    (he : Integrable (fun x => Real.exp (w x)) μ)
    (hea : Integrable (fun x => Real.exp (a * w x)) μ) :
    Real.exp (sourceLogAverage μ a w) ≤ ∫ x, Real.exp (w x) ∂μ := by
  have H := Real.exp_le_exp.mpr (sourceLogAverage_le_log_exp μ a ha w hi he hea)
  rwa [Real.exp_log (by
    simpa only [mgf, one_mul] using mgf_pos (t := 1) (by simpa only [one_mul] using he))] at H

/-- Subtracting actual positive-mass logarithmic averages is exactly a
logarithmic average under the normalized baseline exponential tilt. -/
theorem sourceLogAverage_sub_tilted {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (a : ℝ) (ha : a ≠ 0)
    (f g : Ω → ℝ)
    (hf : Integrable (fun x => Real.exp (a * f x)) μ)
    (hg : Integrable (fun x => Real.exp (a * g x)) μ) :
    sourceLogAverage μ a f - sourceLogAverage μ a g =
      sourceLogAverage (μ.tilted (fun x => a * g x)) a (fun x => f x - g x) := by
  have hI : (∫ x, Real.exp (a * (f x - g x)) ∂μ.tilted (fun x => a * g x)) =
      (∫ x, Real.exp (a * f x) ∂μ) / (∫ x, Real.exp (a * g x) ∂μ) := by
    rw [integral_exp_tilted]
    congr 2
    funext x
    dsimp
    ring_nf
  simp only [sourceLogAverage, ha, ite_false, hI]
  rw [Real.log_div (integral_exp_pos hf).ne' (integral_exp_pos hg).ne']
  ring

end OverlapPaper
