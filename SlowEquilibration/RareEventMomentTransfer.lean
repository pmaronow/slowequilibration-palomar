-- SPDX-License-Identifier: Apache-2.0
module

public import Mathlib.Probability.Moments.SubGaussian
public import Mathlib.Analysis.Convex.Integral
public import Mathlib.MeasureTheory.Function.LpSeminorm.Indicator

@[expose] public section

/-!
# Actual expectation normalization after a rare exceptional event

The nonnegative observable is dominated by the exponential of a subgaussian
logarithm and agrees with it outside the specified exceptional event. Its
expectation and normalized moments below are those of the actual observable.
-/

namespace SlowEquilibration.RareEventMomentTransfer

noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal NNReal

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem exponential_on_bad_event_bound {X : Ω → ℝ} {c : ℝ≥0}
    (hG : HasSubgaussianMGF X c μ) {B : Set Ω} (hB : MeasurableSet B) :
    (∫ x in B, Real.exp (X x) ∂μ) ≤ Real.exp (c : ℝ) * Real.sqrt (μ.real B) := by
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg
    (show (2 : ℝ).HolderConjugate 2 from by rw [Real.holderConjugate_iff]; norm_num)
    (ae_of_all μ (fun x => (Real.exp_pos (X x)).le))
    (ae_of_all μ (fun x => show 0 ≤ B.indicator (fun _ => (1 : ℝ)) x from by
      by_cases hx : x ∈ B <;> simp [hx]))
    (show MemLp (fun x => Real.exp (X x)) (ENNReal.ofReal 2) μ from by
      simpa using hG.memLp_exp_mul 1 2)
    (show MemLp (B.indicator (fun _ => (1 : ℝ))) (ENNReal.ofReal 2) μ from
      memLp_indicator_const _ hB _ (Or.inr (measure_ne_top μ B)))
  have hleft : (∫ x, Real.exp (X x) * B.indicator (fun _ => (1 : ℝ)) x ∂μ) =
      ∫ x in B, Real.exp (X x) ∂μ := by
    rw [← integral_indicator hB]
    congr 1
    funext x
    by_cases hx : x ∈ B <;> simp [hx]
  have hright : (∫ x, (B.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ) ∂μ) = μ.real B := by
    have heq : (fun x => (B.indicator (fun _ => (1 : ℝ)) x) ^ (2 : ℝ)) =
        B.indicator (fun _ => (1 : ℝ)) := by
      funext x
      by_cases hx : x ∈ B <;> simp [hx]
    rw [heq, integral_indicator hB]
    simp
  have hsecond : (∫ x, Real.exp (X x) ^ (2 : ℝ) ∂μ) ≤ Real.exp (2 * (c : ℝ)) := by
    simpa only [← Real.exp_mul, mul_comm (X _), mgf, show (c : ℝ) * (2 : ℝ) ^ 2 / 2 = 2 * c by ring]
      using hG.mgf_le 2
  rw [hleft, hright] at hHolder
  calc
    _ ≤ (∫ x, Real.exp (X x) ^ (2 : ℝ) ∂μ) ^ (1 / (2 : ℝ)) *
        (μ.real B) ^ (1 / (2 : ℝ)) := hHolder
    _ ≤ (Real.exp (2 * (c : ℝ))) ^ (1 / (2 : ℝ)) * (μ.real B) ^ (1 / (2 : ℝ)) := by
      gcongr
    _ = _ := by
      rw [← Real.exp_mul, Real.sqrt_eq_rpow]
      congr 1
      ring_nf

theorem normalized_dominated_exponential_moments
    (Y D : Ω → ℝ) (hY : Integrable Y μ) (hD : AEMeasurable D μ)
    (c : ℝ≥0) (hG : HasSubgaussianMGF (fun x => Y x - ∫ y, Y y ∂μ) c μ)
    (B : Set Ω) (hB : MeasurableSet B)
    (hdom : ∀ᵐ x ∂μ, 0 ≤ D x ∧ D x ≤ Real.exp (Y x))
    (heq : ∀ᵐ x ∂μ, x ∉ B → D x = Real.exp (Y x))
    (hsmall : Real.exp (c : ℝ) * Real.sqrt (μ.real B) ≤ 1 / 2) :
    Integrable D μ ∧ Real.exp (∫ y, Y y ∂μ) / 2 ≤ ∫ y, D y ∂μ ∧
    0 < ∫ y, D y ∂μ ∧ ∀ r : ℝ, 0 ≤ r →
      Integrable (fun x => (D x / (∫ y, D y ∂μ)) ^ r) μ ∧
      (∫ x, (D x / (∫ y, D y ∂μ)) ^ r ∂μ) ≤
        (2 : ℝ) ^ r * Real.exp ((c : ℝ) * r ^ 2 / 2) := by
  let m := ∫ y, Y y ∂μ
  have hExp : Integrable (fun x => Real.exp (Y x)) μ := by
    apply ((hG.integrable_exp_mul 1).mul_const (Real.exp m)).congr
    exact ae_of_all μ (fun x => by
      simp only [one_mul]
      rw [← Real.exp_add]
      congr 1
      dsimp [m]
      ring)
  have hIntD : Integrable D μ := hExp.mono' hD.aestronglyMeasurable (by
    filter_upwards [hdom] with x hx
    rw [Real.norm_of_nonneg hx.1]
    exact hx.2)
  have hBad : (∫ x in B, Real.exp (Y x) ∂μ) ≤ Real.exp m / 2 := by
    have hb := exponential_on_bad_event_bound hG hB
    have heqExp : (fun x => Real.exp (Y x)) =
        (fun x => Real.exp m * Real.exp (Y x - m)) := by
      funext x
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heqExp, integral_const_mul]
    calc
      _ ≤ Real.exp m * (Real.exp (c : ℝ) * Real.sqrt (μ.real B)) :=
        mul_le_mul_of_nonneg_left hb (Real.exp_pos m).le
      _ ≤ Real.exp m * (1 / 2) := mul_le_mul_of_nonneg_left hsmall (Real.exp_pos m).le
      _ = _ := by ring
  have hJ : Real.exp m ≤ ∫ x, Real.exp (Y x) ∂μ :=
    convexOn_exp.map_integral_le Real.continuous_exp.continuousOn isClosed_univ
      (ae_of_all μ (fun _ => mem_univ _)) hY hExp
  have hsum : (∫ x, Real.exp (Y x) ∂μ) ≤
      (∫ x, D x ∂μ) + ∫ x in B, Real.exp (Y x) ∂μ := by
    rw [← integral_indicator hB, ← integral_add hIntD (hExp.indicator hB)]
    apply integral_mono_ae hExp (hIntD.add (hExp.indicator hB))
    filter_upwards [hdom, heq] with x hx hxeq
    change Real.exp (Y x) ≤ D x + B.indicator (fun x => Real.exp (Y x)) x
    by_cases hxB : x ∈ B
    · simp only [indicator_of_mem hxB]
      linarith [hx.1]
    · simp only [indicator_of_notMem hxB, add_zero, hxeq hxB]
      exact le_rfl
  have hmean : Real.exp m / 2 ≤ ∫ x, D x ∂μ := by linarith
  have hpos : 0 < ∫ x, D x ∂μ := (half_pos (Real.exp_pos m)).trans_le hmean
  refine ⟨hIntD, hmean, hpos, ?_⟩
  intro r hr
  have hpoint : ∀ᵐ x ∂μ, (D x / (∫ y, D y ∂μ)) ^ r ≤
      (2 : ℝ) ^ r * Real.exp (r * (Y x - m)) := by
    filter_upwards [hdom] with x hx
    calc
      _ ≤ (Real.exp (Y x) / (Real.exp m / 2)) ^ r :=
        Real.rpow_le_rpow (div_nonneg hx.1 hpos.le)
          (div_le_div₀ (Real.exp_pos (Y x)).le hx.2 (half_pos (Real.exp_pos m)) hmean) hr
      _ = _ := by
        have he : Real.exp (Y x) / (Real.exp m / 2) = 2 * Real.exp (Y x - m) := by
          rw [Real.exp_sub]
          ring_nf
        rw [he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos _).le,
          ← Real.exp_mul]
        congr 1
        ring_nf
  have hboundInt : Integrable (fun x => (2 : ℝ) ^ r * Real.exp (r * (Y x - m))) μ :=
    (hG.integrable_exp_mul r).const_mul _
  have hnormInt : Integrable (fun x => (D x / (∫ y, D y ∂μ)) ^ r) μ := by
    apply hboundInt.mono'
    · exact (hD.div_const _ |>.pow_const r).aestronglyMeasurable
    · filter_upwards [hdom, hpoint] with x hx hp
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg hx.1 hpos.le) r)]
      exact hp
  refine ⟨hnormInt, ?_⟩
  calc
    _ ≤ ∫ x, (2 : ℝ) ^ r * Real.exp (r * (Y x - m)) ∂μ :=
      integral_mono_ae hnormInt hboundInt hpoint
    _ = (2 : ℝ) ^ r * ∫ x, Real.exp (r * (Y x - m)) ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hG.mgf_le r) (Real.rpow_nonneg (by norm_num) _)

theorem normalized_upper_exponential_moments
    (Y D : Ω → ℝ) (hY : Integrable Y μ) (hD : AEMeasurable D μ)
    (c : ℝ≥0) (hG : HasSubgaussianMGF (fun x => Y x - ∫ y, Y y ∂μ) c μ)
    (B : Set Ω) (hB : MeasurableSet B)
    (hdom : ∀ᵐ x ∂μ, 0 ≤ D x ∧ D x ≤ Real.exp (Y x))
    (heq : ∀ᵐ x ∂μ, x ∉ B → D x = Real.exp (Y x))
    (hsmall : Real.exp (c : ℝ) * Real.sqrt (μ.real B) ≤ 1 / 2)
    (r : ℝ) (hr : 0 ≤ r) :
    Integrable (fun x => (Real.exp (Y x) / (∫ y, D y ∂μ)) ^ r) μ ∧
    (∫ x, (Real.exp (Y x) / (∫ y, D y ∂μ)) ^ r ∂μ) ≤
      (2 : ℝ) ^ r * Real.exp ((c : ℝ) * r ^ 2 / 2) := by
  have hbase := normalized_dominated_exponential_moments Y D hY hD c hG B hB hdom heq hsmall
  let m := ∫ y, Y y ∂μ
  have hpos := hbase.2.2.1
  have hpoint (x : Ω) : (Real.exp (Y x) / (∫ y, D y ∂μ)) ^ r ≤
      (2 : ℝ) ^ r * Real.exp (r * (Y x - m)) := by
    calc
      _ ≤ (Real.exp (Y x) / (Real.exp m / 2)) ^ r :=
        Real.rpow_le_rpow (div_nonneg (Real.exp_pos _).le hpos.le)
          (div_le_div_of_nonneg_left (Real.exp_pos _).le
            (half_pos (Real.exp_pos m)) hbase.2.1) hr
      _ = _ := by
        have he : Real.exp (Y x) / (Real.exp m / 2) = 2 * Real.exp (Y x - m) := by
          rw [Real.exp_sub]
          ring_nf
        rw [he, Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (Real.exp_pos _).le,
          ← Real.exp_mul]
        congr 1
        ring_nf
  have hb : Integrable (fun x => (2 : ℝ) ^ r * Real.exp (r * (Y x - m))) μ :=
    (hG.integrable_exp_mul r).const_mul _
  have hi : Integrable (fun x => (Real.exp (Y x) / (∫ y, D y ∂μ)) ^ r) μ := by
    apply hb.mono'
    · exact ((hY.aemeasurable.exp.div_const _).pow_const r).aestronglyMeasurable
    · exact ae_of_all μ (fun x => by
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (div_nonneg (Real.exp_pos _).le hpos.le) r)]
        exact hpoint x)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ x, (2 : ℝ) ^ r * Real.exp (r * (Y x - m)) ∂μ := integral_mono hi hb hpoint
    _ = (2 : ℝ) ^ r * ∫ x, Real.exp (r * (Y x - m)) ∂μ := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (hG.mgf_le r) (Real.rpow_nonneg (by norm_num) _)

end
end SlowEquilibration.RareEventMomentTransfer
