-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SemigroupLaplace
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

namespace SlowEquilibration.SemigroupLaplace.Data

noncomputable section
open MeasureTheory Set Filter
open scoped Topology NNReal
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
variable (S : SlowEquilibration.SemigroupLaplace.Data E)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

omit [CompleteSpace E] in
theorem translated_integral (f : ℝ → E) (h : ℝ) :
    (∫ t : ℝ in Ioi 0, f (t + h)) = ∫ t : ℝ in Ioi h, f t := by
  have he : (fun t : ℝ => t + h) ⁻¹' Ioi h = Ioi 0 := by
    ext t
    simp
  have hm := (measurePreserving_add_right volume h).setIntegral_preimage_emb
    (Homeomorph.addRight h).measurableEmbedding f (Ioi h)
  rwa [he] at hm

theorem P_operator_shift (h : ℝ≥0) (x : E) :
    S.P h (S.operator x) = Real.exp (h : ℝ) •
      (S.operator x - ∫ t : ℝ in (0 : ℝ)..(h : ℝ), S.integrand x t) := by
  have ht (t : ℝ) (ht : 0 < t) :
      S.P h (S.integrand x t) = Real.exp (h : ℝ) • S.integrand x (t + h) := by
    have htnn : (t + (h : ℝ)).toNNReal = h + t.toNNReal := by
      calc
        _ = t.toNNReal + (h : ℝ).toNNReal := Real.toNNReal_add (r := t) (p := (h : ℝ)) ht.le h.prop
        _ = h + t.toNNReal := by rw [Real.toNNReal_coe, add_comm]
    simp only [integrand, map_smul, htnn, S.add, ContinuousLinearMap.comp_apply, smul_smul]
    congr 1
    rw [← Real.exp_add]
    congr 1
    ring
  calc
    _ = ∫ t : ℝ in Ioi 0, S.P h (S.integrand x t) :=
      ((S.P h).integral_comp_comm (S.integrand_integrable x)).symm
    _ = ∫ t : ℝ in Ioi 0, Real.exp (h : ℝ) • S.integrand x (t + h) := by
      apply integral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
      exact ht t ht0
    _ = Real.exp (h : ℝ) • ∫ t : ℝ in Ioi (h : ℝ), S.integrand x t := by
      rw [integral_smul, translated_integral]
    _ = _ := by
      have he := intervalIntegral.integral_Ioi_sub_Ioi (S.integrand_integrable x) h.prop
      change S.value x - (∫ t : ℝ in Ioi (h : ℝ), S.integrand x t) =
        (∫ t : ℝ in (0 : ℝ)..(h : ℝ), S.integrand x t) at he
      congr 1
      simp only [operator_apply]
      rw [← he]
      abel

theorem P_operator_hasDerivAt {t : ℝ} (ht : 0 < t) (x : E) :
    HasDerivAt (fun s : ℝ => S.P s.toNNReal (S.operator x))
      (S.P t.toNNReal (S.operator x) - S.P t.toNNReal x) t := by
  have hprimitive := intervalIntegral.integral_hasDerivAt_right
    ((S.integrand_continuous x).intervalIntegrable 0 t)
    (S.integrand_continuous x).stronglyMeasurable.stronglyMeasurableAtFilter
    (S.integrand_continuous x).continuousAt
  have hprod := (Real.hasDerivAt_exp t).smul ((hasDerivAt_const t (S.operator x)).sub hprimitive)
  have hchange : (fun s : ℝ => S.P s.toNNReal (S.operator x)) =ᶠ[𝓝 t]
      (fun s : ℝ => Real.exp s • (S.operator x - ∫ u : ℝ in (0 : ℝ)..s, S.integrand x u)) := by
    filter_upwards [eventually_gt_nhds ht] with s hs
    have he := S.P_operator_shift s.toNNReal x
    simpa only [Real.coe_toNNReal _ hs.le] using he
  apply (hprod.congr_of_eventuallyEq hchange).congr_deriv
  have he := S.P_operator_shift t.toNNReal x
  rw [Real.coe_toNNReal _ ht.le] at he
  change Real.exp t • (0 - S.integrand x t) +
    Real.exp t • (S.operator x - ∫ u : ℝ in (0 : ℝ)..t, S.integrand x u) = _
  rw [zero_sub, smul_neg, ← he]
  have heprod : Real.exp t • S.integrand x t = S.P t.toNNReal x := by
    rw [integrand, smul_smul, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_smul]
  rw [heprod]
  abel

end
end SlowEquilibration.SemigroupLaplace.Data
