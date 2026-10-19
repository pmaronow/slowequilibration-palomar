-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.RareEventMomentTransfer
public import Mathlib.MeasureTheory.Function.L1Space.Integrable

/-! The manuscript's determinant-weighted Hölder estimate for actual
dependent random variables. Moment integrability is explicit, so a divergent
Bochner integral cannot be interpreted as a zero moment. -/

@[expose] public section
namespace SlowEquilibration
noncomputable section
open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology ENNReal

theorem determinant_weighted_holder {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) [IsProbabilityMeasure ν] (D φ : Ω → ℝ)
    (hD : Integrable D ν) (hDnonneg : ∀ᵐ x ∂ν, 0 ≤ D x)
    (hmean : 0 < ∫ x, D x ∂ν) (hφ : AEStronglyMeasurable φ ν)
    (hφbound : ∀ᵐ x ∂ν, 0 ≤ φ x ∧ φ x ≤ 1)
    {r K q : ℝ} (hr : 1 < r)
    (hMoment : Integrable (fun x => (D x/(∫ y, D y ∂ν))^r) ν)
    (hMomentBound : (∫ x, (D x/(∫ y, D y ∂ν))^r ∂ν) ≤ K)
    (hφMean : (∫ x, φ x ∂ν) ≤ q) :
    (∫ x, D x*φ x ∂ν)/(∫ x, D x ∂ν) ≤ K^(1/r)*q^(1-1/r) := by
  let m := ∫ x, D x ∂ν
  let p := Real.conjExponent r
  have hHolder : r.HolderConjugate p := Real.HolderConjugate.conjExponent hr
  have hrpos : 0 < r := lt_trans zero_lt_one hr
  have hppos : 0 < p := hHolder.right_pos
  have hpone : 1 ≤ p := hHolder.symm.lt.le
  have hDn : ∀ᵐ x ∂ν, 0 ≤ D x/m := hDnonneg.mono (fun x hx => div_nonneg hx hmean.le)
  have hDnorm : Integrable (fun x => ‖D x/m‖^r) ν := by
    apply hMoment.congr
    filter_upwards [hDn] with x hx
    rw [Real.norm_of_nonneg hx]
  have hDlp : MemLp (fun x => D x/m) (ENNReal.ofReal r) ν := by
    apply (integrable_norm_rpow_iff (hD.div_const m).aestronglyMeasurable
      (ENNReal.ofReal_pos.mpr hrpos).ne' ENNReal.ofReal_ne_top).mp
    simpa only [ENNReal.toReal_ofReal hrpos.le] using hDnorm
  have hφnorm : ∀ᵐ x ∂ν, ‖φ x‖ ≤ (1 : ℝ) := hφbound.mono
    (fun x hx => by rw [Real.norm_of_nonneg hx.1]; exact hx.2)
  have hφlp : MemLp φ (ENNReal.ofReal p) ν := MemLp.of_bound hφ 1 hφnorm
  have hφint : Integrable φ ν := (memLp_one_iff_integrable).mp
    (show MemLp φ 1 ν from MemLp.of_bound hφ 1 hφnorm)
  have hφpint : Integrable (fun x => φ x^p) ν := by
    have hh := hφlp.integrable_norm_rpow (ENNReal.ofReal_pos.mpr hppos).ne'
      ENNReal.ofReal_ne_top
    rw [ENNReal.toReal_ofReal hppos.le] at hh
    apply hh.congr
    filter_upwards [hφbound] with x hx
    rw [Real.norm_of_nonneg hx.1]
  have hφp : (∫ x, φ x^p ∂ν) ≤ q := by
    refine (integral_mono_ae hφpint hφint ?_).trans hφMean
    exact hφbound.mono (fun x hx => Real.rpow_le_self_of_le_one hx.1 hx.2 hpone)
  have hK : 0 ≤ K := (integral_nonneg_of_ae
    (hDn.mono (fun x hx => Real.rpow_nonneg hx r))).trans hMomentBound
  have hq : 0 ≤ q := (integral_nonneg_of_ae (hφbound.mono (fun _ hx => hx.1))).trans hφMean
  have hpowM : 0 ≤ ∫ x, (D x/m)^r ∂ν := integral_nonneg_of_ae
    (hDn.mono (fun x hx => Real.rpow_nonneg hx r))
  have hpowφ : 0 ≤ ∫ x, φ x^p ∂ν := integral_nonneg_of_ae
    (hφbound.mono (fun x hx => Real.rpow_nonneg hx.1 p))
  have hh := integral_mul_le_Lp_mul_Lq_of_nonneg hHolder hDn
    (hφbound.mono (fun _ hx => hx.1)) hDlp hφlp
  have he : (∫ x, (D x/m)*φ x ∂ν) = (∫ x, D x*φ x ∂ν)/m := by
    calc
      _ = ∫ x, (D x*φ x)/m ∂ν := by
        congr 1
        funext x
        ring
      _ = _ := integral_div m (fun x => D x*φ x)
  rw [he] at hh
  have hupper := mul_le_mul
    (Real.rpow_le_rpow hpowM hMomentBound (by positivity : 0 ≤ 1/r))
    (Real.rpow_le_rpow hpowφ hφp (by positivity : 0 ≤ 1/p))
    (Real.rpow_nonneg hpowφ _) (Real.rpow_nonneg hK _)
  have hp : 1/p = 1-1/r := by simpa only [one_div] using hHolder.one_sub_inv.symm
  rw [hp] at hh hupper
  exact hh.trans hupper

end
end SlowEquilibration
