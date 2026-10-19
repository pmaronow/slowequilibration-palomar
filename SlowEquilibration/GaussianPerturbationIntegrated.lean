-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationResponse
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

@[expose] public section

/-! # Integrated actual perturbation-energy fluctuations

The Gaussian mean's derivative spread is evaluated by genuine FTC and bounded
by the selected-coordinate feature diagonal. Combined with the proved
convex/Gaussian comparison, this is the integrated quenched component of
Panchenko's perturbation self-averaging lemma.
-/

namespace SlowEquilibration.GaussianPerturbationIntegrated
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationResponse

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

theorem parameterScore_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) :
    ‖parameterScore ν L label w x‖ ≤ K*‖w‖ :=
  ((score ν L (parameterOperator label x w)).le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (norm_score_le ν L hL hK hb _) (norm_nonneg _)).trans
      (mul_le_mul_of_nonneg_left (coordinateMask_norm_le label true w) hK))

theorem meanScore_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) :
    Continuous (meanScore ν L label) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun w => K*‖w‖)
  · exact .of_forall fun y => (parameterScore_gaussian_integrable ν L hL hK hb label y).aestronglyMeasurable
  · exact .of_forall fun _ => .of_forall fun w => parameterScore_norm_le ν L hL hK hb label w _
  · exact (gaussian_norm_integrable (ι := ι)).const_mul K
  · exact .of_forall fun w =>
      (show Differentiable ℝ (parameterScore ν L label w) from
        fun y => (parameterScore_hasDerivAt ν L hL hK hb label w y).differentiableAt).continuous.continuousAt

theorem meanScore_integral_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (l u : ℝ) :
    (∫ x in l..u,meanScore ν L label x) = parameterMean ν L label u-parameterMean ν L label l :=
  intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun x _ => parameterMean_hasDerivAt ν L hL hK hb label x)
    ((meanScore_continuous ν L hL hK hb label).intervalIntegrable l u)

/-- The actual mean derivative spread is exactly a difference of two
short boundary integrals. -/
theorem meanScore_spread_integral_eq (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (y : ℝ) :
    (∫ x in (0 : ℝ)..1,meanScore ν L label (x+y)-meanScore ν L label (x-y)) =
      (∫ x in (1-y)..(1+y),meanScore ν L label x)-
        (∫ x in (-y)..y,meanScore ν L label x) := by
  have hcont := meanScore_continuous ν L hL hK hb label
  have hder (x : ℝ) : HasDerivAt (fun z => parameterMean ν L label (z+y)-parameterMean ν L label (z-y))
      (meanScore ν L label (x+y)-meanScore ν L label (x-y)) x := by
    have hd := ((parameterMean_hasDerivAt ν L hL hK hb label (x+y)).comp x
      ((hasDerivAt_id x).add_const y)).sub
        ((parameterMean_hasDerivAt ν L hL hK hb label (x-y)).comp x ((hasDerivAt_id x).sub_const y))
    convert hd using 1
    · ext z;rfl
    · simp only [meanScore,mul_one]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hder x)
    (((hcont.comp (continuous_id.add_const y)).sub
      (hcont.comp (continuous_id.sub continuous_const))).intervalIntegrable 0 1),
    meanScore_integral_eq ν L hL hK hb,meanScore_integral_eq ν L hL hK hb]
  simp only [zero_add,zero_sub]

/-- Selected-coordinate diagonal control bounds the genuine integrated
mean derivative spread uniformly over all base laws and dimensions. -/
theorem meanScore_spread_integral_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a y : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (ha : 0 ≤ a)
    (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν, (∑ i, if label i=true then (coordinateObservable L i v)^2 else 0) ≤ a)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ x in (0 : ℝ)..1,meanScore ν L label (x+y)-meanScore ν L label (x-y)) ≤ 8*a*y := by
  have hbnd (x : ℝ) (hx : |x| ≤ 2) : ‖meanScore ν L label x‖ ≤ 2*a := by
    rw [Real.norm_eq_abs]
    exact (abs_meanScore_le ν L hL hK hb label hdiag x).trans
      (mul_le_mul_of_nonneg_right hx ha)
  have hp : |∫ x in (1-y)..(1+y),meanScore ν L label x| ≤ 4*a*y := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := 2*a)
      (f := meanScore ν L label) (a := 1-y) (b := 1+y) (fun x hx => by
        have hx' : x ∈ Ioc (1-y) (1+y) := by simpa only [uIoc_of_le (by linarith : 1-y ≤ 1+y)] using hx
        apply hbnd x
        rw [abs_le]
        constructor <;> linarith [hx'.1,hx'.2])
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ (1+y)-(1-y))] at h
    nlinarith [h]
  have hm : |∫ x in (-y)..y,meanScore ν L label x| ≤ 4*a*y := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const (C := 2*a)
      (f := meanScore ν L label) (a := -y) (b := y) (fun x hx => by
        have hx' : x ∈ Ioc (-y) y := by simpa only [uIoc_of_le (by linarith : -y ≤ y)] using hx
        apply hbnd x
        rw [abs_le]
        constructor <;> linarith [hx'.1,hx'.2])
    rw [Real.norm_eq_abs,abs_of_nonneg (by linarith : 0 ≤ y-(-y))] at h
    nlinarith [h]
  rw [meanScore_spread_integral_eq ν L hL hK hb label y]
  linarith [le_abs_self (∫ x in (1-y)..(1+y),meanScore ν L label x),
    neg_le_abs (∫ x in (-y)..y,meanScore ν L label x)]

theorem norm_meanScore_le_gaussianNorm (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (x : ℝ) :
    ‖meanScore ν L label x‖ ≤ K*(∫ w : EuclideanSpace ℝ ι,‖w‖
      ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  calc
    _ ≤ ∫ w,‖parameterScore ν L label w x‖ ∂SYK.standardGaussianMeasureOnEuclidean ι :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ w,K*‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι :=
      integral_mono (parameterScore_gaussian_integrable ν L hL hK hb label x).norm
        ((gaussian_norm_integrable (ι := ι)).const_mul K)
        (fun w => parameterScore_norm_le ν L hL hK hb label w x)
    _ = _ := integral_const_mul _ _

def energyFluctuation (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) : ℝ :=
  ∫ w,|parameterScore ν L label w x-meanScore ν L label x|
    ∂SYK.standardGaussianMeasureOnEuclidean ι

/-- The actual quenched absolute fluctuation integral is continuous;
all Gaussian integrability is derived from the physical feature bound. -/
theorem energyFluctuation_continuous (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) :
    Continuous (energyFluctuation ν L label) := by
  let M := K*(∫ w : EuclideanSpace ℝ ι,‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι)
  have hi (x : ℝ) : Integrable (fun w => |parameterScore ν L label w x-meanScore ν L label x|)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
    simpa only [Real.norm_eq_abs,Pi.sub_apply] using
      ((parameterScore_gaussian_integrable ν L hL hK hb label x).sub (integrable_const _)).norm
  have hbound (w : EuclideanSpace ℝ ι) (x : ℝ) :
      ‖|parameterScore ν L label w x-meanScore ν L label x|‖ ≤ K*‖w‖+M := by
    rw [Real.norm_eq_abs,abs_abs,← Real.norm_eq_abs]
    exact (norm_sub_le _ _).trans (add_le_add
      (parameterScore_norm_le ν L hL hK hb label w x)
      (norm_meanScore_le_gaussianNorm ν L hL hK hb label x))
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated (bound := fun w => K*‖w‖+M)
  · exact .of_forall fun y => (hi y).aestronglyMeasurable
  · exact .of_forall fun y => .of_forall fun w => hbound w y
  · exact ((gaussian_norm_integrable (ι := ι)).const_mul K).add (integrable_const M)
  · exact .of_forall fun w =>
      (((show Differentiable ℝ (parameterScore ν L label w) from
          fun y => (parameterScore_hasDerivAt ν L hL hK hb label w y).differentiableAt).continuous).sub
        (meanScore_continuous ν L hL hK hb label)).abs.continuousAt

/-- Actual integrated quenched energy fluctuations have the quantitative
bound used to obtain the perturbative GG error. -/
theorem energyFluctuation_integral_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a y : ℝ} (hK : 0 < K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (ha : 0 ≤ a)
    (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν, (∑ i, if label i=true then (coordinateObservable L i v)^2 else 0) ≤ a)
    (hy : 0 < y) (hy1 : y ≤ 1) :
    (∫ x in (0 : ℝ)..1,energyFluctuation ν L label x) ≤ 8*a*y+18*Real.exp (1/2)*K/y := by
  have hc := meanScore_continuous ν L hL hK.le hb label
  have hspread : Continuous (fun x => meanScore ν L label (x+y)-meanScore ν L label (x-y)) :=
    (hc.comp (continuous_id.add_const y)).sub (hc.comp (continuous_id.sub continuous_const))
  have hi := intervalIntegral.integral_mono_on (μ := (volume : Measure ℝ))
    (a := (0 : ℝ)) (b := 1) (by norm_num : (0 : ℝ) ≤ 1)
    ((energyFluctuation_continuous ν L hL hK.le hb label).intervalIntegrable 0 1)
    ((hspread.add continuous_const).intervalIntegrable 0 1) (fun x hx => by
      apply integral_score_fluctuation_le ν L hL hK hb label hy
      · rw [abs_le];constructor <;> linarith [hx.1,hx.2]
      · rw [abs_le];constructor <;> linarith [hx.1,hx.2]
      · rw [abs_le];constructor <;> linarith [hx.1,hx.2])
  simp only [Pi.add_apply] at hi
  rw [intervalIntegral.integral_add
      (f := fun x => meanScore ν L label (x+y)-meanScore ν L label (x-y))
      (g := fun _ => 18*Real.exp (1/2)*K/y) (hspread.intervalIntegrable 0 1)
      (continuous_const.intervalIntegrable 0 1),intervalIntegral.integral_const] at hi
  simp only [sub_zero,smul_eq_mul,one_mul] at hi
  exact hi.trans (add_le_add (meanScore_spread_integral_le ν L hL hK.le hb ha label hdiag hy hy1) le_rfl)

end
end SlowEquilibration.GaussianPerturbationIntegrated
