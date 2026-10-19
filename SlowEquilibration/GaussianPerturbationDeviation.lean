-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GaussianPerturbationThermal
public import Mathlib.MeasureTheory.Integral.Prod

@[expose] public section

/-! # Actual absolute perturbation-energy fluctuation

The Gibbs thermal deviation is bounded by its genuine variance, using an
arbitrary positive comparison scale. After Gaussian and coefficient averaging,
the previously proved variance budget yields the thermal part of Panchenko's
self-averaging estimate. The quenched part is the actual log-partition derivative
comparison; no replica identity or positivity assumption enters these bounds.
-/

namespace SlowEquilibration.GaussianPerturbationDeviation
noncomputable section
open MeasureTheory Set Filter
open scoped Topology
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
  GaussianPerturbationSelfAveraging GaussianPerturbationResponse GaussianPerturbationIntegrated
  GaussianPerturbationThermal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

/-- The literal Gibbs mean absolute deviation of the selected field energy. -/
def thermalDeviation (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) : ℝ :=
  ∫ v, |L v (coordinateMask label true w)-parameterScore ν L label w x|
    ∂gibbsMeasure ν L (parameterOperator label x w)

theorem thermalDeviation_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ)
    {r : ℝ} (hr : 0 < r) :
    thermalDeviation ν L label w x ≤ (parameterVariance ν L label w x+r^2)/(2*r) := by
  let G := gibbsMeasure ν L (parameterOperator label x w)
  let ρ := fun v => L v (coordinateMask label true w)
  let c := parameterScore ν L label w x
  have : IsProbabilityMeasure G := gibbsMeasure_probability ν L hL hb _
  have hρ : Measurable ρ :=
    (ContinuousLinearMap.apply ℝ ℝ (coordinateMask label true w)).continuous.measurable.comp hL
  have hc : c = ∫ v,ρ v ∂G := by
    rw [show c=score ν L (parameterOperator label x w) (coordinateMask label true w) from rfl,
      score_apply ν L hL hb,← integral_gibbsMeasure ν L hL hb]
  have hbd : ∀ᵐ v ∂G, |ρ v| ≤ K*‖w‖ := by
    apply ((directionalObservable_bound ν L hb (coordinateMask label true w)).mono
      fun v hv => hv.1.trans (mul_le_mul_of_nonneg_left
        (coordinateMask_norm_le label true w) hK)).filter_mono
      (gibbsMeasure_absolutelyContinuous ν L _).ae_le
  have hi : Integrable (fun v => |ρ v-c|) G := by
    apply Integrable.of_bound (continuous_abs.measurable.comp (hρ.sub_const c)).aestronglyMeasurable (K*‖w‖+|c|)
    filter_upwards [hbd] with v hv
    change ‖|ρ v-c|‖ ≤ _
    rw [Real.norm_eq_abs,abs_abs]
    exact (abs_sub _ _).trans (add_le_add hv le_rfl)
  have hi2 : Integrable (fun v => (ρ v-c)^2) G := by
    apply Integrable.of_bound ((hρ.sub_const c).pow_const 2).aestronglyMeasurable
      ((K*‖w‖+|c|)^2)
    filter_upwards [hbd] with v hv
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    have h := (abs_sub (ρ v) c).trans (add_le_add hv le_rfl)
    have hh := mul_self_le_mul_self (abs_nonneg (ρ v-c)) h
    simpa only [← pow_two,sq_abs] using hh
  have hv : parameterVariance ν L label w x = ∫ v,(ρ v-c)^2 ∂G := by
    change ProbabilityTheory.variance ρ G = _
    rw [ProbabilityTheory.variance_eq_integral hρ.aemeasurable,← hc]
  have hpoint : ∀ v,|ρ v-c| ≤ ((ρ v-c)^2+r^2)/(2*r) := by
    intro v
    apply (le_div_iff₀ (by positivity : 0 < 2*r)).mpr
    have hs : (ρ v-c)^2+r^2-|ρ v-c| * (2*r) = (|ρ v-c|-r)^2 := by
      calc
        _ = |ρ v-c|^2+r^2-|ρ v-c| * (2*r) := by rw [sq_abs]
        _ = _ := by ring
    apply sub_nonneg.mp
    rw [hs]
    exact sq_nonneg _
  have hright : Integrable (fun v => ((ρ v-c)^2+r^2)/(2*r)) G :=
    (hi2.add (integrable_const (μ := G) (r^2))).div_const (2*r)
  have hmono : (∫ v,|ρ v-c| ∂G) ≤ ∫ v,((ρ v-c)^2+r^2)/(2*r) ∂G :=
    integral_mono hi hright hpoint
  have heq : (∫ v,((ρ v-c)^2+r^2)/(2*r) ∂G) =
      (parameterVariance ν L label w x+r^2)/(2*r) := by
    rw [integral_div,integral_add hi2 (integrable_const (μ := G) (r^2)),integral_const]
    simp only [probReal_univ,one_smul]
    rw [← hv]
  exact hmono.trans_eq heq

theorem thermalDeviation_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (w : EuclideanSpace ℝ ι) (x : ℝ) :
    ‖thermalDeviation ν L label w x‖ ≤ 2*K*‖w‖ := by
  let G := gibbsMeasure ν L (parameterOperator label x w)
  have : IsProbabilityMeasure G := gibbsMeasure_probability ν L hL hb _
  have hc := parameterScore_norm_le ν L hL hK hb label w x
  have hbd : ∀ᵐ v ∂G, |L v (coordinateMask label true w)-parameterScore ν L label w x| ≤ 2*K*‖w‖ := by
    have hρ := (directionalObservable_bound ν L hb (coordinateMask label true w)).mono
      fun v hv => hv.1.trans (mul_le_mul_of_nonneg_left
        (coordinateMask_norm_le label true w) hK)
    filter_upwards [hρ.filter_mono (gibbsMeasure_absolutelyContinuous ν L _).ae_le] with v hv
    have hc' : |parameterScore ν L label w x| ≤ K*‖w‖ := by simpa [Real.norm_eq_abs] using hc
    exact (abs_sub _ _).trans (by linarith)
  change ‖∫ v,_ ∂G‖ ≤ _
  have hbd' : ∀ᵐ v ∂G, ‖|L v (coordinateMask label true w)-parameterScore ν L label w x|‖ ≤ 2*K*‖w‖ :=
    hbd.mono fun v hv => by simpa only [Real.norm_eq_abs,abs_abs] using hv
  simpa using norm_integral_le_of_norm_le_const hbd'

omit [DecidableEq ι] in
theorem parameterOperator_joint_continuous (label : ι → Bool) :
    Continuous (fun p : ℝ × EuclideanSpace ℝ ι => parameterOperator label p.1 p.2) := by
  change Continuous (fun p : ℝ × EuclideanSpace ℝ ι =>
    coordinateMask label false p.2+p.1 • coordinateMask label true p.2)
  exact ((coordinateMask label false).continuous.comp continuous_snd).add
    (continuous_fst.smul ((coordinateMask label true).continuous.comp continuous_snd))

theorem thermalDeviation_joint_measurable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) :
    Measurable (fun p : ℝ × EuclideanSpace ℝ ι => thermalDeviation ν L label p.2 p.1) := by
  let op := fun p : ℝ × EuclideanSpace ℝ ι => parameterOperator label p.1 p.2
  let sc := fun p : ℝ × EuclideanSpace ℝ ι => parameterScore ν L label p.2 p.1
  have hop : Continuous op := parameterOperator_joint_continuous label
  have hsc : Continuous sc :=
    ((score_contDiff ν L hL hK hb).continuous.comp hop).clm_apply
      ((coordinateMask label true).continuous.comp continuous_snd)
  have heval : Measurable (fun p : (ℝ × EuclideanSpace ℝ ι) × V =>
      L p.2 (coordinateMask label true p.1.2)) := by
    exact (show Continuous (fun p : (EuclideanSpace ℝ ι →L[ℝ] ℝ) × EuclideanSpace ℝ ι => p.1 p.2)
      from continuous_fst.clm_apply continuous_snd).measurable.comp
        ((hL.comp measurable_snd).prodMk
          ((coordinateMask label true).measurable.comp (measurable_snd.comp measurable_fst)))
  have hfield : Measurable (fun p : (ℝ × EuclideanSpace ℝ ι) × V => L p.2 (op p.1)) :=
    (show Continuous (fun p : (EuclideanSpace ℝ ι →L[ℝ] ℝ) × EuclideanSpace ℝ ι => p.1 p.2)
      from continuous_fst.clm_apply continuous_snd).measurable.comp
        ((hL.comp measurable_snd).prodMk (hop.measurable.comp measurable_fst))
  have hm : Measurable (fun p : (ℝ × EuclideanSpace ℝ ι) × V =>
      |L p.2 (coordinateMask label true p.1.2)-sc p.1| * Real.exp (L p.2 (op p.1))) :=
    (continuous_abs.measurable.comp (heval.sub (hsc.measurable.comp measurable_fst))).mul hfield.exp
  have heq : (fun p : ℝ × EuclideanSpace ℝ ι => thermalDeviation ν L label p.2 p.1) =
      fun p => (∫ v,|L v (coordinateMask label true p.2)-sc p| * Real.exp (L v (op p)) ∂ν)/
        moment ν (fun _ => 1) L (op p) := by
    funext p
    rw [thermalDeviation,integral_gibbsMeasure ν L hL hb]
    rfl
  rw [heq]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.div
    ((moment_contDiff ν (fun _ => 1) L measurable_const hL (C := 1) (by norm_num) hK
      (hb.mono fun _ hv => ⟨by norm_num,hv⟩)).continuous.comp hop).measurable

theorem thermalDeviation_gaussian_integrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (x : ℝ) :
    Integrable (fun w => thermalDeviation ν L label w x)
      (SYK.standardGaussianMeasureOnEuclidean ι) := by
  apply ((gaussian_norm_integrable (ι := ι)).const_mul (2*K)).mono'
    ((thermalDeviation_joint_measurable ν L hL hK hb label).comp
      (measurable_const.prodMk measurable_id)).aestronglyMeasurable
  exact .of_forall fun w => thermalDeviation_norm_le ν L hL hK hb label w x

def meanThermalDeviation (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) : ℝ :=
  ∫ w,thermalDeviation ν L label w x ∂SYK.standardGaussianMeasureOnEuclidean ι

theorem meanThermalDeviation_measurable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) :
    Measurable (meanThermalDeviation ν L label) :=
  (thermalDeviation_joint_measurable ν L hL hK hb label).stronglyMeasurable.integral_prod_right'.measurable

theorem meanThermalDeviation_norm_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (x : ℝ) :
    ‖meanThermalDeviation ν L label x‖ ≤
      2*K*(∫ w : EuclideanSpace ℝ ι,‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι) := by
  unfold meanThermalDeviation
  calc
    _ ≤ ∫ w,‖thermalDeviation ν L label w x‖ ∂SYK.standardGaussianMeasureOnEuclidean ι :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ w,2*K*‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι := integral_mono
      (thermalDeviation_gaussian_integrable ν L hL hK hb label x).norm
      ((gaussian_norm_integrable (ι := ι)).const_mul (2*K))
      (fun w => thermalDeviation_norm_le ν L hL hK hb label w x)
    _ = _ := integral_const_mul _ _

theorem meanThermalDeviation_intervalIntegrable (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K) (label : ι → Bool) (l u : ℝ) :
    IntervalIntegrable (meanThermalDeviation ν L label) volume l u := by
  apply IntegrableOn.intervalIntegrable
  have : IsFiniteMeasure (volume.restrict (uIcc l u)) := by
    change IsFiniteMeasure (volume.restrict (Icc (min l u) (max l u)))
    infer_instance
  apply Integrable.of_bound (meanThermalDeviation_measurable ν L hL hK hb label).aestronglyMeasurable
    (2*K*(∫ w : EuclideanSpace ℝ ι,‖w‖ ∂SYK.standardGaussianMeasureOnEuclidean ι))
  exact .of_forall fun x => meanThermalDeviation_norm_le ν L hL hK hb label x

/-- The actual thermal absolute-deviation budget; taking r=√a gives
the usual Cauchy--Schwarz bound without introducing a joint-space proxy. -/
theorem meanThermalDeviation_integral_le (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K a : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool)
    (hdiag : ∀ᵐ v ∂ν, (∑ i, if label i=true then (coordinateObservable L i v)^2 else 0) ≤ a)
    {r : ℝ} (hr : 0 < r) :
    (∫ x in (0 : ℝ)..1,meanThermalDeviation ν L label x) ≤ (a+r^2)/(2*r) := by
  have hp (x : ℝ) : meanThermalDeviation ν L label x ≤
      (meanVariance ν L label x+r^2)/(2*r) := by
    unfold meanThermalDeviation
    calc
      _ ≤ ∫ w,(parameterVariance ν L label w x+r^2)/(2*r)
          ∂SYK.standardGaussianMeasureOnEuclidean ι := integral_mono
        (thermalDeviation_gaussian_integrable ν L hL hK hb label x)
        (((parameterVariance_gaussian_integrable ν L hL hK hb label x).add
          (integrable_const _)).div_const _) (fun w => thermalDeviation_le ν L hL hK hb label w x hr)
      _ = _ := by rw [integral_div,integral_add
        (parameterVariance_gaussian_integrable ν L hL hK hb label x) (integrable_const _)]; simp [meanVariance]
  calc
    _ ≤ ∫ x in (0 : ℝ)..1,(meanVariance ν L label x+r^2)/(2*r) :=
      intervalIntegral.integral_mono_on (by norm_num)
        (meanThermalDeviation_intervalIntegrable ν L hL hK hb label 0 1)
        (((meanVariance_continuous ν L hL hK hb label).add continuous_const).div_const _ |>.intervalIntegrable 0 1)
        (fun x _ => hp x)
    _ = ((∫ x in (0 : ℝ)..1,meanVariance ν L label x)+r^2)/(2*r) := by
      rw [intervalIntegral.integral_div,intervalIntegral.integral_add
        ((meanVariance_continuous ν L hL hK hb label).intervalIntegrable 0 1)
        (intervalIntegrable_const)]; simp
    _ ≤ _ := div_le_div_of_nonneg_right
      (add_le_add (meanVariance_integral_le ν L hL hK hb label hdiag) le_rfl) (by positivity)

end
end SlowEquilibration.GaussianPerturbationDeviation
