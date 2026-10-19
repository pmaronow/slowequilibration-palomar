-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPanchenkoEnergyToGG

/-! The actual annealed Gibbs absolute-energy deviation appearing in the
manuscript, and its finite-volume comparison with the thermal and disorder
terms used by Gaussian integration by parts. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoActualDeviation

open MeasureTheory ProbabilityTheory
open GaussianSpinInterpolation GaussianSpinComparison
open GaussianPerturbationParameter GaussianPerturbationSelfAveraging
open GaussianPerturbationDeviation GaussianPerturbationIntegrated
open scoped Topology
set_option autoImplicit false
set_option maxHeartbeats 1400000
set_option linter.style.haveILetI false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

/-- The original two-stage average, first under the genuine Gibbs measure
for each disorder and then under the original standard Gaussian disorder. -/
def meanAbsoluteEnergyDeviation
    (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (label : ι → Bool) (x : ℝ) : ℝ :=
  ∫ w, (∫ v,
      |L v (coordinateMask label true w)-meanScore ν L label x|
        ∂gibbsMeasure ν L (parameterOperator label x w))
    ∂SYK.standardGaussianMeasureOnEuclidean ι

omit [DecidableEq ι] in
theorem absoluteEnergyDeviation_inner_measurable
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) :
    Measurable (fun w : EuclideanSpace ℝ ι =>
      ∫ v, |L v (coordinateMask label true w)-meanScore ν L label x|
        ∂gibbsMeasure ν L (parameterOperator label x w)) := by
  let op := fun w : EuclideanSpace ℝ ι => parameterOperator label x w
  let c := meanScore ν L label x
  have hop : Continuous op := (parameterOperator label x).continuous
  have heval : Measurable (fun p : (EuclideanSpace ℝ ι) × V =>
      L p.2 (coordinateMask label true p.1)) := by
    exact (show Continuous (fun p : (EuclideanSpace ℝ ι →L[ℝ] ℝ) ×
        EuclideanSpace ℝ ι => p.1 p.2)
      from continuous_fst.clm_apply continuous_snd).measurable.comp
        ((hL.comp measurable_snd).prodMk
          ((coordinateMask label true).measurable.comp measurable_fst))
  have hfield : Measurable (fun p : (EuclideanSpace ℝ ι) × V =>
      L p.2 (op p.1)) := by
    exact (show Continuous (fun p : (EuclideanSpace ℝ ι →L[ℝ] ℝ) ×
        EuclideanSpace ℝ ι => p.1 p.2)
      from continuous_fst.clm_apply continuous_snd).measurable.comp
        ((hL.comp measurable_snd).prodMk (hop.measurable.comp measurable_fst))
  have hm : Measurable (fun p : (EuclideanSpace ℝ ι) × V =>
      |L p.2 (coordinateMask label true p.1)-c| *
        Real.exp (L p.2 (op p.1))) :=
    (continuous_abs.measurable.comp (heval.sub_const c)).mul hfield.exp
  have heq : (fun w : EuclideanSpace ℝ ι =>
      ∫ v, |L v (coordinateMask label true w)-c|
        ∂gibbsMeasure ν L (op w)) =
      fun w => (∫ v, |L v (coordinateMask label true w)-c| *
          Real.exp (L v (op w)) ∂ν) /
        moment ν (fun _ => 1) L (op w) := by
    funext w
    rw [integral_gibbsMeasure ν L hL hb]
    rfl
  rw [heq]
  exact hm.stronglyMeasurable.integral_prod_right'.measurable.div
    ((moment_contDiff ν (fun _ => 1) L measurable_const hL (C := 1)
      (by norm_num) hK (hb.mono fun _ hv => ⟨by norm_num, hv⟩)).continuous.comp
        hop).measurable

theorem absoluteEnergyDeviation_inner_le
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) (w : EuclideanSpace ℝ ι) :
    (∫ v, |L v (coordinateMask label true w)-meanScore ν L label x|
        ∂gibbsMeasure ν L (parameterOperator label x w)) ≤
      thermalDeviation ν L label w x +
        |parameterScore ν L label w x-meanScore ν L label x| := by
  let G := gibbsMeasure ν L (parameterOperator label x w)
  let ρ := fun v => L v (coordinateMask label true w)
  let s := parameterScore ν L label w x
  let c := meanScore ν L label x
  letI : IsProbabilityMeasure G := gibbsMeasure_probability ν L hL hb _
  have hρ : Measurable ρ :=
    (ContinuousLinearMap.apply ℝ ℝ (coordinateMask label true w)).continuous.measurable.comp hL
  have hρbd : ∀ᵐ v ∂G, |ρ v| ≤ K*‖w‖ := by
    apply ((directionalObservable_bound ν L hb (coordinateMask label true w)).mono
      fun v hv => hv.1.trans (mul_le_mul_of_nonneg_left
        (coordinateMask_norm_le label true w) hK)).filter_mono
      (gibbsMeasure_absolutelyContinuous ν L _).ae_le
  have hρi : Integrable ρ G := by
    apply Integrable.of_bound hρ.aestronglyMeasurable (K*‖w‖)
    exact hρbd.mono fun v hv => by simpa only [Real.norm_eq_abs] using hv
  have hi : Integrable (fun v => |ρ v-c|) G :=
    (hρi.sub (integrable_const c)).abs
  have ht : Integrable (fun v => |ρ v-s|) G :=
    (hρi.sub (integrable_const s)).abs
  have hpoint (v : V) : |ρ v-c| ≤ |ρ v-s|+|s-c| := by
    have heq : ρ v-c = (ρ v-s)+(s-c) := by ring
    rw [heq]
    exact abs_add_le _ _
  have hle := integral_mono hi (ht.add (integrable_const _)) hpoint
  simp only [Pi.add_apply] at hle
  rw [integral_add ht (integrable_const _), integral_const, probReal_univ,
    one_smul] at hle
  change (∫ v, |ρ v-c| ∂G) ≤ (∫ v, |ρ v-s| ∂G)+|s-c|
  exact hle

theorem meanAbsoluteEnergyDeviation_le_totalDeviation
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ v ∂ν, ‖L v‖ ≤ K)
    (label : ι → Bool) (x : ℝ) :
    meanAbsoluteEnergyDeviation ν L label x ≤
      meanThermalDeviation ν L label x + energyFluctuation ν L label x := by
  let G := SYK.standardGaussianMeasureOnEuclidean ι
  let c := meanScore ν L label x
  let A := fun w : EuclideanSpace ℝ ι =>
    ∫ v, |L v (coordinateMask label true w)-c|
      ∂gibbsMeasure ν L (parameterOperator label x w)
  let T := fun w : EuclideanSpace ℝ ι => thermalDeviation ν L label w x
  let Q := fun w : EuclideanSpace ℝ ι => |parameterScore ν L label w x-c|
  have hTi : Integrable T G :=
    thermalDeviation_gaussian_integrable ν L hL hK hb label x
  have hQi : Integrable Q G := by
    simpa only [Q, Pi.sub_apply, Real.norm_eq_abs] using
      ((parameterScore_gaussian_integrable ν L hL hK hb label x).sub
        (integrable_const c)).norm
  have hAi : Integrable A G := by
    apply (hTi.add hQi).mono'
      (absoluteEnergyDeviation_inner_measurable ν L hL hK hb label x).aestronglyMeasurable
    exact .of_forall fun w => by
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun v => abs_nonneg _)]
      exact absoluteEnergyDeviation_inner_le ν L hL hK hb label x w
  change (∫ w, A w ∂G) ≤ (∫ w, T w ∂G)+(∫ w, Q w ∂G)
  calc
    _ ≤ ∫ w, T w+Q w ∂G :=
      integral_mono hAi (hTi.add hQi)
        (fun w => absoluteEnergyDeviation_inner_le ν L hL hK hb label x w)
    _ = _ := integral_add hTi hQi

open SphericalModel SphericalForm
open PureCapturePhysicalShellGG
open PureCapturePhysicalPanchenkoEnergyToGG
open Filter

/-- The literal two-stage annealed Gibbs absolute-energy deviation is
sublinear whenever the physical thermal term is, at a differentiability
point of the limiting pressure. -/
theorem physical_mean_absolute_energy_deviation_tendsto_zero_of_thermal
    (μ : FiniteMixture) (β : ℝ) (p : ℝ → ℝ)
    (hp : ∀ t, Tendsto (fun n : ℕ => quenchedPressure (n+2) μ t)
      atTop (𝓝 (p t)))
    (hpdiff : DifferentiableAt ℝ p β)
    (hthermal : Tendsto (fun n : ℕ =>
      meanThermalDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      meanAbsoluteEnergyDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ)) atTop (𝓝 0) := by
  have hbudget := physical_total_energy_budget_tendsto_zero_of_thermal
    μ β p hp hpdiff hthermal
  have hupper (n : ℕ) :
      meanAbsoluteEnergyDeviation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
            ((n+2 : ℕ) : ℝ) ≤
      (meanThermalDeviation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β +
        energyFluctuation (shellLaw (n+2))
          (shellLinear (mixtureCoefficients μ)) (fun _ => true) β) /
            ((n+2 : ℕ) : ℝ) := by
    letI : IsProbabilityMeasure (shellLaw (n+2)) := shellLaw_probability (by omega)
    let L := shellLinear (N := n+2) (mixtureCoefficients μ)
    let K := Real.sqrt (((n+2 : ℕ) : ℝ)*μ.xi 1)
    have hb : ∀ᵐ v ∂shellLaw (n+2), ‖L v‖ ≤ K := by
      apply Filter.Eventually.of_forall
      intro v
      simpa only [L,K,covariancePolynomial_mixture] using
        shellLinear_bound (by omega : 1 ≤ n+2) (mixtureCoefficients μ)
          (mixtureCoefficients_nonnegative μ) v
    have h := meanAbsoluteEnergyDeviation_le_totalDeviation
      (shellLaw (n+2)) L (shellLinear_measurable (mixtureCoefficients μ))
      (Real.sqrt_nonneg _) hb (fun _ => true) β
    exact div_le_div_of_nonneg_right h (by positivity)
  have hlower (n : ℕ) : 0 ≤
      meanAbsoluteEnergyDeviation (shellLaw (n+2))
        (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
          ((n+2 : ℕ) : ℝ) := by
    unfold meanAbsoluteEnergyDeviation
    exact div_nonneg (integral_nonneg fun w =>
      integral_nonneg fun v => abs_nonneg _) (by positivity)
  exact squeeze_zero hlower hupper hbudget

end SlowEquilibration.PureCapturePhysicalPanchenkoActualDeviation
