-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.PureCapturePhysicalPanchenkoThermalPartition
public import SlowEquilibration.PureCapturePhysicalPanchenkoPressureTransport
public import SlowEquilibration.PureCapturePhysicalPanchenkoSymmetricSpread

/-! The scalar Gibbs second-difference bound for the literal spherical
thermal energy, followed by Gaussian disorder averaging. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoThermalPhysical
open MeasureTheory ProbabilityTheory
open GaussianSpinInterpolation GaussianSpinComparison
open GaussianPerturbationParameter GaussianPerturbationDeviation
open SphericalParisiGibbsTilt
open PureCapturePhysicalPanchenkoThermalPartition
open PureCapturePhysicalPanchenkoPressureTransport
open PureCapturePhysicalPanchenkoSymmetricSpread
open PureCapturePhysicalShellGG SphericalModel SphericalForm
open scoped Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

variable {V ι : Type*} [MeasurableSpace V] [Fintype ι] [DecidableEq ι]

theorem full_parameterOperator (w : EuclideanSpace ℝ ι) (t : ℝ) :
    parameterOperator (fun _ : ι => true) t w = t • w := by
  ext i
  simp [parameterOperator, coordinateMask, diagonal_apply]

theorem full_coordinateMask (w : EuclideanSpace ℝ ι) :
    coordinateMask (fun _ : ι => true) true w = w := by
  ext i
  simp [coordinateMask, diagonal_apply]

theorem full_parameterLogPartition_eq_scalar
    (ν : Measure V) (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ)
    (w : EuclideanSpace ℝ ι) (t : ℝ) :
    parameterLogPartition ν L (fun _ => true) w t =
      Real.log (scalarPartition ν (fun z => t * L z w)) := by
  rw [parameterLogPartition, full_parameterOperator]
  unfold logPartition GaussianSpinInterpolation.moment GaussianSpinInterpolation.weight scalarPartition
  simp only [one_mul]
  change Real.log (∫ z, Real.exp (L z (t • w)) ∂ν) = _
  congr 1
  apply integral_congr_ae
  exact .of_forall fun z => by simp only [map_smul, smul_eq_mul]

theorem full_thermalDeviation_le_log_partition_second_difference
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hb : ∀ᵐ z ∂ν, ‖L z‖ ≤ K)
    (w : EuclideanSpace ℝ ι) (β δ : ℝ) :
    δ * thermalDeviation ν L (fun _ => true) w β ≤
      Real.log 2 + parameterLogPartition ν L (fun _ => true) w (β+δ) +
        parameterLogPartition ν L (fun _ => true) w (β-δ) -
        2 * parameterLogPartition ν L (fun _ => true) w β := by
  let H : V → ℝ := fun z => L z w
  have hH : Measurable H :=
    (ContinuousLinearMap.apply ℝ ℝ w).continuous.measurable.comp hL
  have hbound : ∀ᵐ z ∂ν, |H z| ≤ K*‖w‖ :=
    (directionalObservable_bound ν L hb w).mono fun z hz => hz.1
  have hG : gibbsMeasure ν L (parameterOperator (fun _ : ι => true) β w) =
      scalarGibbs ν (fun z => β*H z) := by
    rw [full_parameterOperator, actual_gaussian_gibbs_eq_scalar]
    congr 1
    funext z
    simp only [H, map_smul, smul_eq_mul]
  have hscore : parameterScore ν L (fun _ => true) w β =
      ∫ z, H z ∂scalarGibbs ν (fun z => β*H z) := by
    rw [show parameterScore ν L (fun _ => true) w β =
      score ν L (parameterOperator (fun _ : ι => true) β w)
        (coordinateMask (fun _ : ι => true) true w) from rfl,
      full_coordinateMask, score_apply ν L hL hb,
      ← integral_gibbsMeasure ν L hL hb, hG]
  have hscalar := scalarGibbs_centered_absolute_le_second_difference
    ν H hH hbound β δ
  dsimp only at hscalar
  rw [← hscore] at hscalar
  change δ * (∫ z, |H z - parameterScore ν L (fun _ => true) w β|
    ∂scalarGibbs ν (fun z => β*H z)) ≤ _ at hscalar
  rw [← hG] at hscalar
  rw [full_parameterLogPartition_eq_scalar ν L w (β+δ),
    full_parameterLogPartition_eq_scalar ν L w (β-δ),
    full_parameterLogPartition_eq_scalar ν L w β]
  simpa only [thermalDeviation, full_coordinateMask, H] using hscalar

/-- Gaussian disorder averaging of the finite-volume thermal bound. -/
theorem full_meanThermalDeviation_le_parameterMean_second_difference
    (ν : Measure V) [IsProbabilityMeasure ν]
    (L : V → EuclideanSpace ℝ ι →L[ℝ] ℝ) (hL : Measurable L)
    {K : ℝ} (hK : 0 ≤ K) (hb : ∀ᵐ z ∂ν, ‖L z‖ ≤ K)
    (β δ : ℝ) :
    δ * meanThermalDeviation ν L (fun _ => true) β ≤
      Real.log 2 + parameterMean ν L (fun _ => true) (β+δ) +
        parameterMean ν L (fun _ => true) (β-δ) -
        2 * parameterMean ν L (fun _ => true) β := by
  let γ := SYK.standardGaussianMeasureOnEuclidean ι
  let q := fun t w => parameterLogPartition ν L (fun _ => true) w t
  have hi0 : Integrable (fun w => thermalDeviation ν L (fun _ => true) w β) γ :=
    thermalDeviation_gaussian_integrable ν L hL hK hb (fun _ => true) β
  have hip : Integrable (q (β+δ)) γ :=
    parameterLogPartition_gaussian_integrable ν L hL hK hb (fun _ => true) (β+δ)
  have him : Integrable (q (β-δ)) γ :=
    parameterLogPartition_gaussian_integrable ν L hL hK hb (fun _ => true) (β-δ)
  have hib : Integrable (q β) γ :=
    parameterLogPartition_gaussian_integrable ν L hL hK hb (fun _ => true) β
  have hir : Integrable (fun w => Real.log 2+q (β+δ) w+q (β-δ) w-2*q β w) γ :=
    (((integrable_const (Real.log 2)).add hip).add him).sub (hib.const_mul 2)
  have hmono := integral_mono (hi0.const_mul δ) hir
    (fun w => full_thermalDeviation_le_log_partition_second_difference ν L hL hb w β δ)
  calc
    δ * meanThermalDeviation ν L (fun _ => true) β =
        ∫ w, δ*thermalDeviation ν L (fun _ => true) w β ∂γ := by
      simp only [meanThermalDeviation, integral_const_mul]
      rfl
    _ ≤ ∫ w, Real.log 2+q (β+δ) w+q (β-δ) w-2*q β w ∂γ := hmono
    _ = Real.log 2 + parameterMean ν L (fun _ => true) (β+δ) +
          parameterMean ν L (fun _ => true) (β-δ) -
          2 * parameterMean ν L (fun _ => true) β := by
      calc
        _ = (∫ w, Real.log 2+q (β+δ) w+q (β-δ) w ∂γ) -
            (∫ w, 2*q β w ∂γ) := by
              exact integral_sub (((integrable_const (Real.log 2)).add hip).add him)
                (hib.const_mul 2)
        _ = ((∫ w, Real.log 2+q (β+δ) w ∂γ) +
            (∫ w, q (β-δ) w ∂γ)) -
            2*(∫ w, q β w ∂γ) := by
              have hplus : (∫ w, Real.log 2+q (β+δ) w+q (β-δ) w ∂γ) =
                  (∫ w, Real.log 2+q (β+δ) w ∂γ) +
                    (∫ w, q (β-δ) w ∂γ) :=
                integral_add ((integrable_const (Real.log 2)).add hip) him
              have hscale : (∫ w, 2*q β w ∂γ) = 2*(∫ w, q β w ∂γ) :=
                integral_const_mul 2 _
              rw [hplus,hscale]
        _ = _ := by
          have hplus : (∫ w, Real.log 2+q (β+δ) w ∂γ) =
              (∫ w, Real.log 2 ∂γ) + (∫ w, q (β+δ) w ∂γ) :=
            integral_add (integrable_const (Real.log 2)) hip
          rw [hplus, integral_const]
          simp only [probReal_univ, one_smul]
          rfl

end SlowEquilibration.PureCapturePhysicalPanchenkoThermalPhysical
