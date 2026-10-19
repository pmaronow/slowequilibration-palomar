-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalPanchenkoConvexSpread
public import SlowEquilibration.PureCapturePhysicalShellGG

/-! The unperturbed Panchenko parameter pressure is the literal physical
spherical quenched pressure. The shell subtype changes neither partition
nor Gaussian disorder average. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalPanchenkoPressureTransport

open MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open GaussianSpinInterpolation GaussianSpinComparison GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging
open PureCapturePhysicalShellGG
open scoped RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

theorem parameterLogPartition_full_eq_spherical
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture)
    (β : ℝ) (w : EuclideanDisorder N μ.maxDegree) :
    parameterLogPartition (shellLaw N)
      (shellLinear (mixtureCoefficients μ)) (fun _ => true) w β =
    logPartition (sphereLaw N) (sphereLinear (mixtureCoefficients μ))
      (β • w) := by
  let c := mixtureCoefficients μ
  have hop : parameterOperator (fun _ : Coordinate N μ.maxDegree => true) β w = β • w := by
    ext i
    simp [parameterOperator, coordinateMask, diagonal_apply]
  have hm := moment_map_one (shellLaw N) (Subtype.val : Shell N → Vector N)
    measurable_subtype_coe (sphereLinear c) (sphereLinear_measurable c) (β • w)
  rw [shellLaw_map_coe hN] at hm
  unfold parameterLogPartition logPartition
  rw [hop]
  change Real.log (moment (shellLaw N) (fun _ => 1)
      (fun x : Shell N => sphereLinear c x.val) (β • w)) =
    Real.log (moment (sphereLaw N) (fun _ => 1) (sphereLinear c) (β • w))
  exact congrArg Real.log hm.symm

theorem parameterMean_full_eq_averagedLogPartition
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    parameterMean (shellLaw N)
      (shellLinear (mixtureCoefficients μ)) (fun _ => true) β =
    averagedLogPartition (sphereLaw N)
      (sphereLinear (mixtureCoefficients μ)) β := by
  unfold parameterMean averagedLogPartition
  apply integral_congr_ae
  exact .of_forall fun w => parameterLogPartition_full_eq_spherical hN μ β w

theorem parameterMean_full_div_eq_quenchedPressure
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    parameterMean (shellLaw N)
      (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
      (N : ℝ) = quenchedPressure N μ β := by
  rw [parameterMean_full_eq_averagedLogPartition hN μ β]
  exact gaussianMeanLogPartition_eq_quenchedPressure hN μ β

/-- The normalized original Gibbs energy mean is the derivative of the
literal finite-volume quenched pressure. -/
theorem meanScore_full_div_eq_deriv_quenchedPressure
    {N : ℕ} (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) :
    meanScore (shellLaw N)
      (shellLinear (mixtureCoefficients μ)) (fun _ => true) β /
      (N : ℝ) = deriv (quenchedPressure N μ) β := by
  letI : IsProbabilityMeasure (shellLaw N) := shellLaw_probability hN
  let L := shellLinear (N := N) (mixtureCoefficients μ)
  let K := Real.sqrt ((N : ℝ)*μ.xi 1)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hb : ∀ᵐ x ∂shellLaw N, ‖L x‖ ≤ K := by
    apply Filter.Eventually.of_forall
    intro x
    simpa only [L, K, covariancePolynomial_mixture] using
      shellLinear_bound hN (mixtureCoefficients μ)
        (mixtureCoefficients_nonnegative μ) x
  have hd := parameterMean_hasDerivAt (shellLaw N) L
    (shellLinear_measurable (mixtureCoefficients μ)) hK hb
    (fun _ => true) β
  have hfun : (fun t => parameterMean (shellLaw N) L (fun _ => true) t /
      (N : ℝ)) = quenchedPressure N μ := by
    funext t
    exact parameterMean_full_div_eq_quenchedPressure hN μ t
  have hdiv := hd.div_const (N : ℝ)
  rw [hfun] at hdiv
  exact hdiv.deriv.symm

end SlowEquilibration.PureCapturePhysicalPanchenkoPressureTransport
