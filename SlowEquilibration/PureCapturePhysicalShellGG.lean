-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.PureCapturePhysicalConvexDerivativeLimit
public import SlowEquilibration.GaussianGGPowerResponse
public import SlowEquilibration.GaussianGibbsTransport

/-! The actual spherical finite-dimensional disorder, carried by an exact
sphere subtype, is a bounded Gaussian replica model. This permits direct
unperturbed covariance integration by parts. -/

@[expose] public section
noncomputable section
namespace SlowEquilibration.PureCapturePhysicalShellGG

open Set Filter MeasureTheory ProbabilityTheory
open SphericalModel SphericalForm
open GaussianReplicaCalculus GaussianPerturbationParameter
open GaussianPerturbationSelfAveraging GaussianPerturbationDeviation
open GaussianPerturbationIntegrated
open GaussianSpinInterpolation GaussianSpinComparison
open scoped Topology BigOperators RealInnerProductSpace

set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option linter.style.haveILetI false

abbrev Shell (N : ℕ) := {x : Vector N // ‖x‖ ^ 2 = (N : ℝ)}

def shellLaw (N : ℕ) : Measure (Shell N) :=
  Measure.comap Subtype.val (sphereLaw N)

theorem shellLaw_map_coe {N : ℕ} (hN : 1 ≤ N) :
    (shellLaw N).map (Subtype.val : Shell N → Vector N) = sphereLaw N := by
  unfold shellLaw
  change (Measure.comap (Subtype.val : Shell N → Vector N)
    (sphereLaw N)).map Subtype.val = sphereLaw N
  have hh := map_comap_subtype_coe
    (s := {x : Vector N | ‖x‖ ^ 2 = (N : ℝ)})
    (isClosed_eq (continuous_norm.pow 2) continuous_const).measurableSet
    (sphereLaw N)
  exact hh.trans (Measure.restrict_eq_self_of_ae_mem (sphereLaw_support hN))

theorem shellLaw_probability {N : ℕ} (hN : 1 ≤ N) :
    IsProbabilityMeasure (shellLaw N) := by
  have hm := shellLaw_map_coe hN
  have h := congrArg (fun ν : Measure (Vector N) => ν univ) hm
  rw [Measure.map_apply measurable_subtype_coe MeasurableSet.univ] at h
  exact ⟨by simpa using h⟩

def shellLinear {N P : ℕ} (c : Degree P → ℝ) :
    Shell N → EuclideanDisorder N P →L[ℝ] ℝ :=
  fun x => sphereLinear c x.val

theorem shellLinear_measurable {N P : ℕ} (c : Degree P → ℝ) :
    Measurable (shellLinear (N := N) c) :=
  (sphereLinear_measurable c).comp measurable_subtype_coe

theorem shellLinear_norm {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Shell N) :
    ‖shellLinear c x‖ =
      Real.sqrt ((N : ℝ) * covariancePolynomial c 1) := by
  rw [shellLinear, sphereLinear, innerSL_apply_norm]
  exact fieldFeature_norm hN c hc x.val x.property

theorem shellLinear_bound {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (x : Shell N) :
    ‖shellLinear c x‖ ≤
      Real.sqrt ((N : ℝ) * covariancePolynomial c 1) :=
  (shellLinear_norm hN c hc x).le

theorem shellParameterLinear_apply {N P : ℕ}
    (c : Degree P → ℝ) (β : ℝ) (x : Shell N)
    (g : EuclideanDisorder N P) :
    parameterLinear (shellLinear c) (fun _ => true) β x g =
      sphereLinear c x.val (β • g) := by
  have hop : parameterOperator (fun _ : Coordinate N P => true) β g = β • g := by
    ext i
    simp [parameterOperator, coordinateMask, diagonal_apply]
  simp only [parameterLinear, ContinuousLinearMap.comp_apply, hop,
    shellLinear]

theorem shellGibbsLaw_map {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (β : ℝ)
    (g : EuclideanDisorder N μ.maxDegree) :
    (gibbsMeasure (shellLaw N)
      (parameterLinear (shellLinear (mixtureCoefficients μ))
        (fun _ => true) β) g).map Subtype.val =
      gibbsLaw N β (field (mixtureCoefficients μ) (unpackDisorder g)) := by
  have heq : ∀ᵐ x ∂shellLaw N,
      parameterLinear (shellLinear (mixtureCoefficients μ))
        (fun _ => true) β x g =
      sphereLinear (mixtureCoefficients μ) x.val (β • g) :=
    .of_forall (shellParameterLinear_apply _ β · g)
  rw [gibbsMeasure_map_of_field_eq (shellLaw N) Subtype.val
    measurable_subtype_coe _ g (sphereLinear (mixtureCoefficients μ))
      (sphereLinear_measurable _) (β • g) heq,
    shellLaw_map_coe hN, gaussianGibbs_eq_gibbsLaw]

theorem shellSelectedKernel_eq_covariance {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (x y : Shell N) :
    selectedKernel (shellLinear (mixtureCoefficients μ)) (fun _ => true) x y =
      (N : ℝ) * μ.xi (overlap x.val y.val) := by
  classical
  calc
    _ = inner ℝ (fieldFeature (mixtureCoefficients μ) x.val)
        (fieldFeature (mixtureCoefficients μ) y.val) := by
      simp [selectedKernel, shellLinear, sphereLinear, innerSL_apply_apply,
        PiLp.inner_apply, RCLike.inner_apply, mul_comm]
    _ = _ := by
      rw [fieldFeature_inner_gram hN _ (mixtureCoefficients_nonnegative μ),
        covariancePolynomial_mixture]

/-- Unperturbed finite spherical covariance GG defect is controlled by
the actual thermal and disorder energy fluctuations. The Gaussian field,
its sphere law, and its covariance kernel are all the physical ones. -/
theorem shellCovarianceGG_error_le {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {β : ℝ} (hβ : 0 < β) (m : ℕ)
    (f : (Fin (m+1) → Shell N) → ℝ)
    (hf : Measurable f) (hfb : ∀ σ, |f σ| ≤ 1) :
    |covarianceGG (shellLaw N)
      (parameterLinear (shellLinear (mixtureCoefficients μ)) (fun _ => true) β)
      (fun x y : Shell N => μ.xi (overlap x.val y.val)) m f| ≤
      (meanThermalDeviation
        (shellLaw N) (shellLinear (mixtureCoefficients μ))
        (fun _ => true) β +
       energyFluctuation
        (shellLaw N) (shellLinear (mixtureCoefficients μ))
        (fun _ => true) β) / (((m : ℝ)+1)*β*(N : ℝ)) := by
  letI : IsProbabilityMeasure (shellLaw N) := shellLaw_probability hN
  let L := shellLinear (N := N) (mixtureCoefficients μ)
  let label : Coordinate N μ.maxDegree → Bool := fun _ => true
  let K := Real.sqrt ((N : ℝ)*μ.xi 1)
  have hK : 0 ≤ K := Real.sqrt_nonneg _
  have hb (x : Shell N) : ‖L x‖ ≤ K := by
    simpa only [L, K, covariancePolynomial_mixture] using
      shellLinear_bound hN (mixtureCoefficients μ)
        (mixtureCoefficients_nonnegative μ) x
  have hdiag (x : Shell N) : selectedKernel L label x x =
      (N : ℝ)*μ.xi 1 := by
    rw [show selectedKernel L label x x =
      (N : ℝ)*μ.xi (overlap x.val x.val) from
      shellSelectedKernel_eq_covariance hN μ x x,
      overlap_self (by omega) x.val x.property]
  have hbase := covarianceGG_le_selected_deviation
    (shellLaw N) L (shellLinear_measurable (mixtureCoefficients μ))
      hK hb label β ((N : ℝ)*μ.xi 1) hβ hdiag m f hf hfb
  have hker : selectedKernel L label =
      fun x y : Shell N => (N : ℝ)*μ.xi (overlap x.val y.val) := by
    funext x y
    exact shellSelectedKernel_eq_covariance hN μ x y
  rw [hker, covarianceGG_const_mul, abs_mul,
    abs_of_pos (Nat.cast_pos.mpr (by omega : 0 < N))] at hbase
  have hden : 0 < ((m : ℝ)+1)*β := mul_pos (by positivity) hβ
  have hNr : (0 : ℝ) < N := Nat.cast_pos.mpr (by omega)
  exact (le_div_iff₀ (mul_pos hden hNr)).mpr (by
    apply (le_div_iff₀ hden).mp at hbase
    nlinarith)

end SlowEquilibration.PureCapturePhysicalShellGG
