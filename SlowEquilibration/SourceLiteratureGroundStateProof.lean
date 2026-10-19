-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceMixedCountCapturePackage
public import SlowEquilibration.SphericalParisiUniformSphereDualPressure

/-!
# The finite-dimensional Chen–Sen comparison and a variational reduction

The finite-dimensional Laplace comparison uses the actual ordered tensor
field, its integrable derivative envelope, and normalized surface measure.
The comparison and Chen's formula prove existence of a common scalar limit
for the expected ground energies and normalized variational values. The
final reduction separates this result from the two zero-temperature
variational steps: recovery of every ground profile and compactness of
finite-temperature minimizers. These remaining steps are explicit theorem
hypotheses, not asserted literature results.

This file does not establish the full Chen–Sen interface from Chen's
formula alone: the recovery and liminf compactness statements below remain
unproved. The downstream `_reduced` theorems replace the ground-state
interface by these two explicitly named, purely variational hypotheses.

The source is Chen–Sen, arXiv:1512.08492v2, Section 2, especially Lemmas 1–6
and the proof of Theorem 1. Chen's finite-temperature Parisi formula enters
only when passing the finite-dimensional pressure to its variational value.
-/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceLiteratureGroundStateProof

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel PureTensorJetBounds FiniteTensorMixtureMaximum
open SphericalParisiGroundRSUpper SphericalParisiSphereNet
open SphericalParisiLabeledOriginalEndpoint SphericalParisiUniformSphereDualPressure
open GaussianSpinInterpolation SourceLiteratureGroundState SourceLiteratureParisi
open scoped Topology RealInnerProductSpace

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private theorem logPartition_le_maximum {σ : Type*} [Fintype σ]
    {N : ℕ} (hN : 0 < N) (ν : Measure (UnitSphere N)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) {β : ℝ} (hβ : 0 < β)
    (g : EuclideanSpace ℝ (Coordinate N d)) :
    logPartition ν (spinLinear d c β) g ≤ β * actualMaximum d c g := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  let f : C(UnitSphere N, ℝ) :=
    ⟨fun x => inner ℝ (feature d c x.val) g,
      (((feature_continuous d c).comp continuous_subtype_val).inner continuous_const)⟩
  have hi : Integrable (fun x => Real.exp (β * f x)) ν :=
    ((f.continuous.const_mul β).rexp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hb (x : UnitSphere N) : f x ≤ actualMaximum d c g :=
    le_ciSup (SphericalParisiContinuousMaximum.evaluation_bddAbove f) x
  have hZ : (∫ x, Real.exp (β * f x) ∂ν) ≤
      Real.exp (β * actualMaximum d c g) := by
    simpa only [integral_const, probReal_univ, one_smul] using
      integral_mono hi (integrable_const (Real.exp (β * actualMaximum d c g)))
        (fun x => Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (hb x) hβ.le))
  have hp : 0 < ∫ x, Real.exp (β * f x) ∂ν :=
    integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hi |>.mpr
      (by simp [Function.support, Real.exp_ne_zero])
  have H := Real.log_le_log hp hZ
  simpa only [logPartition, GaussianSpinInterpolation.moment, weight, spinLinear, innerSL_apply_apply,
    real_inner_smul_left, one_mul, Real.log_exp, f, ContinuousMap.coe_mk] using H

private theorem maximum_le_logPartition_of_cap {σ : Type*} [Fintype σ]
    {N : ℕ} (hN : 0 < N) (ν : Measure (UnitSphere N)) [IsProbabilityMeasure ν]
    (d : σ → ℕ) (c : σ → ℝ) (hd : ∀ i, 1 ≤ d i)
    {ε β p : ℝ} (hβ : 0 < β) (hp : 0 < p)
    (hcap : ∀ x : UnitSphere N, p ≤ ν.real {y | ‖y.val - x.val‖ ≤ ε})
    (g : EuclideanSpace ℝ (Coordinate N d)) :
    actualMaximum d c g ≤ logPartition ν (spinLinear d c β) g / β -
      Real.log p / β + derivativeEnvelope d c g * ε := by
  classical
  let : NeZero N := ⟨hN.ne'⟩
  let f : UnitSphere N → ℝ := fun x => inner ℝ (feature d c x.val) g
  have hf : Continuous f :=
    (((feature_continuous d c).comp continuous_subtype_val).inner continuous_const)
  have hi : Integrable (fun x => Real.exp (β * f x)) ν :=
    ((hf.const_mul β).rexp).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hlog : logPartition ν (spinLinear d c β) g =
      Real.log (∫ x, Real.exp (β * f x) ∂ν) := by
    simp only [logPartition, GaussianSpinInterpolation.moment, weight, spinLinear, innerSL_apply_apply,
      real_inner_smul_left, one_mul, f]
  apply ciSup_le
  intro x
  let A : Set (UnitSphere N) := {y | ‖y.val - x.val‖ ≤ ε}
  have hA : MeasurableSet A := by
    exact measurableSet_le (by fun_prop) measurable_const
  have hlocal : ∀ y ∈ A, f x - derivativeEnvelope d c g * ε ≤ f y := by
    intro y hy
    change ‖y.val - x.val‖ ≤ ε at hy
    have H := (original_field_increment_le hN d c hd g x y).trans
      (mul_le_mul_of_nonneg_left (by simpa only [norm_sub_rev] using hy)
        (derivativeEnvelope_nonneg hN d c g))
    have H' := (abs_le.mp H).2
    dsimp [f] at *
    linarith
  have hbound : Real.exp (β * (f x - derivativeEnvelope d c g * ε)) * p ≤
      ∫ y, Real.exp (β * f y) ∂ν := by
    calc
      _ ≤ Real.exp (β * (f x - derivativeEnvelope d c g * ε)) * ν.real A :=
        mul_le_mul_of_nonneg_left (hcap x) (Real.exp_pos _).le
      _ = ∫ _y in A, Real.exp (β * (f x - derivativeEnvelope d c g * ε)) ∂ν := by
        rw [setIntegral_const]
        simp only [measureReal_def, smul_eq_mul, mul_comm]
      _ ≤ ∫ y in A, Real.exp (β * f y) ∂ν :=
        setIntegral_mono_on (integrable_const _).integrableOn hi.integrableOn hA
          (fun y hy => Real.exp_le_exp.mpr
            (mul_le_mul_of_nonneg_left (hlocal y hy) hβ.le))
      _ ≤ _ := setIntegral_le_integral hi (.of_forall fun _ => (Real.exp_pos _).le)
  have H := Real.log_le_log (mul_pos (Real.exp_pos _) hp) hbound
  rw [Real.log_mul (Real.exp_ne_zero _) hp.ne', Real.log_exp, ← hlog] at H
  have H' := (div_le_div_iff_of_pos_right hβ).mpr H
  simp only [add_div, mul_div_cancel_left₀ _ hβ.ne'] at H'
  dsimp only [f] at H'
  linarith

private theorem unit_cap_mass_eq {N : ℕ} (hN : 0 < N) (ε : ℝ)
    (x y : UnitSphere N) :
    (unitSphereProbability N).real {z | ‖z.val - x.val‖ ≤ ε} =
      (unitSphereProbability N).real {z | ‖z.val - y.val‖ ≤ ε} := by
  have hroot : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hN)
  have hpre (a : UnitSphere N) :
      physicalAxis ⁻¹' Metric.closedBall (physicalAxis a) (Real.sqrt (N : ℝ) * ε) =
        {z : UnitSphere N | ‖z.val - a.val‖ ≤ ε} := by
    ext z
    simp only [mem_preimage, Metric.mem_closedBall, dist_eq_norm, physicalAxis,
      ← smul_sub, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_iff_right₀ hroot
  have htransport (a : UnitSphere N) :
      (unitSphereProbability N).real {z | ‖z.val - a.val‖ ≤ ε} =
        (sphereLaw N).real (Metric.closedBall (physicalAxis a) (Real.sqrt (N : ℝ) * ε)) := by
    rw [← unitSphereProbability_physical_map (by omega : 1 ≤ N),
      map_measureReal_apply (physicalAxis_measurable N) measurableSet_closedBall,
      hpre a]
  let U := ((ℝ ∙ (physicalAxis x - physicalAxis y))ᗮ).reflection
  have hnorm : ‖physicalAxis x‖ = ‖physicalAxis y‖ := by
    simp only [physicalAxis, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), unit_norm, mul_one]
  have hU : U (physicalAxis x) = physicalAxis y := Submodule.reflection_sub hnorm
  rw [htransport x, htransport y]
  calc
    _ = (sphereLaw N).real (U ⁻¹' Metric.closedBall (physicalAxis y)
        (Real.sqrt (N : ℝ) * ε)) := by
      rw [← hU, U.isometry.preimage_closedBall]
    _ = ((sphereLaw N).map U).real (Metric.closedBall (physicalAxis y)
        (Real.sqrt (N : ℝ) * ε)) :=
      (map_measureReal_apply U.continuous.measurable measurableSet_closedBall).symm
    _ = _ := by rw [sphereLaw_rotation_invariant U]

private theorem unit_cap_mass_lower {N : ℕ} (hN : 0 < N)
    {ε : ℝ} (hε : 0 < ε) (x : UnitSphere N) :
    Real.exp (-(N : ℝ) * Real.log (1 + 2 / ε)) ≤
      (unitSphereProbability N).real {z | ‖z.val - x.val‖ ≤ ε} := by
  classical
  let := unitSphereProbability_isProbability (by omega : 1 ≤ N)
  obtain ⟨k, points, hk, hcover, hcard⟩ := exists_unitSphere_net hN hε
  have hcov : (⋃ j : Fin k, {z : UnitSphere N | ‖z.val - (points j).val‖ ≤ ε}) = univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨j, hj⟩ := hcover z
    exact mem_iUnion.mpr ⟨j, hj⟩
  have heq (j : Fin k) :
      (unitSphereProbability N).real {z | ‖z.val - (points j).val‖ ≤ ε} =
        (unitSphereProbability N).real {z | ‖z.val - x.val‖ ≤ ε} :=
    unit_cap_mass_eq hN ε (points j) x
  have hm : 1 ≤ (k : ℝ) * (unitSphereProbability N).real {z | ‖z.val - x.val‖ ≤ ε} := by
    calc
      1 = (unitSphereProbability N).real (⋃ j : Fin k,
          {z : UnitSphere N | ‖z.val - (points j).val‖ ≤ ε}) := by rw [hcov]; simp
      _ ≤ ∑ j : Fin k, (unitSphereProbability N).real
          {z | ‖z.val - (points j).val‖ ≤ ε} := measureReal_iUnion_fintype_le _
      _ = _ := by
        simp_rw [heq]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hmpos : 0 < (unitSphereProbability N).real {z | ‖z.val - x.val‖ ≤ ε} := by
    by_contra h
    have hz : (unitSphereProbability N).real {z | ‖z.val - x.val‖ ≤ ε} = 0 :=
      le_antisymm (le_of_not_gt h) measureReal_nonneg
    rw [hz, mul_zero] at hm
    norm_num at hm
  have H := Real.log_le_log (by norm_num : (0 : ℝ) < 1) hm
  rw [Real.log_one, Real.log_mul (Nat.cast_pos.mpr hk).ne' hmpos.ne'] at H
  have hl : -(N : ℝ) * Real.log (1 + 2 / ε) ≤
      Real.log ((unitSphereProbability N).real {z | ‖z.val - x.val‖ ≤ ε}) := by linarith
  simpa only [Real.exp_log hmpos] using Real.exp_le_exp.mpr hl

private theorem finite_laplace_comparison (μ : FiniteMixture) {N : ℕ}
    (hN : 0 < N) {ε β : ℝ} (hε : 0 < ε) (hβ : 0 < β) :
    0 ≤ canonicalGroundEnergy μ N - quenchedPressure N μ β / β ∧
      canonicalGroundEnergy μ N - quenchedPressure N μ β / β ≤
        Real.log (1 + 2 / ε) / β +
          derivativeConstant (SphericalParisiFiniteMixtureGroundBridge.tensorDegree μ)
            (SphericalParisiFiniteMixtureGroundBridge.tensorCoefficient μ) * ε := by
  classical
  let d := SphericalParisiFiniteMixtureGroundBridge.tensorDegree μ
  let c := SphericalParisiFiniteMixtureGroundBridge.tensorCoefficient μ
  let ν := unitSphereProbability N
  let := unitSphereProbability_isProbability (by omega : 1 ≤ N)
  have hd (i) : 1 ≤ d i := by
    change 1 ≤ SphericalParisiFiniteMixtureGroundBridge.tensorDegree μ i
    have := SphericalParisiFiniteMixtureGroundBridge.tensorDegree_ge_two μ i
    omega
  have hNr : 0 < (N : ℝ) := Nat.cast_pos.mpr hN
  have hi := actualMaximum_integrable hN d c
  have hLp := originalSpinLogPartition_integrable ν d c β
  have hD := derivativeEnvelope_integrable hN d c
  have hlow : originalSpinPressure ν d c β ≤
      β * ∫ g, actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d) := by
    simpa only [originalSpinPressure, integral_const_mul] using
      integral_mono hLp (hi.const_mul β) (logPartition_le_maximum hN ν d c hβ)
  have hupper : (∫ g, actualMaximum (N := N) d c g
      ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) ≤
        originalSpinPressure ν d c β / β +
          (N : ℝ) * Real.log (1 + 2 / ε) / β +
            derivativeConstant d c * (N : ℝ) * ε := by
    calc
      _ ≤ ∫ g, (logPartition ν (spinLinear d c β) g / β +
          (N : ℝ) * Real.log (1 + 2 / ε) / β) + derivativeEnvelope d c g * ε
          ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d) := by
        apply integral_mono hi (((hLp.div_const β).add (integrable_const _)).add (hD.mul_const ε))
        intro g
        have H := maximum_le_logPartition_of_cap hN ν d c hd hβ
          (Real.exp_pos (-(N : ℝ) * Real.log (1 + 2 / ε)))
          (unit_cap_mass_lower hN hε) g
        rw [Real.log_exp] at H
        simpa only [Pi.add_apply, neg_mul, neg_div, sub_neg_eq_add] using H
      _ = originalSpinPressure ν d c β / β +
          (N : ℝ) * Real.log (1 + 2 / ε) / β +
            (∫ g, derivativeEnvelope d c g
              ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) * ε := by
        rw [integral_add (f := fun g => logPartition ν (spinLinear d c β) g / β +
            (N : ℝ) * Real.log (1 + 2 / ε) / β)
          (g := fun g => derivativeEnvelope d c g * ε)
          ((hLp.div_const β).fun_add (integrable_const ((N : ℝ) * Real.log (1 + 2 / ε) / β)))
          (hD.mul_const ε),
          integral_add (f := fun g => logPartition ν (spinLinear d c β) g / β)
          (g := fun _ => (N : ℝ) * Real.log (1 + 2 / ε) / β)
          (hLp.div_const β) (integrable_const _), integral_div,
          integral_const, integral_mul_const]
        simp only [probReal_univ, one_smul, originalSpinPressure]
      _ ≤ _ := add_le_add_right
        (mul_le_mul_of_nonneg_right (expected_derivativeEnvelope_le hN d c hd) hε.le) _
  have hP : originalSpinPressure ν d c β / (N : ℝ) = quenchedPressure N μ β :=
    uniform_originalSpinPressure_eq_quenchedPressure (by omega) μ β
  have hL := div_le_div_of_nonneg_right
    ((div_le_iff₀ hβ).mpr (by nlinarith [hlow]) : originalSpinPressure ν d c β / β ≤
      ∫ g, actualMaximum (N := N) d c g
        ∂SYK.standardGaussianMeasureOnEuclidean (Coordinate N d)) hNr.le
  have hU := div_le_div_of_nonneg_right hupper hNr.le
  have hdiv : (originalSpinPressure ν d c β / β) / (N : ℝ) =
      quenchedPressure N μ β / β := by rw [← hP]; ring
  rw [hdiv] at hL
  rw [add_div, add_div, hdiv] at hU
  have hcancel : ((N : ℝ) * Real.log (1 + 2 / ε) / β) / (N : ℝ) =
      Real.log (1 + 2 / ε) / β := by field_simp
  have hcancelD : (derivativeConstant d c * (N : ℝ) * ε) / (N : ℝ) =
      derivativeConstant d c * ε := by field_simp
  rw [hcancel, hcancelD] at hU
  change quenchedPressure N μ β / β ≤ canonicalGroundEnergy μ N at hL
  change canonicalGroundEnergy μ N ≤ quenchedPressure N μ β / β +
    Real.log (1 + 2 / ε) / β + derivativeConstant d c * ε at hU
  exact ⟨sub_nonneg.mpr hL, by linarith⟩

/-- An explicit mixture-dependent, dimension-independent Laplace constant. -/
def laplaceConstant (μ : FiniteMixture) : ℝ :=
  derivativeConstant (SphericalParisiFiniteMixtureGroundBridge.tensorDegree μ)
    (SphericalParisiFiniteMixtureGroundBridge.tensorCoefficient μ) + Real.log 3 + 1

/-- Chen–Sen's finite-dimensional zero-temperature comparison for the
literal Gaussian Hamiltonian and normalized spherical pressure. -/
theorem finite_maximum_pressure_error (μ : FiniteMixture) {N : ℕ}
    (hN : 0 < N) {β : ℝ} (hβ : 1 ≤ β) :
    |canonicalGroundEnergy μ N - quenchedPressure N μ β / β| ≤
      laplaceConstant μ * (Real.log β + 1) / β := by
  have hb : 0 < β := zero_lt_one.trans_le hβ
  obtain ⟨hlow, hhigh⟩ := finite_laplace_comparison μ hN (one_div_pos.mpr hb) hb
  rw [abs_of_nonneg hlow]
  have hlog : Real.log (1 + 2 / (1 / β)) ≤ Real.log 3 + Real.log β := by
    have hle : 1 + 2 / (1 / β) ≤ 3 * β := by
      simp only [one_div, div_inv_eq_mul]
      linarith
    have H := Real.log_le_log (by positivity : 0 < 1 + 2 / (1 / β)) hle
    rwa [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hb.ne'] at H
  have hβlog : 0 ≤ Real.log β := Real.log_nonneg hβ
  have hD := derivativeConstant_nonneg
    (SphericalParisiFiniteMixtureGroundBridge.tensorDegree μ)
    (SphericalParisiFiniteMixtureGroundBridge.tensorCoefficient μ)
  have h3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  calc
    _ ≤ Real.log (1 + 2 / (1 / β)) / β +
        derivativeConstant (SphericalParisiFiniteMixtureGroundBridge.tensorDegree μ)
          (SphericalParisiFiniteMixtureGroundBridge.tensorCoefficient μ) * (1 / β) := hhigh
    _ ≤ (Real.log β + Real.log 3 +
        derivativeConstant (SphericalParisiFiniteMixtureGroundBridge.tensorDegree μ)
          (SphericalParisiFiniteMixtureGroundBridge.tensorCoefficient μ)) / β := by
      rw [add_div, add_div, mul_one_div]
      have H := div_le_div_of_nonneg_right hlog hb.le
      rw [add_div] at H
      linarith
    _ ≤ _ := by
      apply div_le_div_of_nonneg_right _ hb.le
      unfold laplaceConstant
      nlinarith [mul_nonneg hD hβlog, mul_nonneg h3 hβlog]

private theorem normalized_log_error_tendsto_zero (C : ℝ) :
    Tendsto (fun β : ℝ => C * (Real.log β + 1) / β) atTop (𝓝 0) := by
  have hlog : Tendsto (fun β : ℝ => Real.log β / β) atTop (𝓝 0) := by
    simpa only [pow_one, one_mul, add_zero] using
      Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hone : Tendsto (fun β : ℝ => (1 : ℝ) / β) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop tendsto_id
  simpa only [← add_div, ← mul_div_assoc, add_zero, mul_zero] using
    (hlog.add hone).const_mul C

private theorem canonicalGroundEnergy_tendsto_of_pressure_comparison
    (hChen : Chen2013FiniteParisi) (μ : FiniteMixture) (E : ℝ)
    (hzero : Tendsto (fun β : ℝ => CSParisiMeasure.variationalValue μ β / β)
      atTop (𝓝 E)) :
    Tendsto (canonicalGroundEnergy μ) atTop (𝓝 E) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  have herr : ∀ᶠ β : ℝ in atTop,
      laplaceConstant μ * (Real.log β + 1) / β < ε / 3 :=
    (normalized_log_error_tendsto_zero (laplaceConstant μ)).eventually (gt_mem_nhds hthird)
  have hvar : ∀ᶠ β : ℝ in atTop,
      dist (CSParisiMeasure.variationalValue μ β / β) E < ε / 3 :=
    (Metric.tendsto_nhds.mp hzero) (ε / 3) hthird
  obtain ⟨β, hβ, herrβ, hvarβ⟩ :=
    ((eventually_ge_atTop (1 : ℝ)).and (herr.and hvar)).exists
  have hp : Tendsto (fun N : ℕ => quenchedPressure N μ β / β) atTop
      (𝓝 (CSParisiMeasure.variationalValue μ β / β)) :=
    (hChen μ β (zero_le_one.trans hβ)).div_const β
  filter_upwards [(Metric.tendsto_nhds.mp hp) (ε / 3) hthird,
    eventually_gt_atTop (0 : ℕ)] with N hpN hN
  calc
    dist (canonicalGroundEnergy μ N) E ≤
        dist (canonicalGroundEnergy μ N) (quenchedPressure N μ β / β) +
          dist (quenchedPressure N μ β / β) E := dist_triangle _ _ _
    _ ≤ dist (canonicalGroundEnergy μ N) (quenchedPressure N μ β / β) +
        (dist (quenchedPressure N μ β / β)
          (CSParisiMeasure.variationalValue μ β / β) +
        dist (CSParisiMeasure.variationalValue μ β / β) E) :=
      add_le_add le_rfl (dist_triangle _ _ _)
    _ < ε := by
      simp only [Real.dist_eq] at hpN hvarβ ⊢
      linarith [finite_maximum_pressure_error μ hN hβ]

private theorem variationalValue_dist_le_errors
    (hChen : Chen2013FiniteParisi) (μ : FiniteMixture)
    {β γ : ℝ} (hβ : 1 ≤ β) (hγ : 1 ≤ γ) :
    dist (CSParisiMeasure.variationalValue μ β / β)
      (CSParisiMeasure.variationalValue μ γ / γ) ≤
        laplaceConstant μ * (Real.log β + 1) / β +
          laplaceConstant μ * (Real.log γ + 1) / γ := by
  have hp := (hChen μ β (zero_le_one.trans hβ)).div_const β
  have hq := (hChen μ γ (zero_le_one.trans hγ)).div_const γ
  apply le_of_tendsto (hp.dist hq)
  filter_upwards [eventually_gt_atTop (0 : ℕ)] with N hN
  calc
    dist (quenchedPressure N μ β / β) (quenchedPressure N μ γ / γ) ≤
        dist (quenchedPressure N μ β / β) (canonicalGroundEnergy μ N) +
        dist (canonicalGroundEnergy μ N) (quenchedPressure N μ γ / γ) :=
      dist_triangle _ _ _
    _ ≤ _ := by
      apply add_le_add
      · simpa only [Real.dist_eq, abs_sub_comm] using finite_maximum_pressure_error μ hN hβ
      · simpa only [Real.dist_eq] using finite_maximum_pressure_error μ hN hγ

private theorem variationalValue_natural_temperatures_cauchy
    (hChen : Chen2013FiniteParisi) (μ : FiniteMixture) :
    CauchySeq (fun n : ℕ =>
      CSParisiMeasure.variationalValue μ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) := by
  have hτ : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have herr := (normalized_log_error_tendsto_zero (laplaceConstant μ)).comp hτ
  have hτone (n : ℕ) : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop.mp
    (herr.eventually (gt_mem_nhds (half_pos hε)))
  simp only [Function.comp_apply] at hN
  refine ⟨N, ?_⟩
  intro n hn m hm
  have hh := variationalValue_dist_le_errors hChen μ (hτone n) (hτone m)
  exact hh.trans_lt (by linarith [hN n hn, hN m hm])

/-- Chen's finite-temperature formula alone implies existence of a common
expected-ground-energy and zero-temperature variational limit. No ground
profile attainment or additional literature interface is used. -/
theorem exists_ground_and_zero_temperature_limits
    (hChen : Chen2013FiniteParisi) (μ : FiniteMixture) :
    ∃ E : ℝ, Tendsto (canonicalGroundEnergy μ) atTop (𝓝 E) ∧
      Tendsto (fun β : ℝ => CSParisiMeasure.variationalValue μ β / β)
        atTop (𝓝 E) := by
  obtain ⟨E, hE⟩ := cauchySeq_tendsto_of_complete
    (variationalValue_natural_temperatures_cauchy hChen μ)
  have hτ : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have herrReal := normalized_log_error_tendsto_zero (laplaceConstant μ)
  have herrNat := herrReal.comp hτ
  have hτone (n : ℕ) : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)
  have hzero : Tendsto
      (fun β : ℝ => CSParisiMeasure.variationalValue μ β / β) atTop (𝓝 E) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    have hthird : 0 < ε / 3 := by positivity
    obtain ⟨n, hnerr, hnE⟩ :=
      ((herrNat.eventually (gt_mem_nhds hthird)).and
        ((Metric.tendsto_nhds.mp hE) (ε / 3) hthird)).exists
    simp only [Function.comp_apply] at hnerr
    filter_upwards [eventually_ge_atTop (1 : ℝ),
      herrReal.eventually (gt_mem_nhds hthird)] with β hβ hβerr
    calc
      dist (CSParisiMeasure.variationalValue μ β / β) E ≤
          dist (CSParisiMeasure.variationalValue μ β / β)
            (CSParisiMeasure.variationalValue μ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) +
          dist (CSParisiMeasure.variationalValue μ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) E :=
        dist_triangle _ _ _
      _ ≤ (laplaceConstant μ * (Real.log β + 1) / β +
            laplaceConstant μ * (Real.log ((n + 1 : ℕ) : ℝ) + 1) / ((n + 1 : ℕ) : ℝ)) +
          dist (CSParisiMeasure.variationalValue μ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)) E :=
        add_le_add (variationalValue_dist_le_errors hChen μ hβ (hτone n)) le_rfl
      _ < ε := by linarith
  exact ⟨E, canonicalGroundEnergy_tendsto_of_pressure_comparison hChen μ E hzero, hzero⟩

/-- Normalized actual CS minima along the positive integer temperatures. -/
def normalizedCSValue (μ : FiniteMixture) (n : ℕ) : ℝ :=
  CSParisiMeasure.variationalValue μ ((n + 1 : ℕ) : ℝ) / ((n + 1 : ℕ) : ℝ)

/-- The unfinished recovery step of Chen–Sen, Section 2.2. It asks for
actual admissible probability laws approaching each full ground profile,
not for a one-step restriction or a ground-energy conclusion. -/
def GroundRecoverySequences : Prop :=
  ∀ (μ : FiniteMixture) (v : GroundProfile),
    ∃ ζ : ℕ → CrisantiSommers.Admissible,
      Tendsto (fun n => (ζ n).value ((n + 1 : ℕ) : ℝ) μ.xi / ((n + 1 : ℕ) : ℝ))
        atTop (𝓝 (groundFunctional μ v))

/-- The unfinished compactness/liminf step for the rescaled finite-
temperature minimizers (Chen–Sen, Lemmas 1–5). This asks only for a
subsequence and an admissible profile satisfying the liminf inequality.
It assumes neither minimality nor any physical ground-energy limit. -/
def GroundMinimizerLiminfCompactness : Prop :=
  ∀ μ : FiniteMixture, ∃ u : GroundProfile, ∃ φ : ℕ → ℕ,
    StrictMono φ ∧ ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in atTop, groundFunctional μ u ≤ normalizedCSValue μ (φ n) + ε

/-- Exact reduction of the repository's entire ground-state interface to
Chen's formula and the two remaining purely variational steps. -/
theorem chenSenFiniteGround_of_variational_steps
    (hChen : Chen2013FiniteParisi)
    (hRecovery : GroundRecoverySequences)
    (hCompactness : GroundMinimizerLiminfCompactness) :
    ChenSenFiniteGround := by
  intro μ
  obtain ⟨E, hGround, hCS⟩ := exists_ground_and_zero_temperature_limits hChen μ
  have hτ : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
  have hlim : Tendsto (normalizedCSValue μ) atTop (𝓝 E) := hCS.comp hτ
  obtain ⟨u, φ, hφ, hlo⟩ := hCompactness μ
  have hu : groundFunctional μ u ≤ E := by
    apply le_of_forall_pos_le_add
    intro ε hε
    exact ge_of_tendsto ((hlim.comp hφ.tendsto_atTop).add_const ε) (hlo ε hε)
  have hv (v : GroundProfile) : E ≤ groundFunctional μ v := by
    obtain ⟨ζ, hζ⟩ := hRecovery μ v
    apply le_of_tendsto_of_tendsto hlim hζ
    exact .of_forall fun n => div_le_div_of_nonneg_right
      (CSParisiMeasure.canonicalMinimizer_isMinimizer μ ((n + 1 : ℕ) : ℝ) (ζ n))
      (by positivity)
  have hQ : groundFunctional μ u = E := le_antisymm hu (hv u)
  refine ⟨u, fun v => hu.trans (hv v), ?_⟩
  rw [hQ]
  exact hGround

open SphericalTAPCertificate SourceLiteratureStrictTAPGap
open LiteratureSubagTAP LiteratureSubagReplicaExclusion LiteratureSubagProposition24
open SourceReductionConsumerAsymptotic SphericalOverlapExponential
open SphericalOrthogonalHaar
open SphericalAging.HardSphereDynamics
open scoped NNReal

/-- The literal condensed/initial endpoint with the ground-state interface
replaced by the two unfinished variational steps above. All other source
inputs and the full conclusion are preserved. -/
theorem finiteMixture_main_condensed_and_initial_literal_reduced
    (μ : FiniteMixture) {β x Q : ℝ}
    (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hRecovery : GroundRecoverySequences)
    (hCompactness : GroundMinimizerLiminfCompactness)
    (h5 : Theorem5 (literatureThermodynamicData hChen
      (chenSenFiniteGround_of_variational_steps hChen hRecovery hCompactness) μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β)
    (h24 : Proposition24 μ β Q) :
    ∃ γ : ℝ, 0 < γ ∧
      VaryingConvergesInProbability
        (fun n => disorderLaw (n+2) μ.maxDegree)
        (fun n => originalUniformIntervalDistance μ β
          (exponentialGridHorizon γ (n+2)))
        (fun _ _ => 1) ∧
      uniformSeparationInProbability μ β (fun N => exponentialGridHorizon γ N) ∧
      (∀ ε : ℝ, 0 < ε →
        Tendsto (uniformPrescribedFailure μ β
          (fun N => exponentialGridHorizon γ N) ε) atTop (𝓝 0)) ∧
      (∀ (Ω : ℕ → Type) [∀ N, MeasurableSpace (Ω N)]
          (P : ∀ N, Measure (Ω N)) [∀ N, IsProbabilityMeasure (P N)]
          (J : ∀ N, Ω N → Disorder N μ.maxDegree)
          (ν : ∀ N, Ω N → ProbabilityMeasure (Vector N)),
          (∀ N, HasLaw (J N) (disorderLaw N μ.maxDegree) (P N)) →
          (∀ N, AEMeasurable (ν N) (P N)) →
          (∀ N, IndepFun
            (fun ω => fun x : {x : Vector N // OnSphere x} =>
              field (mixtureCoefficients μ) (J N ω) x) (ν N) (P N)) →
          (∀ N, 1 ≤ N → ∀ᵐ ω ∂P N, ∀ᵐ y ∂(ν N ω).toMeasure, OnSphere y) →
          ∀ ε : ℝ, 0 < ε →
            Tendsto (fun N => (P N).real
              {ω | intervalDistance μ β (exponentialGridHorizon γ N)
                (J N ω) (ν N ω) < 1-ε}) atTop (𝓝 0)) := by
  exact SourceFiniteMixtureMainLiteral.finiteMixture_main_condensed_and_initial_literal
    μ h hChen (chenSenFiniteGround_of_variational_steps hChen hRecovery hCompactness)
      h5 h25 h24

universe u v

/-- The all-initial spherical endpoint, with its universe-polymorphic
conclusion unchanged, reduced to the same two variational steps. -/
theorem finiteMixture_all_initial_spherical_of_literature_reduced
    (μ : FiniteMixture) {β x Q : ℝ} (h : Certificate μ β x Q)
    (hChen : Chen2013FiniteParisi)
    (hRecovery : GroundRecoverySequences)
    (hCompactness : GroundMinimizerLiminfCompactness)
    (h5 : Theorem5 (literatureThermodynamicData hChen
      (chenSenFiniteGround_of_variational_steps hChen hRecovery hCompactness) μ h.beta_pos.le))
    (h25 : Remark25Contrapositive μ β) (h24 : Proposition24 μ β Q) :
    ∃ γ : ℝ, 0 < γ ∧ SourceMixedCountCapturePackage.SphericalInitialConclusions.{u,v} μ β γ := by
  exact SourceMixedCountCapturePackage.finiteMixture_all_initial_spherical_of_literature.{u,v}
    μ h hChen (chenSenFiniteGround_of_variational_steps hChen hRecovery hCompactness)
      h5 h25 h24

end SlowEquilibration.SourceLiteratureGroundStateProof
