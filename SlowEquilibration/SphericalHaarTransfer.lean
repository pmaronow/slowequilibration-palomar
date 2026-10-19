module
-- SPDX-License-Identifier: Apache-2.0

public import SlowEquilibration.SphericalHaarInitial
public import SlowEquilibration.SphericalDisorderKernelMeasurable
public import SlowEquilibration.KernelInitialLawMeasurable
import all Mathlib.Basic.Real.Basic

@[expose] public section

/-! # Field-independent initial-law transfer for the actual mixed diffusion

The ordinary Haar average, the true tensor disorder invariance and the
actual Langevin kernel covariance give the source expected-deficit bound.
All field/initial-law total variations are genuinely jointly measurable.
-/
namespace SlowEquilibration.SphericalOrthogonalHaar
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1800000
open Set MeasureTheory ProbabilityTheory Filter
open SphericalModel SphericalDynamics SphericalReversibility SphericalRotationCovariance
open KernelInitialLawMeasurable
open SphericalAging.HardSphereDynamics
open scoped Topology NNReal ENNReal
variable {N : ℕ}

attribute [local irreducible] mixedTransitionKernel

@[irreducible] def distance (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : ProbabilityMeasure (Vector N)) : ℝ :=
  totalVariation (mixedTransitionKernel μ J β t ∘ₘ ν.toMeasure) (mixtureGibbsLaw μ β J)

lemma conditional_disorderTransitionKernel (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : Disorder N μ.maxDegree) :
    conditionalKernel (disorderTransitionKernel μ β t) J=mixedTransitionKernel μ J β t := by
  apply Kernel.ext
  intro x
  exact disorderTransitionKernel_apply μ β t (J,x)

/-- Actual distance is jointly Borel in the field and arbitrary initial
probability, including singular laws. -/
theorem distance_joint_measurable (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0) :
    Measurable (fun p : Disorder N μ.maxDegree × ProbabilityMeasure (Vector N) =>
      distance μ β t p.1 p.2) := by
  have hm := initialLawOutput_totalVariation_measurable (disorderTransitionKernel μ β t)
    (disorderGibbsKernel hN (mixtureCoefficients μ) β)
  convert hm using 1
  funext p
  rw [initialLawOutput,conditional_disorderTransitionKernel,disorderGibbsKernel_apply]
  unfold distance
  rfl

lemma distance_field_measurable (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (ν : ProbabilityMeasure (Vector N)) : Measurable (fun J : Disorder N μ.maxDegree => distance μ β t J ν) := by
  have hm : Measurable (fun J : Disorder N μ.maxDegree => (J,ν)) :=
    measurable_id.prodMk measurable_const
  exact (distance_joint_measurable hN μ β t).comp hm

lemma distance_nonneg (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : ProbabilityMeasure (Vector N)) : 0 ≤ distance μ β t J ν := by
  let := mixtureGibbsLaw_probability hN μ β J
  unfold distance
  exact totalVariation_nonneg _ _

lemma distance_le_one (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : ProbabilityMeasure (Vector N)) : distance μ β t J ν ≤ 1 := by
  let := mixtureGibbsLaw_probability hN μ β J
  unfold distance
  exact totalVariation_le_one _ _

lemma distance_integrable (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (ν : ProbabilityMeasure (Vector N)) :
    Integrable (fun J : Disorder N μ.maxDegree => distance μ β t J ν) (disorderLaw N μ.maxDegree) := by
  apply Integrable.of_bound (distance_field_measurable hN μ β t ν).aestronglyMeasurable 1
  exact .of_forall fun J => by
    rw [Real.norm_eq_abs,abs_of_nonneg (distance_nonneg hN μ β t J ν)]
    exact distance_le_one hN μ β t J ν

def rotatedInitialProbability (ν : ProbabilityMeasure (Vector N)) (g : OrthogonalGroup N) :
    ProbabilityMeasure (Vector N) := ⟨rotatedInitialKernel ν.toMeasure g,inferInstance⟩

lemma rotatedInitialProbability_measurable (ν : ProbabilityMeasure (Vector N)) :
    Measurable (rotatedInitialProbability ν) := (rotatedInitialKernel ν.toMeasure).measurable.subtype_mk

lemma rotatedInitialProbability_measure (ν : ProbabilityMeasure (Vector N)) (g : OrthogonalGroup N) :
    (rotatedInitialProbability ν g).toMeasure=ν.toMeasure.map (Unitary.linearIsometryEquiv g) :=
  rotatedInitialKernel_apply ν.toMeasure g

/-- The actual disorder expectation of distance is invariant under
rotating a prescribed initial law. This uses the real law-preserving tensor
action and the derived physical-kernel covariance. -/
theorem meanDistance_rotation (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (ν : ProbabilityMeasure (Vector N)) (hν : ∀ᵐ x ∂ν.toMeasure, OnSphere x)
    (g : OrthogonalGroup N) :
    (∫ J, distance μ β t J (rotatedInitialProbability ν g) ∂disorderLaw N μ.maxDegree)=
      ∫ J, distance μ β t J ν ∂disorderLaw N μ.maxDegree := by
  let U := Unitary.linearIsometryEquiv g
  have hm := distance_field_measurable hN μ β t (rotatedInitialProbability ν g)
  have he := integral_map (μ := disorderLaw N μ.maxDegree)
    (rotatedDisorder_measurable (P := μ.maxDegree) U).aemeasurable hm.aestronglyMeasurable
  rw [(rotatedDisorder_hasLaw (P := μ.maxDegree) U).map_eq] at he
  calc
    _ = ∫ J, distance μ β t (rotatedDisorder U J) (rotatedInitialProbability ν g)
        ∂disorderLaw N μ.maxDegree := he
    _ = _ := by
      apply integral_congr_ae
      exact .of_forall fun J => by
        unfold distance
        rw [rotatedInitialProbability_measure]
        exact mixed_totalVariation_rotation hN μ J β U t ν.toMeasure hν

def uniformInitialProbability (N : ℕ) : ProbabilityMeasure (Vector N) :=
  ⟨sphereLaw N,inferInstance⟩

/-- Source red-haar expected-distance inequality for the literal mixed
Langevin kernel. No isotropy, covariance, convexity, Haar-average or
measurability hypothesis replaces its actual provider. -/
theorem meanDistance_uniform_le (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (ν : ProbabilityMeasure (Vector N)) (hν : ∀ᵐ x ∂ν.toMeasure, OnSphere x) :
    (∫ J, distance μ β t J (uniformInitialProbability N) ∂disorderLaw N μ.maxDegree) ≤
      ∫ J, distance μ β t J ν ∂disorderLaw N μ.maxDegree := by
  have hm : Measurable (fun p : Disorder N μ.maxDegree × OrthogonalGroup N =>
      distance μ β t p.1 (rotatedInitialProbability ν p.2)) := by
    have hg : Measurable (fun p : Disorder N μ.maxDegree × OrthogonalGroup N =>
        (p.1,rotatedInitialProbability ν p.2)) :=
      measurable_fst.prodMk ((rotatedInitialProbability_measurable ν).comp measurable_snd)
    exact (distance_joint_measurable hN μ β t).comp hg
  have hi : Integrable (fun p : Disorder N μ.maxDegree × OrthogonalGroup N =>
      distance μ β t p.1 (rotatedInitialProbability ν p.2))
      ((disorderLaw N μ.maxDegree).prod (haar N)) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact .of_forall fun p => by
      rw [Real.norm_eq_abs,abs_of_nonneg (distance_nonneg hN μ β t p.1 _)]
      exact distance_le_one hN μ β t p.1 _
  calc
    _ ≤ ∫ J, ∫ g : OrthogonalGroup N, distance μ β t J (rotatedInitialProbability ν g)
        ∂haar N ∂disorderLaw N μ.maxDegree := by
      apply integral_mono_ae (distance_integrable hN μ β t _) hi.integral_prod_left
      exact .of_forall fun J => by
        have he := uniform_initial_totalVariation_le_haar_average hN μ J β t ν.toMeasure hν
        unfold uniformInitialProbability distance
        simpa only [ProbabilityMeasure.coe_mk,rotatedInitialProbability_measure] using he
    _ = ∫ g : OrthogonalGroup N, ∫ J, distance μ β t J (rotatedInitialProbability ν g)
        ∂disorderLaw N μ.maxDegree ∂haar N := integral_integral_swap hi
    _ = _ := by
      simp_rw [meanDistance_rotation hN μ β t ν hν]
      simp

/-- The source expected deficit is largest for the literal uniform initial
law. All measures and all expectations here are the actual physical ones. -/
theorem meanDeficit_le_uniform (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (ν : ProbabilityMeasure (Vector N)) (hν : ∀ᵐ x ∂ν.toMeasure, OnSphere x) :
    (∫ J, 1-distance μ β t J ν ∂disorderLaw N μ.maxDegree) ≤
      ∫ J, 1-distance μ β t J (uniformInitialProbability N) ∂disorderLaw N μ.maxDegree := by
  rw [integral_sub (integrable_const _) (distance_integrable hN μ β t ν),
    integral_sub (integrable_const _) (distance_integrable hN μ β t (uniformInitialProbability N))]
  exact sub_le_sub_left (meanDistance_uniform_le hN μ β t ν hν) _

/-- Source red-haar-uniform, before taking the supremum over prescribed
initial laws. The same bound holds for every singular or nonsingular law
fixed before the field is drawn. -/
theorem prescribed_initial_failure_le (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (t : ℝ≥0)
    (ν : ProbabilityMeasure (Vector N)) (hν : ∀ᵐ x ∂ν.toMeasure, OnSphere x)
    {ε : ℝ} (hε : 0 < ε) :
    (disorderLaw N μ.maxDegree).real {J | distance μ β t J ν < 1-ε} ≤
      ε⁻¹*(∫ J, 1-distance μ β t J (uniformInitialProbability N) ∂disorderLaw N μ.maxDegree) := by
  have hi := (integrable_const (1:ℝ)).sub (distance_integrable hN μ β t ν)
  have hmarkov := mul_meas_ge_le_integral_of_nonneg (μ := disorderLaw N μ.maxDegree)
    (.of_forall fun J => sub_nonneg.mpr (distance_le_one hN μ β t J ν)) hi ε
  have hsub : {J : Disorder N μ.maxDegree | distance μ β t J ν < 1-ε} ⊆
      {J | ε ≤ 1-distance μ β t J ν} := by
    intro J hJ
    change distance μ β t J ν < 1-ε at hJ
    change ε ≤ 1-distance μ β t J ν
    linarith
  have hm := (measureReal_mono (μ := disorderLaw N μ.maxDegree) hsub).trans
    ((le_div_iff₀ hε).mpr (by nlinarith [hmarkov]))
  have he := meanDeficit_le_uniform hN μ β t ν hν
  calc
    _ ≤ (∫ J, 1-distance μ β t J ν ∂disorderLaw N μ.maxDegree)/ε := hm
    _ ≤ (∫ J, 1-distance μ β t J (uniformInitialProbability N) ∂disorderLaw N μ.maxDegree)/ε :=
      div_le_div_of_nonneg_right he hε.le
    _ = _ := by ring

def intervalDistance (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : ProbabilityMeasure (Vector N)) : ℝ :=
  sInf ((fun t : ℝ => distance μ β t.toNNReal J ν) '' Icc 0 (T:ℝ))

/-- Actual endpoint contraction, expressed on the manuscript's entire
real time interval for arbitrary prescribed initial laws. -/
lemma intervalDistance_eq_endpoint (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (J : Disorder N μ.maxDegree) (ν : ProbabilityMeasure (Vector N)) :
    intervalDistance μ β T J ν=distance μ β T J ν := by
  simpa only [intervalDistance,distance,Real.toNNReal_coe] using
    mixed_totalVariation_endpoint_infimum hN μ J β ν.toMeasure T.coe_nonneg

/-- The uniform source bound has its supremum outside disorder probability.
There is no simultaneous field event for all prescribed initial laws. -/
theorem uniform_prescribed_initial_failure_le (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    {ε : ℝ} (hε : 0 < ε) :
    sSup {r : ℝ | ∃ ν : ProbabilityMeasure (Vector N),
      (∀ᵐ x ∂ν.toMeasure, OnSphere x) ∧
      r=(disorderLaw N μ.maxDegree).real {J | intervalDistance μ β T J ν < 1-ε}} ≤
      ε⁻¹*(∫ J, 1-distance μ β T J (uniformInitialProbability N) ∂disorderLaw N μ.maxDegree) := by
  apply csSup_le
  · refine ⟨(disorderLaw N μ.maxDegree).real
      {J | intervalDistance μ β T J (uniformInitialProbability N)<1-ε},uniformInitialProbability N,?_,rfl⟩
    exact (sphereLaw_support hN).mono fun x hx => (onSphere_iff_norm_sq x).mpr hx
  · rintro r ⟨ν,hν,rfl⟩
    simp_rw [intervalDistance_eq_endpoint hN μ β T]
    exact prescribed_initial_failure_le hN μ β T ν hν hε

/-- An initial probability chosen independently of the actual tensor field
obeys the same bound in the ordinary product law. Every prescribed law may
be singular and no averaging-density or regularity condition is assumed. -/
theorem independent_random_initial_failure_le (hN : 1 ≤ N) (μ : FiniteMixture) (β : ℝ) (T : ℝ≥0)
    (η : Measure (ProbabilityMeasure (Vector N))) [IsProbabilityMeasure η]
    (hη : ∀ᵐ ν ∂η, ∀ᵐ x ∂ν.toMeasure, OnSphere x) {ε : ℝ} (hε : 0 < ε) :
    ((disorderLaw N μ.maxDegree).prod η).real
      {p | intervalDistance μ β T p.1 p.2 < 1-ε} ≤
      ε⁻¹*(∫ J, 1-distance μ β T J (uniformInitialProbability N) ∂disorderLaw N μ.maxDegree) := by
  simp_rw [intervalDistance_eq_endpoint hN μ β T]
  have hE : MeasurableSet {p : Disorder N μ.maxDegree × ProbabilityMeasure (Vector N) |
      distance μ β T p.1 p.2 < 1-ε} :=
    measurableSet_lt (distance_joint_measurable hN μ β T) measurable_const
  have hm : Measurable (fun ν : ProbabilityMeasure (Vector N) =>
      (disorderLaw N μ.maxDegree) {J | distance μ β T J ν < 1-ε}) :=
    measurable_measure_prodMk_right hE
  have hi : Integrable (fun ν : ProbabilityMeasure (Vector N) =>
      (disorderLaw N μ.maxDegree).real {J | distance μ β T J ν < 1-ε}) η := by
    apply Integrable.of_bound hm.ennreal_toReal.aestronglyMeasurable 1
    exact .of_forall fun ν => by
      change |(disorderLaw N μ.maxDegree).real {J | distance μ β T J ν < 1-ε}| ≤ 1
      rw [abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have he : ((disorderLaw N μ.maxDegree).prod η).real
      {p | distance μ β T p.1 p.2 < 1-ε} =
      ∫ ν, (disorderLaw N μ.maxDegree).real {J | distance μ β T J ν < 1-ε} ∂η := by
    rw [Measure.real,Measure.prod_apply_symm hE]
    exact (integral_toReal hm.aemeasurable (.of_forall fun ν =>
      measure_lt_top (disorderLaw N μ.maxDegree) {J | distance μ β T J ν < 1-ε})).symm
  rw [he]
  have hb := integral_mono_ae hi (integrable_const
    (ε⁻¹*(∫ J, 1-distance μ β T J (uniformInitialProbability N) ∂disorderLaw N μ.maxDegree))) (by
      filter_upwards [hη] with ν hν
      exact prescribed_initial_failure_le hN μ β T ν hν hε)
  simpa only [integral_const,probReal_univ,one_smul] using hb

end
end SlowEquilibration.SphericalOrthogonalHaar
