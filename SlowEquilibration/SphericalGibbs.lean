-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalModel
public import Mathlib.MeasureTheory.Integral.Prod
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.Analysis.Normed.Group.Bounded

@[expose] public section

namespace SlowEquilibration.SphericalModel

noncomputable section
open MeasureTheory Set Filter ProbabilityTheory
open scoped Topology

/-- The literal spherical partition function against the uniform sphere law. -/
def partition (N : ℕ) (β : ℝ) (H : Vector N → ℝ) : ℝ :=
  ∫ x, Real.exp (β*H x) ∂sphereLaw N

/-- The ordinary Gibbs density, normalized by the partition integral. -/
def gibbsDensity (N : ℕ) (β : ℝ) (H : Vector N → ℝ) (x : Vector N) : ℝ :=
  Real.exp (β*H x)/partition N β H

/-- The actual Gibbs probability measure, constructed by density with respect
to the uniform sphere probability law. -/
def gibbsLaw (N : ℕ) (β : ℝ) (H : Vector N → ℝ) : Measure (Vector N) :=
  (sphereLaw N).withDensity (fun x => ENNReal.ofReal (gibbsDensity N β H x))

theorem sphereLaw_mem_closedBall {N : ℕ} (hN : 1 ≤ N) :
    ∀ᵐ x ∂sphereLaw N, x ∈ Metric.closedBall (0:Vector N) (Real.sqrt N) := by
  filter_upwards [sphereLaw_support hN] with x hx
  rw [Metric.mem_closedBall,dist_zero_right]
  nlinarith [Real.sq_sqrt (Nat.cast_nonneg N),Real.sqrt_nonneg (N:ℝ),norm_nonneg x]

theorem integrable_sphere_of_continuous {N : ℕ} (hN : 1 ≤ N)
    {f : Vector N → ℝ} (hf : Continuous f) : Integrable f (sphereLaw N) := by
  have hi := hf.continuousOn.integrableOn_compact
    (isCompact_closedBall (0:Vector N) (Real.sqrt N)) (μ:=sphereLaw N)
  simpa only [IntegrableOn,
    Measure.restrict_eq_self_of_ae_mem (sphereLaw_mem_closedBall hN)] using hi

theorem partition_integrand_integrable {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) {H : Vector N → ℝ} (hH : Continuous H) :
    Integrable (fun x => Real.exp (β*H x)) (sphereLaw N) :=
  integrable_sphere_of_continuous hN (Real.continuous_exp.comp (continuous_const.mul hH))

theorem partition_pos {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) : 0 < partition N β H :=
  integral_exp_pos (partition_integrand_integrable hN β hH)

theorem gibbsDensity_pos {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (x : Vector N) :
    0 < gibbsDensity N β H x :=
  div_pos (Real.exp_pos _) (partition_pos hN β hH)

theorem gibbsDensity_continuous {N : ℕ} (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) : Continuous (gibbsDensity N β H) :=
  (Real.continuous_exp.comp (continuous_const.mul hH)).div_const _

theorem gibbsDensity_integrable {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) :
    Integrable (gibbsDensity N β H) (sphereLaw N) :=
  (partition_integrand_integrable hN β hH).div_const _

theorem integral_gibbsDensity {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) :
    (∫ x, gibbsDensity N β H x ∂sphereLaw N)=1 := by
  unfold gibbsDensity
  rw [integral_div]
  exact div_self (partition_pos hN β hH).ne'

theorem gibbsLaw_probability {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) : IsProbabilityMeasure (gibbsLaw N β H) := by
  constructor
  rw [gibbsLaw,withDensity_apply _ MeasurableSet.univ,Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (gibbsDensity_integrable hN β hH)
      (Eventually.of_forall (fun x => (gibbsDensity_pos hN β hH x).le)),
    integral_gibbsDensity hN β hH]
  norm_num

theorem gibbsLaw_absolutelyContinuous {N : ℕ} (β : ℝ) (H : Vector N → ℝ) :
    gibbsLaw N β H ≪ sphereLaw N := withDensity_absolutelyContinuous _ _

theorem gibbsLaw_support {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ) :
    ∀ᵐ x ∂gibbsLaw N β H, ‖x‖^2=(N:ℝ) :=
  (sphereLaw_support hN).filter_mono (gibbsLaw_absolutelyContinuous β H).ae_le

/-- Gibbs expectations are ordinary weighted sphere expectations. -/
theorem integral_gibbsLaw {N : ℕ} (hN : 1 ≤ N) (β : ℝ)
    {H : Vector N → ℝ} (hH : Continuous H) (f : Vector N → ℝ) :
    (∫ x, f x ∂gibbsLaw N β H) =
      ∫ x, gibbsDensity N β H x*f x ∂sphereLaw N := by
  rw [gibbsLaw,integral_withDensity_eq_integral_toReal_smul
    (gibbsDensity_continuous β hH).measurable.ennreal_ofReal]
  · congr 1
    funext x
    simp [ENNReal.toReal_ofReal (gibbsDensity_pos hN β hH x).le]
  · exact Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top)

/-- All partition and Gibbs constructions are now attached to the actual
mixed Gaussian field, with no assumed normalization or probability law. -/
def mixturePartition {N : ℕ} (μ : SlowEquilibration.FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) : ℝ := partition N β (fieldOfMixture μ J)

def mixtureGibbsLaw {N : ℕ} (μ : SlowEquilibration.FiniteMixture) (β : ℝ)
    (J : Disorder N μ.maxDegree) : Measure (Vector N) :=
  gibbsLaw N β (fieldOfMixture μ J)

theorem mixturePartition_pos {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibration.FiniteMixture) (β : ℝ) (J : Disorder N μ.maxDegree) :
    0 < mixturePartition μ β J :=
  partition_pos hN β (fieldOfMixture_contDiff μ J).continuous

theorem mixtureGibbsLaw_probability {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibration.FiniteMixture) (β : ℝ) (J : Disorder N μ.maxDegree) :
    IsProbabilityMeasure (mixtureGibbsLaw μ β J) :=
  gibbsLaw_probability hN β (fieldOfMixture_contDiff μ J).continuous

/-- Joint continuity is proved from the finite tensor polynomial, including
both disorder coefficients and spatial coordinates. -/
theorem field_jointContinuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (fun z : Disorder N P × Vector N => field c z.1 z.2) := by
  unfold field blockField SphericalAging.FiniteModel.Hamiltonian
    SphericalAging.FiniteModel.tensorMonomial
  fun_prop

theorem field_exp_integrable {N P : ℕ} (c : Degree P → ℝ)
    (x : Vector N) (β : ℝ) :
    Integrable (fun J : Disorder N P => Real.exp (β*field c J x)) (disorderLaw N P) := by
  have hG := field_hasGaussianLaw c x
  exact (show HasLaw (fun J : Disorder N P => field c J x)
    (gaussianReal (∫ J,field c J x ∂disorderLaw N P)
      (variance (fun J => field c J x) (disorderLaw N P)).toNNReal)
      (disorderLaw N P) from ⟨hG.aemeasurable,hG.map_eq_gaussianReal⟩).integrable_comp
    (integrable_exp_mul_gaussianReal β)

/-- The Gaussian exponential integrand is genuinely integrable on the
product of disorder and uniform sphere laws. -/
theorem field_exp_prod_integrable {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p, 0 ≤ c p) (β : ℝ) :
    Integrable (fun z : Disorder N P × Vector N => Real.exp (β*field c z.1 z.2))
      ((disorderLaw N P).prod (sphereLaw N)) := by
  have hcont : Continuous (fun z : Disorder N P × Vector N =>
      Real.exp (β*field c z.1 z.2)) :=
    Real.continuous_exp.comp (continuous_const.mul (field_jointContinuous (N:=N) c))
  apply (integrable_prod_iff' hcont.measurable.aestronglyMeasurable).mpr
  refine ⟨Eventually.of_forall (fun x => field_exp_integrable c x β),?_⟩
  apply (integrable_const (Real.exp ((N:ℝ)*β^2*covariancePolynomial c 1/2))).congr
  filter_upwards [sphereLaw_support hN] with x hx
  simp only [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact (field_exp_integral_on_sphere (lt_of_lt_of_le Nat.zero_lt_one hN) c hc x hx β).symm

/-- The exact annealed partition formula is a proved Fubini consequence
of the actual Gaussian moment and sphere support, not a pressure hypothesis. -/
theorem expected_partition {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (hc : ∀ p,0 ≤ c p) (β : ℝ) :
    (∫ J : Disorder N P,partition N β (field c J) ∂disorderLaw N P) =
      Real.exp ((N:ℝ)*β^2*covariancePolynomial c 1/2) := by
  unfold partition
  rw [integral_integral_swap (field_exp_prod_integrable hN c hc β)]
  have heq : (fun x : Vector N => ∫ J : Disorder N P,Real.exp (β*field c J x)
      ∂disorderLaw N P) =ᵐ[sphereLaw N]
      fun _ => Real.exp ((N:ℝ)*β^2*covariancePolynomial c 1/2) := by
    filter_upwards [sphereLaw_support hN] with x hx
    exact field_exp_integral_on_sphere (lt_of_lt_of_le Nat.zero_lt_one hN) c hc x hx β
  rw [integral_congr_ae heq]
  simp

theorem mixture_expected_partition {N : ℕ} (hN : 1 ≤ N)
    (μ : SlowEquilibration.FiniteMixture) (β : ℝ) :
    (∫ J : Disorder N μ.maxDegree,mixturePartition μ β J ∂disorderLaw N μ.maxDegree) =
      Real.exp ((N:ℝ)*β^2*μ.xi 1/2) := by
  unfold mixturePartition fieldOfMixture
  rw [expected_partition hN (mixtureCoefficients μ) (mixtureCoefficients_nonnegative μ),
    covariancePolynomial_mixture]

end
end SlowEquilibration.SphericalModel
