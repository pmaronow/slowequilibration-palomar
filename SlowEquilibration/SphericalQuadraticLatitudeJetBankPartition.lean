-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetPairMoment
public import SlowEquilibration.SphericalQuadraticLatitudeJetPairPalmLaw
public import SlowEquilibration.SphericalTAPQuadraticBankPhysicalOverlap
public import SlowEquilibration.SphericalTruncatedSecondMoment

@[expose] public section

/-! The literal angular partition of the second Taylor bank on the physical
transverse sphere. Exact two-point Gaussian moments are available under the
original and every canonical mixed Palm tensor law. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory Filter SphericalModel
open SphericalTAPCriticalAnalyticNeighborhood
open ConditionedDeterminantMoments
open scoped Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

def quadraticBankPoint {d : ℕ} (μ : FiniteMixture) (a β : ℝ)
    (u : Vector (d+2)) (J : Disorder (d+2) μ.maxDegree)
    (y : Vector (d+1)) : ℝ :=
  Real.exp (β * quadraticLatitudeJet μ a u
    (quadraticBankDirection (d+1) u y) J)

def quadraticBankPartition {d : ℕ} (μ : FiniteMixture) (a β : ℝ)
    (u : Vector (d+2)) (J : Disorder (d+2) μ.maxDegree) : ℝ :=
  ∫ y : Vector (d+1), quadraticBankPoint μ a β u J y ∂sphereLaw (d+1)

theorem quadraticBankPoint_continuous_direction {d : ℕ}
    (μ : FiniteMixture) (a β : ℝ) (u : Vector (d+2))
    (J : Disorder (d+2) μ.maxDegree) :
    Continuous (quadraticBankPoint μ a β u J) := by
  let A := iteratedFDeriv ℝ 2 (field (mixtureCoefficients μ) J) (a • u)
  have hdir : Continuous (quadraticBankDirection (d+1) u) := by
    unfold quadraticBankDirection
    exact (continuous_const : Continuous (fun _ : Vector (d+1) =>
      Real.sqrt (((d+1+1:ℕ):ℝ)/((d+1:ℕ):ℝ)))).smul
        (latitudeFrameAt u).continuous
  have harg : Continuous (fun y : Vector (d+1) =>
      ![quadraticBankDirection (d+1) u y,
        quadraticBankDirection (d+1) u y]) := by
    apply continuous_pi
    intro i
    fin_cases i <;> simpa using hdir
  have hjet : Continuous (fun y : Vector (d+1) => A
      ![quadraticBankDirection (d+1) u y,
        quadraticBankDirection (d+1) u y]) := A.cont.comp harg
  change Continuous (fun y : Vector (d+1) => Real.exp
    (β * (((1-a^2)/2) * A
      ![quadraticBankDirection (d+1) u y,
        quadraticBankDirection (d+1) u y])))
  exact Real.continuous_exp.comp
    (continuous_const.mul (continuous_const.mul hjet))

theorem quadraticBankPoint_measurable_disorder {d : ℕ}
    (μ : FiniteMixture) (a β : ℝ) (u : Vector (d+2))
    (y : Vector (d+1)) :
    Measurable (fun J : Disorder (d+2) μ.maxDegree =>
      quadraticBankPoint μ a β u J y) := by
  unfold quadraticBankPoint quadraticLatitudeJet
  have hj : Measurable (SphericalGaussianJet.jet (mixtureCoefficients μ) 2 (a • u)
      ![quadraticBankDirection (d+1) u y,
        quadraticBankDirection (d+1) u y]) := by
    convert (SphericalGaussianJet.jetCLM (mixtureCoefficients μ) 2 (a • u)
        ![quadraticBankDirection (d+1) u y,
          quadraticBankDirection (d+1) u y]).continuous.measurable using 1
    funext J
    simp only [SphericalGaussianJet.jetCLM_apply]
  exact Real.measurable_exp.comp
    (measurable_const.mul (measurable_const.mul
      hj))

theorem quadraticBankPoint_joint_measurable {d : ℕ}
    (μ : FiniteMixture) (a β : ℝ) (u : Vector (d+2)) :
    Measurable (fun z : Disorder (d+2) μ.maxDegree × Vector (d+1) =>
      quadraticBankPoint μ a β u z.1 z.2) := by
  have h : Measurable (fun z : Vector (d+1) × Disorder (d+2) μ.maxDegree =>
      quadraticBankPoint μ a β u z.2 z.1) :=
    measurable_uncurry_of_continuous_of_measurable
      (ι := Vector (d+1)) (α := Disorder (d+2) μ.maxDegree) (β := ℝ)
      (u := fun y J => quadraticBankPoint μ a β u J y)
      (fun J => quadraticBankPoint_continuous_direction μ a β u J)
      (fun y => quadraticBankPoint_measurable_disorder μ a β u y)
  have hs : Measurable (fun z : Disorder (d+2) μ.maxDegree × Vector (d+1) =>
      (z.2,z.1)) := measurable_snd.prodMk measurable_fst
  simpa only [Function.comp_def,Prod.fst,Prod.snd] using h.comp hs

theorem quadraticBankPoint_integrable_direction {d : ℕ}
    (μ : FiniteMixture) (a β : ℝ) (u : Vector (d+2))
    (J : Disorder (d+2) μ.maxDegree) :
    Integrable (quadraticBankPoint μ a β u J) (sphereLaw (d+1)) := by
  exact SphericalForm.integrable_sphereSupported_continuous (sphereLaw (d+1))
    (sphereLaw_support (by omega))
    (quadraticBankPoint_continuous_direction μ a β u J)

theorem quadraticBankPoint_physicalMixedPalm_integrable
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (mark : EuclideanSpace ℝ (Fin 2)) (y : Vector (d+1)) :
    Integrable (fun J : Disorder (d+2) μ.maxDegree =>
      quadraticBankPoint μ a β u J y) (mixedLaw μ Q u hu mark) := by
  let ω := quadraticBankDirection (d+1) u y
  have hi := quadraticLatitudeJetPair_physicalMixedPalm_exp_integrable
    μ hμ Q a (β/2) u hu ω ω
    (quadraticBankDirection_tangent u hu y)
    (quadraticBankDirection_tangent u hu y) mark
  convert hi using 1
  funext J
  unfold quadraticBankPoint quadraticLatitudeJetPair
  congr 1
  ring

theorem quadraticBankPoint_physicalMixedPalm_mean
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (mark : EuclideanSpace ℝ (Fin 2)) (y : Vector (d+1))
    (hy : ‖y‖^2=((d+1:ℕ):ℝ)) :
    (∫ J, quadraticBankPoint μ a β u J y ∂mixedLaw μ Q u hu mark) =
      Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2) := by
  have h := quadraticLatitudeJetPair_physicalMixedPalm_exp_integral_transverse
    μ hμ Q a (β/2) u hu y y hy hy mark
  have hpoint (J : Disorder (d+2) μ.maxDegree) :
      quadraticBankPoint μ a β u J y =
        Real.exp ((β/2)*quadraticLatitudeJetPair μ a u
          (quadraticBankDirection (d+1) u y)
          (quadraticBankDirection (d+1) u y) J) := by
    unfold quadraticBankPoint quadraticLatitudeJetPair
    congr 1
    ring
  simp_rw [hpoint]
  rw [h,overlap_self (by omega) y hy]
  congr 1
  ring

private theorem quadraticBankPoint_pair_le (x y : ℝ) :
    Real.exp x*Real.exp y ≤ Real.exp (2*x)+Real.exp (2*y) := by
  rw [show Real.exp (2*x)=(Real.exp x)^2 by
    rw [two_mul,Real.exp_add,pow_two],
    show Real.exp (2*y)=(Real.exp y)^2 by
    rw [two_mul,Real.exp_add,pow_two]]
  nlinarith [sq_nonneg (Real.exp x-Real.exp y),
    mul_nonneg (Real.exp_pos x).le (Real.exp_pos y).le]

private theorem quadraticBankPoint_pair_integrable_disorder
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (mark : EuclideanSpace ℝ (Fin 2)) (y z : Vector (d+1)) :
    Integrable (fun J : Disorder (d+2) μ.maxDegree =>
      quadraticBankPoint μ a β u J y * quadraticBankPoint μ a β u J z)
      (mixedLaw μ Q u hu mark) := by
  have hi := quadraticLatitudeJetPair_physicalMixedPalm_exp_integrable
    μ hμ Q a β u hu
      (quadraticBankDirection (d+1) u y)
      (quadraticBankDirection (d+1) u z)
      (quadraticBankDirection_tangent u hu y)
      (quadraticBankDirection_tangent u hu z) mark
  convert hi using 1
  funext J
  unfold quadraticBankPoint quadraticLatitudeJetPair
  rw [← Real.exp_add]
  congr 1
  ring

/-- Real Fubini is justified for the genuine Palm quadratic partition at
every mark. The integrability is uniform in angle because the elementary
two-replica exponential bound reduces it to one-point Gaussian moments. -/
theorem quadraticBankPoint_pair_prod_integrable
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (mark : EuclideanSpace ℝ (Fin 2)) :
    Integrable (fun w : Disorder (d+2) μ.maxDegree ×
      (Vector (d+1) × Vector (d+1)) =>
      quadraticBankPoint μ a β u w.1 w.2.1 *
        quadraticBankPoint μ a β u w.1 w.2.2)
      ((mixedLaw μ Q u hu mark).prod
        ((sphereLaw (d+1)).prod (sphereLaw (d+1)))) := by
  haveI : IsProbabilityMeasure (mixedLaw μ Q u hu mark) := by
    unfold mixedLaw
    infer_instance
  let m := Real.exp ((2*β)^2*((d+2:ℕ):ℝ)*
    sourceQuadraticLatitudeVariance μ a/2)
  have hm : Measurable (fun w : Disorder (d+2) μ.maxDegree ×
      (Vector (d+1) × Vector (d+1)) =>
      quadraticBankPoint μ a β u w.1 w.2.1 *
        quadraticBankPoint μ a β u w.1 w.2.2) := by
    have h := quadraticBankPoint_joint_measurable μ a β u
    have hp₁ : Measurable (fun w : Disorder (d+2) μ.maxDegree ×
        (Vector (d+1) × Vector (d+1)) => (w.1,w.2.1)) :=
      measurable_fst.prodMk measurable_snd.fst
    have hp₂ : Measurable (fun w : Disorder (d+2) μ.maxDegree ×
        (Vector (d+1) × Vector (d+1)) => (w.1,w.2.2)) :=
      measurable_fst.prodMk measurable_snd.snd
    have h₁ : Measurable (fun w : Disorder (d+2) μ.maxDegree ×
        (Vector (d+1) × Vector (d+1)) =>
        quadraticBankPoint μ a β u w.1 w.2.1) := by
      simpa only [Function.comp_def,Prod.fst,Prod.snd] using h.comp hp₁
    have h₂ : Measurable (fun w : Disorder (d+2) μ.maxDegree ×
        (Vector (d+1) × Vector (d+1)) =>
        quadraticBankPoint μ a β u w.1 w.2.2) := by
      simpa only [Function.comp_def,Prod.fst,Prod.snd] using h.comp hp₂
    exact h₁.mul h₂
  apply (integrable_prod_iff' hm.aestronglyMeasurable).mpr
  refine ⟨.of_forall (fun yz => quadraticBankPoint_pair_integrable_disorder
    μ hμ Q a β u hu mark yz.1 yz.2),?_⟩
  apply (integrable_const (2*m)).mono'
    hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  filter_upwards [sphereLaw_pair_support (by omega : 1≤d+1)] with yz hyz
  have hi₁ := quadraticBankPoint_physicalMixedPalm_integrable
    μ hμ Q a (2*β) u hu mark yz.1
  have hi₂ := quadraticBankPoint_physicalMixedPalm_integrable
    μ hμ Q a (2*β) u hu mark yz.2
  have hiPair := quadraticBankPoint_pair_integrable_disorder
    μ hμ Q a β u hu mark yz.1 yz.2
  have hpoint (J : Disorder (d+2) μ.maxDegree) :
      quadraticBankPoint μ a β u J yz.1 *
        quadraticBankPoint μ a β u J yz.2 ≤
        quadraticBankPoint μ a (2*β) u J yz.1+
        quadraticBankPoint μ a (2*β) u J yz.2 := by
    have hh := quadraticBankPoint_pair_le
      (β*quadraticLatitudeJet μ a u
        (quadraticBankDirection (d+1) u yz.1) J)
      (β*quadraticLatitudeJet μ a u
        (quadraticBankDirection (d+1) u yz.2) J)
    simpa only [quadraticBankPoint,show 2*(β*quadraticLatitudeJet μ a u
      (quadraticBankDirection (d+1) u yz.1) J) =
        (2*β)*quadraticLatitudeJet μ a u
          (quadraticBankDirection (d+1) u yz.1) J by ring,
      show 2*(β*quadraticLatitudeJet μ a u
      (quadraticBankDirection (d+1) u yz.2) J) =
        (2*β)*quadraticLatitudeJet μ a u
          (quadraticBankDirection (d+1) u yz.2) J by ring] using hh
  have hle : (∫ J, ‖quadraticBankPoint μ a β u J yz.1 *
      quadraticBankPoint μ a β u J yz.2‖ ∂mixedLaw μ Q u hu mark) ≤
      (∫ J, quadraticBankPoint μ a (2*β) u J yz.1+
        quadraticBankPoint μ a (2*β) u J yz.2
        ∂mixedLaw μ Q u hu mark) := by
    apply integral_mono hiPair.norm (hi₁.add hi₂)
    intro J
    change ‖quadraticBankPoint μ a β u J yz.1 *
      quadraticBankPoint μ a β u J yz.2‖ ≤ _
    have hzero : 0 ≤ quadraticBankPoint μ a β u J yz.1 *
        quadraticBankPoint μ a β u J yz.2 := by
      unfold quadraticBankPoint
      positivity
    rw [Real.norm_of_nonneg hzero]
    simpa only [Pi.add_apply] using hpoint J
  rw [integral_add hi₁ hi₂,
    quadraticBankPoint_physicalMixedPalm_mean μ hμ Q a (2*β) u hu mark yz.1 hyz.1,
    quadraticBankPoint_physicalMixedPalm_mean μ hμ Q a (2*β) u hu mark yz.2 hyz.2] at hle
  have hnonneg : 0 ≤ (∫ J,
      ‖quadraticBankPoint μ a β u J yz.1 *
        quadraticBankPoint μ a β u J yz.2‖
      ∂mixedLaw μ Q u hu mark) := integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnonneg]
  simpa [m,two_mul] using hle

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
