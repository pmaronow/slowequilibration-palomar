-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalQuadraticLatitudeJetBankPartition
public import SlowEquilibration.SphericalQuadraticLatitudeJetPurePairPalmLaw

@[expose] public section

/-! Fubini and pointwise exponential integrability for the genuine Y₂
bank under the literal proper-pure value/tangent posterior. -/

namespace SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
noncomputable section
open MeasureTheory ProbabilityTheory Filter SphericalModel SphericalGaussianJet
open SphericalTAPCriticalAnalyticNeighborhood
open ConditionedDeterminantMoments SphericalMarkedWindows
open scoped Topology RealInnerProductSpace
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.style.haveILetI false

theorem quadraticBankPoint_physicalPurePalm_integrable
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (b : ℝ) (y : Vector (d+1)) :
    Integrable (fun J : Disorder (d+2) μ.maxDegree =>
      quadraticBankPoint μ a β u J y) (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
  let ω := quadraticBankDirection (d+1) u y
  have hi := quadraticLatitudeJetPair_physicalPurePalm_exp_integrable
    μ hμ Q a (β/2) u hu ω ω
    (quadraticBankDirection_tangent u hu y)
    (quadraticBankDirection_tangent u hu y) b
  convert hi using 1
  funext J
  unfold quadraticBankPoint quadraticLatitudeJetPair
  congr 1
  ring

theorem quadraticBankPoint_physicalPurePalm_mean
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (b : ℝ) (y : Vector (d+1))
    (hy : ‖y‖^2=((d+1:ℕ):ℝ)) :
    (∫ J, quadraticBankPoint μ a β u J y ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) =
      Real.exp (β^2*((d+2:ℕ):ℝ)*sourceQuadraticLatitudeVariance μ a/2) := by
  have h := quadraticLatitudeJetPair_physicalPurePalm_exp_integral_transverse
    μ hμ Q a (β/2) u hu y y hy hy b
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
    (b : ℝ) (y z : Vector (d+1)) :
    Integrable (fun J : Disorder (d+2) μ.maxDegree =>
      quadraticBankPoint μ a β u J y * quadraticBankPoint μ a β u J z)
      (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
  have hi := quadraticLatitudeJetPair_physicalPurePalm_exp_integrable
    μ hμ Q a β u hu
      (quadraticBankDirection (d+1) u y)
      (quadraticBankDirection (d+1) u z)
      (quadraticBankDirection_tangent u hu y)
      (quadraticBankDirection_tangent u hu z) b
  convert hi using 1
  funext J
  unfold quadraticBankPoint quadraticLatitudeJetPair
  rw [← Real.exp_add]
  congr 1
  ring

/-- Real Fubini is justified for the genuine Palm quadratic partition at
every b. The integrability is uniform in angle because the elementary
two-replica exponential bound reduces it to one-point Gaussian moments. -/
theorem quadraticBankPoint_pair_prod_integrable_pure
    {d : ℕ} (μ : FiniteMixture) (hμ : 3 ≤ μ.minDegree)
    (Q a β : ℝ) (u : Vector (d+2))
    (hu : ‖u‖^2=((d+2:ℕ):ℝ))
    (b : ℝ) :
    Integrable (fun w : Disorder (d+2) μ.maxDegree ×
      (Vector (d+1) × Vector (d+1)) =>
      quadraticBankPoint μ a β u w.1 w.2.1 *
        quadraticBankPoint μ a β u w.1 w.2.2)
      ((valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b).prod
        ((sphereLaw (d+1)).prod (sphereLaw (d+1)))) := by
  haveI : IsProbabilityMeasure (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
    unfold valueConditionedLaw
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
    μ hμ Q a β u hu b yz.1 yz.2),?_⟩
  apply (integrable_const (2*m)).mono'
    hm.stronglyMeasurable.norm.integral_prod_left'.aestronglyMeasurable
  filter_upwards [sphereLaw_pair_support (by omega : 1≤d+1)] with yz hyz
  have hi₁ := quadraticBankPoint_physicalPurePalm_integrable
    μ hμ Q a (2*β) u hu b yz.1
  have hi₂ := quadraticBankPoint_physicalPurePalm_integrable
    μ hμ Q a (2*β) u hu b yz.2
  have hiPair := quadraticBankPoint_pair_integrable_disorder
    μ hμ Q a β u hu b yz.1 yz.2
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
      quadraticBankPoint μ a β u J yz.2‖ ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) ≤
      (∫ J, quadraticBankPoint μ a (2*β) u J yz.1+
        quadraticBankPoint μ a (2*β) u J yz.2
        ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := by
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
    quadraticBankPoint_physicalPurePalm_mean μ hμ Q a (2*β) u hu b yz.1 hyz.1,
    quadraticBankPoint_physicalPurePalm_mean μ hμ Q a (2*β) u hu b yz.2 hyz.2] at hle
  have hnonneg : 0 ≤ (∫ J,
      ‖quadraticBankPoint μ a β u J yz.1 *
        quadraticBankPoint μ a β u J yz.2‖
      ∂valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu b) := integral_nonneg (fun _ => norm_nonneg _)
  rw [Real.norm_of_nonneg hnonneg]
  simpa [m,two_mul] using hle

end
end SlowEquilibration.SphericalQuadraticLatitudeJetCovariance
