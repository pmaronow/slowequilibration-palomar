-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SphericalTAPPosteriorLatitudeRegularity
public import SlowEquilibration.SourcePhysicalPairSelectionRegularity
public import SphericalAging.GaussianLandscapeMoments
public import Mathlib.Analysis.Calculus.MeanValue
public import SlowEquilibration.SourceReductionClosedBandGraph
public import SlowEquilibration.SphericalGibbsKernel
public import SlowEquilibration.SphericalTAPCriticalLightBandMark
public import SlowEquilibration.ReplicaBandExpectedUpper
public import SlowEquilibration.SourcePureSection9SmallClosures
public import SlowEquilibration.SphericalTAPLatitudeBorelCoarea

/-! Literal regularity and Borel statements for the manuscript mixed-band
chapter. The conditional estimates use the actual ambient transverse sphere
and include the unconditional ball Lipschitz tail and mean. Closed energy
and radial sets are allowed without boundedness assumptions. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceMixedBandsLiteral.BallLipschitz
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric
open SphericalModel PairConditionalDeterminantMoments
open SphericalAging.GaussianLandscape SphericalAging.GaussianLandscapeMoments
open scoped BigOperators NNReal
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual ambient derivative-norm maximum on the closed physical ball.
The mean value private theorem identifies it as a valid ball Lipschitz constant. -/
def physicalBallLipschitzConstant {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) : ℝ :=
  sSup ((fun x => ‖fderiv ℝ (field c J) x‖) '' closedBall 0 (Real.sqrt (N : ℝ)))

attribute [local irreducible] physicalBallLipschitzConstant

private lemma field_fderiv_joint_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (fun z : Disorder N P × Vector N => fderiv ℝ (field c z.1) z.2) :=
  (source_param_fderiv_contDiff (fun J x => field c J x)
    (source_field_joint_contDiff c)).continuous

private lemma physicalBallLipschitzConstant_continuous {N P : ℕ} (c : Degree P → ℝ) :
    Continuous (physicalBallLipschitzConstant (N := N) c) := by
  unfold physicalBallLipschitzConstant
  exact (isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).continuous_sSup
    (field_fderiv_joint_continuous c).norm

private lemma field_fderiv_ball_image_bddAbove {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) :
    BddAbove ((fun x => ‖fderiv ℝ (field c J) x‖) ''
      closedBall 0 (Real.sqrt (N : ℝ))) := by
  have hc : Continuous (fun x : Vector N => ‖fderiv ℝ (field c J) x‖) :=
    ((field_contDiff c J).fderiv_right (m := ⊤) (by simp)).continuous.norm
  exact ((isCompact_closedBall (0 : Vector N) (Real.sqrt (N : ℝ))).image hc).bddAbove

private lemma field_fderiv_le_physicalBallLipschitzConstant {N P : ℕ}
    (c : Degree P → ℝ) (J : Disorder N P) (x : Vector N)
    (hx : x ∈ closedBall 0 (Real.sqrt (N : ℝ))) :
    ‖fderiv ℝ (field c J) x‖ ≤ physicalBallLipschitzConstant c J := by
  unfold physicalBallLipschitzConstant
  exact le_csSup (field_fderiv_ball_image_bddAbove c J) ⟨x,hx,rfl⟩

lemma physicalBallLipschitzConstant_nonneg {N P : ℕ}
    (c : Degree P → ℝ) (J : Disorder N P) :
    0 ≤ physicalBallLipschitzConstant c J := by
  exact (norm_nonneg _).trans (field_fderiv_le_physicalBallLipschitzConstant c J 0
    (by simpa only [mem_closedBall, dist_self] using Real.sqrt_nonneg (N : ℝ)))

/-- No random coefficient bound is assumed in the Lipschitz identification. -/
private theorem physicalBallLipschitzConstant_lipschitzOn {N P : ℕ}
    (c : Degree P → ℝ) (J : Disorder N P) :
    LipschitzOnWith ⟨physicalBallLipschitzConstant c J,
      physicalBallLipschitzConstant_nonneg c J⟩
      (field c J) (closedBall 0 (Real.sqrt (N : ℝ))) := by
  apply Convex.lipschitzOnWith_of_nnnorm_fderiv_le
    (fun x _ => (field_contDiff c J).differentiable (by simp) x) _
    (convex_closedBall (0 : Vector N) (Real.sqrt (N : ℝ)))
  intro x hx
  exact_mod_cast field_fderiv_le_physicalBallLipschitzConstant c J x hx

/-- A genuine integrable random tensor envelope for the physical Lipschitz constant. -/
def normalizedLipschitzEnvelope {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) : ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) * (p.val.val : ℝ) *
    landscapeNorm N p.val.val (J p)

private lemma normalizedLipschitzEnvelope_nonneg {N P : ℕ} (c : Degree P → ℝ)
    (J : Disorder N P) : 0 ≤ normalizedLipschitzEnvelope c J := by
  unfold normalizedLipschitzEnvelope
  apply Finset.sum_nonneg
  intro p hp
  exact mul_nonneg (by positivity) (landscapeNorm_nonnegative _ _ _)

private lemma physicalBallLipschitzConstant_le_envelope {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) (J : Disorder N P) :
    physicalBallLipschitzConstant c J ≤
      normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ) := by
  unfold physicalBallLipschitzConstant
  apply csSup_le
  · exact ⟨‖fderiv ℝ (field c J) 0‖,0,
      by simpa only [mem_closedBall,dist_self] using Real.sqrt_nonneg (N : ℝ),rfl⟩
  · rintro v ⟨x,hx,rfl⟩
    have hball : ‖x‖ ≤ Real.sqrt (N : ℝ) := by
      simpa only [mem_closedBall,dist_zero_right] using hx
    have hjet := field_iteratedFDeriv_ball_bound hN c J x hball 1
    have hs : 0 < Real.sqrt (N : ℝ) := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega))
    have hsq : Real.sqrt (N : ℝ)^2 = (N : ℝ) := Real.sq_sqrt (Nat.cast_nonneg N)
    simp only [pow_one,norm_iteratedFDeriv_one,Nat.descFactorial_one] at hjet
    apply (mul_le_mul_iff_right₀ hs).mp
    calc
      _ ≤ (N : ℝ)*normalizedLipschitzEnvelope c J := hjet
      _ = Real.sqrt (N : ℝ) *
          (normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ)) := by
        calc
          _ = normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ)^2 := by rw [hsq]; ring
          _ = _ := by ring

private lemma physicalBallLipschitzConstant_regular_bound {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) (J : Disorder N P)
    (hJ : J ∈ regularDisorder) :
    physicalBallLipschitzConstant c J ≤ derivativeConstant c * Real.sqrt (N : ℝ) := by
  unfold physicalBallLipschitzConstant
  apply csSup_le
  · exact ⟨‖fderiv ℝ (field c J) 0‖,0,
      by simpa only [mem_closedBall,dist_self] using Real.sqrt_nonneg (N : ℝ),rfl⟩
  · rintro v ⟨x,hx,rfl⟩
    have hball : ‖x‖ ≤ Real.sqrt (N : ℝ) := by
      simpa only [mem_closedBall,dist_zero_right] using hx
    have hgrad := (field_regularDisorder_ball_bounds hN c J hJ x hball).2.1
    simpa only [gradient,LinearIsometryEquiv.norm_map] using hgrad

private lemma degree_landscapeNorm_integrable_and_mean {N P : ℕ}
    (hN : 1 ≤ N) (p : Degree P) :
    Integrable (fun J : Disorder N P => landscapeNorm N p.val.val (J p))
      (disorderLaw N P) ∧
    (∫ J : Disorder N P, landscapeNorm N p.val.val (J p) ∂disorderLaw N P) ≤
      momentCeiling p.val.val 1 := by
  have hb := uniform_real_power_moment hN (show 0 < p.val.val by omega)
    (k := 1) (by norm_num)
  simp only [Real.rpow_one] at hb
  refine ⟨(degree_block_hasLaw p).integrable_comp hb.1,?_⟩
  have heq := (degree_block_hasLaw (N := N) p).integral_comp hb.1.aestronglyMeasurable
  have heq' : (∫ J : Disorder N P, landscapeNorm N p.val.val (J p) ∂disorderLaw N P) =
      (∫ J : SphericalAging.FiniteModel.Disorder N p.val.val, landscapeNorm N p.val.val J
        ∂SphericalAging.FiniteModel.disorderLaw N p.val.val) := by
    simpa only [Function.comp_def] using heq
  rw [heq']
  exact hb.2

def lipschitzMeanConstant {P : ℕ} (c : Degree P → ℝ) : ℝ :=
  ∑ p : Degree P, Real.sqrt (c p) * (p.val.val : ℝ) * momentCeiling p.val.val 1

private lemma normalizedLipschitzEnvelope_integrable {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    Integrable (normalizedLipschitzEnvelope (N := N) c) (disorderLaw N P) := by
  unfold normalizedLipschitzEnvelope
  apply integrable_finsetSum
  intro p hp
  exact (degree_landscapeNorm_integrable_and_mean hN p).1.const_mul _

private lemma expected_normalizedLipschitzEnvelope_le {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    (∫ J : Disorder N P, normalizedLipschitzEnvelope c J ∂disorderLaw N P) ≤
      lipschitzMeanConstant c := by
  unfold normalizedLipschitzEnvelope lipschitzMeanConstant
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul]
    apply Finset.sum_le_sum
    intro p hp
    exact mul_le_mul_of_nonneg_left (degree_landscapeNorm_integrable_and_mean hN p).2
      (by positivity)
  · intro p hp
    exact (degree_landscapeNorm_integrable_and_mean hN p).1.const_mul _

private lemma physicalBallLipschitzConstant_integrable {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    Integrable (physicalBallLipschitzConstant (N := N) c) (disorderLaw N P) := by
  apply ((normalizedLipschitzEnvelope_integrable hN c).mul_const
    (Real.sqrt (N : ℝ))).mono_nonneg
    (physicalBallLipschitzConstant_continuous c).aestronglyMeasurable
    (ae_of_all _ (physicalBallLipschitzConstant_nonneg c))
    (ae_of_all _ (physicalBallLipschitzConstant_le_envelope hN c))

/-- The actual ball derivative supremum has dimension-free expected scale. -/
private theorem expected_physicalBallLipschitzConstant_le {N P : ℕ}
    (hN : 1 ≤ N) (c : Degree P → ℝ) :
    (∫ J : Disorder N P, physicalBallLipschitzConstant c J ∂disorderLaw N P) ≤
      lipschitzMeanConstant c * Real.sqrt (N : ℝ) := by
  calc
    _ ≤ ∫ J : Disorder N P, normalizedLipschitzEnvelope c J * Real.sqrt (N : ℝ)
        ∂disorderLaw N P := integral_mono (physicalBallLipschitzConstant_integrable hN c)
      ((normalizedLipschitzEnvelope_integrable hN c).mul_const _)
      (physicalBallLipschitzConstant_le_envelope hN c)
    _ = (∫ J : Disorder N P, normalizedLipschitzEnvelope c J ∂disorderLaw N P) *
        Real.sqrt (N : ℝ) := integral_mul_const _ _
    _ ≤ _ := mul_le_mul_of_nonneg_right (expected_normalizedLipschitzEnvelope_le hN c)
      (Real.sqrt_nonneg _)

/-- The original Gaussian failure event is Borel and exponentially small. -/
private theorem physicalBallLipschitzConstant_tail {N P : ℕ}
    (hN : 2 ≤ N) (c : Degree P → ℝ) :
    MeasurableSet {J : Disorder N P |
      derivativeConstant c * Real.sqrt (N : ℝ) < physicalBallLipschitzConstant c J} ∧
    (disorderLaw N P).real {J : Disorder N P |
      derivativeConstant c * Real.sqrt (N : ℝ) < physicalBallLipschitzConstant c J} ≤
      Real.exp (-(N : ℝ)) := by
  refine ⟨measurableSet_lt measurable_const
    (physicalBallLipschitzConstant_continuous c).measurable,?_⟩
  refine (measureReal_mono (μ := disorderLaw N P) (h₂ := measure_ne_top _ _) ?_).trans
    (regularDisorder_failure_probability hN)
  intro J hJ hreg
  exact (not_lt_of_ge (physicalBallLipschitzConstant_regular_bound (by omega) c J hreg)) hJ

/-- Both unconditional assertions in the Moreover clause of Lemma 12.3,
with a common positive constant fixed before every dimension. -/
private theorem source_unconditional_ball_lipschitz (μ : FiniteMixture) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      let Lip := physicalBallLipschitzConstant (N := N) (mixtureCoefficients μ)
      (∀ J, LipschitzOnWith ⟨Lip J,physicalBallLipschitzConstant_nonneg _ J⟩
        (field (mixtureCoefficients μ) J) (closedBall 0 (Real.sqrt (N : ℝ)))) ∧
      MeasurableSet {J | C * Real.sqrt (N : ℝ) < Lip J} ∧
      (disorderLaw N μ.maxDegree).real {J | C * Real.sqrt (N : ℝ) < Lip J} ≤
        C * Real.exp (-(N : ℝ)) ∧
      Integrable Lip (disorderLaw N μ.maxDegree) ∧
      (∫ J, Lip J ∂disorderLaw N μ.maxDegree) ≤ C * Real.sqrt (N : ℝ) := by
  let c := mixtureCoefficients μ
  let C := 1+derivativeConstant c+|lipschitzMeanConstant c|
  have hC1 : 1 ≤ C := by dsimp [C]; linarith [(derivativeConstant_pos c).le,abs_nonneg (lipschitzMeanConstant c)]
  have hCd : derivativeConstant c ≤ C := by dsimp [C]; linarith [abs_nonneg (lipschitzMeanConstant c)]
  have hCm : lipschitzMeanConstant c ≤ C := by
    dsimp [C]
    linarith [le_abs_self (lipschitzMeanConstant c),(derivativeConstant_pos c).le]
  refine ⟨C,by linarith,?_⟩
  intro N hN
  dsimp only
  obtain ⟨_hB,htail⟩ := physicalBallLipschitzConstant_tail hN c
  refine ⟨physicalBallLipschitzConstant_lipschitzOn c,
    measurableSet_lt measurable_const (physicalBallLipschitzConstant_continuous c).measurable,
    ?_,physicalBallLipschitzConstant_integrable (by omega) c,?_⟩
  · calc
      _ ≤ (disorderLaw N μ.maxDegree).real {J |
          derivativeConstant c * Real.sqrt (N : ℝ) < physicalBallLipschitzConstant c J} :=
        measureReal_mono (h₂ := measure_ne_top _ _) (fun J hJ =>
          lt_of_le_of_lt (mul_le_mul_of_nonneg_right hCd (Real.sqrt_nonneg _)) hJ)
      _ ≤ Real.exp (-(N : ℝ)) := htail
      _ ≤ C * Real.exp (-(N : ℝ)) :=
        le_mul_of_one_le_left (Real.exp_nonneg _) hC1
  · exact (expected_physicalBallLipschitzConstant_le (by omega) c).trans
      (mul_le_mul_of_nonneg_right hCm (Real.sqrt_nonneg _))

end
end SlowEquilibration.SourceMixedBandsLiteral.BallLipschitz

namespace SlowEquilibration.SourceMixedBandsLiteral.AmbientLatitude
noncomputable section
open Set MeasureTheory
open SphericalModel SphericalMarkedWindows PairConditionalDeterminantMoments
open SphericalGaussianJet WholeFieldRegression
open SphericalTAPLatitudePathJets SphericalTAPPosteriorBallRegularity
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal latitude curve remains on the physical sphere. -/
private theorem physicalLatitudePoint_norm_sq {N : ℕ}
    (u ω : Vector N) (hu : ‖u‖^2 = (N : ℝ)) (hω : ‖ω‖^2 = (N : ℝ))
    (hort : inner ℝ ω u = 0) {a : ℝ} (ha : |a| ≤ 1) :
    ‖physicalLatitudePoint u ω a‖^2 = (N : ℝ) := by
  have hir : inner ℝ u ω = 0 := by rwa [real_inner_comm]
  have hbase : 0 ≤ 1-a^2 := by nlinarith [abs_le.mp ha]
  unfold physicalLatitudePoint
  rw [norm_add_sq_real]
  simp only [norm_smul,Real.norm_eq_abs,mul_pow,sq_abs,
    real_inner_smul_left,real_inner_smul_right,hir,mul_zero,add_zero,hu,hω]
  rw [transverseLatitudeRadius,Real.sq_sqrt hbase]
  ring

/-- A compact interior latitude strip has a dimension-free bound on the
first scalar derivative of its transverse radius. -/
private theorem transverseLatitudeRadius_first_uniform {r : ℝ} (hr1 : r < 1) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ a ∈ Icc (-r) r,
      |deriv transverseLatitudeRadius a| ≤ A := by
  have hsub : Icc (-r) r ⊆ Ioo (-1:ℝ) 1 := by
    intro a ha
    constructor <;> linarith [ha.1,ha.2,hr1]
  have hcontOpen : ContinuousOn (iteratedDeriv 1 transverseLatitudeRadius)
      (Ioo (-1:ℝ) 1) := by
    have h := transverseLatitudeRadius_contDiffOn.continuousOn_iteratedDerivWithin
      (m := 1) (by norm_num) isOpen_Ioo.uniqueDiffOn
    exact h.congr (fun a ha =>
      (iteratedDerivWithin_of_isOpen isOpen_Ioo ha).symm)
  simp only [iteratedDeriv_one] at hcontOpen
  have hcont : ContinuousOn (fun a => |deriv transverseLatitudeRadius a|)
      (Icc (-r) r) := (hcontOpen.mono hsub).abs
  obtain ⟨A,hA⟩ := isCompact_Icc.bddAbove_image hcont
  refine ⟨max A 0,le_max_right _ _,?_⟩
  intro a ha
  exact (hA ⟨a,ha,rfl⟩).trans (le_max_left _ _)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
private theorem physicalLatitudePoint_hasDerivAt {N : ℕ}
    (u ω : Vector N) {a : ℝ} (ha : a ∈ Ioo (-1:ℝ) 1) :
    HasDerivAt (physicalLatitudePoint u ω)
      (u+deriv transverseLatitudeRadius a • ω) a := by
  have hr := transverseLatitudeRadius_hasDerivAt ha
  have hlin : HasDerivAt (fun t : ℝ => t • u) u a := by
    simpa only [id_eq,one_smul] using (hasDerivAt_id a).smul_const u
  have hrad : HasDerivAt (fun t : ℝ => transverseLatitudeRadius t • ω)
      (deriv transverseLatitudeRadius a • ω) a := by
    rw [hr.deriv]
    exact hr.smul_const ω
  unfold physicalLatitudePoint
  exact hlin.fun_add hrad

/-- Uniform physical speed on an interior strip, for every actual ambient
center and transverse point. -/
private theorem physicalLatitudePoint_speed_bound {N : ℕ}
    (u ω : Vector N) (hu : ‖u‖^2 = (N : ℝ)) (hω : ‖ω‖^2 = (N : ℝ))
    {a r A : ℝ} (ha : a ∈ Icc (-r) r) (hr1 : r < 1)
    (hA : ∀ t ∈ Icc (-r) r, |deriv transverseLatitudeRadius t| ≤ A) :
    ‖deriv (physicalLatitudePoint u ω) a‖ ≤ (1+A)*Real.sqrt (N : ℝ) := by
  have haopen : a ∈ Ioo (-1:ℝ) 1 := by
    constructor <;> linarith [ha.1,ha.2,hr1]
  have hunorm : ‖u‖ = Real.sqrt (N : ℝ) :=
    SphericalAging.LandscapeDerivatives.sphere_norm u hu
  have hωnorm : ‖ω‖ = Real.sqrt (N : ℝ) :=
    SphericalAging.LandscapeDerivatives.sphere_norm ω hω
  rw [(physicalLatitudePoint_hasDerivAt u ω haopen).deriv]
  calc
    _ ≤ ‖u‖+‖deriv transverseLatitudeRadius a • ω‖ := norm_add_le _ _
    _ = Real.sqrt (N : ℝ)+|deriv transverseLatitudeRadius a| * Real.sqrt (N : ℝ) := by
      rw [norm_smul,Real.norm_eq_abs,hunorm,hωnorm]
    _ ≤ Real.sqrt (N : ℝ)+A*Real.sqrt (N : ℝ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right (hA a ha) (Real.sqrt_nonneg _))
    _ = _ := by ring

/-- On the actual posterior tensor regularity event, the original field
has bounded second latitude derivative at every literal ambient point. -/
private theorem field_posterior_ambient_latitude_uniform_bound
    {P : ℕ} (c : Degree P → ℝ) {K r : ℝ}
    (hK : 0 ≤ K) (_hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N →
      ∀ J : Disorder N P, J ∈ sourcePosteriorOrderedRegularity K →
      ∀ (u ω : Vector N), ‖u‖^2 = (N : ℝ) → ‖ω‖^2 = (N : ℝ) →
        inner ℝ ω u = 0 → ∀ a ∈ Icc (-r) r,
          |iteratedDeriv 2 (fun t => field c J (physicalLatitudePoint u ω t)) a| ≤
            C*(N : ℝ) := by
  obtain ⟨A,hA0,hA⟩ := transverseLatitudeRadius_first_uniform hr1
  obtain ⟨B,hB0,hB⟩ := transverseLatitudeRadius_second_uniform hr1
  let C := posteriorDerivativeConstant c K * ((1+A)^2+B)
  have hfactor : 0 < (1+A)^2+B := by
    have hsq : 0 < (1+A)^2 := sq_pos_of_pos (by linarith)
    linarith
  have hC : 0 < C := mul_pos (posteriorDerivativeConstant_pos c hK) hfactor
  refine ⟨C,hC,?_⟩
  intro N hN J hJ u ω hu hω hort a ha
  have haopen : a ∈ Ioo (-1:ℝ) 1 := by
    constructor <;> linarith [ha.1,ha.2,hr1]
  have hcurve := physicalLatitudePoint_contDiffAt u ω haopen
  have hball : ‖physicalLatitudePoint u ω a‖ ≤ Real.sqrt (N : ℝ) := by
    have hsq := physicalLatitudePoint_norm_sq u ω hu hω hort
      ((abs_le.mpr ha).trans hr1.le)
    exact (SphericalAging.LandscapeDerivatives.sphere_norm _ hsq).le
  have hspeed := physicalLatitudePoint_speed_bound u ω hu hω ha hr1 hA
  have hωball := (SphericalAging.LandscapeDerivatives.sphere_norm ω hω).le
  have hacc := physicalLatitudePoint_acceleration_bound u ω ha hr1 hωball hB
  exact field_posterior_curve_second_bound hN c J hK hJ
    (physicalLatitudePoint u ω) a hcurve hball hspeed hacc

/-- Literal source conditional bad-curvature event: the existential
transverse point ranges over the complete ambient sphere u-perp, with
radius sqrtN, rather than the image of an unproved chart. -/
def ambientLatitudeFailure {N P : ℕ} (c : Degree P → ℝ)
    (u : Vector N) (lo hi C : ℝ) : Set (Disorder N P) :=
  {J | ∃ ω : Vector N, ‖ω‖^2 = (N : ℝ) ∧ inner ℝ ω u = 0 ∧
    ∃ a ∈ Icc lo hi,
      C*(N : ℝ) < |iteratedDeriv 2
        (fun t => field c J (physicalLatitudePoint u ω t)) a|}

attribute [local irreducible] ambientLatitudeFailure

/-- For each fixed actual latitude point in the interior, the original
field's second latitude derivative is continuous in its original tensor
coefficients. This derives both ambient jets from the proved joint
polynomial smoothness; it assumes no stochastic continuity result. -/
private theorem physicalLatitudeField_second_disorder_continuous {N P : ℕ}
    (c : Degree P → ℝ) (u ω : Vector N) {a : ℝ}
    (ha : a ∈ Ioo (-1:ℝ) 1) :
    Continuous (fun J : Disorder N P => iteratedDeriv 2
      (fun t => field c J (physicalLatitudePoint u ω t)) a) := by
  let y := physicalLatitudePoint u ω a
  let v := deriv (physicalLatitudePoint u ω) a
  let w := iteratedDeriv 2 (physicalLatitudePoint u ω) a
  have hf : ContDiff ℝ ⊤ (Function.uncurry (fun (J : Disorder N P) x => field c J x)) :=
    source_field_joint_contDiff c
  have hdf : ContDiff ℝ ⊤
      (Function.uncurry (fun (J : Disorder N P) x => fderiv ℝ (field c J) x)) :=
    source_param_fderiv_contDiff (fun J x => field c J x) hf
  have hfirst : Continuous (fun J : Disorder N P => fderiv ℝ (field c J) y) :=
    Continuous.fderiv hf continuous_const (by simp)
  have hsecond : Continuous (fun J : Disorder N P =>
      fderiv ℝ (fderiv ℝ (field c J)) y) :=
    Continuous.fderiv hdf continuous_const (by simp)
  have hc : Continuous (fun J : Disorder N P =>
      fderiv ℝ (fderiv ℝ (field c J)) y v v + fderiv ℝ (field c J) y w) :=
    ((hsecond.clm_apply continuous_const).clm_apply continuous_const).add
      (hfirst.clm_apply continuous_const)
  have heq : (fun J : Disorder N P => iteratedDeriv 2
      (fun t => field c J (physicalLatitudePoint u ω t)) a) =
      (fun J : Disorder N P =>
        fderiv ℝ (fderiv ℝ (field c J)) y v v + fderiv ℝ (field c J) y w) := by
    funext J
    have hchain := iteratedDeriv_vcomp_two
      ((field_contDiff c J).of_le (by norm_num)).contDiffAt
      (physicalLatitudePoint_contDiffAt u ω ha)
    change iteratedDeriv 2
      (fun t => field c J (physicalLatitudePoint u ω t)) a = _ at hchain
    simpa only [iteratedFDeriv_two_apply,Fin.isValue] using hchain
  rw [heq]
  exact hc

/-- The literal strict bad-curvature event is open, hence Borel. It is an
arbitrary union of open coefficient events for fixed interior latitude and
transverse point; compactness is unnecessary for this measurability step. -/
private theorem ambientLatitudeFailure_isOpen {N P : ℕ}
    (c : Degree P → ℝ) (u : Vector N) (lo hi C : ℝ)
    (hI : Icc lo hi ⊆ Ioo (-1:ℝ) 1) :
    IsOpen (ambientLatitudeFailure c u lo hi C) := by
  have heq : ambientLatitudeFailure c u lo hi C =
      ⋃ ω : {ω : Vector N | ‖ω‖^2 = (N : ℝ) ∧ inner ℝ ω u = 0},
        ⋃ a : Icc lo hi,
          {J : Disorder N P | C*(N : ℝ) < |iteratedDeriv 2
            (fun t => field c J (physicalLatitudePoint u ω.1 t)) a.1|} := by
    ext J
    simp only [Set.mem_iUnion,Set.mem_ofPred_eq]
    unfold ambientLatitudeFailure
    constructor
    · rintro ⟨ω,hω,hort,a,ha,hbad⟩
      exact ⟨⟨ω,hω,hort⟩,⟨a,ha⟩,hbad⟩
    · rintro ⟨ω,a,hbad⟩
      exact ⟨ω.1,ω.2.1,ω.2.2,a.1,a.2,hbad⟩
  rw [heq]
  apply isOpen_iUnion
  intro ω
  apply isOpen_iUnion
  intro a
  exact isOpen_lt continuous_const
    (physicalLatitudeField_second_disorder_continuous c u ω.1 (hI a.2)).abs

private theorem ambientLatitudeFailure_measurable {N P : ℕ}
    (c : Degree P → ℝ) (u : Vector N) (lo hi C : ℝ)
    (hI : Icc lo hi ⊆ Ioo (-1:ℝ) 1) :
    MeasurableSet (ambientLatitudeFailure c u lo hi C) :=
  (ambientLatitudeFailure_isOpen c u lo hi C hI).measurableSet

/-- Actual mixed full-field critical conditioning controls every literal
ambient transverse point, with constants before all dimensions and marks. -/
private theorem source_mixed_ambient_latitude_failure
    (μ : FiniteMixture) {Q M r : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hM : 0 ≤ M)
    (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ (h k : ℝ), |h| ≤ M → |k| ≤ M →
        (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q)
          u hu (WithLp.toLp 2 ![h,k])).real
          (ambientLatitudeFailure (mixtureCoefficients μ) u (-r) r C) ≤
            (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2) := by
  obtain ⟨K,hK,htail⟩ := source_mixed_physical_posterior_orderedRegularity μ hQ hnp hM
  obtain ⟨C,hC,hbound⟩ := field_posterior_ambient_latitude_uniform_bound
    (mixtureCoefficients μ) hK.le hr0 hr1
  refine ⟨C,hC,?_⟩
  intro n hn u hu h k hh hk
  let : IsProbabilityMeasure (mixedConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu (WithLp.toLp 2 ![h,k])) := by
    unfold mixedConditionedLaw
    infer_instance
  have hsub : ambientLatitudeFailure (mixtureCoefficients μ) u (-r) r C ⊆
      (sourcePosteriorOrderedRegularity (N := n+1) (P := μ.maxDegree) K)ᶜ := by
    intro J hbad hgood
    unfold ambientLatitudeFailure at hbad
    obtain ⟨ω,hω,hort,a,ha,hstrict⟩ := hbad
    exact not_lt_of_ge (hbound (n+1) (by omega) J hgood u ω hu hω hort a ha) hstrict
  exact (measureReal_mono hsub).trans (htail n u hu h k hh hk)

/-- Proper pure compatible-mark conditioning uses value and zero full
tangent gradient; no radial observation is silently reintroduced. -/
private theorem source_value_ambient_latitude_failure
    (μ : FiniteMixture) {Q M r : ℝ} (hQ : 0 < Q)
    (hM : 0 ≤ M) (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (n : ℕ), 1 ≤ n →
      ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)),
      ∀ h : ℝ, |h| ≤ M →
        (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu h).real
          (ambientLatitudeFailure (mixtureCoefficients μ) u (-r) r C) ≤
            (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2) := by
  obtain ⟨K,hK,htail⟩ := source_value_physical_posterior_orderedRegularity μ hQ hM
  obtain ⟨C,hC,hbound⟩ := field_posterior_ambient_latitude_uniform_bound
    (mixtureCoefficients μ) hK.le hr0 hr1
  refine ⟨C,hC,?_⟩
  intro n hn u hu h hh
  let : IsProbabilityMeasure (valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu h) := by
    unfold valueConditionedLaw
    infer_instance
  have hsub : ambientLatitudeFailure (mixtureCoefficients μ) u (-r) r C ⊆
      (sourcePosteriorOrderedRegularity (N := n+1) (P := μ.maxDegree) K)ᶜ := by
    intro J hbad hgood
    unfold ambientLatitudeFailure at hbad
    obtain ⟨ω,hω,hort,a,ha,hstrict⟩ := hbad
    exact not_lt_of_ge (hbound (n+1) (by omega) J hgood u ω hu hω hort a ha) hstrict
  exact (measureReal_mono hsub).trans (htail n u hu h hh)

end
end SlowEquilibration.SourceMixedBandsLiteral.AmbientLatitude

namespace SlowEquilibration.SourceMixedBandsLiteral
open Set MeasureTheory
open SphericalModel SphericalMarkedWindows SphericalGaussianJet
open SphericalTAPLatitudePathJets AmbientLatitude
open BallLipschitz
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

private lemma compact_marks_bounded (K₀ : Set (ℝ × ℝ)) (hK : IsCompact K₀) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ z ∈ K₀, |z.1| ≤ M ∧ |z.2| ≤ M := by
  obtain ⟨R,hR⟩ := hK.isBounded.exists_norm_le
  refine ⟨max R 0,le_max_right _ _,?_⟩
  intro z hz
  have hnorm := (hR z hz).trans (le_max_left R 0)
  constructor
  · exact (show |z.1| ≤ ‖z‖ by simpa only [Real.norm_eq_abs] using norm_fst_le z).trans hnorm
  · exact (show |z.2| ≤ ‖z‖ by simpa only [Real.norm_eq_abs] using norm_snd_le z).trans hnorm

private lemma ambientLatitudeFailure_interval_constant_mono {N P : ℕ}
    (c : Degree P → ℝ) (u : Vector N) {lo hi lo' hi' C C' : ℝ}
    (hI : Icc lo hi ⊆ Icc lo' hi') (hC : C' ≤ C) :
    ambientLatitudeFailure c u lo hi C ⊆ ambientLatitudeFailure c u lo' hi' C' := by
  intro J hJ
  unfold ambientLatitudeFailure at hJ ⊢
  obtain ⟨ω,hω,hort,a,ha,hstrict⟩ := hJ
  exact ⟨ω,hω,hort,a,hI ha,lt_of_le_of_lt
    (mul_le_mul_of_nonneg_right hC (Nat.cast_nonneg N)) hstrict⟩

/-- The unconditional clause uses the actual ball derivative supremum,
which is a genuine Lipschitz constant for the original field. -/
def UnconditionalSourceLipschitz (μ : FiniteMixture) (C c : ℝ) : Prop :=
  ∀ N : ℕ, 2 ≤ N →
    let Lip := physicalBallLipschitzConstant (N := N) (mixtureCoefficients μ)
    (∀ J, LipschitzOnWith ⟨Lip J,physicalBallLipschitzConstant_nonneg _ J⟩
      (field (mixtureCoefficients μ) J) (Metric.closedBall 0 (Real.sqrt (N : ℝ)))) ∧
    MeasurableSet {J | C*Real.sqrt (N : ℝ) < Lip J} ∧
    (disorderLaw N μ.maxDegree).real {J | C*Real.sqrt (N : ℝ) < Lip J} ≤
      C*Real.exp (-c*(N : ℝ)) ∧
    Integrable Lip (disorderLaw N μ.maxDegree) ∧
    (∫ J, Lip J ∂disorderLaw N μ.maxDegree) ≤ C*Real.sqrt (N : ℝ)

/-- The proved unconditional bounds tolerate any larger common C and
any smaller positive exponential rate. -/
private theorem exists_unconditional_source_lipschitz_larger_constant (μ : FiniteMixture) :
    ∃ L : ℝ, 0 < L ∧ ∀ C : ℝ, L ≤ C →
      UnconditionalSourceLipschitz μ C (1/2) := by
  obtain ⟨L,hL,hall⟩ := source_unconditional_ball_lipschitz μ
  refine ⟨L,hL,?_⟩
  intro C hLC N hN
  obtain ⟨hcert,_hmeas,htail,hi,hmean⟩ := hall N hN
  refine ⟨hcert,measurableSet_lt measurable_const
    (physicalBallLipschitzConstant_continuous (mixtureCoefficients μ)).measurable,
    ?_,hi,?_⟩
  · have hsub : {J : Disorder N μ.maxDegree |
        C*Real.sqrt (N : ℝ) < physicalBallLipschitzConstant (mixtureCoefficients μ) J} ⊆
        {J : Disorder N μ.maxDegree |
        L*Real.sqrt (N : ℝ) < physicalBallLipschitzConstant (mixtureCoefficients μ) J} := by
      intro J hJ
      exact lt_of_le_of_lt (mul_le_mul_of_nonneg_right hLC (Real.sqrt_nonneg _)) hJ
    calc
      _ ≤ (disorderLaw N μ.maxDegree).real {J |
          L*Real.sqrt (N : ℝ) < physicalBallLipschitzConstant (mixtureCoefficients μ) J} :=
        measureReal_mono (h₂ := measure_ne_top _ _) hsub
      _ ≤ L*Real.exp (-(N : ℝ)) := htail
      _ ≤ C*Real.exp (-(1/2:ℝ)*(N : ℝ)) := by
        apply mul_le_mul hLC
        · apply Real.exp_le_exp.mpr
          have hNr : (0:ℝ) ≤ N := Nat.cast_nonneg N
          linarith
        · exact Real.exp_nonneg _
        · exact hL.le.trans hLC
  · exact hmean.trans (mul_le_mul_of_nonneg_right hLC (Real.sqrt_nonneg _))

/-- All printed Lemma 12.3 conclusions for a non-pure field. The event
ranges over the full literal ambient transverse sphere; its probability
is Borel, and one C fixed before N also bounds the original Lipschitz
expectation and upper tail. -/
theorem source_mixed_actual_regular
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree)
    (K₀ : Set (ℝ × ℝ)) (hK₀ : IsCompact K₀)
    {lo hi : ℝ} (hlo : -1 < lo) (hlohi : lo ≤ hi) (hhi : hi < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      (∀ (n : ℕ), 1 ≤ n →
        ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)), ∀ z ∈ K₀,
          MeasurableSet (ambientLatitudeFailure (mixtureCoefficients μ) u lo hi C) ∧
          (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q)
            u hu (WithLp.toLp 2 ![z.1,z.2])).real
            (ambientLatitudeFailure (mixtureCoefficients μ) u lo hi C) ≤
              C*Real.exp (-c*((n+1:ℕ):ℝ))) ∧
      UnconditionalSourceLipschitz μ C c := by
  obtain ⟨M,hM,hmarks⟩ := compact_marks_bounded K₀ hK₀
  obtain ⟨r,hr0,hr1,hI⟩ := compactLatitudeInterval_symmetric_strip hlo hlohi hhi
  obtain ⟨C₀,hC₀,hcurv⟩ := source_mixed_ambient_latitude_failure μ hQ hnp hM hr0 hr1
  obtain ⟨L,hL,hLip⟩ := exists_unconditional_source_lipschitz_larger_constant μ
  let C := C₀+L+(Fintype.card (Degree μ.maxDegree):ℝ)+1
  have hcard0 : (0:ℝ) ≤ Fintype.card (Degree μ.maxDegree) := by positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hC₀le : C₀ ≤ C := by dsimp [C]; linarith
  have hLle : L ≤ C := by dsimp [C]; linarith
  have hcardle : (Fintype.card (Degree μ.maxDegree):ℝ) ≤ C := by dsimp [C]; linarith
  have hIopen : Icc lo hi ⊆ Ioo (-1:ℝ) 1 := by
    intro a ha
    exact ⟨hlo.trans_le ha.1,ha.2.trans_lt hhi⟩
  refine ⟨C,1/2,hC,by norm_num,?_,hLip C hLle⟩
  intro n hn u hu z hz
  obtain ⟨hh,hk⟩ := hmarks z hz
  let : IsProbabilityMeasure (mixedConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu (WithLp.toLp 2 ![z.1,z.2])) := by
    unfold mixedConditionedLaw
    infer_instance
  refine ⟨ambientLatitudeFailure_measurable _ _ _ _ _ hIopen,?_⟩
  calc
    _ ≤ (mixedConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q)
        u hu (WithLp.toLp 2 ![z.1,z.2])).real
        (ambientLatitudeFailure (mixtureCoefficients μ) u (-r) r C₀) :=
      measureReal_mono (h₂ := measure_ne_top _ _)
        (ambientLatitudeFailure_interval_constant_mono _ u hI hC₀le)
    _ ≤ (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2) :=
      hcurv n hn u hu z.1 z.2 hh hk
    _ ≤ C*Real.exp (-(1/2:ℝ)*((n+1:ℕ):ℝ)) := by
      have heq : -((n+1:ℕ):ℝ)/2 = -(1/2:ℝ)*((n+1:ℕ):ℝ) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hcardle (Real.exp_nonneg _)

/-- The same complete conclusion under the proper pure value-only law.
For pure source use, K₀ is restricted to compatible (h,p*h) marks; the
stronger value-posterior theorem needs no assumption on its unused radial
coordinate. One C controls both the curvature event and the unconditional
Lipschitz tail/expectation for every N≥2. -/
theorem source_value_actual_regular
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q)
    (K₀ : Set (ℝ × ℝ)) (hK₀ : IsCompact K₀)
    {lo hi : ℝ} (hlo : -1 < lo) (hlohi : lo ≤ hi) (hhi : hi < 1) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
      (∀ (n : ℕ), 1 ≤ n →
        ∀ (u : Vector (n+1)) (hu : ‖u‖^2 = ((n+1:ℕ):ℝ)), ∀ z ∈ K₀,
          MeasurableSet (ambientLatitudeFailure (mixtureCoefficients μ) u lo hi C) ∧
          (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q) u hu z.1).real
            (ambientLatitudeFailure (mixtureCoefficients μ) u lo hi C) ≤
              C*Real.exp (-c*((n+1:ℕ):ℝ))) ∧
      UnconditionalSourceLipschitz μ C c := by
  obtain ⟨M,hM,hmarks⟩ := compact_marks_bounded K₀ hK₀
  obtain ⟨r,hr0,hr1,hI⟩ := compactLatitudeInterval_symmetric_strip hlo hlohi hhi
  obtain ⟨C₀,hC₀,hcurv⟩ := source_value_ambient_latitude_failure μ hQ hM hr0 hr1
  obtain ⟨L,hL,hLip⟩ := exists_unconditional_source_lipschitz_larger_constant μ
  let C := C₀+L+(Fintype.card (Degree μ.maxDegree):ℝ)+1
  have hcard0 : (0:ℝ) ≤ Fintype.card (Degree μ.maxDegree) := by positivity
  have hC : 0 < C := by dsimp [C]; linarith
  have hC₀le : C₀ ≤ C := by dsimp [C]; linarith
  have hLle : L ≤ C := by dsimp [C]; linarith
  have hcardle : (Fintype.card (Degree μ.maxDegree):ℝ) ≤ C := by dsimp [C]; linarith
  have hIopen : Icc lo hi ⊆ Ioo (-1:ℝ) 1 := by
    intro a ha
    exact ⟨hlo.trans_le ha.1,ha.2.trans_lt hhi⟩
  refine ⟨C,1/2,hC,by norm_num,?_,hLip C hLle⟩
  intro n hn u hu z hz
  obtain ⟨hh,_hk⟩ := hmarks z hz
  let : IsProbabilityMeasure (valueConditionedLaw
      (centerCoefficients (mixtureCoefficients μ) Q) u hu z.1) := by
    unfold valueConditionedLaw
    infer_instance
  refine ⟨ambientLatitudeFailure_measurable _ _ _ _ _ hIopen,?_⟩
  calc
    _ ≤ (valueConditionedLaw (centerCoefficients (mixtureCoefficients μ) Q)
        u hu z.1).real (ambientLatitudeFailure (mixtureCoefficients μ) u (-r) r C₀) :=
      measureReal_mono (h₂ := measure_ne_top _ _)
        (ambientLatitudeFailure_interval_constant_mono _ u hI hC₀le)
    _ ≤ (Fintype.card (Degree μ.maxDegree):ℝ)*Real.exp (-((n+1:ℕ):ℝ)/2) :=
      hcurv n hn u hu z.1 hh
    _ ≤ C*Real.exp (-(1/2:ℝ)*((n+1:ℕ):ℝ)) := by
      have heq : -((n+1:ℕ):ℝ)/2 = -(1/2:ℝ)*((n+1:ℕ):ℝ) := by ring
      rw [heq]
      exact mul_le_mul_of_nonneg_right hcardle (Real.exp_nonneg _)

open SourceReductionClosedBandGraph
open PairConditionalDeterminantMoments SphericalForm
open Filter TwoAtomStationarity
open SphericalTAPCriticalLightBandMark
open scoped Topology

/-- Critical centers with arbitrary closed energy and radial mark sets. -/
def closedCenterGraph {N : ℕ} (μ : FiniteMixture) (Q : ℝ) (I U : Set ℝ) :
    Set (Disorder N μ.maxDegree × Vector N) :=
  {z | ‖z.2‖^2=(N:ℝ) ∧
    surfaceGradient (field (centerCoefficients (mixtureCoefficients μ) Q) z.1) z.2=0 ∧
    field (centerCoefficients (mixtureCoefficients μ) Q) z.1 z.2 ∈ I ∧
    (actualScore (centerCoefficients (mixtureCoefficients μ) Q) z.1 z.2) 1 ∈ U}

private theorem closedCenterGraph_isClosed {N : ℕ} (μ : FiniteMixture) (Q : ℝ)
    {I U : Set ℝ} (hI : IsClosed I) (hU : IsClosed U) :
    IsClosed (closedCenterGraph (N := N) μ Q I U) := by
  let c := centerCoefficients (mixtureCoefficients μ) Q
  have hs : IsClosed {z : Disorder N μ.maxDegree × Vector N | ‖z.2‖^2=(N:ℝ)} :=
    isClosed_eq (continuous_snd.norm.pow 2) continuous_const
  have hg : IsClosed {z : Disorder N μ.maxDegree × Vector N |
      surfaceGradient (field c z.1) z.2=0} :=
    isClosed_eq (source_surfaceGradient_joint_contDiff c).continuous continuous_const
  have he := hI.preimage (field_jointContinuous (N := N) c)
  have hk := hU.preimage ((PiLp.continuous_apply 2 (fun _ : Fin 2 => ℝ) 1).comp
    (actualScore_jointContinuous (N := N) c))
  exact hs.inter (hg.inter (he.inter hk))

/-- The band-union graph, with no boundedness assumption on either mark set. -/
def closedBandUnionGraph {N : ℕ} (μ : FiniteMixture) (Q b : ℝ) (I U : Set ℝ) :
    Set (Disorder N μ.maxDegree × Vector N) :=
  SourceReductionCompactBandProjection.bandUnionGraph
    (closedCenterGraph μ Q I U) (physicalBandRelation Q b)

/-- The closed-graph clause of `lem:mb-borel`, for arbitrary closed sets. -/
theorem band_union_graph_isClosed {N : ℕ} (μ : FiniteMixture) (Q b : ℝ)
    {I U : Set ℝ} (hI : IsClosed I) (hU : IsClosed U) :
    IsClosed (closedBandUnionGraph (N := N) μ Q b I U) := by
  let S : Set (Vector N) := {u | ‖u‖^2=(N:ℝ)}
  let : CompactSpace S := isCompact_iff_compactSpace.mp (sourceSphere_compact N)
  let C : Set (Disorder N μ.maxDegree × S) :=
    {z | (z.1,z.2.1) ∈ closedCenterGraph μ Q I U}
  let B : Set (Vector N × S) := {z | (z.1,z.2.1) ∈ physicalBandRelation Q b}
  have hC : IsClosed C := (closedCenterGraph_isClosed μ Q hI hU).preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hB : IsClosed B := (physicalBandRelation_isClosed Q b).preimage
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))
  have hp := SourceReductionCompactBandProjection.bandUnionGraph_isClosed hC hB
  convert hp using 1
  ext z
  constructor
  · rintro ⟨u,hu,hbu⟩
    exact ⟨⟨u,hu.1⟩,hu,hbu⟩
  · rintro ⟨u,hu,hbu⟩
    exact ⟨u.1,hu,hbu⟩

/-- Gibbs mass outside the arbitrary-closed-mark band union. -/
def closedBandComplementMass {N : ℕ} (μ : FiniteMixture) (Q b β : ℝ)
    (I U : Set ℝ) (J : Disorder N μ.maxDegree) : ℝ :=
  (mixtureGibbsLaw μ β J).real {σ | (J,σ) ∉ closedBandUnionGraph μ Q b I U}

/-- The capture observable in `lem:mb-borel` is Borel for arbitrary
closed energy and radial sets. Infinite critical fibers are allowed. -/
theorem band_complement_mass_measurable {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) (Q b β : ℝ) {I U : Set ℝ}
    (hI : IsClosed I) (hU : IsClosed U) :
    Measurable (closedBandComplementMass (N := N) μ Q b β I U) := by
  have hm := (ProbabilityTheory.Kernel.measurable_kernel_prodMk_left
    (κ := disorderGibbsKernel hN (mixtureCoefficients μ) β)
    (band_union_graph_isClosed (N := N) μ Q b hI hU).measurableSet.compl).ennreal_toReal
  convert hm using 1
  funext J
  rw [disorderGibbsKernel_apply]
  rfl

/-- `lem:mb-subag-mean`: the literal expected replicated-band limsup,
for any finite mixture, without a positive-volume premise. The transverse
orthogonal configuration proving eventual positive volume is internal to
the imported source theorem. Its width is `δ=α/√Q` in manuscript notation. -/
theorem replicated_band_expected_limsup
    (μ : FiniteMixture) {β Q : ℝ} (hβ : 0 < β) (hQ : Q ∈ Ioo (0:ℝ) 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ δ ∈ Ioc (0:ℝ) (Real.sqrt Q/2),
      ∀ ρ : ℝ, 0 < ρ → ∀ k : ℕ, 1 ≤ k →
        ∀ m : (N : ℕ) → Vector N, (∀ N, ‖m N‖^2=(N:ℝ)*Q) →
          Filter.limsup (fun N =>
            (LiteratureSubagPhysicalDefinitions.expectedReplicatedBandPressure
              k μ β Q δ ρ (m N) : EReal)) atTop ≤
            ((Real.log (1-Q)/2+β^2*residualAtOne μ Q/2+C*Real.sqrt δ+
              C*Real.sqrt (1/(k:ℝ)+(ρ+Real.sqrt (8*δ))/(1-Q)) : ℝ) : EReal) :=
  SourcePureSection9SmallClosures.expectedReplicatedBandPressure_full_width_limsup μ hβ hQ

open LiteratureSubagPhysicalDefinitions ProbabilityTheory
open scoped BigOperators InnerProductSpace RealInnerProductSpace

private theorem replicatedBand_measurable {N k : ℕ} (Q δ ρ : ℝ) (m : Vector N) :
    MeasurableSet (ReplicatedBand k Q δ ρ m) := by
  simp only [ReplicatedBand,Set.ofPred_and,Set.ofPred_forall]
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun i => measurableSet_le
      (by unfold overlap; fun_prop) measurable_const
  · exact MeasurableSet.iInter fun i => MeasurableSet.iInter fun j =>
      MeasurableSet.iInter fun _ => measurableSet_lt
        (by unfold overlap; fun_prop) measurable_const

private theorem replicatedPressure_measurable {N : ℕ} (k : ℕ)
    (μ : FiniteMixture) (β Q δ ρ : ℝ) (m : Vector N) :
    Measurable (fun J : Disorder N μ.maxDegree => replicatedBandPressure k μ β Q δ ρ J m) := by
  have hf : Continuous (fun z : Disorder N μ.maxDegree × (Fin k → Vector N) =>
      Real.exp (β*∑ i : Fin k, (field (mixtureCoefficients μ) z.1 (z.2 i)-
        field (mixtureCoefficients μ) z.1 m))) := by
    apply Real.continuous_exp.comp
    apply continuous_const.mul
    apply continuous_finsetSum
    intro i _
    exact ((field_jointContinuous (mixtureCoefficients μ)).comp
      (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))).sub
        ((field_jointContinuous (mixtureCoefficients μ)).comp
          (continuous_fst.prodMk continuous_const))
  have hi := hf.stronglyMeasurable.integral_prod_right'
    (ν := (Measure.pi (fun _ : Fin k => sphereLaw N)).restrict (ReplicatedBand k Q δ ρ m))
  exact hi.measurable.log.div_const _

private theorem replicatedPartition_rotation {N : ℕ} (k : ℕ)
    (μ : FiniteMixture) (β Q δ ρ : ℝ)
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree) (m : Vector N) :
    replicatedBandPartition k μ β Q δ ρ (rotatedDisorder U J) (U m) =
      replicatedBandPartition k μ β Q δ ρ J m := by
  let ν := Measure.pi (fun _ : Fin k => sphereLaw N)
  let T : (Fin k → Vector N) → (Fin k → Vector N) := fun σ i => U (σ i)
  have hT : Measurable T := Measurable.of_eval (fun i =>
    U.continuous.measurable.comp (measurable_pi_apply i))
  have hmap : ν.map T=ν := by
    rw [Measure.pi_map_pi (fun _ : Fin k => U.continuous.measurable.aemeasurable)]
    simp only [sphereLaw_rotation_invariant]
    rfl
  let F := (ReplicatedBand k Q δ ρ (U m)).indicator (fun σ =>
    Real.exp (β*∑ i : Fin k, (field (mixtureCoefficients μ) (rotatedDisorder U J) (σ i)-
      field (mixtureCoefficients μ) (rotatedDisorder U J) (U m))))
  have hF : StronglyMeasurable F := by
    have hc : Continuous (fun σ : Fin k → Vector N =>
      Real.exp (β*∑ i : Fin k, (field (mixtureCoefficients μ) (rotatedDisorder U J) (σ i)-
        field (mixtureCoefficients μ) (rotatedDisorder U J) (U m)))) := by
      apply Real.continuous_exp.comp
      apply continuous_const.mul
      apply continuous_finsetSum
      intro i _
      exact (((field_contDiff (mixtureCoefficients μ) (rotatedDisorder U J)).continuous).comp
        (continuous_apply i)).sub continuous_const
    exact hc.stronglyMeasurable.indicator (replicatedBand_measurable Q δ ρ (U m))
  have hchange := integral_map (μ := ν) hT.aemeasurable hF.aestronglyMeasurable
  rw [hmap] at hchange
  unfold replicatedBandPartition
  rw [← integral_indicator (replicatedBand_measurable Q δ ρ (U m)),
    ← integral_indicator (replicatedBand_measurable Q δ ρ m)]
  change (∫ σ, F σ ∂ν) = _
  rw [hchange]
  apply integral_congr_ae
  exact ae_of_all _ (fun σ => by
    change F (T σ) = _
    have hmem : T σ ∈ ReplicatedBand k Q δ ρ (U m) ↔ σ ∈ ReplicatedBand k Q δ ρ m := by
      simp only [ReplicatedBand,mem_ofPred_eq,T,overlap,U.inner_map_map]
    by_cases hs : σ ∈ ReplicatedBand k Q δ ρ m
    · rw [show F (T σ) = _ from Set.indicator_of_mem (hmem.mpr hs) _,
        Set.indicator_of_mem hs]
      simp only [T,field_rotated]
    · rw [show F (T σ) = 0 from Set.indicator_of_notMem (fun hh => hs (hmem.mp hh)) _,
        Set.indicator_of_notMem hs])

/-- The center-independence clause of `lem:mb-subag-mean`, including
empty replicated bands. This follows from the actual tensor rotation law. -/
theorem replicated_band_expected_center_independent {N : ℕ} (k : ℕ)
    (μ : FiniteMixture) (β Q δ ρ : ℝ) (m₁ m₂ : Vector N)
    (hm : ‖m₁‖=‖m₂‖) :
    expectedReplicatedBandPressure k μ β Q δ ρ m₁ =
      expectedReplicatedBandPressure k μ β Q δ ρ m₂ := by
  let U := ((ℝ ∙ (m₁-m₂))ᗮ).reflection
  have hU : U m₁=m₂ := Submodule.reflection_sub hm
  have hrot := (rotatedDisorder_hasLaw (P := μ.maxDegree) U).integral_comp
    (replicatedPressure_measurable k μ β Q δ ρ m₂).aestronglyMeasurable
  have heq (J : Disorder N μ.maxDegree) :
      replicatedBandPressure k μ β Q δ ρ (rotatedDisorder U J) m₂ =
        replicatedBandPressure k μ β Q δ ρ J m₁ := by
    rw [← hU]
    unfold replicatedBandPressure
    rw [replicatedPartition_rotation]
  simpa only [Function.comp_apply,heq,expectedReplicatedBandPressure] using hrot

private theorem overlap_level_null {n : ℕ} (hn : 2 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ)) (t : ℝ) :
    sphereLaw (n+1) {σ | overlap σ u=t}=0 := by
  by_cases ht : t ∈ Icc (-1:ℝ) 1
  · have hc := SphericalTAPLatitudeBorelCoarea.partitionOn_borel_latitude_eq_lintegral
      hn 0 (H := fun _ => (0:ℝ)) continuous_const u hu {t}
      (measurableSet_singleton t) (singleton_subset_iff.mpr ht)
    have he : partitionOn 0 (fun _ : Vector (n+1) => (0:ℝ))
        (overlapRegion u {t}) = (sphereLaw (n+1)).real {σ | overlap σ u=t} := by
      simp [partitionOn,overlapRegion,Measure.real]
    rw [he] at hc
    simpa [Measure.real,ENNReal.ofReal_toReal (measure_ne_top _ _)] using hc
  · have ha : ∀ᵐ σ ∂sphereLaw (n+1), ¬overlap σ u=t := by
      filter_upwards [sphereLaw_support (by omega : 1 ≤ n+1)] with σ hσ heq
      exact ht (heq ▸ overlap_mem_Icc_of_norm_sq (by omega : 1 ≤ n+1) σ u hσ hu)
    simpa only [not_not] using (ae_iff.mp ha)

private theorem band_boundary_null {n : ℕ} (hn : 2 ≤ n)
    (u : Vector (n+1)) (hu : ‖u‖^2=((n+1:ℕ):ℝ)) (q b : ℝ) :
    sphereLaw (n+1) {σ | |overlap σ u-q|=b}=0 := by
  apply measure_mono_null (t := {σ | overlap σ u=q+b} ∪ {σ | overlap σ u=q-b})
  · intro σ hσ
    change |overlap σ u-q|=b at hσ
    by_cases hs : 0 ≤ overlap σ u-q
    · left
      change overlap σ u=q+b
      rw [abs_of_nonneg hs] at hσ
      linarith
    · right
      change overlap σ u=q-b
      rw [abs_of_neg (lt_of_not_ge hs)] at hσ
      linarith
  · exact measure_union_null (overlap_level_null hn u hu _) (overlap_level_null hn u hu _)

/-- Joint continuity of the literal moving-band partition in every
dimension `N ≥ 3`, including arbitrary widths. The proof uses the null
latitude boundary and local domination on the compact physical sphere. -/
theorem band_partition_continuous {n : ℕ} (hn : 2 ≤ n)
    (μ : FiniteMixture) (β Q b : ℝ) :
    Continuous (fun p : Disorder (n+1) μ.maxDegree ×
      {u : Vector (n+1) // ‖u‖^2=((n+1:ℕ):ℝ)} =>
      partitionOn β (field (mixtureCoefficients μ) p.1)
        {σ | |overlap σ p.2.1-Real.sqrt Q| ≤ b}) := by
  let S : Set (Vector (n+1)) := {u | ‖u‖^2=((n+1:ℕ):ℝ)}
  let B := fun p : Disorder (n+1) μ.maxDegree × S =>
    {σ : Vector (n+1) | |overlap σ p.2.1-Real.sqrt Q| ≤ b}
  have hB (p : Disorder (n+1) μ.maxDegree × S) : MeasurableSet (B p) := by
    apply measurableSet_le _ measurable_const
    unfold overlap
    fun_prop
  let F := fun (p : Disorder (n+1) μ.maxDegree × S) =>
    (B p).indicator (fun σ => Real.exp (β*field (mixtureCoefficients μ) p.1 σ))
  have hrepr (p : Disorder (n+1) μ.maxDegree × S) :
      partitionOn β (field (mixtureCoefficients μ) p.1) (B p) =
        ∫ σ, F p σ ∂sphereLaw (n+1) := by
    rw [partitionOn,← integral_indicator (hB p)]
  change Continuous (fun p : Disorder (n+1) μ.maxDegree × S =>
    partitionOn β (field (mixtureCoefficients μ) p.1) (B p))
  simp_rw [hrepr]
  apply continuous_iff_continuousAt.mpr
  intro p0
  have hK : IsCompact ((Metric.closedBall p0.1 1) ×ˢ S) :=
    (isCompact_closedBall _ _).prod (sourceSphere_compact (n+1))
  have hG : Continuous (fun z : Disorder (n+1) μ.maxDegree × Vector (n+1) =>
      Real.exp (β*field (mixtureCoefficients μ) z.1 z.2)) :=
    Real.continuous_exp.comp (continuous_const.mul (field_jointContinuous _))
  obtain ⟨M,hM⟩ := (hK.image hG).isBounded.exists_norm_le
  apply continuousAt_of_dominated (bound := fun _ => max M 0)
  · exact .of_forall (fun p =>
      ((Real.continuous_exp.comp (continuous_const.mul
        (field_contDiff (mixtureCoefficients μ) p.1).continuous)).stronglyMeasurable.indicator
          (hB p)).aestronglyMeasurable)
  · have hnear : ∀ᶠ p : Disorder (n+1) μ.maxDegree × S in 𝓝 p0,
        p.1 ∈ Metric.closedBall p0.1 1 := by
      apply (continuous_fst.continuousAt.eventually
        (Metric.closedBall_mem_nhds p0.1 (by norm_num : (0:ℝ)<1)))
    filter_upwards [hnear] with p hp
    filter_upwards [sphereLaw_support (by omega : 1 ≤ n+1)] with σ hσ
    by_cases hmem : σ ∈ B p
    · rw [show F p σ = _ from Set.indicator_of_mem hmem _]
      exact (hM _ ⟨(p.1,σ),⟨hp,hσ⟩,rfl⟩).trans (le_max_left _ _)
    · rw [show F p σ=0 from Set.indicator_of_notMem hmem _,norm_zero]
      exact le_max_right _ _
  · exact integrable_const _
  · have hboundary := band_boundary_null hn p0.2.1 p0.2.2 (Real.sqrt Q) b
    have ha : ∀ᵐ σ ∂sphereLaw (n+1), |overlap σ p0.2.1-Real.sqrt Q| ≠ b := by
      simpa only [ae_iff,not_not] using hboundary
    filter_upwards [ha] with σ hσ
    have hv : Continuous (fun p : Disorder (n+1) μ.maxDegree × S =>
        |overlap σ p.2.1-Real.sqrt Q|) := by unfold overlap; fun_prop
    by_cases hlt : |overlap σ p0.2.1-Real.sqrt Q| < b
    · have he : (fun p => F p σ) =ᶠ[𝓝 p0]
          (fun p => Real.exp (β*field (mixtureCoefficients μ) p.1 σ)) := by
        filter_upwards [hv.continuousAt.eventually (gt_mem_nhds hlt)] with p hp
        exact Set.indicator_of_mem (s := B p) (show σ ∈ B p from hp.le) _
      have hc : Continuous (fun p : Disorder (n+1) μ.maxDegree × S =>
          Real.exp (β*field (mixtureCoefficients μ) p.1 σ)) :=
        Real.continuous_exp.comp (continuous_const.mul
          ((field_jointContinuous (mixtureCoefficients μ)).comp
            (continuous_fst.prodMk continuous_const)))
      exact hc.continuousAt.congr_of_eventuallyEq he
    · have hgt : b < |overlap σ p0.2.1-Real.sqrt Q| := lt_of_le_of_ne (not_lt.mp hlt) hσ.symm
      have he : (fun p => F p σ) =ᶠ[𝓝 p0] (fun _ => (0:ℝ)) := by
        filter_upwards [hv.continuousAt.eventually (lt_mem_nhds hgt)] with p hp
        exact Set.indicator_of_notMem (s := B p) (show σ ∉ B p from not_le.mpr hp) _
      exact continuousAt_const.congr_of_eventuallyEq he

end SlowEquilibration.SourceMixedBandsLiteral
