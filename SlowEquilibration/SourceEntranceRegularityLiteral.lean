-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.SourceEntranceRegressionBoundary
public import SlowEquilibration.ConditionedEntranceSourceRateAllSmallScales
public import SlowEquilibration.ConditionedEntrancePureRateAllSmallScales
public import SlowEquilibration.ConditionedEntranceSourceCutoffHorizonMono
public import SlowEquilibration.ConditionedEntrancePureCutoffHorizonMono
public import SlowEquilibration.EntranceActualSourceCutoffTiltMoments
public import SlowEquilibration.EntranceLatitudeCenterMean
public import Mathlib.Probability.ConditionalProbability

/-! The rotation-invariant tensor regularity event and its consequences for
Section 8. This file proves the block and aggregate clauses of
`lem:ent-regularity`, and conditioning estimates for the actual source
processes. The tensor event does not assert the harmonic-sector clause of
that lemma; in particular it is not identified with the manuscript's full
event. No harmonic decomposition or sharp sphere functional inequality is
assumed here. -/

@[expose] public section
noncomputable section

namespace SlowEquilibration.SourceEntranceRegularityLiteral

open MeasureTheory ProbabilityTheory Set Filter
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance
open SphericalAging HardSphereDynamics SphericalOverlapExponential
open SourceEntranceRegressionBoundary WholeFieldRegression SphericalPosteriorGradientIndependence
open scoped BigOperators RealInnerProductSpace NNReal ENNReal
set_option autoImplicit false
set_option maxHeartbeats 800000

private theorem tensorForm_eq_inner {N p : ℕ}
    (J : SphericalAging.FiniteModel.Disorder N p) (v : Fin p → Vector N) :
    GaussianLandscape.tensorForm N p J v =
      inner ℝ (WithLp.toLp 2 J) (AdaptiveGradientDisclosure.pureTensor v) := by
  classical
  rw [GaussianLandscape.tensorForm_apply]
  simp only [AdaptiveGradientDisclosure.pureTensor, PiLp.inner_apply,
    RCLike.inner_apply, conj_trivial, mul_comm]

private theorem tensorForm_rotated {N p : ℕ}
    (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : SphericalAging.FiniteModel.Disorder N p) :
    GaussianLandscape.tensorForm N p (TensorHamiltonianRotation.rotatedDisorder U J) =
      (GaussianLandscape.tensorForm N p J).compContinuousLinearMap
        (fun _ => (U.symm : Vector N →L[ℝ] Vector N)) := by
  ext1 v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [tensorForm_eq_inner, tensorForm_eq_inner,
    TensorHamiltonianRotation.rotatedDisorder, WithLp.toLp_ofLp]
  have he : AdaptiveGradientDisclosure.pureTensor v =
      TensorOrthogonalAction.action U
        (AdaptiveGradientDisclosure.pureTensor (fun i => U.symm (v i))) := by
    rw [TensorOrthogonalAction.action_pureTensor]
    simp only [LinearIsometryEquiv.apply_symm_apply]
  rw [he, (TensorOrthogonalAction.action U).inner_map_map]
  rfl

/-- The genuine ordered multilinear operator norm is unchanged by rotation. -/
theorem landscapeNorm_rotated {N p : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : SphericalAging.FiniteModel.Disorder N p) :
    GaussianLandscape.landscapeNorm N p (TensorHamiltonianRotation.rotatedDisorder U J) =
      GaussianLandscape.landscapeNorm N p J := by
  unfold GaussianLandscape.landscapeNorm
  rw [tensorForm_rotated, ContinuousMultilinearMap.norm_compContinuous_linearIsometryEquiv]

/-- The coefficient event used below is invariant under every orthogonal map. -/
theorem regularDisorder_rotated {N P : ℕ} (U : Vector N ≃ₗᵢ[ℝ] Vector N)
    (J : Disorder N P) : rotatedDisorder U J ∈ regularDisorder ↔ J ∈ regularDisorder := by
  change (∀ p, GaussianLandscape.landscapeNorm N p.val.val
    (TensorHamiltonianRotation.rotatedDisorder U (J p)) ≤ blockThreshold p) ↔ _
  simp only [landscapeNorm_rotated]
  rfl

/-- One supported homogeneous summand, with its actual covariance amplitude. -/
def degreeCoefficients (μ : FiniteMixture) (p : Degree μ.maxDegree) :
    Degree μ.maxDegree → ℝ := fun q => if q = p then mixtureCoefficients μ p else 0

/-- The summand is exactly the manuscript's `H_{N,p}`, rather than a raw tensor. -/
theorem degree_field_eq {N : ℕ} (μ : FiniteMixture) (p : Degree μ.maxDegree)
    (J : Disorder N μ.maxDegree) (x : Vector N) :
    field (degreeCoefficients μ p) J x = Real.sqrt (mixtureCoefficients μ p)*blockField p J x := by
  classical
  unfold field
  rw [Finset.sum_eq_single p]
  · simp [degreeCoefficients]
  · intro q _ hqp
    simp [degreeCoefficients,hqp]
  · simp

/-- Squaring the degree multiplier makes its square root the positive degree. -/
def radialCoefficients (μ : FiniteMixture) (Q : ℝ) : Degree μ.maxDegree → ℝ :=
  fun p => (p.val.val : ℝ)^2 * centerCoefficients (mixtureCoefficients μ) Q p

/-- The radial field is exactly the weighted sum defining `K_Q`. -/
theorem radial_field_eq {N : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) (x : Vector N) :
    field (radialCoefficients μ Q) J x =
      ∑ p : Degree μ.maxDegree, (p.val.val : ℝ)*
        Real.sqrt (centerCoefficients (mixtureCoefficients μ) Q p)*blockField p J x := by
  unfold field radialCoefficients
  apply Finset.sum_congr rfl
  intro p _
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (Nat.cast_nonneg _)]

/-- `K_Q` is the actual radial directional derivative of the center field. -/
theorem radial_field_eq_jet {N : ℕ} (μ : FiniteMixture) (Q : ℝ)
    (J : Disorder N μ.maxDegree) (x : Vector N) :
    field (radialCoefficients μ Q) J x =
      jet (centerCoefficients (mixtureCoefficients μ) Q) 1 x (fun _ => x) J := by
  rw [radial_field_eq,radial_jet_sum]
  apply Finset.sum_congr rfl
  intro p _
  ring

/-- A single dimension-independent constant for all nonharmonic clauses. -/
def regularityConstant (μ : FiniteMixture) (Q : ℝ) : ℝ :=
  1 + 6*(derivativeConstant (mixtureCoefficients μ) +
    derivativeConstant (centerCoefficients (mixtureCoefficients μ) Q) +
    derivativeConstant (radialCoefficients μ Q)) +
      ∑ p : Degree μ.maxDegree, derivativeConstant (degreeCoefficients μ p)

/-- The actual supremum of the norm over the round sphere. -/
def sphereSupNorm {N : ℕ} {E : Type*} [NormedAddCommGroup E] (f : Vector N → E) : ℝ :=
  sSup {r | ∃ x : Vector N, ‖x‖^2 = (N : ℝ) ∧ r = ‖f x‖}

private theorem sphereSupNorm_le {N : ℕ} {E : Type*} [NormedAddCommGroup E]
    (f : Vector N → E) {B : ℝ} (hB : 0 ≤ B)
    (hf : ∀ x : Vector N, ‖x‖^2 = (N : ℝ) → ‖f x‖ ≤ B) : sphereSupNorm f ≤ B := by
  unfold sphereSupNorm
  by_cases hne : ({r | ∃ x : Vector N, ‖x‖^2 = (N : ℝ) ∧ r = ‖f x‖} : Set ℝ).Nonempty
  · apply csSup_le hne
    rintro r ⟨x,hx,rfl⟩
    exact hf x hx
  · rw [Set.not_nonempty_iff_eq_empty.mp hne, Real.sSup_empty]
    exact hB

private theorem field_suprema {N P : ℕ} (hN : 1 ≤ N)
    (c : Degree P → ℝ) (J : Disorder N P) (hJ : J ∈ regularDisorder) :
    sphereSupNorm (field c J) ≤ derivativeConstant c*(N : ℝ) ∧
    sphereSupNorm (gradient (field c J)) ≤ derivativeConstant c*Real.sqrt (N : ℝ) ∧
    sphereSupNorm (iteratedFDeriv ℝ 2 (field c J)) ≤ derivativeConstant c ∧
    sphereSupNorm (tangentGradient c J) ≤ derivativeConstant c*Real.sqrt (N : ℝ) ∧
    sphereSupNorm (tangentHessian c J) ≤ 2*derivativeConstant c := by
  have hc := (derivativeConstant_pos c).le
  refine ⟨sphereSupNorm_le _ (by positivity) ?_,sphereSupNorm_le _ (by positivity) ?_,
    sphereSupNorm_le _ hc ?_,sphereSupNorm_le _ (by positivity) ?_,
    sphereSupNorm_le _ (by positivity) ?_⟩
  · intro x hx
    simpa only [Real.norm_eq_abs] using
      (field_regularDisorder_ball_bounds hN c J hJ x (LandscapeDerivatives.sphere_norm x hx).le).1
  · intro x hx
    exact (field_regularDisorder_ball_bounds hN c J hJ x
      (LandscapeDerivatives.sphere_norm x hx).le).2.1
  · intro x hx
    exact (field_regularDisorder_ball_bounds hN c J hJ x
      (LandscapeDerivatives.sphere_norm x hx).le).2.2.1
  · exact fun x hx => (field_regularDisorder_sphere_bounds hN c J hJ x hx).1
  · exact fun x hx => (field_regularDisorder_sphere_bounds hN c J hJ x hx).2

/-- Block derivatives and all three aggregate sums printed in
`lem:ent-regularity`. The block derivative form uses the equivalent scale
`sqrt(N)^m ||D^m H|| ≤ C N`, also valid for order three. -/
def NonharmonicRegularClauses {N : ℕ} (μ : FiniteMixture) (Q C : ℝ)
    (J : Disorder N μ.maxDegree) : Prop :=
  (∀ (p : Degree μ.maxDegree) (x : Vector N), ‖x‖^2 = (N : ℝ) →
    ∀ m : ℕ, m ≤ 3 → Real.sqrt (N : ℝ)^m *
      ‖iteratedFDeriv ℝ m (field (degreeCoefficients μ p) J) x‖ ≤ C*(N : ℝ)) ∧
    sphereSupNorm (fieldOfMixture μ J) +
      sphereSupNorm (field (centerCoefficients (mixtureCoefficients μ) Q) J) +
      sphereSupNorm (field (radialCoefficients μ Q) J) ≤ C*(N : ℝ) ∧
    sphereSupNorm (gradient (fieldOfMixture μ J)) +
      sphereSupNorm (gradient (field (centerCoefficients (mixtureCoefficients μ) Q) J)) +
      sphereSupNorm (tangentGradient (mixtureCoefficients μ) J) +
      sphereSupNorm (tangentGradient (centerCoefficients (mixtureCoefficients μ) Q) J) ≤
        C*Real.sqrt (N : ℝ) ∧
    sphereSupNorm (iteratedFDeriv ℝ 2 (fieldOfMixture μ J)) +
      sphereSupNorm (iteratedFDeriv ℝ 2 (field (centerCoefficients (mixtureCoefficients μ) Q) J)) +
      sphereSupNorm (tangentHessian (mixtureCoefficients μ) J) +
      sphereSupNorm (tangentHessian (centerCoefficients (mixtureCoefficients μ) Q) J) ≤ C

/-- The explicitly constructed rotation-invariant event proves clauses (1)
and (3), with the exact exponential failure bound and no regularity premise. -/
theorem nonharmonic_regular_event (μ : FiniteMixture) (Q : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ, 2 ≤ N →
      MeasurableSet (regularDisorder (N := N) (P := μ.maxDegree)) ∧
      (disorderLaw N μ.maxDegree).real regularDisorderᶜ ≤ Real.exp (-(N : ℝ)) ∧
      (∀ (U : Vector N ≃ₗᵢ[ℝ] Vector N) (J : Disorder N μ.maxDegree),
        rotatedDisorder U J ∈ regularDisorder ↔ J ∈ regularDisorder) ∧
      ∀ (J : Disorder N μ.maxDegree), J ∈ regularDisorder → NonharmonicRegularClauses μ Q C J := by
  classical
  let A := derivativeConstant (mixtureCoefficients μ)
  let B := derivativeConstant (centerCoefficients (mixtureCoefficients μ) Q)
  let D := derivativeConstant (radialCoefficients μ Q)
  have hA : 0 < A := derivativeConstant_pos _
  have hB : 0 < B := derivativeConstant_pos _
  have hD : 0 < D := derivativeConstant_pos _
  have hsum : 0 ≤ ∑ p : Degree μ.maxDegree, derivativeConstant (degreeCoefficients μ p) :=
    Finset.sum_nonneg fun p _ => (derivativeConstant_pos _).le
  have hC : 0 < regularityConstant μ Q := by unfold regularityConstant; dsimp [A,B,D] at *; positivity
  refine ⟨regularityConstant μ Q,hC,?_⟩
  intro N hN
  refine ⟨regularDisorder_measurable _ _,regularDisorder_failure_probability hN,
    fun U J => regularDisorder_rotated U J,?_⟩
  intro J hJ
  constructor
  · intro p x hx m hm
    have hp : derivativeConstant (degreeCoefficients μ p) ≤ regularityConstant μ Q := by
      have hle := Finset.single_le_sum (fun q (_ : q ∈ Finset.univ) =>
        (derivativeConstant_pos (degreeCoefficients μ q)).le) (Finset.mem_univ p)
      unfold regularityConstant
      linarith
    exact (field_regularDisorder_derivatives (show 1 ≤ N by omega) _ J hJ x
      (LandscapeDerivatives.sphere_norm x hx).le m hm).trans
        (mul_le_mul_of_nonneg_right hp (Nat.cast_nonneg _))
  · have ha := field_suprema (by omega : 1 ≤ N) (mixtureCoefficients μ) J hJ
    have hb := field_suprema (by omega : 1 ≤ N) (centerCoefficients (mixtureCoefficients μ) Q) J hJ
    have hd := field_suprema (by omega : 1 ≤ N) (radialCoefficients μ Q) J hJ
    have hlarge : 6*(A+B+D) ≤ regularityConstant μ Q := by
      unfold regularityConstant
      change 6*(A+B+D) ≤ 1+6*(A+B+D)+_
      linarith
    have hv : A+B+D ≤ regularityConstant μ Q := by linarith
    have hg : 2*(A+B) ≤ regularityConstant μ Q := by linarith
    have hh : 3*(A+B) ≤ regularityConstant μ Q := by linarith
    refine ⟨(add_le_add (add_le_add ha.1 hb.1) hd.1).trans ?_,
      (add_le_add (add_le_add (add_le_add ha.2.1 hb.2.1) ha.2.2.2.1) hb.2.2.2.1).trans ?_,
      (add_le_add (add_le_add (add_le_add ha.2.2.1 hb.2.2.1) ha.2.2.2.2) hb.2.2.2.2).trans ?_⟩
    · change A*(N : ℝ)+B*(N : ℝ)+D*(N : ℝ) ≤ _
      nlinarith [mul_le_mul_of_nonneg_right hv (Nat.cast_nonneg N)]
    · change A*Real.sqrt (N : ℝ)+B*Real.sqrt (N : ℝ)+
        A*Real.sqrt (N : ℝ)+B*Real.sqrt (N : ℝ) ≤ _
      nlinarith [mul_le_mul_of_nonneg_right hg (Real.sqrt_nonneg (N : ℝ))]
    · change A+B+2*A+2*B ≤ _
      linarith

private theorem mass_half_of_failure {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Set Ω} (hE : MeasurableSet E)
    {N : ℕ} (hN : 2 ≤ N) (hfail : P.real Eᶜ ≤ Real.exp (-(N : ℝ))) :
    (1/2 : ℝ) ≤ P.real E := by
  have hr : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hexp : Real.exp (-(N : ℝ)) ≤ 1/2 := by
    rw [Real.exp_neg]
    have h := Real.add_one_le_exp (N : ℝ)
    apply (inv_le_iff_one_le_mul₀ (Real.exp_pos _)).mpr
    linarith
  have hs := measureReal_add_measureReal_compl (μ := P) hE
  rw [probReal_univ] at hs
  linarith

/-- Conditioning on this concrete event defines a probability law in every
dimension at least two; its normalizing mass is at least one half. -/
theorem regularDisorder_mass_half {N P : ℕ} (hN : 2 ≤ N) :
    (1/2 : ℝ) ≤ (disorderLaw N P).real regularDisorder :=
  mass_half_of_failure _ (regularDisorder_measurable _ _)
    hN (regularDisorder_failure_probability hN)

/-- The actual Gaussian disorder restricted to the rotation-invariant
event above and normalized by its probability. -/
def regularDisorderLaw (N P : ℕ) : Measure (Disorder N P) :=
  ProbabilityTheory.cond (disorderLaw N P) regularDisorder

/-- The normalizing probability is nonzero, proved rather than assumed. -/
theorem regularDisorderLaw_probability {N P : ℕ} (hN : 2 ≤ N) :
    IsProbabilityMeasure (regularDisorderLaw N P) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  intro hz
  have hm := regularDisorder_mass_half (P := P) hN
  simp only [Measure.real,hz,ENNReal.toReal_zero] at hm
  norm_num at hm

private theorem integral_cond_le_twice {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Set Ω}
    (hhalf : (1/2 : ℝ) ≤ P.real E) (f : Ω → ℝ)
    (hi : Integrable f P) (hf : ∀ x, 0 ≤ f x) :
    (∫ x, f x ∂ProbabilityTheory.cond P E) ≤ 2*∫ x, f x ∂P := by
  rw [ProbabilityTheory.cond, integral_smul_measure, ENNReal.toReal_inv]
  have hP : 0 < P.real E := by linarith
  have hinv : (P.real E)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ hP).mpr
    linarith
  have hnon : 0 ≤ ∫ x in E, f x ∂P := integral_nonneg hf
  calc
    _ ≤ 2*∫ x in E, f x ∂P := mul_le_mul_of_nonneg_right hinv hnon
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (setIntegral_le_integral hi (ae_of_all _ hf)) (by norm_num)

private theorem unit_integrable {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {f : Ω → ℝ}
    (hm : Measurable f) (hf : ∀ x, f x ∈ Icc 0 1) : Integrable f P := by
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ fun x => by simpa [abs_of_nonneg (hf x).1] using (hf x).2

private theorem horizon_mono (N : ℕ) {γ γ' : ℝ} (h : γ ≤ γ') :
    exponentialGridHorizon γ N ≤ exponentialGridHorizon γ' N := by
  apply NNReal.coe_le_coe.mp
  exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left h (Nat.cast_nonneg N))

private theorem two_exp_le {c x : ℝ} (hc : 0 < c)
    (hx : 2*Real.log 2/c ≤ x) :
    2*Real.exp (-c*x) ≤ Real.exp (-(c/2)*x) := by
  conv_lhs => arg 1; rw [← Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have := (div_le_iff₀ hc).mp hx
  nlinarith

private theorem mixed_axis_mono {N : ℕ} (hN : 1 ≤ N)
    (μ : FiniteMixture) {Q : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) {α : ℝ} (hα : 0 < α)
    (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (β e k : ℝ)
    {H H' : ℝ≥0} (hH : H ≤ H') (J : Disorder N μ.maxDegree) :
    sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H e k J ≤
      sourceAxisAveragedCapHitProbability μ Q hQ hnp α χ hχ β H' e k J := by
  have hi (T : ℝ≥0) : Integrable (fun u : Vector N =>
      sourceCapHitProbability μ Q hQ hnp α χ hχ β T (J,(u,(e,k)))) (sphereLaw N) :=
    unit_integrable _ ((sourceCapHitProbability_measurable μ Q hQ hnp α χ hχ β T).comp
      (by fun_prop)) (fun u => sourceCapHitProbability_mem_unit μ Q hQ hnp α χ hχ β T (J,(u,(e,k))))
  apply integral_mono_ae (hi H) (hi H')
  filter_upwards [sphereLaw_support hN] with u hu
  exact sourceCapHitProbability_mono_horizon hN μ hnp Q hQ hQ1 α hα χ hχ β H H' hH
    (J,(u,(e,k))) ((onSphere_iff_norm_sq u).mpr hu)

/-- The actual mixed truncated process, averaged over independent uniform
axis and initial point and Wiener noise, with the Gaussian seed conditioned
on the proved tensor event. One horizon exponent works for all smaller
positive exponents. Identifying this event with the full manuscript event
still requires the harmonic-sector bounds. -/
theorem conditioned_mixed_truncated_cap_avoidance
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ aStar : ℝ, 0 < aStar ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 c C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < c ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
            (∫ J, sourceAxisAveragedCapHitProbability μ Q hQ hnp
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β (exponentialGridHorizon γ (n+1)) e k J
              ∂regularDisorderLaw (n+1) μ.maxDegree) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-c*((n+1 : ℕ) : ℝ)) := by
  let χ := sourceScalarCutoff
  have hχ : ContDiff ℝ 2 χ := sourceScalarCutoff_contDiff_two
  have hχb : ∀ s, |χ s| ≤ 1 := sourceScalarCutoff_abs_le_one
  have hχR : ∀ s, 2 < |s| → χ s = 0 := fun _ hs => sourceScalarCutoff_zero_of_two_lt_abs hs
  obtain ⟨aStar,hStar,hall⟩ :=
    actual_mixedSource_axis_averaged_cap_hit_source_rate_all_small_scales
      μ hd hQ hQ1 hnp hB hβ χ hχ hχb hχR
  refine ⟨aStar,hStar,?_⟩
  intro a ha haStar
  obtain ⟨γ0,c,C,hγ0,hc,hC,hN⟩ := hall ha haStar
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp hN
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/c)
  refine ⟨γ0,c/2,2*C,max n0 (max M 1),hγ0,by positivity,by positivity,?_⟩
  intro n hn γ _ hγ e k he hk
  let f : Disorder (n+1) μ.maxDegree → ℝ := sourceAxisAveragedCapHitProbability μ Q hQ hnp
    (2*a) χ hχ β (exponentialGridHorizon γ (n+1)) e k
  let f0 : Disorder (n+1) μ.maxDegree → ℝ := sourceAxisAveragedCapHitProbability μ Q hQ hnp
    (2*a) χ hχ β (exponentialGridHorizon γ0 (n+1)) e k
  have hi : Integrable f (disorderLaw (n+1) μ.maxDegree) :=
    unit_integrable _ (sourceAxisAveragedCapHitProbability_measurable ..)
      (fun J => sourceAxisAveragedCapHitProbability_mem_unit μ Q hQ hnp (2*a) χ hχ β
        (exponentialGridHorizon γ (n+1)) e k J)
  have hi0 : Integrable f0 (disorderLaw (n+1) μ.maxDegree) :=
    unit_integrable _ (sourceAxisAveragedCapHitProbability_measurable ..)
      (fun J => sourceAxisAveragedCapHitProbability_mem_unit μ Q hQ hnp (2*a) χ hχ β
        (exponentialGridHorizon γ0 (n+1)) e k J)
  have hmono : ∫ J, f J ∂disorderLaw (n+1) μ.maxDegree ≤
      ∫ J, f0 J ∂disorderLaw (n+1) μ.maxDegree :=
    integral_mono hi hi0 (fun J => mixed_axis_mono (by omega) μ hQ hQ1 hnp
      (by positivity) χ hχ β e k (horizon_mono _ hγ) J)
  have hcond := integral_cond_le_twice (disorderLaw (n+1) μ.maxDegree)
    (regularDisorder_mass_half (by omega)) f hi
    (fun J => (sourceAxisAveragedCapHitProbability_mem_unit μ Q hQ hnp (2*a) χ hχ β
      (exponentialGridHorizon γ (n+1)) e k J).1)
  have htail := two_exp_le hc (x := ((n+1 : ℕ) : ℝ)) (by
    have hMn : M ≤ n+1 := by omega
    exact hM.trans (by exact_mod_cast hMn))
  change (∫ J, f J ∂regularDisorderLaw (n+1) μ.maxDegree) ≤ _
  exact hcond.trans ((mul_le_mul_of_nonneg_left
    (hmono.trans (hn0 n (by omega) e k he hk)) (by norm_num)).trans (by nlinarith))

private theorem pure_axis_mono {N : ℕ} (hN : 1 ≤ N)
    (d : ℕ) (hd : 2 ≤ d) (c : ℝ) (hc : 0 < c) (Q : ℝ)
    {α : ℝ} (hα : 0 < α) (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ) (β e : ℝ)
    {H H' : ℝ≥0} (hH : H ≤ H') (J : Disorder N (FiniteMixture.pure d hd c hc).maxDegree) :
    pureAxisAveragedCapHitProbability d hd c hc Q α χ hχ β H e J ≤
      pureAxisAveragedCapHitProbability d hd c hc Q α χ hχ β H' e J := by
  have hi (T : ℝ≥0) : Integrable (fun u : Vector N =>
      pureSourceCapHitProbability d hd c hc Q α χ hχ β T (J,(u,(e,0)))) (sphereLaw N) :=
    unit_integrable _ ((pureSourceCapHitProbability_measurable d hd c hc Q α χ hχ β T).comp
      (by fun_prop)) (fun u => pureSourceCapHitProbability_mem_unit d hd c hc Q α χ hχ β T (J,(u,(e,0))))
  apply integral_mono_ae (hi H) (hi H')
  filter_upwards [sphereLaw_support hN] with u hu
  exact pureSourceCapHitProbability_mono_horizon hN d hd c hc Q α hα χ hχ β H H' hH
    (J,(u,(e,0))) ((onSphere_iff_norm_sq u).mpr hu)

/-- The proper-pure truncated process under the same proved disorder
conditioning, uniformly over every smaller positive horizon exponent. -/
theorem conditioned_pure_truncated_cap_avoidance
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
    ∃ aStar : ℝ, 0 < aStar ∧ ∀ {a : ℝ}, 0 < a → a ≤ aStar →
      ∃ (γ0 κ C : ℝ) (N0 : ℕ), 0 < γ0 ∧ 0 < κ ∧ 0 < C ∧
        ∀ n ≥ N0, ∀ {γ : ℝ}, 0 < γ → γ ≤ γ0 →
          ∀ e : ℝ, |e| ≤ B →
            (∫ J, pureAxisAveragedCapHitProbability d (by omega) c hc Q
              (2*a) sourceScalarCutoff sourceScalarCutoff_contDiff_two β (exponentialGridHorizon γ (n+1)) e J
              ∂regularDisorderLaw (n+1) μ.maxDegree) ≤
              C*(((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)+
                ((n+1 : ℕ) : ℝ)^(3-(μ.minDegree : ℝ)))+
                Real.exp (-κ*((n+1 : ℕ) : ℝ)) := by
  let χ := sourceScalarCutoff
  have hχ : ContDiff ℝ 2 χ := sourceScalarCutoff_contDiff_two
  have hχb : ∀ s, |χ s| ≤ 1 := sourceScalarCutoff_abs_le_one
  have hχR : ∀ s, 2 < |s| → χ s = 0 := fun _ hs => sourceScalarCutoff_zero_of_two_lt_abs hs
  dsimp only
  let μ := FiniteMixture.pure d (by omega : 2 ≤ d) c hc
  obtain ⟨aStar,hStar,hall⟩ :=
    actual_pureSource_axis_averaged_cap_hit_source_rate_all_small_scales
      d hd c hc hQ hB hβ χ hχ hχb hχR
  refine ⟨aStar,hStar,?_⟩
  intro a ha haStar
  obtain ⟨γ0,κ,C,hγ0,hκ,hC,hN⟩ := hall ha haStar
  obtain ⟨n0,hn0⟩ := eventually_atTop.mp hN
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/κ)
  refine ⟨γ0,κ/2,2*C,max n0 (max M 1),hγ0,by positivity,by positivity,?_⟩
  intro n hn γ _ hγ e he
  let f : Disorder (n+1) μ.maxDegree → ℝ := pureAxisAveragedCapHitProbability d
    (by omega) c hc Q (2*a) χ hχ β (exponentialGridHorizon γ (n+1)) e
  let f0 : Disorder (n+1) μ.maxDegree → ℝ := pureAxisAveragedCapHitProbability d
    (by omega) c hc Q (2*a) χ hχ β (exponentialGridHorizon γ0 (n+1)) e
  have hi : Integrable f (disorderLaw (n+1) μ.maxDegree) :=
    unit_integrable _ (pureAxisAveragedCapHitProbability_measurable ..)
      (fun J => pureAxisAveragedCapHitProbability_mem_unit d (by omega) c hc Q (2*a) χ hχ β
        (exponentialGridHorizon γ (n+1)) e J)
  have hi0 : Integrable f0 (disorderLaw (n+1) μ.maxDegree) :=
    unit_integrable _ (pureAxisAveragedCapHitProbability_measurable ..)
      (fun J => pureAxisAveragedCapHitProbability_mem_unit d (by omega) c hc Q (2*a) χ hχ β
        (exponentialGridHorizon γ0 (n+1)) e J)
  have hmono : ∫ J, f J ∂disorderLaw (n+1) μ.maxDegree ≤
      ∫ J, f0 J ∂disorderLaw (n+1) μ.maxDegree :=
    integral_mono hi hi0 (fun J => pure_axis_mono (by omega) d (by omega) c hc Q
      (by positivity) χ hχ β e (horizon_mono _ hγ) J)
  have hcond := integral_cond_le_twice (disorderLaw (n+1) μ.maxDegree)
    (regularDisorder_mass_half (by omega)) f hi
    (fun J => (pureAxisAveragedCapHitProbability_mem_unit d (by omega) c hc Q (2*a) χ hχ β
      (exponentialGridHorizon γ (n+1)) e J).1)
  have htail := two_exp_le hκ (x := ((n+1 : ℕ) : ℝ)) (by
    have hMn : M ≤ n+1 := by omega
    exact hM.trans (by exact_mod_cast hMn))
  change (∫ J, f J ∂regularDisorderLaw (n+1) μ.maxDegree) ≤ _
  exact hcond.trans ((mul_le_mul_of_nonneg_left
    (hmono.trans (hn0 n (by omega) e he)) (by norm_num)).trans (by nlinarith))

private theorem event_cond_le_twice {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] {E : Set Ω} (hE : MeasurableSet E)
    (hhalf : (1/2 : ℝ) ≤ P.real E) (A : Set Ω) :
    (ProbabilityTheory.cond P E).real A ≤ 2*P.real A := by
  rw [Measure.real, ProbabilityTheory.cond_apply hE, ENNReal.toReal_mul, ENNReal.toReal_inv]
  have hpos : 0 < P.real E := by linarith
  have hinv : (P.real E)⁻¹ ≤ 2 := by
    apply (inv_le_iff_one_le_mul₀ hpos).mpr
    linarith
  exact (mul_le_mul_of_nonneg_right hinv (ENNReal.toReal_nonneg)).trans
    (mul_le_mul_of_nonneg_left (measureReal_mono inter_subset_right (measure_ne_top _ _))
      (by norm_num))

/-- The same coefficient event in the literal joint boundary seed space. -/
def boundaryRegular (n : ℕ) (μ : FiniteMixture) :
    Set (Vector (n+1) × BoundarySeed n μ) :=
  {q | unpackDisorder q.2.1 ∈ regularDisorder}

local instance boundary_probability (n : ℕ) (μ : FiniteMixture) :
    IsProbabilityMeasure (boundarySeedLaw n μ) := by
  unfold boundarySeedLaw
  infer_instance

private theorem boundaryRegular_measurable (n : ℕ) (μ : FiniteMixture) :
    MeasurableSet (boundaryRegular n μ) := by
  exact (regularDisorder_measurable _ _).preimage
    ((unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp measurable_snd.fst)

private theorem boundaryRegular_failure {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture) :
    (boundarySeedLaw n μ).real (boundaryRegular n μ)ᶜ ≤ Real.exp (-((n+1 : ℕ) : ℝ)) := by
  let E : Set (BoundarySeed n μ) := {q | unpackDisorder q.1 ∉ regularDisorder}
  have hE : MeasurableSet E := (regularDisorder_measurable _ _).compl.preimage
    ((unpackCLM (n+1) μ.maxDegree).continuous.measurable.comp measurable_fst)
  have he : (boundarySeedLaw n μ).real (boundaryRegular n μ)ᶜ =
      (posteriorTrajectoryLaw n μ).real E := by
    have hm : (boundarySeedLaw n μ).map Prod.snd = posteriorTrajectoryLaw n μ := by
      unfold boundarySeedLaw
      rw [Measure.map_snd_prod,measure_univ,one_smul]
    simp only [Measure.real]
    rw [← hm, Measure.map_apply measurable_snd hE]
    rfl
  rw [he]
  exact SphericalPosteriorGradientIndependence.posteriorTrajectory_regularDisorder_failure_le n hn μ

/-- Disorder conditioning in the original Gaussian seed leaves the axis,
uniform initial point, and Brownian noise independent of that seed. -/
def regularBoundarySeedLaw (n : ℕ) (μ : FiniteMixture) :
    Measure (Vector (n+1) × BoundarySeed n μ) :=
  ProbabilityTheory.cond (boundarySeedLaw n μ) (boundaryRegular n μ)

private theorem cond_product_left {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure A) (R : Measure Z) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (E : Set A) :
    ProbabilityTheory.cond (P.prod R) (E ×ˢ univ) = (ProbabilityTheory.cond P E).prod R := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod,measure_univ,mul_one,Measure.prod_smul_left,
    Measure.restrict_prod_eq_prod_univ]

private theorem cond_product_right {A Z : Type*} [MeasurableSpace A] [MeasurableSpace Z]
    (P : Measure A) (R : Measure Z) [IsProbabilityMeasure P] [IsProbabilityMeasure R]
    (E : Set Z) :
    ProbabilityTheory.cond (P.prod R) (univ ×ˢ E) = P.prod (ProbabilityTheory.cond R E) := by
  unfold ProbabilityTheory.cond
  rw [Measure.prod_prod,measure_univ,one_mul,Measure.prod_smul_right]
  congr 1
  simpa only [Measure.restrict_univ] using
    (Measure.prod_restrict (μ := P) (ν := R) univ E).symm

/-- Exact product-law identity: only the original Gaussian coefficient seed
is conditioned; the uniform axis, uniform initial state and Wiener law stay
as independent factors. -/
theorem regularBoundarySeedLaw_eq_product (n : ℕ) (μ : FiniteMixture) :
    regularBoundarySeedLaw n μ =
      (sphereLaw (n+1)).prod
        ((ProbabilityTheory.cond (stdGaussian (EuclideanDisorder (n+1) μ.maxDegree))
          {z | unpackDisorder z ∈ regularDisorder}).prod
            ((sphereLaw (n+1)).prod (VectorBrownian.law (n+1)))) := by
  have he : boundaryRegular n μ = univ ×ˢ
      ({z : EuclideanDisorder (n+1) μ.maxDegree | unpackDisorder z ∈ regularDisorder} ×ˢ univ) := by
    ext q
    simp only [boundaryRegular,mem_ofPred_eq,mem_prod,mem_univ,true_and,and_true]
  unfold regularBoundarySeedLaw boundarySeedLaw
  rw [he,cond_product_right]
  unfold posteriorTrajectoryLaw
  rw [cond_product_left]

/-- The original joint seed conditioned on the event above is a genuine
probability measure; positivity of the conditioning mass is discharged. -/
theorem regularBoundarySeedLaw_probability {n : ℕ} (hn : 1 ≤ n) (μ : FiniteMixture) :
    IsProbabilityMeasure (regularBoundarySeedLaw n μ) := by
  apply ProbabilityTheory.cond_isProbabilityMeasure
  intro hz
  have hm := mass_half_of_failure (boundarySeedLaw n μ) (boundaryRegular_measurable n μ)
    (by omega : 2 ≤ n+1) (boundaryRegular_failure hn μ)
  simp only [Measure.real,hz,ENNReal.toReal_zero] at hm
  norm_num at hm

/-- The mixed removed-gradient boundary estimate survives the explicit
regularity conditioning, with half the exponential decay exponent. -/
theorem conditioned_mixed_gradient_cutoff_not_reached
    (μ : FiniteMixture) (hnp : μ.minDegree < μ.maxDegree)
    {Q B β b : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e k : ℝ, |e| ≤ B → |k| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real (mixedGradientExit n μ Q β e k b (H+2*T) H) ≤
          Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        (regularBoundarySeedLaw n μ).real (mixedGradientExit n μ Q β e k b (H+2*T) H) ≤
          Real.exp (-(c/2)*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,n0,hn0⟩ :=
    mixed_uniform_axis_gradient_cutoff_not_reached μ hnp hQ hQ1 hB hβ hb
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/c)
  refine ⟨T,hT,γ,c,hγ,hc,max n0 (max M 1),?_⟩
  intro n hn e k he hk
  have hrate := hn0 n (by omega) e k he hk
  refine ⟨hrate,?_⟩
  have hhalf := mass_half_of_failure (boundarySeedLaw n μ) (boundaryRegular_measurable n μ)
    (by omega : 2 ≤ n+1) (boundaryRegular_failure (by omega) μ)
  have hcond := event_cond_le_twice (boundarySeedLaw n μ) (boundaryRegular_measurable n μ)
    hhalf (mixedGradientExit n μ Q β e k b
      (exponentialGridHorizon γ (n+1)+2*T) (exponentialGridHorizon γ (n+1)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hrate (by norm_num)).trans
    (two_exp_le hc (by
      have hMn : M ≤ n+1 := by omega
      exact hM.trans (by exact_mod_cast hMn))))

/-- Proper value/zero-gradient conditioning, including all admissible pure
marks, with the same explicit conditioned boundary conclusion. -/
theorem conditioned_value_gradient_cutoff_not_reached
    (μ : FiniteMixture) {Q B β b : ℝ} (hQ : 0 < Q)
    (hB : 0 ≤ B) (hβ : 0 ≤ β) (hb : 0 < b) :
    ∃ (T : ℝ≥0), 0 < T ∧ ∃ γ c : ℝ, 0 < γ ∧ 0 < c ∧
      ∃ n0 : ℕ, ∀ n ≥ n0, ∀ e : ℝ, |e| ≤ B →
        let H := exponentialGridHorizon γ (n+1)
        (boundarySeedLaw n μ).real (valueGradientExit n μ Q β e b (H+2*T) H) ≤
          Real.exp (-c*((n+1 : ℕ) : ℝ)) ∧
        (regularBoundarySeedLaw n μ).real (valueGradientExit n μ Q β e b (H+2*T) H) ≤
          Real.exp (-(c/2)*((n+1 : ℕ) : ℝ)) := by
  obtain ⟨T,hT,γ,c,hγ,hc,n0,hn0⟩ :=
    value_uniform_axis_gradient_cutoff_not_reached μ hQ hB hβ hb
  obtain ⟨M,hM⟩ := exists_nat_ge (2*Real.log 2/c)
  refine ⟨T,hT,γ,c,hγ,hc,max n0 (max M 1),?_⟩
  intro n hn e he
  have hrate := hn0 n (by omega) e he
  refine ⟨hrate,?_⟩
  have hhalf := mass_half_of_failure (boundarySeedLaw n μ) (boundaryRegular_measurable n μ)
    (by omega : 2 ≤ n+1) (boundaryRegular_failure (by omega) μ)
  have hcond := event_cond_le_twice (boundarySeedLaw n μ) (boundaryRegular_measurable n μ)
    hhalf (valueGradientExit n μ Q β e b
      (exponentialGridHorizon γ (n+1)+2*T) (exponentialGridHorizon γ (n+1)))
  exact hcond.trans ((mul_le_mul_of_nonneg_left hrate (by norm_num)).trans
    (two_exp_le hc (by
      have hMn : M ≤ n+1 := by omega
      exact hM.trans (by exact_mod_cast hMn))))

end SlowEquilibration.SourceEntranceRegularityLiteral
