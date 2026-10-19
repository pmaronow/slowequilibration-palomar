-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.SphericalInfiniteDriftTruncation
public import SlowEquilibration.SphericalC1FiniteBridge
public import SlowEquilibration.SphericalInfiniteCutoffLaw

/-! Gibbs stationarity of the literal infinite-field Brownian diffusion,
obtained by actual finite-cutoff transition convergence. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.SphericalInfiniteModel
open Set MeasureTheory ProbabilityTheory Filter SphericalModel SphericalForm
open SphericalAging SphericalAging.HardSphereDynamics SphericalDynamics SphericalReversibility
open scoped Topology NNReal
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

def partialExpectation {N : ℕ} (μ : InfiniteMixture) (J : Disorder N) (β : ℝ)
    (P : ℕ) (t : ℝ≥0) (f : Vector N → ℝ) : Vector N → ℝ :=
  SphericalC1Dynamics.expectation β (partialGradient μ P J)
    (partialGradient_contDiff μ P J) t f

def infiniteExpectation (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1)) (β : ℝ)
    (t : ℝ≥0) (f : Vector (n+1) → ℝ) : Vector (n+1) → ℝ :=
  SphericalC1Dynamics.expectation β (infiniteGradient n μ J)
    (infiniteGradient_contDiff n μ J) t f

private theorem sphere_norm_le {N : ℕ} {x : Vector N} (hx : OnSphere x) :
    ‖x‖≤Real.sqrt N :=
  le_of_eq ((Real.sqrt_sq (norm_nonneg _)).symm.trans
    (congrArg Real.sqrt ((onSphere_iff_norm_sq x).mp hx)))

theorem partialField_norm_le_fullJetEnvelope {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) (P : ℕ)
    (x : Vector N) (hx : OnSphere x) : ‖partialField μ P J x‖≤fullJetEnvelope μ 0 J := by
  have hb (p : ℕ) : ‖block μ p J x‖≤blockJetEnvelope μ 0 p J := by
    simpa only [norm_iteratedFDeriv_zero] using
      block_iteratedFDeriv_norm_le hN μ 0 p J x (sphere_norm_le hx)
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum (fun p _ => hb p)).trans
    ((hJ 0 (by omega)).sum_le_tsum (Finset.range P)
      (fun p _ => blockJetEnvelope_nonneg hN μ 0 p J)))

theorem partialField_tendsto_onSphere {N : ℕ} (hN : 0<N) (μ : InfiniteMixture)
    (J : Disorder N) (hJ : J∈summableJetDisorder μ) (x : Vector N) (hx : OnSphere x) :
    Tendsto (fun P => partialField μ P J x) atTop (𝓝 (field μ J x)) := by
  have hb (p : ℕ) : ‖block μ p J x‖≤blockJetEnvelope μ 0 p J := by
    simpa only [norm_iteratedFDeriv_zero] using
      block_iteratedFDeriv_norm_le hN μ 0 p J x (sphere_norm_le hx)
  have hn : Summable (fun p => ‖block μ p J x‖) :=
    (hJ 0 (by omega)).of_nonneg_of_le (fun _ => norm_nonneg _) hb
  exact hn.of_norm.tendsto_sum_tsum_nat

theorem partition_mul_integral_gibbs {N : ℕ} (hN : 1≤N) (β : ℝ)
    (H : Vector N → ℝ) (hH : Continuous H) (f : Vector N → ℝ) :
    partition N β H*(∫ x,f x ∂gibbsLaw N β H)=
      ∫ x,Real.exp (β*H x)*f x ∂sphereLaw N := by
  rw [integral_gibbsLaw hN β hH]
  simp_rw [gibbsDensity,div_mul_eq_mul_div]
  rw [integral_div,mul_div_cancel₀ _ (partition_pos hN β hH).ne']

theorem partial_weighted_stationarity {N : ℕ} (hN : 1≤N) (μ : InfiniteMixture)
    (J : Disorder N) (β : ℝ) (P : ℕ) (hP : ∃ p,p≤P+1 ∧ 0<μ.coeff p)
    (t : ℝ≥0) (f : Vector N → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x,Real.exp (β*partialField μ P J x)*partialExpectation μ J β P t f x ∂sphereLaw N)=
      ∫ x,Real.exp (β*partialField μ P J x)*f x ∂sphereLaw N := by
  let ν := μ.finiteCutoff (P+1) hP
  let K := finiteDisorder (N := N) ν.maxDegree J
  have he : fieldOfMixture ν K=partialField μ P J := by
    funext x
    simpa only [Nat.add_sub_cancel] using finiteCutoff_field μ (P+1) hP J x
  have hg : partialGradient μ P J=mixedGradient ν K := by
    unfold partialGradient mixedGradient
    rw [he]
  have hE (x : Vector N) (hx : OnSphere x) :
      partialExpectation μ J β P t f x=mixedExpectation ν K β t f x := by
    have heq : (⟨partialGradient μ P J,partialGradient_contDiff μ P J⟩ :
        {g : State N → State N // ContDiff ℝ 1 g})=
        ⟨mixedGradient ν K,(mixedGradient_contDiff ν K).of_le (by simp)⟩ := Subtype.ext hg
    have hh := congrArg (fun g : {g : State N → State N // ContDiff ℝ 1 g} =>
      SphericalC1Dynamics.expectation β g.val g.property t f x) heq
    exact hh.trans (SphericalC1Dynamics.expectation_eq_mixed (by omega) ν K β x hx t f)
  have hs := compact_mixedExpectation_stationary hN ν K β hf hfc t
  change (∫ x,mixedExpectation ν K β t f x ∂gibbsLaw N β (fieldOfMixture ν K))=
    ∫ x,f x ∂gibbsLaw N β (fieldOfMixture ν K) at hs
  rw [he] at hs
  have hsta : (∫ x,partialExpectation μ J β P t f x ∂gibbsLaw N β (partialField μ P J))=
      ∫ x,f x ∂gibbsLaw N β (partialField μ P J) := by
    rw [← hs]
    apply integral_congr_ae
    filter_upwards [gibbsLaw_support hN β (partialField μ P J)] with x hx
    exact hE x ((onSphere_iff_norm_sq x).mpr hx)
  rw [← partition_mul_integral_gibbs hN β _ (partialField_contDiff μ P J).continuous,
    ← partition_mul_integral_gibbs hN β _ (partialField_contDiff μ P J).continuous,hsta]

/-- Dominated convergence for actual finite-cutoff Gibbs numerators. -/
theorem weighted_partial_integral_tendsto (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (F : ℕ → Vector (n+1) → ℝ) (G : Vector (n+1) → ℝ)
    (hF : ∀ P,StronglyMeasurable (F P)) (C : ℝ≥0)
    (hC : ∀ P x,‖F P x‖≤C)
    (hlim : ∀ x,OnSphere x → Tendsto (fun P => F P x) atTop (𝓝 (G x))) :
    Tendsto (fun P => ∫ x,Real.exp (β*partialField μ P J x)*F P x ∂sphereLaw (n+1))
      atTop (𝓝 (∫ x,Real.exp (β*regularAmbientField n μ J x)*G x ∂sphereLaw (n+1))) := by
  letI := sphereLaw_probability (n+1)
  apply tendsto_integral_of_dominated_convergence
    (fun _ => Real.exp (|β| * fullJetEnvelope μ 0 J)*(C : ℝ))
  · intro P
    exact ((Real.continuous_exp.comp ((partialField_contDiff μ P J).continuous.const_mul β)).stronglyMeasurable.mul
      (hF P)).aestronglyMeasurable
  · exact integrable_const _
  · intro P
    filter_upwards [sphereLaw_support (show 1≤n+1 by omega)] with x hx
    have hs := (onSphere_iff_norm_sq x).mpr hx
    rw [norm_mul,Real.norm_of_nonneg (Real.exp_nonneg _)]
    apply mul_le_mul
    · apply Real.exp_le_exp.mpr
      calc
        β*partialField μ P J x ≤ |β*partialField μ P J x| := le_abs_self _
        _ = |β| * ‖partialField μ P J x‖ := by rw [abs_mul,Real.norm_eq_abs]
        _ ≤ |β| * fullJetEnvelope μ 0 J :=
          mul_le_mul_of_nonneg_left (partialField_norm_le_fullJetEnvelope (by omega) μ J hJ P x hs)
            (abs_nonneg β)
    · exact hC P x
    · exact norm_nonneg _
    · exact Real.exp_nonneg _
  · filter_upwards [sphereLaw_support (show 1≤n+1 by omega)] with x hx
    have hs := (onSphere_iff_norm_sq x).mpr hx
    rw [regularAmbientField_restrict n μ J hJ x hx]
    exact ((Real.continuous_exp.tendsto _).comp
      ((partialField_tendsto_onSphere (by omega) μ J hJ x hs).const_mul β)).mul (hlim x hs)

/-- Compact C² stationarity is proved from finite cutoff stationarity and
the actual terminal-state convergence, under the original infinite Gibbs law. -/
theorem compact_infiniteExpectation_stationary (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ)
    (t : ℝ≥0) (f : Vector (n+1) → ℝ) (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (∫ x,infiniteExpectation n μ J β t f x ∂gibbsLaw (n+1) β (field μ J))=
      ∫ x,f x ∂gibbsLaw (n+1) β (field μ J) := by
  obtain ⟨C0,hC0⟩ := hfc.exists_bound_of_continuous hf.continuous
  let C : ℝ≥0 := ⟨max C0 0,le_max_right _ _⟩
  have hC : ∀ x,‖f x‖≤C := fun x => (hC0 x).trans (le_max_left _ _)
  have hL := weighted_partial_integral_tendsto n μ J hJ β
    (fun P => partialExpectation μ J β P t f) (infiniteExpectation n μ J β t f)
    (fun P => SphericalC1Dynamics.expectation_stronglyMeasurable β _ _ t f hf.continuous.stronglyMeasurable)
    C (fun P x => SphericalC1Dynamics.expectation_norm_le β _ _ t f C hC x)
    (fun x hx => partial_expectation_tendsto n μ J hJ β x hx t f hf.continuous C hC)
  have hR := weighted_partial_integral_tendsto n μ J hJ β (fun _ => f) f
    (fun _ => hf.continuous.stronglyMeasurable) C (fun _ => hC) (fun _ _ => tendsto_const_nhds)
  have hp : ∃ p,0<μ.coeff p := by
    obtain ⟨p,hp⟩ := Function.ne_iff.mp μ.nonzero
    exact ⟨p,lt_of_le_of_ne (μ.nonneg p) (Ne.symm hp)⟩
  obtain ⟨p,hp⟩ := hp
  have he : (fun P => ∫ x,Real.exp (β*partialField μ P J x)*partialExpectation μ J β P t f x
      ∂sphereLaw (n+1)) =ᶠ[atTop]
      (fun P => ∫ x,Real.exp (β*partialField μ P J x)*f x ∂sphereLaw (n+1)) := by
    filter_upwards [eventually_ge_atTop p] with P hP
    exact partial_weighted_stationarity (by omega) μ J β P ⟨p,by omega,hp⟩ t f hf hfc
  have hw := tendsto_nhds_unique (hL.congr' he) hR
  rw [literal_gibbsLaw_eq_regular n μ β J hJ]
  apply mul_left_cancel₀ (partition_pos (show 1≤n+1 by omega) β
    (regularAmbientField_contDiff n μ J).continuous).ne'
  rw [partition_mul_integral_gibbs (by omega) β _ (regularAmbientField_contDiff n μ J).continuous,
    partition_mul_integral_gibbs (by omega) β _ (regularAmbientField_contDiff n μ J).continuous]
  exact hw

/-- The actual probability law after evolving independent literal Gibbs
initial data with the constructed infinite-field Brownian kernel. -/
def infiniteGibbsWaitingLaw (n : ℕ) (μ : InfiniteMixture) (J : Disorder (n+1))
    (β : ℝ) (t : ℝ≥0) : Measure (Vector (n+1)) :=
  infiniteTransitionKernel n μ J β t ∘ₘ gibbsLaw (n+1) β (field μ J)

theorem infiniteGibbsWaitingLaw_probability (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (t : ℝ≥0) :
    IsProbabilityMeasure (infiniteGibbsWaitingLaw n μ J β t) := by
  let := literal_gibbsLaw_probability n μ β J hJ
  unfold infiniteGibbsWaitingLaw
  infer_instance

theorem infiniteGibbsWaitingLaw_onSphere (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (t : ℝ≥0) :
    ∀ᵐ x ∂infiniteGibbsWaitingLaw n μ J β t,OnSphere x := by
  apply Measure.ae_comp_of_ae_ae (sphere_measurableSet (n+1))
  filter_upwards [gibbsLaw_support (show 1≤n+1 by omega) β (field μ J)] with x hx
  rw [infiniteTransitionKernel_law]
  exact (ae_map_iff (infiniteProcess_measurable n μ J β x t).aemeasurable
    (sphere_measurableSet (n+1))).2
    ((infiniteProcess_onSphere n μ J β x ((onSphere_iff_norm_sq x).mpr hx)).mono (fun _ h => h t))

theorem infiniteGibbsWaitingLaw_integral (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (t : ℝ≥0)
    (f : Vector (n+1) → ℝ) (hf : Continuous f) (hfc : HasCompactSupport f) :
    (∫ y,f y ∂infiniteGibbsWaitingLaw n μ J β t)=
      ∫ x,infiniteExpectation n μ J β t f x ∂gibbsLaw (n+1) β (field μ J) := by
  let := literal_gibbsLaw_probability n μ β J hJ
  let := infiniteGibbsWaitingLaw_probability n μ J hJ β t
  have hi : Integrable f (infiniteGibbsWaitingLaw n μ J β t) :=
    hf.integrable_of_hasCompactSupport hfc
  rw [infiniteGibbsWaitingLaw,Measure.comp_eq_comp_const_apply] at hi ⊢
  rw [Kernel.integral_comp hi,Kernel.const_apply]
  apply integral_congr_ae
  exact .of_forall (fun x => (SphericalC1Dynamics.expectation_eq_kernel β _ _ t f
    hf.stronglyMeasurable x).symm)

/-- Full literal Gibbs stationarity of the actual infinite-field SDE.
Both the kernel and invariant probability are the original constructed objects. -/
theorem infiniteTransitionKernel_gibbs_invariant (n : ℕ) (μ : InfiniteMixture)
    (J : Disorder (n+1)) (hJ : J∈summableJetDisorder μ) (β : ℝ) (t : ℝ≥0) :
    infiniteTransitionKernel n μ J β t ∘ₘ gibbsLaw (n+1) β (field μ J)=
      gibbsLaw (n+1) β (field μ J) := by
  let := literal_gibbsLaw_probability n μ β J hJ
  let := infiniteGibbsWaitingLaw_probability n μ J hJ β t
  change infiniteGibbsWaitingLaw n μ J β t=_
  apply SphereSmoothTestMeasureExt.measure_eq_of_compactC2_integrals
    (infiniteGibbsWaitingLaw_onSphere n μ J hJ β t)
    ((gibbsLaw_support (show 1≤n+1 by omega) β (field μ J)).mono
      (fun x hx => (onSphere_iff_norm_sq x).mpr hx))
  intro f hf hfc
  rw [infiniteGibbsWaitingLaw_integral n μ J hJ β t f hf.continuous hfc]
  exact compact_infiniteExpectation_stationary n μ J hJ β t f hf hfc

end SlowEquilibration.SphericalInfiniteModel
