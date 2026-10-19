-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceActualSourceGlobalTilt
public import SlowEquilibration.ConditionedEntranceTiltCommutator

/-! The manuscript's genuine second tilt-defect moment under the single
globally normalized mixed-source axis–spin law. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open SphericalAging HardSphereDynamics
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem pair_integrable {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    {f : Vector N × Vector N → ℝ} (hf : Continuous f) :
    Integrable f ((sphereLaw N).prod (gibbsLaw N β H)) := by
  let : IsProbabilityMeasure (sphereLaw N) := sphereLaw_probability N
  let : IsProbabilityMeasure (gibbsLaw N β H) := gibbsLaw_probability hN β hH
  have hs : ∀ᵐ z : Vector N × Vector N
      ∂(sphereLaw N).prod (gibbsLaw N β H),
      ‖z.1‖^2 = (N : ℝ) ∧ ‖z.2‖^2 = (N : ℝ) := by
    apply (Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [sphereLaw_support hN] with u hu
    filter_upwards [gibbsLaw_support hN β H] with x hx
    exact ⟨hu,hx⟩
  obtain ⟨C,hC⟩ := ((isCompact_closedBall (0 : Vector N) (Real.sqrt N)).prod
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn hf.continuousOn
  apply Integrable.of_bound hf.aestronglyMeasurable C
  filter_upwards [hs] with z hz
  apply hC
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]

/-- For every latitude-good original disorder, the normalized physical
source reverse-density defect has the literal `2 ε` bound of the
entropy–resolvent comparison. The constant is chosen before dimension,
cutoff, marks and axis. -/
theorem actual_mixedSource_globalTilt_defectSquare_eventually_le
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (α : ℝ), 0 < α →
        α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β) →
      ∀ (χ : ℝ → ℝ), ContDiff ℝ 2 χ →
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
      let H₀ := fieldOfMixture μ J
      let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
        β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
      let M := ∫ z, Real.exp (w z)
        ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
      (∫ z, (tiltDefect w z)^2
        ∂normalizedTilt ((sphereLaw (n+1)).prod
          (gibbsLaw (n+1) β H₀)) w M) ≤
        2 * C * ((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by
  obtain ⟨C,hC,hMom⟩ :=
    EntranceLatitudeTangentObservable.actual_sourceSmoothCutoffField_tilt_moments
      μ hd hQ hnp hB hβ
  have hSmall := sourceTilt_eta_eventually_half μ.minDegree hd C
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom,hSmall] with n hn hs
  intro J hJ α hα hαsmall χ hχ hχb hχR e k he hk
  dsimp only
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
  let π := gibbsLaw (n+1) β H₀
  let ν := (sphereLaw (n+1)).prod π
  let M := ∫ z, Real.exp (w z) ∂ν
  have hN : 1 ≤ n+1 := by omega
  have hH₀ : Continuous H₀ := (fieldOfMixture_contDiff μ J).continuous
  let : IsProbabilityMeasure (sphereLaw (n+1)) := sphereLaw_probability (n+1)
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH₀
  have hH : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2) :=
    (sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun z : Vector (n+1) × Vector (n+1) =>
        ((J,(z.1,(e,k))),z.2)) by fun_prop)
  have hw : Continuous w := (hH.sub (hH₀.comp continuous_snd)).const_mul β
  have heexp : Integrable (fun z => Real.exp (w z)) ν :=
    pair_integrable hN β H₀ hH₀ hw.rexp
  have hηaxis : ∀ᵐ x ∂π,
      (∫ u, |Real.exp (w (u,x))-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    exact (hn J hJ x hx α hα hαsmall χ hχ hχb hχR e k he hk).1
  have hεaxis : ∀ᵐ x ∂π,
      (∫ u, Real.exp (w (u,x)) * (tiltDefect w (u,x))^2
        ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    simpa only [tiltDefect,w,H₀,neg_mul] using
      (hn J hJ x hx α hα hαsmall χ hχ hχb hχR e k he hk).2
  have hMclose : |M-1| ≤ C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) :=
    exponential_mass_close_one (sphereLaw (n+1)) π w heexp rfl hηaxis
  have hM : 1/2 ≤ M := by
    have hl := (abs_le.mp hMclose).1
    linarith
  have hε : 0 ≤ C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by
    positivity
  have hkcont : Continuous (fun z : Vector (n+1) × Vector (n+1) =>
      Real.exp (w z) * (tiltDefect w z)^2) := by
    unfold tiltDefect
    fun_prop
  have hik : Integrable (fun z => Real.exp (w z) *
      (tiltDefect w z)^2 * (1 : ℝ)) ν := by
    simpa only [mul_one] using
      pair_integrable hN β H₀ hH₀ hkcont
  have h := tiltDefect_square_projection (sphereLaw (n+1)) π w hw.measurable
    hM hε (fun _ => (1 : ℝ)) (integrable_const 1)
    (Filter.Eventually.of_forall (fun _ => by norm_num)) hik hεaxis
  change (∫ z, (tiltDefect w z)^2 ∂normalizedTilt ν w M) ≤ _
  simpa only [integral_const, probReal_univ, one_smul, mul_one, mul_assoc] using h

end SlowEquilibration.ConditionedEntrance
