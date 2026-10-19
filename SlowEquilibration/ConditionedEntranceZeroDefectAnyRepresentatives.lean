-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceFisherDefectAnyRepresentatives
public import SlowEquilibration.ConditionedEntranceSourceReferenceMassTwo

/-! The zero-order source commutator has the sharp `F-1` second moment
for any frozen-axis representative of the literal base reference. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
open SphericalAging.HardSphereDynamics
set_option autoImplicit false
set_option maxHeartbeats 600000

private theorem pair_integrable_mul_snd {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    {g : Vector N × Vector N → ℝ} (hg : Continuous g)
    {Γ : Vector N → ℝ} (hΓ : Integrable Γ (gibbsLaw N β H)) :
    Integrable (fun z => g z * Γ z.2)
      ((sphereLaw N).prod (gibbsLaw N β H)) := by
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
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn
      hg.continuousOn
  apply (hΓ.comp_snd (sphereLaw N)).bdd_mul hg.aestronglyMeasurable
  filter_upwards [hs] with z hz
  apply hC
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]

theorem zero_defect_projection_any_frozen_representative
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (w : Vector N × Vector N → ℝ)
    (hw : Continuous w) (M : ℝ) (hM : 1/2 ≤ M)
    (F : Vector N × Vector N → ℝ)
    (hFrozenF : ∀ u v x, F (u,x) = F (v,x))
    (hFint : Integrable (fun x => F (0,x)) (gibbsLaw N β H))
    (hFlo : ∀ᵐ x ∂gibbsLaw N β H, 1 ≤ F (0,x))
    (hFmass : (∫ x, F (0,x) ∂gibbsLaw N β H) = 2)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hεaxis : ∀ᵐ x ∂gibbsLaw N β H,
      (∫ u, Real.exp (w (u,x)) * (tiltDefect w (u,x))^2
        ∂sphereLaw N) ≤ ε) :
    (∫ z, (tiltDefect w z)^2 * (F z - 1)
      ∂normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤
      2 * ε := by
  let π := gibbsLaw N β H
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH
  let Γ : Vector N → ℝ := fun x => F (0,x)-1
  have hΓ : Integrable Γ π := hFint.sub (integrable_const 1)
  have hΓpos : ∀ᵐ x ∂π, 0 ≤ Γ x := hFlo.mono (fun _ hx => by dsimp only [Γ]; linarith)
  have hΓmass : (∫ x, Γ x ∂π) = 1 := by
    rw [show (∫ x, Γ x ∂π) =
      (∫ x, F (0,x) ∂π) - (∫ _ : Vector N, (1 : ℝ) ∂π) from
      integral_sub hFint (integrable_const _)]
    simp only [integral_const,probReal_univ,one_smul]
    change (∫ x, F (0,x) ∂gibbsLaw N β H) - 1 = 1
    rw [hFmass]
    norm_num
  have hkg : Continuous (fun z : Vector N × Vector N =>
      Real.exp (w z) * (tiltDefect w z)^2) := by
    unfold tiltDefect
    fun_prop
  have hweighted : Integrable (fun z : Vector N × Vector N =>
      Real.exp (w z) * (tiltDefect w z)^2 * Γ z.2)
      ((sphereLaw N).prod π) :=
    pair_integrable_mul_snd hN β H hH hkg hΓ
  have h := tiltDefect_square_projection (sphereLaw N) π w hw.measurable hM hε
    Γ hΓ hΓpos hweighted hεaxis
  rw [hΓmass] at h
  have hident (z : Vector N × Vector N) : F z - 1 = Γ z.2 := by
    exact congrArg (· - 1) (hFrozenF z.1 0 z.2)
  simpa only [hident,mul_one] using h

/-- Source second-moment estimate for the exact `F-1` zero-order
commutator. The supplied representative is the one used by the physical
energy theorem; the mass-two identity belongs to the base resolvent. -/
theorem actual_mixedSource_zeroDefectSquare_any_representative_eventually_le
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q) (hQ1 : Q ≤ 1)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J ∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (α : ℝ) (hα : 0 < α),
        α ≤ EntranceLatitudeTangentObservable.sourceCutoffMomentScale μ Q B (2*β) →
      ∀ (χ : ℝ → ℝ) (hχ : ContDiff ℝ 2 χ),
        (∀ s, |χ s| ≤ 1) → (∀ s, 2 < |s| → χ s = 0) →
      ∀ (e k : ℝ), |e| ≤ B → |k| ≤ B →
      let H₀ := fieldOfMixture μ J
      let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
        β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
      let π := gibbsLaw (n+1) β H₀
      let M := ∫ z, Real.exp (w z) ∂((sphereLaw (n+1)).prod π)
      ∀ (u : Vector (n+1)) (hu : OnSphere u)
        (θr : ℝ≥0) (hθr : 0 < θr),
      let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
        μ hnp Q hQ hQ1 α hα χ hχ (J,(u,(e,k))) hu
      ∀ (F : Vector (n+1) × Vector (n+1) → ℝ),
        (∀ a b x, F (a,x) = F (b,x)) →
        (fun x => F (0,x)) =ᵐ[π] sourceReferencePositivePart D β θr →
        (∀ᵐ x ∂π, 1 ≤ F (0,x)) →
        (∫ z, (tiltDefect w z)^2 * (F z - 1)
          ∂normalizedTilt ((sphereLaw (n+1)).prod π) w M) ≤
          2 * (C * ((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))) := by
  obtain ⟨C,hC,hMom⟩ :=
    EntranceLatitudeTangentObservable.actual_sourceSmoothCutoffField_tilt_moments
      μ hd hQ hnp hB hβ
  have hSmall := sourceTilt_eta_eventually_half μ.minDegree hd C
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom,hSmall] with n hn hs
  intro J hJ α hα hαsmall χ hχ hχb hχR e k he hk
  dsimp only
  let H₀ := fieldOfMixture μ J
  let π := gibbsLaw (n+1) β H₀
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
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
  have heexp : Integrable (fun z => Real.exp (w z)) ν := by
    simpa only [mul_one] using
      pair_integrable_mul_snd hN β H₀ hH₀ hw.rexp
        (integrable_const (μ := π) (1 : ℝ))
  have hηaxis : ∀ᵐ x ∂π,
      (∫ a, |Real.exp (w (a,x))-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    exact (hn J hJ x hx α hα hαsmall χ hχ hχb hχR e k he hk).1
  have hεaxis : ∀ᵐ x ∂π,
      (∫ a, Real.exp (w (a,x)) * (tiltDefect w (a,x))^2
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
  have hε : 0 ≤ C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by positivity
  intro u hu θr hθr
  let D := SourceData.atSourceParameters hN μ hnp Q hQ hQ1 α hα χ hχ
    (J,(u,(e,k))) hu
  intro F hFrozenF hFrep hFlo
  have hπ : π = gibbsLaw (n+1) β D.baseData.hamiltonian := by
    simp only [π,H₀,D,SourceData.baseData_hamiltonian,
      SourceData.atSourceParameters]
  have hFrep' : (fun x => F (0,x)) =ᵐ[π]
      sourceReferencePositivePart D β θr := hFrep
  have hFint : Integrable (fun x => F (0,x)) π := by
    rw [hπ]
    exact (sourceReferencePositivePart_integrable D β θr).congr
      (by simpa only [hπ] using hFrep'.symm)
  have hFmass : (∫ x, F (0,x) ∂π) = 2 := by
    rw [integral_congr_ae hFrep',hπ]
    exact sourceReferencePositivePart_mass_two D β θr hθr
  exact zero_defect_projection_any_frozen_representative hN β H₀ hH₀
    w hw M hM F hFrozenF hFint hFlo hFmass hε hεaxis

end SlowEquilibration.ConditionedEntrance
