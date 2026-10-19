-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceQuenchedFisherDefectSquare

/-! The source Fisher-defect projection is independent of how the joint
completed Sobolev representative was selected. This lets the exact same
representative feed the raw physical energy equation and the second
moment bound. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Set Metric Topology
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm
set_option autoImplicit false
set_option maxHeartbeats 500000

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

theorem fisher_defect_projection_any_frozen_representatives
    {N : ℕ} (hN : 1 ≤ N) (β : ℝ) (H : Vector N → ℝ)
    (hH : Continuous H) (w : Vector N × Vector N → ℝ)
    (hw : Continuous w) (M : ℝ) (hM : 1/2 ≤ M)
    (F : Vector N × Vector N → ℝ)
    (GF : (Fin N × Fin N) → Vector N × Vector N → ℝ)
    (hFrozenF : ∀ u v x, F (u,x) = F (v,x))
    (hFrozenGF : ∀ ij u v x, GF ij (u,x) = GF ij (v,x))
    (F₀ : sphericalSobolevGraph hN β H hH)
    (hF : (fun x => F (0,x)) =ᵐ[gibbsLaw N β H] F₀.val.fst)
    (hGF : ∀ ij, (fun x => GF ij (0,x)) =ᵐ[gibbsLaw N β H] F₀.val.snd ij)
    (hFlo : ∀ᵐ x ∂gibbsLaw N β H, 1 ≤ F₀.val.fst x)
    {ε : ℝ} (hε : 0 ≤ ε)
    (hεaxis : ∀ᵐ x ∂gibbsLaw N β H,
      (∫ u, Real.exp (w (u,x)) * (tiltDefect w (u,x))^2
        ∂sphereLaw N) ≤ ε) :
    (∫ z, (tiltDefect w z)^2 *
      (∑ ij : Fin N × Fin N, (GF ij z)^2 / F z)
      ∂normalizedTilt ((sphereLaw N).prod (gibbsLaw N β H)) w M) ≤
      2 * ε * sphericalFisher hN β H hH F₀ := by
  let π := gibbsLaw N β H
  let : IsProbabilityMeasure π := gibbsLaw_probability hN β hH
  let Γ : Vector N → ℝ := fun x =>
    ∑ ij : Fin N × Fin N, (GF ij (0,x))^2 / F (0,x)
  have hF0 : ∀ᵐ x ∂π, 1 ≤ F (0,x) := by
    filter_upwards [hFlo,hF] with x hf he
    simpa only [he] using hf
  have hCoordAe (ij : Fin N × Fin N) :
      (fun x => (GF ij (0,x))^2 / F (0,x)) =ᵐ[π]
        (fun x => (F₀.val.snd ij x)^2 * (F₀.val.fst x)⁻¹) := by
    filter_upwards [hF,hGF ij] with x hf hg
    simp only [hf,hg,div_eq_mul_inv]
  have hCoordInt (ij : Fin N × Fin N) :
      Integrable (fun x => (GF ij (0,x))^2 / F (0,x)) π := by
    exact (sphericalFisher_coordinate_integrable hN β H hH F₀ hFlo ij).congr
      (hCoordAe ij).symm
  have hΓ : Integrable Γ π :=
    integrable_finsetSum Finset.univ (fun ij _ => hCoordInt ij)
  have hΓpos : ∀ᵐ x ∂π, 0 ≤ Γ x := by
    filter_upwards [hF0] with x hx
    exact Finset.sum_nonneg (fun ij _ => div_nonneg (sq_nonneg _) (by linarith))
  have hΓmass : (∫ x, Γ x ∂π) = sphericalFisher hN β H hH F₀ := by
    calc
      _ = ∑ ij : Fin N × Fin N,
          ∫ x, (GF ij (0,x))^2 / F (0,x) ∂π := by
            simpa only [Γ] using
              integral_finsetSum Finset.univ (fun ij _ => hCoordInt ij)
      _ = ∑ ij : Fin N × Fin N,
          ∫ x, (F₀.val.snd ij x)^2 * (F₀.val.fst x)⁻¹ ∂π := by
            apply Finset.sum_congr rfl
            intro ij _
            exact integral_congr_ae (hCoordAe ij)
      _ = _ := rfl
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
  have hident (z : Vector N × Vector N) :
      (∑ ij : Fin N × Fin N, (GF ij z)^2 / F z) = Γ z.2 := by
    dsimp only [Γ]
    apply Finset.sum_congr rfl
    intro ij _
    rw [hFrozenGF ij z.1 0 z.2, hFrozenF z.1 0 z.2]
  simpa only [hident] using h

/-- The manuscript's second source-tilt moment controls the Fisher
commutator for every jointly measurable completed reference representative
that is frozen in the axis. The representative is supplied by the physical
energy construction, so no separate existential choice is needed. -/
theorem actual_mixedSource_fisherDefectSquare_any_representatives_eventually_le
    (μ : FiniteMixture) (hd : 4 ≤ μ.minDegree)
    {Q B β : ℝ} (hQ : 0 < Q)
    (hnp : μ.minDegree < μ.maxDegree) (hB : 0 ≤ B) (hβ : 0 ≤ β) :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ n : ℕ in Filter.atTop,
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
      let π := gibbsLaw (n+1) β H₀
      let M := ∫ z, Real.exp (w z) ∂((sphereLaw (n+1)).prod π)
      ∀ (F : Vector (n+1) × Vector (n+1) → ℝ)
        (GF : (Fin (n+1) × Fin (n+1)) →
          Vector (n+1) × Vector (n+1) → ℝ),
        (∀ u v x, F (u,x) = F (v,x)) →
        (∀ ij u v x, GF ij (u,x) = GF ij (v,x)) →
      ∀ (F₀ : sphericalSobolevGraph (by omega : 1 ≤ n+1) β H₀
        (fieldOfMixture_contDiff μ J).continuous),
        (fun x => F (0,x)) =ᵐ[π] F₀.val.fst →
        (∀ ij, (fun x => GF ij (0,x)) =ᵐ[π] F₀.val.snd ij) →
        (∀ᵐ x ∂π, 1 ≤ F₀.val.fst x) →
        (∫ z, (tiltDefect w z)^2 *
            (∑ ij : Fin (n+1) × Fin (n+1), (GF ij z)^2 / F z)
          ∂normalizedTilt ((sphereLaw (n+1)).prod π) w M) ≤
          2 * (C * ((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))) *
            sphericalFisher (by omega : 1 ≤ n+1) β H₀
              (fieldOfMixture_contDiff μ J).continuous F₀ := by
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
  have hε : 0 ≤ C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by positivity
  intro F GF hFrozenF hFrozenGF F₀ hF hGF hFlo
  exact fisher_defect_projection_any_frozen_representatives hN β H₀ hH₀ w hw
    M hM F GF hFrozenF hFrozenGF F₀ hF hGF hFlo hε hεaxis

end SlowEquilibration.ConditionedEntrance
