-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntranceJointReducedEnergy
public import SlowEquilibration.ConditionedEntranceQuenchedTiltDefectSquare
public import SlowEquilibration.SphericalWeightedCrossAbsorption

/-! The mixed-source second tilt-defect moment projected onto the
literal frozen original-base Fisher density of the physical reference. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set Metric Topology
open SphericalAging HardSphereDynamics
open scoped NNReal BigOperators
namespace SlowEquilibration.ConditionedEntrance
open SphericalModel SphericalForm SmoothKilled
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

private theorem pair_integrable_mul_snd {N : ℕ} (hN : 1 ≤ N)
    (β : ℝ) (H : Vector N → ℝ) (hH : Continuous H)
    {f : Vector N × Vector N → ℝ} (hf : Continuous f)
    {Γ : Vector N → ℝ} (hΓ : Integrable Γ (gibbsLaw N β H)) :
    Integrable (fun z => f z * Γ z.2)
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
    (isCompact_closedBall (0 : Vector N) (Real.sqrt N))).exists_bound_of_continuousOn hf.continuousOn
  apply (hΓ.comp_snd (sphereLaw N)).bdd_mul hf.aestronglyMeasurable
  filter_upwards [hs] with z hz
  apply hC
  constructor
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.1,Real.sqrt_sq (norm_nonneg z.1)]
  · simp only [mem_closedBall,dist_zero_right]
    rw [← hz.2,Real.sqrt_sq (norm_nonneg z.2)]

/-- The source second moment projects onto the actual original-base
Sobolev Fisher density. `F₀` and its rotation gradients come from the
physical joint reference construction, and the source Gibbs tilt has one
global axis–spin normalizer. -/
theorem actual_mixedSource_globalTilt_fisherDefectSquare_eventually_le
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
      ∀ (u : Vector (n+1)) (hu : OnSphere u),
      ∀ (θr : ℝ≥0), 0 < θr →
        let p : SourceParameters (n+1) μ := (J,(u,(e,k)))
        let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
          μ hnp Q hQ hQ1 α hα χ hχ p hu
        let H₀ := fieldOfMixture μ J
        let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
          β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
        let M := ∫ z, Real.exp (w z)
          ∂((sphereLaw (n+1)).prod (gibbsLaw (n+1) β H₀))
        ∃ F : SourceParameters (n+1) μ × Vector (n+1) → ℝ,
          ∃ GF : (Fin (n+1) × Fin (n+1)) →
              SourceParameters (n+1) μ × Vector (n+1) → ℝ,
          ∃ F₀ : sphericalSobolevGraph (by omega : 1 ≤ n+1) β
              D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous,
            sphericalEnergyL2Map (by omega : 1 ≤ n+1) β
              D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous F₀ =
                referenceRate D.baseData β θr (referenceInitialVector D.baseData β) ∧
            ((fun x => F (p,x)) =ᵐ[gibbsLaw (n+1) β D.baseData.hamiltonian]
              F₀.val.fst) ∧
            (∀ ij, (fun x => GF ij (p,x)) =ᵐ[
              gibbsLaw (n+1) β D.baseData.hamiltonian] F₀.val.snd ij) ∧
            (∫ z, (tiltDefect w z)^2 *
                (∑ ij : Fin (n+1) × Fin (n+1),
                  (GF ij (p,z.2))^2 / F (p,z.2))
              ∂normalizedTilt ((sphereLaw (n+1)).prod
                (gibbsLaw (n+1) β H₀)) w M) ≤
              2 * (C * ((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))) *
                sphericalFisher (by omega : 1 ≤ n+1) β
                  D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous F₀ := by
  obtain ⟨C,hC,hMom⟩ :=
    EntranceLatitudeTangentObservable.actual_sourceSmoothCutoffField_tilt_moments
      μ hd hQ hnp hB hβ
  have hSmall := sourceTilt_eta_eventually_half μ.minDegree hd C
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom,hSmall] with n hn hs
  intro J hJ α hα hαsmall χ hχ hχb hχR e k he hk u hu θr hθr
  dsimp only
  let p : SourceParameters (n+1) μ := (J,(u,(e,k)))
  let D := SourceData.atSourceParameters (by omega : 1 ≤ n+1)
    μ hnp Q hQ hQ1 α hα χ hχ p hu
  let H₀ := fieldOfMixture μ J
  let w : Vector (n+1) × Vector (n+1) → ℝ := fun z =>
    β * (sourceSmoothCutoffField μ Q hQ hnp J z.1 e k α χ z.2 - H₀ z.2)
  let π := gibbsLaw (n+1) β H₀
  let ν := (sphereLaw (n+1)).prod π
  let M := ∫ z, Real.exp (w z) ∂ν
  have hN : 1 ≤ n+1 := by omega
  have hJreg : J ∈ regularDisorder := hJ.1
  obtain ⟨F,GF,U,G,hF,hGF,hU,hG,hFf,hGFf,hB,hA,hK,hR,hCross,hJF,hE⟩ :=
    sourceJointReferenceReducedEnergy hN μ hnp Q hQ hQ1 α hα χ hχ β hβ θr hθr
  obtain ⟨hFs,hUs,hFb,hUb,hFisher,hEnergy,hGraph⟩ := hE p hu hJreg
  obtain ⟨F₀,F₁,v,hF₀,hv,hFF₀,hGF₀,hFF₁,hGF₁,hUv,hGv⟩ := hGraph
  refine ⟨F,GF,F₀,hF₀,hFF₀,hGF₀,?_⟩
  have hπ : π = gibbsLaw (n+1) β D.baseData.hamiltonian := by
    simp only [π,H₀,D,p,SourceData.baseData_hamiltonian,
      SourceData.atSourceParameters]
  have hAC : ae π ≤ ae (gibbsLaw (n+1) β D.hamiltonian) := by
    rw [hπ]
    exact (gibbsLaw_absolutelyContinuous_gibbsLaw hN β β
      D.hamiltonian D.baseData.hamiltonian D.hamiltonian_contDiff.continuous).ae_le
  have hFbase : ∀ᵐ x ∂π, 1 ≤ F (p,x) := by
    exact (hFb.mono (fun _ hx => hx.1)).filter_mono hAC
  have hFlo : ∀ᵐ x ∂π, 1 ≤ F₀.val.fst x := by
    filter_upwards [hFbase,show (fun x => F (p,x)) =ᵐ[π] F₀.val.fst by
      simpa only [hπ] using hFF₀] with x hf hx
    simpa only [hx] using hf
  have hFloD : ∀ᵐ x ∂gibbsLaw (n+1) β D.baseData.hamiltonian,
      1 ≤ F₀.val.fst x := by
    simpa only [hπ] using hFlo
  have hFFπ : (fun x => F (p,x)) =ᵐ[π] F₀.val.fst := by
    simpa only [hπ] using hFF₀
  have hGFπ (ij : Fin (n+1) × Fin (n+1)) :
      (fun x => GF ij (p,x)) =ᵐ[π] F₀.val.snd ij := by
    simpa only [hπ] using hGF₀ ij
  have hCoordAe (ij : Fin (n+1) × Fin (n+1)) :
      (fun x => (GF ij (p,x))^2 / F (p,x)) =ᵐ[π]
        (fun x => (F₀.val.snd ij x)^2 * (F₀.val.fst x)⁻¹) := by
    filter_upwards [hFFπ,hGFπ ij] with x hf hg
    simp only [hf,hg,div_eq_mul_inv]
  have hCoordInt (ij : Fin (n+1) × Fin (n+1)) :
      Integrable (fun x => (GF ij (p,x))^2 / F (p,x)) π := by
    have hi := sphericalFisher_coordinate_integrable hN β
      D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous F₀ hFloD ij
    rw [hπ]
    exact hi.congr (by simpa only [hπ] using (hCoordAe ij).symm)
  let Γ : Vector (n+1) → ℝ := fun x =>
    ∑ ij : Fin (n+1) × Fin (n+1), (GF ij (p,x))^2 / F (p,x)
  have hΓ : Integrable Γ π := by
    exact integrable_finsetSum Finset.univ (fun ij _ => hCoordInt ij)
  have hΓpos : ∀ᵐ x ∂π, 0 ≤ Γ x := by
    filter_upwards [hFbase] with x hx
    exact Finset.sum_nonneg (fun ij _ => div_nonneg (sq_nonneg _) (by linarith))
  have hΓmass : (∫ x, Γ x ∂π) = sphericalFisher hN β
      D.baseData.hamiltonian D.baseData.hamiltonian_contDiff.continuous F₀ := by
    calc
      _ = ∑ ij : Fin (n+1) × Fin (n+1),
          ∫ x, (GF ij (p,x))^2 / F (p,x) ∂π := by
            simpa only [Γ] using
              integral_finsetSum Finset.univ (fun ij _ => hCoordInt ij)
      _ = ∑ ij : Fin (n+1) × Fin (n+1),
          ∫ x, (F₀.val.snd ij x)^2 * (F₀.val.fst x)⁻¹ ∂π := by
            apply Finset.sum_congr rfl
            intro ij _
            exact integral_congr_ae (hCoordAe ij)
      _ = _ := by rw [hπ]; rfl
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
      (∫ v, |Real.exp (w (v,x))-1| ∂sphereLaw (n+1)) ≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) := by
    filter_upwards [gibbsLaw_support hN β H₀] with x hx
    exact (hn J hJ x hx α hα hαsmall χ hχ hχb hχR e k he hk).1
  have hεaxis : ∀ᵐ x ∂π,
      (∫ v, Real.exp (w (v,x)) * (tiltDefect w (v,x))^2
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
      (tiltDefect w z)^2 * Γ z.2) ν :=
    pair_integrable_mul_snd hN β H₀ hH₀ hkcont hΓ
  have h := tiltDefect_square_projection (sphereLaw (n+1)) π w hw.measurable
    hM hε Γ hΓ hΓpos hik hεaxis
  rw [hΓmass] at h
  simpa only [Γ,ν,π,M] using h

end SlowEquilibration.ConditionedEntrance
