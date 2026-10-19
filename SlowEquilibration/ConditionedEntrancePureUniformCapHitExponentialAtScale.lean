-- SPDX-License-Identifier: Apache-2.0
module
public import SlowEquilibration.ConditionedEntrancePureUniformCapHitAtScale
public import SlowEquilibration.ConditionedEntranceSourceHorizonGridNumeric

/-! The mixed conditioned source's genuine physical cap-hit probability has
an explicit polynomial-plus-exponential bound at one exponential horizon,
averaged over spherical axes and uniform initial spins on the original
latitude-good tensor event. -/
@[expose] public section
noncomputable section
open MeasureTheory ProbabilityTheory Filter
open SlowEquilibration.SphericalModel SlowEquilibration.SphericalForm
open SlowEquilibration.SphericalOverlapExponential
open SphericalAging.HardSphereDynamics
open scoped NNReal
namespace SlowEquilibration.ConditionedEntrance
open SmoothKilledGeneral PhysicalHitting
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem actual_pureSource_uniform_cap_hit_exponential_horizon_at_scale
    (d : ℕ) (hd : 4 ≤ d) (c : ℝ) (hc : 0 < c)
    {Q B β : ℝ} (hQ : 0 < Q) (hB : 0 ≤ B) (hβ : 0 ≤ β)
    {α : ℝ} (hα : 0<α)
    (hαmoment : α≤EntranceLatitudeTangentObservable.sourceCutoffMomentScale (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) Q B (2*β))
    (hαenergy : α≤1/(128*(1+β*
      pureCutoffEnergyConstant d (by omega) c hc Q B)))
    (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s,|χ s|≤1) (hχR : ∀ s,2 < |s|→χ s=0) :
    ∃ (γ Cε Cη Ccap : ℝ),
      0<γ ∧ 0<Cε ∧ 0<Cη ∧ 0<Ccap ∧
      let T := pureSourceShortCell d (by omega) c hc Q B α β hB hα hβ χ hχ
      let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
      0<c₀ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) (FiniteMixture.pure d (by omega : 2 ≤ d) c hc).maxDegree), J∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n (FiniteMixture.pure d (by omega : 2 ≤ d) c hc) →
      ∀ (e : ℝ), |e|≤B →
      let H := exponentialGridHorizon γ (n+1)
      let ε := Cε*((n+1 : ℕ) : ℝ)^(2-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ))
      let η := Cη*((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))*((n+1 : ℕ) : ℝ)
      (∫ u,pureSourceCapHitProbability d (by omega) c hc Q α χ hχ β H
        (J,(u,(e,0))) ∂sphereLaw (n+1)) ≤
      (2/(T : ℝ)+4)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256)+
        (4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
          8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256))/c₀ := by
  obtain ⟨γ₀,Cε,Cη,Ccap,hγ₀,hCε,hCη,hCcap,hEvent⟩ :=
    actual_pureSource_uniform_cap_hit_at_scale d hd c hc hQ hB hβ
      hα hαmoment hαenergy
  let γ := min γ₀ (α^2/256)
  have hγ : 0<γ := lt_min hγ₀ (by positivity)
  have hγα : γ≤α^2/256 := min_le_right _ _
  have hγold : γ≤γ₀ := min_le_left _ _
  let T := pureSourceShortCell d (by omega) c hc Q B α β hB hα hβ χ hχ
  have hT : 0<T := pureSourceShortCell_pos d (by omega) c hc Q B α β hB hα hβ χ hχ
  have hT18 : (T : ℝ)≤1/18 := pureSourceShortCell_le_eighteenth d (by omega) c hc Q B α β hB hα hβ χ hχ
  have hT1 : (T : ℝ)≤1 := by linarith
  let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
  have hc₀ : 0<c₀ := (source_exponential_exposure_floor γ hγ.le 0 T hT hT1).1
  refine ⟨γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,?_⟩
  dsimp only
  refine ⟨hc₀,?_⟩
  filter_upwards [hEvent] with n hn
  intro J hJ e he
  let H := exponentialGridHorizon γ (n+1)
  let θ := sourceExponentialDiscount γ (n+1)
  let ε := Cε*((n+1 : ℕ) : ℝ)^(2-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ))
  let η := Cη*((n+1 : ℕ) : ℝ)^(1-((FiniteMixture.pure d (by omega : 2 ≤ d) c hc).minDegree : ℝ)/2)
  let Hf := 2*Real.log 2+
    4*β*derivativeConstant (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))*((n+1 : ℕ) : ℝ)
  let P : ℝ := ∫ u,pureSourceCapHitProbability d (by omega) c hc Q α χ hχ β H
    (J,(u,(e,0))) ∂sphereLaw (n+1)
  let E : ℝ := (gridSize H T : ℝ)*
    (2*Real.exp (-((n+1 : ℕ) : ℝ)*(α/12)^2/(16*(T : ℝ))))
  let R : ℝ := 4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
    8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256)
  have hθ : 0<θ := sourceExponentialDiscount_pos γ (n+1)
  have hrate : Real.exp (-γ₀*((n+1 : ℕ) : ℝ))≤(θ : ℝ) := by
    change Real.exp (-γ₀*((n+1 : ℕ) : ℝ))≤
      Real.exp (-γ*((n+1 : ℕ) : ℝ))
    apply Real.exp_le_exp.mpr
    nlinarith [mul_nonneg (Nat.cast_nonneg (n+1 : ℕ))
      (sub_nonneg.mpr hγold)]
  have hExposure := hn J hJ χ hχ hχb hχR e he θ hθ hrate H
  change exposureFactor (θ : ℝ) H T*(P-E)≤R at hExposure
  have hFloor := (source_exponential_exposure_floor γ hγ.le (n+1) T hT hT1).2
  change c₀≤exposureFactor (θ : ℝ) H T at hFloor
  have hε : 0≤ε := by dsimp only [ε]; positivity
  have hη : 0≤η := by dsimp only [η]; positivity
  have hHf : 0≤Hf := by
    have hdpos := (derivativeConstant_pos (mixtureCoefficients (FiniteMixture.pure d (by omega : 2 ≤ d) c hc))).le
    have hl : 0≤Real.log 2 := Real.log_nonneg (by norm_num)
    dsimp only [Hf]
    positivity
  have hR : 0≤R := by dsimp only [R]; positivity
  have hP := source_exposure_to_probability hc₀ hFloor hR hExposure
  have hE := source_exponential_grid_error_le γ α hγ.le hγα (n+1) T hT hT18
  change E≤(2/(T : ℝ)+4)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256) at hE
  change P≤_
  exact hP.trans (add_le_add_left hE (R/c₀))

end SlowEquilibration.ConditionedEntrance
