-- SPDX-License-Identifier: Apache-2.0
module
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
open SmoothKilled PhysicalHitting
set_option autoImplicit false
set_option maxHeartbeats 900000

theorem actual_mixedSource_uniform_cap_hit_exponential_horizon
    (μ : FiniteMixture) (hd : 4≤μ.minDegree)
    {Q B β : ℝ} (hQ : 0<Q) (hQ1 : Q≤1)
    (hnp : μ.minDegree<μ.maxDegree) (hB : 0≤B) (hβ : 0≤β)
    (χ : ℝ→ℝ) (hχ : ContDiff ℝ 2 χ)
    (hχb : ∀ s,|χ s|≤1) (hχR : ∀ s,2 < |s|→χ s=0) :
    ∃ (α : ℝ) (hα : 0<α) (γ Cε Cη Ccap : ℝ),
      0<γ ∧ 0<Cε ∧ 0<Cη ∧ 0<Ccap ∧
      let T := sourceShortCell μ Q B α β hα hβ χ hχ
      let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
      0<c₀ ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree), J∈
        EntranceLatitudeTangentObservable.originalLatitudeMeanGood n μ →
      ∀ (e k : ℝ), |e|≤B → |k|≤B →
      let H := exponentialGridHorizon γ (n+1)
      let ε := Cε*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))
      let η := Cη*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)
      let Hf := 2*Real.log 2+
        4*β*derivativeConstant (mixtureCoefficients μ)*((n+1 : ℕ) : ℝ)
      (∫ u,∫ x,sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x
        ∂sphereLaw (n+1) ∂sphereLaw (n+1)) ≤
      (2/(T : ℝ)+4)*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256)+
        (4*η+10*Real.sqrt ε+3*ε*(1+Hf)+
          8*Ccap*Real.exp (-((n+1 : ℕ) : ℝ)*α^2/256))/c₀ := by
  obtain ⟨α,hα,γ₀,Cε,Cη,Ccap,hγ₀,hCε,hCη,hCcap,hEvent⟩ :=
    actual_mixedSource_uniform_cap_hit_fixed_scales μ hd hQ hQ1 hnp hB hβ
  let γ := min γ₀ (α^2/256)
  have hγ : 0<γ := lt_min hγ₀ (by positivity)
  have hγα : γ≤α^2/256 := min_le_right _ _
  have hγold : γ≤γ₀ := min_le_left _ _
  let T := sourceShortCell μ Q B α β hα hβ χ hχ
  have hT : 0<T := sourceShortCell_pos μ Q B α β hα hβ χ hχ
  have hT18 : (T : ℝ)≤1/18 := sourceShortCell_le_eighteenth μ Q B α β hα hβ χ hχ
  have hT1 : (T : ℝ)≤1 := by linarith
  let c₀ := Real.exp (-2)*(1-Real.exp (-(T : ℝ)))
  have hc₀ : 0<c₀ := (source_exponential_exposure_floor γ hγ.le 0 T hT hT1).1
  refine ⟨α,hα,γ,Cε,Cη,Ccap,hγ,hCε,hCη,hCcap,?_⟩
  dsimp only
  refine ⟨hc₀,?_⟩
  filter_upwards [hEvent] with n hn
  intro J hJ e k he hk
  let H := exponentialGridHorizon γ (n+1)
  let θ := sourceExponentialDiscount γ (n+1)
  let ε := Cε*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ))
  let η := Cη*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2)
  let Hf := 2*Real.log 2+
    4*β*derivativeConstant (mixtureCoefficients μ)*((n+1 : ℕ) : ℝ)
  let P : ℝ := ∫ u,∫ x,
    sourceAxisCapHitProbability μ hQ hnp J β α χ hχ e k H u x
      ∂sphereLaw (n+1) ∂sphereLaw (n+1)
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
  have hshort := sourceShortCell_short μ Q B α β hB hα hβ χ hχ e k he hk
  let : IsProbabilityMeasure (sphereLaw (n+1)) := sphereLaw_probability (n+1)
  obtain ⟨u₀,hu₀⟩ := (sphereLaw_support (by omega : 1≤n+1)).exists
  have hu₀ : OnSphere u₀ := (onSphere_iff_norm_sq u₀).mpr hu₀
  have hExposure := hn J hJ χ hχ hχb hχR e k he hk θ hθ hrate
    u₀ hu₀ H T hT hshort
  change exposureFactor (θ : ℝ) H T*(P-E)≤R at hExposure
  have hFloor := (source_exponential_exposure_floor γ hγ.le (n+1) T hT hT1).2
  change c₀≤exposureFactor (θ : ℝ) H T at hFloor
  have hε : 0≤ε := by dsimp only [ε]; positivity
  have hη : 0≤η := by dsimp only [η]; positivity
  have hHf : 0≤Hf := by
    have hdpos := (derivativeConstant_pos (mixtureCoefficients μ)).le
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
