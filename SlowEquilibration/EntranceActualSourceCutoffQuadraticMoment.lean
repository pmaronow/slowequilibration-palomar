-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceSourceCutoffQuadraticMoment

/-! Literal mixed and proper pure cutoff Hamiltonian difference moments.
Every source envelope hypothesis is discharged from the actual original
field and its genuine shared-bank event. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The literal mixed cutoff Hamiltonian difference has its actual
uniform N^(2-d) weighted square moment on the original shared-bank event. -/
theorem actual_sourceSmoothCutoffField_square_exp_abs_eventually_bounded (μ : FiniteMixture)
    (hd : 4≤μ.minDegree) {Q M ζ : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    (hM : 0≤M) (hζ : 0≤ζ) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree),J∈originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (α : ℝ),0<α → α≤ sourceCutoffMomentScale μ Q M ζ →
      ∀ (χ : ℝ→ℝ),Continuous χ → (∀ s,|χ s|≤1) → (∀ s,2< |s| → χ s=0) →
      ∀ e k : ℝ,|e|≤M → |k|≤M →
      let W := fun u => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x-fieldOfMixture μ J x
      Integrable (fun u => (W u)^2*Real.exp (ζ*|W u|)) (sphereLaw (n+1)) ∧
      (∫ u,(W u)^2*Real.exp (ζ*|W u|) ∂sphereLaw (n+1))≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by
  obtain ⟨C,hC,hMom⟩ := source_cutoff_quadratic_moment_eventually_bounded μ hd hQ.le hM hζ
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom] with n hn
  intro J hJ x hx α hα hαsmall χ hχ hχb hχ0 e k he hk
  have h := hn J hJ x hx α hα hαsmall χ hχ hχb hχ0
    (fun u => sourceRegressionCorrection μ Q hQ hnp J u e k x)
    (sourceRegressionCorrection_axis_continuous μ hQ hnp J e k x)
    (fun u hu => actual_sourceRegressionCorrection_abs_le_observable μ hQ hnp hM J hJ.1 u x hu hx he hk)
  have heq : (fun u => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x-fieldOfMixture μ J x)=
      (fun u => sourceAxisCutoff μ Q J α χ x u*sourceRegressionCorrection μ Q hQ hnp J u e k x) := by
    funext u
    rw [sourceSmoothCutoffField_eq]
    unfold sourceAxisCutoff
    ring
  have heqPoint (u : Vector (n+1)) := congrFun heq u
  simpa only [←heqPoint] using h

/-- The proper pure literal cutoff difference has the same genuine
weighted square rate, using its value-plus-zero-gradient correction. -/
theorem actual_pureSourceSmoothCutoffField_square_exp_abs_eventually_bounded
    (p : ℕ) (hp : 4≤p) (c : ℝ) (hc : 0<c) {Q M ζ : ℝ} (hQ : 0<Q)
    (hM : 0≤M) (hζ : 0≤ζ) :
    let μ := FiniteMixture.pure p (by omega) c hc
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree),J∈originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (α : ℝ),0<α → α≤ sourceCutoffMomentScale μ Q M ζ →
      ∀ (χ : ℝ→ℝ),Continuous χ → (∀ s,|χ s|≤1) → (∀ s,2< |s| → χ s=0) →
      ∀ e : ℝ,|e|≤M →
      let W := fun u => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ x-fieldOfMixture μ J x
      Integrable (fun u => (W u)^2*Real.exp (ζ*|W u|)) (sphereLaw (n+1)) ∧
      (∫ u,(W u)^2*Real.exp (ζ*|W u|) ∂sphereLaw (n+1))≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega) c hc
  have hd : 4≤μ.minDegree := by rw [(CSPureModels.pure_degrees p (by omega) c hc).1];exact hp
  obtain ⟨C,hC,hMom⟩ := source_cutoff_quadratic_moment_eventually_bounded μ hd hQ.le hM hζ
  refine ⟨C,hC,?_⟩
  filter_upwards [hMom] with n hn
  intro J hJ x hx α hα hαsmall χ hχ hχb hχ0 e he
  have h := hn J hJ x hx α hα hαsmall χ hχ hχb hχ0
    (fun u => pureSourceRegressionCorrection p (by omega) c hc Q J u e x)
    (pureSourceRegressionCorrection_axis_continuous p (by omega) c hc Q J e x)
    (fun u hu => actual_pureSourceRegressionCorrection_abs_le_observable p (by omega) c hc hQ hM J hJ.1 u x hu hx he)
  have heq : (fun u => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ x-fieldOfMixture μ J x)=
      (fun u => sourceAxisCutoff μ Q J α χ x u*pureSourceRegressionCorrection p (by omega) c hc Q J u e x) := by
    funext u
    unfold pureSourceSmoothCutoffField sourceAxisCutoff
    ring
  have heqPoint (u : Vector (n+1)) := congrFun heq u
  simpa only [←heqPoint] using h

end
end SlowEquilibration.EntranceLatitudeTangentObservable
