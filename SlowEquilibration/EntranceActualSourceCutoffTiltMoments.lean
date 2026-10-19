-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.EntranceActualSourceCutoffQuadraticMoment
public import SlowEquilibration.SphericalExponentialTiltDefects

/-! Literal source eta and epsilon moments, derived from the actual
original Gaussian bank event for both mixed and proper pure models. -/

@[expose] public section
namespace SlowEquilibration.EntranceLatitudeTangentObservable
noncomputable section
open MeasureTheory ProbabilityTheory Filter Set
open SphericalModel SphericalForm SphericalGaussianJet ConditionedEntrance
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- Actual mixed source eta=O(N^(1-d/2)) and epsilon=O(N^(2-d)),
uniformly in bounded physical marks, every frozen axis and every allowed
cutoff scale; constants are selected before dimension. -/
theorem actual_sourceSmoothCutoffField_tilt_moments (μ : FiniteMixture)
    (hd : 4≤μ.minDegree) {Q M β : ℝ} (hQ : 0<Q) (hnp : μ.minDegree<μ.maxDegree)
    (hM : 0≤M) (hβ : 0≤β) :
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree),J∈originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (α : ℝ),0<α → α≤ sourceCutoffMomentScale μ Q M (2*β) →
      ∀ (χ : ℝ→ℝ),ContDiff ℝ 2 χ → (∀ s,|χ s|≤1) → (∀ s,2< |s| → χ s=0) →
      ∀ e k : ℝ,|e|≤M → |k|≤M →
      let W := fun u => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x-fieldOfMixture μ J x
      (∫ u,|Real.exp (β*W u)-1| ∂sphereLaw (n+1))≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (∫ u,Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw (n+1))≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by
  obtain ⟨C,hC,hMom⟩ := actual_sourceSmoothCutoffField_square_exp_abs_eventually_bounded μ hd hQ hnp hM
    (show 0≤2*β by positivity)
  refine ⟨1+β*Real.sqrt C+β^2*C,by positivity,?_⟩
  filter_upwards [hMom] with n hn
  intro J hJ x hx α hα hαsmall χ hχ hχb hχ0 e k he hk
  let W := fun u => sourceSmoothCutoffField μ Q hQ hnp J u e k α χ x-fieldOfMixture μ J x
  have hW : Continuous W :=
    ((sourceSmoothCutoffField_jointContinuous μ Q hQ hnp α χ hχ.continuous).comp
      (show Continuous (fun u : Vector (n+1) => ((J,(u,(e,k))),x)) by fun_prop)).sub continuous_const
  have h := sphere_exponential_tilt_defects_of_square_bound (d := μ.minDegree) (by omega : 1≤n+1)
    hβ hC.le W hW (hn J hJ x hx α hα hαsmall χ hχ.continuous hχb hχ0 e k he hk).2
  refine ⟨h.1.trans ?_,h.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (sq_nonneg β) hC.le] : β*Real.sqrt C≤1+β*Real.sqrt C+β^2*C) (by positivity)
  · exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hβ (Real.sqrt_nonneg C)] : β^2*C≤1+β*Real.sqrt C+β^2*C) (by positivity)

/-- Actual proper pure source eta and epsilon rates, retaining its literal
value/zero-gradient posterior and homogeneous correction, without Σ inverse. -/
theorem actual_pureSourceSmoothCutoffField_tilt_moments
    (p : ℕ) (hp : 4≤p) (c : ℝ) (hc : 0<c) {Q M β : ℝ} (hQ : 0<Q)
    (hM : 0≤M) (hβ : 0≤β) :
    let μ := FiniteMixture.pure p (by omega) c hc
    ∃ C : ℝ,0<C ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (J : Disorder (n+1) μ.maxDegree),J∈originalLatitudeMeanGood n μ →
      ∀ (x : Vector (n+1)),‖x‖^2=((n+1 : ℕ) : ℝ) →
      ∀ (α : ℝ),0<α → α≤ sourceCutoffMomentScale μ Q M (2*β) →
      ∀ (χ : ℝ→ℝ),ContDiff ℝ 2 χ → (∀ s,|χ s|≤1) → (∀ s,2< |s| → χ s=0) →
      ∀ e : ℝ,|e|≤M →
      let W := fun u => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ x-fieldOfMixture μ J x
      (∫ u,|Real.exp (β*W u)-1| ∂sphereLaw (n+1))≤
        C*((n+1 : ℕ) : ℝ)^(1-(μ.minDegree : ℝ)/2) ∧
      (∫ u,Real.exp (β*W u)*(1-Real.exp (-β*W u))^2 ∂sphereLaw (n+1))≤
        C*((n+1 : ℕ) : ℝ)^(2-(μ.minDegree : ℝ)) := by
  dsimp only
  let μ := FiniteMixture.pure p (by omega) c hc
  obtain ⟨C,hC,hMom⟩ := actual_pureSourceSmoothCutoffField_square_exp_abs_eventually_bounded p hp c hc hQ hM
    (show 0≤2*β by positivity)
  refine ⟨1+β*Real.sqrt C+β^2*C,by positivity,?_⟩
  filter_upwards [hMom] with n hn
  intro J hJ x hx α hα hαsmall χ hχ hχb hχ0 e he
  let W := fun u => pureSourceSmoothCutoffField p (by omega) c hc Q J u e α χ x-fieldOfMixture μ J x
  have hW : Continuous W :=
    ((pureSourceJointHamiltonian_contDiff p (by omega) c hc Q α χ hχ).continuous.comp
      (show Continuous (fun u : Vector (n+1) => ((J,(u,(e,(0 : ℝ)))),x)) by fun_prop)).sub continuous_const
  have h := sphere_exponential_tilt_defects_of_square_bound (d := μ.minDegree) (by omega : 1≤n+1)
    hβ hC.le W hW (hn J hJ x hx α hα hαsmall χ hχ.continuous hχb hχ0 e he).2
  refine ⟨h.1.trans ?_,h.2.trans ?_⟩
  · exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg (sq_nonneg β) hC.le] : β*Real.sqrt C≤1+β*Real.sqrt C+β^2*C) (by positivity)
  · exact mul_le_mul_of_nonneg_right (by nlinarith [mul_nonneg hβ (Real.sqrt_nonneg C)] : β^2*C≤1+β*Real.sqrt C+β^2*C) (by positivity)

end
end SlowEquilibration.EntranceLatitudeTangentObservable
