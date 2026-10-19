-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedInverseOnGap

/-! Genuine physical covariance-weighted inverse trace convergence,
the exact deterministic term in the common-row Schur complement. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK GOEScaling GOEPhysicalPotential
open BoundedQuadraticConvergence CompactUniformSequence
open scoped Topology RealInnerProductSpace
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def physicalCovarianceTrace (n j : ℕ) (b k ρ : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) : ℝ :=
  (scaleFactor n (n+1+j) b)^2*physicalClippedResolvent n j b k ρ W

/-- Literal b/N trace of the actual continuous inverse operator. -/
lemma physicalCovarianceTrace_eq_operator_trace (n j : ℕ) {b : ℝ} (hb : 0 ≤ b) (k ρ : ℝ)
    (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    physicalCovarianceTrace n j b k ρ W=
      (b/(n+1+j:ℕ))*LinearMap.trace ℝ (EuclideanSpace ℝ (Fin (n+1)))
        (clippedInverseOperator k (scaleFactor n (n+1+j) b*ρ) W).toLinearMap := by
  rw [clippedInverseOperator_trace]
  unfold physicalCovarianceTrace physicalClippedResolvent
  rw [scaleFactor_square n (by omega) hb]
  ring

lemma physicalClippedResolvent_bounds (n j : ℕ) {b ρ : ℝ} (hb : 0 < b) (hρ : 0 < ρ)
    (k : ℝ) (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
    0 ≤ physicalClippedResolvent n j b k ρ W ∧
      physicalClippedResolvent n j b k ρ W ≤ 1/(scaleFactor n (n+1+j) b*ρ) := by
  have hh:=clippedResolvent_bounds n (k-2) (mul_pos (scaleFactor_pos n (N:=n+1+j) (by omega) hb) hρ) W
  simpa only [physicalClippedResolvent,← physicalClippedTrace_eq_standard] using hh

lemma physicalClippedResolvent_centered_square_integrable (n j : ℕ) {b ρ : ℝ}
    (hb : 0 < b) (hρ : 0 < ρ) (k t : ℝ) :
    Integrable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>
      (physicalClippedResolvent n j b k ρ W-t)^2) (goeLaw (n+1) (n+1+j) b) := by
  apply (square_integral_le_small_bad _ _
    ((physicalClippedTrace_measurable n k _).sub_const t)
    (C:=1/(scaleFactor n (n+1+j) b*ρ)+|t|) (ε:=0)
    (by positivity [scaleFactor_pos n (by omega : 0 < n+1+j) hb]) (by norm_num) ?_).1
  intro W
  have hh:=physicalClippedResolvent_bounds n j hb hρ k W
  change |physicalClippedResolvent n j b k ρ W-t| ≤ _
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg hh.1];gcongr;exact hh.2)

/-- Actual covariance-weighted operator trace converges in L² to the
source term b*m_b(k), uniformly along varying outside-edge shifts. -/
theorem physical_covariance_trace_varying_L2 (j : ℕ) {b ρ k : ℝ} (hb : 0 < b)
    (hρ : 0 < ρ) (hk : 2*Real.sqrt b < k) (hρk : ρ ≤ (k/Real.sqrt b-2)/2)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (kN : ℕ → ℝ) (hkN : Tendsto kN atTop (𝓝 k)) :
    Tendsto (fun l:ℕ=>∫ W,(physicalCovarianceTrace (φ l) j b (kN l) ρ W-b*physicalResolvent b (kN l))^2
      ∂goeLaw (φ l+1) (φ l+1+j) b) atTop (𝓝 0) := by
  let a : ℕ → ℝ:=fun l=>scaleFactor (φ l) (φ l+1+j) b
  let α : ℕ → ℝ:=fun l=>(a l)^2
  have ha (l:ℕ) : 0 < a l:=scaleFactor_pos _ (by omega) hb
  have hα : Tendsto α atTop (𝓝 b) := by
    simpa only [α,a,Function.comp_def,Real.sq_sqrt hb.le] using ((scaleFactor_tendsto j hb.le).comp hφ).pow 2
  have htrace:=physical_clipped_resolvent_varying_L2 j hb hρ hk hρk φ hφ kN hkN
  let K : ℕ → ℝ:=fun l=>|(α l-b)*physicalResolvent b (kN l)|
  have hKt : Tendsto K atTop (𝓝 0) := by
    have hr:=((physicalResolvent_continuous_shift b).tendsto k).comp hkN
    simpa only [K,Function.comp_def,sub_self,zero_mul,abs_zero] using ((hα.sub_const b).mul hr).abs
  have hup : Tendsto (fun l=>2*(α l)^2*(∫ W,(physicalClippedResolvent (φ l) j b (kN l) ρ W-physicalResolvent b (kN l))^2
      ∂goeLaw (φ l+1) (φ l+1+j) b)+2*(K l)^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] using
      (((hα.pow 2).const_mul 2).mul htrace).add ((hKt.pow 2).const_mul 2)
  apply squeeze_zero (fun l=>integral_nonneg (fun _=>sq_nonneg _)) (fun l=>?_) hup
  let μ:=goeLaw (φ l+1) (φ l+1+j) b
  let F:=fun W:Matrix (Fin (φ l+1)) (Fin (φ l+1)) ℝ=>
    α l*physicalClippedResolvent (φ l) j b (kN l) ρ W-b*physicalResolvent b (kN l)
  let G:=fun W:Matrix (Fin (φ l+1)) (Fin (φ l+1)) ℝ=>
    α l*(physicalClippedResolvent (φ l) j b (kN l) ρ W-physicalResolvent b (kN l))
  have hGInt : Integrable (fun W=>G W^2) μ := by
    have hh:=(physicalClippedResolvent_centered_square_integrable (φ l) j hb hρ (kN l)
      (physicalResolvent b (kN l))).const_mul ((α l)^2)
    simpa only [G,mul_pow] using hh
  have hFMeas : Measurable F := (measurable_const.mul (physicalClippedTrace_measurable _ _ _)).sub_const _
  have hFbound (W) : |F W| ≤ α l/(a l*ρ)+|b*physicalResolvent b (kN l)| := by
    have hh:=physicalClippedResolvent_bounds (φ l) j hb hρ (kN l) W
    calc
      _ ≤ |α l*physicalClippedResolvent (φ l) j b (kN l) ρ W|+|b*physicalResolvent b (kN l)| :=abs_sub _ _
      _=α l*physicalClippedResolvent (φ l) j b (kN l) ρ W+|b*physicalResolvent b (kN l)| := by
        rw [abs_of_nonneg (mul_nonneg (sq_nonneg _) hh.1)]
      _ ≤ α l*(1/(a l*ρ))+|b*physicalResolvent b (kN l)| :=
        add_le_add (mul_le_mul_of_nonneg_left hh.2 (sq_nonneg _)) le_rfl
      _=_ := by ring
  have hFInt : Integrable (fun W=>F W^2) μ :=
    (square_integral_le_small_bad μ F hFMeas (C:=α l/(a l*ρ)+|b*physicalResolvent b (kN l)|)
      (ε:=0) (by positivity [ha l]) (by norm_num) hFbound).1
  have heq (W) : F W-G W=(α l-b)*physicalResolvent b (kN l) := by dsimp only [F,G];ring
  have hh:=integral_square_perturbation_bound μ F G hFInt hGInt (K:=K l) (abs_nonneg _) (fun W=>by rw [heq])
  have hGI : (∫ W,G W^2 ∂μ)=(α l)^2*(∫ W,(physicalClippedResolvent (φ l) j b (kN l) ρ W-physicalResolvent b (kN l))^2 ∂μ) := by
    simp only [G,mul_pow,integral_const_mul]
  rw [hGI] at hh
  simpa only [F,physicalCovarianceTrace,α,a,mul_assoc] using hh

/-- Genuine compact-window uniform covariance-weighted trace limit. -/
theorem uniform_physical_covariance_trace_L2 (j : ℕ) {b ρ k0 k1 : ℝ} (hb : 0 < b)
    (hρ : 0 < ρ) (hk0 : 2*Real.sqrt b < k0) (hρk0 : ρ ≤ (k0/Real.sqrt b-2)/2)
    {ε : ℝ} (hε : 0 < ε) : ∀ᶠ n:ℕ in atTop,∀ k ∈ Icc k0 k1,
    (∫ W,(physicalCovarianceTrace n j b k ρ W-b*physicalResolvent b k)^2
      ∂goeLaw (n+1) (n+1+j) b) ≤ ε := by
  apply uniform_eventually_le_of_varying_limit isCompact_Icc
    (fun n k=>∫ W,(physicalCovarianceTrace n j b k ρ W-b*physicalResolvent b k)^2
      ∂goeLaw (n+1) (n+1+j) b) _ hε
  intro φ hφ p k hk hp
  apply physical_covariance_trace_varying_L2 j hb hρ (lt_of_lt_of_le hk0 hk.1) _ φ hφ p hp
  exact hρk0.trans (div_le_div_of_nonneg_right
    (sub_le_sub_right (div_le_div_of_nonneg_right hk.1 (Real.sqrt_nonneg b)) 2) (by norm_num))

end
end SlowEquilibration.GOEClippedResolvent

