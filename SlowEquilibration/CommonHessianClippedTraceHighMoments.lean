-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianSubgaussianHighMoments
public import SlowEquilibration.CommonHessianRealMomentPerturbation
public import SlowEquilibration.GOEClippedResolventQuantitative

/-! Actual every-real-q outside-edge clipped GOE trace rate from the true
centered MGF and the proved Jacobi-resolvent mean bias. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK GaussianQuadraticVariance
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Actual all fixed real q absolute moments of the normalized clipped
trace error, uniformly on the entire positive outside-edge ray. -/
theorem realizedClippedResolvent_uniform_q_rate {g ρ:ℝ}
    (hg:0<g) (hρ:0<ρ) (hρg:ρ≤g/2) (q:ℝ) (hq:0≤q) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,∀ s:ℝ,g ≤ s →
      Integrable (fun A=>|realizedClippedResolvent n s ρ A-semicircleResolvent s|^q)
        (stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))) ∧
      (∫ A,|realizedClippedResolvent n s ρ A-semicircleResolvent s|^q
        ∂stdGaussian (GOEAsymptotics.GaussianMatrix (n+1)))≤C/(n+1:ℝ)^q:=by
  let V:=subgaussianMomentConstant q (Real.pi^2/(4*ρ^4))
  let B:=meanBiasConstant g ρ
  have hB:0≤B:=meanBiasConstant_nonneg hg hρ
  have hV:0<V:=subgaussianMomentConstant_pos _ _
  refine ⟨(2:ℝ)^q*(V+B^q),by positivity,?_⟩
  filter_upwards [realizedClippedResolvent_uniform_mean_rate hg hρ hρg] with n hn
  intro s hs
  let P:=stdGaussian (GOEAsymptotics.GaussianMatrix (n+1))
  let m:=∫ A,realizedClippedResolvent n s ρ A ∂P
  let F:=fun A=>realizedClippedResolvent n s ρ A-semicircleResolvent s
  let G:=fun A=>realizedClippedResolvent n s ρ A-m
  have hMeas:=(realizedClippedResolvent_lipschitz n s hρ).continuous.measurable
  have hBudget:((Real.pi^2/(2*ρ^4*(n+1:ℝ)^2)).toNNReal:ℝ)*(n+1:ℝ)^2/2≤
      Real.pi^2/(4*ρ^4):=by
    rw [Real.coe_toNNReal _ (by positivity)]
    field_simp <;> norm_num
  have hVar:=subgaussian_high_moment P G (hMeas.sub_const m)
    (realizedClippedResolvent_centered_subGaussian n s hρ) (by positivity : 0<(n+1:ℝ)) hBudget q hq
  have hDiff (A):|F A-G A|≤B/(n+1:ℝ):=by
    change |(realizedClippedResolvent n s ρ A-semicircleResolvent s)-
      (realizedClippedResolvent n s ρ A-m)|≤_
    rw [show (realizedClippedResolvent n s ρ A-semicircleResolvent s)-
      (realizedClippedResolvent n s ρ A-m)=m-semicircleResolvent s by ring]
    exact hn s hs
  have hPert:=integral_absolute_moment_perturbation P F G (hMeas.sub_const _) q hq
    hVar.1 (show 0≤B/(n+1:ℝ) by positivity) hDiff
  refine ⟨hPert.1,hPert.2.trans ?_⟩
  calc
    _ ≤ (2:ℝ)^q*(V/(n+1:ℝ)^q+(B/(n+1:ℝ))^q):=
      mul_le_mul_of_nonneg_left (add_le_add hVar.2 le_rfl) (by positivity)
    _=_:=by rw [Real.div_rpow hB (by positivity)];ring

/-- The genuine every-real-q conclusion under the literal symmetric
matrix GOE law used by the original common Hessian posterior. -/
theorem clippedResolvent_uniform_q_rate {g ρ:ℝ}
    (hg:0<g) (hρ:0<ρ) (hρg:ρ≤g/2) (q:ℝ) (hq:0≤q) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,∀ s:ℝ,g ≤ s →
      Integrable (fun W=>|clippedResolvent n s ρ W-semicircleResolvent s|^q)
        (goeLaw (n+1) (n+1) 1) ∧
      (∫ W,|clippedResolvent n s ρ W-semicircleResolvent s|^q
        ∂goeLaw (n+1) (n+1) 1)≤C/(n+1:ℝ)^q:=by
  obtain ⟨C,hC,h⟩:=realizedClippedResolvent_uniform_q_rate hg hρ hρg q hq
  refine ⟨C,hC,?_⟩
  filter_upwards [h] with n hn
  intro s hs
  have hm:=GOEDeterminantMoments.realization_measurable n
  have hf:Measurable (fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>
      |clippedResolvent n s ρ W-semicircleResolvent s|^q):=
    ((clippedResolvent_measurable n s ρ).sub_const _).abs.pow_const q
  rw [←GOEDeterminantMoments.realization_law n]
  refine ⟨(integrable_map_measure hf.aestronglyMeasurable hm.aemeasurable).mpr (hn s hs).1,?_⟩
  rw [integral_map hm.aemeasurable hf.aestronglyMeasurable]
  exact (hn s hs).2

end
end SlowEquilibration.GOEClippedResolvent
