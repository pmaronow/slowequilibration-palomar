-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.CommonHessianClippedTraceHighMoments
public import SlowEquilibration.GOEPhysicalCovarianceBias
public import SlowEquilibration.GOEPhysicalCovarianceTraceIntegrability

/-! True all-q physical covariance-weighted common inverse-trace rate,
with the literal variance b/N and source semicircle target retained. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK GOEScaling GOEPhysicalPotential
open GaussianQuadraticVariance
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000

/-- Actual ordinary all-real-q trace approximation on the fixed physical
gap ray. The constant is independent of the dimension and physical shift. -/
theorem physical_covariance_trace_uniform_q_rate (j:ℕ) {b g ρ:ℝ}
    (hb:0<b) (hg:0<g) (hρ:0<ρ) (hρg:ρ ≤ (g/Real.sqrt b)/2)
    (q:ℝ) (hq:0 ≤ q) :
    ∃ C:ℝ,0<C ∧ ∀ᶠ n:ℕ in atTop,∀ k:ℝ,2*Real.sqrt b+g ≤ k →
      Integrable (fun W=>|physicalCovarianceTrace n j b k ρ W-b*physicalResolvent b k|^q)
        (goeLaw (n+1) (n+1+j) b) ∧
      (∫ W,|physicalCovarianceTrace n j b k ρ W-b*physicalResolvent b k|^q
        ∂goeLaw (n+1) (n+1+j) b) ≤ C/(n+1:ℝ)^q:=by
  obtain ⟨Cs,hCs,hStd⟩:=clippedResolvent_uniform_q_rate
    (div_pos hg (Real.sqrt_pos.mpr hb)) hρ hρg q hq
  let D:=2*b*(j:ℝ)/g
  have hD:0 ≤ D:=by dsimp only [D];positivity
  refine ⟨(2:ℝ)^q*((Real.sqrt b)^q*Cs+D^q),by positivity,?_⟩
  filter_upwards [hStd] with n hn
  intro k hk
  let a:=scaleFactor n (n+1+j) b
  let s:=k/a-2
  let P:=goeLaw (n+1) (n+1) 1
  have ha:0<a:=scaleFactor_pos n (by omega) hb
  have hgap:g/Real.sqrt b ≤ s:=by
    have hh:=scaled_shift_gap (n:=n) (N:=n+1+j) (by omega) (by omega) hb hg hk
    dsimp only [s,a]
    linarith
  have hStdRate:=hn s hgap
  have hscale:Measurable (fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>a • W):=by fun_prop
  have hmap:P.map (fun W=>a • W)=goeLaw (n+1) (n+1+j) b:=goeLaw_scale n (by omega) hb.le
  have hEval (W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ):
      physicalCovarianceTrace n j b k ρ (a • W)=a*clippedResolvent n s ρ W:=by
    change a^2*physicalClippedTrace n k (a*ρ) (a • W)=_
    rw [physicalClippedTrace_scale n ha k ρ W]
    dsimp only [s]
    field_simp
  let F:=fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>a*clippedResolvent n s ρ W-b*physicalResolvent b k
  let G:=fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>a*(clippedResolvent n s ρ W-semicircleResolvent s)
  have hGE (W):|G W|^q=a^q*|clippedResolvent n s ρ W-semicircleResolvent s|^q:=by
    dsimp only [G]
    rw [abs_mul,abs_of_pos ha,Real.mul_rpow ha.le (abs_nonneg _)]
  have hGI:Integrable (fun W=>|G W|^q) P:=by
    simpa only [hGE] using hStdRate.1.const_mul (a^q)
  have hFMeas:Measurable F:=(measurable_const.mul (clippedResolvent_measurable n s ρ)).sub_const _
  have hBias:=physical_covariance_target_bias n j hb hg hk
  have hDiff (W):|F W-G W| ≤ D/(n+1:ℝ):=by
    rw [show F W-G W=a*semicircleResolvent s-b*physicalResolvent b k by dsimp only [F,G];ring]
    exact hBias
  have hPert:=integral_absolute_moment_perturbation P F G hFMeas q hq hGI
    (show 0 ≤ D/(n+1:ℝ) by positivity) hDiff
  have ha2:a^2 ≤ b:=by
    rw [show a^2=b*(n+1:ℝ)/(n+1+j:ℕ) from scaleFactor_square n (by omega) hb.le]
    apply (div_le_iff₀ (by positivity : 0<((n+1+j:ℕ):ℝ))).mpr
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg hb.le (Nat.cast_nonneg j)]
  have haRoot:a ≤ Real.sqrt b:=(Real.le_sqrt ha.le hb.le).mpr ha2
  have hGIBound:(∫ W,|G W|^q ∂P) ≤ (Real.sqrt b)^q*Cs/(n+1:ℝ)^q:=by
    simp only [hGE,integral_const_mul]
    exact (mul_le_mul (Real.rpow_le_rpow ha.le haRoot hq) hStdRate.2
      (integral_nonneg (fun _=>Real.rpow_nonneg (abs_nonneg _) q)) (by positivity)).trans_eq (by ring)
  have hBound:(∫ W,|F W|^q ∂P) ≤ (2:ℝ)^q*((Real.sqrt b)^q*Cs+D^q)/(n+1:ℝ)^q:=by
    calc
      _ ≤ _:=hPert.2
      _ ≤ (2:ℝ)^q*((Real.sqrt b)^q*Cs/(n+1:ℝ)^q+(D/(n+1:ℝ))^q):=
        mul_le_mul_of_nonneg_left (add_le_add hGIBound le_rfl) (by positivity)
      _=_:=by rw [Real.div_rpow hD (by positivity)];ring
  have hm:Measurable (fun W:Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>
      |physicalCovarianceTrace n j b k ρ W-b*physicalResolvent b k|^q):=
    ((physicalCovarianceTrace_measurable n j b k ρ).sub_const _).abs.pow_const q
  rw [←hmap]
  refine ⟨?_,?_⟩
  · exact (integrable_map_measure hm.aestronglyMeasurable hscale.aemeasurable).mpr
      (by simpa only [Function.comp_def,hEval,F] using hPert.1)
  · rw [integral_map hscale.aemeasurable hm.aestronglyMeasurable]
    simpa only [hEval,F] using hBound

end
end SlowEquilibration.GOEClippedResolvent
