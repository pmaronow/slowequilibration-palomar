-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedResolventQuantitative
public import SlowEquilibration.GOEPhysicalCovarianceBias

/-! Genuine quantitative physical covariance-weighted inverse trace.
The literal variance-b/N law, scaled cutoff a_N*rho and source b*m_b(k)
are retained. The actual square error is uniformly of order 1/N². -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK GOEScaling GOEPhysicalPotential
open BoundedQuadraticConvergence
open scoped Topology
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- The genuine physical covariance-weighted clipped operator trace has a
uniform dimension-inverse squared error, throughout the actual fixed gap ray.
No spectral limit, bias, rate or exceptional probability is a premise. -/
theorem physical_covariance_trace_uniform_L2_rate (j : ℕ) {b g ρ : ℝ}
    (hb : 0 < b) (hg : 0 < g) (hρ : 0 < ρ) (hρg : ρ ≤ (g/Real.sqrt b)/2) :
    ∃ C : ℝ,0 < C ∧ ∀ᶠ n : ℕ in atTop,∀ k : ℝ,2*Real.sqrt b+g≤k →
      (∫ W,(physicalCovarianceTrace n j b k ρ W-b*physicalResolvent b k)^2
        ∂goeLaw (n+1) (n+1+j) b) ≤ C/(n+1:ℝ)^2 := by
  obtain ⟨Cs,hCs,hStd⟩:=clippedResolvent_uniform_L2_rate
    (div_pos hg (Real.sqrt_pos.mpr hb)) hρ hρg
  let D:=2*b*(j:ℝ)/g
  refine ⟨2*b*Cs+2*D^2,by positivity,?_⟩
  filter_upwards [hStd] with n hn
  intro k hk
  let a:=scaleFactor n (n+1+j) b
  let s:=k/a-2
  let P:=goeLaw (n+1) (n+1) 1
  have ha : 0 < a:=scaleFactor_pos n (by omega) hb
  have hgap : g / Real.sqrt b ≤ s := by
    have hh:=scaled_shift_gap (n:=n) (N:=n+1+j) (by omega) (by omega) hb hg hk
    dsimp only [s,a]
    linarith
  have hStdRate:=hn s hgap
  have hscale : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>a • W) := by fun_prop
  have hmap : P.map (fun W=>a • W)=goeLaw (n+1) (n+1+j) b:=goeLaw_scale n (by omega) hb.le
  have hm : Measurable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>
      (physicalCovarianceTrace n j b k ρ W-b*physicalResolvent b k)^2) := by
    exact ((measurable_const.mul (physicalClippedTrace_measurable n k _)).sub_const _).pow_const 2
  rw [← hmap,integral_map hscale.aemeasurable hm.aestronglyMeasurable]
  have hEval (W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ) :
      physicalCovarianceTrace n j b k ρ (a • W)=a*clippedResolvent n s ρ W := by
    change a^2*physicalClippedTrace n k (a*ρ) (a • W)=_
    rw [physicalClippedTrace_scale n ha k ρ W]
    dsimp only [s]
    field_simp
  simp only [hEval]
  let F:=fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>a*clippedResolvent n s ρ W-b*physicalResolvent b k
  let G:=fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>a*(clippedResolvent n s ρ W-semicircleResolvent s)
  have hGInt : Integrable (fun W=>G W^2) P := by
    have hh:=(clippedResolvent_centered_square_integrable n s (semicircleResolvent s) hρ).const_mul (a^2)
    simpa only [G,mul_pow] using hh
  have hFMeas : Measurable F:=(measurable_const.mul (clippedResolvent_measurable n s ρ)).sub_const _
  have hFbound (W) : |F W|≤a/ρ+|b*physicalResolvent b k| := by
    have hh:=clippedResolvent_bounds n s hρ W
    calc
      _ ≤ |a*clippedResolvent n s ρ W|+|b*physicalResolvent b k|:=abs_sub _ _
      _ = a*clippedResolvent n s ρ W+|b*physicalResolvent b k| := by
        rw [abs_of_nonneg (mul_nonneg ha.le hh.1)]
      _ ≤ a*(1/ρ)+|b*physicalResolvent b k| :=
        add_le_add (mul_le_mul_of_nonneg_left hh.2 ha.le) le_rfl
      _ = _ := by ring
  have hFInt : Integrable (fun W=>F W^2) P :=
    (square_integral_le_small_bad P F hFMeas (C:=a/ρ+|b*physicalResolvent b k|)
      (ε:=0) (by positivity) (by norm_num) hFbound).1
  have hBias:=physical_covariance_target_bias n j hb hg hk
  have hbound (W) : |F W-G W|≤D/(n+1:ℝ) := by
    have he : F W-G W=a*semicircleResolvent s-b*physicalResolvent b k := by dsimp only [F,G];ring
    rw [he]
    exact hBias
  have hPert:=integral_square_perturbation_bound P F G hFInt hGInt
    (K:=D/(n+1:ℝ)) (by dsimp only [D];positivity) hbound
  have hGI : (∫ W,G W^2 ∂P)=a^2*(∫ W,(clippedResolvent n s ρ W-semicircleResolvent s)^2 ∂P) := by
    simp only [G,mul_pow,integral_const_mul]
  rw [hGI] at hPert
  have ha2 : a^2≤b := by
    rw [show a^2=b*(n+1:ℝ)/(n+1+j:ℕ) from scaleFactor_square n (by omega) hb.le]
    apply (div_le_iff₀ (by positivity : 0 < ((n+1+j:ℕ):ℝ))).mpr
    simp only [Nat.cast_add,Nat.cast_one]
    nlinarith [mul_nonneg hb.le (Nat.cast_nonneg j)]
  have hProd : a^2*(∫ W,(clippedResolvent n s ρ W-semicircleResolvent s)^2 ∂P)≤b*(Cs/(n+1:ℝ)^2) :=
    mul_le_mul ha2 hStdRate (integral_nonneg (fun _=>sq_nonneg _)) hb.le
  calc
    _ ≤ _ :=hPert
    _ ≤ 2*(b*(Cs/(n+1:ℝ)^2))+2*(D/(n+1:ℝ))^2 :=
      add_le_add (mul_le_mul_of_nonneg_left hProd (by norm_num)) le_rfl
    _ = _ := by rw [div_pow];ring

end
end SlowEquilibration.GOEClippedResolvent
