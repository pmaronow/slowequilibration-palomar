-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedResolventL2
public import SlowEquilibration.GOEClippedResolventLipschitz
public import SlowEquilibration.QuadraticPerturbation

/-! Actual clipped GOE resolvent L² convergence along varying matrix
dimensions and convergent shifts, with no varying-shift limit premise. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK BoundedQuadraticConvergence
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

lemma semicircleResolvent_continuous : Continuous semicircleResolvent := by
  unfold semicircleResolvent
  fun_prop

lemma clippedResolvent_centered_square_integrable (n : ℕ) (s b : ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    Integrable (fun W : Matrix (Fin (n+1)) (Fin (n+1)) ℝ=>(clippedResolvent n s ρ W-b)^2)
      (goeLaw (n+1) (n+1) 1) := by
  apply (square_integral_le_small_bad _ _ ((clippedResolvent_measurable n s ρ).sub_const b)
    (C:=1/ρ+|b|) (ε:=0) (by positivity) (by norm_num) ?_).1
  intro W
  have hb:=clippedResolvent_bounds n s hρ W
  exact (abs_sub _ _).trans (by rw [abs_of_nonneg hb.1];gcongr;exact hb.2)

/-- Actual mean-square convergence remains true for every diverging
matrix dimension and every convergent outside-edge shift sequence. -/
theorem clippedResolvent_varying_shift_L2 (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop)
    (sN : ℕ → ℝ) {s ρ : ℝ} (hsN : Tendsto sN atTop (𝓝 s)) (hs : 0 < s)
    (hρ : 0 < ρ) (hρs : ρ ≤ s/2) :
    Tendsto (fun j:ℕ=>∫ W,(clippedResolvent (φ j) (sN j) ρ W-semicircleResolvent (sN j))^2
      ∂goeLaw (φ j+1) (φ j+1) 1) atTop (𝓝 0) := by
  let K : ℕ → ℝ:=fun j=>|sN j-s|/ρ^2+|semicircleResolvent (sN j)-semicircleResolvent s|
  have hK0 (j:ℕ) : 0 ≤ K j:=by positivity
  have hd : Tendsto (fun j=>|sN j-s|) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,abs_zero] using (hsN.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ=>s) atTop (𝓝 s))).abs
  have hg : Tendsto (fun j=>|semicircleResolvent (sN j)-semicircleResolvent s|) atTop (𝓝 0) := by
    simpa only [Function.comp_def,sub_self,abs_zero] using ((semicircleResolvent_continuous.tendsto s).comp hsN |>.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ=>semicircleResolvent s) atTop (𝓝 (semicircleResolvent s)))).abs
  have hKt : Tendsto K atTop (𝓝 0) := by
    simpa only [zero_div,add_zero] using (hd.div_const (ρ^2)).add hg
  have hfixed:=(clippedResolvent_converges_in_L2 hs hρ hρs).comp hφ
  have hupper : Tendsto (fun j=>2*(∫ W,(clippedResolvent (φ j) s ρ W-semicircleResolvent s)^2
      ∂goeLaw (φ j+1) (φ j+1) 1)+2*K j^2) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] using
      (hfixed.const_mul 2).add ((hKt.pow 2).const_mul 2)
  apply squeeze_zero (fun j=>integral_nonneg (fun _=>sq_nonneg _)) (fun j=>?_) hupper
  apply integral_square_perturbation_bound _ _ _
    (clippedResolvent_centered_square_integrable (φ j) (sN j) _ hρ)
    (clippedResolvent_centered_square_integrable (φ j) s _ hρ) (hK0 j)
  intro W
  calc
    _ = |(clippedResolvent (φ j) (sN j) ρ W-clippedResolvent (φ j) s ρ W)-
        (semicircleResolvent (sN j)-semicircleResolvent s)| := by congr 1;ring
    _ ≤ |clippedResolvent (φ j) (sN j) ρ W-clippedResolvent (φ j) s ρ W|+
        |semicircleResolvent (sN j)-semicircleResolvent s| := abs_sub _ _
    _ ≤ K j := add_le_add (clippedResolvent_shift_bound (φ j) hρ (sN j) s W) le_rfl

end
end SlowEquilibration.GOEClippedResolvent
