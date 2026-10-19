-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.GOEClippedResolventPhysicalScale
public import SlowEquilibration.GOEPhysicalPotential

/-! Actual fixed-codimension physical variance-b/N clipped resolvent L²
limit, retaining the explicitly scaled physical cutoff a_N rho. -/
@[expose] public section
namespace SlowEquilibration.GOEClippedResolvent
noncomputable section
open Function MeasureTheory ProbabilityTheory Filter Set
open GOEAsymptotics SphericalGaussianJet OAI.CriticalSK GOEScaling GOEPhysicalPotential
open BoundedQuadraticConvergence
open scoped Topology
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

def physicalResolvent (b k : ℝ) : ℝ := (Real.sqrt b)⁻¹*semicircleResolvent (k/Real.sqrt b-2)

def physicalClippedResolvent (n j : ℕ) (b k ρ : ℝ) :=
  physicalClippedTrace n k (scaleFactor n (n+1+j) b*ρ)

lemma physicalResolvent_continuous_shift (b : ℝ) : Continuous (physicalResolvent b) := by
  unfold physicalResolvent
  exact continuous_const.mul (semicircleResolvent_continuous.comp ((continuous_id.div_const _).sub continuous_const))

/-- Actual physical GOE clipped trace convergence along arbitrary
converging shifts and diverging dimensions. The cutoff is literally
scaleFactor(n,N,b)*rho, as displayed in its definition. -/
theorem physical_clipped_resolvent_varying_L2 (j : ℕ) {b ρ k : ℝ} (hb : 0 < b)
    (hρ : 0 < ρ) (hk : 2*Real.sqrt b < k) (hρk : ρ ≤ (k/Real.sqrt b-2)/2)
    (φ : ℕ → ℕ) (hφ : Tendsto φ atTop atTop) (kN : ℕ → ℝ) (hkN : Tendsto kN atTop (𝓝 k)) :
    Tendsto (fun l:ℕ=>∫ W,(physicalClippedResolvent (φ l) j b (kN l) ρ W-physicalResolvent b (kN l))^2
      ∂goeLaw (φ l+1) (φ l+1+j) b) atTop (𝓝 0) := by
  let a : ℕ → ℝ:=fun l=>scaleFactor (φ l) (φ l+1+j) b
  have ha (l:ℕ) : 0 < a l:=scaleFactor_pos _ (by omega) hb
  have hat : Tendsto a atTop (𝓝 (Real.sqrt b)) := (scaleFactor_tendsto j hb.le).comp hφ
  have hbS : Real.sqrt b≠0:=(Real.sqrt_pos.mpr hb).ne'
  let sN : ℕ → ℝ:=fun l=>kN l/a l-2
  let s:=k/Real.sqrt b-2
  have hs : 0 < s := by
    have hh:=(lt_div_iff₀ (Real.sqrt_pos.mpr hb)).mpr hk
    linarith
  have hsN : Tendsto sN atTop (𝓝 s):= (hkN.div hat hbS).sub_const 2
  have hstd:=clippedResolvent_varying_shift_L2 φ hφ sN hsN hs hρ hρk
  let K : ℕ → ℝ:=fun l=>|(a l)⁻¹*semicircleResolvent (sN l)-physicalResolvent b (kN l)|
  have hKt : Tendsto K atTop (𝓝 0) := by
    have h1:= (hat.inv₀ hbS).mul ((semicircleResolvent_continuous.tendsto s).comp hsN)
    have h2:= (physicalResolvent_continuous_shift b).tendsto k |>.comp hkN
    simpa only [K,s,Function.comp_def,physicalResolvent,sub_self,abs_zero] using (h1.sub h2).abs
  have hupper : Tendsto (fun l=>2*((a l)⁻¹)^2*(∫ W,(clippedResolvent (φ l) (sN l) ρ W-semicircleResolvent (sN l))^2
      ∂goeLaw (φ l+1) (φ l+1) 1)+2*K l^2) atTop (𝓝 0) := by
    simpa only [mul_zero,zero_pow (by norm_num : (2:ℕ)≠0),add_zero] using
      (((hat.inv₀ hbS).pow 2).const_mul 2 |>.mul hstd).add ((hKt.pow 2).const_mul 2)
  apply squeeze_zero (fun l=>integral_nonneg (fun _=>sq_nonneg _)) (fun l=>?_) hupper
  have hscale : Measurable (fun W:Matrix (Fin (φ l+1)) (Fin (φ l+1)) ℝ=>a l • W) := by fun_prop
  have hmap : (goeLaw (φ l+1) (φ l+1) 1).map (fun W=>a l • W)=goeLaw (φ l+1) (φ l+1+j) b :=
    goeLaw_scale _ (by omega) hb.le
  have hm : Measurable (fun W:Matrix (Fin (φ l+1)) (Fin (φ l+1)) ℝ=>
      (physicalClippedResolvent (φ l) j b (kN l) ρ W-physicalResolvent b (kN l))^2) :=
    ((physicalClippedTrace_measurable _ _ _).sub_const _).pow_const 2
  rw [← hmap,integral_map hscale.aemeasurable hm.aestronglyMeasurable]
  have hEval (W : Matrix (Fin (φ l+1)) (Fin (φ l+1)) ℝ) :
      physicalClippedResolvent (φ l) j b (kN l) ρ (a l • W)=
        (a l)⁻¹*clippedResolvent (φ l) (sN l) ρ W := by
    change physicalClippedTrace (φ l) (kN l) (a l*ρ) (a l • W)=_
    exact physicalClippedTrace_scale (φ l) (ha l) (kN l) ρ W
  simp only [hEval]
  let F:=fun W:Matrix (Fin (φ l+1)) (Fin (φ l+1)) ℝ=>(a l)⁻¹*clippedResolvent (φ l) (sN l) ρ W-physicalResolvent b (kN l)
  let G:=fun W:Matrix (Fin (φ l+1)) (Fin (φ l+1)) ℝ=>(a l)⁻¹*(clippedResolvent (φ l) (sN l) ρ W-semicircleResolvent (sN l))
  have hGInt : Integrable (fun W=>G W^2) (goeLaw (φ l+1) (φ l+1) 1) := by
    have hh:=(clippedResolvent_centered_square_integrable (φ l) (sN l) (semicircleResolvent (sN l)) hρ).const_mul (((a l)⁻¹)^2)
    simpa only [G,mul_pow] using hh
  have hFMeas : Measurable F:= (measurable_const.mul (clippedResolvent_measurable _ _ _)).sub_const _
  have hFbound (W) : |F W| ≤ (a l)⁻¹/ρ+|physicalResolvent b (kN l)| := by
    have hh:=clippedResolvent_bounds (φ l) (sN l) hρ W
    calc
      _ ≤ |(a l)⁻¹*clippedResolvent (φ l) (sN l) ρ W|+|physicalResolvent b (kN l)|:=abs_sub _ _
      _= (a l)⁻¹*clippedResolvent (φ l) (sN l) ρ W+|physicalResolvent b (kN l)| := by
        rw [abs_mul,abs_of_pos (inv_pos.mpr (ha l)),abs_of_nonneg hh.1]
      _ ≤ (a l)⁻¹*(1/ρ)+|physicalResolvent b (kN l)| :=
        add_le_add (mul_le_mul_of_nonneg_left hh.2 (inv_nonneg.mpr (ha l).le)) le_rfl
      _=_ := by rw [← mul_div_assoc,mul_one]
  have hapos := ha l
  have hFInt : Integrable (fun W=>F W^2) (goeLaw (φ l+1) (φ l+1) 1) :=
    (square_integral_le_small_bad _ F hFMeas (C:=(a l)⁻¹/ρ+|physicalResolvent b (kN l)|)
      (ε:=0) (by positivity) (by norm_num) hFbound).1
  have heq (W) : F W-G W=(a l)⁻¹*semicircleResolvent (sN l)-physicalResolvent b (kN l) := by dsimp only [F,G];ring
  have hh:=integral_square_perturbation_bound _ F G hFInt hGInt (K:=K l) (abs_nonneg _) (fun W=>by rw [heq])
  have hGI : (∫ W,G W^2 ∂goeLaw (φ l+1) (φ l+1) 1)=
      ((a l)⁻¹)^2*(∫ W,(clippedResolvent (φ l) (sN l) ρ W-semicircleResolvent (sN l))^2 ∂goeLaw (φ l+1) (φ l+1) 1) := by
    simp only [G,mul_pow,integral_const_mul]
  rw [hGI] at hh
  simpa only [F,mul_assoc] using hh

end
end SlowEquilibration.GOEClippedResolvent
