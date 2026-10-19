module

public import SphericalAging.LpMomentBounds

public section
/-! Elementary interpolation powers for the genuine second-flow remainder. -/
noncomputable section
open MeasureTheory Filter Topology
namespace SphericalAging.SecondVariationPowerBounds

lemma flow_power (C B d : ℝ) (hC : 0≤C) (hB : 0≤B) (hd : 0≤d) :
    (C*d^2)^((1 : ℝ)/3)*(B*d)^((2 : ℝ)/3)=
      C^((1 : ℝ)/3)*B^((2 : ℝ)/3)*d^((4 : ℝ)/3) := by
  rw [Real.mul_rpow hC (sq_nonneg _),Real.mul_rpow hB hd,
    ←Real.rpow_natCast d 2,←Real.rpow_mul hd]
  have he : (2 : ℝ)*((1 : ℝ)/3)=((2 : ℝ)/3) := by norm_num
  simp only [Nat.cast_ofNat] at *
  rw [he]
  have hr := Real.rpow_add_of_nonneg hd (by norm_num : (0 : ℝ)≤2/3) (by norm_num : (0 : ℝ)≤2/3)
  have hs : (2 : ℝ)/3+2/3=4/3 := by norm_num
  rw [hs] at hr
  rw [hr]
  ring

lemma response_power (C B d n : ℝ) (hC : 0≤C) (hB : 0≤B) (hd : 0≤d) (hn : 0≤n) :
    (C*d*n)^((1 : ℝ)/3)*(B*n)^((2 : ℝ)/3)=
      C^((1 : ℝ)/3)*B^((2 : ℝ)/3)*d^((1 : ℝ)/3)*n := by
  rw [Real.mul_rpow (mul_nonneg hC hd) hn,Real.mul_rpow hC hd,Real.mul_rpow hB hn]
  have hr := Real.rpow_add_of_nonneg hn (by norm_num : (0 : ℝ)≤1/3) (by norm_num : (0 : ℝ)≤2/3)
  norm_num at hr
  calc
    _ = C^((1 : ℝ)/3)*B^((2 : ℝ)/3)*d^((1 : ℝ)/3)*(n^((1 : ℝ)/3)*n^((2 : ℝ)/3)) := by ring
    _ = _ := by rw [←hr]

lemma norm_mul_third (d : ℝ) (hd : 0≤d) : d*d^((1 : ℝ)/3)=d^((4 : ℝ)/3) := by
  have hr := Real.rpow_add_of_nonneg hd (by norm_num : (0 : ℝ)≤1) (by norm_num : (0 : ℝ)≤1/3)
  norm_num at hr
  exact hr.symm

variable {E G : Type*} [NormedAddCommGroup E] [NormedAddCommGroup G]

/-- A quadratic plus four-thirds remainder is genuinely little-o of the increment. -/
theorem isLittleO_of_bound {R : E → G} (x : E) {A B : ℝ} (hA : 0≤A) (hB : 0≤B)
    (hR : ∀ y,‖R y‖≤A*‖y-x‖^2+B*‖y-x‖^((4 : ℝ)/3)) :
    R =o[𝓝 x] (fun y => y-x) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  have hlim : Tendsto (fun y : E => A*‖y-x‖+B*‖y-x‖^((1 : ℝ)/3)) (𝓝 x) (𝓝 0) := by
    have hn : Tendsto (fun y : E => ‖y-x‖) (𝓝 x) (𝓝 0) := by
      have hc : Continuous (fun y : E => ‖y-x‖) := (continuous_id.sub continuous_const).norm
      simpa only [sub_self,norm_zero] using hc.tendsto x
    have hp := (Real.continuousAt_rpow_const (0 : ℝ) ((1 : ℝ)/3) (.inr (by norm_num))).tendsto.comp hn
    simpa using (hn.const_mul A).add (hp.const_mul B)
  have hevent : ∀ᶠ y : E in 𝓝 x,A*‖y-x‖+B*‖y-x‖^((1 : ℝ)/3)<ε := hlim.eventually (gt_mem_nhds hε)
  filter_upwards [hevent] with y hy
  apply (hR y).trans
  have he : A*‖y-x‖^2+B*‖y-x‖^((4 : ℝ)/3)=
      (A*‖y-x‖+B*‖y-x‖^((1 : ℝ)/3))*‖y-x‖ := by
    rw [←norm_mul_third _ (norm_nonneg _)];ring
  rw [he]
  exact mul_le_mul_of_nonneg_right hy.le (norm_nonneg _)
end SphericalAging.SecondVariationPowerBounds
