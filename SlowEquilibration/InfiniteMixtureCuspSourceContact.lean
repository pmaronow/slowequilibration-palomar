-- SPDX-License-Identifier: Apache-2.0
module

public import SlowEquilibration.InfiniteMixtureCuspBarrierEpsilon

/-! The exact source contact expansion for the very same order and coefficient
stored in any constructed cusp coordinate. The proof pulls the established
normal form back through its genuine local inverse. -/
@[expose] public section
noncomputable section
namespace SlowEquilibration.InfiniteMixture.CuspCoordinate
open Set Filter Asymptotics
open scoped Topology
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
variable {μ : InfiniteMixture} (c : CuspCoordinate μ)

private theorem pow_near_identity_remainder {g : ℝ → ℝ}
    (hg : g =O[𝓝 (0:ℝ)] (fun t => t))
    (hrem : (fun t => g t-t) =O[𝓝 (0:ℝ)] (fun t => t^2)) (k : ℕ) :
    (fun t => g t^k-t^k) =O[𝓝 (0:ℝ)] (fun t => t^(k+1)) := by
  induction k with
  | zero => simpa only [pow_zero,sub_self] using (isBigO_zero (fun t : ℝ => t^(0+1)) (𝓝 (0:ℝ)))
  | succ k ih =>
    have h₁ := ih.mul hg
    have h₂ := (isBigO_refl (fun t : ℝ => t^k) (𝓝 (0:ℝ))).mul hrem
    have h₁' : (fun t => (g t^k-t^k)*g t) =O[𝓝 (0:ℝ)] (fun t => t^(k+2)) := by
      simpa only [pow_succ] using h₁
    have h₂' : (fun t => t^k*(g t-t)) =O[𝓝 (0:ℝ)] (fun t => t^(k+2)) := by
      simpa only [pow_add] using h₂
    apply (h₁'.add h₂').congr' ?_ .rfl
    exact Eventually.of_forall (fun t => by simp only [pow_succ];ring)

private theorem sourceContact_along_coordinate :
    (fun t : ℝ => μ.A (μ.qD+c.g t)-μ.Amax*(1-c.a*(c.g t)^(2*c.m)))
      =O[𝓝 (0:ℝ)] (fun t => t^(2*c.m+1)) := by
  let k : ℕ := 2*c.m
  have hk : 1 ≤ k := by dsimp [k];have := c.m_pos;omega
  have hg : c.g =O[𝓝 (0:ℝ)] (fun t => t) := by
    simpa only [c.zero,sub_zero] using c.derivative.differentiableAt.isBigO_sub
  have hp := (pow_near_identity_remainder hg c.remainder k).const_mul_left (μ.Amax*c.a)
  let R : ℝ → ℝ := fun t => μ.Amax*c.a^2*t^(k-1)/(1+c.a*t^k)
  have hden : (1:ℝ)+c.a*(0:ℝ)^k ≠ 0 := by simp [zero_pow (by omega : k≠0)]
  have hRc : ContinuousAt R 0 := by
    dsimp [R]
    exact (by fun_prop : ContinuousAt (fun t : ℝ => μ.Amax*c.a^2*t^(k-1)) 0).div
      (by fun_prop) hden
  have hR := hRc.tendsto.isBigO_one ℝ
  have hq := (isBigO_refl (fun t : ℝ => t^(k+1)) (𝓝 (0:ℝ))).mul hR
  have hq' : (fun t => t^(k+1)*R t) =O[𝓝 (0:ℝ)] (fun t => t^(k+1)) := by
    simpa only [mul_one] using hq
  have hn : ∀ᶠ t in 𝓝 (0:ℝ), t ∈ Icc (-c.radius) c.radius :=
    eventually_of_mem (Ioo_mem_nhds (by linarith [c.radius_pos]) c.radius_pos)
      (fun _ ht => ⟨ht.1.le,ht.2.le⟩)
  apply (hp.add hq').congr' ?_ .rfl
  filter_upwards [hn] with t ht
  rw [c.normal t ht]
  have hd : 1+c.a*t^k ≠ 0 := by
    have ht0 : 0 ≤ t^k := by dsimp [k];rw [pow_mul];positivity
    have := c.a_pos
    positivity
  have hpowers : t^(k+1)*t^(k-1) = t^(2*k) := by
    rw [← pow_add]
    congr 1
    omega
  change μ.Amax*c.a*(c.g t^k-t^k)+t^(k+1)*R t = _
  dsimp [R]
  change _ = μ.Amax/(1+c.a*t^k)-μ.Amax*(1-c.a*c.g t^k)
  field_simp [hd]
  have hpowers' : t^(k+1)*t^(k-1) = (t^k)^2 := by
    rw [hpowers,mul_comm (2:ℕ) k,pow_mul]
  linear_combination μ.Amax*c.a^2 * hpowers'

/-- The literal unnormalized source expansion, for the same `m` and `a`
that govern this coordinate's roots and barrier coefficient. -/
theorem sourceContact :
    (fun y : ℝ => μ.A (μ.qD+y)-μ.Amax*(1-c.a*y^(2*c.m)))
      =O[𝓝 (0:ℝ)] (fun y => y^(2*c.m+1)) := by
  have hdn : deriv c.g 0 ≠ 0 := by rw [c.derivative.deriv];norm_num
  let h := c.analytic.hasStrictDerivAt.localInverse c.g (deriv c.g 0) 0 hdn
  have hh : AnalyticAt ℝ h 0 := by
    simpa only [c.zero] using c.analytic.analyticAt_localInverse hdn
  have hl : ∀ᶠ t in 𝓝 (0:ℝ), h (c.g t) = t :=
    c.analytic.hasStrictDerivAt.eventually_left_inverse hdn
  have hr : ∀ᶠ y in 𝓝 (0:ℝ), c.g (h y) = y := by
    simpa only [c.zero] using c.analytic.hasStrictDerivAt.eventually_right_inverse hdn
  have hh0 : h 0 = 0 := by simpa only [c.zero] using hl.self_of_nhds
  have hd : HasDerivAt h 1 0 := by
    simpa only [c.zero,c.derivative.deriv,inv_one] using
      (c.analytic.hasStrictDerivAt.to_localInverse hdn).hasDerivAt
  have hO : h =O[𝓝 (0:ℝ)] (fun y => y) := by
    simpa only [hh0,sub_zero] using hd.differentiableAt.isBigO_sub
  have ht : Tendsto h (𝓝 (0:ℝ)) (𝓝 (0:ℝ)) := by
    simpa only [hh0] using hh.continuousAt.tendsto
  have hcomp := (c.sourceContact_along_coordinate.comp_tendsto ht).trans (hO.pow (2*c.m+1))
  apply hcomp.congr' ?_ .rfl
  filter_upwards [hr] with y hy
  simp only [Function.comp_def,hy]

/-- The normalized expansion in the source theorem statement. -/
theorem sourceContact_normalized :
    (fun y : ℝ => μ.A (μ.qD+y)/μ.Amax-(1-c.a*y^(2*c.m)))
      =O[𝓝 (0:ℝ)] (fun y => y^(2*c.m+1)) := by
  apply (c.sourceContact.const_mul_left μ.Amax⁻¹).congr' ?_ .rfl
  exact Eventually.of_forall (fun y => by field_simp [μ.Amax_pos.ne'])

/-- The stored barrier coefficient is exactly the literal source coefficient
formed from this same order and leading contact coefficient. -/
theorem barrierCoefficient_eq_source :
    c.barrierCoefficient =
      (2*(c.m:ℝ)*μ.qD)/((2*(c.m:ℝ)+1)*(1-μ.qD))*c.a^(-1/(2*(c.m:ℝ))) := by
  simp only [barrierCoefficient,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_add,Nat.cast_one,
    neg_div,one_div]

end SlowEquilibration.InfiniteMixture.CuspCoordinate
